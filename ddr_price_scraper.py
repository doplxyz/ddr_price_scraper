#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
drive_price_scraper.py
======================
Amazon.co.jp の SSD・HDD 価格スクレイピング＋グラフ生成を一貫実行するツール。

[Version 1.7]
  - 引数をユーザで管理出来るよう見える化

[Version 1.6]
  - 異常値フィルタを強化: 中央値(Median)基準で高額側をカットする機能を追加
    (Price > Median * 2.5 を除外)

============================================================
[必要条件]
  - Python 3.12.3 以上
  - 必要な外部ライブラリ:
      requests     … HTTP通信
      matplotlib   … グラフ生成

============================================================
[導入手順]

  1. Python 3.12.3 以上の環境があることを確認する。
         $ python3 --version
         Python 3.12.x

  2. 外部ライブラリをインストールする。
     ── 標準の場合（仮想環境なし）──
         $ pip install requests matplotlib

     ── 仮想環境を使う場合（推奨）──
         $ python3 -m venv .venv
         $ source .venv/bin/activate          # Windows: .venv\\Scripts\\activate
         $ pip install requests matplotlib

     ── pip が「externally-managed-environment」と拒否する場合 ──
         以下のいずれかを対応する:
           a) 仮想環境を使う（上記「仮想環境を使う場合」）
           b) pipx を使う
               $ pipx install requests matplotlib
           c) 強制インストールする（自己責任）
               $ pip install --break-system-packages requests matplotlib

============================================================
[コマンド体系]
  このツールは2つの実行モードを持っています。

  1. --scrape フラグモード (推奨)
     スクレイピングを実行し、完了後に自動的にグラフを生成します。
     基本的にはこれを使います。

  2. gauge サブコマンド
     過去に取得したログファイルから、グラフのみを再生成します。
     スクレイピングは行いません。

============================================================
[使い方の例]

  --- 基本的な使い方 ---
  # SSD/HDD 両方をスクレイピングし、グラフを出力する
  $ python3 drive_price_scraper.py --scrape

  --- 絞り込み実行 ---
  # SSD のみ実行
  $ python3 drive_price_scraper.py --scrape --kind SSD

  # SSD の 1TB, 2TB, 4TB のみ実行
  $ python3 drive_price_scraper.py --scrape --kind SSD --caps 1TB 2TB 4TB

  --- グラフのみ再生成 (gauge) ---
  # 今日の日付のログからグラフを作り直す
  $ python3 drive_price_scraper.py gauge

  # 特定の日付(2026-01-31)のログを指定してグラフ化
  $ python3 drive_price_scraper.py gauge --date 2026-01-31

  # グラフを画面に表示する（GUI環境のみ）
  $ python3 drive_price_scraper.py gauge --show

  --- 高度なオプション ---
  # ページ遷移のスリープを 5秒に短縮（デフォルト10秒）
  $ python3 drive_price_scraper.py --scrape --sleep 5.0

  # 主要ブランドのみに絞って SSD を検索
  $ python3 drive_price_scraper.py --scrape --kind SSD --brand-only

============================================================
[オプション一覧]
  --scrape               スクレイピング＋グラフ生成を実行
  --base-dir DIR         データ保存・読込の基準ディレクトリ（デフォルト: カレント）
  --kind {SSD,HDD,ALL}   対象ドライブ種別（デフォルト: ALL）
  --caps CAP [CAP...]    対象容量を個別に指定（例: 1TB 2TB）
  --sleep SEC            ページ間ウェイト秒数（デフォルト: 10.0）
  --jitter SEC           ランダム待機の最大秒数（デフォルト: 2.0）
  --timeout SEC          HTTPタイムアウト秒数（デフォルト: 40）
  --show                 生成したグラフをウィンドウで表示（GUI必須）
  --raw                  フィルタ処理を無効化し、全件をCSV出力
  --brand-only           (SSD/HDD) 主要ブランド・メーカー品のみに絞る
  --no-capacity-match    容量不一致の判定（除外）を無効化する
  --debug-save-all       デバッグ用に取得した全HTMLを保存する
  --low-price-ratio R    安値異常値判定の係数。中央値 * R 未満を除外（デフォルト: 0.3）
  --high-price-ratio R   高値異常値判定の係数。中央値 * R 超過を除外（デフォルト: 2.5）
  --scale DIV            グラフの金額バーの縮尺除数（デフォルト: 100）

  [サブコマンド: gauge]
  --date YYYY-MM-DD      処理対象の日付（デフォルト: 今日）
  --ssd-dir DIR          SSDログディレクトリを直接指定
  --hdd-dir DIR          HDDログディレクトリを直接指定
"""

import re
import csv
import time
import sys
import os
import argparse
import random
import datetime
import statistics
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

import requests

# ============================================================
# ■ VERSION 管理
# ============================================================
VERSION = "1.7"


# ============================================================
# ■ CONFIG セクション
# ============================================================

# [CHANGE] Amazon.co.jp のベースURL
AMAZON_BASE_URL = "https://www.amazon.co.jp"

# [CHANGE] 検索URL のテンプレート
SEARCH_URL_TEMPLATE = AMAZON_BASE_URL + "/s?k={kind}+{cap}&ref=nb_sb_noss_1"

# [CHANGE] スクレイピング対象の容量リスト
SSD_CAPACITIES = ["128GB","256GB","512GB","1TB", "2TB", "4TB", "8TB"]
HDD_CAPACITIES = ["1TB", "2TB", "4TB", "6TB", "8TB", "10TB", "12TB", "14TB", "16TB", "18TB", "20TB", "22TB", "24TB", "26TB", "28TB"]

# [CHANGE] SSD ブランドラベル
SSD_BRAND_DEFS = [
    ("Samsung",          [r"\bSamsung\b", r"サムスン"]),
    ("Western Digital",  [r"Western\s*Digital", r"\bWD\b"]),
    ("SanDisk",          [r"SanDisk", r"サンディスク"]),
    ("Crucial",          [r"Crucial", r"クルーシャル"]),
    ("Micron",           [r"\bMicron\b"]),
    ("Kingston",         [r"Kingston", r"キングストン"]),
    ("SK hynix",         [r"SK\s*hynix", r"SKhynix", r"エスケーハイニックス"]),
    ("KIOXIA",           [r"KIOXIA", r"キオクシア"]),
    ("Toshiba",          [r"TOSHIBA", r"東芝"]),
    ("Seagate",          [r"Seagate", r"シーゲイト", r"FireCuda"]),
    ("Solidigm",         [r"Solidigm"]),
    ("Intel",            [r"\bIntel\b"]),
    ("Corsair",          [r"Corsair", r"コルセア"]),
    ("ADATA",            [r"\bADATA\b"]),
    ("Team",             [r"Team(Group)?", r"Team\s*Group", r"チーム"]),
    ("Silicon Power",    [r"Silicon\s*Power"]),
    ("Patriot",          [r"Patriot"]),
    ("Transcend",        [r"Transcend", r"トランセンド"]),
    ("Sabrent",          [r"Sabrent"]),
    ("PNY",              [r"\bPNY\b"]),
    ("Lexar",            [r"Lexar"]),
    ("GIGABYTE",         [r"GIGABYTE"]),
    ("MSI",              [r"\bMSI\b"]),
    ("BUFFALO",          [r"BUFFALO", r"バッファロー"]),
    ("IODATA",           [r"IO\s*DATA", r"IODATA", r"アイ・オー", r"アイオー"]),
    ("ELECOM",           [r"ELECOM", r"エレコム"]),
]

# [CHANGE] HDD メーカーラベル
HDD_MAKER_DEFS = [
    ("Seagate",          [r"Seagate", r"シーゲイト", r"BarraCuda", r"IronWolf", r"Exos", r"SkyHawk"]),
    ("Western Digital",  [r"Western Digital", r"ウエスタンデジタル", r"\bWD\b",
                           r"WD Red", r"WD Blue", r"WD Black", r"WD Purple", r"Gold", r"Ultrastar"]),
    ("Toshiba",          [r"TOSHIBA", r"東芝", r"N300", r"X300", r"P300", r"MG\d{2}", r"DT\d{2}"]),
    ("HGST",             [r"\bHGST\b", r"Hitachi Global Storage"]),
    ("Hitachi",          [r"\bHitachi\b", r"日立"]),
]

# [CHANGE] HDD のブランド（周辺機器・外付け系も含む）
HDD_EXTRA_BRAND_DEFS = [
    ("BUFFALO",          [r"BUFFALO", r"バッファロー"]),
    ("IODATA",           [r"IO DATA", r"IODATA", r"アイ・オー", r"アイオー"]),
    ("ELECOM",           [r"ELECOM", r"エレコム"]),
]

# [CHANGE] SSD付属品キワード（除外対象）
SSD_ACCESSORY_WORDS = [
    "ケース", "エンクロージャ", "エンクロージャー", "外付けケース", "SSDケース", "SSD ケース",
    "M.2ケース", "M.2 ケース", "NVMeケース", "NVMe ケース", "USBケース", "USB ケース",
    "クレードル", "ドック", "ドッキング", "クローン", "クローンドック", "クローンスタンド",
    "変換", "アダプタ", "アダプター", "ケーブル", "SATA-USB", "USB-SATA", "NVMe-USB", "M.2-USB",
    "PCIe変換", "PCIe 変換", "変換基板", "ライザー", "延長ケーブル",
    "ヒートシンク", "放熱", "サーマル", "熱伝導", "サーマルパッド", "冷却",
    "ブラケット", "マウンタ", "マウンター", "トレイ", "ネジ", "工具",
    "ドライバー", "固定", "両面テープ", "XBOX",
]

# [CHANGE] HDD付属品キワード（除外対象）
HDD_ACCESSORY_WORDS = [
    "ケース", "スタンド", "ドック", "ドッキング", "クローン",
    "エンクロージャ", "変換", "アダプタ", "ケーブル",
    "ブラケット", "マウンタ", "トレイ", "ネジ", "工具",
    "RAIDケース", "RAID ケース", "HDDケース", "HDD ケース", "SSDケース", "SSD ケース",
    "クレードル", "ハブ", "USBハブ", "電源アダプタ", "XBOX",
]

# [CHANGE] PC本体キワード（SSD除外用）
SSD_PC_WORDS = [
    "ノートパソコン", "ゲーミングPC", "デスクトップ", "Mini PC", "ミニPC", "ワークステーション",
    "MacBook", "iMac", "Mac mini", "ThinkPad", "Chromebook", "NAS本体", "NAS キット",
]

# [CHANGE] その他メディア（SSD除外用）
SSD_OTHER_MEDIA_WORDS = [
    "USBメモリ", "USBフラッシュ", "フラッシュドライブ", "SDカード", "microSD", "メモリーカード",
    "CFexpress", "カードリーダー", "HDD", "ハードディスク", "Blu-ray", "DVD",
]

# [CHANGE] NASデバイス本体キワード（HDD除外用）
HDD_NAS_DEVICE_WORDS = [
    "Synology", "QNAP", "NASync", "2ベイ", "4ベイ", "5ベイ", "6ベイ", "8ベイ",
    "DiskStation", "TerraMaster", "Asustor",
]

# [CHANGE] "おすすめ出品なし" ノイズフレーズ
BAD_OFFER_PHRASES = [
    '「おすすめ出品」の要件を満たす出品はありません',
    'おすすめ出品の要件を満たす出品はありません',
    'The offer does not meet the Featured Offer requirements',
    'does not meet the Featured Offer requirements',
    'There are no Featured Offer eligible offers',
]


# ============================================================
# LAYOUT CONFIGURATION SECTION
# ============================================================
# このセクションの数値を変更することで、グラフの見栄えを調整できます

# --- Figure Size Settings ---
FIGURE_WIDTH = 11              # グラフ全体の幅,default,16
FIGURE_HEIGHT_BASE = 4.0       # 最小の高さ,default,4.0
FIGURE_HEIGHT_PER_ROW = 0.65   # 1行あたりの追加高さ,default,0.65
FIGURE_HEIGHT_OFFSET = 1.2     # 高さ計算のオフセット,default,1.2
FIGURE_DPI = 90               # 解像度(DPI),default,120

# --- Figure Margin Settings ---
MARGIN_TOP = 0.95              # 上マージン(0.0-1.0),default,0.90
MARGIN_BOTTOM = 0.05           # 下マージン(0.0-1.0),default,0.05
MARGIN_RIGHT = 0.98           # 右マージン(0.0-1.0),default,0.995
MARGIN_LEFT = 0.12             # 左マージン(0.0-1.0),default,0.05

# --- Bar Chart Settings ---
BAR_HEIGHT = 0.62              # バーの高さ (MAX),default,0.62
BAR_AVG_RATIO = 0.70            # AVGバーの高さ比率(MAXバーに対する),default,0.7
BAR_MIN_RATIO = 0.40           # MINバーの高さ比率(MAXバーに対する),default,0.45

# --- Bar Color Settings ---
COLOR_MAX = "#FF8888"          # MAX価格の色(赤系),default,#FF6666
COLOR_AVG = "#66CC66"          # AVG価格の色(緑系),default,#66CC66
COLOR_MIN = "#6666FF"          # MIN価格の色(青系),default,#6666FF

# --- Bar Alpha (Transparency) Settings ---
ALPHA_MAX = 0.38                # MAX価格の透明度(0.0-1.0),default,0.8
ALPHA_AVG = 0.39                # AVG価格の透明度(0.0-1.0),default,0.9
ALPHA_MIN = 0.40                # MIN価格の透明度(0.0-1.0),default,1.0

# --- X-Axis Settings ---
X_AXIS_MAX_BAR_POSITION = 0.92 # 最大バーがX軸上で表示される位置(0.0-1.0)
                               # 例: 0.60 = グラフ幅の60%位置に最大値が来る,default,0.60

# --- Text Area Layout Settings ---
TEXT_START_MULTIPLIER = 0.10   # テキスト開始位置の倍率(global_max * この値),default,1.00
TEXT_START_MIN_RATIO = 0.10    # テキスト開始位置の最小比率(xlim_right * この値),default,0.60

# --- Column Width Settings (Text Area) ---
# 各列の幅の比率。合計値で正規化されます。
COLUMN_WIDTH_MIN = 1.1         # MIN列の幅,default,1.2
COLUMN_WIDTH_AVG = 1.1         # AVG列の幅,default,1.2
COLUMN_WIDTH_MAX = 1.1         # MAX列の幅,default,1.2
COLUMN_WIDTH_CNT = 0.3         # Count列の幅(他より狭く設定),default,0.5

# --- Title Settings ---
TITLE_FONTSIZE = 16            # タイトルのフォントサイズ,default,16
TITLE_PAD = 20                 # タイトルと図の間隔,default,20
TITLE_Y_POSITION = 0.990        # タイトルのY位置(0.0-1.0),default,0.95

# --- Legend Settings ---
LEGEND_LOCATION = "lower right"        # 凡例の位置,default,
LEGEND_BBOX_X = 0.99                   # 凡例のX位置(bbox_to_anchor),default,1.00
LEGEND_BBOX_Y = 0.99                   # 凡例のY位置(bbox_to_anchor),default,1.01
LEGEND_NCOL = 3                        # 凡例の列数,default,3
LEGEND_FONTSIZE = 10                   # 凡例のフォントサイズ,default,10

# --- Header Row Settings (Column Labels) ---
HEADER_Y_POSITION = -0.45       # ヘッダー行のY位置(負の値で上に配置),default,-0.70
HEADER_FONTSIZE = 10            # ヘッダーのフォントサイズ,default,10

# --- Data Text Settings ---
DATA_TEXT_FONTSIZE = 11         # データテキストのフォントサイズ,default,11
DATA_COUNT_FONTSIZE = 11        # Count列のフォントサイズ,default,11

# --- Y-Axis Label Settings ---
Y_LABEL_FONTSIZE = 11           # Y軸ラベルのフォントサイズ,default,11

# ============================================================
# END OF LAYOUT CONFIGURATION SECTION
# ============================================================


# ============================================================
# ■ COMMON セクション
# ============================================================

BLOCK_PATTERNS = [
    r"Robot Check",
    r"Enter the characters you see below",
    r"/errors/validateCaptcha",
    r"申し訳ございません",
    r"画像に表示されている文字を入力してください",
    r"入力された文字が一致しません",
]
BLOCK_RE = re.compile("|".join(BLOCK_PATTERNS), re.IGNORECASE)

ASIN_RE         = re.compile(r'data-asin="([A-Z0-9]{10})"')
TITLE_RES       = [
    re.compile(r'<h2[^>]*>.*?<span[^>]*>(.*?)</span>.*?</h2>', re.IGNORECASE | re.DOTALL),
    re.compile(r'<span[^>]*class="[^"]*a-text-normal[^"]*"[^>]*>(.*?)</span>', re.IGNORECASE | re.DOTALL),
]
PRICE_WHOLE_RE  = re.compile(r'class="a-price-whole"[^>]*>([\d,]+)<', re.IGNORECASE)
YEN_RE          = re.compile(r"[￥¥]\s*([\d,]+)")
SPONSORED_RE    = re.compile(r"スポンサー|Sponsored", re.IGNORECASE)
NEXT_RE         = re.compile(r'aria-label="次へ"|class="[^"]*s-pagination-next[^"]*"', re.IGNORECASE)

BAD_OFFER_RE = re.compile("|".join(re.escape(s) for s in BAD_OFFER_PHRASES), re.IGNORECASE)

TB_RE = re.compile(r"(\d+(?:\.\d+)?)\s*TB", re.IGNORECASE)
GB_RE = re.compile(r"(\d{2,5})\s*GB", re.IGNORECASE)

_SESSION = requests.Session()

COMMON_HEADERS = {
    "User-Agent":              "Mozilla/5.0 (X11; Linux x86_64; rv:127.0) Gecko/20100101 Firefox/127.0",
    "Accept":                  "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language":         "ja,en-US;q=0.7,en;q=0.3",
    "Connection":              "close",
    "DNT":                     "1",
    "Upgrade-Insecure-Requests": "1",
}


def log_progress(msg: str) -> None:
    print(f"# {msg}", flush=True)


def sleep_with_jitter(base_sec: float, jitter_max: float, label: str = "") -> None:
    j = random.random() * max(0.0, jitter_max)
    sec = max(0.0, base_sec) + j
    if label:
        log_progress(f"{label}: sleep {sec:.1f}s")
    t0 = time.time()
    dot_mode = (sec >= 3.0)
    while True:
        left = sec - (time.time() - t0)
        if left <= 0:
            break
        step = 1.0 if left > 1.0 else left
        time.sleep(step)
        if dot_mode:
            sys.stdout.write(".")
            sys.stdout.flush()
    if dot_mode:
        sys.stdout.write("\n")
        sys.stdout.flush()


def fetch_html(url: str, timeout_sec: int, page_hint: str = "", sleep_retry: tuple = (0, 2, 5, 9)) -> str:
    headers = dict(COMMON_HEADERS)
    headers["Referer"] = AMAZON_BASE_URL + "/"

    last_err: Exception | None = None
    for i, wait in enumerate(sleep_retry, start=1):
        if wait:
            log_progress(f"{page_hint}retry wait {wait}s (attempt {i}/{len(sleep_retry)})")
            sleep_with_jitter(wait, 0.0, label="retry-sleep")
        try:
            log_progress(f"{page_hint}fetching (attempt {i}/{len(sleep_retry)})")
            resp = _SESSION.get(url, headers=headers, timeout=timeout_sec)
            if resp.status_code in (408, 429, 503, 504):
                last_err = requests.HTTPError(response=resp)
                log_progress(f"{page_hint}HTTPError {resp.status_code}")
                continue
            resp.raise_for_status()
            return resp.text
        except requests.HTTPError as e:
            last_err = e
            code = e.response.status_code if e.response is not None else 0
            log_progress(f"{page_hint}HTTPError {code}")
            if code in (408, 429, 503, 504):
                continue
            raise
        except Exception as e:
            last_err = e
            log_progress(f"{page_hint}Exception {type(e).__name__}")
            continue
    raise last_err  # type: ignore[misc]


def is_blocked(html: str) -> bool:
    return bool(BLOCK_RE.search(html))


def extract_k_from_url(url: str) -> str:
    try:
        from urllib.parse import urlsplit, parse_qs, unquote_plus
        u = urlsplit(url)
        q = parse_qs(u.query)
        k = q.get("k", [""])[0]
        k = unquote_plus(k)
        return " ".join(k.split())
    except Exception:
        return ""


def build_page_url(url0: str, page: int) -> str:
    from urllib.parse import urlsplit, parse_qs, urlencode, urlunsplit
    u = urlsplit(url0)
    q = parse_qs(u.query, keep_blank_values=True)
    q["page"] = [str(page)]
    new_q = urlencode(q, doseq=True)
    return urlunsplit((u.scheme, u.netloc, u.path, new_q, u.fragment))


def parse_hit_count(html: str) -> Optional[int]:
    m = re.search(r"(\d[\d,]*)\s*件の結果", html)
    if not m:
        return None
    try:
        return int(m.group(1).replace(",", ""))
    except Exception:
        return None


def clean_text(s: str) -> str:
    from html import unescape
    s = unescape(s)
    s = re.sub(r"<[^>]+>", "", s)
    return " ".join(s.split()).strip()


def extract_title(block: str) -> str:
    for rex in TITLE_RES:
        m = rex.search(block)
        if m:
            return clean_text(m.group(1))
    return ""


def extract_price_yen(block: str) -> Optional[int]:
    m = PRICE_WHOLE_RE.search(block)
    if m:
        try:
            return int(m.group(1).replace(",", ""))
        except Exception:
            pass
    m2 = YEN_RE.search(block)
    if m2:
        try:
            return int(m2.group(1).replace(",", ""))
        except Exception:
            pass
    return None


def extract_sponsored(block: str) -> int:
    return 1 if SPONSORED_RE.search(block) else 0


def block_has_bad_offer(block_html: str) -> bool:
    from html import unescape as _ue
    if not block_html:
        return False
    if BAD_OFFER_RE.search(block_html):
        return True
    return bool(BAD_OFFER_RE.search(_ue(block_html)))


def split_item_blocks(html: str) -> list[tuple[str, str]]:
    pos = []
    for m in ASIN_RE.finditer(html):
        pos.append((m.start(), m.group(1)))
    blocks = []
    for i, (start, asin) in enumerate(pos):
        end = pos[i + 1][0] if i + 1 < len(pos) else len(html)
        if asin and asin != "0000000000":
            blocks.append((asin, html[start:end]))
    return blocks


def extract_capacity_gb_tb(title: str) -> tuple[Optional[int], Optional[float], list[int], list[float]]:
    tbs: list[float] = []
    gbs: list[int] = []
    for m in TB_RE.finditer(title):
        try:
            tbs.append(float(m.group(1)))
        except Exception:
            pass
    for m in GB_RE.finditer(title):
        try:
            gbs.append(int(m.group(1)))
        except Exception:
            pass
    primary_tb = tbs[0] if tbs else None
    primary_gb: Optional[int] = None
    if primary_tb is None and gbs:
        primary_gb = max(gbs)
    elif primary_tb is not None:
        primary_gb = int(round(primary_tb * 1024))
    return primary_gb, primary_tb, gbs, tbs


def guess_target_capacity_from_query(ktext: str) -> tuple[Optional[int], Optional[float]]:
    if not ktext:
        return None, None
    m = TB_RE.search(ktext)
    if m:
        try:
            return None, float(m.group(1))
        except Exception:
            pass
    m2 = GB_RE.search(ktext)
    if m2:
        try:
            return int(m2.group(1)), None
        except Exception:
            pass
    return None, None


def stats_summary(prices: list[int]) -> Optional[tuple[int, int, int]]:
    ps = [p for p in prices if isinstance(p, int)]
    if not ps:
        return None
    return min(ps), int(round(sum(ps) / len(ps))), max(ps)


def calc_median(values: list[int]) -> int:
    if not values:
        return 0
    return int(round(statistics.median(values)))


def _compile_brand_list(defs: list) -> list[tuple[str, re.Pattern]]:
    out = []
    for name, patterns in defs:
        combined = "|".join(patterns)
        out.append((name, re.compile(combined, re.IGNORECASE)))
    return out


# ============================================================
# ■ SSD_FILTER セクション
# ============================================================

_SSD_BRANDS     = _compile_brand_list(SSD_BRAND_DEFS)
_SSD_ACCESSORY_RE = re.compile("|".join(map(re.escape, SSD_ACCESSORY_WORDS)), re.IGNORECASE)
_SSD_PC_RE      = re.compile("|".join(map(re.escape, SSD_PC_WORDS)), re.IGNORECASE)
_SSD_OTHER_RE   = re.compile("|".join(map(re.escape, SSD_OTHER_MEDIA_WORDS)), re.IGNORECASE)
_SSD_RE         = re.compile(r"\bSSD\b|ソリッドステート|Solid State", re.IGNORECASE)

_SSD_IFACE_HINTS = [
    ("Thunderbolt", re.compile(r"Thunderbolt|TB3|TB4", re.IGNORECASE)),
    ("USB",         re.compile(r"USB|Type-?C|UASP", re.IGNORECASE)),
    ("NVMe",        re.compile(r"NVMe|PCIe|Gen\s*[34]|M\.2", re.IGNORECASE)),
    ("SATA",        re.compile(r"SATA|Serial\s*ATA|2\.5", re.IGNORECASE)),
]
_SSD_FORM_HINTS = [
    ("M.2",       re.compile(r"\bM\.2\b|2280|2230|2242|2260", re.IGNORECASE)),
    ("2.5inch",   re.compile(r"2\.5|2\.5インチ|7mm|9\.5mm", re.IGNORECASE)),
    ("Portable",  re.compile(r"ポータブル|外付け|Portable|External", re.IGNORECASE)),
]


def ssd_guess_brand(title: str) -> str:
    for name, rex in _SSD_BRANDS:
        if rex.search(title):
            return name
    return ""


def ssd_extract_iface(title: str) -> str:
    for name, rex in _SSD_IFACE_HINTS:
        if rex.search(title):
            return name
    return ""


def ssd_extract_form(title: str) -> str:
    for name, rex in _SSD_FORM_HINTS:
        if rex.search(title):
            return name
    return ""


def ssd_classify(title: str, target_gb: Optional[int], target_tb: Optional[float], capacity_match_enabled: bool) -> tuple[str, str]:
    t = title
    if not t:
        return "other", "empty title"

    if _SSD_ACCESSORY_RE.search(t):
        return "accessory", "accessory keyword"
    if _SSD_PC_RE.search(t):
        return "pc_device", "pc/device keyword"

    if _SSD_OTHER_RE.search(t):
        if not _SSD_RE.search(t):
            return "other", "non-ssd media"
        if re.search(r"USBメモリ|SDカード|microSD|メモリーカード", t, re.IGNORECASE):
            return "other", "usb/sd mixed"
        if re.search(r"\bHDD\b|ハードディスク", t, re.IGNORECASE):
            return "other", "hdd keyword"

    ssdish = bool(
        _SSD_RE.search(t) or
        re.search(r"NVMe|M\.2|PCIe|SATA|ソリッドステート|内蔵|外付け|ポータブル", t, re.IGNORECASE)
    )
    if not ssdish:
        return "other", "no ssd hints"

    cap_gb, cap_tb, gb_list, tb_list = extract_capacity_gb_tb(t)

    if capacity_match_enabled and ((target_tb is not None) or (target_gb is not None)):
        uniq_tb = set(round(x, 3) for x in tb_list)
        uniq_gb = set(gb_list)
        if (len(uniq_tb) > 1) or (len(uniq_gb) > 1 and target_tb is None):
            return "other", "multi-capacity listing"
        if cap_tb is None and cap_gb is None:
            return "other", "no capacity"

        if target_tb is not None:
            if cap_tb is None:
                if cap_gb is None:
                    return "other", "capacity mismatch"
                if abs(cap_gb - int(round(target_tb * 1024))) > 80 and abs(cap_gb - int(round(target_tb * 1000))) > 80:
                    return "other", "capacity mismatch"
            else:
                if abs(cap_tb - target_tb) > 0.2:
                    return "other", "capacity mismatch"
        else:
            if cap_gb is None:
                return "other", "capacity mismatch"
            if abs(cap_gb - target_gb) > max(20, int(target_gb * 0.10)):
                return "other", "capacity mismatch"

    iface = ssd_extract_iface(t)
    form  = ssd_extract_form(t)

    if re.search(r"外付け|ポータブル|Portable|External", t, re.IGNORECASE) or iface in ("USB", "Thunderbolt"):
        return "drive_external", "external hints"
    if re.search(r"NVMe|PCIe|M\.2|Gen\s*[34]", t, re.IGNORECASE) or (form == "M.2"):
        return "drive_internal_nvme", "nvme/m.2 hints"
    if re.search(r"SATA|2\.5|2\.5インチ|Serial\s*ATA", t, re.IGNORECASE) or (form == "2.5inch"):
        return "drive_internal_sata", "sata/2.5 hints"

    return "drive_internal_sata", "generic ssd"


# ============================================================
# ■ HDD_FILTER セクション
# ============================================================

_HDD_MAKERS     = _compile_brand_list(HDD_MAKER_DEFS)
_HDD_EXTRA      = _compile_brand_list(HDD_EXTRA_BRAND_DEFS)
_HDD_ACCESSORY_RE  = re.compile("|".join(map(re.escape, HDD_ACCESSORY_WORDS)), re.IGNORECASE)
_HDD_NAS_RE     = re.compile("|".join(map(re.escape, HDD_NAS_DEVICE_WORDS)), re.IGNORECASE)
_HDD_HINT_RE    = re.compile(r"\bHDD\b|ハードディスク|ハードドライブ|Hard Drive|内蔵|外付け|外付|ポータブル", re.IGNORECASE)
_HDD_SSD_RE     = re.compile(r"\bSSD\b|ソリッドステート", re.IGNORECASE)

_HDD_IFACE_HINTS = [
    ("SAS",   re.compile(r"\bSAS\b|Serial Attached SCSI", re.IGNORECASE)),
    ("SATA",  re.compile(r"\bSATA\b", re.IGNORECASE)),
    ("USB",   re.compile(r"\bUSB\b|USB3\.|Type-?C|Thunderbolt", re.IGNORECASE)),
    ("NVMe",  re.compile(r"\bNVMe\b|M\.2", re.IGNORECASE)),
]

_SEAGATE_MODEL_RE  = re.compile(r"\bST\d{4,6}[A-Z0-9]{2,}\b", re.IGNORECASE)
_WD_MODEL_RE       = re.compile(r"\bWD\d{4,6}[A-Z0-9]{2,}\b", re.IGNORECASE)
_TOSHIBA_MODEL_RE  = re.compile(r"\bHDW[A-Z0-9]{4,}\b|\bMG\d{2}\b|\bN300\b|\bX300\b|\bP300\b", re.IGNORECASE)
_HGST_MODEL_RE     = re.compile(r"\bHUH\d{3,}\b|\bHUS\d{3,}\b", re.IGNORECASE)

_FF35_RE = re.compile(r"3\.5\s*(?:インチ|inch|in)", re.IGNORECASE)
_FF25_RE = re.compile(r"2\.5\s*(?:インチ|inch|in)", re.IGNORECASE)


def hdd_guess_brand(title: str) -> str:
    for name, rex in _HDD_MAKERS:
        if rex.search(title):
            return name
    for name, rex in _HDD_EXTRA:
        if rex.search(title):
            return name
    return ""


def hdd_extract_iface(title: str) -> str:
    for name, rex in _HDD_IFACE_HINTS:
        if rex.search(title):
            return name
    return ""


def hdd_extract_form_factor(title: str) -> Optional[float]:
    if _FF35_RE.search(title):
        return 3.5
    if _FF25_RE.search(title):
        return 2.5
    return None


def hdd_has_drive_model_hint(title: str) -> bool:
    return bool(
        _SEAGATE_MODEL_RE.search(title) or
        _WD_MODEL_RE.search(title) or
        _TOSHIBA_MODEL_RE.search(title) or
        _HGST_MODEL_RE.search(title)
    )


def hdd_classify(title: str, target_tb: Optional[float], capacity_match_enabled: bool, no_recommended_offer: bool) -> tuple[str, str]:
    t = title

    if no_recommended_offer:
        return "other", "no recommended offer"
    if _HDD_ACCESSORY_RE.search(t):
        return "accessory", "accessory keyword"
    if _HDD_NAS_RE.search(t):
        if not re.search(r"NAS向け|NAS用|NAS向けHDD|NAS 用", t, re.IGNORECASE):
            return "nas_device", "NAS device keyword"

    if _HDD_SSD_RE.search(t) and not re.search(r"\bHDD\b|ハードディスク", t, re.IGNORECASE):
        return "other", "SSD keyword"

    cap0, cap_list = _hdd_extract_capacity_tb(t)

    if capacity_match_enabled and (target_tb is not None):
        if len(set(round(x, 3) for x in cap_list)) > 1:
            return "other", "multi-capacity listing"
        if cap0 is None:
            return "other", "no capacity"
        if abs(cap0 - target_tb) > 0.2:
            return "other", "capacity mismatch"

    hdd_hint  = bool(_HDD_HINT_RE.search(t))
    model_hint = hdd_has_drive_model_hint(t)
    brand     = hdd_guess_brand(t)

    is_internal = bool(re.search(r"内蔵|3\.5|2\.5|SATA|SAS", t, re.IGNORECASE))
    is_external = bool(re.search(r"外付け|外付|ポータブル|USB", t, re.IGNORECASE))

    if hdd_hint or model_hint or brand:
        if is_external and not is_internal:
            return "drive_external", "external HDD-like"
        if is_internal or model_hint or re.search(r"ハードディスク|HDD", t, re.IGNORECASE):
            return "drive_internal", "internal HDD-like"

    return "other", "not HDD-like"


def _hdd_extract_capacity_tb(title: str) -> tuple[Optional[float], list[float]]:
    tbs: list[float] = []
    for m in TB_RE.finditer(title):
        try:
            tbs.append(float(m.group(1)))
        except Exception:
            pass
    if tbs:
        uniq = sorted(set(tbs))
        return uniq[0], uniq

    gbs: list[float] = []
    for m in GB_RE.finditer(title):
        try:
            gbs.append(float(m.group(1)))
        except Exception:
            pass
    if gbs:
        uniq_g = sorted(set(gbs))
        return uniq_g[0] / 1024.0, [g / 1024.0 for g in uniq_g]
    return None, []


# ============================================================
# ■ SCRAPE_RUNNER セクション
# ============================================================

def _out_csv_name(kind: str, cap: str) -> str:
    s = cap.strip().lower()
    s = re.sub(r"[^a-z0-9]+", "", s)
    return f"amazon_{kind.lower()}_{s if s else 'query'}.csv"


def _dedupe_by_asin(rows: list[dict]) -> list[dict]:
    best: dict[str, dict] = {}
    for r in rows:
        asin = r["asin"]
        if asin not in best:
            best[asin] = r
            continue
        a  = best[asin]
        pa = a.get("price_yen")
        pr = r.get("price_yen")
        if (pa is None) and (pr is not None):
            best[asin] = r
        elif (pa is not None) and (pr is not None) and pr < pa:
            best[asin] = r
    return list(best.values())


def run_scrape_one(kind: str, cap: str, sleep_sec: float = 10.0, jitter_sec: float = 2.0, timeout_sec: int = 40,
                   raw: bool = False, brand_only: bool = False, no_capacity_match: bool = False,
                   debug_save_all: bool = False, low_price_ratio: float = 0.3, high_price_ratio: float = 2.5) -> str:
    url0 = SEARCH_URL_TEMPLATE.format(kind=kind, cap=cap)
    out_csv = _out_csv_name(kind, cap)
    ktext   = extract_k_from_url(url0)
    target_gb, target_tb = guess_target_capacity_from_query(ktext)
    capacity_match_enabled = not no_capacity_match

    log_progress(f"version: {VERSION}")
    print("url:", url0)
    if ktext:
        print("query(k):", ktext)
    if target_tb is not None:
        print("target_capacity_tb:", target_tb)
    if target_gb is not None:
        print("target_capacity_gb:", target_gb)
    print("mode:", "raw" if raw else f"{kind.lower()}-filter")

    all_raw_rows: list[dict] = []
    pages_ok = 0
    stop_reason = "reached max-pages"
    debug_file: str | None = None
    max_pages   = 1
    hit_count_observed: Optional[int] = None

    for page in range(1, max_pages + 1):
        if page > 1:
            sleep_with_jitter(sleep_sec, jitter_sec, label=f"page-sleep {page}/{max_pages}")

        page_url = build_page_url(url0, page)
        html = fetch_html(page_url, timeout_sec=timeout_sec, page_hint=f"page {page}/{max_pages}: ")

        if debug_save_all:
            fn = f"amazon_{kind.lower()}_{cap}_page{page:02d}_debug.html"
            with open(fn, "w", encoding="utf-8") as f:
                f.write(html)

        if is_blocked(html):
            fn = f"amazon_{kind.lower()}_{cap}_page{page:02d}_BLOCK_debug.html"
            with open(fn, "w", encoding="utf-8") as f:
                f.write(html)
            stop_reason = f"blocked detected (debug saved: {fn})"
            debug_file = fn
            break

        if page == 1:
            hit_count_observed = parse_hit_count(html)

        blocks = split_item_blocks(html)
        if not blocks:
            fn = f"amazon_{kind.lower()}_{cap}_page{page:02d}_EMPTY_debug.html"
            with open(fn, "w", encoding="utf-8") as f:
                f.write(html)
            stop_reason = f"parsed 0 blocks at page {page} (debug saved)"
            debug_file = fn
            break

        rows = []
        for asin, block in blocks:
            title = extract_title(block)
            if not title:
                continue
            price    = extract_price_yen(block)
            sponsor  = extract_sponsored(block)
            url      = f"{AMAZON_BASE_URL}/dp/{asin}"

            if kind.upper() == "SSD":
                cap_gb, cap_tb, _, _ = extract_capacity_gb_tb(title)
                iface  = ssd_extract_iface(title)
                form   = ssd_extract_form(title)
                brand  = ssd_guess_brand(title)

                if raw:
                    category, reason = "raw", "raw mode"
                elif block_has_bad_offer(block):
                    category, reason = "bad_offer", "featured offer missing"
                else:
                    category, reason = ssd_classify(title, target_gb, target_tb, capacity_match_enabled)
                    if brand_only and not brand:
                        category, reason = "other", "brand-only: unknown brand"

                rows.append({
                    "asin": asin, "title": title, "price_yen": price,
                    "sponsored": sponsor, "url": url,
                    "capacity_gb": cap_gb if cap_gb is not None else "",
                    "capacity_tb": cap_tb if cap_tb is not None else "",
                    "form": form, "iface": iface,
                    "brand_guess": brand,
                    "category": category, "reason": reason,
                })
            else:  # HDD
                no_offer = 1 if block_has_bad_offer(block) else 0

                if raw:
                    category, reason = "raw", "raw mode"
                else:
                    category, reason = hdd_classify(title, target_tb, capacity_match_enabled, bool(no_offer))
                    if brand_only:
                        is_maker = any(rex.search(title) for _n, rex in _HDD_MAKERS)
                        if category.startswith("drive_") and not is_maker:
                            category, reason = "other", "not drive maker"

                cap0, _ = _hdd_extract_capacity_tb(title)
                ff      = hdd_extract_form_factor(title)
                iface   = hdd_extract_iface(title)
                brand   = hdd_guess_brand(title)

                rows.append({
                    "asin": asin, "title": title, "price_yen": price,
                    "sponsored": sponsor, "url": url,
                    "capacity_tb": cap0 if cap0 is not None else "",
                    "form_factor_in": ff if ff is not None else "",
                    "iface": iface, "brand_guess": brand,
                    "category": category, "reason": reason,
                    "no_recommended_offer": no_offer,
                })

        all_raw_rows.extend(rows)
        pages_ok += 1
        log_progress(f"page {page}/{max_pages} parsed {len(rows)} items (total so far {len(all_raw_rows)})")

    all_raw_rows = _dedupe_by_asin(all_raw_rows)

    filtered: list[dict] = []
    for r in all_raw_rows:
        if raw or r.get("category", "").startswith("drive_"):
            filtered.append(r)
    
    # 異常値フィルタ (rawモード以外)
    if not raw and filtered:
        valid_prices = [x["price_yen"] for x in filtered if isinstance(x.get("price_yen"), int)]
        if valid_prices:
            median_price = calc_median(valid_prices)
            
            thresh_low  = median_price * low_price_ratio
            thresh_high = median_price * high_price_ratio
            
            new_filtered = []
            removed_low = 0
            removed_high = 0
            
            for r in filtered:
                p = r.get("price_yen")
                if isinstance(p, int):
                    if p < thresh_low:
                        removed_low += 1
                        continue
                    if p > thresh_high:
                        removed_high += 1
                        continue
                new_filtered.append(r)
            
            if removed_low > 0 or removed_high > 0:
                print(f"Price Filter: Median={median_price:,}")
                if removed_low > 0:
                    print(f"  - Low Cut (<{thresh_low:,.0f}): {removed_low} items")
                if removed_high > 0:
                    print(f"  - High Cut (>{thresh_high:,.0f}): {removed_high} items")
            
            filtered = new_filtered

    if kind.upper() == "SSD":
        cols = ["asin","title","price_yen","sponsored","url",
                "capacity_gb","capacity_tb","form","iface","brand_guess","category","reason"]
    else:
        cols = ["asin","title","price_yen","sponsored","url",
                "capacity_tb","form_factor_in","iface","brand_guess","category","reason","no_recommended_offer"]

    with open(out_csv, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=cols, extrasaction="ignore")
        w.writeheader()
        w.writerows(filtered)

    print(f"saved: {out_csv} rows={len(filtered)}")
    if hit_count_observed is not None:
        print("hit_count(observed):", hit_count_observed)
    print("pages fetched:", pages_ok, "stop:", stop_reason)
    if debug_file:
        print("debug_html:", debug_file)
    print("version:", VERSION)

    prices_all = [r["price_yen"] for r in filtered if isinstance(r.get("price_yen"), int)]
    price_missing = sum(1 for r in filtered if not isinstance(r.get("price_yen"), int))

    s_all = stats_summary(prices_all)
    if s_all is not None:
        mn, avg, mx = s_all
        print("ALL min", mn, "avg", avg, "max", mx, "count", len(prices_all))
    print("price_missing_count", price_missing)

    def _print_group(prefix: str, key: str) -> None:
        groups: dict[str, list[int]] = {}
        for rr in filtered:
            v = rr.get(key)
            label = str(v).strip() if v not in (None, "") else "Unknown"
            p = rr.get("price_yen")
            if isinstance(p, int):
                groups.setdefault(label, []).append(p)
        for label in sorted(groups.keys()):
            sm = stats_summary(groups[label])
            if sm:
                mn, avg, mx = sm
                print(prefix, label, "min", mn, "avg", avg, "max", mx, "count", len(groups[label]))

    _print_group("BRAND", "brand_guess")
    if kind.upper() == "SSD":
        _print_group("IFACE", "iface")
        _print_group("FORM",  "form")
    _print_group("CAP_TB", "capacity_tb")

    return out_csv


# ============================================================
# ■ GAUGE（グラフ生成）セクション
# ============================================================

_ALL_RE   = re.compile(r'^ALL\s+min\s+(\d+)\s+avg\s+(\d+)\s+max\s+(\d+)\s+count\s+(\d+)\s*$', re.M)
_QUERY_RE = re.compile(r'^query\(k\):\s*(SSD|HDD)\s+(.+?)\s*$', re.M)
_CAP_TB_RE = re.compile(r'(\d+(?:\.\d+)?)\s*TB', re.I)


@dataclass
class StatRow:
    cap_label:  str
    cap_tb:     float
    min_price:  int
    avg_price:  int
    max_price:  int
    count:      int


def _parse_cap_tb(label: str) -> float:
    m = _CAP_TB_RE.search(label)
    if m:
        try:
            return float(m.group(1))
        except ValueError:
            pass
    m_gb = re.search(r'(\d+(?:\.\d+)?)\s*GB', label, re.I)
    if m_gb:
        try:
            return float(m_gb.group(1)) / 1024.0
        except ValueError:
            pass
    nums = re.findall(r'\d+(?:\.\d+)?', label)
    if nums:
        try:
            val = float(nums[0])
            return val
        except ValueError:
            return 0.0
    return 0.0


def _extract_cap_label(kind: str, log_name: str, text: str) -> str:
    m = _QUERY_RE.search(text)
    if m:
        k, cap = m.group(1), m.group(2)
        if k.upper() == kind.upper():
            return cap.strip()
    base = Path(log_name).name
    m2 = re.search(r'_(\d+(?:\.\d+)?TB)\.log$', base, re.I)
    if m2:
        return m2.group(1).upper()
    m3 = re.search(r'_(\d+(?:\.\d+)?)TB\.log$', base, re.I)
    if m3:
        return f"{m3.group(1)}TB".upper()
    return base


def load_stats_from_dir(dirpath: Path, kind: str) -> list[StatRow]:
    if not dirpath.exists():
        return []
    rows = []
    for p in sorted(dirpath.glob("*.log")):
        txt = p.read_text(encoding="utf-8", errors="replace")
        m = _ALL_RE.search(txt)
        if not m:
            continue
        mn, av, mx, cnt = int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(4))
        cap_label = _extract_cap_label(kind, p.name, txt)
        cap_tb    = _parse_cap_tb(cap_label)
        rows.append(StatRow(cap_label, cap_tb, mn, av, mx, cnt))
    rows.sort(key=lambda r: (r.cap_tb, r.cap_label))
    return rows


def plot_price_gauge(rows: list[StatRow], kind: str, date_str: str, out_path: Path, 
                     scale: int = 100, show: bool = False, prev_rows: list[StatRow] = None) -> None:
    if not rows:
        return

    if not show:
        import matplotlib
        matplotlib.use("Agg")

    import matplotlib.pyplot as plt
    from matplotlib.ticker import FuncFormatter

    labels = [r.cap_label for r in rows]
    mins   = [r.min_price / scale for r in rows]
    avgs   = [r.avg_price / scale for r in rows]
    maxs   = [r.max_price / scale for r in rows]

    # 前日データマッピング {cap_label: StatRow}
    prev_map = {}
    if prev_rows:
        for r in prev_rows:
            prev_map[r.cap_label] = r

    global_max = max(maxs) if maxs else 1.0
    
    # グラフ高さ計算
    fig_h = max(FIGURE_HEIGHT_BASE, FIGURE_HEIGHT_PER_ROW * len(rows) + FIGURE_HEIGHT_OFFSET)
    
    fig, ax = plt.subplots(figsize=(FIGURE_WIDTH, fig_h), dpi=FIGURE_DPI)
    
    # 余白調整
    plt.subplots_adjust(top=MARGIN_TOP, bottom=MARGIN_BOTTOM, right=MARGIN_RIGHT, left=MARGIN_LEFT)

    y = list(range(len(rows)))

    # バーの描画
    bar_h_max = BAR_HEIGHT
    bar_h_avg = BAR_HEIGHT * BAR_AVG_RATIO
    bar_h_min = BAR_HEIGHT * BAR_MIN_RATIO

    ax.barh(y, maxs, color=COLOR_MAX, alpha=ALPHA_MAX, height=bar_h_max, label="MAX")
    ax.barh(y, avgs, color=COLOR_AVG, alpha=ALPHA_AVG, height=bar_h_avg, label="AVG")
    ax.barh(y, mins, color=COLOR_MIN, alpha=ALPHA_MIN, height=bar_h_min, label="MIN")

    ax.set_yticks(y)
    ax.set_yticklabels(labels, fontsize=Y_LABEL_FONTSIZE, fontweight='bold', fontfamily='sans-serif')
    ax.invert_yaxis()
    
    # X軸の範囲設定
    if X_AXIS_MAX_BAR_POSITION > 0:
        xlim_right = global_max / X_AXIS_MAX_BAR_POSITION
    else:
        xlim_right = global_max * 1.5
    ax.set_xlim(0, xlim_right)

    def price_fmt(x, pos):
        return f"{int(x * scale):,}"

    ax.xaxis.set_major_formatter(FuncFormatter(price_fmt))

    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)
    ax.spines['left'].set_visible(False)
    ax.spines['bottom'].set_visible(True)
    ax.grid(axis="x", linestyle=":", alpha=0.4, color='gray')
    ax.set_axisbelow(True)

    # タイトル
    fig.suptitle(f"{kind} price gauge {date_str} (JPY)", fontsize=TITLE_FONTSIZE, fontweight='bold', y=TITLE_Y_POSITION)

    # Legend
    handles, legend_labels = ax.get_legend_handles_labels()
    ax.legend(handles[::-1], legend_labels[::-1], 
              loc=LEGEND_LOCATION, bbox_to_anchor=(LEGEND_BBOX_X, LEGEND_BBOX_Y), 
              ncol=LEGEND_NCOL, frameon=False, fontsize=LEGEND_FONTSIZE)

    # --- テキスト列レイアウト ---
    # 設定変数の比率に基づいて各カラムの幅と位置を計算する
    
    # テキストエリアの右端と左端の目安を計算
    pos_right_limit = xlim_right * MARGIN_RIGHT
    pos_left_limit  = max(global_max * TEXT_START_MULTIPLIER, xlim_right * TEXT_START_MIN_RATIO)
    
    text_area_width = pos_right_limit - pos_left_limit
    
    # もし幅が取れない場合は最低限の幅を確保（安全策）
    if text_area_width <= 0:
        text_area_width = xlim_right * 0.3

    # 各カラムの重み合計
    total_weight = COLUMN_WIDTH_MIN + COLUMN_WIDTH_AVG + COLUMN_WIDTH_MAX + COLUMN_WIDTH_CNT
    if total_weight <= 0: total_weight = 4.0

    # 1ウェイトあたりの幅
    unit_w = text_area_width / total_weight

    # 各カラムの幅
    w_cnt = unit_w * COLUMN_WIDTH_CNT
    w_max = unit_w * COLUMN_WIDTH_MAX
    w_avg = unit_w * COLUMN_WIDTH_AVG
    w_min = unit_w * COLUMN_WIDTH_MIN
    
    # カラムの配置（右端基準）
    x_cnt = pos_right_limit
    x_max = x_cnt - w_cnt
    x_avg = x_max - w_max
    x_min = x_avg - w_avg

    # ヘッダー描画
    ax.text(x_min, HEADER_Y_POSITION, "MIN",   color=COLOR_MIN, fontweight="bold", ha="right", fontsize=HEADER_FONTSIZE)
    ax.text(x_avg, HEADER_Y_POSITION, "AVG",   color=COLOR_AVG, fontweight="bold", ha="right", fontsize=HEADER_FONTSIZE)
    ax.text(x_max, HEADER_Y_POSITION, "MAX",   color=COLOR_MAX, fontweight="bold", ha="right", fontsize=HEADER_FONTSIZE)
    ax.text(x_cnt, HEADER_Y_POSITION, "Count", color="#333333", fontweight="bold", ha="right", fontsize=HEADER_FONTSIZE)

    # 差分フォーマット用関数
    def fmt_price(curr, prev_val):
        txt = f"{curr:,}"
        if prev_val is None:
            return txt + " (-)"
        diff = curr - prev_val
        if diff > 0:
            return txt + f" (+{diff:,})"
        elif diff < 0:
            return txt + f" ({diff:,})"
        else:
            return txt + " (±0)"

    for i, r in enumerate(rows):
        prev_row = prev_map.get(r.cap_label)
        
        # MIN
        p_min = prev_row.min_price if prev_row else None
        t_min = fmt_price(r.min_price, p_min)
        ax.text(x_min, i, t_min, va="center", ha="right", fontsize=DATA_TEXT_FONTSIZE, family="monospace", fontweight='medium')

        # AVG
        p_avg = prev_row.avg_price if prev_row else None
        t_avg = fmt_price(r.avg_price, p_avg)
        ax.text(x_avg, i, t_avg, va="center", ha="right", fontsize=DATA_TEXT_FONTSIZE, family="monospace", fontweight='medium')

        # MAX
        p_max = prev_row.max_price if prev_row else None
        t_max = fmt_price(r.max_price, p_max)
        ax.text(x_max, i, t_max, va="center", ha="right", fontsize=DATA_TEXT_FONTSIZE, family="monospace", fontweight='medium')

        # Count
        ax.text(x_cnt, i, str(r.count), va="center", ha="right", fontsize=DATA_COUNT_FONTSIZE, family="sans-serif")

    fig.savefig(str(out_path), dpi=FIGURE_DPI, bbox_inches=None)
    if show:
        print(f"[INFO] Displaying plot for {kind}...")
        plt.show()
    plt.close(fig)


def run_gauge(date_str: str, base_dir: str = ".", ssd_dir: Optional[str] = None, hdd_dir: Optional[str] = None, show: bool = False, scale: int = 100) -> None:
    base = Path(base_dir).expanduser().resolve()

    s_dir = Path(ssd_dir).expanduser().resolve() if ssd_dir else base / f"ssd_scrape_{date_str}"
    h_dir = Path(hdd_dir).expanduser().resolve() if hdd_dir else base / f"hdd_scrape_{date_str}"
    
    # 前日データの特定
    try:
        dt = datetime.datetime.strptime(date_str, "%Y-%m-%d").date()
        yesterday = dt - datetime.timedelta(days=1)
        yesterday_str = yesterday.strftime("%Y-%m-%d")
    except ValueError:
        yesterday_str = ""
    
    s_prev_dir = base / f"ssd_scrape_{yesterday_str}"
    h_prev_dir = base / f"hdd_scrape_{yesterday_str}"

    print(f"--- SSD/HDD Price Gauge Tool ({date_str}) ---")
    if yesterday_str:
        print(f"Comparing with previous day: {yesterday_str}")

    # SSD
    if s_dir.is_dir():
        ssd_rows = load_stats_from_dir(s_dir, "SSD")
        ssd_prev = load_stats_from_dir(s_prev_dir, "SSD") if s_prev_dir.is_dir() else []
        if ssd_rows:
            out = base / f"ssd_price_{date_str}.png"
            plot_price_gauge(ssd_rows, kind="SSD", date_str=date_str, out_path=out, scale=scale, show=show, prev_rows=ssd_prev)
            print(f"[OK] SSD Graph saved: {out}")
        else:
            print(f"[WARN] SSD Directory found but no parsable logs in: {s_dir}")
    else:
        print(f"[SKIP] SSD Directory not found: {s_dir}")

    # HDD
    if h_dir.is_dir():
        hdd_rows = load_stats_from_dir(h_dir, "HDD")
        hdd_prev = load_stats_from_dir(h_prev_dir, "HDD") if h_prev_dir.is_dir() else []
        if hdd_rows:
            out = base / f"hdd_price_{date_str}.png"
            plot_price_gauge(hdd_rows, kind="HDD", date_str=date_str, out_path=out, scale=scale, show=show, prev_rows=hdd_prev)
            print(f"[OK] HDD Graph saved: {out}")
        else:
            print(f"[WARN] HDD Directory found but no parsable logs in: {h_dir}")
    else:
        print(f"[SKIP] HDD Directory not found: {h_dir}")


# ============================================================
# ■ MAIN（サブコマンド・argparse）
# ============================================================

def _today_str() -> str:
    return datetime.date.today().strftime("%Y-%m-%d")


def main() -> int:
    ap = argparse.ArgumentParser(
        prog="drive_price_scraper.py",
        description="Amazon SSD/HDD 価格スクレイピング＋グラフ生成 統合ツール",
    )
    
    ap.add_argument("--scrape", action="store_true", help="スクレイピング＋グラフ生成を実行")
    
    ap.add_argument("--base-dir", default=".",          help="データ検索・出力の基準ディレクトリ（デフォルト: .）")
    ap.add_argument("--sleep",    type=float, default=10.0, help="ページ間ウェイト秒（デフォルト: 10.0）")
    ap.add_argument("--jitter",   type=float, default=2.0,  help="追加ランダム待機の上限秒（デフォルト: 2.0）")
    ap.add_argument("--timeout",  type=int,   default=40,   help="HTTPタイムアウト秒（デフォルト: 40）")
    ap.add_argument("--show",     action="store_true",  help="グラフを画像表示（GUI環境のみ）")
    
    ap.add_argument("--kind", default="ALL", choices=["SSD","HDD","ALL"],
                        help="絞る種類（デフォルト: ALL）")
    ap.add_argument("--caps", nargs="+", default=None,
                        help="絞る容量リスト")
    ap.add_argument("--raw",               action="store_true", help="フィルタ無効")
    ap.add_argument("--brand-only",        action="store_true", help="主要ブランドのみ")
    ap.add_argument("--no-capacity-match", action="store_true", help="容量一致フィルタ無効")
    ap.add_argument("--debug-save-all",    action="store_true", help="各ページHTMLを保存")
    ap.add_argument("--low-price-ratio",   type=float, default=0.3, help="安値異常値判定の係数。中央値 * R 未満を除外（デフォルト: 0.3）")
    ap.add_argument("--high-price-ratio",  type=float, default=2.5, help="高値異常値判定の係数。中央値 * R 超過を除外（デフォルト: 2.5）")
    ap.add_argument("--scale",   type=int, default=100, help="gaugeのバー描画スケール除数")

    sub = ap.add_subparsers(dest="command")
    
    sp_gauge = sub.add_parser("gauge", help="ログからグラフ生成のみ実行")
    sp_gauge.add_argument("--date",    default=_today_str(), help="処理対象の日付 YYYY-MM-DD（デフォルト: 今日）")
    sp_gauge.add_argument("--ssd-dir", default=None,         help="SSDログディレクトリを直接指定")
    sp_gauge.add_argument("--hdd-dir", default=None,         help="HDDログディレクトリを直接指定")

    args = ap.parse_args()

    if args.scrape:
        today = _today_str()
        base  = Path(args.base_dir).expanduser().resolve()

        kind_list: list[str] = []
        if args.kind.upper() in ("SSD", "ALL"):
            kind_list.append("SSD")
        if args.kind.upper() in ("HDD", "ALL"):
            kind_list.append("HDD")

        for kind in kind_list:
            cap_list = SSD_CAPACITIES if kind == "SSD" else HDD_CAPACITIES
            if args.caps:
                cap_list = [c for c in args.caps]

            dir_name = f"{kind.lower()}_scrape_{today}"
            out_dir  = base / dir_name
            out_dir.mkdir(parents=True, exist_ok=True)

            print(f"=== {kind} Scrape Start [{today}] ===")
            print(f"Output Directory: {out_dir}")

            for cap in cap_list:
                log_file = out_dir / f"{kind.lower()}_{cap}.log"
                print(f"Processing {kind} {cap} -> {log_file}")

                orig_stdout = sys.stdout
                with open(str(log_file), "w", encoding="utf-8") as lf:
                    sys.stdout = lf
                    try:
                        run_scrape_one(
                            kind=kind, cap=cap,
                            sleep_sec=args.sleep, jitter_sec=args.jitter,
                            timeout_sec=args.timeout,
                            raw=args.raw, brand_only=args.brand_only,
                            no_capacity_match=args.no_capacity_match,
                            debug_save_all=args.debug_save_all,
                            low_price_ratio=args.low_price_ratio,
                            high_price_ratio=args.high_price_ratio,
                        )
                    finally:
                        sys.stdout = orig_stdout

                csv_pattern = f"amazon_{kind.lower()}_*.csv"
                for csv_file in Path(".").glob(csv_pattern):
                    dest = out_dir / csv_file.name
                    csv_file.rename(dest)

                sleep_with_jitter(args.sleep, args.jitter, label=f"{kind} {cap} inter-cap sleep")

            print("")
            print(f"--- {kind} Summary ---")
            for log_f in sorted(out_dir.glob("*.log")):
                txt = log_f.read_text(encoding="utf-8", errors="replace")
                cap_label = ""
                for line in txt.splitlines():
                    if line.startswith("query(k):"):
                        cap_label = line.replace("query(k):", "").strip()
                m = _ALL_RE.search(txt)
                if m and cap_label:
                    print(f"  {cap_label} -> ALL min {m.group(1)} avg {m.group(2)} max {m.group(3)} count {m.group(4)}")

        print("")
        print("============================================================")
        print("  Starting gauge generation...")
        print("============================================================")
        run_gauge(
            date_str=today,
            base_dir=args.base_dir,
            show=args.show,
            scale=args.scale,
        )

    elif args.command == "gauge":
        run_gauge(
            date_str=args.date,
            base_dir=args.base_dir,
            ssd_dir=args.ssd_dir,
            hdd_dir=args.hdd_dir,
            show=args.show,
            scale=args.scale,
        )
    else:
        ap.print_help()
        return 0
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
