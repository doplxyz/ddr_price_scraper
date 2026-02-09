#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ddr_price_scraper.py
====================
Amazon.co.jp の DDR4/DDR5 メモリ価格スクレイピング＋グラフ生成を一貫実行するツール。

[Version 2.2]
  - 引数をユーザで管理出来るよう見える化
  
[Version 2.1]
  - コマンド体系を刷新 (gauge サブコマンド導入)
  - 引数なし実行時にヘルプを表示
  - グラフのテキストエリア配置を微調整 (HDD版準拠)
  - MAX列とCount列の間隔を詰め、視認性を向上
  - ヘルプを充実させた
  - 単品(規格・容量指定)でのスクレイピング機能を追加

============================================================
[必要条件]
  - Python 3.12 以上
  - 必要な外部ライブラリ:
      matplotlib   … グラフ生成

============================================================
[コマンド体系]
  このツールは2つの実行モードを持っています。

  1) --scrape フラグモード(推奨)
     Amazon.co.jp をスクレイピングして CSV を保存し、
     続けて同じ日付のグラフ画像(PNG)を自動生成します。

     通常は TARGETS 定義の全容量を取得しますが、
     --kind と --capacity を指定することで、特定の1件のみを取得可能です。

  2) gauge サブコマンド(グラフのみ再生成)
     既に保存済みの CSV ディレクトリから、グラフ画像(PNG)だけを作り直します。
     スクレイピングは行いません。

  [入出力の基本]
    - 取得データ保存先(ディレクトリ):
        {base-dir}/ddr_scrape_{YYYY-MM-DD}/
    - 出力グラフ画像(PNG):
        {base-dir}/ddr_price_{YYYY-MM-DD}.png

============================================================
[使い方の例]

  --- 基本:スクレイピング＋グラフ生成(推奨) ---
  # DDR4/DDR5(TARGETS定義の全容量)をスクレイピングして、PNGも出力する
  $ python3 ddr_price_scraper.py --scrape

  --- 単品指定でスクレイピング(特定の容量だけやり直したい場合など) ---
  # DDR5 32GB のみを取得し、その後グラフを更新する
  $ python3 ddr_price_scraper.py --scrape --kind DDR5 --capacity 32GB

  --- 日付を指定してスクレイピング(ディレクトリ名もその日付になる) ---
  $ python3 ddr_price_scraper.py --scrape --date 2026-01-31

  --- 保存場所(基準ディレクトリ)を変更して実行 ---
  # 例:data/ 配下に ddr_scrape_YYYY-MM-DD と PNG を作る
  $ python3 ddr_price_scraper.py --scrape --base-dir ./data

  --- グラフのみ再生成(gauge) ---
  # 今日の日付の ddr_scrape_YYYY-MM-DD から PNG を作り直す
  $ python3 ddr_price_scraper.py gauge

  # 特定の日付(2026-01-31)のログを指定してグラフ化
  $ python3 ddr_price_scraper.py gauge --date 2026-01-31

  # グラフを画面に表示する(GUI環境のみ)
  $ python3 ddr_price_scraper.py gauge --show

  --- 高度なオプション ---
  # ページ遷移のスリープを 10秒に延長(デフォルト: 7.0秒)
  $ python3 ddr_price_scraper.py --scrape --sleep 10.0

============================================================
[オプション一覧(このスクリプトで実際に使えるもの)]
  --scrape                 スクレイピングを実行(終了後にグラフも生成)
  gauge                    グラフのみ再生成(スクレイピングなし)

  --kind KIND              対象規格を指定 (DDR4 または DDR5) ※単体取得時のみ
  --capacity CAP           対象容量を指定 (例: 32GB) ※単体取得時のみ

  --date YYYY-MM-DD        対象日付(保存先ディレクトリ名・PNG名に使う)
                           省略時は「今日」

  --base-dir DIR           基準ディレクトリ(省略時はカレントディレクトリ)
                           例:DIR/ddr_scrape_YYYY-MM-DD/ にCSVが入る

  --sleep SEC              各ターゲット間の待機秒(デフォルト: 7.0)
  --jitter SEC             追加ランダム待機の上限秒(デフォルト: 2.0)
  --timeout SEC            HTTPタイムアウト秒(デフォルト: 30)
  --retries N              リトライ回数(デフォルト: 3)

  --show                   生成したグラフをウィンドウ表示(GUI環境のみ)

  -h / --help              ヘルプ表示
============================================================

"""

from __future__ import annotations

import argparse
import datetime as _dt
import re
import sys
import time
import random
import csv
import statistics
import urllib.request
import urllib.parse
import urllib.error
import http.cookiejar
from html import unescape
from dataclasses import dataclass
from pathlib import Path
from typing import List, Optional, Tuple, Dict

# ============================================================
# LAYOUT CONFIGURATION SECTION
# ============================================================
# このセクションの数値を変更することで、グラフの見栄えを調整できます

# --- Figure Size Settings ---
FIGURE_WIDTH = 11            # グラフ全体の幅,default,16
FIGURE_HEIGHT_BASE = 4.0       # 最小の高さ,default,4.0
FIGURE_HEIGHT_PER_ROW = 0.65   # 1行あたりの追加高さ,default,0.65
FIGURE_HEIGHT_OFFSET = 1.2     # 高さ計算のオフセット,default,1.2
FIGURE_DPI = 90               # 解像度(DPI),default,100

# --- Figure Margin Settings ---
MARGIN_TOP = 0.90              # 上マージン(0.0-1.0),default,0.90
MARGIN_BOTTOM = 0.05           # 下マージン(0.0-1.0),default,0.05
MARGIN_RIGHT = 0.98            # 右マージン(0.0-1.0),default,0.98
MARGIN_LEFT = 0.07             # 左マージン(0.0-1.0),default,0.10

# --- Bar Chart Settings ---
BAR_HEIGHT = 0.62              # バーの高さ,default,0.62
BAR_AVG_RATIO = 0.70            # AVGバーの高さ比率(MAXバーに対する),default,0.7
BAR_MIN_RATIO = 0.40            # MINバーの高さ比率(MAXバーに対する),default,0.4

# --- Bar Color Settings ---
COLOR_MAX = "#FF8888"          # MAX価格の色(赤系),default,#FF8888
COLOR_AVG = "#66CC66"          # AVG価格の色(緑系),default,#66CC66
COLOR_MIN = "#6666FF"          # MIN価格の色(青系),default,#6666FF

# --- Bar Alpha (Transparency) Settings ---
ALPHA_MAX = 0.38               # MAX価格の透明度(0.0-1.0),default,0.8
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
COLUMN_WIDTH_MIN = 1.1         # MIN列の幅,default,1.1
COLUMN_WIDTH_AVG = 1.1         # AVG列の幅,default,1.1
COLUMN_WIDTH_MAX = 1.1         # MAX列の幅,default,1.1
COLUMN_WIDTH_CNT = 0.3         # Count列の幅(他より狭く設定),default,0.5

# --- Title Settings ---
TITLE_FONTSIZE = 16            # タイトルのフォントサイズ,default,16
TITLE_PAD = 20                 # タイトルと図の間隔,default,20

# --- Legend Settings ---
LEGEND_LOCATION = "lower right"        # 凡例の位置,default,lower right
LEGEND_BBOX_X = 1.00                    # 凡例のX位置(bbox_to_anchor),default,1.0
LEGEND_BBOX_Y = 0.99                 # 凡例のY位置(bbox_to_anchor),default,1.01
LEGEND_NCOL = 3                        # 凡例の列数,default,3
LEGEND_FONTSIZE = 10                   # 凡例のフォントサイズ,default,10

# --- Header Row Settings (Column Labels) ---
HEADER_Y_POSITION = -0.70       # ヘッダー行のY位置(負の値で上に配置),default,-0.8
HEADER_FONTSIZE = 10           # ヘッダーのフォントサイズ(現在はコード内で固定),default,10

# --- Data Text Settings ---
DATA_TEXT_FONTSIZE = 10        # データテキストのフォントサイズ,default,10
DATA_COUNT_FONTSIZE = 11       # Count列のフォントサイズ,default,11

# --- Y-Axis Label Settings ---
Y_LABEL_FONTSIZE = 12          # Y軸ラベルのフォントサイズ,default,12

# ============================================================
# END OF LAYOUT CONFIGURATION SECTION
# ============================================================


# ============================================================
# Global Settings
# ============================================================
VERSION = "2.2"

TARGETS = {
    "DDR4": ["4GB", "8GB",  "16GB", "32GB", "64GB", "128GB"],
    "DDR5": ["8GB", "16GB", "32GB", "48GB", "64GB", "96GB", "128GB"],
}

AMAZON_BASE_URL = "https://www.amazon.co.jp"

# ============================================================
# Data Models & Regex
# ============================================================
@dataclass
class StatRow:
    kind: str
    capacity: int
    label: str
    min_price: int
    avg_price: int
    max_price: int
    count: int

    @property
    def sort_key(self):
        k_idx = 0 if self.kind == "DDR4" else 1
        return (k_idx, self.capacity)

BLOCK_PATTERNS = [
    r"Robot Check",
    r"Enter the characters you see below",
    r"/errors/validateCaptcha",
    r"申し訳ございません",
    r"画像に表示されている文字を入力してください",
]
BLOCK_RE = re.compile("|".join(BLOCK_PATTERNS), re.IGNORECASE)

ASIN_RE = re.compile(r'data-asin="([A-Z0-9]{10})"')
TITLE_RES = [
    re.compile(r'<h2[^>]*>.*?<span[^>]*>(.*?)</span>.*?</h2>', re.IGNORECASE | re.DOTALL),
    re.compile(r'<span[^>]*class="[^"]*a-text-normal[^"]*"[^>]*>(.*?)</span>', re.IGNORECASE | re.DOTALL),
]
PRICE_WHOLE_RE = re.compile(r'class="a-price-whole"[^>]*>([\d,]+)<', re.IGNORECASE)
YEN_RE = re.compile(r"[￥¥]\s*([\d,]+)")
BAD_SELLER_RE = re.compile(r"「おすすめ出品」の要件を満たす出品はありません", re.IGNORECASE)

DDR4_RE = re.compile(r"\bDDR4\b", re.IGNORECASE)
DDR5_RE = re.compile(r"\bDDR5\b", re.IGNORECASE)
MEM_HINT_RE = re.compile(r"メモリ|memory|RAM|DIMM|SODIMM|SO-DIMM|UDIMM|PC4-|PC5-", re.IGNORECASE)
NOT_MEMORY_RE = re.compile(r"SSD|HDD|NVMe|M\.2|USB|Motherboard|CPU|Ryzen|Core|Laptop|GPU|GeForce|Case|Cooler|Fan|Cable|Adapter|Tester", re.IGNORECASE)

GB_SCRAPE_RE = re.compile(r"(\d{1,3})\s*GB", re.IGNORECASE)
KIT_X_RE = re.compile(r"(\d)\s*[x×\*]\s*(\d{1,3})\s*GB", re.IGNORECASE)
KIT_REV_RE = re.compile(r"(\d{1,3})\s*GB\s*[x×\*]\s*(\d)", re.IGNORECASE)

# ============================================================
# [BLOCK] HTTP & Utils
# ============================================================
CJ = http.cookiejar.CookieJar()
OPENER = urllib.request.build_opener(urllib.request.HTTPCookieProcessor(CJ))
COMMON_HEADERS = {
    "User-Agent": "Mozilla/5.0 (X11; Linux x86_64; rv:127.0) Gecko/20100101 Firefox/127.0",
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "ja,en-US;q=0.7,en;q=0.3",
    "Connection": "close",
    "DNT": "1",
    "Upgrade-Insecure-Requests": "1",
}

def log_progress(msg: str) -> None:
    print(f"# {msg}", flush=True)

def sleep_with_indicator(sec: float, label: str):
    if sec <= 0: return
    sys.stdout.write(f"# {label}: wait {sec:.1f}s ")
    sys.stdout.flush()
    time.sleep(sec)
    sys.stdout.write("\n")

def sleep_with_jitter(base_sec: float, jitter_max: float, label: str = "") -> None:
    j = random.random() * max(0.0, jitter_max)
    total_sec = max(0.0, base_sec) + j
    if label:
        sleep_with_indicator(total_sec, label)
    else:
        time.sleep(total_sec)

def calc_median(values: List[int]) -> int:
    if not values: return 0
    return int(round(statistics.median(values)))

def fetch_html(url: str, timeout_sec: int, retries: int = 3) -> str:
    headers = dict(COMMON_HEADERS)
    headers["Referer"] = AMAZON_BASE_URL + "/"
    req = urllib.request.Request(url, headers=headers, method="GET")
    
    waits = [2, 5, 10, 20]
    for i in range(retries + 1):
        if i > 0:
            w = waits[min(i-1, len(waits)-1)]
            sleep_with_indicator(w, f"Retry {i}/{retries}")
        try:
            with OPENER.open(req, timeout=timeout_sec) as resp:
                charset = resp.headers.get_content_charset() or "utf-8"
                return resp.read().decode(charset, errors="replace")
        except urllib.error.HTTPError as e:
            log_progress(f"HTTPError {e.code} (attempt {i+1})")
        except urllib.error.URLError as e:
            log_progress(f"URLError: {e.reason} (attempt {i+1})")
        except Exception as e:
            log_progress(f"UnexpectedError: {e} (attempt {i+1})")
    raise RuntimeError(f"Fetch failed after {retries+1} attempts")

# ============================================================
# [BLOCK] HTML Parsing
# ============================================================
def find_first_asin(html: str) -> Optional[str]:
    m = ASIN_RE.search(html)
    return m.group(1) if m else None

def extract_price_from_whole_snippet(html_snippet: str) -> Optional[int]:
    m = PRICE_WHOLE_RE.search(html_snippet)
    if not m: return None
    raw = m.group(1).replace(",", "").strip()
    try:
        return int(raw)
    except ValueError:
        return None

def extract_yen_price(text: str) -> Optional[int]:
    m = YEN_RE.search(text)
    if not m: return None
    raw = m.group(1).replace(",", "").strip()
    try:
        return int(raw)
    except ValueError:
        return None

def extract_title(html_snippet: str) -> str:
    for regex in TITLE_RES:
        m = regex.search(html_snippet)
        if m:
            title_raw = m.group(1)
            title_unescaped = unescape(title_raw)
            title_clean = re.sub(r"<[^>]+>", "", title_unescaped).strip()
            return title_clean
    return ""

def is_captcha_blocked(html: str) -> bool:
    return BLOCK_RE.search(html) is not None

def is_bad_seller_page(html: str) -> bool:
    return BAD_SELLER_RE.search(html) is not None

def guess_ddr_kind(text: str) -> Optional[str]:
    if DDR5_RE.search(text): return "DDR5"
    if DDR4_RE.search(text): return "DDR4"
    return None

def looks_like_memory(text: str) -> bool:
    if NOT_MEMORY_RE.search(text): return False
    return bool(MEM_HINT_RE.search(text))

def extract_capacity_gb(text: str) -> Optional[int]:
    kit_x = KIT_X_RE.search(text)
    if kit_x:
        qty = int(kit_x.group(1))
        per_gb = int(kit_x.group(2))
        return qty * per_gb
    kit_rev = KIT_REV_RE.search(text)
    if kit_rev:
        per_gb = int(kit_rev.group(1))
        qty = int(kit_rev.group(2))
        return qty * per_gb
    gb = GB_SCRAPE_RE.search(text)
    if gb:
        return int(gb.group(1))
    return None

# ============================================================
# [BLOCK] Scraping Logic
# ============================================================
def build_search_url(kind_str: str, cap_str: str) -> str:
    query = f"{kind_str} {cap_str} メモリ"
    params = {
        "k": query,
        "__mk_ja_JP": "カタカナ",
        "crid": "FAKECRID123",
        "sprefix": query,
        "ref": "nb_sb_noss_1",
    }
    return AMAZON_BASE_URL + "/s?" + urllib.parse.urlencode(params)

def split_items(html: str) -> List[str]:
    """
    HTML内のdata-asin属性を持つ要素を検出し、各商品のチャンクに分割する
    旧バージョンのparse_search_results_robustのロジックを使用
    """
    matches = list(ASIN_RE.finditer(html))
    chunks = []
    
    if not matches:
        return chunks
    
    for idx, m in enumerate(matches):
        start = m.start()
        if (idx + 1) < len(matches):
            end = matches[idx + 1].start()
        else:
            end = min(len(html), start + 10000)
        
        chunk = html[start:end]
        chunks.append(chunk)
    
    return chunks

def parse_product_chunk(chunk: str, target_kind: str, target_cap_gb: int) -> Optional[Tuple[int, str]]:
    # BAD_SELLER判定（旧スクリプトと同様にチャンク単位でチェック）
    if BAD_SELLER_RE.search(chunk):
        return None
    
    title = extract_title(chunk)
    if not title: return None
    
    detected_kind = guess_ddr_kind(title)
    if detected_kind != target_kind: return None
    
    if not looks_like_memory(title): return None
    
    cap = extract_capacity_gb(title)
    if cap != target_cap_gb: return None
    
    price = extract_price_from_whole_snippet(chunk)
    if price is None: return None
    
    return (price, title)

def run_scrape_one(kind: str, cap_str: str, out_dir: Path, 
                   sleep_sec: float, jitter_sec: float, 
                   timeout_sec: int, retries: int):
    cap_val = int(cap_str.replace("GB", ""))
    label = f"amazon_{kind.lower()}_{cap_str.lower()}"
    out_csv = out_dir / f"{label}.csv"
    
    log_progress(f"Scraping: {kind} {cap_str}")
    url = build_search_url(kind, cap_str)
    
    try:
        html = fetch_html(url, timeout_sec, retries)
    except RuntimeError as e:
        log_progress(f"[FAIL] {label} -> {e}")
        return
    
    # デバッグ用: HTMLを保存
    debug_html = out_dir / f"{label}_debug.html"
    try:
        with open(debug_html, "w", encoding="utf-8") as f:
            f.write(html)
    except:
        pass
    
    if is_captcha_blocked(html):
        log_progress(f"[WARN] {label} -> CAPTCHA detected! Abort.")
        return
    
    # Bad seller page判定を削除（商品が見つからない場合は後で判定）
    
    chunks = split_items(html)
    log_progress(f"Found {len(chunks)} candidate chunks")
    
    results = []
    skipped_reasons = {"bad_seller": 0, "no_title": 0, "wrong_kind": 0, "not_memory": 0, "wrong_capacity": 0, "no_price": 0}
    
    for chunk in chunks:
        # BAD_SELLER判定
        if BAD_SELLER_RE.search(chunk):
            skipped_reasons["bad_seller"] += 1
            continue
        
        # タイトル取得
        title = extract_title(chunk)
        if not title:
            skipped_reasons["no_title"] += 1
            continue
        
        # 規格判定
        detected_kind = guess_ddr_kind(title)
        if detected_kind != kind:
            skipped_reasons["wrong_kind"] += 1
            continue
        
        # メモリかどうかの判定
        if not looks_like_memory(title):
            skipped_reasons["not_memory"] += 1
            continue
        
        # 容量判定
        cap = extract_capacity_gb(title)
        if cap != cap_val:
            skipped_reasons["wrong_capacity"] += 1
            continue
        
        # 価格取得
        price = extract_price_from_whole_snippet(chunk)
        if price is None:
            skipped_reasons["no_price"] += 1
            continue
        
        results.append((price, title))
    
    # スキップ理由のサマリを表示
    log_progress(f"Skipped: bad_seller={skipped_reasons['bad_seller']}, no_title={skipped_reasons['no_title']}, "
                 f"wrong_kind={skipped_reasons['wrong_kind']}, not_memory={skipped_reasons['not_memory']}, "
                 f"wrong_capacity={skipped_reasons['wrong_capacity']}, no_price={skipped_reasons['no_price']}")
    
    if not results:
        log_progress(f"[WARN] {label} -> No valid items found. Check {label}_debug.html")
        return
    
    if not results:
        log_progress(f"[WARN] {label} -> No valid items found.")
        return
    
    with open(out_csv, "w", newline="", encoding="utf-8") as f:
        writer = csv.writer(f)
        writer.writerow(["Price", "Title"])
        for (price, title) in results:
            writer.writerow([price, title])
    
    log_progress(f"[OK] {label} -> {len(results)} items saved to {out_csv.name}")

# ============================================================
# [BLOCK] CSV Loading & Stats
# ============================================================
def load_stats_from_dir(data_dir: Path, outlier_lo: float = 0.3, outlier_hi: float = 2.5) -> List[StatRow]:
    if not data_dir.exists(): return []
    
    rows = []
    for csv_path in sorted(data_dir.glob("*.csv")):
        stem = csv_path.stem
        parts = stem.split("_")
        
        # ファイル名形式の判定と解析
        # パターン1: amazon_ddr4_8gb.csv (3要素以上)
        # パターン2: DDR4_8GB.csv (2要素)
        kind = None
        cap_str = None
        
        if len(parts) >= 3:
            # amazon_ddr4_8gb形式を想定
            kind = parts[1].upper()
            cap_str = parts[2]
        elif len(parts) >= 2:
            # DDR4_8GB形式を想定
            kind = parts[0].upper()
            cap_str = parts[1]
        else:
            continue  # 要素が足りない場合はスキップ
        
        # 規格チェック: DDR4またはDDR5でなければスキップ
        if kind not in ["DDR4", "DDR5"]: continue
        
        # 容量文字列から数値を抽出
        cap_val_str = cap_str.replace("GB", "").replace("gb", "").strip()
        try:
            cap_val = int(cap_val_str)
        except ValueError:
            continue  # 数値に変換できない場合はスキップ
        
        prices = []
        with open(csv_path, "r", encoding="utf-8") as f:
            reader = csv.DictReader(f)
            for row in reader:
                try:
                    p = int(row["Price"])
                    prices.append(p)
                except (ValueError, KeyError):
                    pass
        
        if not prices: continue
        
        med = calc_median(prices)
        lo_thr = int(med * outlier_lo)
        hi_thr = int(med * outlier_hi)
        valid = [p for p in prices if lo_thr <= p <= hi_thr]
        
        if not valid: valid = prices
            
        rows.append(StatRow(
            kind=kind,
            capacity=cap_val,
            label=f"{kind} {cap_val}GB",
            min_price=min(valid),
            avg_price=int(sum(valid)/len(valid)),
            max_price=max(valid),
            count=len(valid)
        ))
    rows.sort(key=lambda x: x.sort_key)
    return rows

# ============================================================
# [BLOCK] Graph Generation
# ============================================================
def plot_price_gauge(rows: List[StatRow], out_path: Path, date_str: str, prev_rows: List[StatRow] = None, show: bool = False):
    """
    グラフ生成関数
    
    レイアウト設定は、スクリプト冒頭の「LAYOUT CONFIGURATION SECTION」で
    定義された変数を使用します。
    """
    if not rows: return
    import matplotlib
    if not show: matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.ticker import FuncFormatter

    # [LABEL] Previous Data Mapping
    prev_map = {r.label: r for r in (prev_rows or [])}
    
    # [LABEL] Data Extraction
    labels = [r.label for r in rows]
    mins = [r.min_price for r in rows]
    avgs = [r.avg_price for r in rows]
    maxs = [r.max_price for r in rows]

    global_max = max(maxs) if maxs else 10000
    
    # [LABEL] X-Axis Limit Calculation
    # 最大バーがグラフ幅の指定位置に来るように調整
    xlim_right = global_max / X_AXIS_MAX_BAR_POSITION
    
    # [LABEL] Text Start Position Calculation
    col_start_x = global_max * TEXT_START_MULTIPLIER
    if col_start_x < xlim_right * TEXT_START_MIN_RATIO:
        col_start_x = xlim_right * TEXT_START_MIN_RATIO
        
    # [LABEL] Column Layout Calculation
    text_width = xlim_right - col_start_x
    
    w_min = COLUMN_WIDTH_MIN
    w_avg = COLUMN_WIDTH_AVG
    w_max = COLUMN_WIDTH_MAX
    w_cnt = COLUMN_WIDTH_CNT
    total_w = w_min + w_avg + w_max + w_cnt
    w_unit = text_width / total_w
    
    # 各列の右端位置を計算(ha='right'のため)
    x_min_txt = col_start_x + w_unit * w_min
    x_avg_txt = x_min_txt + w_unit * w_avg
    x_max_txt = x_avg_txt + w_unit * w_max
    x_cnt_txt = x_max_txt + w_unit * w_cnt
    
    # [LABEL] Figure Size Calculation
    fig_h = max(FIGURE_HEIGHT_BASE, FIGURE_HEIGHT_PER_ROW * len(rows) + FIGURE_HEIGHT_OFFSET)
    fig, ax = plt.subplots(figsize=(FIGURE_WIDTH, fig_h), dpi=FIGURE_DPI)
    
    # [LABEL] Figure Margins
    plt.subplots_adjust(
        top=MARGIN_TOP, 
        bottom=MARGIN_BOTTOM, 
        right=MARGIN_RIGHT, 
        left=MARGIN_LEFT
    )

    # [LABEL] Y-Axis Positions
    y_pos = list(range(len(rows)))
    
    # [LABEL] Bar Drawing
    ax.barh(y_pos, maxs, color=COLOR_MAX, alpha=ALPHA_MAX, height=BAR_HEIGHT, label="MAX")
    ax.barh(y_pos, avgs, color=COLOR_AVG, alpha=ALPHA_AVG, height=BAR_HEIGHT*BAR_AVG_RATIO, label="AVG")
    ax.barh(y_pos, mins, color=COLOR_MIN, alpha=ALPHA_MIN, height=BAR_HEIGHT*BAR_MIN_RATIO, label="MIN")
    
    # [LABEL] Y-Axis Labels
    ax.set_yticks(y_pos)
    ax.set_yticklabels(labels, fontsize=Y_LABEL_FONTSIZE, fontweight='bold')
    ax.invert_yaxis()
    
    # [LABEL] X-Axis Settings
    ax.set_xlim(0, xlim_right)
    ax.xaxis.set_major_formatter(FuncFormatter(lambda x, p: f"{int(x):,}"))
    ax.grid(axis='x', linestyle=':', alpha=0.5)
    
    # [LABEL] Spine Visibility
    ax.spines['right'].set_visible(False)
    ax.spines['top'].set_visible(False)
    ax.spines['left'].set_visible(False)
    
    # [LABEL] Title
    ax.set_title(
        f"DDR4 & DDR5 Price Gauge {date_str} (JPY)", 
        fontsize=TITLE_FONTSIZE, 
        fontweight='bold', 
        pad=TITLE_PAD
    )
    
    # [LABEL] Legend
    handles, legend_labels = ax.get_legend_handles_labels()
    ax.legend(
        handles[::-1], 
        legend_labels[::-1], 
        loc=LEGEND_LOCATION, 
        bbox_to_anchor=(LEGEND_BBOX_X, LEGEND_BBOX_Y), 
        ncol=LEGEND_NCOL, 
        frameon=False, 
        fontsize=LEGEND_FONTSIZE
    )

    # [LABEL] Header Row (Column Labels)
    head_y = HEADER_Y_POSITION
    ax.text(x_min_txt, head_y, "MIN", color='blue', fontweight='bold', ha='right')
    ax.text(x_avg_txt, head_y, "AVG", color='green', fontweight='bold', ha='right')
    ax.text(x_max_txt, head_y, "MAX", color='red', fontweight='bold', ha='right')
    ax.text(x_cnt_txt, head_y, "Count", color='black', fontweight='bold', ha='right')
    
    # [LABEL] Price Difference Formatting Function
    def fmt_diff(curr, prev):
        txt = f"{curr:,}"
        if prev is None: return txt + " (-)"
        diff = curr - prev
        if diff > 0: return f"{txt} (+{diff:,})"
        if diff < 0: return f"{txt} ({diff:,})"
        return f"{txt} (±0)"

    # [LABEL] Data Text Rendering
    for i, r in enumerate(rows):
        pr = prev_map.get(r.label)
        t_min = fmt_diff(r.min_price, pr.min_price if pr else None)
        t_avg = fmt_diff(r.avg_price, pr.avg_price if pr else None)
        t_max = fmt_diff(r.max_price, pr.max_price if pr else None)
        
        ax.text(x_min_txt, i, t_min, va='center', ha='right', fontsize=DATA_TEXT_FONTSIZE, fontfamily='monospace')
        ax.text(x_avg_txt, i, t_avg, va='center', ha='right', fontsize=DATA_TEXT_FONTSIZE, fontfamily='monospace')
        ax.text(x_max_txt, i, t_max, va='center', ha='right', fontsize=DATA_TEXT_FONTSIZE, fontfamily='monospace')
        ax.text(x_cnt_txt, i, str(r.count), va='center', ha='right', fontsize=DATA_COUNT_FONTSIZE)

    # [LABEL] Save & Display
    plt.savefig(out_path)
    if show: plt.show()
    plt.close()

# ============================================================
# [BLOCK] Main Orchestrator
# ============================================================
def main():
    # コマンドライン引数の処理
    # 引数がスクリプト名のみの場合はヘルプを表示
    if len(sys.argv) == 1:
        print(__doc__)
        return 0

    ap = argparse.ArgumentParser(description="DDR Price Scraper Tool", add_help=False)
    
    # サブコマンド用の引数 (nargs='?' で省略可能に)
    ap.add_argument("mode", nargs="?", choices=["gauge"], help="Subcommand: gauge to regen graph")
    
    ap.add_argument("--scrape", action="store_true", help="Execute scraping")
    ap.add_argument("--date", default=_dt.date.today().strftime("%Y-%m-%d"), help="Target date YYYY-MM-DD")
    ap.add_argument("--base-dir", default=".", help="Base directory")
    
    # 単体スクレイピング用の追加引数
    ap.add_argument("--kind", choices=["DDR4", "DDR5"], help="Target DDR Kind (e.g. DDR4)")
    ap.add_argument("--capacity", help="Target capacity (e.g. 32GB)")

    ap.add_argument("--sleep", type=float, default=10.0, help="Wait time (sec)")
    ap.add_argument("--jitter", type=float, default=2.0, help="Jitter time (sec)")
    ap.add_argument("--timeout", type=int, default=30, help="HTTP timeout (sec)")
    ap.add_argument("--retries", type=int, default=3, help="Retry count")
    
    ap.add_argument("--show", action="store_true", help="Show GUI window")
    ap.add_argument("-h", "--help", action="help", help="show this help message and exit")

    args = ap.parse_args()
    
    if not args.scrape and args.mode != 'gauge':
        print(__doc__)
        return 0

    base_dir = Path(args.base_dir).resolve()
    target_dir = base_dir / f"ddr_scrape_{args.date}"
    
    # [LABEL] Scrape Phase
    if args.scrape:
        target_dir.mkdir(parents=True, exist_ok=True)
        print(f"=== Scraping Start [{args.date}] (v{VERSION}) ===")
        print(f"Config: Sleep={args.sleep}s (+0~{args.jitter}s), Retry={args.retries}")
        
        # スクレイピング対象の決定
        scrape_targets = {}
        if args.kind and args.capacity:
            # 単体指定あり
            scrape_targets[args.kind] = [args.capacity]
            print(f"Target: Single Mode -> {args.kind} {args.capacity}")
        elif args.kind or args.capacity:
            # どちらか片方のみ指定された場合はエラーにする
            print("[Error] --kind and --capacity must be used together for single target scraping.")
            return 1
        else:
            # 指定なし＝全量
            scrape_targets = TARGETS
            print(f"Target: Batch Mode (All targets)")

        for kind, caps in scrape_targets.items():
            for cap in caps:
                run_scrape_one(kind, cap, target_dir, 
                               args.sleep, args.jitter, args.timeout, args.retries)
                sleep_with_jitter(args.sleep, args.jitter, "Next Target")
        print("\n=== Scraping Finished ===")
    
    # [LABEL] Graph Phase
    if not target_dir.exists():
        if args.scrape:
            print(f"[Error] Scrape failed to create dir: {target_dir}")
        else:
            print(f"[Error] Directory not found: {target_dir}")
            print("Hint: Run with --scrape first.")
        return 1
        
    print(f"=== Generating Graph [{args.date}] ===")
    
    rows = load_stats_from_dir(target_dir, 0.3, 2.5)
    
    if not rows:
        print("[Error] No valid CSVs found in directory.")
        return 1
        
    try:
        current_dt = _dt.datetime.strptime(args.date, "%Y-%m-%d").date()
        prev_date = (current_dt - _dt.timedelta(days=1)).strftime("%Y-%m-%d")
        prev_dir = base_dir / f"ddr_scrape_{prev_date}"
        prev_rows = load_stats_from_dir(prev_dir, 0.3, 2.5) if prev_dir.exists() else []
    except ValueError:
        prev_rows = []
    
    out_png = base_dir / f"ddr_price_{args.date}.png"
    plot_price_gauge(rows, out_png, args.date, prev_rows, args.show)
    
    print(f"[Success] Graph saved to: {out_png}")
    print("-" * 65)
    print(f"{'Label':<15} | {'Min':>9} | {'Avg':>9} | {'Max':>9} | {'Cnt':>3}")
    print("-" * 65)
    for r in rows:
        print(f"{r.label:<15} | {r.min_price:>9,} | {r.avg_price:>9,} | {r.max_price:>9,} | {r.count:>3}")
    print("-" * 65)
    return 0

if __name__ == "__main__":
    sys.exit(main())
