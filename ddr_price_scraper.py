#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ddr_price_scraper.py
====================
Amazon.co.jp の DDR4/DDR5 メモリ価格スクレイピング＋グラフ生成を一貫実行するツール。

[Version 2.2]
  - コンフィグ変数の整理（価格フィルタ係数、スリープ時間を定数化）
  - 内部バージョン更新

[Version 2.1]
  - コマンド体系を刷新 (gauge サブコマンド導入)
  - 引数なし実行時にヘルプを表示
  - グラフのテキストエリア配置を微調整 (HDD版準拠)
  - MAX列とCount列の間隔を詰め、視認性を向上
  - ヘルプを充実させた
  - 単品（規格・容量指定）でのスクレイピング機能を追加

============================================================
[必要条件]
  - Python 3.12 以上
  - 必要な外部ライブラリ:
      matplotlib   … グラフ生成

============================================================
[コマンド体系]
  このツールは2つの実行モードを持っています。

  1) --scrape フラグモード（推奨）
     Amazon.co.jp をスクレイピングして CSV を保存し、
     続けて同じ日付のグラフ画像（PNG）を自動生成します。

     通常は TARGETS 定義の全容量を取得しますが、
     --kind と --capacity を指定することで、特定の1件のみを取得可能です。

  2) gauge サブコマンド（グラフのみ再生成）
     既に保存済みの CSV ディレクトリから、グラフ画像（PNG）だけを作り直します。
     スクレイピングは行いません。

  [入出力の基本]
    - 取得データ保存先（ディレクトリ）:
        {base-dir}/ddr_scrape_{YYYY-MM-DD}/
    - 出力グラフ画像（PNG）:
        {base-dir}/ddr_price_{YYYY-MM-DD}.png

============================================================
[使い方の例]

  --- 基本：スクレイピング＋グラフ生成（推奨） ---
  # DDR4/DDR5（TARGETS定義の全容量）をスクレイピングして、PNGも出力する
  $ python3 ddr_price_scraper.py --scrape

  --- 単品指定でスクレイピング（特定の容量だけやり直したい場合など） ---
  # DDR5 32GB のみを取得し、その後グラフを更新する
  $ python3 ddr_price_scraper.py --scrape --kind DDR5 --capacity 32GB

  --- 日付を指定してスクレイピング（ディレクトリ名もその日付になる） ---
  $ python3 ddr_price_scraper.py --scrape --date 2026-01-31

  --- 保存場所（基準ディレクトリ）を変更して実行 ---
  # 例：data/ 配下に ddr_scrape_YYYY-MM-DD と PNG を作る
  $ python3 ddr_price_scraper.py --scrape --base-dir ./data

  --- グラフのみ再生成（gauge） ---
  # 今日の日付の ddr_scrape_YYYY-MM-DD から PNG を作り直す
  $ python3 ddr_price_scraper.py gauge

  # 特定の日付(2026-01-31)のログを指定してグラフ化
  $ python3 ddr_price_scraper.py gauge --date 2026-01-31

  # グラフを画面に表示する（GUI環境のみ）
  $ python3 ddr_price_scraper.py gauge --show

  --- 高度なオプション ---
  # ページ遷移のスリープを 10秒に延長（デフォルト: 7.0秒）
  $ python3 ddr_price_scraper.py --scrape --sleep 10.0

============================================================
[オプション一覧（このスクリプトで実際に使えるもの）]
  --scrape                 スクレイピングを実行（終了後にグラフも生成）
  gauge                    グラフのみ再生成（スクレイピングなし）

  --kind KIND              対象規格を指定 (DDR4 または DDR5) ※単体取得時のみ
  --capacity CAP           対象容量を指定 (例: 32GB) ※単体取得時のみ

  --date YYYY-MM-DD        対象日付（保存先ディレクトリ名・PNG名に使う）
                           省略時は「今日」

  --base-dir DIR           基準ディレクトリ（省略時はカレントディレクトリ）
                           例：DIR/ddr_scrape_YYYY-MM-DD/ にCSVが入る

  --sleep SEC              各ターゲット間の待機秒（デフォルト: 7.0）
  --jitter SEC             追加ランダム待機の上限秒（デフォルト: 2.0）
  --timeout SEC            HTTPタイムアウト秒（デフォルト: 30）
  --retries N              リトライ回数（デフォルト: 3）

  --show                   生成したグラフをウィンドウ表示（GUI環境のみ）

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
# Global Settings
# ============================================================
VERSION = "2.2"

# ============================================================
# User Configuration
# ============================================================
# Price filtering settings (Cutoff thresholds relative to Median)
# Lower limit: Median * RATIO. Prices below this are excluded (e.g. 0.3 = 30% of median).
PRICE_FILTER_LOWER_RATIO = 0.3

# Upper limit: Median * RATIO. Prices above this are excluded.
# User note: "Supposed to be 95%" (0.95)
PRICE_FILTER_UPPER_RATIO = 0.95

# Sleep settings (seconds)
DEFAULT_SLEEP_SEC = 7.0
DEFAULT_JITTER_SEC = 2.0


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
# HTTP & Utils
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
            if e.code in (404,): break
        except Exception as e:
            log_progress(f"Error {type(e).__name__} (attempt {i+1})")
    
    log_progress(f"Failed to fetch after retries: {url}")
    return ""

# ============================================================
# Scraping Logic
# ============================================================
def extract_ddr_gen(title: str) -> str:
    if DDR5_RE.search(title): return "DDR5"
    if DDR4_RE.search(title): return "DDR4"
    return ""

def classify_ddr_item(title: str, target_gen: str, target_gb: Optional[int]) -> Tuple[str, str]:
    if NOT_MEMORY_RE.search(title): return ("other", "not_memory_keyword")
    gen = extract_ddr_gen(title)
    if not gen: return ("other", "no_ddr_gen")
    if target_gen and gen != target_gen: return ("other", f"gen_mismatch({gen})")
    if not MEM_HINT_RE.search(title): return ("other", "no_memory_hint")
    if target_gb is not None:
        gb_matches = GB_SCRAPE_RE.findall(title)
        if gb_matches:
            gb_vals = [int(g) for g in gb_matches]
            if target_gb not in gb_vals:
                return ("other", f"capacity_mismatch(target={target_gb})")
    return ("memory", "")

def extract_capacity_kit(title: str) -> int:
    kit_x = KIT_X_RE.search(title)
    if kit_x:
        n, per = int(kit_x.group(1)), int(kit_x.group(2))
        return n * per
    kit_rev = KIT_REV_RE.search(title)
    if kit_rev:
        per, n = int(kit_rev.group(1)), int(kit_rev.group(2))
        return n * per
    gb_matches = GB_SCRAPE_RE.findall(title)
    if gb_matches:
        return int(gb_matches[0])
    return 0

def parse_search_results_robust(html: str) -> List[Dict]:
    matches = list(ASIN_RE.finditer(html))
    rows = []
    if not matches: return rows

    for idx, m in enumerate(matches):
        asin = m.group(1)
        start = m.start()
        if (idx + 1) < len(matches):
            end = matches[idx + 1].start()
        else:
            end = min(len(html), start + 10000)
        
        chunk = html[start:end]
        if BAD_SELLER_RE.search(chunk): continue

        title = ""
        for tr in TITLE_RES:
            tm = tr.search(chunk)
            if tm:
                title = unescape(re.sub(r'<[^>]+>', '', tm.group(1))).strip()
                break
        if not title: continue

        price = None
        pm = PRICE_WHOLE_RE.search(chunk)
        if pm:
            try: price = int(pm.group(1).replace(',', ''))
            except: pass
        if price is None:
            ym = YEN_RE.search(chunk)
            if ym:
                try: price = int(ym.group(1).replace(',', ''))
                except: pass
        
        url = f"{AMAZON_BASE_URL}/dp/{asin}"
        rows.append({ "asin": asin, "title": title, "price_yen": price, "url": url })
    return rows

def run_scrape_one(kind: str, cap: str, out_dir: Path, sleep_sec: float, jitter_sec: float, timeout_sec: int, retries: int):
    query_str = f"{kind} {cap}"
    url = f"{AMAZON_BASE_URL}/s?k={kind}+{cap}&ref=nb_sb_noss_1"
    
    log_progress(f"Fetching: {query_str} ...")
    target_gb = None
    try: target_gb = int(cap.replace("GB", ""))
    except: pass
    
    html = fetch_html(url, timeout_sec, retries)
    if not html:
        log_progress("  [Fail] No HTML content.")
        return None
    if BLOCK_RE.search(html):
        log_progress("  [Fail] Blocked/Captcha detected.")
        return None
    
    rows = parse_search_results_robust(html)
    log_progress(f"  Raw Items: {len(rows)}")
    if not rows:
        log_progress("  [Warn] 0 items found. Skipping CSV save.")
        return None
    
    filtered = []
    for r in rows:
        cat, reason = classify_ddr_item(r["title"], kind, target_gb)
        if cat == "memory":
            total_gb = extract_capacity_kit(r["title"])
            if target_gb and total_gb > 0 and total_gb != target_gb: continue
            r["total_gb"] = total_gb if total_gb > 0 else target_gb
            filtered.append(r)
    
    log_progress(f"  Filtered Items: {len(filtered)}")
    if not filtered:
        log_progress("  [Warn] 0 items after filtering. Skipping CSV save.")
        return None

    csv_name = f"amazon_{kind.lower()}_{cap.lower()}.csv"
    csv_path = out_dir / csv_name
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        fieldnames = ["asin", "title", "price_yen", "url", "total_gb"]
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        for row in filtered:
            out = {k: row.get(k, "") for k in fieldnames}
            w.writerow(out)
    return csv_path

# ============================================================
# Stats & Plotting Logic
# ============================================================
def load_stats_from_dir(dirpath: Path, low_ratio: float, high_ratio: float) -> List[StatRow]:
    rows = []
    if not dirpath.exists(): return rows
    
    for p in dirpath.glob("*.csv"):
        name_upper = p.stem.upper()
        kind = "DDR5" if "DDR5" in name_upper else ("DDR4" if "DDR4" in name_upper else None)
        if not kind: continue
        
        parts = name_upper.split('_')
        cap_val = 0
        for part in parts:
            if part.endswith("GB") and part[:-2].isdigit():
                cap_val = int(part[:-2])
                break
        if cap_val == 0: continue
            
        prices = []
        try:
            with open(p, "r", encoding="utf-8") as f:
                reader = csv.DictReader(f)
                for r in reader:
                    val = r.get("price_yen") or r.get("price")
                    if val and str(val).isdigit():
                        prices.append(int(val))
        except: continue
            
        if not prices: continue
        med = calc_median(prices)
        valid = [x for x in prices if (med * low_ratio) <= x <= (med * high_ratio)]
        if not valid: continue
            
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

def plot_price_gauge(rows: List[StatRow], out_path: Path, date_str: str, prev_rows: List[StatRow] = None, show: bool = False):
    if not rows: return
    import matplotlib
    if not show: matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.ticker import FuncFormatter

    prev_map = {r.label: r for r in (prev_rows or [])}
    labels = [r.label for r in rows]
    mins = [r.min_price for r in rows]
    avgs = [r.avg_price for r in rows]
    maxs = [r.max_price for r in rows]

    global_max = max(maxs) if maxs else 10000
    
    # x-axis limit: Scale so max bar is at roughly 60% position
    xlim_right = global_max / 0.60
    
    # Text Start Position Calculation
    # User request: col_start_x = global_max * 1.00
    # Threshold: if less than xlim_right * 0.60, use 0.60
    col_start_x = global_max * 1.00
    if col_start_x < xlim_right * 0.60:
        col_start_x = xlim_right * 0.60
        
    # Calculate column layout
    # Available width for text
    text_width = xlim_right - col_start_x
    
    # Define weights for column spacing (MAX and CNT are tighter)
    # MIN: 1.1, AVG: 1.1, MAX: 1.1, CNT: 0.5
    w_min, w_avg, w_max, w_cnt = 1.1, 1.1, 1.1, 0.5
    total_w = w_min + w_avg + w_max + w_cnt
    w_unit = text_width / total_w
    
    # Calculate RIGHT edges for each column (since ha='right')
    x_min_txt = col_start_x + w_unit * w_min
    x_avg_txt = x_min_txt + w_unit * w_avg
    x_max_txt = x_avg_txt + w_unit * w_max
    x_cnt_txt = x_max_txt + w_unit * w_cnt
    
    fig_h = max(4.0, 0.65 * len(rows) + 1.2)
    fig, ax = plt.subplots(figsize=(16, fig_h), dpi=100)
    
    plt.subplots_adjust(top=0.90, bottom=0.05, right=0.98, left=0.10)

    y_pos = list(range(len(rows)))
    
    c_max = "#FF8888"
    c_avg = "#66CC66"
    c_min = "#6666FF"
    
    bar_h = 0.62
    ax.barh(y_pos, maxs, color=c_max, alpha=0.8, height=bar_h, label="MAX")
    ax.barh(y_pos, avgs, color=c_avg, alpha=0.9, height=bar_h*0.7, label="AVG")
    ax.barh(y_pos, mins, color=c_min, alpha=1.0, height=bar_h*0.4, label="MIN")
    
    ax.set_yticks(y_pos)
    ax.set_yticklabels(labels, fontsize=12, fontweight='bold')
    ax.invert_yaxis()
    
    ax.set_xlim(0, xlim_right)
    ax.xaxis.set_major_formatter(FuncFormatter(lambda x, p: f"{int(x):,}"))
    ax.grid(axis='x', linestyle=':', alpha=0.5)
    
    ax.spines['right'].set_visible(False)
    ax.spines['top'].set_visible(False)
    ax.spines['left'].set_visible(False)
    
    ax.set_title(f"DDR4 & DDR5 Price Gauge {date_str} (JPY)", fontsize=16, fontweight='bold', pad=20)
    
    handles, legend_labels = ax.get_legend_handles_labels()
    ax.legend(handles[::-1], legend_labels[::-1], 
              loc="lower right", bbox_to_anchor=(1.0, 1.01), 
              ncol=3, frameon=False, fontsize=10)

    head_y = -0.8
    ax.text(x_min_txt, head_y, "MIN", color='blue', fontweight='bold', ha='right')
    ax.text(x_avg_txt, head_y, "AVG", color='green', fontweight='bold', ha='right')
    ax.text(x_max_txt, head_y, "MAX", color='red', fontweight='bold', ha='right')
    ax.text(x_cnt_txt, head_y, "Count", color='black', fontweight='bold', ha='right')
    
    def fmt_diff(curr, prev):
        txt = f"{curr:,}"
        if prev is None: return txt + " (-)"
        diff = curr - prev
        if diff > 0: return f"{txt} (+{diff:,})"
        if diff < 0: return f"{txt} ({diff:,})"
        return f"{txt} (±0)"

    for i, r in enumerate(rows):
        pr = prev_map.get(r.label)
        t_min = fmt_diff(r.min_price, pr.min_price if pr else None)
        t_avg = fmt_diff(r.avg_price, pr.avg_price if pr else None)
        t_max = fmt_diff(r.max_price, pr.max_price if pr else None)
        
        ax.text(x_min_txt, i, t_min, va='center', ha='right', fontsize=10, fontfamily='monospace')
        ax.text(x_avg_txt, i, t_avg, va='center', ha='right', fontsize=10, fontfamily='monospace')
        ax.text(x_max_txt, i, t_max, va='center', ha='right', fontsize=10, fontfamily='monospace')
        ax.text(x_cnt_txt, i, str(r.count), va='center', ha='right', fontsize=11)

    plt.savefig(out_path)
    if show: plt.show()
    plt.close()

# ============================================================
# Main Orchestrator
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

    ap.add_argument("--sleep", type=float, default=DEFAULT_SLEEP_SEC, help="Wait time (sec)")
    ap.add_argument("--jitter", type=float, default=DEFAULT_JITTER_SEC, help="Jitter time (sec)")
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
    
    # 1. Scrape Phase
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
                # 最後の要素でなければ待機するなどの細かい制御も可能だが、
                # ここでは単純に毎回スリープを挟む（単体時は最後でも入るが許容）
                sleep_with_jitter(args.sleep, args.jitter, "Next Target")
        print("\n=== Scraping Finished ===")
    
    # 2. Graph Phase
    if not target_dir.exists():
        if args.scrape:
            print(f"[Error] Scrape failed to create dir: {target_dir}")
        else:
            print(f"[Error] Directory not found: {target_dir}")
            print("Hint: Run with --scrape first.")
        return 1
        
    print(f"=== Generating Graph [{args.date}] ===")
    
    rows = load_stats_from_dir(target_dir, PRICE_FILTER_LOWER_RATIO, PRICE_FILTER_UPPER_RATIO)
    
    if not rows:
        print("[Error] No valid CSVs found in directory.")
        return 1
        
    try:
        current_dt = _dt.datetime.strptime(args.date, "%Y-%m-%d").date()
        prev_date = (current_dt - _dt.timedelta(days=1)).strftime("%Y-%m-%d")
        prev_dir = base_dir / f"ddr_scrape_{prev_date}"
        prev_rows = load_stats_from_dir(prev_dir, PRICE_FILTER_LOWER_RATIO, PRICE_FILTER_UPPER_RATIO) if prev_dir.exists() else []
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
