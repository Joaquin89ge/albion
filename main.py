#!/usr/bin/env python3
"""Fase 3: craft/buy local + flete (local vs viaje, umbral 5%/salto)."""

from __future__ import annotations

import argparse
import html as html_module
import json
import statistics
import sys
import time
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any
from urllib.parse import urlencode

import pandas as pd
import requests
from tabulate import tabulate

# --- Config fase 1 ---
SERVER = "west"
BASE_URL = f"https://{SERVER}.albion-online-data.com/api/v2/stats"
CITIES = [
    "Lymhurst",
    "Fort Sterling",
    "Martlock",
    "Bridgewatch",
    "Thetford",
]
QUALITIES = "1"
MAX_AGE_HOURS = 3
# Picos reales (hammer 16k un día) no deben mover ranking semanal/mensual.
ASK_OUTLIER_MULT = 3.0
WEEK_VS_MONTH_MULT = 2.0
CACHE_TTL_MIN = 10
HISTORY_DAYS = 28
HISTORY_WEEK_DAYS = 7
MAX_URL_LEN = 4096

# --- Config fase 2 ---
BRANCHES = {
    "leather_gear": True,
    "tanner": True,
    "tools": True,
    "cloth_gear": True,
    "weaver": True,
}
RRR_BASE = 0.15
RRR_CRAFT_BONUS = 0.25
RRR_REFINE_BONUS = 0.37
SETUP_FEE = 0.025
TAX_FEE = 0.08
VERBOSE_MARKET = False

# --- Config fase 3 ---
MARGIN_PER_HOP = 0.05
AODP_RETRIES = 3
AODP_RETRY_SLEEP = 1.5

# Liquidez (vol_dest = promedio diario de ventas 7d en destino)
LIQ_MATS_BRANCHES = frozenset({"tanner", "weaver"})
LIQ_MATS_MUERTO = 50.0  # /día; flojo hasta OK
LIQ_MATS_OK = 200.0
LIQ_GEAR_MUERTO = 5.0
LIQ_GEAR_OK = 15.0
LIQ_REL_RATIO = 0.10  # vs ciudad royal más líquida del mismo ítem
LIQ_SPREAD_WIDE = 0.50  # (ask-bid)/ask
LIQ_MUERTO = "muerto"
LIQ_FLOJO = "flojo"
LIQ_OK = "ok"
DISTANCE: dict[str, dict[str, int]] = {
    "Thetford": {
        "Thetford": 0,
        "Fort Sterling": 1,
        "Lymhurst": 2,
        "Bridgewatch": 2,
        "Martlock": 1,
    },
    "Fort Sterling": {
        "Fort Sterling": 0,
        "Thetford": 1,
        "Lymhurst": 1,
        "Bridgewatch": 2,
        "Martlock": 2,
    },
    "Lymhurst": {
        "Lymhurst": 0,
        "Fort Sterling": 1,
        "Bridgewatch": 1,
        "Martlock": 2,
        "Thetford": 2,
    },
    "Bridgewatch": {
        "Bridgewatch": 0,
        "Lymhurst": 1,
        "Martlock": 1,
        "Thetford": 2,
        "Fort Sterling": 2,
    },
    "Martlock": {
        "Martlock": 0,
        "Bridgewatch": 1,
        "Thetford": 1,
        "Lymhurst": 2,
        "Fort Sterling": 2,
    },
}

SCRIPT_DIR = Path(__file__).resolve().parent
RECIPES_FILE = SCRIPT_DIR / "recipes.json"
CACHE_DIR = SCRIPT_DIR / "cache"
PRICES_CACHE = CACHE_DIR / "prices.json"
HISTORY_CACHE = CACHE_DIR / "history.json"

SENTINEL_DATE = datetime(1, 1, 1, tzinfo=timezone.utc)

def display_item(item_id: str, enc: Any = None) -> str:
    """Full AODP id (keeps SET1/SET2/SET3). Append @enc only if missing and enc>0."""
    s = str(item_id)
    if "@" in s:
        return s
    if enc is None or (isinstance(enc, float) and pd.isna(enc)):
        return s
    enc_i = int(enc)
    if enc_i == 0:
        return s
    return f"{s}@{enc_i}"


def short_city(ciudad: str) -> str:
    return str(ciudad)


def short_item(item_id: str, enc: Any = None) -> str:
    return display_item(item_id, enc)


def fmt_silver(val: float | None, signed: bool = False) -> str:
    if val is None or (isinstance(val, float) and pd.isna(val)):
        return "—"
    v = float(val)
    sign = ""
    if signed:
        if v > 0:
            sign = "+"
        elif v < 0:
            sign = "-"
            v = abs(v)
    elif v < 0:
        sign = "-"
        v = abs(v)
    if v < 1000:
        s = str(int(round(v)))
    elif v < 1_000_000:
        s = f"{v / 1000:.1f}k".rstrip("0").rstrip(".")
        if not s.endswith("k"):
            s += "k"
    else:
        s = f"{v / 1_000_000:.1f}m".rstrip("0").rstrip(".")
        if not s.endswith("m"):
            s += "m"
    return f"{sign}{s}"


def fmt_pct(val: float | None) -> str:
    if val is None or (isinstance(val, float) and pd.isna(val)):
        return "—"
    v = float(val)
    sign = "+" if v > 0 else ""
    return f"{sign}{v:.0f}%"


def fmt_vol(val: float | None) -> str:
    return fmt_silver(val, signed=False)


def fmt_age(hours: float | None) -> str:
    if hours is None or (isinstance(hours, float) and pd.isna(hours)):
        return "—"
    return f"{int(round(float(hours)))}h"


def fmt_route(origen: str, destino: str, saltos: int) -> str:
    if int(saltos) == 0:
        return str(origen)
    return f"{origen} → {destino} ×{int(saltos)}"


def _enc_cell(enc: Any) -> str:
    if enc is None or (isinstance(enc, float) and pd.isna(enc)):
        return "—"
    return str(int(enc))


def is_suspicious(
    edad_h: float | None, margen_pct: float | None, max_edad: float, max_margen: float
) -> bool:
    if edad_h is not None and not pd.isna(edad_h) and float(edad_h) > max_edad:
        return True
    if margen_pct is not None and not pd.isna(margen_pct):
        if abs(float(margen_pct)) > max_margen:
            return True
    return False


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Albion craft/flete dashboard (terminal + HTML)"
    )
    parser.add_argument(
        "--top", type=int, default=20, help="Filas del ranking compacto (default: 20)"
    )
    parser.add_argument(
        "--min-ganancia",
        type=float,
        default=0,
        help="Piso de silver neto en el top (default: 0)",
    )
    parser.add_argument(
        "--min-margen",
        type=float,
        default=0,
        help="Piso de margen %% en el top (default: 0)",
    )
    parser.add_argument(
        "--max-edad",
        type=float,
        default=MAX_AGE_HOURS,
        help="Horas para marcar fresco / !! (default: 3)",
    )
    parser.add_argument(
        "--max-margen",
        type=float,
        default=200,
        help="%% por encima = sospechoso !! (default: 200)",
    )
    parser.add_argument(
        "--html",
        default="dashboard.html",
        metavar="PATH",
        help="Ruta de salida HTML (default: dashboard.html)",
    )
    parser.add_argument(
        "--no-html", action="store_true", help="No escribir archivo HTML"
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Dump completo: ranking, mercado, local vs viaje crudo",
    )
    parser.add_argument(
        "--min-vol-mats",
        type=float,
        default=LIQ_MATS_MUERTO,
        help=(
            "Piso diario tanner/weaver: debajo = liq muerto "
            f"(default: {LIQ_MATS_MUERTO:g})"
        ),
    )
    parser.add_argument(
        "--min-vol-gear",
        type=float,
        default=LIQ_GEAR_MUERTO,
        help=(
            "Piso diario leather/cloth/tools: debajo = liq muerto "
            f"(default: {LIQ_GEAR_MUERTO:g})"
        ),
    )
    return parser.parse_args()


def load_recipes(path: Path) -> dict[str, dict[str, Any]]:
    return json.loads(path.read_text(encoding="utf-8"))


def active_recipes(all_recipes: dict[str, dict[str, Any]]) -> dict[str, dict[str, Any]]:
    return {
        item_id: recipe
        for item_id, recipe in all_recipes.items()
        if BRANCHES.get(recipe.get("branch", ""), False)
    }


def output_item_id(base_id: str, enc: str) -> str:
    if enc == "0":
        return base_id
    return f"{base_id}@{enc}"


def collect_item_ids(recipes: dict[str, dict[str, Any]]) -> list[str]:
    ids: set[str] = set()
    for base_id, recipe in recipes.items():
        for enc, mats in recipe.get("enchants", {}).items():
            ids.add(output_item_id(base_id, enc))
            for mat in mats:
                ids.add(mat["item_id"])
    return sorted(ids)


def cache_is_fresh(path: Path) -> bool:
    if not path.exists() or path.stat().st_size < 4:
        return False
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return False
    if not payload:
        return False
    age = datetime.now(timezone.utc) - datetime.fromtimestamp(
        path.stat().st_mtime, tz=timezone.utc
    )
    return age < timedelta(minutes=CACHE_TTL_MIN)


def make_batches(items: list[str], endpoint: str) -> list[list[str]]:
    """Split items into URL-safe batches (item IDs go in the path)."""
    batches: list[list[str]] = []
    current: list[str] = []

    def url_len(batch: list[str]) -> int:
        item_path = ",".join(batch)
        if endpoint == "history":
            params = history_query_params()
        else:
            params = {"locations": ",".join(CITIES), "qualities": QUALITIES}
        return len(f"{BASE_URL}/{endpoint}/{item_path}.json?{urlencode(params)}")

    for item in items:
        trial = current + [item]
        if current and url_len(trial) >= MAX_URL_LEN:
            batches.append(current)
            current = [item]
        else:
            current = trial
    if current:
        batches.append(current)
    return batches


def history_query_params() -> dict[str, str]:
    end = datetime.now(timezone.utc).date()
    start = end - timedelta(days=HISTORY_DAYS)
    return {
        "locations": ",".join(CITIES),
        "qualities": QUALITIES,
        "time-scale": "24",
        "date": start.isoformat(),
        "end_date": end.isoformat(),
    }


def build_url(endpoint: str, batch: list[str]) -> str:
    item_path = ",".join(batch)
    if endpoint == "history":
        params = history_query_params()
    else:
        params = {"locations": ",".join(CITIES), "qualities": QUALITIES}
    return f"{BASE_URL}/{endpoint}/{item_path}.json?{urlencode(params)}"


def fetch_json(url: str) -> list | None:
    last_exc: requests.RequestException | None = None
    for attempt in range(1, AODP_RETRIES + 1):
        try:
            resp = requests.get(
                url,
                headers={"Accept-Encoding": "gzip"},
                timeout=30,
            )
            resp.raise_for_status()
            return resp.json()
        except requests.RequestException as exc:
            last_exc = exc
            if attempt < AODP_RETRIES:
                print(
                    f"  [RETRY {attempt}/{AODP_RETRIES}] {exc}",
                    file=sys.stderr,
                )
                time.sleep(AODP_RETRY_SLEEP)
    print(f"  [ERROR] {url[:120]}... -> {last_exc}", file=sys.stderr)
    return None


def fetch_prices(items: list[str], use_cache: bool) -> list[dict]:
    if use_cache and cache_is_fresh(PRICES_CACHE):
        print(f"Cache hit: {PRICES_CACHE.name} (< {CACHE_TTL_MIN} min)")
        return json.loads(PRICES_CACHE.read_text(encoding="utf-8"))

    print("Fetching prices from AODP...")
    all_rows: list[dict] = []
    batches = make_batches(items, "prices")
    for i, batch in enumerate(batches, 1):
        url = build_url("prices", batch)
        print(f"  prices batch {i}/{len(batches)} ({len(batch)} items)")
        data = fetch_json(url)
        if data:
            all_rows.extend(data)

    if all_rows:
        CACHE_DIR.mkdir(parents=True, exist_ok=True)
        PRICES_CACHE.write_text(json.dumps(all_rows), encoding="utf-8")
    else:
        print("  [WARN] precios vacíos: no se escribe cache", file=sys.stderr)
    return all_rows


def fetch_history(items: list[str], use_cache: bool) -> list[dict]:
    if use_cache and cache_is_fresh(HISTORY_CACHE):
        print(f"Cache hit: {HISTORY_CACHE.name} (< {CACHE_TTL_MIN} min)")
        return json.loads(HISTORY_CACHE.read_text(encoding="utf-8"))

    print("Fetching history from AODP...")
    all_rows: list[dict] = []
    batches = make_batches(items, "history")
    for i, batch in enumerate(batches, 1):
        url = build_url("history", batch)
        print(f"  history batch {i}/{len(batches)} ({len(batch)} items)")
        data = fetch_json(url)
        if data:
            all_rows.extend(data)

    if all_rows:
        CACHE_DIR.mkdir(parents=True, exist_ok=True)
        HISTORY_CACHE.write_text(json.dumps(all_rows), encoding="utf-8")
    else:
        print("  [WARN] historial vacío: no se escribe cache", file=sys.stderr)
    return all_rows


def parse_aodp_date(raw: str | None) -> datetime | None:
    if not raw or raw.startswith("0001-01-01"):
        return None
    try:
        dt = datetime.fromisoformat(raw.replace("Z", "+00:00"))
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt
    except ValueError:
        return None


def age_hours(dt: datetime | None) -> float | None:
    if dt is None:
        return None
    return (datetime.now(timezone.utc) - dt).total_seconds() / 3600


def prices_to_df(rows: list[dict]) -> pd.DataFrame:
    records: list[dict] = []
    for row in rows:
        quality = row.get("quality")
        if quality not in (None, 1, "1"):
            continue

        ask = row.get("sell_price_min") or 0
        if ask == 0:
            ask = None

        sell_dt = parse_aodp_date(row.get("sell_price_min_date"))
        if ask is not None and sell_dt is None:
            ask = None

        bid = row.get("buy_price_max") or 0
        if bid == 0:
            bid = None
        buy_dt = parse_aodp_date(row.get("buy_price_max_date"))
        if bid is not None and buy_dt is None:
            bid = None

        bid_edad = age_hours(buy_dt)
        ask_edad = age_hours(sell_dt)
        edades = [e for e in (bid_edad, ask_edad) if e is not None]
        edad = max(edades) if edades else None
        fresco = edad is not None and edad <= MAX_AGE_HOURS

        records.append(
            {
                "item": row.get("item_id", ""),
                "ciudad": row.get("city", ""),
                "bid": bid,
                "ask": ask,
                "bid_edad_h": round(bid_edad, 1) if bid_edad is not None else None,
                "ask_edad_h": round(ask_edad, 1) if ask_edad is not None else None,
                "edad_h": round(edad, 1) if edad is not None else None,
                "fresco": "sí" if fresco else "no",
            }
        )
    if not records:
        return pd.DataFrame(
            columns=[
                "item",
                "ciudad",
                "bid",
                "ask",
                "bid_edad_h",
                "ask_edad_h",
                "edad_h",
                "fresco",
            ]
        )
    return pd.DataFrame(records)


def history_to_df(rows: list[dict]) -> pd.DataFrame:
    now = datetime.now(timezone.utc)
    cutoff = now - timedelta(days=HISTORY_DAYS)
    agg: dict[tuple[str, str], list[dict]] = {}

    for entry in rows:
        item_id = entry.get("item_id", "")
        ciudad = entry.get("location", "")
        for point in entry.get("data", []):
            ts_raw = point.get("timestamp")
            if not ts_raw:
                continue
            try:
                ts = datetime.fromisoformat(ts_raw.replace("Z", "+00:00"))
                if ts.tzinfo is None:
                    ts = ts.replace(tzinfo=timezone.utc)
            except ValueError:
                continue
            if ts < cutoff:
                continue
            price = point.get("avg_price", 0) or 0
            if price <= 0:
                continue
            key = (item_id, ciudad)
            agg.setdefault(key, []).append(
                {
                    "ts": ts,
                    "avg_price": float(price),
                    "item_count": point.get("item_count", 0) or 0,
                }
            )

    records: list[dict] = []
    for (item_id, ciudad), points in agg.items():
        if not points:
            continue
        avg_7d, vol_7d = _robust_vwap(points, now, HISTORY_WEEK_DAYS)
        avg_28d, vol_28d = _robust_vwap(points, now, HISTORY_DAYS)
        quote = _horizon_quote(avg_7d, avg_28d)
        records.append(
            {
                "item": item_id,
                "ciudad": ciudad,
                "avg_7d": avg_7d,
                "avg_28d": avg_28d,
                "quote": quote,
                "vol_7d": vol_7d,
                "vol_28d": vol_28d,
            }
        )
    if not records:
        return pd.DataFrame(
            columns=[
                "item",
                "ciudad",
                "avg_7d",
                "avg_28d",
                "quote",
                "vol_7d",
                "vol_28d",
            ]
        )
    return pd.DataFrame(records)


def _robust_vwap(
    points: list[dict], now: datetime, days: int
) -> tuple[float | None, float | None]:
    """Media ponderada por volumen, recortando días extraordinarios vs la mediana."""
    cutoff = now - timedelta(days=days)
    window = [p for p in points if p["ts"] >= cutoff and p["avg_price"] > 0]
    if not window:
        return None, None
    prices = [p["avg_price"] for p in window]
    med = statistics.median(prices)
    kept = [
        p
        for p in window
        if med / ASK_OUTLIER_MULT <= p["avg_price"] <= med * ASK_OUTLIER_MULT
    ]
    if not kept:
        kept = window
    vol_sum = sum(p["item_count"] for p in kept)
    if vol_sum > 0:
        vwap = sum(p["avg_price"] * p["item_count"] for p in kept) / vol_sum
    else:
        vwap = sum(p["avg_price"] for p in kept) / len(kept)
    daily_vol = sum(p["item_count"] for p in window) / len(window)
    return round(vwap, 1), round(daily_vol, 1)


def _horizon_quote(avg_7d: float | None, avg_28d: float | None) -> float | None:
    """Semana si es estable vs el mes; si la semana fue extraordinaria, usar el mes."""
    if avg_7d is None:
        return avg_28d
    if avg_28d is None:
        return avg_7d
    if avg_7d > avg_28d * WEEK_VS_MONTH_MULT or avg_7d < avg_28d / WEEK_VS_MONTH_MULT:
        return avg_28d
    return avg_7d


def build_market_table(
    prices_df: pd.DataFrame, history_df: pd.DataFrame
) -> pd.DataFrame:
    if history_df.empty:
        merged = prices_df.copy()
        merged["avg_7d"] = None
        merged["avg_28d"] = None
        merged["quote"] = None
        merged["vol_7d"] = None
        merged["vol_28d"] = None
    else:
        merged = prices_df.merge(history_df, on=["item", "ciudad"], how="left")

    cols = [
        "item",
        "ciudad",
        "bid",
        "ask",
        "avg_7d",
        "avg_28d",
        "quote",
        "vol_7d",
        "vol_28d",
        "bid_edad_h",
        "ask_edad_h",
        "edad_h",
        "fresco",
    ]
    for col in cols:
        if col not in merged.columns:
            merged[col] = None
    merged = merged[cols]
    merged = merged.sort_values(["item", "ciudad"]).reset_index(drop=True)
    return merged


def _finite_pos(val: Any) -> float | None:
    if val is None or pd.isna(val):
        return None
    try:
        f = float(val)
    except (TypeError, ValueError):
        return None
    if f <= 0:
        return None
    return f


def fair_quote(ask: Any, ask_edad_h: Any, quote: Any, avg_7d: Any) -> tuple[float | None, float | None]:
    """Precio de ranking: media semana/mes. Ask spot solo si no hay historial usable."""
    quote_f = _finite_pos(quote) or _finite_pos(avg_7d)
    if quote_f is not None:
        return quote_f, None

    ask_f = _finite_pos(ask)
    edad_f = None
    if ask_edad_h is not None and not pd.isna(ask_edad_h):
        try:
            edad_f = float(ask_edad_h)
        except (TypeError, ValueError):
            edad_f = None
    if ask_f is not None and edad_f is not None and edad_f <= MAX_AGE_HOURS:
        return ask_f, edad_f
    return None, None


class MarketLookup:
    """Acceso rápido a precios por (item, ciudad)."""

    def __init__(self, market_df: pd.DataFrame) -> None:
        self._rows: dict[tuple[str, str], pd.Series] = {}
        for _, row in market_df.iterrows():
            item = row["item"]
            ciudad = row["ciudad"]
            if not item or pd.isna(item) or not ciudad or pd.isna(ciudad):
                continue
            self._rows[(str(item), str(ciudad))] = row

    def get(self, item: str, ciudad: str) -> pd.Series | None:
        return self._rows.get((item, ciudad))

    def mat_price(self, item: str, ciudad: str) -> tuple[float | None, float | None, float | None]:
        """Compra de mats: media semanal/mensual (no bid ocasional)."""
        row = self.get(item, ciudad)
        if row is None:
            return None, None, None
        price = _finite_pos(row.get("quote")) or _finite_pos(row.get("avg_7d"))
        if price is None:
            bid = _finite_pos(row.get("bid"))
            edad = row.get("bid_edad_h")
            if bid is not None:
                return bid, float(edad) if pd.notna(edad) else None, _finite_pos(row.get("vol_7d"))
            return None, None, None
        return price, None, _finite_pos(row.get("vol_7d"))

    def sell_price(self, item: str, ciudad: str) -> tuple[float | None, float | None, float | None]:
        """Venta/compra de terminado: media semanal/mensual, no ask extraordinario."""
        row = self.get(item, ciudad)
        if row is None:
            return None, None, None
        price, edad = fair_quote(
            row.get("ask"),
            row.get("ask_edad_h"),
            row.get("quote"),
            row.get("avg_7d"),
        )
        if price is None:
            return None, None, None
        return price, edad, _finite_pos(row.get("vol_7d"))


def rrr_for_city(city: str, recipe: dict[str, Any]) -> float:
    bonus_city = recipe.get("bonus_city")
    kind = recipe.get("kind")
    if bonus_city is None:
        return RRR_BASE
    if city == bonus_city:
        if kind == "refine":
            return RRR_REFINE_BONUS
        if kind == "craft":
            return RRR_CRAFT_BONUS
    return RRR_BASE


def compute_craft_cost(
    mats: list[dict[str, Any]],
    city: str,
    rrr: float,
    lookup: MarketLookup,
) -> tuple[float | None, float | None, float | None]:
    """Retorna (costo_craft, vol_mats_min, edad_h_worst)."""
    total = 0.0
    vols: list[float] = []
    edades: list[float] = []
    for mat in mats:
        price, edad, vol = lookup.mat_price(mat["item_id"], city)
        if price is None:
            return None, None, None
        total += mat["qty"] * price
        if vol is not None:
            vols.append(vol)
        if edad is not None:
            edades.append(edad)
    cost = total * (1 - rrr)
    vol_mats = min(vols) if vols else None
    edad = max(edades) if edades else None
    return cost, vol_mats, edad


def action_label(method: str, hops: int) -> str:
    if hops == 0:
        return f"{method} local"
    return f"{method}+viaje"


def travel_worth_it(extra_margin_pct: float, hops: int) -> bool:
    """Viaje vale si margen % extra vs local >= MARGIN_PER_HOP * saltos."""
    if hops == 0:
        return True
    return extra_margin_pct >= MARGIN_PER_HOP * hops * 100


def _liq_ok_floor(muerto_floor: float, default_muerto: float, default_ok: float) -> float:
    if muerto_floor <= default_ok:
        return default_ok
    return muerto_floor * (default_ok / default_muerto)


def _spread_ratio(bid: Any, ask: Any) -> float | None:
    bid_f = _finite_pos(bid)
    ask_f = _finite_pos(ask)
    if bid_f is None or ask_f is None:
        return None
    return (ask_f - bid_f) / ask_f


def score_liquidity(
    rama: str,
    vol_dest: Any,
    max_vol: Any,
    spread: float | None,
    min_vol_mats: float,
    min_vol_gear: float,
    ok_vol_mats: float,
    ok_vol_gear: float,
) -> str:
    """Etiqueta liq: muerto / flojo / ok (volumen diario + ratio entre ciudades + spread)."""
    if rama in LIQ_MATS_BRANCHES:
        muerto_floor, ok_floor = min_vol_mats, ok_vol_mats
    else:
        muerto_floor, ok_floor = min_vol_gear, ok_vol_gear

    vol_f = _finite_pos(vol_dest)
    vol = vol_f if vol_f is not None else 0.0

    if vol < muerto_floor:
        label = LIQ_MUERTO
    elif vol < ok_floor:
        label = LIQ_FLOJO
    else:
        label = LIQ_OK

    max_f = _finite_pos(max_vol)
    max_v = max_f if max_f is not None else 0.0
    # Evitar ruido: solo comparar si la ciudad más líquida ya es un mercado real.
    if max_v >= ok_floor and (vol / max_v) < LIQ_REL_RATIO:
        label = LIQ_MUERTO

    if spread is not None and not pd.isna(spread) and float(spread) > LIQ_SPREAD_WIDE:
        if vol < ok_floor:
            label = LIQ_MUERTO
        elif label == LIQ_OK:
            label = LIQ_FLOJO
    return label


def apply_liquidity(
    ranking_df: pd.DataFrame,
    lookup: MarketLookup,
    min_vol_mats: float,
    min_vol_gear: float,
) -> pd.DataFrame:
    """Añade columna liq usando vol_dest, max vol royal y spread ask/bid del destino."""
    cols = list(ranking_df.columns)
    if "liq" not in cols:
        insert_at = cols.index("vol_dest") + 1 if "vol_dest" in cols else len(cols)
        cols = cols[:insert_at] + ["liq"] + cols[insert_at:]

    if ranking_df.empty:
        out = ranking_df.copy()
        out["liq"] = pd.Series(dtype=object)
        return out[cols] if set(cols) <= set(out.columns) else out

    ok_mats = _liq_ok_floor(min_vol_mats, LIQ_MATS_MUERTO, LIQ_MATS_OK)
    ok_gear = _liq_ok_floor(min_vol_gear, LIQ_GEAR_MUERTO, LIQ_GEAR_OK)

    max_vol_by_item: dict[str, float] = {}
    for item in ranking_df["item"].astype(str).unique():
        vols: list[float] = []
        for city in CITIES:
            mrow = lookup.get(item, city)
            if mrow is None:
                continue
            v = _finite_pos(mrow.get("vol_7d"))
            if v is not None:
                vols.append(v)
        max_vol_by_item[item] = max(vols) if vols else 0.0

    labels: list[str] = []
    for _, row in ranking_df.iterrows():
        item = str(row["item"])
        dest = str(row["destino"])
        mrow = lookup.get(item, dest)
        spread = None if mrow is None else _spread_ratio(mrow.get("bid"), mrow.get("ask"))
        labels.append(
            score_liquidity(
                str(row.get("rama", "")),
                row.get("vol_dest"),
                max_vol_by_item.get(item, 0.0),
                spread,
                min_vol_mats,
                min_vol_gear,
                ok_mats,
                ok_gear,
            )
        )

    out = ranking_df.copy()
    out["liq"] = labels
    return out[cols]


def _travel_candidates(group: pd.DataFrame) -> pd.DataFrame:
    travel = group[group["saltos"] > 0]
    if travel.empty or "liq" not in travel.columns:
        return travel
    liquid = travel[travel["liq"] != LIQ_MUERTO]
    return liquid


def build_ranking_table(
    recipes: dict[str, dict[str, Any]], lookup: MarketLookup
) -> pd.DataFrame:
    """Ranking craft/buy × origen × destino; ordenado por ganancia desc."""
    rows: list[dict[str, Any]] = []

    for base_id, recipe in recipes.items():
        branch = recipe.get("branch", "")
        for enc, mats in recipe.get("enchants", {}).items():
            out_id = output_item_id(base_id, enc)

            origin_costs: dict[str, dict[str, Any]] = {}
            for origen in CITIES:
                rrr = rrr_for_city(origen, recipe)
                craft, vol_mats, craft_edad = compute_craft_cost(
                    mats, origen, rrr, lookup
                )
                buy, buy_edad, _ = lookup.sell_price(out_id, origen)
                origin_costs[origen] = {
                    "craft": craft,
                    "buy": buy,
                    "vol_mats": vol_mats,
                    "craft_edad": craft_edad,
                    "buy_edad": buy_edad,
                }

            for destino in CITIES:
                sell, sell_edad, vol_dest = lookup.sell_price(out_id, destino)
                if sell is None:
                    continue
                venta_neta = sell * (1 - TAX_FEE - SETUP_FEE)

                for origen in CITIES:
                    hops = DISTANCE[origen][destino]
                    oc = origin_costs[origen]
                    options: list[tuple[str, float, float | None, float | None]] = []
                    if oc["craft"] is not None:
                        options.append(
                            ("craft", oc["craft"], oc["vol_mats"], oc["craft_edad"])
                        )
                    if oc["buy"] is not None:
                        options.append(
                            ("buy", oc["buy"], oc["vol_mats"], oc["buy_edad"])
                        )

                    for method, costo, vol_mats, mat_edad in options:
                        ganancia = venta_neta - costo
                        margen_pct = (ganancia / costo * 100) if costo > 0 else None
                        edades = [
                            e
                            for e in (mat_edad, sell_edad)
                            if e is not None
                        ]
                        edad_h = max(edades) if edades else None
                        fresco = (
                            "sí"
                            if edad_h is not None and edad_h <= MAX_AGE_HOURS
                            else "no"
                        )

                        rows.append(
                            {
                                "item": out_id,
                                "enc": int(enc),
                                "rama": branch,
                                "accion": action_label(method, hops),
                                "origen": origen,
                                "destino": destino,
                                "saltos": hops,
                                "costo": round(costo, 1),
                                "venta_neta": round(venta_neta, 1),
                                "ganancia": round(ganancia, 1),
                                "margen_%": (
                                    round(margen_pct, 1)
                                    if margen_pct is not None
                                    else None
                                ),
                                "vol_dest": vol_dest,
                                "vol_mats": vol_mats,
                                "edad_h": (
                                    round(edad_h, 1) if edad_h is not None else None
                                ),
                                "fresco": fresco,
                            }
                        )

    cols = [
        "item",
        "enc",
        "rama",
        "accion",
        "origen",
        "destino",
        "saltos",
        "costo",
        "venta_neta",
        "ganancia",
        "margen_%",
        "vol_dest",
        "vol_mats",
        "edad_h",
        "fresco",
    ]
    if not rows:
        return pd.DataFrame(columns=cols)

    df = pd.DataFrame(rows)
    return df.sort_values("ganancia", ascending=False, na_position="last")[cols]


def build_local_vs_travel_block(ranking_df: pd.DataFrame) -> pd.DataFrame:
    """Dos filas por ítem: mejor local vs mejor destino (umbral 5%/salto)."""
    if ranking_df.empty:
        return pd.DataFrame()

    rows: list[dict[str, Any]] = []
    for item, group in ranking_df.groupby("item", sort=False):
        meta = group.iloc[0]
        local = group[group["saltos"] == 0]
        best_local = (
            local.loc[local["ganancia"].idxmax()] if not local.empty else None
        )
        best_pool = group
        if "liq" in group.columns:
            liquid = group[group["liq"] != LIQ_MUERTO]
            if not liquid.empty:
                best_pool = liquid
        best_dest = best_pool.loc[best_pool["ganancia"].idxmax()]

        if best_local is not None:
            rows.append(
                {
                    "item": item,
                    "enc": meta["enc"],
                    "rama": meta["rama"],
                    "tipo": "local",
                    "accion": best_local["accion"],
                    "origen": best_local["origen"],
                    "destino": best_local["destino"],
                    "ganancia": best_local["ganancia"],
                    "margen_%": best_local["margen_%"],
                    "saltos": 0,
                    "extra_gan": None,
                    "extra_margen_%": None,
                    "umbral_ok": "sí",
                }
            )

        extra_gan: float | None = None
        extra_margen: float | None = None
        umbral_ok = "sí"
        if best_local is not None:
            extra_gan = round(
                float(best_dest["ganancia"]) - float(best_local["ganancia"]), 1
            )
            if (
                pd.notna(best_dest["margen_%"])
                and pd.notna(best_local["margen_%"])
            ):
                extra_margen = round(
                    float(best_dest["margen_%"]) - float(best_local["margen_%"]),
                    1,
                )
                umbral_ok = (
                    "sí"
                    if travel_worth_it(extra_margen, int(best_dest["saltos"]))
                    else "no"
                )
        elif int(best_dest["saltos"]) > 0:
            umbral_ok = "no"

        rows.append(
            {
                "item": item,
                "enc": meta["enc"],
                "rama": meta["rama"],
                "tipo": "destino",
                "accion": best_dest["accion"],
                "origen": best_dest["origen"],
                "destino": best_dest["destino"],
                "ganancia": best_dest["ganancia"],
                "margen_%": best_dest["margen_%"],
                "saltos": best_dest["saltos"],
                "extra_gan": extra_gan,
                "extra_margen_%": extra_margen,
                "umbral_ok": umbral_ok,
            }
        )

    return pd.DataFrame(rows)


def filter_top_ranking(
    ranking_df: pd.DataFrame,
    top: int,
    min_ganancia: float,
    min_margen: float,
    exclude_muerto: bool = True,
) -> pd.DataFrame:
    if ranking_df.empty:
        return ranking_df
    floor = max(min_ganancia, 0)
    mask = ranking_df["ganancia"] > floor
    if min_margen > 0:
        mask &= ranking_df["margen_%"].fillna(-1) >= min_margen
    filtered = ranking_df[mask]
    if exclude_muerto and "liq" in filtered.columns:
        filtered = filtered[filtered["liq"] != LIQ_MUERTO]
    return filtered.head(top)


def build_local_vs_travel_lines(ranking_df: pd.DataFrame) -> list[dict[str, Any]]:
    """Una fila por ítem si local o viaje es positivo."""
    if ranking_df.empty:
        return []

    lines: list[dict[str, Any]] = []
    for item, group in ranking_df.groupby("item", sort=False):
        local = group[group["saltos"] == 0]
        travel = _travel_candidates(group)
        best_local = (
            local.loc[local["ganancia"].idxmax()] if not local.empty else None
        )
        best_travel = (
            travel.loc[travel["ganancia"].idxmax()] if not travel.empty else None
        )

        local_pos = best_local is not None and float(best_local["ganancia"]) > 0
        travel_pos = best_travel is not None and float(best_travel["ganancia"]) > 0
        if not local_pos and not travel_pos:
            continue

        verdict = "LOCAL"
        extra_gan: float | None = None
        extra_margen: float | None = None

        if local_pos and travel_pos:
            extra_gan = round(
                float(best_travel["ganancia"]) - float(best_local["ganancia"]), 1
            )
            if pd.notna(best_travel["margen_%"]) and pd.notna(best_local["margen_%"]):
                extra_margen = round(
                    float(best_travel["margen_%"]) - float(best_local["margen_%"]),
                    1,
                )
                if travel_worth_it(extra_margen, int(best_travel["saltos"])):
                    verdict = "VIAJE"
                else:
                    verdict = "LOCAL"
            elif extra_gan > 0 and travel_worth_it(0, int(best_travel["saltos"])):
                verdict = "VIAJE"
        elif travel_pos and not local_pos:
            verdict = "VIAJE"

        meta = group.iloc[0]
        lines.append(
            {
                "item": item,
                "enc": meta["enc"],
                "rama": meta["rama"],
                "local": best_local,
                "travel": best_travel,
                "local_pos": local_pos,
                "travel_pos": travel_pos,
                "extra_gan": extra_gan,
                "extra_margen": extra_margen,
                "verdict": verdict,
            }
        )
    return lines


def _susp_mark(
    edad_h: float | None, margen_pct: float | None, max_edad: float, max_margen: float
) -> str:
    return "!!" if is_suspicious(edad_h, margen_pct, max_edad, max_margen) else ""


def _fmt_local_travel_cell(row: pd.Series | None) -> str:
    if row is None:
        return "—"
    return (
        f"{row['accion']} · "
        f"{fmt_route(row['origen'], row['destino'], int(row['saltos']))} · "
        f"{fmt_silver(row['ganancia'], signed=True)}/{fmt_pct(row['margen_%'])}"
    )


def _lv_suspicious(entry: dict[str, Any], max_edad: float, max_margen: float) -> str:
    for side in (entry.get("local"), entry.get("travel")):
        if side is not None and is_suspicious(
            side.get("edad_h"), side.get("margen_%"), max_edad, max_margen
        ):
            return "!!"
    return ""


def print_dashboard(
    ranking_df: pd.DataFrame,
    lv_lines: list[dict[str, Any]],
    top: int,
    min_ganancia: float,
    min_margen: float,
    max_edad: float,
    max_margen: float,
) -> None:
    top_df = filter_top_ranking(ranking_df, top, min_ganancia, min_margen)
    now = datetime.now().strftime("%Y-%m-%d %H:%M")

    print(f"\n{'=' * 72}")
    print(f"  ALBION DASHBOARD  |  {SERVER}  |  {now}")
    print(f"{'=' * 72}")

    print(f"\n--- TOP {top} (por plata, gan>{max(min_ganancia, 0)}, sin liq:muerto) ---")
    if top_df.empty:
        print("(sin oportunidades positivas)")
    else:
        top_rows: list[dict[str, Any]] = []
        for _, row in top_df.iterrows():
            susp = _susp_mark(row["edad_h"], row["margen_%"], max_edad, max_margen)
            fresco = str(row["fresco"])
            if susp:
                fresco = f"{fresco} {susp}"
            top_rows.append(
                {
                    "ítem": display_item(str(row["item"]), row.get("enc")),
                    "enc": _enc_cell(row.get("enc")),
                    "rama": row["rama"],
                    "acción": row["accion"],
                    "origen": row["origen"],
                    "destino": row["destino"],
                    "saltos": int(row["saltos"]),
                    "costo": fmt_silver(row["costo"]),
                    "venta_neta": fmt_silver(row["venta_neta"]),
                    "ganancia": fmt_silver(row["ganancia"], signed=True),
                    "margen_%": fmt_pct(row["margen_%"]),
                    "vol_dest": fmt_vol(row.get("vol_dest")),
                    "liq": row.get("liq", "—"),
                    "vol_mats": fmt_vol(row.get("vol_mats")),
                    "edad": fmt_age(row["edad_h"]),
                    "fresco": fresco,
                }
            )
        print(tabulate(top_rows, headers="keys", tablefmt="simple"))

    print("\n--- LOCAL vs VIAJE (1 línea/ítem) ---")
    if not lv_lines:
        print("(sin datos)")
    else:
        lv_rows: list[dict[str, Any]] = []
        for entry in lv_lines:
            extra = entry["extra_gan"]
            extra_s = fmt_silver(extra, signed=True) if extra is not None else "—"
            susp = _lv_suspicious(entry, max_edad, max_margen)
            veredicto = entry["verdict"]
            if susp:
                veredicto = f"{veredicto} {susp}"
            lv_rows.append(
                {
                    "ítem": display_item(str(entry["item"]), entry.get("enc")),
                    "enc": _enc_cell(entry.get("enc")),
                    "rama": entry.get("rama", ""),
                    "local": _fmt_local_travel_cell(
                        entry["local"] if entry["local_pos"] else None
                    ),
                    "viaje": _fmt_local_travel_cell(
                        entry["travel"] if entry["travel_pos"] else None
                    ),
                    "extra": extra_s,
                    "veredicto": veredicto,
                }
            )
        print(tabulate(lv_rows, headers="keys", tablefmt="simple"))


def _html_class_signed(val: float | None) -> str:
    if val is None or (isinstance(val, float) and pd.isna(val)):
        return ""
    return "pos" if float(val) > 0 else "neg" if float(val) < 0 else ""


def write_html(
    path: Path,
    ranking_df: pd.DataFrame,
    lv_lines: list[dict[str, Any]],
    top: int,
    min_ganancia: float,
    min_margen: float,
    max_edad: float,
    max_margen: float,
) -> None:
    top_df = filter_top_ranking(ranking_df, top, min_ganancia, min_margen)
    now = datetime.now().strftime("%Y-%m-%d %H:%M")

    def esc(s: Any) -> str:
        return html_module.escape(str(s))

    def td_signed(val: float | None, fmt_fn) -> str:
        cls = _html_class_signed(val)
        if cls:
            return f'<td class="{cls}">{esc(fmt_fn(val))}</td>'
        return f"<td>{esc(fmt_fn(val))}</td>"

    top_rows: list[str] = []
    for _, row in top_df.iterrows():
        susp = _susp_mark(row["edad_h"], row["margen_%"], max_edad, max_margen)
        susp_cls = ' class="susp"' if susp else ""
        liq = str(row.get("liq", "—"))
        if not susp and liq == LIQ_FLOJO:
            susp_cls = ' class="flojo"'
        fresco = str(row["fresco"])
        if susp:
            fresco = f"{fresco} {susp}"
        top_rows.append(
            f"<tr{susp_cls}>"
            f"<td>{esc(display_item(str(row['item']), row.get('enc')))}</td>"
            f"<td>{esc(_enc_cell(row.get('enc')))}</td>"
            f"<td>{esc(row['rama'])}</td>"
            f"<td>{esc(row['accion'])}</td>"
            f"<td>{esc(row['origen'])}</td>"
            f"<td>{esc(row['destino'])}</td>"
            f"<td>{esc(int(row['saltos']))}</td>"
            f"<td>{esc(fmt_silver(row['costo']))}</td>"
            f"<td>{esc(fmt_silver(row['venta_neta']))}</td>"
            f"{td_signed(row['ganancia'], lambda v: fmt_silver(v, signed=True))}"
            f"{td_signed(row['margen_%'], fmt_pct)}"
            f"<td>{esc(fmt_vol(row.get('vol_dest')))}</td>"
            f"<td>{esc(row.get('liq', '—'))}</td>"
            f"<td>{esc(fmt_vol(row.get('vol_mats')))}</td>"
            f"<td>{esc(fmt_age(row['edad_h']))}</td>"
            f"<td>{esc(fresco)}</td>"
            f"</tr>"
        )

    lv_rows: list[str] = []
    for entry in lv_lines:
        susp = _lv_suspicious(entry, max_edad, max_margen)
        susp_cls = ' class="susp"' if susp else ""
        local_s = _fmt_local_travel_cell(entry["local"] if entry["local_pos"] else None)
        travel_s = _fmt_local_travel_cell(
            entry["travel"] if entry["travel_pos"] else None
        )
        extra = entry["extra_gan"]
        extra_s = fmt_silver(extra, signed=True) if extra is not None else "—"
        veredicto = entry["verdict"]
        if susp:
            veredicto = f"{veredicto} {susp}"
        lv_rows.append(
            f"<tr{susp_cls}>"
            f"<td>{esc(display_item(str(entry['item']), entry.get('enc')))}</td>"
            f"<td>{esc(_enc_cell(entry.get('enc')))}</td>"
            f"<td>{esc(entry.get('rama', ''))}</td>"
            f"<td>{esc(local_s)}</td>"
            f"<td>{esc(travel_s)}</td>"
            f"<td class=\"{_html_class_signed(extra)}\">{esc(extra_s)}</td>"
            f"<td><strong>{esc(veredicto)}</strong></td>"
            f"</tr>"
        )

    doc = f"""<!DOCTYPE html>
<html lang="es">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Albion Dashboard — {esc(SERVER)}</title>
<style>
body {{ font-family: system-ui, sans-serif; margin: 1rem; background: #1a1a2e; color: #eee; }}
h1 {{ font-size: 1.2rem; margin: 0 0 0.25rem; }}
.meta {{ color: #888; font-size: 0.85rem; margin-bottom: 1.5rem; }}
h2 {{ font-size: 1rem; margin: 1.5rem 0 0.5rem; color: #aaa; }}
.table-wrap {{ overflow-x: auto; }}
table {{ border-collapse: collapse; width: 100%; font-size: 0.8rem; }}
th, td {{ border: 1px solid #333; padding: 0.35rem 0.5rem; text-align: left; }}
th {{ background: #16213e; }}
tr:nth-child(even) {{ background: #0f0f23; }}
.pos {{ color: #4ade80; }}
.neg {{ color: #f87171; }}
.susp {{ background: #3b1f1f !important; }}
.susp td {{ color: #fca5a5; }}
.flojo {{ background: #2a2410 !important; }}
</style>
</head>
<body>
<h1>Albion Dashboard</h1>
<p class="meta">{esc(SERVER)} · {esc(now)} · top {top}</p>

<h2>TOP {top} (por plata, sin liq:muerto)</h2>
<div class="table-wrap">
<table>
<thead><tr>
<th>Ítem</th><th>Enc</th><th>Rama</th><th>Acción</th><th>Origen</th><th>Destino</th>
<th>Saltos</th><th>Costo</th><th>Venta neta</th><th>Ganancia</th><th>Margen</th>
<th>Vol dest</th><th>Liq</th><th>Vol mats</th><th>Edad</th><th>Fresco</th>
</tr></thead>
<tbody>
{"".join(top_rows) if top_rows else "<tr><td colspan='16'>(sin datos)</td></tr>"}
</tbody>
</table>
</div>

<h2>Local vs viaje</h2>
<div class="table-wrap">
<table>
<thead><tr>
<th>Ítem</th><th>Enc</th><th>Rama</th><th>Local</th><th>Viaje</th><th>Extra</th><th>Veredicto</th>
</tr></thead>
<tbody>
{"".join(lv_rows) if lv_rows else "<tr><td colspan='7'>(sin datos)</td></tr>"}
</tbody>
</table>
</div>
</body>
</html>
"""
    path.write_text(doc, encoding="utf-8")
    print(f"\nHTML → {path}")


def missing_market_items(
    item_ids: list[str], market_df: pd.DataFrame
) -> list[str]:
    """Ítems sin ningún precio usable en ninguna ciudad."""
    missing: list[str] = []
    for item in item_ids:
        subset = market_df[market_df["item"] == item]
        if subset.empty:
            missing.append(item)
            continue
        has_price = False
        for _, row in subset.iterrows():
            if (pd.notna(row.get("bid")) and row["bid"] > 0) or (
                pd.notna(row.get("ask")) and row["ask"] > 0
            ) or (pd.notna(row.get("quote")) and row["quote"] > 0) or (
                pd.notna(row.get("avg_7d")) and row["avg_7d"] > 0
            ) or (pd.notna(row.get("avg_28d")) and row["avg_28d"] > 0):
                has_price = True
                break
        if not has_price:
            missing.append(item)
    return missing


def print_df(df: pd.DataFrame, title: str) -> None:
    print(f"\n--- {title} ---")
    if df.empty:
        print("(sin datos)")
        return
    display = df.copy()
    for col in display.columns:
        if display[col].dtype in ("float64", "float32"):
            display[col] = display[col].apply(
                lambda v: "" if pd.isna(v) else v
            )
        else:
            display[col] = display[col].apply(
                lambda v: "" if pd.isna(v) else v
            )
    print(tabulate(display, headers="keys", tablefmt="simple", showindex=False))


def print_spread(df: pd.DataFrame) -> None:
    print("\n--- Spread crudo (ask min vs max, sin fees) ---")
    spreads: list[dict] = []

    for item, group in df.groupby("item"):
        with_ask = group[group["ask"].notna() & (group["ask"] > 0)]
        if len(with_ask) < 2:
            continue
        min_row = with_ask.loc[with_ask["ask"].idxmin()]
        max_row = with_ask.loc[with_ask["ask"].idxmax()]
        ask_min = min_row["ask"]
        ask_max = max_row["ask"]
        gap_pct = ((ask_max - ask_min) / ask_min) * 100 if ask_min else 0
        spreads.append(
            {
                "item": item,
                "ciudad_ask_min": min_row["ciudad"],
                "ask_min": int(ask_min),
                "ciudad_ask_max": max_row["ciudad"],
                "ask_max": int(ask_max),
                "gap_%": round(gap_pct, 1),
            }
        )

    if not spreads:
        print("(sin spreads: ningún ítem con ask>0 en >=2 ciudades)")
        return

    spread_df = pd.DataFrame(spreads).sort_values("item")
    print(tabulate(spread_df, headers="keys", tablefmt="simple", showindex=False))


def main() -> None:
    args = parse_args()

    if not RECIPES_FILE.exists():
        print(f"Missing {RECIPES_FILE}", file=sys.stderr)
        sys.exit(1)

    all_recipes = load_recipes(RECIPES_FILE)
    recipes = active_recipes(all_recipes)
    if not recipes:
        print("No active recipes (check BRANCHES flags)", file=sys.stderr)
        sys.exit(1)

    items = collect_item_ids(recipes)
    active_branches = [b for b, on in BRANCHES.items() if on]
    print(
        f"AODP server: {SERVER} | {len(items)} items | "
        f"{len(CITIES)} cities | ramas: {', '.join(active_branches)}"
    )
    use_cache = True

    prices_raw = fetch_prices(items, use_cache)
    history_raw = fetch_history(items, use_cache)

    prices_df = prices_to_df(prices_raw)
    history_df = history_to_df(history_raw)
    market_df = build_market_table(prices_df, history_df)
    lookup = MarketLookup(market_df)

    ranking_df = build_ranking_table(recipes, lookup)
    ranking_df = apply_liquidity(
        ranking_df, lookup, args.min_vol_mats, args.min_vol_gear
    )
    lv_lines = build_local_vs_travel_lines(ranking_df)

    print_dashboard(
        ranking_df,
        lv_lines,
        top=args.top,
        min_ganancia=args.min_ganancia,
        min_margen=args.min_margen,
        max_edad=args.max_edad,
        max_margen=args.max_margen,
    )

    if not args.no_html:
        html_path = Path(args.html)
        if not html_path.is_absolute():
            html_path = SCRIPT_DIR / html_path
        write_html(
            html_path,
            ranking_df,
            lv_lines,
            top=args.top,
            min_ganancia=args.min_ganancia,
            min_margen=args.min_margen,
            max_edad=args.max_edad,
            max_margen=args.max_margen,
        )

    if args.verbose:
        print_df(
            market_df[
                ["item", "ciudad", "bid", "ask", "avg_7d", "avg_28d", "quote", "vol_7d", "edad_h", "fresco"]
            ],
            "Precios + media 7d/28d (quote = semana, o mes si la semana fue extraordinaria)",
        )
        print_spread(market_df)
        print_df(ranking_df, "Ranking flete (craft/buy × origen × destino)")
        local_vs_travel = build_local_vs_travel_block(ranking_df)
        print_df(local_vs_travel, "Local vs viaje (2 filas/ítem, umbral 5%/salto)")

    missing = missing_market_items(items, market_df)
    if missing:
        print(f"\n--- Ítems sin datos AODP ({len(missing)}) ---")
        for item in missing:
            print(f"  {item}")


if __name__ == "__main__":
    main()
