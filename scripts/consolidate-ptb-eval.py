#!/usr/bin/env python3
"""Consolidate ptb-eval per-sentence CSV outputs into one row per experiment.

`ptb-eval` writes a CSV with one row per (sentence, strategy):

    sentence_no,strategy,score,parse_ms,total_ms,finalized_states,heap_pushes,...

This script turns a set of such files into a single *wide* CSV with:

  * one row per input file (an "experiment"),
  * columns A and B = `timestamp` and `title`, parsed from the file name
    `times-<timestamp>[-<title>].csv` (falls back to the file's mtime + stem when
    the name does not match),
  * one column per (strategy, measurement), e.g. `astar-sx.total_ms`, holding the
    measurement aggregated across all sentences in that file (default: sum).

A given (strategy, measurement) pair always maps to the same column across all
files, so runs that used different strategy sets still line up; cells for a
strategy a run did not use are left blank. Columns are grouped by strategy, so
each strategy's block of measurements is contiguous.

The result is a plain CSV for import into a spreadsheet.

Examples
--------
    # consolidate explicit files into a spreadsheet-ready CSV
    python scripts/consolidate-ptb-eval.py times-*.csv -o summary.csv

    # default: glob 'times-*.csv' in the current directory, write to stdout
    python scripts/consolidate-ptb-eval.py

    # use medians instead of sums (e.g. for *_ms columns)
    python scripts/consolidate-ptb-eval.py times-*.csv --agg median
"""

from __future__ import annotations

import argparse
import csv
import datetime as dt
import glob
import os
import re
import statistics
import sys
from collections import defaultdict

# File name -> (timestamp, title). Timestamp is the numeric run token; title is
# whatever follows it (defaulting to "base" for the un-suffixed baseline file).
LABEL_RE = re.compile(r"^times-(?P<ts>\d+)(?:-(?P<title>.+))?$")

# Columns that identify a sentence row rather than a measurement.
ID_COLS = ("sentence_no", "strategy")

# Pseudo-measurement: how many sentence rows a strategy had in a file. Helps spot
# runs that are not comparable (different sentence sets). Always listed first.
COUNT_METRIC = "n_sentences"


def parse_label(path: str) -> tuple[str, str]:
    """Derive (timestamp, title) from the file name, or fall back to mtime/stem."""
    stem = os.path.splitext(os.path.basename(path))[0]
    m = LABEL_RE.match(stem)
    if m:
        return m.group("ts"), (m.group("title") or "base")
    ts = dt.datetime.fromtimestamp(os.path.getmtime(path)).strftime("%Y%m%d-%H%M%S")
    return ts, stem


def parse_number(s: str | None):
    """Parse a cell into int (preferred, exact for counts) or float, else None."""
    if s is None:
        return None
    s = s.strip()
    if s == "":
        return None
    try:
        return int(s)
    except ValueError:
        try:
            return float(s)
        except ValueError:
            return None


def aggregate(values, how: str):
    nums = [v for v in values if v is not None]
    if not nums:
        return None
    if how == "sum":
        return sum(nums)  # stays int when every input is int
    if how == "mean":
        return sum(nums) / len(nums)
    if how == "median":
        return statistics.median(nums)
    if how == "min":
        return min(nums)
    if how == "max":
        return max(nums)
    if how == "first":
        return nums[0]
    raise ValueError(f"unknown aggregation {how!r}")


def fmt(v) -> str:
    """Format a value for CSV: integers without a decimal point, floats tidied."""
    if v is None:
        return ""
    if isinstance(v, bool):
        return str(int(v))
    if isinstance(v, int):
        return str(v)
    if isinstance(v, float):
        if v != v:  # NaN
            return "nan"
        if v.is_integer():
            return str(int(v))
        return f"{round(v, 6)}"
    return str(v)


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Consolidate ptb-eval CSVs into one row per experiment.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument(
        "files",
        nargs="*",
        help="ptb-eval CSV files (default: glob 'times-*.csv' in the cwd).",
    )
    ap.add_argument("-o", "--output", help="output CSV path (default: stdout).")
    ap.add_argument(
        "--agg",
        default="sum",
        choices=["sum", "mean", "median", "min", "max", "first"],
        help="how to aggregate a measurement across sentences (default: sum).",
    )
    ap.add_argument(
        "--sep",
        default=".",
        help="separator between strategy and measurement in column names (default '.').",
    )
    ap.add_argument(
        "--no-count",
        action="store_true",
        help=f"omit the per-strategy '{COUNT_METRIC}' column.",
    )
    args = ap.parse_args()

    files = args.files or sorted(glob.glob("times-*.csv"))
    if not files:
        ap.error("no input files given and no 'times-*.csv' found in the cwd")

    metric_order: list[str] = []  # canonical measurement order, first-seen
    seen_metrics: set[str] = set()
    strategies: set[str] = set()
    rows: list[tuple[str, str, str, dict]] = []  # (timestamp, title, path, agg)

    for path in files:
        try:
            fh = open(path, newline="")
        except OSError as e:
            print(f"warning: skipping {path}: {e}", file=sys.stderr)
            continue
        with fh:
            reader = csv.DictReader(fh)
            if not reader.fieldnames:
                print(f"warning: {path} is empty; skipping", file=sys.stderr)
                continue
            metrics = [c for c in reader.fieldnames if c not in ID_COLS]
            for m in metrics:
                if m not in seen_metrics:
                    seen_metrics.add(m)
                    metric_order.append(m)

            collected: dict[tuple[str, str], list] = defaultdict(list)
            counts: dict[str, int] = defaultdict(int)
            for r in reader:
                strat = (r.get("strategy") or "").strip()
                if not strat:
                    continue  # skip blank / malformed rows
                strategies.add(strat)
                counts[strat] += 1
                for m in metrics:
                    collected[(strat, m)].append(parse_number(r.get(m)))

            agg = {key: aggregate(vals, args.agg) for key, vals in collected.items()}
            if not args.no_count:
                for strat, c in counts.items():
                    agg[(strat, COUNT_METRIC)] = c

        ts, title = parse_label(path)
        rows.append((ts, title, path, agg))

    if not rows:
        ap.error("no usable rows found in the input files")

    if not args.no_count:
        metric_order = [COUNT_METRIC] + metric_order

    strat_list = sorted(strategies)
    col_keys = [(s, m) for s in strat_list for m in metric_order]
    header = ["timestamp", "title"] + [f"{s}{args.sep}{m}" for (s, m) in col_keys]

    rows.sort(key=lambda row: (row[0], row[1], row[2]))

    out = open(args.output, "w", newline="") if args.output else sys.stdout
    try:
        writer = csv.writer(out)
        writer.writerow(header)
        for ts, title, _path, agg in rows:
            writer.writerow([ts, title] + [fmt(agg.get(key)) for key in col_keys])
    finally:
        if args.output:
            out.close()

    print(
        f"consolidated {len(rows)} file(s), {len(strat_list)} strateg(y/ies), "
        f"{len(metric_order)} measurement(s) ({args.agg}) -> "
        f"{args.output or 'stdout'}",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
