#!/usr/bin/env python3
"""Visualize the per-sentence CSV rows emitted by `ptb-eval`.

The script accepts either a clean CSV file from stdout or a captured terminal
log containing progress bars, warnings, and the final summary. Only rows from
the `sentence_no,strategy,...` CSV table are plotted.
"""

from __future__ import annotations

import argparse
import csv
import math
import sys
from collections import defaultdict
from pathlib import Path


DEFAULT_METRICS = ["total_ms", "finalized_states", "output_rules", "score"]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Plot ptb-eval per-sentence CSV output.",
    )
    parser.add_argument(
        "input",
        nargs="?",
        help="CSV/log file to read. Reads stdin when omitted or '-'.",
    )
    parser.add_argument(
        "-o",
        "--output",
        default="ptb-eval.svg",
        help="Image file to write. SVG works without third-party packages; PNG/PDF use matplotlib.",
    )
    parser.add_argument(
        "--metrics",
        default=",".join(DEFAULT_METRICS),
        help=(
            "Comma-separated metrics to plot. Available columns are the CSV "
            "headers, e.g. parse_ms,total_ms,finalized_states,output_rules,score."
        ),
    )
    parser.add_argument(
        "--baseline",
        default=None,
        help="Optional strategy used for an extra runtime-ratio plot.",
    )
    parser.add_argument(
        "--title",
        default="ptb-eval",
        help="Figure title.",
    )
    parser.add_argument(
        "--show",
        action="store_true",
        help="Open an interactive window after writing the output.",
    )
    parser.add_argument(
        "--backend",
        choices=["auto", "svg", "matplotlib"],
        default="auto",
        help="Plot backend. 'svg' uses only the Python standard library.",
    )
    parser.add_argument(
        "--linear",
        action="store_true",
        help="Use linear y-axes for all metrics. By default large count metrics use log scale.",
    )
    return parser.parse_args()


def read_text(path: str | None) -> str:
    if path is None or path == "-":
        return sys.stdin.read()
    return Path(path).read_text(encoding="utf-8")


def parse_number(value: str) -> float:
    if value == "NaN":
        return math.nan
    return float(value)


def extract_rows(text: str) -> tuple[list[str], list[dict[str, object]]]:
    header: list[str] | None = None
    rows: list[dict[str, object]] = []

    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line:
            continue

        if line.startswith("sentence_no,strategy,"):
            header = next(csv.reader([line]))
            continue

        if header is None:
            continue

        parts = next(csv.reader([line]))
        if len(parts) != len(header):
            continue
        if not parts[0].isdigit():
            continue

        record: dict[str, object] = {"sentence_no": int(parts[0]), "strategy": parts[1]}
        for key, value in zip(header[2:], parts[2:]):
            record[key] = parse_number(value)
        rows.append(record)

    if header is None:
        raise SystemExit("No ptb-eval CSV header found.")
    if not rows:
        raise SystemExit("No ptb-eval CSV rows found.")
    return header, rows


def ordered_unique(values: list[object]) -> list[object]:
    seen = set()
    out = []
    for value in values:
        if value not in seen:
            seen.add(value)
            out.append(value)
    return out


def should_log_metric(metric: str) -> bool:
    return metric in {"finalized_states", "output_rules"} or metric.endswith("_rules")


def plot_metric(ax, rows, sentences, strategies, metric, linear: bool) -> None:
    by_key = {(row["sentence_no"], row["strategy"]): row for row in rows}
    for strategy in strategies:
        ys = []
        for sentence in sentences:
            row = by_key.get((sentence, strategy))
            ys.append(math.nan if row is None else row.get(metric, math.nan))
        ax.plot(sentences, ys, marker="o", linewidth=1.6, markersize=3.5, label=strategy)

    ax.set_title(metric)
    ax.set_xlabel("sentence")
    ax.grid(True, which="both", alpha=0.25)
    if not linear and should_log_metric(metric):
        ax.set_yscale("log")


def plot_runtime_ratio(ax, rows, sentences, strategies, baseline: str) -> None:
    by_key = {(row["sentence_no"], row["strategy"]): row for row in rows}
    for strategy in strategies:
        if strategy == baseline:
            continue
        ratios = []
        for sentence in sentences:
            base = by_key.get((sentence, baseline))
            row = by_key.get((sentence, strategy))
            if base is None or row is None:
                ratios.append(math.nan)
                continue
            base_ms = float(base.get("total_ms", math.nan))
            this_ms = float(row.get("total_ms", math.nan))
            ratios.append(this_ms / base_ms if base_ms > 0 else math.nan)
        ax.plot(sentences, ratios, marker="o", linewidth=1.6, markersize=3.5, label=strategy)

    ax.axhline(1.0, color="black", linewidth=1.0, alpha=0.45)
    ax.set_title(f"total_ms / {baseline}")
    ax.set_xlabel("sentence")
    ax.grid(True, which="both", alpha=0.25)


COLORS = [
    "#1f77b4",
    "#ff7f0e",
    "#2ca02c",
    "#d62728",
    "#9467bd",
    "#8c564b",
    "#e377c2",
    "#7f7f7f",
]


def xml_escape(value: object) -> str:
    return (
        str(value)
        .replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace('"', "&quot;")
    )


def metric_series(rows, sentences, strategies, metric):
    by_key = {(row["sentence_no"], row["strategy"]): row for row in rows}
    series = []
    for strategy in strategies:
        values = []
        for sentence in sentences:
            row = by_key.get((sentence, strategy))
            values.append(math.nan if row is None else float(row.get(metric, math.nan)))
        series.append((strategy, values))
    return series


def ratio_series(rows, sentences, strategies, baseline):
    by_key = {(row["sentence_no"], row["strategy"]): row for row in rows}
    series = []
    for strategy in strategies:
        if strategy == baseline:
            continue
        values = []
        for sentence in sentences:
            base = by_key.get((sentence, baseline))
            row = by_key.get((sentence, strategy))
            if base is None or row is None:
                values.append(math.nan)
                continue
            base_ms = float(base.get("total_ms", math.nan))
            this_ms = float(row.get("total_ms", math.nan))
            values.append(this_ms / base_ms if base_ms > 0 else math.nan)
        series.append((strategy, values))
    return series


def finite_values(series):
    return [
        value
        for _, values in series
        for value in values
        if isinstance(value, float) and math.isfinite(value)
    ]


def svg_plot_panel(parts, x, y, width, height, title, sentences, series, log_y):
    margin_left = 62
    margin_right = 18
    margin_top = 32
    margin_bottom = 42
    plot_x = x + margin_left
    plot_y = y + margin_top
    plot_w = width - margin_left - margin_right
    plot_h = height - margin_top - margin_bottom

    values = finite_values(series)
    if not values:
        return
    if log_y:
        values = [value for value in values if value > 0]
    if not values:
        log_y = False
        values = finite_values(series)

    y_min = min(values)
    y_max = max(values)
    if y_min == y_max:
        pad = abs(y_min) * 0.1 or 1.0
        y_min -= pad
        y_max += pad
    elif not log_y:
        pad = (y_max - y_min) * 0.08
        y_min -= pad
        y_max += pad

    if log_y:
        y_min = max(min(values), 1e-12)
        y_max = max(values)
        log_min = math.log10(y_min)
        log_max = math.log10(y_max)
        if log_min == log_max:
            log_min -= 1
            log_max += 1

        def scale_y(value):
            if not math.isfinite(value) or value <= 0:
                return None
            pos = (math.log10(value) - log_min) / (log_max - log_min)
            return plot_y + plot_h - pos * plot_h

        y_labels = [10**tick for tick in range(math.floor(log_min), math.ceil(log_max) + 1)]
    else:

        def scale_y(value):
            if not math.isfinite(value):
                return None
            pos = (value - y_min) / (y_max - y_min)
            return plot_y + plot_h - pos * plot_h

        y_labels = [y_min + (y_max - y_min) * i / 4 for i in range(5)]

    x_min = min(sentences)
    x_max = max(sentences)

    def scale_x(sentence):
        if x_max == x_min:
            return plot_x + plot_w / 2
        return plot_x + (sentence - x_min) / (x_max - x_min) * plot_w

    parts.append(f'<text x="{x + width / 2:.1f}" y="{y + 18}" text-anchor="middle" class="title">{xml_escape(title)}</text>')
    parts.append(f'<rect x="{plot_x}" y="{plot_y}" width="{plot_w}" height="{plot_h}" fill="white" stroke="#d0d0d0"/>')

    for label in y_labels:
        sy = scale_y(label)
        if sy is None:
            continue
        parts.append(f'<line x1="{plot_x}" y1="{sy:.1f}" x2="{plot_x + plot_w}" y2="{sy:.1f}" stroke="#eeeeee"/>')
        display = f"{label:.3g}"
        parts.append(f'<text x="{plot_x - 8}" y="{sy + 4:.1f}" text-anchor="end" class="tick">{display}</text>')

    for sentence in sentences:
        if len(sentences) > 12 and sentence != sentences[0] and sentence != sentences[-1] and sentence % 5 != 0:
            continue
        sx = scale_x(sentence)
        parts.append(f'<line x1="{sx:.1f}" y1="{plot_y + plot_h}" x2="{sx:.1f}" y2="{plot_y + plot_h + 5}" stroke="#777"/>')
        parts.append(f'<text x="{sx:.1f}" y="{plot_y + plot_h + 20}" text-anchor="middle" class="tick">{sentence}</text>')

    for idx, (strategy, values_for_strategy) in enumerate(series):
        color = COLORS[idx % len(COLORS)]
        current = []
        polylines = []
        for sentence, value in zip(sentences, values_for_strategy):
            sy = scale_y(value)
            if sy is None:
                if current:
                    polylines.append(current)
                    current = []
                continue
            current.append((scale_x(sentence), sy))
        if current:
            polylines.append(current)

        for points in polylines:
            coords = " ".join(f"{px:.1f},{py:.1f}" for px, py in points)
            parts.append(f'<polyline points="{coords}" fill="none" stroke="{color}" stroke-width="2"/>')
            for px, py in points:
                parts.append(f'<circle cx="{px:.1f}" cy="{py:.1f}" r="2.5" fill="{color}"/>')


def write_svg(output, rows, sentences, strategies, metrics, baseline, title, linear):
    panels = len(metrics) + (1 if baseline else 0)
    cols = 2 if panels > 1 else 1
    panel_w = 680
    panel_h = 340
    legend_h = 54
    title_h = 36
    rows_count = math.ceil(panels / cols)
    width = panel_w * cols
    height = title_h + legend_h + panel_h * rows_count
    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        "<style>"
        "text{font-family:-apple-system,BlinkMacSystemFont,Segoe UI,sans-serif;fill:#222}"
        ".suptitle{font-size:20px;font-weight:650}"
        ".title{font-size:14px;font-weight:650}"
        ".tick{font-size:11px;fill:#555}"
        ".legend{font-size:12px}"
        "</style>",
        '<rect width="100%" height="100%" fill="white"/>',
        f'<text x="{width / 2:.1f}" y="24" text-anchor="middle" class="suptitle">{xml_escape(title)}</text>',
    ]

    legend_y = title_h + 18
    legend_x = 24
    for idx, strategy in enumerate(strategies):
        color = COLORS[idx % len(COLORS)]
        x = legend_x + idx * 150
        y = legend_y
        parts.append(f'<line x1="{x}" y1="{y}" x2="{x + 24}" y2="{y}" stroke="{color}" stroke-width="3"/>')
        parts.append(f'<text x="{x + 32}" y="{y + 4}" class="legend">{xml_escape(strategy)}</text>')

    panel_index = 0
    for metric in metrics:
        row = panel_index // cols
        col = panel_index % cols
        series = metric_series(rows, sentences, strategies, metric)
        svg_plot_panel(
            parts,
            col * panel_w,
            title_h + legend_h + row * panel_h,
            panel_w,
            panel_h,
            metric,
            sentences,
            series,
            (not linear) and should_log_metric(metric),
        )
        panel_index += 1

    if baseline:
        row = panel_index // cols
        col = panel_index % cols
        svg_plot_panel(
            parts,
            col * panel_w,
            title_h + legend_h + row * panel_h,
            panel_w,
            panel_h,
            f"total_ms / {baseline}",
            sentences,
            ratio_series(rows, sentences, strategies, baseline),
            False,
        )

    parts.append("</svg>")
    output.write_text("\n".join(parts), encoding="utf-8")


def print_summary(rows: list[dict[str, object]], strategies: list[str]) -> None:
    by_strategy = defaultdict(list)
    for row in rows:
        by_strategy[row["strategy"]].append(row)

    print("strategy,total_ms,median_total_ms,finalized_states,output_rules", file=sys.stderr)
    for strategy in strategies:
        strategy_rows = by_strategy[strategy]
        totals = sorted(float(row["total_ms"]) for row in strategy_rows)
        total_ms = sum(totals)
        mid = len(totals) // 2
        median = totals[mid] if len(totals) % 2 else (totals[mid - 1] + totals[mid]) / 2
        finalized = sum(int(row["finalized_states"]) for row in strategy_rows)
        output_rules = sum(int(row["output_rules"]) for row in strategy_rows)
        print(
            f"{strategy},{total_ms:.2f},{median:.2f},{finalized},{output_rules}",
            file=sys.stderr,
        )


def main() -> None:
    args = parse_args()
    header, rows = extract_rows(read_text(args.input))

    metrics = [metric.strip() for metric in args.metrics.split(",") if metric.strip()]
    missing = [metric for metric in metrics if metric not in header]
    if missing:
        raise SystemExit(f"Unknown metric(s): {', '.join(missing)}")

    strategies = [str(value) for value in ordered_unique([row["strategy"] for row in rows])]
    sentences = sorted({int(row["sentence_no"]) for row in rows})

    if args.baseline is not None and args.baseline not in strategies:
        raise SystemExit(f"Baseline strategy {args.baseline!r} is not present in the data.")

    output = Path(args.output)
    use_svg = args.backend == "svg" or (args.backend == "auto" and output.suffix.lower() == ".svg")
    if use_svg:
        write_svg(output, rows, sentences, strategies, metrics, args.baseline, args.title, args.linear)
    else:
        try:
            import matplotlib.pyplot as plt
        except ModuleNotFoundError as exc:
            raise SystemExit(
                "matplotlib is required for non-SVG output. Use '-o ptb-eval.svg' "
                "or install matplotlib."
            ) from exc

        panels = len(metrics) + (1 if args.baseline else 0)
        cols = 2 if panels > 1 else 1
        rows_count = math.ceil(panels / cols)
        fig, axes = plt.subplots(rows_count, cols, figsize=(7 * cols, 3.8 * rows_count), squeeze=False)
        flat_axes = list(axes.flat)

        for ax, metric in zip(flat_axes, metrics):
            plot_metric(ax, rows, sentences, strategies, metric, args.linear)

        next_axis = len(metrics)
        if args.baseline:
            plot_runtime_ratio(flat_axes[next_axis], rows, sentences, strategies, args.baseline)
            next_axis += 1

        for ax in flat_axes[next_axis:]:
            ax.axis("off")

        handles, labels = flat_axes[0].get_legend_handles_labels()
        fig.legend(handles, labels, loc="upper center", ncol=min(len(labels), 4), frameon=False)
        fig.suptitle(args.title, y=0.995)
        fig.tight_layout(rect=(0, 0, 1, 0.94))
        fig.savefig(output, dpi=180)

    print(f"wrote {output}", file=sys.stderr)
    print_summary(rows, strategies)

    if args.show:
        if use_svg:
            raise SystemExit("--show is only supported with the matplotlib backend.")
        plt.show()


if __name__ == "__main__":
    main()
