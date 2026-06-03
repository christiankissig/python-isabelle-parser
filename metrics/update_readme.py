"""Inject the latest metrics into README.rst between the METRICS markers.

Reads metrics/metrics.json and rewrites the block delimited by
``.. METRICS:START`` and ``.. METRICS:END`` with an RST table.
"""

import json
import os
from typing import Any

README = os.environ.get("README", "README.rst")
METRICS = os.environ.get("METRICS_OUT", "metrics/metrics.json")


def build_table(m: dict[str, Any]) -> str:
    def row(metric: str, value: Any) -> str:
        return f"   * - {metric}\n     - {value}\n"

    fps = m.get("files_per_sec")
    mbs = m.get("mb_per_sec")
    throughput = (
        f"{fps} files/s · {mbs} MB/s (×{m.get('workers', '?')} workers)"
        if fps is not None
        else "n/a"
    )
    median = m.get("median_ok_parse_s")
    median_s = f"{median} s" if median is not None else "n/a"

    table = ".. list-table::\n   :header-rows: 1\n   :widths: 45 55\n\n"
    table += row("Metric", "Value")
    table += row("AFP snapshot", m.get("afp_version", "unknown"))
    table += row("Files sampled", m.get("sample_size", "?"))
    table += row("Parse coverage", f"{m.get('coverage_pct')}% ({m.get('ok')} parsed)")
    table += row(
        f"Timeouts (> {m.get('timeout_budget_s')}s)",
        f"{m.get('timeout_pct')}% ({m.get('timeout')})",
    )
    table += row("Throughput", throughput)
    table += row("Median parse time (parsed files)", median_s)
    table += row("Measured", m.get("measured_at", "?"))
    table += (
        "\n*Coverage is the share of a seeded random sample of AFP theory files "
        "that parse within the timeout; a whole file counts as failed if any "
        "statement fails. Updated weekly by the metrics workflow.*\n"
    )
    return table


def main() -> None:
    m = json.load(open(METRICS))
    text = open(README).read()
    block = build_table(m)
    start, end = ".. METRICS:START", ".. METRICS:END"
    i = text.find(start)
    j = text.find(end)
    if i == -1 or j == -1 or j < i:
        raise SystemExit(
            "METRICS markers not found in README; expected "
            "'.. METRICS:START' and '.. METRICS:END'."
        )
    new = text[: i + len(start)] + "\n\n" + block + "\n" + text[j:]
    open(README, "w").write(new)
    print(f"Updated {README}.")


if __name__ == "__main__":
    main()
