"""Measure parser coverage and performance against an AFP corpus.

Parses a fixed (seeded) random sample of theory files from the corpus, recording
how many parse successfully and how fast, and writes the figures to
``metrics/metrics.json``. A per-file timeout bounds the run; timeouts count as
"not parsed" (the Earley chart can grow super-linearly on large files).

Configuration via environment variables:
  CORPUS_DIR       corpus location (default: corpus)
  METRICS_SAMPLE   number of files to sample (default: 500; 0 = all)
  METRICS_TIMEOUT  per-file timeout in seconds (default: 15)
  METRICS_SEED     RNG seed for the sample (default: 42)
  METRICS_OUT      output path (default: metrics/metrics.json)
"""

import datetime
import glob
import json
import os
import random
import signal
import statistics
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from typing import Any

# Make isabelle_parser importable in pool workers regardless of start method
# (spawn/forkserver re-import this module, re-running this line) or whether the
# package is installed.
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

CORPUS = os.environ.get("CORPUS_DIR", "corpus")
SAMPLE = int(os.environ.get("METRICS_SAMPLE", "500"))
TIMEOUT = int(os.environ.get("METRICS_TIMEOUT", "15"))
SEED = int(os.environ.get("METRICS_SEED", "42"))
OUT = os.environ.get("METRICS_OUT", "metrics/metrics.json")

_parser = None


def _get_parser() -> Any:
    global _parser
    if _parser is None:
        from isabelle_parser import load_parser

        _parser = load_parser()
    return _parser


def _parse_one(path: str) -> tuple[str, int, float]:
    try:
        data = open(path, errors="replace").read()
    except Exception:
        return ("error", 0, 0.0)
    size = len(data.encode("utf-8", "replace"))

    def _alarm(signum: int, frame: Any) -> None:
        raise TimeoutError()

    signal.signal(signal.SIGALRM, _alarm)
    signal.setitimer(signal.ITIMER_REAL, TIMEOUT)
    start = time.time()
    try:
        _get_parser().parse(data)
        status = "ok"
    except TimeoutError:
        status = "timeout"
    except Exception:
        status = "fail"
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
    return (status, size, time.time() - start)


def main() -> None:
    files = sorted(glob.glob(os.path.join(CORPUS, "**", "*.thy"), recursive=True))
    if not files:
        raise SystemExit(f"No .thy files found under '{CORPUS}'.")
    random.seed(SEED)
    random.shuffle(files)
    if SAMPLE:
        files = files[:SAMPLE]

    version = "unknown"
    vfile = os.path.join(CORPUS, "AFP_VERSION")
    if os.path.exists(vfile):
        version = open(vfile).read().strip()

    workers = os.cpu_count() or 2
    counts = {"ok": 0, "fail": 0, "timeout": 0, "error": 0}
    ok_times = []
    total_bytes = 0
    wall_start = time.time()
    with ProcessPoolExecutor(max_workers=workers) as ex:
        for fut in as_completed([ex.submit(_parse_one, f) for f in files]):
            status, size, dt = fut.result()
            counts[status] += 1
            total_bytes += size
            if status == "ok":
                ok_times.append(dt)
    wall = time.time() - wall_start

    attempted = len(files)
    metrics = {
        "afp_version": version,
        "sample_size": attempted,
        "workers": workers,
        "timeout_budget_s": TIMEOUT,
        "ok": counts["ok"],
        "fail": counts["fail"],
        "timeout": counts["timeout"],
        "error": counts["error"],
        "coverage_pct": round(100 * counts["ok"] / attempted, 1),
        "timeout_pct": round(100 * counts["timeout"] / attempted, 1),
        "wall_seconds": round(wall, 1),
        "files_per_sec": round(attempted / wall, 2) if wall else None,
        "mb_per_sec": round(total_bytes / 1e6 / wall, 3) if wall else None,
        "median_ok_parse_s": round(statistics.median(ok_times), 3)
        if ok_times
        else None,
        "measured_at": datetime.datetime.now(datetime.timezone.utc).strftime(
            "%Y-%m-%d %H:%M UTC"
        ),
    }

    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w") as fh:
        json.dump(metrics, fh, indent=2)
        fh.write("\n")
    print(json.dumps(metrics, indent=2))


if __name__ == "__main__":
    main()
