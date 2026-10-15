"""Optional tracking entry point; requires --python, --output and --tracking-uri.

The shared wrapper creates a real MLflow run without requiring Git history or
writing over the supplied archived solutions.
"""
from pathlib import Path
import sys


def main(argv=None):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from track_example import main as track
    return track(["--example", "reaction-zero", *(sys.argv[1:] if argv is None else argv)])


if __name__ == "__main__":
    raise SystemExit(main())
