"""Embed actual solved fields in a self-contained offline numerical explorer."""
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parents[1]
def render():
    data=json.loads((ROOT/"docs/numerical-data/solutions.json").read_text())
    payload=json.dumps(data,separators=(",",":"),allow_nan=False).replace("<","\\u003c")
    template=(ROOT/"numerical/demo_template.html").read_text()
    if template.count("__NUMERICAL_DATA__")!=1:
        raise ValueError("The data placeholder must occur exactly once")
    target=ROOT/"docs/numerical.html"
    target.write_text(template.replace("__NUMERICAL_DATA__",payload),encoding="utf-8")
    print(f"Created {target.relative_to(ROOT)} ({target.stat().st_size:,} bytes), fully offline")

if __name__=="__main__":render()
