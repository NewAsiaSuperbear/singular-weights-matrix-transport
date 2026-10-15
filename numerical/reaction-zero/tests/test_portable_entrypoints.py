"""Source-archive provenance and offline HTML regressions; no scientific sweep."""
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import shutil
import subprocess

import pytest

from numerical import run_experiments

ROOT = Path(__file__).resolve().parents[1]


def test_source_archive_retains_hashes_without_claiming_clean_git(tmp_path, monkeypatch):
    source = tmp_path / "numerical"
    source.mkdir()
    (source / "solver.py").write_text("# source fixture\n")
    (source / "requirements.txt").write_text("numpy\n")
    monkeypatch.setattr(run_experiments, "ROOT", tmp_path)
    # Disallow Git discovery even if the temporary directory is in a parent repo.
    def missing_git(*args, **kwargs):
        raise FileNotFoundError("git is not installed")
    monkeypatch.setattr(run_experiments.subprocess, "check_output", missing_git)
    state = run_experiments.source_state()
    assert state["git_commit"] is None
    assert state["git_branch"] is None
    assert state["git_dirty"] is None
    assert state["repository_detected"] is False
    assert state["source_sha256"] == {
        "numerical/solver.py": hashlib.sha256((source / "solver.py").read_bytes()).hexdigest(),
        "numerical/requirements.txt": hashlib.sha256((source / "requirements.txt").read_bytes()).hexdigest(),
    }


class Links(HTMLParser):
    def __init__(self):
        super().__init__()
        self.links = []

    def handle_starttag(self, tag, attrs):
        if tag == "a":
            self.links.extend(value for key, value in attrs if key == "href")


@pytest.mark.parametrize("name", ["docs/numerical.html", "numerical/demo_template.html"])
def test_offline_report_links_exist(name):
    parser = Links()
    parser.feed((ROOT / name).read_text())
    for href in parser.links:
        if not href.startswith(("https://", "http://", "#")):
            # Template URLs resolve from the generated page's directory.
            assert (ROOT / "docs" / href.split("#", 1)[0]).is_file(), href


def test_built_html_preserves_original_solution_arrays():
    page = (ROOT / "docs/numerical.html").read_text()
    payload = re.search(r'<script type="application/json" id="solution-data">(.*?)</script>', page, re.DOTALL).group(1)
    assert json.loads(payload) == json.loads((ROOT / "docs/numerical-data/solutions.json").read_text())


@pytest.mark.skipif(shutil.which("node") is None, reason="Node is needed for JavaScript execution")
def test_missing_tracking_id_is_rendered_without_javascript_error():
    template = (ROOT / "numerical/demo_template.html").read_text()
    function = re.search(r"function trackingLabel\(runId\)\{[^\n]+\}", template).group(0)
    code = function + "\nprocess.stdout.write(JSON.stringify([trackingLabel(null),trackingLabel(undefined),trackingLabel(''),trackingLabel('0123456789abcdef')]))"
    result = subprocess.run(["node", "-e", code], check=True, text=True, capture_output=True)
    assert json.loads(result.stdout) == ["Tracking not enabled"] * 3 + ["MLflow run 0123456789ab…"]
