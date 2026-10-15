"""Check that the portable scientific data preserves feasibility and provenance."""
from pathlib import Path
import hashlib
import json
import re
import numpy as np
import pytest

ROOT=Path(__file__).resolve().parents[1]
DATA=json.loads((ROOT/"docs/numerical-data/solutions.json").read_text())
SAVED=[*DATA["finite"]["solutions"],DATA["finite"]["balanced"],*DATA["infinite"]["solutions"]]

@pytest.mark.parametrize("r",SAVED,ids=lambda r:f"{'balanced' if r['balanced'] else r['epsilon']}-{r['nx']}cells")
def test_saved_fields_satisfy_full_matrix_equation(r):
    g=np.asarray(r["rho"]);q=np.asarray(r["flux"]);reaction=np.asarray(r["reaction"])
    assert g.shape==(r["nt"]+1,r["nx"],2,2)
    assert q.shape==(r["nt"],r["nx"]+1,2,2)
    assert reaction.shape==(r["nt"],r["nx"],2,2)
    assert np.isfinite(g).all() and np.isfinite(q).all() and np.isfinite(reaction).all()
    assert np.max(np.abs(g-g.swapaxes(-1,-2)))<1e-8
    assert np.linalg.eigvalsh(g).min()>-1e-7
    assert np.max(np.abs(q[:,[0,-1]]))==0
    symq=(q+q.swapaxes(-1,-2))/2
    symr=(reaction+reaction.swapaxes(-1,-2))/2
    ce=np.diff(g,axis=0)/r["dt"]+np.diff(symq,axis=1)/r["dx"]-symr
    assert np.linalg.norm(ce,axis=(-1,-2)).max()<1e-7
    tv=r["dt"]*r["dx"]*np.linalg.norm(reaction,axis=(-1,-2)).sum()
    assert tv==pytest.approx(r["reaction_tv"],rel=1e-12,abs=1e-12)
    assert r["primal_transport"]+r["primal_reaction"]==pytest.approx(r["primal_total"],abs=1e-12)
    if r["balanced"]:assert not reaction.any()

def test_embedded_data_and_source_hashes_are_exact():
    html=(ROOT/"docs/numerical.html").read_text()
    match=re.search(r'<script type="application/json" id="solution-data">(.*?)</script>',html,re.S)
    assert match and json.loads(match.group(1))==DATA
    assert "__NUMERICAL_DATA__" not in html
    assert DATA["metadata"]["seed"]==921
    assert DATA["metadata"]["mlflow_run_id"]
    for name,digest in DATA["metadata"]["source"]["source_sha256"].items():
        # Archived results bind their actual runtime sources; current sources
        # may receive later portability fixes without rewriting those results.
        source=ROOT/"docs/numerical-data/source"/name
        assert hashlib.sha256(source.read_bytes()).hexdigest()==digest,name
