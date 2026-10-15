"""Solve a matrix-valued finite-volume study and export portable evidence.

Use track_experiment.py to record a research run in MLflow. This CLI remains
independent of the tracking client so the solver has a small dependency set.
"""
from __future__ import annotations
import argparse
import csv
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import subprocess
import time
import numpy as np
from numerical.solver import solve_transport, BalancedInfeasibleError

ROOT = Path(__file__).resolve().parents[1]
SEED = 921
TOLERANCE = 1e-10


def endpoints(nx: int) -> tuple[np.ndarray, np.ndarray]:
    """Noncommuting PSD mixtures with exactly matched integrated matrices."""
    x = (np.arange(nx) + .5) / nx
    rng = np.random.default_rng(SEED)
    angles = [.30 + float(rng.uniform(-.025,.025)), -0.68 + float(rng.uniform(-.025,.025))]
    mats = []
    for angle, eig in zip(angles, ([.8,.2],[.65,.35])):
        u = np.array([[np.cos(angle), -np.sin(angle)], [np.sin(angle), np.cos(angle)]])
        mats.append(u @ np.diag(eig) @ u.T)
    def bump(center):
        y = np.exp(-.5*((x-center)/.08)**2)
        return y / (y.sum()/nx)
    def field(ca, cb):
        return bump(ca)[:,None,None]*mats[0] + .7*bump(cb)[:,None,None]*mats[1] + .025*np.eye(2)[None,:,:]
    return field(.23,.64), field(.55,.80)


def source_state() -> dict:
    def git(*args):
        return subprocess.check_output(["git",*args],cwd=ROOT,text=True).strip()
    files = sorted((ROOT/"numerical").glob("*.py")) + [ROOT/"numerical/requirements.txt"]
    return {"git_commit":git("rev-parse","HEAD"),"git_branch":git("branch","--show-current"),
            "git_dirty":bool(git("status","--porcelain")),
            "source_sha256":{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}}


def run(output: Path, run_id: str | None, nx: int=16, nt: int=16) -> dict:
    output.mkdir(parents=True,exist_ok=True)
    metadata = {"seed":SEED,"seed_display":"0921","mlflow_experiment":"matrix-transport-reaction-zero",
                "mlflow_run_id":run_id,"mesh":{"nx":nx,"nt":nt,"length":1.0,"duration":1.0},
                "solver":"CLARABEL","tolerance":TOLERANCE,"model":"2x2 staggered finite-volume SDP",
                "versions":{p:importlib.metadata.version(p) for p in ["cvxpy","clarabel","numpy","scipy"]},
                "source":source_state(),"created_utc":time.strftime("%Y-%m-%dT%H:%M:%SZ",time.gmtime())}
    data = {"metadata":metadata,"finite":{"solutions":[]},"infinite":{"solutions":[]},"refinement":[],"analytical_validation":[]}
    rows = []
    def compute(scenario, a, b, h, ntime, epsilon):
        print(f"Solving {scenario}: nx={len(a)} nt={ntime} epsilon={epsilon}",flush=True)
        result = solve_transport(a,b,h,nt=ntime,tolerance=TOLERANCE)
        if result["status"] != "optimal" or result["diagnostics"] is None:
            raise RuntimeError(f"Numerical solve failed for {scenario}: {result['status']}; {result.get('reason', '')}")
        result["epsilon"] = epsilon
        result["H"] = None if h is None else h.tolist()
        diag = result["diagnostics"]
        if (diag["ce_max_scaled_residual"] > 1e-7 or
            diag["endpoint_max_scaled_residual"] > 1e-7 or
            diag["cone_max_scaled_violation"] > 1e-7 or
            diag["relative_primal_dual_gap"] is None or
            diag["relative_primal_dual_gap"] > 1e-7):
            raise RuntimeError(f"Numerical diagnostics exceed acceptance thresholds: {scenario}")
        slack = diag["independent_objective_epigraph_slack"]
        if slack is None or abs(slack) > 2e-7*max(1.,abs(result["primal_total"])):
            raise RuntimeError(f"Epigraph/quadratic cost reconstruction mismatch: {scenario}")
        rows.append({"scenario":scenario,"nx":len(a),"nt":ntime,"epsilon":epsilon,
                     "total":result["primal_total"],"transport":result["primal_transport"],
                     "reaction":result["primal_reaction"],"reaction_tv":result["reaction_tv"],
                     "ce_residual":diag["ce_max_frobenius_residual"],"min_mass_eigenvalue":diag["rho_min_eigenvalue"],
                     "relative_dual_gap":diag["relative_primal_dual_gap"],"epigraph_cost_slack":slack,
                     "scaled_cone_violation":diag["cone_max_scaled_violation"],
                     "status":result["status"],"runtime_seconds":result["runtime_seconds"]})
        return result
    start = time.perf_counter()
    a,b = endpoints(nx)
    balanced = compute("finite-balanced",a,b,None,nt,None)
    data["finite"]["balanced"] = balanced
    data["finite"]["initial_integrated_matrix"] = (a.sum(axis=0)/nx).tolist()
    data["finite"]["final_integrated_matrix"] = (b.sum(axis=0)/nx).tolist()
    for epsilon in [1.,.4,.16,.064,.0256]:
        data["finite"]["solutions"].append(compute("finite",a,b,epsilon*np.diag([1.,.55]),nt,epsilon))
    aa = np.tile(np.diag([1.2,.3]),(6,1,1)); bb = np.tile(np.diag([.3,1.2]),(6,1,1))
    try:
        solve_transport(aa,bb,None,nt=nt)
    except BalancedInfeasibleError:
        data["infinite"]["balanced_infeasible"] = True
    else:
        raise RuntimeError("Balanced-incompatible endpoints were not rejected")
    data["infinite"]["analytical_scaled_cost"] = 1.2
    data["infinite"]["invariant"] = "Entrywise divergence preserves the full integrated matrix; endpoints have equal trace but different integrated matrices."
    for epsilon in [1.,.5,.25,.125,.0625]:
        result = compute("infinite",aa,bb,epsilon*np.eye(2),nt,epsilon)
        result["analytical_cost"] = 1.2/epsilon**2
        data["infinite"]["solutions"].append(result)
    for n in sorted(set([8,12,nx,24])):
        ar,br=endpoints(n)
        if n==nx and nt==n:
            bal=balanced; small=data["finite"]["solutions"][-1]
        else:
            bal=compute("refinement-balanced",ar,br,None,n,None)
            small=compute("refinement-small-H",ar,br,.0256*np.diag([1.,.55]),n,.0256)
        data["refinement"].append({"nx":n,"nt":n,"balanced_value":bal["primal_total"],
                                   "unbalanced_value":small["primal_total"],
                                   "reaction_tv":small["reaction_tv"],"epsilon":.0256})
    for ntime in [4,8,16,32]:
        r=compute("analytic-time-refinement",aa[:1],bb[:1],np.eye(2),ntime,1.)
        data["analytical_validation"].append({"nt":ntime,"computed":r["primal_total"],"exact":1.2,
                                              "relative_error":abs(r["primal_total"]-1.2)/1.2,
                                              "ce_residual":r["diagnostics"]["ce_max_frobenius_residual"]})
    data["metadata"]["runtime_seconds"] = time.perf_counter()-start
    # Scientific validity checks; these do not constitute certified numerical bounds.
    if not all(r["status"]=="optimal" for r in rows):
        raise RuntimeError("A numerical solve did not report optimal status")
    max_ce=max(float(r["ce_residual"]) for r in rows)
    if max_ce > 2e-6 or min(float(r["min_mass_eigenvalue"]) for r in rows) < -2e-6:
        raise RuntimeError("The solve residual/PSD quality threshold was exceeded")
    bv=balanced["primal_total"]; sols=data["finite"]["solutions"]
    vals=np.array([r["primal_total"] for r in sols])
    if np.any(np.diff(vals)<-1e-6) or np.any(vals>bv+1e-6):
        raise RuntimeError("Scalar shrinking of the fixed anisotropic H violates the expected discrete cost ordering")
    data["metrics"]={"finite_balanced_value":bv,"finite_small_H_value":float(vals[-1]),
                     "finite_small_H_relative_gap":float((bv-vals[-1])/bv),
                     "finite_large_H_reaction_tv":sols[0]["reaction_tv"],
                     "finite_small_H_reaction_tv":sols[-1]["reaction_tv"],
                     "maximum_ce_residual":max_ce,
                     "maximum_relative_dual_gap":max(r["relative_dual_gap"] for r in rows),
                     "maximum_relative_epigraph_slack":max(abs(r["epigraph_cost_slack"])/max(1.,abs(r["total"])) for r in rows),
                     "maximum_scaled_cone_violation":max(r["scaled_cone_violation"] for r in rows),
                     "analytic_nt32_relative_error":data["analytical_validation"][-1]["relative_error"],
                     "runtime_seconds":data["metadata"]["runtime_seconds"]}
    (output/"solutions.json").write_text(json.dumps(data,indent=None,allow_nan=False),encoding="utf-8")
    with (output/"metrics.csv").open("w",newline="",encoding="utf-8") as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
    (output/"summary.json").write_text(json.dumps({"metadata":metadata,"metrics":data["metrics"],
                                                "refinement":data["refinement"],"analytical_validation":data["analytical_validation"]},indent=2),encoding="utf-8")
    plots(data,output)
    print(json.dumps(data["metrics"],indent=2),flush=True)
    return data


def plots(data,output):
    os.environ.setdefault("MPLCONFIGDIR",str(ROOT/".verification/matplotlib"))
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    plt.rcParams.update({"font.family":"DejaVu Sans","font.size":10,"axes.spines.top":False,"axes.spines.right":False})
    fig,axes=plt.subplots(1,3,figsize=(13,3.8))
    ss=data["finite"]["solutions"]; eps=[r["epsilon"] for r in ss]
    axes[0].semilogx(eps,[r["primal_total"] for r in ss],"o-",color="#147a94",label="Unbalanced SDP")
    axes[0].axhline(data["finite"]["balanced"]["primal_total"],color="#ce8140",linestyle="--",label="Same-grid balanced")
    axes[0].set(xlabel="Reaction weight ε",ylabel="Total action",title="Finite balanced value"); axes[0].legend(fontsize=8)
    axes[1].loglog(eps,[r["reaction_tv"] for r in ss],"o-",color="#147a94")
    axes[1].set(xlabel="Reaction weight ε",ylabel="Reaction Frobenius TV",title="Reaction extinction")
    ii=data["infinite"]["solutions"]; ie=[r["epsilon"] for r in ii]
    axes[2].loglog(ie,[r["primal_total"] for r in ii],"o-",color="#a45843",label="Computed, fixed grid")
    axes[2].loglog(ie,[r["analytical_cost"] for r in ii],"--",color="#193b53",label="Continuous: 1.2 / ε²")
    axes[2].set(xlabel="Reaction weight ε",ylabel="Total action",title="Equal trace, incompatible matrices");axes[2].legend(fontsize=8)
    for ax in axes:ax.grid(alpha=.18);ax.invert_xaxis()
    fig.tight_layout();fig.savefig(output/"convergence.png",dpi=190);fig.savefig(output/"convergence.pdf");plt.close(fig)


if __name__=="__main__":
    parser=argparse.ArgumentParser();parser.add_argument("--output",type=Path,default=ROOT/"docs/numerical-data")
    parser.add_argument("--mlflow-run-id");args=parser.parse_args()
    run(args.output,args.mlflow_run_id)
