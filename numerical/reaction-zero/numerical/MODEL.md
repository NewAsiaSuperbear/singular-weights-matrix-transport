# Matrix finite-volume SDP: model and numerical checks

This is a numerical illustration of the reaction-weight-zero theorem. The SDP is a finite
spatial/time discretization, not a new Lean-certified discretization theorem. Fixed-grid
parameter convergence and mesh-refinement evidence are separate questions.

本实验展示离散矩阵输运模型的小反应权重行为。固定网格极限应与同一网格的平衡 SDP
比较；网格细化再与连续模型比较。求解器结果不替代连续定理或离散格式收敛证明。

## Variables and conservation

Use a one-dimensional interval of length `ell`, `Nx` equal cells of width `dx=ell/Nx`,
and `Nt` time intervals of width `dt=1/Nt`.

- `G[k,i]` is a symmetric PSD **cell-average density** at time node `k=0,...,Nt`.
  It is not a cell mass already multiplied by `dx`.
- `Q[k,f]` is a full, possibly nonsymmetric, `2×2` flux on each interior face during time
  interval `k`. Both exterior faces have flux zero.
- `R[k,i]` is a full, possibly nonsymmetric, cell reaction density during time interval `k`.
- `Sq[k,f]` and `Sr[k,i]` are symmetric epigraph variables; the block cones below automatically
  make them PSD.

Let `sym(A)=(A+A.T)/2`. The finite-volume equation is

\[
\frac{G_{k+1,i}-G_{k,i}}{dt}
+\frac{\operatorname{sym}Q_{k,i+1/2}-\operatorname{sym}Q_{k,i-1/2}}{dx}
=\operatorname{sym}R_{k,i}.
\]

This sign agrees with the paper's `∂t G + Dq = R_sym` for entrywise matrix divergence.
Summing over cells telescopes the no-flux boundary terms and gives the exact matrix identity

\[
dx\sum_i(G_{Nt,i}-G_{0,i})
=dt\,dx\sum_{k,i}\operatorname{sym}R_{k,i}.
\]

For the balanced SDP impose **the entire matrix `R=0`**. The complete integrated endpoint
matrix must then agree, not just its trace. Full `Q` and `R` should be retained: for noncommuting
mass matrices, minimizing over their skew parts can affect the action even though the CE sees
their symmetric parts.

## Action and cone normalization

Define

\[
X_{k,i}=\frac{G_{k,i}+G_{k+1,i}}2,
\qquad X_{k,f}=\frac{X_{k,i}+X_{k,i+1}}2.
\]

For transport weight `L=I₂` and SPD reaction weight `H`, impose

\[
\begin{pmatrix}X_{k,f}&Q_{k,f}\\Q_{k,f}^{T}&S^q_{k,f}\end{pmatrix}\succeq0,
\qquad
\begin{pmatrix}X_{k,i}&R_{k,i}H^{-1}\\(R_{k,i}H^{-1})^{T}&S^r_{k,i}\end{pmatrix}\succeq0.
\]

Minimize

\[
E_h=\frac{dt\,dx}{2}
\left(\sum_{k,f\ \mathrm{interior}}\operatorname{tr}S^q_{k,f}
+\sum_{k,i}\operatorname{tr}S^r_{k,i}\right).
\]

The generalized Schur complement gives exactly the local extended costs
`tr(Q.T X† Q)/2` and `tr((R H⁻¹).T X† (R H⁻¹))/2`, including the required range constraints
when `X` is singular. Multiplication by `H⁻¹` is on the **right**; switching the order changes
the model for noncommuting matrices. The coefficient `1/2` is the paper's normalization.
Interior face quadrature has width `dx`; omitted boundary-face terms have prescribed zero flux.

For `H=epsilon*diag(1,0.55)`, its Frobenius norm is `epsilon*sqrt(1+0.55²)`, not exactly
`epsilon`. One conditioning option is to use `R=epsilon*W`: the reaction block then contains
`W*diag(1,0.55)⁻¹`, and the CE contains `epsilon*sym(W)`. This is an exact change of variables,
not a different action.

## Finite balanced example

Use two noncommuting PD component matrices with distinct spatial density profiles and their
translated counterparts. Sampling, truncation or interpolation must preserve each component's
integral, so the integrated matrix agrees to floating-point accuracy on **every** grid. Matching
only the scalar trace is insufficient. A strictly positive background can keep the cones away
from severe singular-density effects; report its size and keep it fixed across refinements.

A uniform background should stay stationary. Assigning a rigid-translation flux `Q=vG` to a
background that reaches the exterior boundary violates no-flux conditions. Alternatively, for
any matched PD endpoint arrays an explicit balanced feasible competitor is

\[
G_{k,i}=(1-t_k)G_{0,i}+t_kG_{Nt,i},\qquad
Q_{k,i+1/2}=-dx\sum_{r\le i}(G_{Nt,r}-G_{0,r}),\qquad R=0.
\]

The final cumulative flux is zero by integrated matrix matching. Positive definite endpoint
arrays give positive definite time/face averages, so this competitor has finite action. It
supplies a useful independent feasible upper bound for the balanced solver value.

At fixed grid compare `v_h(epsilon)` with the separately solved balanced value `b_h`.
The exact SDP should satisfy `v_h(epsilon)≤b_h`. With this fixed scalar scaling of `H`, reducing
`epsilon` enlarges the reaction penalty, so `v_h(epsilon)` is nondecreasing as `epsilon` decreases.
For a finite balanced value, reaction TV should decrease toward zero; a fitted slope of exactly
one is not required by the theorem.

## Infinite balanced example and the time-quadrature trap

Let the spatially uniform endpoint **densities** be

\[
A=\operatorname{diag}(1.2,0.3),\qquad
B=\operatorname{diag}(0.3,1.2),\qquad H=\epsilon I.
\]

Their traces agree, while their full integrated matrices differ. Therefore the balanced problem
is infeasible on every grid and in the continuum. A constant symmetric test selecting the first
diagonal entry proves this directly.

The continuous minimum is

\[
E_{\mathrm{cont}}(\epsilon)
=\frac{2\,ell}{\epsilon^2}\sum_{a=1}^{2}(\sqrt{B_{aa}}-\sqrt{A_{aa}})^2
=\frac{1.2\,ell}{\epsilon^2}.
\]

It is attained by `Q=0` and the uniform diagonal square-root-linear path. A lower bound follows
by bounding reaction cost by the diagonal reaction costs, then using the total mass of each
diagonal coordinate and Cauchy–Schwarz. Off-diagonal mass/reaction or spatial flux cannot improve
that lower bound. The constant `1.2` requires a unit-length domain.

**Do not require this continuous constant at a finite time grid.** Arithmetic time averaging
is midpoint quadrature for a convex matrix perspective and can underestimate the continuous
action. For `Nt=1`, `X=(A+B)/2=0.75 I` and `R=B-A=diag(-0.9,0.9)`, so the exact uniform SDP
value is

\[
\frac{ell}{2\epsilon^2}\operatorname{tr}(R^T X^{-1}R)
=\frac{1.08\,ell}{\epsilon^2},
\]

not `1.2*ell/epsilon²`. The one-step value is globally optimal: spatial averaging cannot reduce
this convex quadratic reaction cost, and flux adds a nonnegative cost.

On each fixed grid, examine the coefficient `epsilon²*v_h(epsilon)` and its stability across
reaction weights. Compare that coefficient with `1.2*ell` only through **time refinement**.
Spatial refinement alone does not remove this uniform example's time-quadrature error. Changing
both grids together can obscure which discretization causes the error.

Reaction TV need not tend to zero in this infinite-value example. Its energy is unbounded as
`epsilon→0`, outside the bounded-energy/finite-balanced-value reaction-extinction conclusion.

## Verification and reporting

For every solve record solver/version, tolerances, status, primal and dual objectives when
available, objective gap, iteration count and timing. An `optimal_inaccurate` label without
small verified residuals is insufficient evidence of the proposed limit.

Report at least:

- Full integrated endpoint matrix mismatch, and the exact balanced-invariant infeasibility test.
- Maximum CE and endpoint residuals, with a stated absolute and scaled normalization.
- Minimum eigenvalues of all nodal mass matrices and all `4×4` Schur blocks; scale cone residuals
  by block size when the reaction weights create large epigraph entries.
- Separately reconstructed transport and reaction epigraph objective contributions, whose sum
  is the reported objective.
- Discrete Frobenius reaction variation `dt*dx*sum(norm(R[k,i], 'fro'))` and the integrated
  reaction matrix appearing in the conservation identity.
- Finite-case comparisons with `b_h` and an independently evaluated explicit balanced competitor;
  infinite-case scaled coefficients and time-refinement error.
- Noncommutativity of the actual finite-case matrix profiles, not just of unused component matrices.

Do not reconstruct a trustworthy objective by silently applying a numerical pseudoinverse at
nearly singular `X`: discarded range violations can make that calculation falsely cheap.
The actual block feasibility and primal/dual gap are essential. Solver error may dominate small
reaction-TV values or the balanced-value gap at tiny `epsilon`.

Use fixed physical profiles and translations across grids. First vary `epsilon` on a fixed
grid; then refine space/time and resolve the corresponding balanced baseline. These experiments
illustrate the expected behavior, but neither empirical refinement nor the continuous Lean
certificate proves consistency/convergence of this particular finite-volume scheme or a joint
mesh/weight limit.

The reproducibility seed is `0921` (integer `921` in code). The supplied numerical
results contain computed solutions, residuals, solver versions, configuration and
source hashes. See [the example README](../README.md) for the standalone command,
saved results and optional MLflow tracking. Tracking IDs are recorded only when
supplied by a real external run; standalone reproduction records a null run ID.
