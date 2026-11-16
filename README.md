# Minimum first-order detuning residual for qubit π gates at fixed duration

**Tingyu Zhang and Yan Cen**
Department of Physics, Fudan University, Shanghai, China

For arbitrary measurable transverse controls satisfying
$u_x^2+u_y^2\le\Omega^2$ and an exact nominal full qubit π gate,
define the dimensionless first-order detuning residual
$\mathbf R=\Omega\int_0^T\mathbf n(t)\,dt$, where
$\mathbf n(t)\cdot\boldsymbol\sigma=U_0(t)^\dagger\sigma_zU_0(t)$.
Its exact minimum is

$$\min_u|\mathbf R|=4\cos\frac{L-\pi}{4}-2,\qquad
\pi\le L=\Omega T\le\frac{7\pi}{3}.$$

All attaining controls are the same-axis three-segment family and its
overall negative, with durations $(a,2a+\pi,a)/\Omega$ and $a=(L-\pi)/4$.
A midpoint comparison proves the bound and all equality cases.
The zero-residual endpoint gives the minimum first-order robust time
$7\pi/(3\Omega)$.

The manuscript completes this proof before developing the physical
consequences. It then derives the fidelity coefficient
$\chi=|\mathbf R|^2/6$, the known weak-dissipation time cost, and the
optimal compensation level in the leading combined-noise budget.
Average gate fidelity, fidelity susceptibility and additive weak-noise
budgets are established quantities, attributed to their original sources
in Sec. 5. The two manuscripts share 32 references.

## Papers

- [English manuscript (PDF)](paper/manuscript.pdf) · [LaTeX](paper/manuscript.tex)
- [中文论文（PDF）](paper/manuscript_zh.pdf) · [LaTeX](paper/manuscript_zh.tex)
- [Shared bibliography](paper/references.bib)
- [Author review notes / 作者校阅说明](AUTHOR_REVIEW.md)

The two versions contain the same scientific results and use the official
IOP `iopjournal` template for a non-anonymous Paper in Quantum Science
and Technology. The data and code availability statements link to the
published reproducibility archive (version 1.0.0):
[10.5281/zenodo.24154006](https://doi.org/10.5281/zenodo.24154006).
The QST revision in this repository includes the
[full-channel data](paper/assets/frontier_full_channel.json),
[duration-switch data](paper/assets/frontier_working_point.json),
[figure reproduction script](paper/build_frontier_figure.py), and
[paper-to-Lean coverage map](lean/paper-coverage.md). These additions are
not part of the previously published v1.0.0 Zenodo archive. No journal
submission or acceptance is claimed.

## Reproduce the manuscripts

Use a TeX distribution with BibTeX, natbib, Latin Modern and ctex.
The official `iopjournal.cls` is included without modification; the
manuscript suppresses its unpublished journal/date placeholders.
Numeric references use the standard `unsrtnat` style. From `paper/`:

```sh
pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex
bibtex manuscript
pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex
pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex

xelatex -interaction=nonstopmode -halt-on-error manuscript_zh.tex
bibtex manuscript_zh
xelatex -interaction=nonstopmode -halt-on-error manuscript_zh.tex
xelatex -interaction=nonstopmode -halt-on-error manuscript_zh.tex
```

The checked-in PDFs and generated `.bbl` files correspond to the source
files. Both languages share five scientific figures and English captions. The QST
revision contains 21 English pages and 18 Chinese pages, with 48 numbered
equations. The reviewed abstract, core definitions and proofs are preserved.

## Lean 4 formalization

[Proof overview and build instructions](lean/README.md)

The 47 source modules formalize the original AC/a.e. quantum dynamics,
the true fidelity susceptibility, the full continuous frontier, and every
attaining control for arbitrary Ω>0. They also prove the weak Lindblad
expansion from the actual channel average, its fourth-order averaged
remainder, and the global leading-budget working-point results.
The geometric minimum is attained in every dimension d≥2.
All 1237 project declarations passed an exhaustive axiom audit on 2026-11-04.
The subsequently added explicit switching threshold and maximal 4.91%
relative leading-budget gain are analytically derived and numerically checked;
these refinements have not been added to the Lean formalization.

```sh
cd lean
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean 4.35.0 and mathlib v4.35.0 are pinned. The source contains no `sorry`,
`admit`, custom axioms or `native_decide`. The principal theorems depend only
on `propext`, `Classical.choice` and `Quot.sound`.

## Numerical checks and figures

```sh
python -m pip install -r requirements.txt
python numerics/verify_solution.py
python numerics/check_budget.py
python paper/build_figure.py
python paper/build_frontier_figure.py
```

The numerical script uses direct 2×2 matrix exponentials and Fréchet
derivatives. Its recorded output is in [verification.json](numerics/verification.json).
Floating-point calculations check conventions and implementation; the
original robust-time result follows from the analytical and formal proofs.
The standard-library budget check reproduces the explicit duration switch
and maximal relative gain; its output is [numbers.json](numerics/numbers.json).
The figure scripts reconstruct the direction and error curves, the two distance-envelope branches, the short-CORPSE pulse, and the analytical frontier with its leading-order working points. The working-point solver
compares all stationary points with both endpoint pulses; its generated
data accompany the figures in `paper/assets/`.

本仓库包含中英双语论文、共享参考文献与科学图、Lean 4 证明及必要复现脚本。
论文主线为“完整门与失谐响应—球面中点锐界—完整速度与敏感度边界—补偿程度选择”。
本轮修订内容、验证结果与公开归档入口见作者校阅说明。

## Finite-noise check in the QST revision

`paper/build_frontier_figure.py` rebuilds both Fig. 4 and Fig. 5 and their
JSON data. Figure 5 uses Gaussian quasistatic detuning with s=0.03,
Gamma1=0 and Gamma_phi/Omega=3 lambda s², at lambda=0.025, lambda_c
and 0.22. Segmentwise 3×3 Bloch-matrix exponentials are averaged by
32-point Gauss–Hermite quadrature. Full-channel values at the analytic
working points are computed directly, separately from the 81-point scans.
The maximum 32/48-point quadrature difference, including the additional
prescription check below, is 2.23e-15. At lambda_c, higher-order terms favor the rectangular pulse over
the leading-budget interior minimizer by 2.57e-6 in absolute infidelity.

The same script also evaluates lambda=1/(2 pi) at s=0.03 in the same
pure-dephasing model. The leading-budget choice lowers the full-channel
infidelity by 4.64% relative to the better endpoint. Numerical duration
reoptimization within the three-segment family improves it by a further
1.44e-8. A 129-point scan covers [pi, 7 pi/3]; each sampled interior
minimum is refined with bounded scalar minimization and compared with
both endpoints. The `prescription_check` entry in the full-channel JSON
stores this scan, the candidates, both selected durations, and the
32/48-point quadrature checks. These additional data do not alter Fig. 5.

The script also preserves the lambda=0.05, s=0.03/0.015 convergence check:
the absolute remainder decreases approximately sixteenfold when s is
halved. The earlier independent 4×4 Liouvillian and six-state-average
verification included mixed relaxation and dephasing; it supports the
noise convention and remainder order and was not rerun for this revision.
No finite-noise optimization over all controls or new Lean theorem is
claimed for these numerical comparisons.

Primary outputs: [frontier and duration data](paper/assets/frontier_working_point.json)
and [full-channel data](paper/assets/frontier_full_channel.json).
