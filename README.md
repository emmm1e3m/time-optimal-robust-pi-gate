# Exact time limit for first-order detuning-robust qubit π gates

**Tingyu Zhang and Yan Cen**  
Department of Physics, Fudan University, Shanghai, China

For arbitrary measurable transverse controls satisfying
$u_x^2+u_y^2\le\Omega^2$, the exact minimum duration of a full qubit π gate
that cancels static detuning to first order is

$$T_{\min}=\frac{7\pi}{3\Omega}.$$

Every minimizing control is, almost everywhere, the known short-CORPSE
sequence or its overall negative: three segments along one axis with
durations $(\pi/3,5\pi/3,\pi/3)/\Omega$. A second independent transverse
control axis gives no time advantage for this task. The proof uses a sharp
midpoint comparison for zero-mean spherical curves with antipodal endpoints.

## Papers

- [English manuscript (PDF)](paper/manuscript.pdf) · [LaTeX](paper/manuscript.tex)
- [中文论文（PDF）](paper/manuscript_zh.pdf) · [LaTeX](paper/manuscript_zh.tex)
- [Shared bibliography](paper/references.bib)
- [Author review notes / 作者校阅说明](AUTHOR_REVIEW.md)

The two versions contain the same scientific results and use the PRA
REVTeX 4.2 format. These are author-review manuscripts; acknowledgments,
data/code availability and required declarations contain visible placeholders.
No journal submission or acceptance is claimed.

## Reproduce the manuscripts

Use a TeX distribution with REVTeX 4.2, BibTeX and ctex. From `paper/`:

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
files. Both languages share the same scientific figure and English caption.

## Lean 4 formalization

[Proof overview and build instructions](lean/README.md)

The 23 source modules formalize the original AC/a.e. Schrödinger model,
the actual detuning-parameter derivative, the sharp time bound, explicit
attaining evolutions and all minimizing controls for every Ω>0. The geometric
bound and sharpness in each dimension d≥2 are also included.

```sh
cd lean
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean 4.35.0 and mathlib v4.35.0 are pinned. The source contains no `sorry`,
`admit`, custom axioms or `native_decide`. The principal theorems depend only
on `propext`, `Classical.choice` and `Quot.sound`.

## Numerical checks and figure

```sh
python -m pip install -r requirements.txt
python numerics/verify_solution.py
python paper/build_figure.py
```

The numerical script uses direct 2×2 matrix exponentials and Fréchet
derivatives. Its recorded output is in [verification.json](numerics/verification.json).
Floating-point calculations check conventions and implementation; the
global optimality result follows from the analytical and formal proofs.
The figure script reconstructs the vector PDF/SVG and PNG from analytic arcs.

本仓库包含中英双语论文、共享参考文献与科学图、Lean 4 证明及必要复现脚本。
论文主线为“原量子控制模型—球面中点锐界—精确时间—全部最优控制”。
作者待核定的非实质声明集中列在校阅说明中。
