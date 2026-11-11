"""绘制已核精确边界与弱噪声工作点；默认输出到脚本同级 assets。"""
import argparse
import json
from pathlib import Path

import numpy as np
from scipy.optimize import brentq
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

PI = np.pi
LSTAR = 7 * PI / 3
APEAK = np.arccos((1 + np.sqrt(33)) / 8)
TEAL, ORANGE, PURPLE = "#087F8C", "#D87928", "#7357A5"
INK, GRAY, LIGHT = "#17212B", "#73808B", "#D7DDE1"


def chi(length):
    return (4 * np.cos((np.asarray(length) - PI) / 4) - 2) ** 2 / 6


def slope(angle):
    return (4 * np.cos(angle) - 2) * np.sin(angle) / 3


def working_point(ratio):
    # 驻点方程的两条单调分支逐一求根，再与两端点比较。
    candidates = [PI, LSTAR]
    if 0 < ratio < slope(APEAK):
        for low, high in ((0, APEAK), (APEAK, PI / 3)):
            angle = brentq(lambda a: slope(a) - ratio, low, high,
                           xtol=5e-15)
            candidates.append(PI + 4 * angle)
    elif ratio == slope(APEAK):
        candidates.append(PI + 4 * APEAK)
    costs = np.asarray([chi(length) + ratio * length for length in candidates])
    best = float(np.min(costs))
    optimum = float(candidates[int(np.argmin(costs))])
    endpoint = float(min(costs[:2]))
    return {
        "lambda": float(ratio), "Lopt_over_pi": optimum / PI,
        "budget_over_s2": best, "ordinary_pi_budget_over_s2": float(costs[0]),
        "short_corpse_budget_over_s2": float(costs[1]),
        "best_endpoint_budget_over_s2": endpoint,
        "relative_gain": 0.0 if endpoint == 0 else 1 - best / endpoint,
        "candidate_L_over_pi": [float(length / PI) for length in candidates],
        "minimizer_L_over_pi": [float(length / PI) for length, cost in
                                zip(candidates, costs) if abs(cost - best) < 2e-13],
    }


def build(output):
    output.mkdir(parents=True, exist_ok=True)
    angle_transition = brentq(
        lambda a: (4 * np.cos(a) - 2) ** 2
        + 8 * a * (4 * np.cos(a) - 2) * np.sin(a) - 4, 0.3, PI / 3)
    ratio_transition = float(slope(angle_transition))
    ratio_crossing = 1 / (2 * PI)
    ratios = np.unique(np.r_[np.linspace(0, 0.24, 481),
                             ratio_crossing, ratio_transition, 0.025, 0.1, 0.22])
    rows = [working_point(ratio) for ratio in ratios]
    highlight = working_point(ratio_crossing)
    lengths = np.linspace(PI, LSTAR, 601)

    # 对整个绘图区核验离散网格不优于枚举结果；检查前序材料的代表值。
    dense_lengths = np.linspace(PI, LSTAR, 20001)
    grid_gap = max(row["budget_over_s2"] -
                   np.min(chi(dense_lengths) + row["lambda"] * dense_lengths)
                   for row in rows)
    assert grid_gap < 2e-12
    assert abs(chi(PI) - 2 / 3) < 2e-15 and chi(LSTAR) < 2e-29
    assert abs(working_point(0.025)["Lopt_over_pi"] - 2.300770686560245) < 2e-12
    assert abs(highlight["relative_gain"] - 0.04910702727773064) < 2e-12
    assert working_point(0.22)["Lopt_over_pi"] == 1
    assert len(working_point(ratio_transition)["minimizer_L_over_pi"]) == 2

    plt.rcParams.update({
        "font.family": "Arial", "mathtext.fontset": "dejavusans",
        "font.size": 8.5, "axes.labelsize": 8.5, "xtick.labelsize": 8,
        "ytick.labelsize": 8, "text.color": INK, "axes.labelcolor": INK,
        "xtick.color": INK, "ytick.color": INK, "axes.edgecolor": GRAY,
        "axes.spines.top": False, "axes.spines.right": False,
        "axes.linewidth": 0.6, "pdf.fonttype": 42, "ps.fonttype": 42,
    })
    # 竖排双面板使单栏图能紧邻对应论述，保持原有数据与纵轴。
    fig, axes = plt.subplots(2, 1, figsize=(3.4, 4.85))
    fig.subplots_adjust(left=0.18, right=0.94, bottom=0.10, top=0.94, hspace=0.62)
    ax = axes[0]
    x = lengths / PI
    ax.fill_between(x, 0, chi(lengths), color="#EEF1F3", zorder=0)
    ax.plot(x, chi(lengths), color=TEAL, lw=2)
    ax.scatter([1, 7 / 3], [2 / 3, 0], color=INK, s=18, zorder=4, clip_on=False)
    ax.text(1.035, 0.685, r"Ordinary $\pi$ pulse", fontsize=8.5, va="bottom")
    # 端点标签直接就近放置，分行避开曲线，不增加类似数据线的引线。
    ax.text(7 / 3 - .015, .10, "Short-\nCORPSE", fontsize=8.5,
            ha="right", va="bottom", linespacing=1.05)
    ax.text(1.39, 0.165, "Excluded for all\ntransverse controls", fontsize=8.5,
            color="#59656F", ha="center", va="center", linespacing=1.35)
    ax.text(1.91, 0.59, r"$u_x^2+u_y^2\leq\Omega^2$", fontsize=8.5, ha="center")
    ax.set(xlim=(1, 7 / 3), ylim=(0, 0.75), xlabel=r"Duration $L/\pi=\Omega T/\pi$",
           ylabel=r"Detuning sensitivity $\chi$")
    ax.set_xticks([1, 1.5, 2, 7 / 3], ["1", "1.5", "2", r"$7/3$"])
    ax.set_yticks([0, 1 / 3, 2 / 3], ["0", r"$1/3$", r"$2/3$"])
    ax.set_title("(a)  Exact sensitivity frontier", loc="left", fontsize=9, pad=7)

    ax = axes[1]
    # 共用同一纵轴，保留连续补偿相对两端点的小幅收益。
    ax.plot(ratios, [r["ordinary_pi_budget_over_s2"] for r in rows],
            color=PURPLE, lw=1.5, ls=(0, (4, 2)), label=r"Ordinary $\pi$ pulse")
    ax.plot(ratios, [r["short_corpse_budget_over_s2"] for r in rows],
            color=ORANGE, lw=1.5, ls=(0, (1.5, 1.7)), label="Short-CORPSE")
    ax.plot(ratios, [r["budget_over_s2"] for r in rows],
            color=TEAL, lw=2, label="Minimum budget")
    ax.scatter([ratio_crossing], [highlight["budget_over_s2"]],
               s=17, color=TEAL, zorder=4)
    ax.annotate("Partial compensation\n" + r"$L_{\rm opt}=2.085\pi$" +
                "\n4.91% below endpoints",
                (ratio_crossing, highlight["budget_over_s2"]),
                xytext=(.174, .74), textcoords="data", fontsize=8,
                linespacing=1.35, ha="center", va="top",
                arrowprops={"arrowstyle": "-", "color": GRAY, "lw": 0.75})
    ax.set(xlim=(0, 0.24), ylim=(0, 1.8), xlabel=r"Noise ratio $\lambda=\kappa/s^2$",
           ylabel=r"Leading error budget / $s^2$")
    ax.set_xticks([0, .08, .16, .24], ["0", "0.08", "0.16", "0.24"])
    ax.set_yticks([0, .5, 1, 1.5], ["0", "0.5", "1.0", "1.5"])
    ax.set_title("(b)  Weak-noise working point", loc="left", fontsize=9, pad=7)
    ax.legend(frameon=False, fontsize=8, loc="upper left", handlelength=2.2,
              borderaxespad=0.2, labelspacing=0.35)
    for ax in axes:
        ax.tick_params(length=2.5, width=0.6)
        ax.set_axisbelow(True)
        ax.grid(axis="y", color=LIGHT, lw=0.5, alpha=0.55)
    fig.savefig(output / "frontier_working_point.pdf")
    fig.savefig(output / "frontier_working_point.png", dpi=300)
    plt.close(fig)

    report = {
        "model": "chi_min(L)+lambda*L; weak-noise leading budget, not finite-noise optimization",
        "definitions": {"L": "Omega*T", "s2": "Var(delta)/Omega**2",
                        "kappa": "(Gamma1+Gamma_phi)/(3*Omega)", "lambda": "kappa/s2"},
        "assumptions": "Full nominal pi gate; ux**2+uy**2<=Omega**2; zero-mean quasistatic detuning; drive-independent weak Markovian relaxation and pure dephasing",
        "transition": {"lambda": ratio_transition,
                       "Lopt_over_pi": (PI + 4 * angle_transition) / PI},
        "highlight": highlight,
        "verification": {"maximum_dense_grid_shortfall": float(grid_gap),
                         "stationary_candidates": "Both monotone branches and both endpoints"},
        "frontier": [{"L_over_pi": float(length / PI), "chi_min": float(chi(length))}
                     for length in lengths],
        "working_points": rows,
    }
    (output / "frontier_working_point.json").write_text(
        json.dumps(report, indent=2), encoding="utf-8")
    print(json.dumps({key: report[key] for key in ("transition", "highlight", "verification")},
                     indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parent / "assets")
    build(parser.parse_args().output_dir)
