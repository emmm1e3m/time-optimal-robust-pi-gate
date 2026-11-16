"""复现精确前沿、最优时长及高斯失谐下的完整信道；默认输出到同级 assets。"""
import argparse
import json
from pathlib import Path

import numpy as np
from numpy.polynomial.hermite import hermgauss
from scipy.linalg import expm
from scipy.optimize import brentq, minimize_scalar
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D

PI = np.pi
LSTAR = 7 * PI / 3
APEAK = np.arccos((1 + np.sqrt(33)) / 8)
TEAL, ORANGE, PURPLE = "#087F8C", "#D87928", "#7357A5"
INK, GRAY, LIGHT = "#17212B", "#73808B", "#D7DDE1"
X = np.array([[0., 0., 0.], [0., 0., -1.], [0., 1., 0.]])
Z = np.array([[0., -1., 0.], [1., 0., 0.], [0., 0., 0.]])
TARGET = np.diag([1., -1., -1.])
QUADRATURE = {order: hermgauss(order) for order in (32, 48)}


def chi(length):
    return (4 * np.cos((np.asarray(length) - PI) / 4) - 2) ** 2 / 6


def slope(angle):
    return (4 * np.cos(angle) - 2) * np.sin(angle) / 3


def leading(length, ratio):
    return chi(length) + ratio * length


def transition():
    angle = brentq(lambda a: (4 * np.cos(a) - 2) ** 2
                   + 8 * a * (4 * np.cos(a) - 2) * np.sin(a) - 4,
                   APEAK, PI / 3, xtol=5e-15)
    return {"a": float(angle), "lambda": float(slope(angle)),
            "L": float(PI + 4 * angle), "L_over_pi": float((PI + 4 * angle) / PI)}


def working_point(ratio):
    # 驻点方程有两条分支；与两端点一并比较以选择全局前导预算。
    candidates = [PI, LSTAR]
    if 0 < ratio < slope(APEAK):
        for low, high in ((0, APEAK), (APEAK, PI / 3)):
            angle = brentq(lambda a: slope(a) - ratio, low, high, xtol=5e-15)
            candidates.append(PI + 4 * angle)
    elif ratio == slope(APEAK):
        candidates.append(PI + 4 * APEAK)
    costs = np.asarray([leading(length, ratio) for length in candidates])
    best = float(np.min(costs))
    endpoint = float(min(costs[:2]))
    minimizers = sorted(float(length) for length, cost in zip(candidates, costs)
                        if abs(cost - best) < 2e-13)
    return {
        "lambda": float(ratio), "Lopt_over_pi": float(candidates[int(np.argmin(costs))] / PI),
        "budget_over_s2": best, "ordinary_pi_budget_over_s2": float(costs[0]),
        "short_corpse_budget_over_s2": float(costs[1]),
        "best_endpoint_budget_over_s2": endpoint,
        "relative_gain": 0.0 if endpoint == 0 else 1 - best / endpoint,
        "candidate_L_over_pi": [float(length / PI) for length in candidates],
        "minimizer_L_over_pi": [length / PI for length in minimizers],
    }


def full_channel(length, ratio, sigma, order=32):
    # Ω=1，Γ1=0；Γφ/2 D[σz] 对应横向 Bloch 衰减率 Γφ。
    angle = (length - PI) / 4
    gamma_phi = 3 * ratio * sigma ** 2
    damping = np.diag([-gamma_phi, -gamma_phi, 0.])
    nodes, weights = QUADRATURE[order]
    infidelity = 0.
    for node, weight in zip(nodes, weights):
        detuning = np.sqrt(2) * sigma * node
        outer = expm((X + detuning * Z + damping) * angle)
        middle = expm((-X + detuning * Z + damping) * (PI + 2 * angle))
        channel = outer @ middle @ outer
        infidelity += weight * (3 - np.trace(TARGET.T @ channel)) / (6 * np.sqrt(PI))
    return float(infidelity)


def channel_point(length, ratio, sigma):
    value32 = full_channel(length, ratio, sigma, 32)
    value48 = full_channel(length, ratio, sigma, 48)
    budget = float(sigma ** 2 * leading(length, ratio))
    return {"L": float(length), "L_over_pi": float(length / PI),
            "leading_infidelity": budget, "full_infidelity": value32,
            "full_minus_leading": value32 - budget,
            "relative_difference_to_leading": (value32 - budget) / budget,
            "quadrature_32_48_absolute": abs(value32 - value48)}


def compute_prescription_check():
    # 只在最大前导收益对应的噪声比复算；全时长网格定位极小值后逐一细化。
    ratio, sigma = 1 / (2 * PI), .03
    choice = working_point(ratio)
    selected = channel_point(choice["Lopt_over_pi"] * PI, ratio, sigma)
    scan = [channel_point(length, ratio, sigma)
            for length in np.linspace(PI, LSTAR, 129)]
    candidates = [dict(name="ordinary_pi", **scan[0]),
                  dict(name="short_corpse", **scan[-1])]
    for index in range(1, len(scan) - 1):
        if (scan[index]["full_infidelity"] < scan[index - 1]["full_infidelity"]
                and scan[index]["full_infidelity"] < scan[index + 1]["full_infidelity"]):
            result = minimize_scalar(
                lambda length: full_channel(length, ratio, sigma, 48),
                bounds=(scan[index - 1]["L"], scan[index + 1]["L"]),
                method="bounded", options={"xatol": 5e-11})
            assert result.success
            candidates.append(dict(name="refined_interior_minimum",
                                   **channel_point(result.x, ratio, sigma)))
    best = min(candidates, key=lambda point: point["full_infidelity"])
    assert best["full_infidelity"] <= min(point["full_infidelity"] for point in scan) + 1e-14
    endpoint = min(scan[0]["full_infidelity"], scan[-1]["full_infidelity"])
    quadrature_gap = max(point["quadrature_32_48_absolute"]
                         for point in scan + candidates + [selected])
    assert quadrature_gap < 1e-12
    return {
        "lambda": float(ratio), "sigma": sigma,
        "Gamma1_over_Omega": 0., "Gamma_phi_over_Omega": 3 * ratio * sigma ** 2,
        "search": "129 points on [pi,7*pi/3]; bounded refinement of each sampled interior minimum; compare both endpoints",
        "scope": "numerical duration optimization within the same-axis three-segment family",
        "scan": scan, "candidates": candidates, "leading_budget_choice": selected,
        "numerical_family_minimum": best,
        "leading_relative_gain": choice["relative_gain"],
        "full_relative_gain_over_better_endpoint": 1 - selected["full_infidelity"] / endpoint,
        "choice_minus_numerical_minimum": selected["full_infidelity"] - best["full_infidelity"],
        "maximum_32_48_quadrature_difference": quadrature_gap,
    }


def compute_frontier():
    critical = transition()
    ratios = np.unique(np.r_[np.linspace(0, .24, 481), 1 / (2 * PI),
                            critical["lambda"], .025, .1, .22])
    rows = [working_point(ratio) for ratio in ratios]
    highlight = working_point(1 / (2 * PI))
    lengths = np.linspace(PI, LSTAR, 601)
    dense = np.linspace(PI, LSTAR, 20001)
    grid_gap = max(row["budget_over_s2"] - np.min(leading(dense, row["lambda"]))
                   for row in rows)
    assert grid_gap < 2e-12
    assert abs(chi(PI) - 2 / 3) < 2e-15 and chi(LSTAR) < 2e-29
    assert abs(working_point(.025)["Lopt_over_pi"] - 2.300770686560245) < 2e-12
    assert abs(highlight["relative_gain"] - .04910702727773064) < 2e-12
    assert working_point(.22)["Lopt_over_pi"] == 1
    assert len(working_point(critical["lambda"])["minimizer_L_over_pi"]) == 2
    return {
        "model": "chi_min(L)+lambda*L; weak-noise leading budget",
        "definitions": {"L": "Omega*T", "s2": "Var(delta)/Omega**2",
                        "kappa": "(Gamma1+Gamma_phi)/(3*Omega)", "lambda": "kappa/s2"},
        "transition": critical, "highlight": highlight,
        "verification": {"maximum_dense_grid_shortfall": float(grid_gap)},
        "frontier": [{"L_over_pi": float(length / PI), "chi_min": float(chi(length))}
                     for length in lengths], "working_points": rows,
    }


def compute_channel(critical, reference=None):
    sigma = .03
    lengths = np.linspace(PI, LSTAR, 81)
    rows = []
    for ratio in (.025, critical["lambda"], .22):
        optimum = working_point(ratio)
        markers = [dict(name="ordinary_pi", **channel_point(PI, ratio, sigma)),
                   dict(name="short_corpse", **channel_point(LSTAR, ratio, sigma))]
        for length_pi in optimum["minimizer_L_over_pi"]:
            if abs(length_pi - 1) > 1e-13 and abs(length_pi - 7 / 3) > 1e-13:
                markers.append(dict(name="analytic_optimum", **channel_point(length_pi * PI, ratio, sigma)))
        rows.append({"lambda": float(ratio), "sigma": sigma,
                     "Gamma1_over_Omega": 0., "Gamma_phi_over_Omega": 3 * ratio * sigma ** 2,
                     "analytic_minimizer_L_over_pi": optimum["minimizer_L_over_pi"],
                     "values": [channel_point(length, ratio, sigma) for length in lengths],
                     "markers": markers})
    checks = []
    for length in (PI, 1.5 * PI, 2 * PI, LSTAR):
        pair = [channel_point(length, .05, width) for width in (.03, .015)]
        scaled = [point["full_minus_leading"] / width ** 2
                  for point, width in zip(pair, (.03, .015))]
        checks.append({"L_over_pi": float(length / PI), "lambda": .05,
                       "sigma_003": pair[0], "sigma_0015": pair[1],
                       "scaled_remainder_ratio": scaled[0] / scaled[1],
                       "absolute_remainder_ratio": pair[0]["full_minus_leading"] / pair[1]["full_minus_leading"]})
    points = [point for row in rows for point in row["values"] + row["markers"]]
    points += [check[key] for check in checks for key in ("sigma_003", "sigma_0015")]
    max_quadrature_gap = max(point["quadrature_32_48_absolute"] for point in points)
    assert max_quadrature_gap < 1e-12
    assert all(3.8 < check["scaled_remainder_ratio"] < 4.2 for check in checks)
    critical_markers = rows[1]["markers"]
    ordinary = next(point for point in critical_markers if point["name"] == "ordinary_pi")
    partial = next(point for point in critical_markers if point["name"] == "analytic_optimum")
    assert abs(partial["leading_infidelity"] - ordinary["leading_infidelity"]) < 1e-15
    verification = {"maximum_32_48_quadrature_difference": max_quadrature_gap,
                    "maximum_scan_absolute_leading_discrepancy": max(abs(point["full_minus_leading"]) for row in rows for point in row["values"]),
                    "critical_full_partial_minus_ordinary": partial["full_infidelity"] - ordinary["full_infidelity"],
                    "critical_leading_partial_minus_ordinary": partial["leading_infidelity"] - ordinary["leading_infidelity"]}
    if reference is not None:
        previous = json.loads(reference.read_text(encoding="utf-8"))
        differences = []
        for new, old in zip(rows, previous["rows"]):
            assert abs(new["lambda"] - old["lambda"]) < 1e-12
            for new_point, old_point in zip(new["values"], old["values"]):
                assert abs(new_point["L"] - old_point["L"]) < 1e-13
                differences.append(abs(new_point["full_infidelity"] - sigma ** 2 * old_point["exact_sigma_003_scaled"]))
        verification["maximum_previous_scan_difference"] = max(differences)
        assert max(differences) < 1e-12
    prescription = compute_prescription_check()
    verification["maximum_32_48_quadrature_difference"] = max(
        max_quadrature_gap, prescription["maximum_32_48_quadrature_difference"])
    return {"model": "Gaussian quasistatic detuning and drive-independent Markov pure dephasing",
            "definitions": {"L": "Omega*T", "s": "std(delta)/Omega", "lambda": "Gamma_phi/(3*Omega*s**2)",
                            "full_infidelity": "Gaussian average of (3-Tr(Rtarget.T @ M))/6",
                            "pulse": "+x,-x,+x; durations (a,pi+2a,a)/Omega, a=(L-pi)/4"},
            "quadrature": "32-point Gauss-Hermite, compared with 48 points at every stored point",
            "transition": critical, "rows": rows, "convergence_checks": checks,
            "verification": verification,
            "prescription_check": prescription}


def style():
    plt.rcParams.update({
        "font.family": "Arial", "mathtext.fontset": "dejavusans", "font.size": 10,
        "axes.labelsize": 10, "xtick.labelsize": 9.5, "ytick.labelsize": 9.5,
        "text.color": INK, "axes.labelcolor": INK, "xtick.color": INK,
        "ytick.color": INK, "axes.edgecolor": GRAY, "axes.spines.top": False,
        "axes.spines.right": False, "axes.linewidth": .65, "pdf.fonttype": 42,
        "ps.fonttype": 42,
    })


def finish(fig, axes, output, name):
    for ax in axes:
        ax.tick_params(length=3, width=.65)
        ax.set_axisbelow(True)
        ax.grid(axis="y", color=LIGHT, lw=.55, alpha=.6)
    fig.savefig(output / f"{name}.pdf")
    fig.savefig(output / f"{name}.png", dpi=300)
    plt.close(fig)


def plot_frontier(report, output):
    critical = report["transition"]
    ratios = np.array([row["lambda"] for row in report["working_points"]])
    rows = report["working_points"]
    highlight = report["highlight"]
    lengths = np.array([point["L_over_pi"] for point in report["frontier"]]) * PI
    fig, axes = plt.subplots(1, 3, figsize=(7.2, 3.15))
    fig.subplots_adjust(left=.075, right=.972, bottom=.20, top=.88, wspace=.48)
    ax = axes[0]
    ax.fill_between(lengths / PI, 0, chi(lengths), color="#EEF1F3", zorder=0)
    ax.plot(lengths / PI, chi(lengths), color=TEAL, lw=1.8)
    ax.scatter([1, 7 / 3], [2 / 3, 0], color=INK, s=23, zorder=4, clip_on=False)
    ax.text(1.035, .685, r"Ordinary $\pi$ pulse", fontsize=9.2, va="bottom")
    ax.text(7 / 3 - .02, .24, "Short-\nCORPSE", fontsize=9.2, ha="right", va="bottom", linespacing=1.05)
    ax.text(1.035, .175, "Excluded for all\ntransverse controls", fontsize=8.6,
            color="#59656F", ha="left", va="center", linespacing=1.25)
    ax.text(1.95, .59, r"$u_x^2+u_y^2\leq\Omega^2$", fontsize=9.5, ha="center")
    ax.set(xlim=(1, 7 / 3), ylim=(0, .75), xlabel=r"Duration $L/\pi$", ylabel=r"Detuning sensitivity $\chi$")
    ax.set_xticks([1, 1.5, 2, 7 / 3], ["1", "1.5", "2", r"$7/3$"])
    ax.set_yticks([0, 1 / 3, 2 / 3], ["0", r"$1/3$", r"$2/3$"])
    ax.set_title("(a) Sensitivity frontier", loc="left", fontsize=10.5, pad=8)

    ax = axes[1]
    ax.plot(ratios, [row["ordinary_pi_budget_over_s2"] for row in rows],
            color=PURPLE, lw=1.4, ls=(0, (4, 2)), label=r"Ordinary $\pi$ pulse")
    ax.plot(ratios, [row["short_corpse_budget_over_s2"] for row in rows],
            color=ORANGE, lw=1.4, ls=(0, (1.5, 1.7)), label="Short-CORPSE")
    ax.plot(ratios, [row["budget_over_s2"] for row in rows], color=TEAL, lw=1.8, label="Minimum budget")
    ax.scatter([highlight["lambda"]], [highlight["budget_over_s2"]], s=23, color=TEAL, zorder=4)
    ax.annotate("Partial compensation\n" + r"$L_{\rm opt}=2.08\pi$" + "\n4.91% below endpoints",
                (highlight["lambda"], highlight["budget_over_s2"]), xytext=(.153, .36),
                fontsize=8.8, linespacing=1.25, ha="center", va="top",
                arrowprops={"arrowstyle": "-", "color": GRAY, "lw": .7})
    ax.set(xlim=(0, .24), ylim=(0, 1.8), xlabel=r"Noise ratio $\lambda$", ylabel=r"Leading error budget / $s^2$")
    ax.set_xticks([0, .08, .16, .24], ["0", "0.08", "0.16", "0.24"])
    ax.set_yticks([0, .5, 1, 1.5], ["0", "0.5", "1.0", "1.5"])
    ax.set_title("(b) Leading error budget", loc="left", fontsize=10.5, pad=8)
    ax.legend(frameon=False, fontsize=8.8, loc="upper left", handlelength=2,
              borderaxespad=.15, labelspacing=.3)

    ax = axes[2]
    ax.axvline(critical["lambda"], color=GRAY, lw=.8, ls=(0, (3, 3)), zorder=0)
    ax.axhline(critical["L_over_pi"], color=GRAY, lw=.8, ls=(0, (3, 3)), zorder=0)
    below = np.r_[ratios[ratios < critical["lambda"]], critical["lambda"]]
    upper = [max(working_point(ratio)["minimizer_L_over_pi"]) for ratio in below]
    ax.plot(below, upper, color=TEAL, lw=1.8)
    ax.plot([critical["lambda"], .24], [1, 1], color=TEAL, lw=1.8)
    ax.scatter([critical["lambda"], critical["lambda"]], [1, critical["L_over_pi"]],
               color=TEAL, edgecolors=INK, linewidths=.5, s=28, zorder=4)
    ax.text(.085, 1.89, r"$L_c/\pi\simeq2.047$", fontsize=9.5, ha="center", va="top")
    ax.text(.085, 1.51, r"$\lambda_c\simeq0.176$", fontsize=9.5, ha="center")
    ax.text(.085, 1.32, r"Two minima at $\lambda_c$", fontsize=9, ha="center")
    ax.set(xlim=(0, .24), ylim=(.88, 2.45), xlabel=r"Noise ratio $\lambda$", ylabel=r"Optimal duration $L_{\rm opt}/\pi$")
    ax.set_xticks([0, .08, .16, .24], ["0", "0.08", "0.16", "0.24"])
    ax.set_yticks([1, 1.5, 2, 7 / 3], ["1", "1.5", "2", r"$7/3$"])
    ax.set_title("(c) Optimal duration", loc="left", fontsize=10.5, pad=8)
    finish(fig, axes, output, "frontier_working_point")


def plot_channel(report, output):
    fig, axes = plt.subplots(1, 3, figsize=(7.2, 3.25))
    fig.subplots_adjust(left=.085, right=.972, bottom=.20, top=.80, wspace=.40)
    for index, (ax, row) in enumerate(zip(axes, report["rows"])):
        points = row["values"]
        length = [point["L_over_pi"] for point in points]
        full = [1000 * point["full_infidelity"] for point in points]
        budget = [1000 * point["leading_infidelity"] for point in points]
        ax.plot(length, full, color=TEAL, lw=1.7, zorder=2)
        ax.plot(length, budget, color=ORANGE, lw=1.3, ls=(0, (4, 2.5)), zorder=3)
        ax.plot(length[::8], full[::8], linestyle="none", marker="o", ms=3.5,
                mfc="white", mec=TEAL, mew=.9, zorder=4)
        for point in row["markers"]:
            is_optimum = any(abs(point["L_over_pi"] - optimum) < 1e-12
                             for optimum in row["analytic_minimizer_L_over_pi"])
            ax.plot(point["L_over_pi"], point["full_infidelity"] * 1000,
                    marker="D" if is_optimum else "s", ms=5.5 if is_optimum else 4.3,
                    color=INK, mfc=INK if is_optimum else "white", mew=.9,
                    linestyle="none", clip_on=False, zorder=6)
        if index == 0:
            ax.text(1.035, .72, r"Ordinary $\pi$", fontsize=9, va="top")
            ax.text(2.31, .35, "Short-\nCORPSE", fontsize=9, ha="right", linespacing=1.05)
            ax.text(1.66, .09, r"$L_{\rm opt}=2.30\pi$", fontsize=9.3)
            ax.set_ylim(.055, .80)
            ax.set_yticks([.1, .3, .5, .7])
        elif index == 1:
            ax.text(1.035, 1.085, r"Ordinary $\pi$", fontsize=9, va="top")
            ax.text(2.31, 1.20, "Short-\nCORPSE", fontsize=9, ha="right", va="bottom", linespacing=1.05)
            ax.text(2.22, 1.075, r"$L_c\simeq2.047\pi$", fontsize=9.3, ha="right", va="top")
            ax.text(1.66, 1.285, r"Ordinary $\pi$:" + "\n" + r"$0.234\%$ below partial",
                    fontsize=9, ha="center", va="center", linespacing=1.3)
            ax.set_ylim(1.035, 1.34)
            ax.set_yticks([1.05, 1.15, 1.25])
        else:
            ax.text(1.22, 1.265, r"Ordinary $\pi$" + "\n" + r"$L_{\rm opt}=\pi$", fontsize=9, va="top", linespacing=1.3)
            ax.text(2.31, 1.49, "Short-CORPSE", fontsize=9, ha="right")
            ax.set_ylim(1.20, 1.54)
            ax.set_yticks([1.2, 1.3, 1.4, 1.5])
        ax.set(xlim=(1, 7 / 3), xlabel=r"Duration $L/\pi$")
        ax.set_xticks([1, 1.5, 2, 7 / 3], ["1", "1.5", "2", r"$7/3$"])
        label = [r"$\lambda=0.025$", r"$\lambda=\lambda_c\simeq0.176$", r"$\lambda=0.22$"][index]
        ax.set_title(f"({chr(97 + index)}) " + label, loc="left", fontsize=10.5, pad=8)
    axes[0].set_ylabel(r"Average gate infidelity ($10^{-3}$)")
    handles = [Line2D([], [], color=TEAL, lw=1.7, marker="o", ms=3.5, mfc="white", label="Full channel"),
               Line2D([], [], color=ORANGE, lw=1.3, ls=(0, (4, 2.5)), label="Leading budget"),
               Line2D([], [], color=INK, marker="D", ms=5, ls="none", label="Leading-budget choice")]
    fig.legend(handles=handles, loc="upper center", bbox_to_anchor=(.54, .99),
               frameon=False, ncol=3, fontsize=9.5, handlelength=2, columnspacing=1.2)
    finish(fig, axes, output, "frontier_full_channel")


def build(output, reference=None):
    output.mkdir(parents=True, exist_ok=True)
    frontier = compute_frontier()
    channel = compute_channel(frontier["transition"], reference)
    style()
    plot_frontier(frontier, output)
    plot_channel(channel, output)
    for name, report in (("frontier_working_point", frontier), ("frontier_full_channel", channel)):
        (output / f"{name}.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"transition": frontier["transition"], "verification": channel["verification"],
                      "markers": [{"lambda": row["lambda"], "points": row["markers"]} for row in channel["rows"]],
                      "convergence": [{"L_over_pi": check["L_over_pi"],
                                       "scaled_remainder_ratio": check["scaled_remainder_ratio"]}
                                      for check in channel["convergence_checks"]]}, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parent / "assets")
    parser.add_argument("--reference-data", type=Path, help="可选：核对原 frontier_noise.json 的81点扫描")
    args = parser.parse_args()
    build(args.output_dir, args.reference_data)
