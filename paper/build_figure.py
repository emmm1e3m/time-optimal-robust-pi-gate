"""绘制方向曲线、半段上包络及 short-CORPSE；默认输出到同级 assets。"""
import argparse
from pathlib import Path

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch
from matplotlib.path import Path as MplPath
from matplotlib.transforms import Affine2D

PI = np.pi
TEAL, ORANGE, PURPLE = "#087F8C", "#D87928", "#7357A5"
INK, GRAY, LIGHT = "#17212B", "#73808B", "#D7DDE1"
COLORS = (TEAL, ORANGE, PURPLE)
TRAJECTORY_LW = 1.6
POINT_SIZE = 7.5


def style():
    plt.rcParams.update({
        "font.family": "Arial", "mathtext.fontset": "dejavusans",
        "font.size": 8.5, "axes.labelsize": 8.5, "xtick.labelsize": 8,
        "ytick.labelsize": 8, "text.color": INK, "axes.labelcolor": INK,
        "xtick.color": INK, "ytick.color": INK, "axes.edgecolor": GRAY,
        "axes.spines.top": False, "axes.spines.right": False,
        "axes.linewidth": 0.6, "pdf.fonttype": 42, "ps.fonttype": 42,
    })


def arrow(ax, start, end, color=INK, lw=.85, size=6, zorder=8):
    ax.add_patch(FancyArrowPatch(start, end, arrowstyle="-|>",
                                mutation_scale=size, lw=lw, color=color,
                                shrinkA=0, shrinkB=0, zorder=zorder))


def family(angle):
    # 每段的积分由原函数给出，避免累积数值积分误差。
    durations = (angle, 2 * angle + PI, angle)
    phases = (0.0, angle, -angle - PI)
    values, offset = [], np.zeros(2)
    for duration, phase0, sign in zip(durations, phases, (1, -1, 1)):
        tau = np.linspace(0.0, duration, 601)
        phase = phase0 + sign * tau
        direction = np.column_stack((np.sin(phase), np.cos(phase)))
        path = offset + np.column_stack((
            (np.cos(phase0) - np.cos(phase)) / sign,
            (np.sin(phase) - np.sin(phase0)) / sign))
        values.append((tau, phase, direction, path))
        offset = path[-1]
    return values


def direction_arrow(ax, points, fraction, color, size=20):
    # 只画小箭头头部，避免额外的短箭杆在圆弧上形成粗结点。
    i = int((len(points) - 1) * fraction)
    tangent = points[min(i + 2, len(points) - 1)] - points[max(i - 2, 0)]
    angle = np.arctan2(tangent[1], tangent[0])
    head = MplPath([[-.6, -.42], [.6, 0], [-.6, .42], [-.6, -.42]])
    marker = head.transformed(Affine2D().rotate(angle))
    ax.scatter(*points[i], s=size, marker=marker, color=color,
               linewidths=0, zorder=8)


def save(fig, output, name):
    fig.savefig(output / (name + ".pdf"))
    fig.savefig(output / (name + ".svg"))
    fig.savefig(output / (name + ".png"), dpi=350)
    plt.close(fig)


def residual_geometry(output):
    segments = family(PI / 4)
    residual = segments[-1][3][-1]
    assert np.allclose(residual, [-(2 * np.sqrt(2) - 2), 0], atol=2e-15)
    fig = plt.figure(figsize=(3.4, 4.8))
    fig.text(.06, .965, "(a)  Unit direction curve", fontsize=9)
    fig.text(.06, .927, r"Attaining example: $a=\pi/4,\ L=2\pi$", fontsize=8.5)
    # 两面板共用每单位长度 0.56 in 的显示尺度，保持圆弧的视觉大小一致。
    ax = fig.add_axes([.10, .555, .80, .350])
    direction_ax = ax
    ax.set_aspect("equal")
    ax.set_xlim(-1.65, 1.65)
    ax.set_ylim(-1.40, 1.60)
    ax.axis("off")
    angle = np.linspace(0, 2 * PI, 400)
    ax.plot(np.sin(angle), np.cos(angle), color=LIGHT, lw=.6)
    # 坐标轴通过真实原点；轴名、端点名和角标分别留在互不重叠的区域。
    arrow(ax, (-1.25, 0), (1.30, 0), GRAY, .6, 5, zorder=0)
    arrow(ax, (0, -1.25), (0, 1.35), GRAY, .6, 5, zorder=0)
    ax.text(1.42, 0, r"$n_y$", ha="left", va="center", fontsize=8.5)
    ax.text(.13, 1.39, r"$n_z$", ha="left", va="center", fontsize=8.5)
    # 重合弧保持同一几何位置和线宽；青/紫虚线间隙露出橙色反向段。
    ax.plot(segments[1][2][:, 0], segments[1][2][:, 1],
            color=ORANGE, lw=TRAJECTORY_LW, solid_capstyle="round")
    for j in (0, 2):
        ax.plot(segments[j][2][:, 0], segments[j][2][:, 1],
                color=COLORS[j], lw=TRAJECTORY_LW, dash_capstyle="butt", ls=(0, (2.4, 1.8)))
    direction_arrow(ax, segments[0][2], .55, TEAL)
    direction_arrow(ax, segments[1][2], .39, ORANGE)
    direction_arrow(ax, segments[2][2], .45, PURPLE)
    for point in ((0, 1), (0, -1), (-1, 0)):
        ax.scatter(*point, color=INK, s=POINT_SIZE, linewidths=0, zorder=10)
    ax.text(-.15, 1.12, r"$\mathbf{n}(0)$", ha="right", va="center")
    ax.text(-.15, -1.14, r"$\mathbf{n}(L)$", ha="right", va="center")
    ax.text(-1.12, -.16, r"$\mathbf{v}$", ha="right", va="center")
    ax.text(.07, -.15, "0", color=GRAY, fontsize=8)
    # 角标位于圆内部，表示端点与中点方向之间的测地距离。
    for start, end in ((-PI / 2, 0), (-PI, -PI / 2)):
        theta = np.linspace(start, end, 80)
        ax.plot(.43 * np.sin(theta), .43 * np.cos(theta), color=GRAY, lw=.6)
    ax.text(-.43, .50, r"$\alpha$", ha="center", va="center")
    ax.text(-.52, -.50, r"$\pi-\alpha$", ha="center", va="center")
    ax.text(.88, .70, "1", color=TEAL, fontsize=8.5)
    ax.text(-1.06, .61, "2", color=ORANGE, fontsize=8.5)
    ax.text(.88, -.76, "3", color=PURPLE, fontsize=8.5)
    ax = fig.add_axes([.10, .064, .80, .420])
    error_ax = ax
    fig.text(.06, .515, "(b)  Integrated error curve", fontsize=9)
    ax.set_aspect("equal")
    ax.set_xlim(-2.06, 1.06)
    ax.set_ylim(-.76, 2.84)
    ax.axis("off")
    # 简化坐标轴保留尺度；路径端点及积分关系在图内直接标出。
    arrow(ax, (-1.83, -.63), (.70, -.63), GRAY, .6, 5)
    arrow(ax, (-1.83, -.63), (-1.83, 2.70), GRAY, .6, 5)
    ax.text(.79, -.63, r"$\Omega r_y$", ha="left", va="center", fontsize=8.5)
    ax.text(-1.83, 2.84, r"$\Omega r_z$", ha="center", fontsize=8.5)
    for j, (_, _, _, path) in enumerate(segments):
        ax.plot(path[:, 0], path[:, 1], color=COLORS[j], lw=TRAJECTORY_LW, solid_capstyle="round")
        direction_arrow(ax, path, .57 if j != 1 else .27, COLORS[j])
    for point in (segments[0][3][0], segments[0][3][-1],
                  segments[1][3][-1], residual):
        ax.scatter(*point, s=POINT_SIZE, color=INK, linewidths=0, zorder=8)
    midpoint = np.array([-(2 * np.sqrt(2) - 2) / 2, 1 + np.sqrt(2)])
    ax.scatter(*midpoint, s=POINT_SIZE, color=INK, linewidths=0, zorder=8)
    arrow(ax, midpoint, midpoint + [-.58, 0], INK, .8, 6)
    ax.text(midpoint[0], midpoint[1] + .26, r"$\mathbf{n}(L/2)=\mathbf{v}$",
            fontsize=8.5, va="center", ha="center")
    arrow(ax, (0, 0), residual, INK, .9, 6)
    ax.text(residual[0] / 2, -.25, r"$\mathbf{R}$", ha="center", va="center")
    ax.text(.14, -.02, r"$\mathbf{r}(0)=0$", fontsize=8.5, va="center")
    ax.text(residual[0] - .15, -.02, r"$\Omega\mathbf{r}(T)$", fontsize=8.5,
            ha="right", va="center")
    ax.text(.43, .65, "1", color=TEAL)
    ax.text(.76, 1.57, "2", color=ORANGE)
    ax.text(-1.40, .65, "3", color=PURPLE)
    fig.text(.5, .023, r"$\mathrm{d}(\Omega\mathbf{r})/\mathrm{d}\tau=\mathbf{n}(\tau)$",
             ha="center", fontsize=8.5)
    # 渲染后核验两面板的横、纵尺度一致，不通过拉伸曲线实现尺寸匹配。
    fig.canvas.draw()
    scales = []
    for axis in (direction_ax, error_ax):
        transformed = axis.transData.transform([(0, 0), (1, 0), (0, 1)])
        scales.extend(np.linalg.norm(transformed[1:] - transformed[0], axis=1))
    assert np.allclose(scales, .56 * fig.dpi, rtol=0, atol=1e-10)
    save(fig, output, "residual_geometry")


def midpoint_envelope(output):
    c = 7 * PI / 6
    t = np.linspace(0, c, 1001)
    fig, axes = plt.subplots(2, 1, figsize=(3.4, 4.4))
    fig.subplots_adjust(left=.17, right=.96, bottom=.18, top=.89, hspace=.64)
    fig.text(.5, .97, r"$c=7\pi/6,\quad \beta\in\{\alpha,\pi-\alpha\}$",
             ha="center", va="top", fontsize=8.7)
    for ax, beta, title in zip(axes, (PI / 2, 11 * PI / 12),
                               ("(a)  Uncapped envelope", "(b)  Capped envelope")):
        envelope = np.minimum.reduce((beta + t, c - t, np.full_like(t, PI)))
        ax.plot(t / PI, (beta + t) / PI, color=TEAL, lw=1.05,
                ls=(0, (4, 2)), label=r"$\beta+t$")
        ax.plot(t / PI, (c - t) / PI, color=ORANGE, lw=1.05,
                ls=(0, (2, 1.8)), label=r"$c-t$")
        ax.axhline(1, color=PURPLE, lw=1.05, ls=(0, (5, 1.5, 1, 1.5)),
                   label=r"$\pi$")
        ax.plot(t / PI, envelope / PI, color=INK, lw=2.0,
                label=r"$\min\{\beta+t,c-t,\pi\}$")
        ax.fill_between(t / PI, 0, envelope / PI, color="#EEF1F3", zorder=0)
        ax.set_title(title, loc="left", fontsize=9, pad=7)
        ax.set_xlim(0, c / PI)
        ax.set_ylim(0, 2.17)
        ax.set_yticks([0, 1, 2], ["0", "1", "2"])
        ax.set_xticks([0, .5, 1, 7 / 6], ["0", r"$1/2$", "1", r"$7/6$"])
        ax.set_xlabel(r"Half-segment time $t/\pi$", labelpad=3)
        ax.set_ylabel(r"Distance bound / $\pi$", labelpad=4)
        ax.tick_params(length=2.5, width=.6, pad=2)
        relation = r"$\beta=\pi/2,\quad c+\beta<2\pi$" if beta < PI * .6 else \
                   r"$\beta=11\pi/12,\quad c+\beta>2\pi$"
        ax.text(.025, 2.02, relation, fontsize=8, va="top")
        if beta + c > 2 * PI:
            lo, hi = PI - beta, c - PI
            ax.scatter([lo / PI, hi / PI], [1, 1], s=11, color=INK, zorder=7)
            ax.annotate(r"$\pi$ plateau", ((lo + hi) / (2 * PI), 1),
                        (.54, 1.34), fontsize=8, va="center",
                        arrowprops={"arrowstyle": "-", "color": GRAY, "lw": .7})
        else:
            switch = (c - beta) / 2
            ax.scatter(switch / PI, (c + beta) / (2 * PI), s=11, color=INK, zorder=7)
    handles, labels = axes[0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="lower center", bbox_to_anchor=(.5, .015),
               frameon=False, ncol=2, fontsize=8, handlelength=2.2,
               columnspacing=1.7, labelspacing=.5)
    save(fig, output, "midpoint_envelope")


def short_corpse(output):
    angle = PI / 3
    segments = family(angle)
    assert np.linalg.norm(segments[-1][3][-1]) < 2e-15
    fig = plt.figure(figsize=(3.4, 4.6))
    ax = fig.add_axes([.18, .69, .77, .230])
    fig.text(.06, .95, "(a)  Short-CORPSE control", fontsize=9)
    switches = np.array([0, PI / 3, 2 * PI, 7 * PI / 3])
    for j, value in enumerate((1, -1, 1)):
        ax.plot(switches[j:j+2] / PI, [value, value], color=COLORS[j], lw=TRAJECTORY_LW, solid_capstyle="round")
        ax.text((switches[j] + switches[j+1]) / (2 * PI), value + .18,
                str(j + 1), ha="center", va="bottom", fontsize=8.5)
    for x in switches[1:-1] / PI:
        ax.plot([x, x], [-1, 1], color=GRAY, lw=.7)
    ax.axhline(0, color=LIGHT, lw=.7, zorder=0)
    ax.set(xlim=(0, 7 / 3), ylim=(-1.4, 1.6),
           xlabel=r"$\Omega t/\pi$", ylabel=r"$u_x/\Omega$")
    ax.set_xticks(switches / PI, ["0", r"$1/3$", "2", r"$7/3$"])
    ax.set_yticks([-1, 1], ["−1", "+1"])
    ax.tick_params(length=2.5, width=.6)
    ax.text(.5, .51, r"$u_y=0$", transform=ax.transAxes, fontsize=8,
            ha="center", va="bottom")

    ax = fig.add_axes([.18, .155, .77, .375])
    fig.text(.06, .565, "(b)  Closed error curve", fontsize=9)
    ax.set_aspect("equal")
    for j, (_, _, _, path) in enumerate(segments):
        ax.plot(path[:, 0], path[:, 1], color=COLORS[j], lw=TRAJECTORY_LW, solid_capstyle="round")
        direction_arrow(ax, path, (.72, .50, .28)[j], COLORS[j])
    for point in (segments[0][3][0], segments[0][3][-1], segments[1][3][-1]):
        ax.scatter(*point, s=POINT_SIZE, color=INK, linewidths=0, zorder=8)
    arrow(ax, (0, 0), (0, .60), TEAL, .85, 6)
    arrow(ax, (0, 0), (0, -.48), PURPLE, .85, 6)
    ax.text(.34, .18, r"$\mathbf{n}(0)$", color=TEAL, fontsize=8.5, va="center")
    ax.text(.15, -.40, r"$\mathbf{n}(T)$", color=PURPLE, fontsize=8.5, va="center")
    ax.text(.67, .65, "1", color=TEAL)
    ax.text(1.13, 2.12, "2", color=ORANGE)
    ax.text(-.79, .65, "3", color=PURPLE)
    ax.text(-1.30, 2.76, r"$r_x=0$", color=GRAY, fontsize=8)
    ax.set(xlim=(-1.58, 1.58), ylim=(-.63, 2.95),
           xlabel=r"$\Omega r_y$", ylabel=r"$\Omega r_z$")
    ax.set_xticks([-1, 0, 1])
    ax.set_yticks([0, 1, 2])
    ax.tick_params(length=2.5, width=.6)
    ax.axhline(0, color=LIGHT, lw=.6, zorder=0)
    fig.text(.5, .022, r"$\mathbf{r}(0)=\mathbf{r}(T)=0$", ha="center", fontsize=8.5)
    save(fig, output, "short_corpse_geometry")


def build(output):
    output.mkdir(parents=True, exist_ok=True)
    style()
    residual_geometry(output)
    midpoint_envelope(output)
    short_corpse(output)
    print("Created residual_geometry, midpoint_envelope, short_corpse_geometry in", output)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parent / "assets")
    build(parser.parse_args().output_dir)
