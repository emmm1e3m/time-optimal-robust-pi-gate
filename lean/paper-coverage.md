# 论文与 Lean 形式化的对应

对应 2026-11-16 QST 双语修订稿。公式编号与标签以 `paper/manuscript.tex` 和 `paper/manuscript_zh.tex` 为准；两稿编号一致。本轮只更新覆盖说明，未改 Lean 数学源码，也未重新运行完整工程。既有构建和公理审计日期为 2026-11-04，入口见 [README](README.md#构建与审计)。

| 论文位置 | 标签及结果 | Lean 入口 |
| --- | --- | --- |
| 定理 1 | `thm:gate`：完整门的最小残差及全部达到控制 | [FrontierMain.lean](RobustPiGate/FrontierMain.lean) 的 `exact_frontier_and_all_minimizers`；[FrontierFidelity.lean](RobustPiGate/FrontierFidelity.lean) 将真实敏感度与残差连接；[FrontierBounds.lean](RobustPiGate/FrontierBounds.lean) 给原曲线下界 |
| 定理 2 | `thm:sphere`：任意 d≥2 的中点投影界和达到性 | [FrontierBounds.lean](RobustPiGate/FrontierBounds.lean)；[FrontierDimension.lean](RobustPiGate/FrontierDimension.lean) 的 `euclidean_minimum` |
| 推论 1 | `cor:robust-time`：最短稳健时间及全部达到控制 | [Main.lean](RobustPiGate/Main.lean) 的 `exact_time_and_all_minimizers` |
| 式 (34) | `eq:chi-curve`：失谐展开及 χ 与残差的关系 | [FrontierFidelity.lean](RobustPiGate/FrontierFidelity.lean) 的 `avgGateFidelity_sensitivity_limit`；[FrontierFidelityRemainder.lean](RobustPiGate/FrontierFidelityRemainder.lean) 给三阶余项 |
| 式 (35) | `eq:main`：χ 的精确最小值 | [FrontierMain.lean](RobustPiGate/FrontierMain.lean) 的 `exact_frontier_and_all_minimizers`；[FrontierPhysical.lean](RobustPiGate/FrontierPhysical.lean) |
| 式 (36) | `eq:lindblad`：所采用的 Lindblad 模型及与仿射信道的连接 | [FrontierNoise.lean](RobustPiGate/FrontierNoise.lean) 的 `lindblad`；[FrontierCombinedNoise.lean](RobustPiGate/FrontierCombinedNoise.lean) 的原方程接口。此处是模型定义和数学连接 |
| 式 (37) | `eq:weak-dissipation`：波形无关的首阶耗散及余项 | [FrontierCombinedNoise.lean](RobustPiGate/FrontierCombinedNoise.lean) 的 `weak_dissipation_rate_remainder` |
| 式 (38) | `eq:noise-parameters`：真实方差与噪声参数 | [FrontierCombinedNoise.lean](RobustPiGate/FrontierCombinedNoise.lean) 在联合预算中使用 Mathlib 的 `ProbabilityTheory.variance` 及相同 κL 规范 |
| 式 (39) | `eq:combined-expansion`：联合 O(η⁴) 预算 | [FrontierCombinedNoise.lean](RobustPiGate/FrontierCombinedNoise.lean) 的 `lindblad_weak_noise_budget` |
| 式 (40) | `eq:budget`：固定时长最小前导预算 | [FrontierMain.lean](RobustPiGate/FrontierMain.lean) 的 `leading_budget_minimum`；[FrontierOptimization.lean](RobustPiGate/FrontierOptimization.lean) 的 `global_leading_budget_attained` 另给全时长、全控制中的实际全局达到 |
| 式 (41) | `eq:working-point`：导数公式和内部最优点的驻点条件 | [FrontierBudget.lean](RobustPiGate/FrontierBudget.lean) 的 `budget_hasDerivAt`、`budget_stationary_iff`、`budget_global_min_stationary` |
| 式 (47) | `eq:near-robust`：稳健端点附近 χ 的二阶展开 | [FrontierBudget.lean](RobustPiGate/FrontierBudget.lean) 的 `sensitivity_shortening_isBigO`，以及同文件的显式余项界 |
| 式 (48) | `eq:compensation-cost`：缩短脉冲的线性耗散收益与二次失谐代价 | [FrontierBudget.lean](RobustPiGate/FrontierBudget.lean) 的 `weighted_budget_shortening_taylor` |

式 (42)–(46)（`eq:budget-slope`、`eq:budget-transition`、`eq:budget-critical`、`eq:relative-gain`、`eq:maximum-gain`）发展出的显式切换分类、λc≈0.176、Lc≈2.047π 以及相对较优端点的最大前导预算收益 4.91%，由正文解析推导及 [预算复算程序](../numerics/check_budget.py) 支持，未新增 Lean 形式化。这一说明针对显式切换和收益结论；式 (42) 是辅助定义，不表示其每个代数组成都缺少已有支持。

式 (39) 后补充了对全部允许控制及 L∈[π,7π/3] 一致的余项说明。该共同常数估计是本轮解析补充；既有 Lean 证明含实际固定控制的展开、传播压缩性及有限阶积分余项，但本轮没有新增对整个控制类的一致估计定理。

图 4(c) 是上述解析选择规则的可视化。图 5 是高斯准静态失谐与纯退相干下的完整信道数值验证，见 [程序](../paper/build_frontier_figure.py) 和 [数据](../paper/assets/frontier_full_channel.json)；同一数据文件的 `prescription_check` 另含正文 λ0=1/(2π) 的实际收益及三段族内数值调时比较。有限噪声数值、临界并列的高阶解除及新增图形没有被当作 Lean 定理。数值传播也不宣称完成了有限噪声下的全控制优化。
