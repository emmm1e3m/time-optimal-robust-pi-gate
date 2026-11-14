# Lean 4 形式化证明

本工程从原始 AC/a.e. 量子动力学出发，证明完整 π 门的精确速度—失谐敏感度边界、全部达到控制，以及弱耗散下的前导预算和全局工作点。固定 Lean 4.35.0、mathlib v4.35.0。

## 主要入口

下列名称位于 `RobustPiGate` 命名空间。

| 入口 | 已形式化内容 |
| --- | --- |
| [FrontierMain.lean](RobustPiGate/FrontierMain.lean)：`exact_frontier_and_all_minimizers` | 任意 Ω>0、π≤ΩT≤7π/3 的真实敏感度最小元及全部达到者 |
| `both_frontier_signs_attain` | 两种整体符号的全失谐演化真实达到边界，包括 a=0 |
| `AdmissiblePi.nominal_time_lower_bound` | 原完整门条件推出 ΩT≥π |
| [FrontierFidelity.lean](RobustPiGate/FrontierFidelity.lean)：`Quantum.avgGateFidelity_sensitivity_limit` | 实际平均门保真度的穿孔极限 χ=Ω²‖∫n‖²/6 |
| [FrontierFidelityRemainder.lean](RobustPiGate/FrontierFidelityRemainder.lean) / [FrontierFidelitySymmetry.lean](RobustPiGate/FrontierFidelitySymmetry.lean) | 明确三阶静态余项、单轴控制的精确失谐偶性 |
| [FrontierDimension.lean](RobustPiGate/FrontierDimension.lean)：`FrontierDimension.euclidean_minimum` | 每个 d≥2、每个区间内时长，在原 AC/a.e. 曲线类上取得几何最小元 |
| [FrontierCombinedNoise.lean](RobustPiGate/FrontierCombinedNoise.lean)：`FrontierNoise.lindblad_weak_noise_budget` | 原 Lindblad 初值问题、实际纯输入球面平均、真实方差和 χ 的联合 O(η⁴) 预算 |
| `FrontierNoise.weak_dissipation_rate_remainder` | 波形无关的一阶耗散及显式 O((ΓT)²) 余项 |
| [FrontierOptimization.lean](RobustPiGate/FrontierOptimization.lean)：`global_leading_budget_attained` | 全部物理时长及全部原控制中的前导预算存在实际达到的全局最小门 |
| [FrontierBudget.lean](RobustPiGate/FrontierBudget.lean)：`budget_global_shortening_isBigO` | 每个全局最优点均满足 h=4λ+O(λ²) |
| [FrontierBudgetEndpoints.lean](RobustPiGate/FrontierBudgetEndpoints.lean) | λ≥2/3 时矩形 π 脉冲全局最优的充分条件 |
| [Main.lean](RobustPiGate/Main.lean)：`exact_time_and_all_minimizers` | 保留原零敏感度端点的精确时间与全部控制分类 |

## 构建与审计

```powershell
lake exe cache get
lake build
lake env lean Audit.lean
lake env lean verification/AllDeclarationsAudit.lean
lake env lean verification/FrontierAudit.lean
lake env lean verification/NoiseAudit.lean
```

2026-11-04 全部 47 个数学模块及顶层导入构建成功。逐模块枚举的 1237 个项目声明（其中 1057 个定理声明，包含自动生成项）全部通过公理审计，仅依赖 `propext`、`Classical.choice`、`Quot.sound`。正式数学源码无 `sorry`、`admit`、自建公理、`unsafe` 或 `native_decide`。源码包不含 `.lake` 缓存。

[完整构建日志](verification/full-build.log)、[逐声明审计](verification/all-declarations.log)、[关键出口审计](verification/key-axioms.log)、[前沿原始前提探针](verification/FrontierAudit.lean)、[物理预算探针](verification/NoiseAudit.lean)均随源码提供。

## 模型与证明连接

`AdmissiblePi` 只要求控制在区间上 a.e. 可测、联合幅度受限、传播子满足原 AC/a.e. 薛定谔方程并实现完整 ±Rx(π)。没有预设平面、饱和、有限段数、残差或鲁棒性。幺正性、真实失谐可导性、噪声曲线和敏感度极限均由方程推出；达到族显式构造全部 δ 下的矩阵指数演化。

弱噪声部分采用 δ=ηξ、Γj=η²γj，γj≥0，固定时长，对称 ξ 具有有限四阶矩。`IsNoisyLindbladChannel` 规定真实仿射 Bloch 初值问题，包含平移初值 c(0)=0；最终定理主动给出全部输入的原 Lindblad 方程及其初值。平均门保真度由实际 z、φ 球面积分定义，方差使用 Mathlib 的 `ProbabilityTheory.variance`。Dyson 余项对全部实 ξ 一致成立，随机解族的连续性、可测性及可积性由原 ODE 和收缩推出。

工作点结论针对前导弱噪声泛函。图中的 2.08π 和 4.91% 是独立复核的数值示例；两端预算相等、全局最优性原则及渐近关系有精确形式化。文献归属和优先权判断不属于 Lean 命题。一般可测有界系数的线性 ODE 存在性没有另设通用存在定理，工程对原方程的 AC 解作量化，并显式提供达到控制的幺正演化。
