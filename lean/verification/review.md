# 任务027：Lean与原问题的独立语义审查

状态：完成。独立语义审查与正式顶层模块的实际公理审计均通过。

## 最终判断

可以准确称“论文主定理已完整形式化”：原始量子ODE模型中的任意正幅度Ω、任意区间a.e.可测双横向控制，精确最短时间 `7π/(3Ω)`、正负两个真实达到族及全部最优控制的a.e.分类均已覆盖；球面主定理的有限维AC/a.e.版本、每个d≥2的锐性和完整等号刚性也已覆盖。

未发现把核心结论放入假设、将完整门替换为单态翻转、将全控制类缩到有限段或连续控制、假设误差公式、依赖不可导时默认 `deriv=0`、空可行集或非可积函数默认积分值造成的真空证明。无与这两个主定理相关的剩余实质缺口。

模型以控制和其原ODE的AC解族共同作为可行对象；没有另行形式化“每个可测有界控制都存在解族”的一般存在定理。当前量词直接覆盖所有这样的原ODE解，证明解唯一，并明确构造两类达到解的全部真实δ参数族，符合本轮明确要求的形式化范围。这项表示选择没有新增物理假设。

## 审查输入与方法

- 原问题：`input_time_optimal_robust_pi_gate/problem.md`。
- 论文：`output/manuscript.tex`，特别是两个主定理、误差曲线归约和所有等号控制。
- Lean：`output/lean/RobustPiGate/`。使用 Lean 4.35.0、mathlib v4.35.0。
- 按新建 REVIEW 上下文执行；未读取作者自评或前审报告。独立检查定义、量词、假设传递、证明结构和实际 `#print axioms`，没有用编译成功替代语义判断。
- 只写本任务目录；未更改共享实现。

## 已确认的语义链

### 1. 原量子模型和失谐导数

`Quantum.QubitMatrix` 是实际的 `Matrix (Fin 2) (Fin 2) ℂ`。Pauli 矩阵、`rx`、`transverseGenerator` 和 `detuningGenerator` 的坐标与原问题的 `-i/2` 规范一致。`Dynamics.qubit_generator_model` 把分解的生成元精确还原为三项 Hamiltonian。

`Dynamics.IsACSolution` 只包含区间绝对连续性、初值为单位矩阵，以及 a.e. `HasDerivAt U (G t * U t)`。`IsQubitEvolution ux uy U T` 对所有真实参数 `δ : ℝ` 要求此原ODE，其中 `ux,uy` 不依赖 δ。没有分段常数、有限切换、连续控制或满幅控制假设。

`duhamel_frame` 由两条原ODE相减、乘积微分和AC微积分基本定理证明；`norm_solution_sub_le` 与 `norm_solution_remainder_le` 再给出一阶差和二阶余项。`parameter_hasDerivAt` 因而证明端点函数对真实 δ 的实际导数，`qubit_parameter_hasDerivAt` 是论文变分公式的精确矩阵版本。`qubit_first_order_robust_iff` 使用已证明的可导性，因此不依赖 Lean 在不可导点把 `deriv` 设为0的默认规则。

这条链不要求从零形式化任意可测线性ODE的存在性：量词覆盖每一个满足原ODE的解族，且证明解唯一。此表示方式符合本任务给定的验收要求。它没有把稳健性—误差积分等价作为假设。

### 2. 球面几何下界和等号

`Geometry.EuclideanSpeedBound` 是单位欧氏 Lipschitz 界，`SphericalSpeedBound` 是球面角距离界。两者没有混淆：`sphericalSpeedBound_of_euclideanSpeedBound` 通过任意细分和趋零的二阶弦长误差证明从前者到后者的蕴含。

`ACCalculus.lipschitzOnWith_of_ac_deriv_bound` 对有限维空间使用AC蕴含的a.e.可导性、导数可测性和AC微积分基本定理，真正从 a.e. 速度界导出 Lipschitz 界。它不会容纳 Cantor 型奇异转向；AC前提不可省略且实际保留。

`SharpLength.spherical_curve_length_lower_bound` 的前提正是正时长、单位球路径、角速度界、反极端点和零向量积分。`Scalar` 中的显式下界公式、非负性、唯一零点及严格单调性均为被证明的结论；`Envelope` 实际积分两条分支，没有把关键积分值放入假设。`TimeScaling.ac_spherical_curve_length_lower_bound` 恢复论文有限维AC/a.e.版本；`spherical_curve_time_lower_bound` 通过真实时间重参数化证明 Ω 缩放。

路径连续性保证上述零积分均是实际可积函数的积分；真实噪声路径由AC性保证此点，没有利用Lean对不可积函数的默认积分值。

`Equality.spherical_curve_equality_rigidity` 从原几何条件导出中点正交和完整三弧轨道。`Rigidity` 中采用球面三角不等式取等号和插值的证明，与论文的横向导数范数分解不同，但证明相同结论；其上层并没有把径向包络饱和当作额外输入。

### 3. 非空性和真实达到解

`ShortEvolution.shortDetunedPropagator` 是三个真实矩阵指数按时间顺序相乘，δ对每一段均为同一个常数。其AC性、a.e.原ODE、单位初值和幺正性均已证明。`shortDetunedPropagator_certificate` 给出实际可测控制、幅度限制、终门 `-rx π` 和 `HasDerivAt ... 0 0`。这排除了由空控制集、空状态类型或虚设演化族导致的真空结论。

`LiftUniqueness.transverse_controls_unique` 通过原ODE和同噪声曲线得到实际控制a.e.唯一性；内部的同噪声假设是局部提升引理所需中间条件。最终 `OptimalControls` 已由几何刚性主动构造参考提升并给出这个条件。

### 4. 实际Bloch桥接

`BlochBridge.blochVec` 从矩阵元读取 `(Re A₀₁, −Im A₀₁, Re A₀₀)`，`noiseVec` 对实际 `U†σzU` 应用此映射。Hermitian、无迹和Pauli重建均被证明，因此此向量不是独立自由变量。单位范数来自实际幺正共轭；`noiseVelocity_norm_sq` 证明欧氏速度平方精确等于 `ux²+uy²`；AC性、a.e.导数、Lipschitz界、完整门产生的反极端点及零积分都主动推导。

`actual_gate_time_lower_bound` 只要求Ω>0、T>0、原ODE解族、a.e.幅度圆盘、完整终门和真实稳健性，已将物理模型与任意Ω的锐下界连接。没有输入几何证书、噪声标架、平面性或预设最优时长。

`RotatedShort` 中任意横向单位轴的参考传播子也直接满足原名义ODE，`axisRotation_conjugates_z` 给出实际矩阵噪声公式；正交轴的单位长度是这一参考构造自然必需条件，最终应由噪声中点的单位范数和正交性推出。

### 5. 物理最小值与归一化控制分类

`PhysicalMain.AdmissibleRobustPi` 将T≥0、区间AEMeasurable控制、原ODE、a.e.幅度、完整±目标门和稳健性原样组合。`robustPiDurations` 对两控制及其演化族均取存在量词。`duration_pos` 排除T=0，`robust_hasDerivAt` 明示实际可导性。

`scaledShortPropagator Ω δ t = shortDetunedPropagator (δ/Ω) (Ω*t)` 保留物理失谐项δ，而非错误地把δ同时放大；`detunedGenerator_scale` 与真实参数链式法则分别证明ODE和稳健性。`robust_pi_minimum` 是这个实际物理可行时长集合的 `IsLeast`，`robust_pi_infimum` 是其 `sInf`，覆盖任意Ω>0。

`OptimalControls.optimal_controls_unique` 的输入仅为原ODE、a.e.幅度界、完整终门和稳健性。中点向量v的单位范数与z分量为0导出参考横向轴 `(-v_y,v_x)` 为单位轴；参考演化与实际演化的噪声矩阵相同是从几何刚性主动证明的。随后使用横向提升唯一性和完整门选轴，得出两个a.e.命题的全局析取：全程为q，或全程为−q；没有允许逐时改变符号。

### 6. 每个维数的几何锐性

`DimensionSharpness.planePath` 将真实shortPhase放进任意给定的正交单位向量平面，证明单位范数、Lipschitz、反极端点和零积分。`euclidean_minimum` 从d≥2明确选择两个不同标准基向量，得到每个 `EuclideanSpace ℝ (Fin d)` 的 `IsLeast`；因此原先只有三维达到证书的范围缺口已补齐。

### 7. 任意Ω的全部最优控制及两个实际达到族

`EvolutionScaling.optimal_controls_unique_scaled` 将真实名义传播子及规范噪声方向重参数化。它从a.e.原ODE与幅度界先证明传播子Lipschitz，从而保留AC；`ae_comp_mul`/`ae_comp_div` 使用非零线性变换的准保测性，正确搬运a.e.控制条件。应用已证归一化刚性后再搬回原时间，得到全局固定符号的 `ux(t)=±Ω q(Ωt), uy(t)=0`，并非逐点任选符号。

`SignSymmetry.negativeScaledShortPropagator` 对真实正号解族作σz共轭。其初值仍为I、生成元恰为负号横向控制和原值δ、AC/a.e.原ODE、完整正号目标门以及真实δ零导数均显式证明。这里的共轭是另一条实际控制轨道的数学构造，不是免费插入两个z门。

`Main.exact_time_and_all_minimizers` 汇合实际物理 `IsLeast` 和任意可行最优控制的完整a.e.分类；`Main.both_short_signs_attain` 把正负两个真实δ演化族放入同一 `AdmissibleRobustPi` 结构。两者合用完整覆盖论文的精确时长、可达性和所有最优控制结论。

## 当前应注意的最终接口

1. 已核查PhysicalMain保留所有原问题条件；物理时长集合独立于几何时长集合，现已直接证明其最小元。
2. 最终采用区间 `AEMeasurable`，原先Borel代表元的语义疑点已解决；下界和唯一性本身无需额外可测性假设。
3. 任意d≥2的锐性已通过DimensionSharpness解决。
4. 任意Ω的控制分类与整体负号真实δ达到族已审查通过，必要性与两个控制类均实际达到现已完整对应。

## 实际公理审计

运行：在 `output/lean/` 执行 `lake env lean ../../work/review/027/Audit.lean`。

证据：[Audit.lean](Audit.lean)、[audit_initial.log](audit_initial.log)。初轮退出码0。20个核心结论的实际依赖只含 `propext`, `Classical.choice`, `Quot.sound`；无 `sorryAx`、自建axiom、`Lean.ofReduceBool`。源文件危险构造检索亦未发现 `sorry`、`admit`、自建 `axiom`、`unsafe`、`implemented_by` 或 `native_decide`。

为避免由可行性定义或抽象接口造成问题替换，另写 [OriginalModelAudit.lean](OriginalModelAudit.lean)，直接以原问题的矩阵ODE、AC、初值、a.e.幅度、±门和 `HasDerivAt ... 0 0` 为前提，调用得到任意实Ω>0的物理下界。[audit_original_model.log](audit_original_model.log) 退出码0，实际依赖仍仅上述3个标准公理。

最终审计证据：[FinalAudit.lean](FinalAudit.lean)、[audit_final.log](audit_final.log)。在正式完整构建完成后，从顶层 `import RobustPiGate` 执行，退出码0；19个最终及核心定理均只依赖 `propext`, `Classical.choice`, `Quot.sound`。日志同时打印实际可行结构、物理时长集合及全部最终出口类型。源文件危险构造复核无匹配。未重编mathlib。

正式顶层 `RobustPiGate.lean` 已导入 `Main` 和 `ExactGeometric`，所以正常项目入口包含物理主定理、双符号达到、所有最优者分类与几何定理，不是只编译基础常数文件。

本报告适用于本次读取并由最终日志加载的正式源码版本。下一步可交付论文与Lean包；无需为本轮验收再增加探索或证明任务。
