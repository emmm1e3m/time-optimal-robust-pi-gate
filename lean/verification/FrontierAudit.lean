import RobustPiGate.FrontierMain

noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal Matrix Matrix.Norms.L2Operator InnerProductSpace
namespace Review067
open RobustPiGate RobustPiGate.Quantum RobustPiGate.Dynamics

/-- 直接输入原文的 AC 薛定谔方程，不预设噪声曲线或参数导数。 -/
theorem original_evolution {ux uy : ℝ → ℝ} {U : ℝ → ℝ → QubitMatrix} {T : ℝ}
    (hac : ∀ δ, AbsolutelyContinuousOnInterval (U δ) 0 T)
    (hinit : ∀ δ, U δ 0 = 1)
    (hode : ∀ δ, ∀ᵐ t, t ∈ Icc 0 T →
      HasDerivAt (U δ)
        (((-Complex.I / 2) • ((ux t : ℂ) • sigmaX +
          (uy t : ℂ) • sigmaY + (δ : ℂ) • sigmaZ)) * U δ t) t)
    (hT : 0 ≤ T) : IsQubitEvolution ux uy U T := by
  intro δ
  refine ⟨hac δ, hinit δ, ?_⟩
  filter_upwards [hode δ] with t ht htI
  rw [uIcc_of_le hT] at htI
  rw [qubit_generator_model]
  exact ht htI

/-- 原始演化前提直接推出实际 trace 公式的穿孔极限。 -/
theorem original_fidelity_limit {ux uy : ℝ → ℝ} {U : ℝ → ℝ → QubitMatrix}
    {T Ω : ℝ} (hac : ∀ δ, AbsolutelyContinuousOnInterval (U δ) 0 T)
    (hinit : ∀ δ, U δ 0 = 1)
    (hode : ∀ δ, ∀ᵐ t, t ∈ Icc 0 T →
      HasDerivAt (U δ)
        (((-Complex.I / 2) • ((ux t : ℂ) • sigmaX +
          (uy t : ℂ) • sigmaY + (δ : ℂ) • sigmaZ)) * U δ t) t)
    (hT : 0 ≤ T) :
    Tendsto (fun f =>
      (1 - (Complex.normSq (Matrix.trace ((U 0 T).conjTranspose * U (Ω * f) T)) + 2) / 6) / f ^ 2)
      (𝓝[≠] 0) (𝓝 (Ω ^ 2 * ‖∫ t in 0..T, noiseVec (U 0 t)‖ ^ 2 / 6)) :=
  avgGateFidelity_sensitivity_limit (original_evolution hac hinit hode hT) Ω

/-- 等号分类的输入只有真实保真度极限达到解析前沿和原始物理条件。 -/
theorem original_attaining_controls {ux uy : ℝ → ℝ} {U : ℝ → ℝ → QubitMatrix}
    {T Ω : ℝ} (hΩ : 0 < Ω) (hL : Ω * T ∈ Icc Real.pi (7 * Real.pi / 3))
    (hac : ∀ δ, AbsolutelyContinuousOnInterval (U δ) 0 T)
    (hinit : ∀ δ, U δ 0 = 1)
    (hode : ∀ δ, ∀ᵐ t, t ∈ Icc 0 T →
      HasDerivAt (U δ)
        (((-Complex.I / 2) • ((ux t : ℂ) • sigmaX +
          (uy t : ℂ) • sigmaY + (δ : ℂ) • sigmaZ)) * U δ t) t)
    (hamp : ∀ᵐ t, t ∈ Icc 0 T → (ux t) ^ 2 + (uy t) ^ 2 ≤ Ω ^ 2)
    (hgate : U 0 T = rx Real.pi ∨ U 0 T = -rx Real.pi)
    (hlimit : Tendsto (fun f =>
      (1 - (Complex.normSq (Matrix.trace ((U 0 T).conjTranspose * U (Ω * f) T)) + 2) / 6) / f ^ 2)
      (𝓝[≠] 0) (𝓝 ((4 * Real.cos ((Ω * T - Real.pi) / 4) - 2) ^ 2 / 6))) :
    (∀ᵐ t, t ∈ Icc 0 T →
      ux t = Ω * frontierControl ((Ω * T - Real.pi) / 4) (Ω * t) ∧ uy t = 0) ∨
    (∀ᵐ t, t ∈ Icc 0 T →
      ux t = -(Ω * frontierControl ((Ω * T - Real.pi) / 4) (Ω * t)) ∧ uy t = 0) := by
  have hT : 0 ≤ T := by nlinarith [Real.pi_pos, hL.1]
  have hU := original_evolution hac hinit hode hT
  have hlimit' := avgGateFidelity_sensitivity_limit hU Ω
  have he : Ω ^ 2 * ‖∫ t in 0..T, noiseVec (U 0 t)‖ ^ 2 / 6 =
      frontierSensitivity (Ω * T) := tendsto_nhds_unique hlimit' hlimit
  have hg : 0 ≤ frontierResidual (Ω * T) :=
    frontierResidual_nonneg hL.1 (by dsimp [criticalHalf]; linarith [hL.2])
  have hn : 0 ≤ Ω * ‖∫ t in 0..T, noiseVec (U 0 t)‖ :=
    mul_nonneg hΩ.le (norm_nonneg _)
  have hr : Ω * ‖∫ t in 0..T, noiseVec (U 0 t)‖ = frontierResidual (Ω * T) := by
    dsimp [frontierSensitivity] at he
    nlinarith
  exact frontier_optimal_controls_unique_scaled hΩ hL hU hamp hgate hr

/-- 原始 AC/a.e. 曲线前提；不将球面 Lipschitz 或平面作为假设。 -/
theorem original_geometric_bounds {d : ℕ} {n : ℝ → EuclideanSpace ℝ (Fin d)} {L : ℝ}
    (hL : L ∈ Icc Real.pi (7 * Real.pi / 3))
    (hac : AbsolutelyContinuousOnInterval n 0 L)
    (hunit : ∀ t ∈ Icc 0 L, ‖n t‖ = 1)
    (hderiv : ∀ᵐ t, t ∈ Icc 0 L → ‖deriv n t‖ ≤ 1) (hend : n L = -n 0) :
    0 ≤ frontierResidual L ∧
    frontierResidual L ≤ ⟪n (L / 2), ∫ t in 0..L, n t⟫_ℝ ∧
    ⟪n (L / 2), ∫ t in 0..L, n t⟫_ℝ ≤ ‖∫ t in 0..L, n t‖ :=
  ac_spherical_curve_frontier_bounds hL.1 hL.2 hac hunit hderiv hend

/-- 最小元可改写成实际极限值集合，不依赖 limUnder 的非存在默认行为。 -/
theorem actual_limit_minimum {Ω : ℝ≥0} {T : ℝ}
    (hΩ : 0 < Ω) (hL : (Ω : ℝ) * T ∈ Icc Real.pi (7 * Real.pi / 3)) :
    IsLeast {χ : ℝ | ∃ ux uy U, AdmissiblePi Ω T ux uy U ∧
      Tendsto (fun f => (1 - avgGateFidelity U Ω T f) / f ^ 2) (𝓝[≠] 0) (𝓝 χ)}
      ((4 * Real.cos (((Ω : ℝ) * T - Real.pi) / 4) - 2) ^ 2 / 6) := by
  have hmain := exact_frontier_and_all_minimizers hΩ hL
  change IsLeast _ (frontierSensitivity ((Ω : ℝ) * T))
  constructor
  · obtain ⟨ux, uy, U, h, hχ⟩ := hmain.1.1
    refine ⟨ux, uy, U, h, ?_⟩
    have hl := avgGateFidelity_sensitivity_limit h.evolution (Ω : ℝ)
    rw [← detuningSensitivity_eq h.evolution, ← hχ] at hl
    exact hl
  · rintro χ ⟨ux, uy, U, h, hl⟩
    have he : detuningSensitivity U Ω T = χ := hl.limUnder_eq
    rw [← he]
    exact h.sensitivity_lower_bound hΩ hL.1 hL.2

/-- d 的量词没有固定为三维，最终前提中也无需预先给正交向量。 -/
theorem every_dimension_attains {d : ℕ} (hd : 2 ≤ d) {L : ℝ}
    (hL : L ∈ Icc Real.pi (7 * Real.pi / 3)) :
    IsLeast {r : ℝ | ∃ n : ℝ → EuclideanSpace ℝ (Fin d),
      AbsolutelyContinuousOnInterval n 0 L ∧
      (∀ᵐ t, t ∈ Icc 0 L → ‖deriv n t‖ ≤ 1) ∧
      (∀ t ∈ Icc 0 L, ‖n t‖ = 1) ∧ n L = -n 0 ∧ r = ‖∫ t in 0..L, n t‖}
      (4 * Real.cos ((L - Real.pi) / 4) - 2) :=
  FrontierDimension.euclidean_minimum hd hL.1 hL.2

/-- 最短名义门端点的最小元确为 2/3。 -/
theorem rectangular_endpoint {Ω : ℝ≥0} (hΩ : 0 < Ω) :
    IsLeast (piSensitivities Ω (Real.pi / (Ω : ℝ))) (2 / 3) := by
  have hΩn : (Ω : ℝ) ≠ 0 := ne_of_gt hΩ
  have hs : (Ω : ℝ) * (Real.pi / (Ω : ℝ)) = Real.pi := by field_simp [hΩn]
  have hL : (Ω : ℝ) * (Real.pi / (Ω : ℝ)) ∈ Icc Real.pi (7 * Real.pi / 3) := by
    rw [hs]
    constructor
    · rfl
    · linarith [Real.pi_pos]
  have h := (exact_frontier_and_all_minimizers hΩ hL).1
  have hg : frontierSensitivity Real.pi = (2 : ℝ) / 3 := by
    norm_num [frontierSensitivity, frontierResidual]
  simpa only [hs, hg] using h

/-- a=0 并不需要补一个排除零端段的假设，正负符号均有物理解。 -/
theorem both_rectangular_signs {Ω : ℝ≥0} (hΩ : 0 < Ω) :
    (AdmissiblePi Ω (scaledFrontierTime 0 Ω) (scaledFrontierControl 0 Ω) (fun _ => 0)
      (scaledFrontierPropagator 0 Ω) ∧
      detuningSensitivity (scaledFrontierPropagator 0 Ω) Ω (scaledFrontierTime 0 Ω) = 2 / 3) ∧
    (AdmissiblePi Ω (scaledFrontierTime 0 Ω) (negativeScaledFrontierControl 0 Ω) (fun _ => 0)
      (negativeScaledFrontierPropagator 0 Ω) ∧
      detuningSensitivity (negativeScaledFrontierPropagator 0 Ω) Ω (scaledFrontierTime 0 Ω) = 2 / 3) := by
  have h := both_frontier_signs_attain hΩ
    (a := 0) (show 0 ∈ Icc (0 : ℝ) (Real.pi / 3) from ⟨le_rfl, by positivity⟩)
  have hg : frontierSensitivity (frontierDuration 0) = (2 : ℝ) / 3 := by
    norm_num [frontierSensitivity, frontierResidual, frontierDuration]
  simpa only [hg] using h

/-- 鲁棒端点的真实敏感度最小元为零。 -/
theorem robust_endpoint {Ω : ℝ≥0} (hΩ : 0 < Ω) :
    IsLeast (piSensitivities Ω (7 * Real.pi / (3 * (Ω : ℝ)))) 0 := by
  have hΩn : (Ω : ℝ) ≠ 0 := ne_of_gt hΩ
  have hs : (Ω : ℝ) * (7 * Real.pi / (3 * (Ω : ℝ))) = 7 * Real.pi / 3 := by
    field_simp [hΩn]
  have hL : (Ω : ℝ) * (7 * Real.pi / (3 * (Ω : ℝ))) ∈ Icc Real.pi (7 * Real.pi / 3) := by
    rw [hs]
    constructor
    · linarith [Real.pi_pos]
    · rfl
  have h := (exact_frontier_and_all_minimizers hΩ hL).1
  have hg : frontierResidual (7 * Real.pi / 3) = 0 := by
    have hc : 2 * criticalHalf = 7 * Real.pi / 3 := by dsimp [criticalHalf]; ring
    simpa only [hc] using frontierResidual_critical
  simpa [hs, frontierSensitivity, hg] using h

/-- 顶层名义门速度限不需要任何鲁棒前提。 -/
theorem no_sub_pi_gate {Ω : ℝ≥0} {T : ℝ} (hΩ : 0 < Ω)
    (hL : (Ω : ℝ) * T < Real.pi) :
    ¬ ∃ ux uy U, AdmissiblePi Ω T ux uy U := by
  rintro ⟨ux, uy, U, h⟩
  exact (not_le_of_gt hL) (h.nominal_time_lower_bound hΩ)

/-- 原敏感度零点与原失谐导数消失等价，参数可导性来自已审 ODE。 -/
theorem zero_sensitivity_iff_first_order {ux uy : ℝ → ℝ}
    {U : ℝ → ℝ → QubitMatrix} {T Ω : ℝ}
    (hΩ : 0 < Ω) (hU : IsQubitEvolution ux uy U T) :
    detuningSensitivity U Ω T = 0 ↔ deriv (fun δ => U δ T) 0 = 0 := by
  constructor
  · intro h
    rw [detuningSensitivity_eq hU] at h
    have hv : (∫ t in 0..T, noiseVec (U 0 t)) = 0 := by
      simpa [hΩ.ne', mul_eq_zero] using h
    apply (qubit_first_order_robust_iff hU).mpr
    change (∫ t in 0..T, noiseMatrix (U 0 t)) = 0
    rw [noise_integral_eq_pauli hU, hv, map_zero]
  · intro h
    have hv := noiseVec_integral_zero (qubit_nominal_solution hU).ac
      ((qubit_first_order_robust_iff hU).mp h)
    rw [detuningSensitivity_eq hU, hv]
    simp

end Review067

#print axioms Review067.original_evolution
#print axioms Review067.original_fidelity_limit
#print axioms Review067.original_attaining_controls
#print axioms Review067.original_geometric_bounds
#print axioms Review067.actual_limit_minimum
#print axioms Review067.every_dimension_attains
#print axioms Review067.rectangular_endpoint
#print axioms Review067.both_rectangular_signs
#print axioms Review067.robust_endpoint
#print axioms Review067.no_sub_pi_gate
#print axioms Review067.zero_sensitivity_iff_first_order
#print axioms RobustPiGate.exact_frontier_and_all_minimizers
#print axioms RobustPiGate.both_frontier_signs_attain
#print axioms RobustPiGate.frontier_sum_eq_iff
#print axioms RobustPiGate.Quantum.scaledFrontierPropagator_certificate
#print axioms RobustPiGate.Quantum.negativeScaledFrontierPropagator_certificate
