import RobustPiGate.FrontierGeometry
import RobustPiGate.FrontierScalar

noncomputable section
open Real Set MeasureTheory InnerProductGeometry
open scoped InnerProductSpace NNReal
namespace RobustPiGate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- 两半显式包络与标量极小值合成真实曲线的中点投影界。 -/
theorem midpoint_projection_frontier_lower_bound {n : ℝ → E} {c : ℝ}
    (hc0 : Real.pi / 2 ≤ c) (hc1 : c ≤ criticalHalf)
    (hcont : ContinuousOn n (Icc 0 (2 * c)))
    (hunit : ∀ t ∈ Icc 0 (2 * c), ‖n t‖ = 1)
    (hspeed : SphericalSpeedBound n 0 (2 * c))
    (hend : n (2 * c) = -n 0) :
    frontierResidual (2 * c) ≤ ⟪n c, ∫ t in 0..2 * c, n t⟫_ℝ := by
  have hc : 0 ≤ c := by linarith [Real.pi_pos]
  obtain ⟨hαc, hβc⟩ := midpoint_angle_feasible hc hspeed hend
  exact (frontier_sum_ge hc0 hc1 (angle_nonneg _ _) (angle_le_pi _ _) hαc hβc).trans
    (midpoint_halfBound_le_integral hc hcont hunit hspeed hend)

/-- 单位中点方向的投影不超过向量积分的模长。 -/
theorem midpoint_projection_le_integral_norm {n : ℝ → E} {c : ℝ}
    (hc : 0 ≤ c) (hunit : ∀ t ∈ Icc 0 (2 * c), ‖n t‖ = 1) :
    ⟪n c, ∫ t in 0..2 * c, n t⟫_ℝ ≤ ‖∫ t in 0..2 * c, n t‖ := by
  simpa [hunit c ⟨hc, by linarith⟩] using
    real_inner_le_norm (n c) (∫ t in 0..2 * c, n t)

/-- 原时长变量中的完整非负下界链，适用于任意实 Hilbert 空间。 -/
theorem spherical_curve_frontier_bounds {n : ℝ → E} {L : ℝ}
    (hL0 : Real.pi ≤ L) (hL1 : L ≤ 7 * Real.pi / 3)
    (hcont : ContinuousOn n (Icc 0 L))
    (hunit : ∀ t ∈ Icc 0 L, ‖n t‖ = 1)
    (hspeed : SphericalSpeedBound n 0 L) (hend : n L = -n 0) :
    0 ≤ frontierResidual L ∧
      frontierResidual L ≤ ⟪n (L / 2), ∫ t in 0..L, n t⟫_ℝ ∧
      ⟪n (L / 2), ∫ t in 0..L, n t⟫_ℝ ≤ ‖∫ t in 0..L, n t‖ := by
  have heq : 2 * (L / 2) = L := by ring
  have hc0 : Real.pi / 2 ≤ L / 2 := by linarith
  have hc1 : L / 2 ≤ criticalHalf := by dsimp [criticalHalf]; linarith
  have hp := midpoint_projection_frontier_lower_bound hc0 hc1
    (by simpa [heq] using hcont) (by simpa [heq] using hunit)
    (by simpa [heq] using hspeed) (by simpa [heq] using hend)
  have hn := midpoint_projection_le_integral_norm (c := L / 2)
    (by linarith [Real.pi_pos]) (by simpa [heq] using hunit)
  exact ⟨frontierResidual_nonneg hL0 (by dsimp [criticalHalf]; linarith),
    by simpa [heq] using hp, by simpa [heq] using hn⟩

/-- 连续球面曲线的精确残差下界；速度以球面 Lipschitz 条件给出。 -/
theorem spherical_curve_frontier_lower_bound {n : ℝ → E} {L : ℝ}
    (hL0 : Real.pi ≤ L) (hL1 : L ≤ 7 * Real.pi / 3)
    (hcont : ContinuousOn n (Icc 0 L))
    (hunit : ∀ t ∈ Icc 0 L, ‖n t‖ = 1)
    (hspeed : SphericalSpeedBound n 0 L) (hend : n L = -n 0) :
    frontierResidual L ≤ ‖∫ t in 0..L, n t‖ := by
  have h := spherical_curve_frontier_bounds hL0 hL1 hcont hunit hspeed hend
  exact h.2.1.trans h.2.2

/-- 论文中的原始 AC 与几乎处处导数界假设给出完整中点投影下界链。 -/
theorem ac_spherical_curve_frontier_bounds [FiniteDimensional ℝ E]
    {n : ℝ → E} {L : ℝ} (hL0 : Real.pi ≤ L) (hL1 : L ≤ 7 * Real.pi / 3)
    (hac : AbsolutelyContinuousOnInterval n 0 L)
    (hunit : ∀ t ∈ Icc 0 L, ‖n t‖ = 1)
    (hderiv : ∀ᵐ t, t ∈ Icc 0 L → ‖deriv n t‖ ≤ 1)
    (hend : n L = -n 0) :
    0 ≤ frontierResidual L ∧
      frontierResidual L ≤ ⟪n (L / 2), ∫ t in 0..L, n t⟫_ℝ ∧
      ⟪n (L / 2), ∫ t in 0..L, n t⟫_ℝ ≤ ‖∫ t in 0..L, n t‖ := by
  have hL : 0 ≤ L := Real.pi_pos.le.trans hL0
  have hLip := Dynamics.lipschitzOnWith_of_ac_deriv_bound (K := 1) hac
    (by simpa [uIcc_of_le hL] using hderiv)
  rw [uIcc_of_le hL] at hLip
  exact spherical_curve_frontier_bounds hL0 hL1 hLip.continuousOn hunit
    (sphericalSpeedBound_of_lipschitzOnWith hunit hLip) hend

/-- 原始 AC 模型的残差模长结论。 -/
theorem ac_spherical_curve_frontier_lower_bound [FiniteDimensional ℝ E]
    {n : ℝ → E} {L : ℝ} (hL0 : Real.pi ≤ L) (hL1 : L ≤ 7 * Real.pi / 3)
    (hac : AbsolutelyContinuousOnInterval n 0 L)
    (hunit : ∀ t ∈ Icc 0 L, ‖n t‖ = 1)
    (hderiv : ∀ᵐ t, t ∈ Icc 0 L → ‖deriv n t‖ ≤ 1)
    (hend : n L = -n 0) : frontierResidual L ≤ ‖∫ t in 0..L, n t‖ := by
  have h := ac_spherical_curve_frontier_bounds hL0 hL1 hac hunit hderiv hend
  exact h.2.1.trans h.2.2

/-- 全局模长取等强制两半曲线在每一点取中点径向包络等号。 -/
theorem spherical_curve_frontier_equality_angles {n : ℝ → E} {c : ℝ}
    (hc0 : Real.pi / 2 ≤ c) (hc1 : c ≤ criticalHalf)
    (hcont : ContinuousOn n (Icc 0 (2 * c)))
    (hunit : ∀ t ∈ Icc 0 (2 * c), ‖n t‖ = 1)
    (hspeed : SphericalSpeedBound n 0 (2 * c))
    (hend : n (2 * c) = -n 0)
    (heq : ‖∫ t in 0..2 * c, n t‖ = frontierResidual (2 * c)) :
    (∀ s ∈ Icc 0 c, angle (n c) (n (c - s)) = min s (c + Real.pi / 2 - s)) ∧
    (∀ s ∈ Icc 0 c, angle (n c) (n (c + s)) = min s (c + Real.pi / 2 - s)) := by
  have hc : 0 < c := by linarith [Real.pi_pos]
  have hα0 := angle_nonneg (n c) (n 0)
  have hαπ := angle_le_pi (n c) (n 0)
  obtain ⟨hαc, hβc⟩ := midpoint_angle_feasible hc.le hspeed hend
  have hscalar := frontier_sum_ge hc0 hc1 hα0 hαπ hαc hβc
  have hproj := midpoint_halfBound_le_integral hc.le hcont hunit hspeed hend
  have hnorm := midpoint_projection_le_integral_norm hc.le hunit
  have hsum : halfBound c (angle (n c) (n 0)) +
      halfBound c (Real.pi - angle (n c) (n 0)) = frontierResidual (2 * c) := by
    apply le_antisymm _ hscalar
    exact hproj.trans (hnorm.trans_eq heq)
  have hα : angle (n c) (n 0) = Real.pi / 2 :=
    (frontier_sum_eq_iff hc0 hc1 hα0 hαπ hαc hβc).mp hsum
  have hpeq : halfBound c (angle (n c) (n 0)) +
      halfBound c (Real.pi - angle (n c) (n 0)) =
      ⟪n c, ∫ t in 0..2 * c, n t⟫_ℝ := by
    apply le_antisymm hproj
    rw [hsum]
    exact hnorm.trans_eq heq
  obtain ⟨hl, hr⟩ := midpoint_projection_eq_envelopes hc hcont hunit hspeed hend hpeq
  rw [hα] at hl hr
  rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring] at hr
  have hv : ‖n c‖ = 1 := hunit c ⟨hc.le, by linarith⟩
  constructor
  · intro s hs
    rw [← envelope_midpoint_eq hc1]
    apply Rigidity.angle_eq_of_projection_eq hv
      (hunit _ (by constructor <;> linarith [hs.1, hs.2]))
      (envelope_mem_Icc (by positivity) hs)
    exact hl s hs
  · intro s hs
    rw [← envelope_midpoint_eq hc1]
    apply Rigidity.angle_eq_of_projection_eq hv
      (hunit _ (by constructor <;> linarith [hs.1, hs.2]))
      (envelope_mem_Icc (by positivity) hs)
    exact hr s hs

/-- 真实时间和任意正幅度上限的残差界，由曲线重参数化推出。 -/
theorem spherical_curve_frontier_time_lower_bound {n : ℝ → E} {T : ℝ} {Ω : ℝ≥0}
    (hΩ : 0 < Ω) (hL0 : Real.pi ≤ (Ω : ℝ) * T)
    (hL1 : (Ω : ℝ) * T ≤ 7 * Real.pi / 3)
    (hLip : LipschitzOnWith Ω n (Icc 0 T))
    (hunit : ∀ t ∈ Icc 0 T, ‖n t‖ = 1) (hend : n T = -n 0) :
    frontierResidual ((Ω : ℝ) * T) ≤ (Ω : ℝ) * ‖∫ t in 0..T, n t‖ := by
  have hΩr : 0 < (Ω : ℝ) := hΩ
  have hΩn : (Ω : ℝ) ≠ 0 := ne_of_gt hΩr
  let m : ℝ → E := fun s => n (s / (Ω : ℝ))
  have hmem {s : ℝ} (hs : s ∈ Icc 0 ((Ω : ℝ) * T)) : s / (Ω : ℝ) ∈ Icc 0 T := by
    exact ⟨div_nonneg hs.1 hΩr.le, (div_le_iff₀ hΩr).mpr (by simpa [mul_comm] using hs.2)⟩
  have hmLip : LipschitzOnWith 1 m (Icc 0 ((Ω : ℝ) * T)) := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro s hs t ht
    have h := (lipschitzOnWith_iff_norm_sub_le.mp hLip) (hmem hs) (hmem ht)
    change ‖n (s / (Ω : ℝ)) - n (t / (Ω : ℝ))‖ ≤ (1 : ℝ) * ‖s - t‖
    have hcancel : (Ω : ℝ) * (|s - t| / (Ω : ℝ)) = |s - t| := by field_simp
    simpa [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hΩr, hcancel] using h
  have hmUnit : ∀ s ∈ Icc 0 ((Ω : ℝ) * T), ‖m s‖ = 1 := fun s hs => hunit _ (hmem hs)
  have hmEnd : m ((Ω : ℝ) * T) = -m 0 := by simpa [m, hΩn] using hend
  have hmIntegral : (∫ s in 0..(Ω : ℝ) * T, m s) = (Ω : ℝ) • (∫ t in 0..T, n t) := by
    dsimp [m]
    rw [intervalIntegral.integral_comp_div _ hΩn]
    simp [hΩn]
  have h := spherical_curve_frontier_lower_bound hL0 hL1 hmLip.continuousOn hmUnit
    (sphericalSpeedBound_of_lipschitzOnWith hmUnit hmLip) hmEnd
  rw [hmIntegral, norm_smul, Real.norm_eq_abs, abs_of_pos hΩr] at h
  exact h

end RobustPiGate

#print axioms RobustPiGate.ac_spherical_curve_frontier_bounds
#print axioms RobustPiGate.spherical_curve_frontier_equality_angles
#print axioms RobustPiGate.spherical_curve_frontier_time_lower_bound
