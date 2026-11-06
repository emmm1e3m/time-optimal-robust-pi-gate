import RobustPiGate.FrontierPhysical
import RobustPiGate.FrontierOptimalControls
import RobustPiGate.FrontierDimension
import RobustPiGate.FrontierBudgetEndpoints

noncomputable section
set_option maxHeartbeats 200000
open Set Real MeasureTheory Filter InnerProductGeometry
open scoped NNReal Matrix Matrix.Norms.L2Operator
namespace RobustPiGate
open Quantum

/-- 反极单位曲线在任意正速度上限下的名义长度界。 -/
theorem antipodal_curve_time_bound {Ω : ℝ≥0} {T : ℝ} {n : ℝ → Vec3}
    (hΩ : 0 < Ω) (hT : 0 ≤ T)
    (hunit : ∀ t ∈ Icc 0 T, ‖n t‖ = 1)
    (hLip : LipschitzOnWith Ω n (Icc 0 T)) (hend : n T = -n 0) :
    Real.pi ≤ (Ω : ℝ) * T := by
  have hΩr : 0 < (Ω : ℝ) := hΩ
  have hΩn : (Ω : ℝ) ≠ 0 := ne_of_gt hΩr
  have hL : 0 ≤ (Ω : ℝ) * T := mul_nonneg Ω.coe_nonneg hT
  let m : ℝ → Vec3 := fun s => n (s / (Ω : ℝ))
  have hmLip : LipschitzOnWith 1 m (Icc 0 ((Ω : ℝ) * T)) :=
    noise_lipschitz_rescale (n := n) (T := T) hΩr hLip
  have hmUnit : ∀ s ∈ Icc 0 ((Ω : ℝ) * T), ‖m s‖ = 1 := by
    intro s hs
    exact hunit (s / (Ω : ℝ)) ⟨div_nonneg hs.1 Ω.coe_nonneg,
      (div_le_iff₀ hΩr).mpr (mul_comm (Ω : ℝ) T ▸ hs.2)⟩
  have hmEnd : m ((Ω : ℝ) * T) = -m 0 := by
    dsimp only [m]
    rw [zero_div, mul_div_cancel_left₀ T hΩn]
    exact hend
  have hm0 : m 0 ≠ 0 := by
    intro hz
    have hh := hmUnit 0 ⟨le_rfl, hL⟩
    rw [hz, norm_zero] at hh
    exact zero_ne_one hh
  have hspeed : SphericalSpeedBound m 0 ((Ω : ℝ) * T) :=
    sphericalSpeedBound_of_lipschitzOnWith (n := m) hmUnit hmLip
  have hs : angle (m 0) (m ((Ω : ℝ) * T)) ≤ |(Ω : ℝ) * T - 0| :=
    hspeed 0 ⟨le_rfl, hL⟩ ((Ω : ℝ) * T) ⟨hL, le_rfl⟩
  rw [hmEnd, angle_self_neg_of_nonzero hm0, sub_zero, abs_of_nonneg hL] at hs
  exact hs

/-- 原始完整门条件已经排除所有短于 π/Ω 的名义门。 -/
theorem AdmissiblePi.nominal_time_lower_bound {Ω : ℝ≥0} {T : ℝ}
    {ux uy : ℝ → ℝ} {U : ℝ → ℝ → QubitMatrix}
    (hΩ : 0 < Ω) (h : AdmissiblePi Ω T ux uy U) : Real.pi ≤ (Ω : ℝ) * T := by
  obtain ⟨hunit, hLip, hend⟩ := h.noise_curve
  rw [uIcc_of_le h.nonneg_duration] at hunit hLip
  exact antipodal_curve_time_bound hΩ h.nonneg_duration hunit hLip hend

theorem negativeScaledFrontier_admissible {Ω : ℝ≥0} {a : ℝ}
    (ha : 0 ≤ a) (hΩ : 0 < Ω) :
    AdmissiblePi Ω (scaledFrontierTime a Ω) (negativeScaledFrontierControl a Ω)
      (fun _ => 0) (negativeScaledFrontierPropagator a Ω) := by
  obtain ⟨hp, hm, ha, he, _hu, hg, _hr⟩ := negativeScaledFrontierPropagator_certificate ha hΩ
  exact ⟨hp.le, hm.aemeasurable, measurable_const.aemeasurable, he,
    Filter.Eventually.of_forall (fun t _ => ha t), Or.inl hg⟩

theorem negativeScaledFrontier_sensitivity {Ω : ℝ≥0} {a : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ Real.pi / 3) (hΩ : 0 < Ω) :
    detuningSensitivity (negativeScaledFrontierPropagator a Ω) Ω (scaledFrontierTime a Ω) =
      frontierSensitivity (frontierDuration a) := by
  rw [detuningSensitivity_eq (negativeScaledFrontier_admissible ha hΩ).evolution]
  have hn := negativeScaledFrontierPropagator_noise_integral_norm ha ha' (show 0 < (Ω : ℝ) from hΩ)
  have he := congrArg (fun r : ℝ => (Ω : ℝ) ^ 2 * r ^ 2 / 6) hn
  change (Ω : ℝ) ^ 2 * ‖∫ t in 0..scaledFrontierTime a Ω,
    noiseVec (negativeScaledFrontierPropagator a Ω 0 t)‖ ^ 2 / 6 = _
  rw [he]
  unfold frontierSensitivity frontierResidual frontierDuration
  rw [show (4 * a + Real.pi - Real.pi) / 4 = a by ring]
  have hΩn : (Ω : ℝ) ≠ 0 := ne_of_gt hΩ
  field_simp

/-- 两种整体符号都由真实带失谐演化达到完整边界，包括零端段。 -/
theorem both_frontier_signs_attain {Ω : ℝ≥0} {a : ℝ}
    (hΩ : 0 < Ω) (ha : a ∈ Icc 0 (Real.pi / 3)) :
    (AdmissiblePi Ω (scaledFrontierTime a Ω) (scaledFrontierControl a Ω) (fun _ => 0)
      (scaledFrontierPropagator a Ω) ∧
      detuningSensitivity (scaledFrontierPropagator a Ω) Ω (scaledFrontierTime a Ω) =
        frontierSensitivity (frontierDuration a)) ∧
    (AdmissiblePi Ω (scaledFrontierTime a Ω) (negativeScaledFrontierControl a Ω) (fun _ => 0)
      (negativeScaledFrontierPropagator a Ω) ∧
      detuningSensitivity (negativeScaledFrontierPropagator a Ω) Ω (scaledFrontierTime a Ω) =
        frontierSensitivity (frontierDuration a)) :=
  ⟨⟨scaledFrontier_admissible ha.1 hΩ, scaledFrontier_sensitivity ha.1 ha.2 hΩ⟩,
    ⟨negativeScaledFrontier_admissible ha.1 hΩ, negativeScaledFrontier_sensitivity ha.1 ha.2 hΩ⟩⟩

/-- 真实保真度系数达到最小值时，控制整段固定为两种符号之一。 -/
theorem frontier_control_classification {Ω : ℝ≥0} {T : ℝ}
    {ux uy : ℝ → ℝ} {U : ℝ → ℝ → QubitMatrix}
    (hΩ : 0 < Ω) (hL : (Ω : ℝ) * T ∈ Icc Real.pi (7 * Real.pi / 3))
    (h : AdmissiblePi Ω T ux uy U)
    (heq : detuningSensitivity U Ω T = frontierSensitivity ((Ω : ℝ) * T)) :
    (∀ᵐ t, t ∈ Icc 0 T →
      ux t = (Ω : ℝ) * frontierControl (((Ω : ℝ) * T - Real.pi) / 4) ((Ω : ℝ) * t) ∧ uy t = 0) ∨
    (∀ᵐ t, t ∈ Icc 0 T →
      ux t = -((Ω : ℝ) * frontierControl (((Ω : ℝ) * T - Real.pi) / 4) ((Ω : ℝ) * t)) ∧ uy t = 0) := by
  apply frontier_optimal_controls_unique_scaled hΩ hL h.evolution
    (by simpa [uIcc_of_le h.nonneg_duration] using h.amplitude) h.gate
  exact (h.sensitivity_eq_frontier_iff hL.1 hL.2).mp heq

/-- 完整物理前沿与全部达到者的统一出口。 -/
theorem exact_frontier_and_all_minimizers {Ω : ℝ≥0} {T : ℝ}
    (hΩ : 0 < Ω) (hL : (Ω : ℝ) * T ∈ Icc Real.pi (7 * Real.pi / 3)) :
    IsLeast (piSensitivities Ω T) (frontierSensitivity ((Ω : ℝ) * T)) ∧
    ∀ (ux uy : ℝ → ℝ) (U : ℝ → ℝ → QubitMatrix), AdmissiblePi Ω T ux uy U →
      detuningSensitivity U Ω T = frontierSensitivity ((Ω : ℝ) * T) →
      (∀ᵐ t, t ∈ Icc 0 T →
        ux t = (Ω : ℝ) * frontierControl (((Ω : ℝ) * T - Real.pi) / 4) ((Ω : ℝ) * t) ∧ uy t = 0) ∨
      (∀ᵐ t, t ∈ Icc 0 T →
        ux t = -((Ω : ℝ) * frontierControl (((Ω : ℝ) * T - Real.pi) / 4) ((Ω : ℝ) * t)) ∧ uy t = 0) :=
  ⟨pi_sensitivity_minimum hΩ hL.1 hL.2, fun _ _ _ h heq => frontier_control_classification hΩ hL h heq⟩

/-- 定义实际控制类上的前导预算值集合，χ仍是原保真度极限。 -/
def leadingPiBudgets (Ω : ℝ≥0) (T v κ : ℝ) : Set ℝ :=
  (fun χ => v * χ + κ * ((Ω : ℝ) * T)) '' piSensitivities Ω T

theorem leading_budget_minimum {Ω : ℝ≥0} {T v κ : ℝ}
    (hΩ : 0 < Ω) (hL : (Ω : ℝ) * T ∈ Icc Real.pi (7 * Real.pi / 3)) (hv : 0 ≤ v) :
    IsLeast (leadingPiBudgets Ω T v κ)
      (v * frontierSensitivity ((Ω : ℝ) * T) + κ * ((Ω : ℝ) * T)) := by
  have hm := pi_sensitivity_minimum hΩ hL.1 hL.2
  refine ⟨⟨_, hm.1, rfl⟩, ?_⟩
  rintro e ⟨χ, hχ, rfl⟩
  exact add_le_add (mul_le_mul_of_nonneg_left (hm.2 hχ) hv) le_rfl

end RobustPiGate

#print axioms RobustPiGate.exact_frontier_and_all_minimizers
#print axioms RobustPiGate.both_frontier_signs_attain
#print axioms RobustPiGate.AdmissiblePi.nominal_time_lower_bound
#print axioms RobustPiGate.leading_budget_minimum
