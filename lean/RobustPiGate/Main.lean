import RobustPiGate.PhysicalMain
import RobustPiGate.EvolutionScaling
import RobustPiGate.SignSymmetry
import RobustPiGate.DimensionSharpness

noncomputable section
open Set Real MeasureTheory Filter
open scoped NNReal Matrix Matrix.Norms.L2Operator
namespace RobustPiGate
open Quantum

/-- 两种整体符号的已知脉冲均在原量子模型中真实达到最短时间。 -/
theorem both_short_signs_attain {Ω : ℝ≥0} (hΩ : 0 < Ω) :
    AdmissibleRobustPi Ω (7 * Real.pi / (3 * (Ω : ℝ)))
      (scaledShortControl Ω) (fun _ => 0) (scaledShortPropagator Ω) ∧
    AdmissibleRobustPi Ω (7 * Real.pi / (3 * (Ω : ℝ)))
      (negativeScaledShortControl Ω) (fun _ => 0) (negativeScaledShortPropagator Ω) := by
  constructor
  · obtain ⟨hp, hm, ha, he, _hu, hg, hr⟩ := scaledShortPropagator_certificate (Ω := (Ω : ℝ)) hΩ
    exact ⟨hp.le, hm.aemeasurable, measurable_const.aemeasurable, he,
      Filter.Eventually.of_forall (fun t _ => ha t), Or.inr hg, hr.deriv⟩
  · obtain ⟨hp, hm, ha, he, _hu, hg, hr⟩ := negativeScaledShortPropagator_certificate (Ω := (Ω : ℝ)) hΩ
    exact ⟨hp.le, hm.aemeasurable, measurable_const.aemeasurable, he,
      Filter.Eventually.of_forall (fun t _ => ha t), Or.inl hg, hr.deriv⟩

/-- 最短时间的每个原始可行控制都属于两个整体符号之一；符号不随时间变化。 -/
theorem optimal_control_classification {Ω : ℝ≥0} (hΩ : 0 < Ω)
    {ux uy : ℝ → ℝ} {U : ℝ → ℝ → QubitMatrix}
    (h : AdmissibleRobustPi Ω (7 * Real.pi / (3 * (Ω : ℝ))) ux uy U) :
    (∀ᵐ t, t ∈ Icc 0 (7 * Real.pi / (3 * (Ω : ℝ))) →
      ux t = (Ω : ℝ) * shortControl ((Ω : ℝ) * t) ∧ uy t = 0) ∨
    (∀ᵐ t, t ∈ Icc 0 (7 * Real.pi / (3 * (Ω : ℝ))) →
      ux t = -((Ω : ℝ) * shortControl ((Ω : ℝ) * t)) ∧ uy t = 0) := by
  have hamp : ∀ᵐ t, t ∈ Icc 0 (7 * Real.pi / (3 * (Ω : ℝ))) →
      (ux t) ^ 2 + (uy t) ^ 2 ≤ (Ω : ℝ) ^ 2 := by
    filter_upwards [h.amplitude] with t ht htI
    exact ht (by rwa [uIcc_of_le h.nonneg_duration])
  exact optimal_controls_unique_scaled (Ω := (Ω : ℝ)) hΩ h.evolution hamp h.gate h.robust

/-- 论文主定理：实际量子问题的精确最短时间及全部最优控制分类。 -/
theorem exact_time_and_all_minimizers {Ω : ℝ≥0} (hΩ : 0 < Ω) :
    IsLeast (robustPiDurations Ω) (7 * Real.pi / (3 * (Ω : ℝ))) ∧
    ∀ (ux uy : ℝ → ℝ) (U : ℝ → ℝ → QubitMatrix),
      AdmissibleRobustPi Ω (7 * Real.pi / (3 * (Ω : ℝ))) ux uy U →
      (∀ᵐ t, t ∈ Icc 0 (7 * Real.pi / (3 * (Ω : ℝ))) →
        ux t = (Ω : ℝ) * shortControl ((Ω : ℝ) * t) ∧ uy t = 0) ∨
      (∀ᵐ t, t ∈ Icc 0 (7 * Real.pi / (3 * (Ω : ℝ))) →
        ux t = -((Ω : ℝ) * shortControl ((Ω : ℝ) * t)) ∧ uy t = 0) :=
  ⟨robust_pi_minimum hΩ, fun _ _ _ h => optimal_control_classification hΩ h⟩

end RobustPiGate

#print axioms RobustPiGate.exact_time_and_all_minimizers
#print axioms RobustPiGate.both_short_signs_attain
