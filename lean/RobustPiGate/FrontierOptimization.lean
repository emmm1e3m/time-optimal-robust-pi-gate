import RobustPiGate.FrontierMain

open MeasureTheory Set Filter
open scoped Topology NNReal Interval Matrix Matrix.Norms.L2Operator
namespace RobustPiGate
open RobustPiGate RobustPiGate.Quantum RobustPiGate.Dynamics

-- 真实静态保真度系数非负，用于排除更长时长。
theorem actual_sensitivity_nonneg
    {ux uy : ℝ → ℝ} {U : ℝ → ℝ → RobustPiGate.Quantum.QubitMatrix} {T Ω : ℝ}
    (hU : RobustPiGate.Dynamics.IsQubitEvolution ux uy U T) :
    0 ≤ RobustPiGate.Quantum.detuningSensitivity U Ω T := by
  rw [RobustPiGate.Quantum.detuningSensitivity_eq hU]
  positivity

-- 任意物理时长、任意原控制；使用真实 χ 非负排除较长门。
theorem global_budget_control_comparison
    {Ω : ℝ≥0} {v κ m T : ℝ} {ux uy : ℝ → ℝ}
    {U : ℝ → ℝ → QubitMatrix}
    (hΩ : 0 < Ω) (hv : 0 < v) (hκ : 0 < κ)
    (hm : IsMinOn (frontierBudget (κ/v)) (Icc Real.pi budgetEndpoint) m)
    (hU : AdmissiblePi Ω T ux uy U) :
    v * frontierSensitivity m + κ*m ≤
      v * detuningSensitivity U Ω T + κ*((Ω : ℝ)*T) := by
  have he (x : ℝ) : v * frontierBudget (κ/v) x = v * frontierSensitivity x + κ*x := by
    unfold frontierBudget
    field_simp [ne_of_gt hv]
  by_cases hL : (Ω : ℝ)*T ≤ budgetEndpoint
  · have hlo := AdmissiblePi.nominal_time_lower_bound hΩ hU
    have hc := mul_le_mul_of_nonneg_left (hm ⟨hlo, hL⟩) hv.le
    simp only [he] at hc
    have hs := hU.sensitivity_lower_bound hΩ hlo hL
    exact hc.trans (add_le_add (mul_le_mul_of_nonneg_left hs hv.le) le_rfl)
  · have hc := mul_le_mul_of_nonneg_left
      (hm (show budgetEndpoint ∈ Icc Real.pi budgetEndpoint from
        ⟨budgetEndpoint_gt_pi.le, le_rfl⟩)) hv.le
    simp only [he, sensitivity_at_budgetEndpoint, mul_zero, zero_add] at hc
    have hs := budget_longer_dominated hκ
      (mul_nonneg hv.le (actual_sensitivity_nonneg (Ω := (Ω : ℝ)) hU.evolution)) (lt_of_not_ge hL)
    exact hc.trans hs.le

-- 标量候选时长可由原完整门控制真实达到；配合上一结论得到全时长最优。
theorem scalar_budget_attained_by_original_control
    {Ω : ℝ≥0} {v κ m : ℝ}
    (hΩ : 0 < Ω) (hm : m ∈ Icc Real.pi budgetEndpoint) :
    ∃ T ux uy U, AdmissiblePi Ω T ux uy U ∧ (Ω : ℝ)*T = m ∧
      v * detuningSensitivity U Ω T + κ*((Ω : ℝ)*T) =
        v * frontierSensitivity m + κ*m := by
  have hΩr : 0 < (Ω : ℝ) := hΩ
  have hnorm : (Ω : ℝ)*(m/(Ω : ℝ)) = m := by
    field_simp [hΩr.ne']
  have hm' : (Ω : ℝ)*(m/(Ω : ℝ)) ∈ Icc Real.pi (7*Real.pi/3) := by
    simpa only [hnorm, budgetEndpoint] using hm
  have hs := pi_sensitivity_minimum hΩ hm'.1 hm'.2
  rw [hnorm] at hs
  obtain ⟨ux, uy, U, hU, he⟩ := hs.1
  refine ⟨m/(Ω : ℝ), ux, uy, U, hU, hnorm, ?_⟩
  rw [hnorm, ← he]


/-- 全部物理时长和全部原控制中，前导预算有实际达到的全局最小门。 -/
theorem global_leading_budget_attained {Ω : ℝ≥0} {v κ : ℝ}
    (hΩ : 0 < Ω) (hv : 0 < v) (hκ : 0 < κ) :
    ∃ T ux uy U, AdmissiblePi Ω T ux uy U ∧
      ∀ T' ux' uy' U', AdmissiblePi Ω T' ux' uy' U' →
        v * detuningSensitivity U Ω T + κ * ((Ω : ℝ) * T) ≤
          v * detuningSensitivity U' Ω T' + κ * ((Ω : ℝ) * T') := by
  obtain ⟨m, hm, hmin⟩ := budget_exists_global_min (κ / v)
  obtain ⟨T, ux, uy, U, hU, _hscale, hcost⟩ :=
    scalar_budget_attained_by_original_control (v := v) (κ := κ) hΩ hm
  refine ⟨T, ux, uy, U, hU, ?_⟩
  intro T' ux' uy' U' hU'
  rw [hcost]
  exact global_budget_control_comparison hΩ hv hκ hmin hU'

#print axioms global_leading_budget_attained
#print axioms global_budget_control_comparison
#print axioms scalar_budget_attained_by_original_control
end RobustPiGate
