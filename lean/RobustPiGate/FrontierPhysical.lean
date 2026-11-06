import RobustPiGate.FrontierFidelity
import RobustPiGate.FrontierBounds
import RobustPiGate.FrontierEvolution

noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology NNReal Matrix Matrix.Norms.L2Operator
namespace RobustPiGate
open Quantum RobustPiGate.Dynamics

/-- 原完整量子控制类在每个时长的真实敏感度下界。 -/
theorem AdmissiblePi.sensitivity_lower_bound {Ω : ℝ≥0} {T : ℝ}
    {ux uy : ℝ → ℝ} {U : ℝ → ℝ → QubitMatrix}
    (hΩ : 0 < Ω) (hL0 : Real.pi ≤ (Ω : ℝ) * T)
    (hL1 : (Ω : ℝ) * T ≤ 7 * Real.pi / 3) (h : AdmissiblePi Ω T ux uy U) :
    frontierSensitivity ((Ω : ℝ) * T) ≤ detuningSensitivity U Ω T := by
  obtain ⟨hunit, hLip, hend⟩ := h.noise_curve
  have hb := spherical_curve_frontier_time_lower_bound hΩ hL0 hL1
    (by simpa [uIcc_of_le h.nonneg_duration] using hLip)
    (by simpa [uIcc_of_le h.nonneg_duration] using hunit) hend
  have hg := frontierResidual_nonneg hL0 (by dsimp [criticalHalf]; linarith)
  rw [detuningSensitivity_eq h.evolution, frontierSensitivity, ← mul_pow]
  exact div_le_div_of_nonneg_right
    ((sq_le_sq₀ hg (mul_nonneg Ω.coe_nonneg (norm_nonneg _))).mpr hb) (by norm_num)

/-- 真实敏感度取等与实际噪声曲线的残差取等完全等价。 -/
theorem AdmissiblePi.sensitivity_eq_frontier_iff {Ω : ℝ≥0} {T : ℝ}
    {ux uy : ℝ → ℝ} {U : ℝ → ℝ → QubitMatrix}
    (hL0 : Real.pi ≤ (Ω : ℝ) * T) (hL1 : (Ω : ℝ) * T ≤ 7 * Real.pi / 3)
    (h : AdmissiblePi Ω T ux uy U) :
    detuningSensitivity U Ω T = frontierSensitivity ((Ω : ℝ) * T) ↔
      (Ω : ℝ) * ‖∫ t in 0..T, noiseVec (U 0 t)‖ = frontierResidual ((Ω : ℝ) * T) := by
  have hg := frontierResidual_nonneg hL0 (by dsimp [criticalHalf]; linarith)
  have hr := mul_nonneg Ω.coe_nonneg (norm_nonneg (∫ t in 0..T, noiseVec (U 0 t)))
  rw [detuningSensitivity_eq h.evolution, frontierSensitivity, ← mul_pow]
  constructor
  · intro he
    nlinarith
  · intro he
    rw [he]

/-- 三段族属于没有预设鲁棒性的完整物理可行类。 -/
theorem scaledFrontier_admissible {Ω : ℝ≥0} {a : ℝ} (ha : 0 ≤ a) (hΩ : 0 < Ω) :
    AdmissiblePi Ω (scaledFrontierTime a Ω) (scaledFrontierControl a Ω) (fun _ => 0)
      (scaledFrontierPropagator a Ω) := by
  obtain ⟨hpos, hm, hamp, he, _hu, hg, _hr⟩ := scaledFrontierPropagator_certificate ha hΩ
  exact {
    nonneg_duration := hpos.le
    measurable_x := hm.aemeasurable
    measurable_y := measurable_const.aemeasurable
    evolution := he
    amplitude := Filter.Eventually.of_forall (fun t _ => hamp t)
    gate := Or.inr hg
  }

/-- 真实保真度极限在三段族上精确达到解析边界。 -/
theorem scaledFrontier_sensitivity {Ω : ℝ≥0} {a : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ Real.pi / 3) (hΩ : 0 < Ω) :
    detuningSensitivity (scaledFrontierPropagator a Ω) Ω (scaledFrontierTime a Ω) =
      frontierSensitivity (frontierDuration a) := by
  rw [detuningSensitivity_eq (scaledFrontier_admissible ha hΩ).evolution]
  calc
    _ = (Ω : ℝ) ^ 2 * ((4 * Real.cos a - 2) / Ω) ^ 2 / 6 :=
      congrArg (fun x : ℝ => (Ω : ℝ) ^ 2 * x ^ 2 / 6)
        (scaledFrontierPropagator_noise_integral_norm ha ha' hΩ)
    _ = _ := by
      rw [frontierSensitivity, frontierResidual]
      rw [show (frontierDuration a - Real.pi) / 4 = a by unfold frontierDuration; ring]
      have hΩn : (Ω : ℝ) ≠ 0 := ne_of_gt hΩ
      field_simp [hΩn]

/-- 每个前沿时长均存在实际控制达到相应敏感度。 -/
theorem frontierSensitivity_mem_piSensitivities {Ω : ℝ≥0} {T : ℝ}
    (hΩ : 0 < Ω) (hL0 : Real.pi ≤ (Ω : ℝ) * T)
    (hL1 : (Ω : ℝ) * T ≤ 7 * Real.pi / 3) :
    frontierSensitivity ((Ω : ℝ) * T) ∈ piSensitivities Ω T := by
  let a := ((Ω : ℝ) * T - Real.pi) / 4
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have ha' : a ≤ Real.pi / 3 := by dsimp [a]; linarith
  have hΩn : (Ω : ℝ) ≠ 0 := ne_of_gt hΩ
  have hduration : frontierDuration a = (Ω : ℝ) * T := by
    dsimp [a, frontierDuration]
    ring
  have ht : scaledFrontierTime a Ω = T := by
    rw [scaledFrontierTime, hduration]
    exact mul_div_cancel_left₀ T hΩn
  have hmem : frontierSensitivity (frontierDuration a) ∈
      piSensitivities Ω (scaledFrontierTime a Ω) := by
    exact ⟨scaledFrontierControl a Ω, (fun _ => 0), scaledFrontierPropagator a Ω,
      scaledFrontier_admissible ha hΩ, (scaledFrontier_sensitivity ha ha' hΩ).symm⟩
  simpa only [ht, hduration] using hmem

/-- PRA前沿主定理：原保真度敏感度集合具有给定最小元。 -/
theorem pi_sensitivity_minimum {Ω : ℝ≥0} {T : ℝ}
    (hΩ : 0 < Ω) (hL0 : Real.pi ≤ (Ω : ℝ) * T)
    (hL1 : (Ω : ℝ) * T ≤ 7 * Real.pi / 3) :
    IsLeast (piSensitivities Ω T) (frontierSensitivity ((Ω : ℝ) * T)) := by
  refine ⟨frontierSensitivity_mem_piSensitivities hΩ hL0 hL1, ?_⟩
  intro χ hχ
  obtain ⟨ux, uy, U, h, rfl⟩ := hχ
  exact h.sensitivity_lower_bound hΩ hL0 hL1

/-- 与论文下确界记号一致的完整控制类精确公式。 -/
theorem pi_sensitivity_infimum {Ω : ℝ≥0} {T : ℝ}
    (hΩ : 0 < Ω) (hL0 : Real.pi ≤ (Ω : ℝ) * T)
    (hL1 : (Ω : ℝ) * T ≤ 7 * Real.pi / 3) :
    sInf (piSensitivities Ω T) = frontierSensitivity ((Ω : ℝ) * T) :=
  (pi_sensitivity_minimum hΩ hL0 hL1).csInf_eq

end RobustPiGate

#print axioms RobustPiGate.AdmissiblePi.sensitivity_lower_bound
#print axioms RobustPiGate.pi_sensitivity_minimum
#print axioms RobustPiGate.pi_sensitivity_infimum
