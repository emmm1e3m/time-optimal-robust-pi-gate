import RobustPiGate.BlochBridge
import RobustPiGate.ShortEvolution

noncomputable section
open Set Real MeasureTheory Filter
open scoped NNReal Matrix Matrix.Norms.L2Operator
namespace RobustPiGate
open Quantum Dynamics

/-- 原问题的可行完整量子门。控制仅要求在演化区间内几乎处处可测。 -/
structure AdmissibleRobustPi (Ω : ℝ≥0) (T : ℝ)
    (ux uy : ℝ → ℝ) (U : ℝ → ℝ → QubitMatrix) : Prop where
  nonneg_duration : 0 ≤ T
  measurable_x : AEMeasurable ux (volume.restrict (uIcc 0 T))
  measurable_y : AEMeasurable uy (volume.restrict (uIcc 0 T))
  evolution : IsQubitEvolution ux uy U T
  amplitude : ∀ᵐ t, t ∈ uIcc 0 T → (ux t) ^ 2 + (uy t) ^ 2 ≤ (Ω : ℝ) ^ 2
  gate : U 0 T = rx Real.pi ∨ U 0 T = -rx Real.pi
  robust : deriv (fun δ => U δ T) 0 = 0

/-- 真正可行时长；演化族与两个控制均在存在量词内。 -/
def robustPiDurations (Ω : ℝ≥0) : Set ℝ :=
  {T | ∃ ux uy U, AdmissibleRobustPi Ω T ux uy U}

/-- 零时间的初始恒等门不可能是目标 π 门。 -/
theorem AdmissibleRobustPi.duration_pos {Ω T ux uy U}
    (h : AdmissibleRobustPi Ω T ux uy U) : 0 < T := by
  by_contra hnot
  have hT : T = 0 := le_antisymm (le_of_not_gt hnot) h.nonneg_duration
  have hi := (qubit_nominal_solution h.evolution).initial
  have hg := h.gate
  rw [hT, hi] at hg
  rcases hg with hg | hg
  · have he := congrArg (fun M : QubitMatrix => M 0 0) hg
    simpa [rx] using he
  · have he := congrArg (fun M : QubitMatrix => M 0 0) hg
    simpa [rx] using he

/-- 对可行门，原失谐参数导数确实存在；不依赖deriv的默认值。 -/
theorem AdmissibleRobustPi.robust_hasDerivAt {Ω T ux uy U}
    (h : AdmissibleRobustPi Ω T ux uy U) :
    HasDerivAt (fun δ => U δ T) 0 0 := by
  have hd := qubit_parameter_hasDerivAt h.evolution
  rw [← hd.deriv, h.robust] at hd
  exact hd

/-- 原物理可行控制类的全局时间下界。 -/
theorem AdmissibleRobustPi.time_lower_bound {Ω T ux uy U}
    (hΩ : 0 < Ω) (h : AdmissibleRobustPi Ω T ux uy U) :
    7 * Real.pi / (3 * (Ω : ℝ)) ≤ T :=
  Quantum.actual_gate_time_lower_bound hΩ h.duration_pos h.evolution h.amplitude h.gate h.robust

/-- 显式构造的全部失谐演化族证明最优时间可达。 -/
theorem short_time_mem_robustPiDurations {Ω : ℝ≥0} (hΩ : 0 < Ω) :
    7 * Real.pi / (3 * (Ω : ℝ)) ∈ robustPiDurations Ω := by
  obtain ⟨hpos, hm, ha, he, _hu, hg, hr⟩ := scaledShortPropagator_certificate (Ω := (Ω : ℝ)) hΩ
  refine ⟨scaledShortControl Ω, (fun _ => 0), scaledShortPropagator Ω, ?_⟩
  exact {
    nonneg_duration := hpos.le
    measurable_x := hm.aemeasurable
    measurable_y := measurable_const.aemeasurable
    evolution := he
    amplitude := Filter.Eventually.of_forall (fun t _ => ha t)
    gate := Or.inr hg
    robust := hr.deriv
  }

/-- PRA主定理的最小元形式：完整门的一阶鲁棒精确最短时间。 -/
theorem robust_pi_minimum {Ω : ℝ≥0} (hΩ : 0 < Ω) :
    IsLeast (robustPiDurations Ω) (7 * Real.pi / (3 * (Ω : ℝ))) := by
  refine ⟨short_time_mem_robustPiDurations hΩ, ?_⟩
  intro T hT
  obtain ⟨ux, uy, U, h⟩ := hT
  exact h.time_lower_bound hΩ

/-- 与论文下确界定义完全相同的精确时间公式。 -/
theorem robust_pi_infimum {Ω : ℝ≥0} (hΩ : 0 < Ω) :
    sInf (robustPiDurations Ω) = 7 * Real.pi / (3 * (Ω : ℝ)) :=
  (robust_pi_minimum hΩ).csInf_eq

end RobustPiGate

#print axioms RobustPiGate.robust_pi_minimum
#print axioms RobustPiGate.robust_pi_infimum
