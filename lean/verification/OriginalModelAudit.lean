import RobustPiGate.BlochBridge

open MeasureTheory Set
open scoped Matrix Matrix.Norms.L2Operator NNReal
open RobustPiGate.Quantum

-- 不经物理可行性定义，直接用原问题的全部矩阵方程前提调用下界。
theorem audit_original_model_lower_bound
    {ux uy : ℝ → ℝ} {U : ℝ → ℝ → QubitMatrix} {Ω T : ℝ}
    (hΩ : 0 < Ω) (hT : 0 < T)
    (hAC : ∀ δ, AbsolutelyContinuousOnInterval (U δ) 0 T)
    (hinit : ∀ δ, U δ 0 = 1)
    (hODE : ∀ δ, ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt (U δ)
      (((-Complex.I / 2) • ((ux t : ℂ) • sigmaX + (uy t : ℂ) • sigmaY +
        (δ : ℂ) • sigmaZ)) * U δ t) t)
    (hamp : ∀ᵐ t, t ∈ Icc 0 T → (ux t) ^ 2 + (uy t) ^ 2 ≤ Ω ^ 2)
    (hgate : U 0 T = rx Real.pi ∨ U 0 T = -rx Real.pi)
    (hrobust : HasDerivAt (fun δ => U δ T) 0 0) :
    7 * Real.pi / (3 * Ω) ≤ T := by
  let Ωnn : ℝ≥0 := ⟨Ω, hΩ.le⟩
  have hU : RobustPiGate.Dynamics.IsQubitEvolution ux uy U T := by
    intro δ
    refine ⟨hAC δ, hinit δ, ?_⟩
    filter_upwards [hODE δ] with t ht htI
    rw [uIcc_of_le hT.le] at htI
    simpa only [RobustPiGate.Dynamics.qubit_generator_model] using ht htI
  exact actual_gate_time_lower_bound (Ω := Ωnn) hΩ hT hU
    (by
      change ∀ᵐ t, t ∈ uIcc 0 T → (ux t) ^ 2 + (uy t) ^ 2 ≤ Ω ^ 2
      simpa only [uIcc_of_le hT.le] using hamp) hgate hrobust.deriv

#print axioms audit_original_model_lower_bound
#check audit_original_model_lower_bound
