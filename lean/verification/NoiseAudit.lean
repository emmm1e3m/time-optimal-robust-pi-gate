import RobustPiGate.FrontierDyson
import RobustPiGate.FrontierAverage
import RobustPiGate.FrontierSphere
import RobustPiGate.FrontierBudget
import RobustPiGate.FrontierFidelity
import RobustPiGate.FrontierNoise
import RobustPiGate.FrontierBlochUnitary
import RobustPiGate.FrontierContinuity
import RobustPiGate.FrontierVariance
import RobustPiGate.FrontierFidelitySymmetry
import RobustPiGate.FrontierCombinedNoise
import RobustPiGate.FrontierOptimization

open MeasureTheory Set Filter
open scoped Topology NNReal Interval Matrix Matrix.Norms.L2Operator

namespace Review070

open RobustPiGate RobustPiGate.Quantum RobustPiGate.Dynamics RobustPiGate.FrontierNoise

-- 直接核对正文的物理单位：真实方差与原保真度极限恢复 s²χ+κL。
theorem combined_physical_budget
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {ux uy : ℝ → ℝ} {γ₁ γφ T Ω : ℝ}
    {U : ℝ → ℝ → QubitMatrix} {V : ℝ → ℝ → ℝ → BlochMatrix}
    (hΩ : 0 < Ω) (hT : 0 ≤ T) (h₁ : 0 ≤ γ₁) (hφ : 0 ≤ γφ)
    (hU : IsQubitEvolution ux uy U T)
    (hV : IsNoisyBlochEvolution ux uy γ₁ γφ V T)
    (hs : FrontierAverage.SymmetricLaw μ)
    (h4 : Integrable (fun x : ℝ => x^4) μ)
    (c : ℝ → ℝ → BlochVector) :
    (fun η => (∫ x, 1 - lindbladGateFidelity (U 0 T) (V η x T) (c η x) ∂μ) -
      (ProbabilityTheory.variance (fun x : ℝ => η*x) μ / Ω^2 * detuningSensitivity U Ω T +
        ((η^2*γ₁ + η^2*γφ) / (3*Ω)) * (Ω*T)))
      =O[𝓝 (0 : ℝ)] (fun η => η^4) := by
  have he (η : ℝ) :
      ProbabilityTheory.variance (fun x : ℝ => η*x) μ / Ω^2 * detuningSensitivity U Ω T +
        ((η^2*γ₁ + η^2*γφ) / (3*Ω)) * (Ω*T) =
      η^2 * ((‖∫ t in 0..T, noiseVec (U 0 t)‖^2 / 6) *
        (∫ x : ℝ, x^2 ∂μ) + (γ₁ + γφ) * T / 3) := by
    rw [FrontierAverage.variance_scaled_of_symmetric_fourth hs h4,
      detuningSensitivity_eq hU]
    field_simp [ne_of_gt hΩ]
    <;> ring
  simp_rw [he]
  exact averaged_lindblad_infidelity hT h₁ hφ hU hV hs h4 c

-- 仿射平移的零初值确保真实 Lindblad 轨迹确实从所指定输入态出发。
theorem actual_lindblad_from_input
    {ux uy : ℝ → ℝ} {δ Γ₁ Γφ T : ℝ}
    {V : ℝ → BlochMatrix} {c : ℝ → BlochVector}
    (hV : IsACSolution (fun t => rotationGenerator (ux t) (uy t) δ + damping Γ₁ Γφ) V T)
    (hc : AbsolutelyContinuousOnInterval c 0 T) (hc0 : c 0 = 0)
    (hdc : ∀ᵐ t, t ∈ uIcc 0 T →
      HasDerivAt c (blochRHS (ux t) (uy t) δ Γ₁ Γφ (c t)) t)
    (q : BlochVector) :
    density ((V 0).mulVec q + c 0) = density q ∧
    AbsolutelyContinuousOnInterval (fun t => density ((V t).mulVec q + c t)) 0 T ∧
      ∀ᵐ t, t ∈ uIcc 0 T →
        HasDerivAt (fun s => density ((V s).mulVec q + c s))
          (lindblad (ux t) (uy t) δ Γ₁ Γφ (density ((V t).mulVec q + c t))) t := by
  constructor
  · simp [hV.initial, hc0]
  · exact affine_bloch_is_lindblad hV hc hdc q

-- 审计量词为任意全局最小点，不是选定驻点分支。
example {lam L : ℝ} (hlam : 0 < lam) (hsmall : 6 * Real.pi ^ 2 * lam < 1)
    (hL : L ∈ Icc Real.pi RobustPiGate.budgetEndpoint)
    (hm : IsMinOn (RobustPiGate.frontierBudget lam)
      (Icc Real.pi RobustPiGate.budgetEndpoint) L) :
    |RobustPiGate.budgetEndpoint - L - 4 * lam| ≤ 24 * Real.pi ^ 4 * lam ^ 2 :=
  RobustPiGate.budget_global_shortening_asymptotic_bound hlam hsmall hL hm

#print axioms RobustPiGate.FrontierDyson.norm_dyson_remainder_le
#print axioms RobustPiGate.FrontierDyson.norm_mixed_remainder_le
#print axioms RobustPiGate.FrontierDyson.functional_mixed_remainder_le
#print axioms RobustPiGate.FrontierAverage.averaged_polynomial_expansion_isBigO
#print axioms RobustPiGate.FrontierSphere.sphereAverage_fidelity
#print axioms RobustPiGate.budget_global_min_iff_candidates
#print axioms RobustPiGate.budget_global_shortening_isBigO
#print axioms actual_sensitivity_nonneg
#print axioms RobustPiGate.FrontierNoise.lindblad_ode_iff_bloch_ode
#print axioms RobustPiGate.FrontierNoise.affine_bloch_is_lindblad
#print axioms RobustPiGate.FrontierNoise.bloch_solution_contraction
#print axioms RobustPiGate.FrontierNoise.weak_dissipation_remainder
#print axioms RobustPiGate.Quantum.blochStaticDysonCoefficient_scaled
#print axioms RobustPiGate.FrontierContinuity.continuous_parameter_solution
#print axioms RobustPiGate.FrontierAverage.variance_scaled_of_symmetric_fourth
#print axioms RobustPiGate.Quantum.single_axis_avgGateFidelity_even
#print axioms RobustPiGate.FrontierNoise.averaged_noise_expansion
#print axioms RobustPiGate.FrontierNoise.averaged_lindblad_infidelity
#print axioms RobustPiGate.FrontierNoise.lindblad_weak_noise_budget
#print axioms RobustPiGate.FrontierNoise.weak_dissipation_rate_remainder
#print axioms RobustPiGate.leading_budget_minimum
#print axioms RobustPiGate.budget_rectangular_global_min_of_large_ratio
#print axioms combined_physical_budget
#print axioms actual_lindblad_from_input
#print axioms global_budget_control_comparison
#print axioms scalar_budget_attained_by_original_control
#print axioms RobustPiGate.global_leading_budget_attained

end Review070
