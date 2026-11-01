import RobustPiGate.RotatedShort
import RobustPiGate.BlochBridge
import RobustPiGate.Equality
import RobustPiGate.LiftUniqueness

noncomputable section
open MeasureTheory Set Filter
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator Topology Interval InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace RobustPiGate.Quantum
open Rigidity

/-- 几何三弧相位与实际短 CORPSE 的有符号累积角完全一致。 -/
theorem threeArcPhase_eq_shortPhase (t : ℝ) :
    threeArcPhase t = Real.pi / 2 + shortPhase t := by
  unfold threeArcPhase
  split_ifs with hfirst hmiddle
  · rw [phase_first hfirst]
  · rw [phase_middle (by linarith) hmiddle]
    ring
  · rw [phase_last (by linarith)]
    ring

theorem rotatedShort_noise_coordinates {ax ay : ℝ}
    (haxis : ax ^ 2 + ay ^ 2 = 1) (t : ℝ) :
    noiseVec (rotatedShort ax ay t) = WithLp.toLp 2
      ![-ay * Real.sin (shortPhase t), ax * Real.sin (shortPhase t), Real.cos (shortPhase t)] := by
  unfold noiseVec noiseMatrix rotatedShort
  rw [axisRotation_conjugates_z haxis]
  ext i
  fin_cases i <;> simp [blochVec, pauli, -Complex.ofReal_sin, -Complex.ofReal_cos]

private theorem midpoint_z_eq_zero {v : Vec3} (hv : ⟪v, ez⟫_ℝ = 0) : v 2 = 0 := by
  simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ, ez] using hv

private theorem transverse_midpoint_axis_unit {v : Vec3} (hv : ‖v‖ = 1) (hvz : v 2 = 0) :
    (-v 1) ^ 2 + (v 0) ^ 2 = 1 := by
  have hn := congrArg (fun r : ℝ => r ^ 2) hv
  rw [EuclideanSpace.real_norm_sq_eq] at hn
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, one_pow] at hn
  change (v 0) ^ 2 + ((v 1) ^ 2 + (v 2) ^ 2) = 1 at hn
  rw [hvz] at hn
  nlinarith

theorem rotatedShort_noise_from_midpoint {v : Vec3} (hv : ‖v‖ = 1) (hvz : v 2 = 0) (t : ℝ) :
    noiseVec (rotatedShort (-v 1) (v 0) t) =
      (-Real.sin (shortPhase t)) • v + Real.cos (shortPhase t) • ez := by
  rw [rotatedShort_noise_coordinates (transverse_midpoint_axis_unit hv hvz)]
  ext i
  fin_cases i <;> simp [ez, hvz] <;> ring

/-- 临界时长的真实名义演化和规范噪声曲线决定全部控制。 -/
theorem optimal_controls_of_critical_noise
    {ux uy : ℝ → ℝ} {U : ℝ → QubitMatrix}
    (hsol : Dynamics.IsACSolution (fun t => transverseGenerator (ux t) (uy t)) U
      (7 * Real.pi / 3))
    (hLip : LipschitzOnWith 1 (fun t => noiseVec (U t)) (Icc 0 (7 * Real.pi / 3)))
    (hgate : U (7 * Real.pi / 3) = rx Real.pi ∨ U (7 * Real.pi / 3) = -rx Real.pi)
    (hzero : (∫ t in 0..7 * Real.pi / 3, noiseVec (U t)) = 0) :
    (∀ᵐ t, t ∈ Icc 0 (7 * Real.pi / 3) → ux t = shortControl t ∧ uy t = 0) ∨
    (∀ᵐ t, t ∈ Icc 0 (7 * Real.pi / 3) → ux t = -shortControl t ∧ uy t = 0) := by
  have hT : 0 < 7 * Real.pi / 3 := by positivity
  have hunitary : ∀ t ∈ Icc 0 (7 * Real.pi / 3), U t ∈ unitary QubitMatrix := by
    intro t ht
    apply hsol.unitary _ (by rwa [uIcc_of_le hT.le])
    exact Filter.Eventually.of_forall fun s _ => transverseGenerator_skew _ _
  have hunit : ∀ t ∈ Icc 0 (7 * Real.pi / 3), ‖noiseVec (U t)‖ = 1 :=
    fun t ht => noiseVec_unit (U t) (hunitary t ht).1 (hunitary t ht).2
  have hinitial : noiseVec (U 0) = ez := by rw [hsol.initial, noiseVec_one]
  have hend : noiseVec (U (7 * Real.pi / 3)) = -noiseVec (U 0) := by
    rw [hinitial]
    exact noiseVec_gate_antipode hgate
  obtain ⟨horth, hshape⟩ := spherical_curve_equality_rigidity
    hLip.continuousOn hunit (sphericalSpeedBound_of_lipschitzOnWith hunit hLip) hend hzero
  let v : Vec3 := noiseVec (U halfDuration)
  have hv : ‖v‖ = 1 := hunit halfDuration
    ⟨halfDuration_pos.le, by dsimp [halfDuration]; linarith [Real.pi_pos]⟩
  have hvz : v 2 = 0 := midpoint_z_eq_zero (by simpa only [hinitial] using horth)
  have haxis : (-v 1) ^ 2 + (v 0) ^ 2 = 1 := transverse_midpoint_axis_unit hv hvz
  have hnoiseVec : ∀ t ∈ Icc 0 (7 * Real.pi / 3),
      noiseVec (U t) = noiseVec (rotatedShort (-v 1) (v 0) t) := by
    intro t ht
    rw [rotatedShort_noise_from_midpoint hv hvz]
    have hs := hshape t ht
    rw [threeArcPhase_eq_shortPhase, hinitial, Real.cos_add, Real.sin_add,
      Real.cos_pi_div_two, Real.sin_pi_div_two] at hs
    simpa only [zero_mul, one_mul, zero_add, add_zero, zero_sub] using hs
  have hnoise : ∀ t ∈ Icc 0 (7 * Real.pi / 3),
      star (U t) * sigmaZ * U t =
        star (rotatedShort (-v 1) (v 0) t) * sigmaZ * rotatedShort (-v 1) (v 0) t := by
    intro t ht
    change noiseMatrix (U t) = noiseMatrix (rotatedShort (-v 1) (v 0) t)
    rw [noiseMatrix_eq_pauli (U t) (hunitary t ht).2,
      noiseMatrix_eq_pauli _ (rotatedShort_unitary haxis t).2, hnoiseVec t ht]
  have hdU : ∀ᵐ t, t ∈ Icc 0 (7 * Real.pi / 3) →
      HasDerivAt U ((-Complex.I / 2) • (pauli (ux t) (uy t) 0 * U t)) t := by
    simpa only [uIcc_of_le hT.le, transverseGenerator_eq_pauli, smul_mul_assoc]
      using hsol.equation
  have hdV : ∀ᵐ t, t ∈ Icc 0 (7 * Real.pi / 3) →
      HasDerivAt (rotatedShort (-v 1) (v 0))
        ((-Complex.I / 2) •
          (pauli ((-v 1) * shortControl t) ((v 0) * shortControl t) 0 *
            rotatedShort (-v 1) (v 0) t)) t := by
    filter_upwards [rotatedShort_ae_ode haxis] with t ht _
    simpa only [transverseGenerator_eq_pauli, smul_mul_assoc] using ht
  have hlift := transverse_controls_unique hT hsol.ac
    (rotatedShort_ac (-v 1) (v 0) 0 (7 * Real.pi / 3))
    hunitary (fun t _ => rotatedShort_unitary haxis t) hnoise hdU hdV
    (hsol.initial.trans (rotatedShort_initial (-v 1) (v 0)).symm)
  have hterminal : Complex.I • pauli (-v 1) (v 0) 0 = rx Real.pi ∨
      Complex.I • pauli (-v 1) (v 0) 0 = -rx Real.pi := by
    rw [← rotatedShort_terminal, ← hlift.1 ⟨hT.le, le_rfl⟩]
    exact hgate
  rcases terminal_axis_unique hterminal with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inl (by simpa only [hx, hy, one_mul, zero_mul] using hlift.2)
  · exact Or.inr (by simpa only [hx, hy, neg_one_mul, zero_mul] using hlift.2)

/-- 原始失谐参数族在最短归一化时间处，只能使用短 CORPSE 或其整体负号。 -/
theorem optimal_controls_unique
    {ux uy : ℝ → ℝ} {U : ℝ → ℝ → QubitMatrix}
    (hU : Dynamics.IsQubitEvolution ux uy U (7 * Real.pi / 3))
    (hamp : ∀ᵐ t, t ∈ Icc 0 (7 * Real.pi / 3) → (ux t) ^ 2 + (uy t) ^ 2 ≤ 1)
    (hgate : U 0 (7 * Real.pi / 3) = rx Real.pi ∨ U 0 (7 * Real.pi / 3) = -rx Real.pi)
    (hrobust : deriv (fun δ => U δ (7 * Real.pi / 3)) 0 = 0) :
    (∀ᵐ t, t ∈ Icc 0 (7 * Real.pi / 3) → ux t = shortControl t ∧ uy t = 0) ∨
    (∀ᵐ t, t ∈ Icc 0 (7 * Real.pi / 3) → ux t = -shortControl t ∧ uy t = 0) := by
  have hT : 0 ≤ 7 * Real.pi / 3 := by positivity
  have ham : ∀ᵐ t, t ∈ uIcc 0 (7 * Real.pi / 3) →
      (ux t) ^ 2 + (uy t) ^ 2 ≤ ((1 : NNReal) : ℝ) ^ 2 := by
    simpa only [uIcc_of_le hT, NNReal.coe_one, one_pow] using hamp
  obtain ⟨_, hLip, _, hzero⟩ := actual_noise_curve hU ham hgate hrobust
  rw [uIcc_of_le hT] at hLip
  exact optimal_controls_of_critical_noise (Dynamics.qubit_nominal_solution hU) hLip hgate hzero

end RobustPiGate.Quantum

#print axioms RobustPiGate.Quantum.optimal_controls_unique
