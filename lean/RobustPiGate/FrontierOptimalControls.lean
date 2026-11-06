import RobustPiGate.FrontierRigidity
import RobustPiGate.FrontierBounds
import RobustPiGate.FrontierEvolution
import RobustPiGate.EvolutionScaling

noncomputable section
open MeasureTheory Set Filter InnerProductGeometry
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator Topology Interval InnerProductSpace NNReal
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace RobustPiGate.Quantum

/-- 几何刚性相位恰好等于真实三段控制的累计转角加 π/2。 -/
theorem frontier_threeArcPhase_eq {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    FrontierRigidity.threeArcPhase (frontierDuration a / 2) t =
      Real.pi / 2 + frontierPhase a t := by
  have h₁ : (frontierDuration a / 2 - Real.pi / 2) / 2 = a := by
    dsimp [frontierDuration]; ring
  have h₂ : (3 * (frontierDuration a / 2) + Real.pi / 2) / 2 = 3 * a + Real.pi := by
    dsimp [frontierDuration]; ring
  unfold FrontierRigidity.threeArcPhase
  rw [h₁, h₂]
  split_ifs with hf hm
  · rw [frontierPhase_first ha hf]
  · rw [frontierPhase_middle (by linarith) hm]
    dsimp [frontierDuration]
    ring
  · rw [frontierPhase_last ha (by linarith)]
    dsimp [frontierDuration]
    ring

theorem rotatedFrontier_noise_coordinates {a ax ay : ℝ}
    (haxis : ax ^ 2 + ay ^ 2 = 1) (t : ℝ) :
    noiseVec (rotatedFrontier a ax ay t) = WithLp.toLp 2
      ![-ay * Real.sin (frontierPhase a t), ax * Real.sin (frontierPhase a t),
        Real.cos (frontierPhase a t)] := by
  unfold noiseVec noiseMatrix rotatedFrontier
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

theorem rotatedFrontier_noise_from_midpoint {a : ℝ} {v : Vec3}
    (hv : ‖v‖ = 1) (hvz : v 2 = 0) (t : ℝ) :
    noiseVec (rotatedFrontier a (-v 1) (v 0) t) =
      (-Real.sin (frontierPhase a t)) • v + Real.cos (frontierPhase a t) • ez := by
  rw [rotatedFrontier_noise_coordinates (transverse_midpoint_axis_unit hv hvz)]
  ext i
  fin_cases i <;> simp [ez, hvz] <;> ring

/-- 连续球面曲线的真实残差等号直接给出三弧形状，包含矩形 π 脉冲端点。 -/
theorem frontier_spherical_curve_rigidity {a : ℝ}
    (ha : a ∈ Icc 0 (Real.pi / 3)) {n : ℝ → Vec3}
    (hcont : ContinuousOn n (Icc 0 (frontierDuration a)))
    (hunit : ∀ t ∈ Icc 0 (frontierDuration a), ‖n t‖ = 1)
    (hspeed : SphericalSpeedBound n 0 (frontierDuration a))
    (hend : n (frontierDuration a) = -n 0)
    (heq : ‖∫ t in 0..frontierDuration a, n t‖ = frontierResidual (frontierDuration a)) :
    ⟪n (frontierDuration a / 2), n 0⟫_ℝ = 0 ∧
    ∀ t ∈ Icc 0 (frontierDuration a),
      n t = Real.cos (FrontierRigidity.threeArcPhase (frontierDuration a / 2) t) •
        n (frontierDuration a / 2) +
        Real.sin (FrontierRigidity.threeArcPhase (frontierDuration a / 2) t) • n 0 := by
  let c : ℝ := frontierDuration a / 2
  have hc : c ∈ Icc (Real.pi / 2) (7 * Real.pi / 6) := by
    dsimp [c, frontierDuration]
    constructor <;> linarith [ha.1, ha.2]
  have hlen : 2 * c = frontierDuration a := by dsimp [c]; ring
  rw [← hlen] at hcont hunit hspeed hend heq
  obtain ⟨hl, hr⟩ := spherical_curve_frontier_equality_angles hc.1 hc.2 hcont hunit hspeed hend heq
  have H := FrontierRigidity.spherical_equality_rigidity hc hunit hend
    (by intro s hs t ht; simpa [abs_sub_comm] using hspeed s hs t ht)
    (by simpa only [FrontierRigidity.radialEnvelope] using hl)
    (by simpa only [FrontierRigidity.radialEnvelope] using hr)
  simpa only [hlen] using H

/-- 整个前沿区间中，真实名义演化的残差等号强制三个同轴满幅段及其整体负号。 -/
theorem optimal_controls_of_frontier_noise {a : ℝ}
    (ha : a ∈ Icc 0 (Real.pi / 3))
    {ux uy : ℝ → ℝ} {U : ℝ → QubitMatrix}
    (hsol : Dynamics.IsACSolution (fun t => transverseGenerator (ux t) (uy t)) U
      (frontierDuration a))
    (hLip : LipschitzOnWith 1 (fun t => noiseVec (U t)) (Icc 0 (frontierDuration a)))
    (hgate : U (frontierDuration a) = rx Real.pi ∨ U (frontierDuration a) = -rx Real.pi)
    (heq : ‖∫ t in 0..frontierDuration a, noiseVec (U t)‖ = frontierResidual (frontierDuration a)) :
    (∀ᵐ t, t ∈ Icc 0 (frontierDuration a) → ux t = frontierControl a t ∧ uy t = 0) ∨
    (∀ᵐ t, t ∈ Icc 0 (frontierDuration a) → ux t = -frontierControl a t ∧ uy t = 0) := by
  have hT : 0 < frontierDuration a := by dsimp [frontierDuration]; linarith [ha.1, Real.pi_pos]
  have hunitary : ∀ t ∈ Icc 0 (frontierDuration a), U t ∈ unitary QubitMatrix := by
    intro t ht
    apply hsol.unitary _ (by rwa [uIcc_of_le hT.le])
    exact Filter.Eventually.of_forall fun s _ => transverseGenerator_skew _ _
  have hunit : ∀ t ∈ Icc 0 (frontierDuration a), ‖noiseVec (U t)‖ = 1 :=
    fun t ht => noiseVec_unit (U t) (hunitary t ht).1 (hunitary t ht).2
  have hinitial : noiseVec (U 0) = ez := by rw [hsol.initial, noiseVec_one]
  have hend : noiseVec (U (frontierDuration a)) = -noiseVec (U 0) := by
    rw [hinitial]
    exact noiseVec_gate_antipode hgate
  obtain ⟨horth, hshape⟩ := frontier_spherical_curve_rigidity ha
    hLip.continuousOn hunit (sphericalSpeedBound_of_lipschitzOnWith hunit hLip) hend heq
  let v : Vec3 := noiseVec (U (frontierDuration a / 2))
  have hv : ‖v‖ = 1 := hunit (frontierDuration a / 2) ⟨by linarith, by linarith⟩
  have hvz : v 2 = 0 := midpoint_z_eq_zero (by simpa only [hinitial] using horth)
  have haxis : (-v 1) ^ 2 + (v 0) ^ 2 = 1 := transverse_midpoint_axis_unit hv hvz
  have hnoiseVec : ∀ t ∈ Icc 0 (frontierDuration a),
      noiseVec (U t) = noiseVec (rotatedFrontier a (-v 1) (v 0) t) := by
    intro t ht
    rw [rotatedFrontier_noise_from_midpoint hv hvz]
    have hs := hshape t ht
    rw [frontier_threeArcPhase_eq ha.1, hinitial, Real.cos_add, Real.sin_add,
      Real.cos_pi_div_two, Real.sin_pi_div_two] at hs
    simpa only [zero_mul, one_mul, zero_add, add_zero, zero_sub] using hs
  have hnoise : ∀ t ∈ Icc 0 (frontierDuration a),
      star (U t) * sigmaZ * U t =
        star (rotatedFrontier a (-v 1) (v 0) t) * sigmaZ * rotatedFrontier a (-v 1) (v 0) t := by
    intro t ht
    change noiseMatrix (U t) = noiseMatrix (rotatedFrontier a (-v 1) (v 0) t)
    rw [noiseMatrix_eq_pauli (U t) (hunitary t ht).2,
      noiseMatrix_eq_pauli _ (rotatedFrontier_unitary ha.1 haxis t).2, hnoiseVec t ht]
  have hdU : ∀ᵐ t, t ∈ Icc 0 (frontierDuration a) →
      HasDerivAt U ((-Complex.I / 2) • (pauli (ux t) (uy t) 0 * U t)) t := by
    simpa only [uIcc_of_le hT.le, transverseGenerator_eq_pauli, smul_mul_assoc] using hsol.equation
  have hdV : ∀ᵐ t, t ∈ Icc 0 (frontierDuration a) →
      HasDerivAt (rotatedFrontier a (-v 1) (v 0))
        ((-Complex.I / 2) •
          (pauli ((-v 1) * frontierControl a t) ((v 0) * frontierControl a t) 0 *
            rotatedFrontier a (-v 1) (v 0) t)) t := by
    filter_upwards [rotatedFrontier_ae_ode ha.1 haxis] with t ht _
    simpa only [transverseGenerator_eq_pauli, smul_mul_assoc] using ht
  have hlift := transverse_controls_unique hT hsol.ac
    (rotatedFrontier_ac ha.1 (-v 1) (v 0) 0 (frontierDuration a))
    hunitary (fun t _ => rotatedFrontier_unitary ha.1 haxis t) hnoise hdU hdV
    (hsol.initial.trans (rotatedFrontier_initial ha.1 (-v 1) (v 0)).symm)
  have hterminal : Complex.I • pauli (-v 1) (v 0) 0 = rx Real.pi ∨
      Complex.I • pauli (-v 1) (v 0) 0 = -rx Real.pi := by
    rw [← rotatedFrontier_terminal ha.1, ← hlift.1 ⟨hT.le, le_rfl⟩]
    exact hgate
  rcases terminal_axis_unique hterminal with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact Or.inl (by simpa only [hx, hy, one_mul, zero_mul] using hlift.2)
  · exact Or.inr (by simpa only [hx, hy, neg_one_mul, zero_mul] using hlift.2)

/-- 任意有界横向 AC 演化的噪声速度界，不要求零残差。 -/
theorem frontier_nominal_noise_lipschitz {ux uy : ℝ → ℝ} {U : ℝ → QubitMatrix}
    {T : ℝ} {Ω : ℝ≥0}
    (hsol : Dynamics.IsACSolution (fun t => transverseGenerator (ux t) (uy t)) U T)
    (hamp : ∀ᵐ t, t ∈ uIcc 0 T → (ux t) ^ 2 + (uy t) ^ 2 ≤ (Ω : ℝ) ^ 2) :
    LipschitzOnWith Ω (fun t => noiseVec (U t)) (uIcc 0 T) := by
  have hunitary : ∀ t ∈ uIcc 0 T,
      (U t).conjTranspose * U t = 1 ∧ U t * (U t).conjTranspose = 1 := by
    intro t ht
    exact hsol.unitary (Filter.Eventually.of_forall fun s _ => transverseGenerator_skew _ _) ht
  have hd : ∀ᵐ t, t ∈ uIcc 0 T →
      HasDerivAt U ((-Complex.I / 2) • (pauli (ux t) (uy t) 0 * U t)) t := by
    simpa only [transverseGenerator_eq_pauli, smul_mul_assoc] using hsol.equation
  exact noiseVec_lipschitz hsol.ac hunitary hd hamp

/-- 任意正幅度 Ω 下，从真实残差等号分类全部控制；等号结构没有作为前提。 -/
theorem frontier_optimal_controls_unique_scaled
    {ux uy : ℝ → ℝ} {U : ℝ → ℝ → QubitMatrix} {T Ω : ℝ}
    (hΩ : 0 < Ω) (hL : Ω * T ∈ Icc Real.pi (7 * Real.pi / 3))
    (hU : Dynamics.IsQubitEvolution ux uy U T)
    (hamp : ∀ᵐ t, t ∈ Icc 0 T → (ux t) ^ 2 + (uy t) ^ 2 ≤ Ω ^ 2)
    (hgate : U 0 T = rx Real.pi ∨ U 0 T = -rx Real.pi)
    (heq : Ω * ‖∫ t in 0..T, noiseVec (U 0 t)‖ = frontierResidual (Ω * T)) :
    (∀ᵐ t, t ∈ Icc 0 T →
      ux t = Ω * frontierControl ((Ω * T - Real.pi) / 4) (Ω * t) ∧ uy t = 0) ∨
    (∀ᵐ t, t ∈ Icc 0 T →
      ux t = -(Ω * frontierControl ((Ω * T - Real.pi) / 4) (Ω * t)) ∧ uy t = 0) := by
  let a : ℝ := (Ω * T - Real.pi) / 4
  have ha : a ∈ Icc 0 (Real.pi / 3) := by
    dsimp [a]
    constructor <;> linarith [hL.1, hL.2]
  have hscale : Ω * T = frontierDuration a := by dsimp [a, frontierDuration]; ring
  have hT : 0 ≤ T := by
    have hp : 0 < Ω * T := lt_of_lt_of_le Real.pi_pos hL.1
    exact (pos_of_mul_pos_right hp hΩ.le).le
  have hdiv : frontierDuration a / Ω = T := by rw [← hscale]; field_simp
  have hampU : ∀ᵐ t, t ∈ uIcc 0 T → (ux t) ^ 2 + (uy t) ^ 2 ≤ Ω ^ 2 := by
    simpa only [uIcc_of_le hT] using hamp
  have hnom := Dynamics.qubit_nominal_solution hU
  have hsol := nominal_time_rescale hΩ hT hnom hampU
  rw [hscale] at hsol
  have hLip := frontier_nominal_noise_lipschitz (Ω := NNReal.mk Ω hΩ.le) hnom hampU
  rw [uIcc_of_le hT] at hLip
  have hLipN := noise_lipschitz_rescale hΩ hLip
  rw [hscale] at hLipN
  have hgateN : U 0 (frontierDuration a / Ω) = rx Real.pi ∨
      U 0 (frontierDuration a / Ω) = -rx Real.pi := by simpa only [hdiv] using hgate
  have heqN : ‖∫ s in 0..frontierDuration a, noiseVec (U 0 (s / Ω))‖ =
      frontierResidual (frontierDuration a) := by
    rw [intervalIntegral.integral_comp_div (fun t => noiseVec (U 0 t)) hΩ.ne',
      zero_div, hdiv, norm_smul, Real.norm_eq_abs, abs_of_pos hΩ, ← hscale]
    exact heq
  have hmem {t : ℝ} (ht : t ∈ Icc 0 T) : Ω * t ∈ Icc 0 (frontierDuration a) := by
    refine ⟨mul_nonneg hΩ.le ht.1, ?_⟩
    rw [← hscale]
    exact mul_le_mul_of_nonneg_left ht.2 hΩ.le
  rcases optimal_controls_of_frontier_noise ha hsol hLipN hgateN heqN with hpos | hneg
  · left
    filter_upwards [ae_comp_mul hΩ.ne' hpos] with t ht htI
    have hh := ht (hmem htI)
    have hx : ux t / Ω = frontierControl a (Ω * t) := by simpa [hΩ.ne'] using hh.1
    have hy : uy t / Ω = 0 := by simpa [hΩ.ne'] using hh.2
    exact ⟨by simpa only [a, mul_comm] using (div_eq_iff hΩ.ne').mp hx,
      by simpa only [zero_mul] using (div_eq_iff hΩ.ne').mp hy⟩
  · right
    filter_upwards [ae_comp_mul hΩ.ne' hneg] with t ht htI
    have hh := ht (hmem htI)
    have hx : ux t / Ω = -frontierControl a (Ω * t) := by simpa [hΩ.ne'] using hh.1
    have hy : uy t / Ω = 0 := by simpa [hΩ.ne'] using hh.2
    exact ⟨by simpa only [a, neg_mul, mul_neg, mul_comm] using (div_eq_iff hΩ.ne').mp hx,
      by simpa only [zero_mul] using (div_eq_iff hΩ.ne').mp hy⟩

end RobustPiGate.Quantum

#print axioms RobustPiGate.Quantum.optimal_controls_of_frontier_noise
#print axioms RobustPiGate.Quantum.frontier_optimal_controls_unique_scaled
