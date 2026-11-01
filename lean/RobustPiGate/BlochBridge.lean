import RobustPiGate.Quantum
import RobustPiGate.ACCalculus
import RobustPiGate.TimeScaling
import RobustPiGate.QubitDynamics

noncomputable section
open Real Set MeasureTheory Filter
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator NNReal

namespace RobustPiGate.Quantum

/-- 从无迹 Hermitian 矩阵读取规范 Bloch 坐标。 -/
def blochVec (A : QubitMatrix) : Vec3 :=
  WithLp.toLp 2 ![(A 0 1).re, -(A 0 1).im, (A 0 0).re]

/-- 规范坐标读取是实连续线性映射。 -/
def blochCLM : QubitMatrix →L[ℝ] Vec3 :=
  LinearMap.toContinuousLinearMap {
    toFun := blochVec
    map_add' := by
      intro A B
      ext i
      fin_cases i <;> simp [blochVec] <;> ring
    map_smul' := by
      intro r A
      ext i
      fin_cases i <;> simp [blochVec] }

@[simp] theorem blochCLM_apply (A : QubitMatrix) : blochCLM A = blochVec A := rfl

/-- 实际传播子的 toggling-frame 噪声矩阵。 -/
def noiseMatrix (U : QubitMatrix) : QubitMatrix := U.conjTranspose * sigmaZ * U

/-- 实际传播子确定的唯一规范噪声方向。 -/
def noiseVec (U : QubitMatrix) : Vec3 := blochVec (noiseMatrix U)

theorem pauli_conjTranspose (x y z : ℝ) : (pauli x y z).conjTranspose = pauli x y z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli, Matrix.conjTranspose_apply] <;> ring

theorem pauli_trace (x y z : ℝ) : Matrix.trace (pauli x y z) = 0 := by
  simp [Matrix.trace, pauli, Fin.sum_univ_two]

theorem sigmaZ_eq_pauli : sigmaZ = pauli 0 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaZ, pauli]

/-- 无迹 Hermitian 矩阵由上述三个坐标精确重建。 -/
theorem pauli_blochVec {A : QubitMatrix}
    (hH : A.conjTranspose = A) (htr : Matrix.trace A = 0) :
    pauli (blochVec A 0) (blochVec A 1) (blochVec A 2) = A := by
  have h00 := congrArg (fun M : QubitMatrix => (M 0 0).im) hH
  have h10r := congrArg (fun M : QubitMatrix => (M 1 0).re) hH
  have h10i := congrArg (fun M : QubitMatrix => (M 1 0).im) hH
  have htrr := congrArg Complex.re htr
  have htri := congrArg Complex.im htr
  simp [Matrix.conjTranspose_apply] at h00 h10r h10i
  simp [Matrix.trace, Fin.sum_univ_two] at htrr htri
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [pauli, blochVec] <;> linarith

/-- 酉共轭后的任意 Pauli 矩阵仍由规范 Bloch 坐标重建。 -/
theorem conjugate_pauli_blochVec (U : QubitMatrix) (hUU : U * U.conjTranspose = 1)
    (x y z : ℝ) :
    pauli (blochVec (U.conjTranspose * pauli x y z * U) 0)
      (blochVec (U.conjTranspose * pauli x y z * U) 1)
      (blochVec (U.conjTranspose * pauli x y z * U) 2) =
      U.conjTranspose * pauli x y z * U := by
  apply pauli_blochVec
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      pauli_conjTranspose, Matrix.mul_assoc]
  · rw [Matrix.trace_mul_cycle, hUU, Matrix.one_mul, pauli_trace]

theorem noiseMatrix_eq_pauli (U : QubitMatrix) (hUU : U * U.conjTranspose = 1) :
    noiseMatrix U = pauli (noiseVec U 0) (noiseVec U 1) (noiseVec U 2) := by
  simpa [noiseVec, noiseMatrix, sigmaZ_eq_pauli] using
    (conjugate_pauli_blochVec U hUU 0 0 1).symm

theorem noiseVec_unit (U : QubitMatrix)
    (hU : U.conjTranspose * U = 1) (hUU : U * U.conjTranspose = 1) :
    ‖noiseVec U‖ = 1 := by
  have hrepr : U.conjTranspose * pauli 0 0 1 * U =
      pauli (noiseVec U 0) (noiseVec U 1) (noiseVec U 2) := by
    simpa [noiseMatrix, sigmaZ_eq_pauli] using noiseMatrix_eq_pauli U hUU
  have hsq := conjugation_preserves_square_norm U hU hUU
    0 0 1 (noiseVec U 0) (noiseVec U 1) (noiseVec U 2) hrepr
  have hn : ‖noiseVec U‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa [Fin.sum_univ_succ, pow_two, add_assoc] using hsq
  nlinarith [norm_nonneg (noiseVec U)]

/-- 由真实横向控制诱导的噪声向量导数。 -/
def noiseVelocity (U : QubitMatrix) (ux uy : ℝ) : Vec3 :=
  blochVec (U.conjTranspose * pauli (-uy) ux 0 * U)

theorem noiseVelocity_norm_sq (U : QubitMatrix)
    (hU : U.conjTranspose * U = 1) (hUU : U * U.conjTranspose = 1) (ux uy : ℝ) :
    ‖noiseVelocity U ux uy‖ ^ 2 = ux ^ 2 + uy ^ 2 := by
  have hr := (conjugate_pauli_blochVec U hUU (-uy) ux 0).symm
  have h := transverse_noise_speed_squared U hU hUU ux uy
    (noiseVelocity U ux uy 0) (noiseVelocity U ux uy 1) (noiseVelocity U ux uy 2) hr
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa [Fin.sum_univ_succ, pow_two, add_assoc] using h

theorem hasDerivAt_noiseMatrix {U : ℝ → QubitMatrix} {t ux uy : ℝ}
    (hd : HasDerivAt U ((-Complex.I / 2) • (pauli ux uy 0 * U t)) t) :
    HasDerivAt (fun s => noiseMatrix (U s))
      ((U t).conjTranspose * pauli (-uy) ux 0 * U t) t := by
  have h := (hd.star.mul_const sigmaZ).mul hd
  have heq :
      star ((-Complex.I / 2) • (pauli ux uy 0 * U t)) * sigmaZ * U t +
      star (U t) * sigmaZ * ((-Complex.I / 2) • (pauli ux uy 0 * U t)) =
      (U t).conjTranspose * pauli (-uy) ux 0 * U t := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
        pauli, sigmaZ, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
        map_ofNat] <;>
      ring_nf <;> simp [Complex.I_sq] <;> ring
  rw [heq] at h
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun s => rfl)

theorem hasDerivAt_noiseVec {U : ℝ → QubitMatrix} {t ux uy : ℝ}
    (hd : HasDerivAt U ((-Complex.I / 2) • (pauli ux uy 0 * U t)) t) :
    HasDerivAt (fun s => noiseVec (U s)) (noiseVelocity (U t) ux uy) t := by
  exact blochCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_noiseMatrix hd)

theorem noiseMatrix_ac {U : ℝ → QubitMatrix} {a b : ℝ}
    (hU : AbsolutelyContinuousOnInterval U a b) :
    AbsolutelyContinuousOnInterval (fun t => noiseMatrix (U t)) a b := by
  have hs : AbsolutelyContinuousOnInterval (fun t => (U t).conjTranspose) a b :=
    star_isometry.lipschitzWith.comp_absolutelyContinuousOnInterval hU
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => sigmaZ) a b :=
    (LipschitzWith.const sigmaZ).lipschitzOnWith.absolutelyContinuousOnInterval
  exact Dynamics.ac_mul (Dynamics.ac_mul hs hc) hU

theorem noiseVec_ac {U : ℝ → QubitMatrix} {a b : ℝ}
    (hU : AbsolutelyContinuousOnInterval U a b) :
    AbsolutelyContinuousOnInterval (fun t => noiseVec (U t)) a b :=
  blochCLM.lipschitzWith.comp_absolutelyContinuousOnInterval (noiseMatrix_ac hU)

theorem noiseVec_lipschitz {U : ℝ → QubitMatrix} {ux uy : ℝ → ℝ} {a b : ℝ}
    {Ω : ℝ≥0} (hU : AbsolutelyContinuousOnInterval U a b)
    (hunitary : ∀ t ∈ uIcc a b,
      (U t).conjTranspose * U t = 1 ∧ U t * (U t).conjTranspose = 1)
    (hd : ∀ᵐ t, t ∈ uIcc a b →
      HasDerivAt U ((-Complex.I / 2) • (pauli (ux t) (uy t) 0 * U t)) t)
    (hamp : ∀ᵐ t, t ∈ uIcc a b → (ux t) ^ 2 + (uy t) ^ 2 ≤ (Ω : ℝ) ^ 2) :
    LipschitzOnWith Ω (fun t => noiseVec (U t)) (uIcc a b) := by
  apply Dynamics.lipschitzOnWith_of_ac_deriv_bound (noiseVec_ac hU)
  filter_upwards [hd, hamp] with t hdt htamp ht
  rw [(hasDerivAt_noiseVec (hdt ht)).deriv]
  have hn := noiseVelocity_norm_sq (U t) (hunitary t ht).1 (hunitary t ht).2 (ux t) (uy t)
  have hb := htamp ht
  nlinarith [norm_nonneg (noiseVelocity (U t) (ux t) (uy t)), Ω.coe_nonneg]

@[simp] theorem noiseVec_one : noiseVec (1 : QubitMatrix) = ez := by
  ext i
  fin_cases i <;> simp [noiseVec, noiseMatrix, blochVec, sigmaZ, ez]

theorem noiseVec_gate_antipode {U : QubitMatrix}
    (hgate : U = rx Real.pi ∨ U = -rx Real.pi) : noiseVec U = -ez := by
  have hm : noiseMatrix U = -sigmaZ := by
    rcases hgate with rfl | rfl
    · exact rx_pi_antipode
    · simpa [noiseMatrix] using rx_pi_antipode
  simp only [noiseVec, hm]
  ext i
  fin_cases i <;> simp [blochVec, sigmaZ, ez]

theorem noiseVec_integral_zero {U : ℝ → QubitMatrix} {a b : ℝ}
    (hU : AbsolutelyContinuousOnInterval U a b)
    (hzero : (∫ t in a..b, noiseMatrix (U t)) = 0) :
    (∫ t in a..b, noiseVec (U t)) = 0 := by
  have hi : IntervalIntegrable (fun t => noiseMatrix (U t)) volume a b :=
    (noiseMatrix_ac hU).continuousOn.intervalIntegrable
  change (∫ t in a..b, blochCLM (noiseMatrix (U t))) = 0
  rw [blochCLM.intervalIntegral_comp_comm hi, hzero, map_zero]

/-- 原量子演化、幅度、目标门和失谐导数条件直接产生完整几何证书。 -/
theorem actual_noise_curve {ux uy : ℝ → ℝ} {U : ℝ → ℝ → QubitMatrix}
    {T : ℝ} {Ω : ℝ≥0}
    (hU : Dynamics.IsQubitEvolution ux uy U T)
    (hamp : ∀ᵐ t, t ∈ uIcc 0 T → (ux t) ^ 2 + (uy t) ^ 2 ≤ (Ω : ℝ) ^ 2)
    (hgate : U 0 T = rx Real.pi ∨ U 0 T = -rx Real.pi)
    (hrobust : deriv (fun δ => U δ T) 0 = 0) :
    (∀ t ∈ uIcc 0 T, ‖noiseVec (U 0 t)‖ = 1) ∧
    LipschitzOnWith Ω (fun t => noiseVec (U 0 t)) (uIcc 0 T) ∧
    noiseVec (U 0 T) = -noiseVec (U 0 0) ∧
    (∫ t in 0..T, noiseVec (U 0 t)) = 0 := by
  have hnom := Dynamics.qubit_nominal_solution hU
  have hunitary : ∀ t ∈ uIcc 0 T,
      (U 0 t).conjTranspose * U 0 t = 1 ∧ U 0 t * (U 0 t).conjTranspose = 1 := by
    intro t ht
    exact Dynamics.qubit_nominal_unitary hU ht
  have hd : ∀ᵐ t, t ∈ uIcc 0 T →
      HasDerivAt (U 0) ((-Complex.I / 2) • (pauli (ux t) (uy t) 0 * U 0 t)) t := by
    filter_upwards [hnom.equation] with t ht htI
    simpa only [transverseGenerator, pauli_eq, Complex.ofReal_zero, zero_smul,
      add_zero, smul_mul_assoc] using ht htI
  refine ⟨fun t ht => noiseVec_unit _ (hunitary t ht).1 (hunitary t ht).2,
    noiseVec_lipschitz hnom.ac hunitary hd hamp, ?_, ?_⟩
  · rw [hnom.initial, noiseVec_one]
    exact noiseVec_gate_antipode hgate
  · apply noiseVec_integral_zero hnom.ac
    exact (Dynamics.qubit_first_order_robust_iff hU).mp hrobust

/-- 原量子ODE模型中，任意可测横向控制的失谐鲁棒 π 门满足锐时间下界。 -/
theorem actual_gate_time_lower_bound {ux uy : ℝ → ℝ}
    {U : ℝ → ℝ → QubitMatrix} {T : ℝ} {Ω : ℝ≥0}
    (hΩ : 0 < Ω) (hT : 0 < T)
    (hU : Dynamics.IsQubitEvolution ux uy U T)
    (hamp : ∀ᵐ t, t ∈ uIcc 0 T → (ux t) ^ 2 + (uy t) ^ 2 ≤ (Ω : ℝ) ^ 2)
    (hgate : U 0 T = rx Real.pi ∨ U 0 T = -rx Real.pi)
    (hrobust : deriv (fun δ => U δ T) 0 = 0) :
    7 * Real.pi / (3 * (Ω : ℝ)) ≤ T := by
  obtain ⟨hunit, hLip, hend, hzero⟩ := actual_noise_curve hU hamp hgate hrobust
  exact spherical_curve_time_lower_bound hΩ hT
    (by simpa [uIcc_of_le hT.le] using hLip)
    (by simpa [uIcc_of_le hT.le] using hunit) hend hzero

end RobustPiGate.Quantum

#print axioms RobustPiGate.Quantum.actual_noise_curve
#print axioms RobustPiGate.Quantum.actual_gate_time_lower_bound
