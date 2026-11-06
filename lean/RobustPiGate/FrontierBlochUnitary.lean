import RobustPiGate.FrontierFidelity
import RobustPiGate.FrontierDyson
import RobustPiGate.FrontierNoise

open MeasureTheory Set Filter
open scoped Topology Interval Matrix ComplexConjugate Matrix.Norms.L2Operator

namespace RobustPiGate.Quantum
open RobustPiGate.Dynamics
noncomputable section
set_option maxHeartbeats 1600000

abbrev QubitBlochMatrix := Matrix (Fin 3) (Fin 3) ℝ

def pauliBasis : Fin 3 → QubitMatrix := ![sigmaX, sigmaY, sigmaZ]

/-- Pauli 的实迹坐标；在无迹Hermitian矩阵上等于规范blochVec。 -/
def pauliCoordinates (A : QubitMatrix) : Fin 3 → ℝ :=
  ![((A 0 1).re + (A 1 0).re) / 2, ((A 1 0).im - (A 0 1).im) / 2,
    ((A 0 0).re - (A 1 1).re) / 2]

theorem pauliCoordinates_eq_blochVec {A : QubitMatrix}
    (hH : A.conjTranspose = A) (htr : Matrix.trace A = 0) :
    pauliCoordinates A = fun i => blochVec A i := by
  have h01r := congrArg (fun M : QubitMatrix => (M 0 1).re) hH
  have h01i := congrArg (fun M : QubitMatrix => (M 0 1).im) hH
  have htrr := congrArg Complex.re htr
  simp [Matrix.conjTranspose_apply] at h01r h01i
  simp [Matrix.trace, Fin.sum_univ_two] at htrr
  ext i
  fin_cases i <;> simp [pauliCoordinates, blochVec] <;> linarith

/-- 真实量子共轭在三个 Pauli 基向量上的实矩阵。 -/
def blochRotation (U : QubitMatrix) : QubitBlochMatrix :=
  fun i j => pauliCoordinates (U * pauliBasis j * U.conjTranspose) i

theorem blochRotation_one : blochRotation (1 : QubitMatrix) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blochRotation, pauliBasis, pauliCoordinates, sigmaX, sigmaY, sigmaZ]

theorem blochRotation_action (U : QubitMatrix) (q : Fin 3 → ℝ) :
    (blochRotation U).mulVec q =
      pauliCoordinates (U * pauli (q 0) (q 1) (q 2) * U.conjTranspose) := by
  ext i
  fin_cases i <;>
    simp [blochRotation, pauliBasis, pauliCoordinates, sigmaX, sigmaY, sigmaZ, pauli,
      Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_two, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply, Complex.mul_re, Complex.mul_im] <;> ring

theorem pauliBasis_eq (j : Fin 3) :
    pauliBasis j = pauli (if j = 0 then 1 else 0) (if j = 1 then 1 else 0)
      (if j = 2 then 1 else 0) := by
  fin_cases j <;> ext i k <;> fin_cases i <;> fin_cases k <;>
    simp [pauliBasis, sigmaX, sigmaY, sigmaZ, pauli]

theorem blochRotation_column_pauli (U : QubitMatrix) (hU : U ∈ unitary QubitMatrix) (j : Fin 3) :
    pauli (blochRotation U 0 j) (blochRotation U 1 j) (blochRotation U 2 j) =
      U * pauliBasis j * U.conjTranspose := by
  have hc : pauliCoordinates (U * pauliBasis j * U.conjTranspose) =
      fun i => blochVec (U * pauliBasis j * U.conjTranspose) i := by
    apply pauliCoordinates_eq_blochVec
    · rw [pauliBasis_eq]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        pauli_conjTranspose, mul_assoc]
    · have hu : U.conjTranspose * U = 1 := hU.1
      rw [Matrix.trace_mul_cycle, hu, one_mul, pauliBasis_eq, pauli_trace]
  simp only [blochRotation, hc]
  simpa only [pauliBasis_eq, Matrix.conjTranspose_conjTranspose] using
    conjugate_pauli_blochVec U.conjTranspose
      (by simpa only [Matrix.conjTranspose_conjTranspose] using (show U.conjTranspose * U = 1 from hU.1))
      (if j = 0 then 1 else 0) (if j = 1 then 1 else 0) (if j = 2 then 1 else 0)

theorem blochRotation_pauli (U : QubitMatrix) (hU : U ∈ unitary QubitMatrix) (q : Fin 3 → ℝ) :
    pauli ((blochRotation U).mulVec q 0) ((blochRotation U).mulVec q 1)
      ((blochRotation U).mulVec q 2) = U * pauli (q 0) (q 1) (q 2) * U.conjTranspose := by
  have hu : U.conjTranspose * U = 1 := hU.1
  have hc : pauliCoordinates (U * pauli (q 0) (q 1) (q 2) * U.conjTranspose) =
      fun i => blochVec (U * pauli (q 0) (q 1) (q 2) * U.conjTranspose) i := by
    apply pauliCoordinates_eq_blochVec
    · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        pauli_conjTranspose, mul_assoc]
    · rw [Matrix.trace_mul_cycle, hu, one_mul, pauli_trace]
  rw [blochRotation_action, hc]
  simpa only [Matrix.conjTranspose_conjTranspose] using
    conjugate_pauli_blochVec U.conjTranspose
      (by simpa only [Matrix.conjTranspose_conjTranspose] using hu) (q 0) (q 1) (q 2)

theorem blochRotation_mul (U V : QubitMatrix) (hV : V ∈ unitary QubitMatrix) :
    blochRotation (U * V) = blochRotation U * blochRotation V := by
  ext i j
  have h := congrFun (blochRotation_action U (fun k => blochRotation V k j)) i
  change (blochRotation U * blochRotation V) i j = _ at h
  rw [blochRotation_column_pauli V hV j] at h
  rw [h]
  simp only [blochRotation, Matrix.conjTranspose_mul, mul_assoc]

theorem blochRotation_star (U : QubitMatrix) :
    blochRotation U.conjTranspose = (blochRotation U).transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blochRotation, pauliBasis, pauliCoordinates, sigmaX, sigmaY, sigmaZ,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem blochRotation_unitary (U : QubitMatrix) (hU : U ∈ unitary QubitMatrix) :
    blochRotation U ∈ unitary QubitBlochMatrix := by
  have hleft : (blochRotation U).transpose * blochRotation U = 1 := by
    have hu : U.conjTranspose * U = 1 := hU.1
    rw [← blochRotation_star, ← blochRotation_mul _ _ hU, hu, blochRotation_one]
  have hh : star (blochRotation U) * blochRotation U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using hleft
  exact ⟨hh, mul_eq_one_comm.mp hh⟩

theorem trace_blochRotation (U : QubitMatrix) (hU : U ∈ unitary QubitMatrix) :
    Matrix.trace (blochRotation U) = Complex.normSq (Matrix.trace U) - 1 := by
  have hu := congrArg (fun M : QubitMatrix => (M 1 1).re) hU.1
  have hu0 := congrArg (fun M : QubitMatrix => (M 0 0).re) hU.1
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.mul_re] at hu hu0
  simp [blochRotation, pauliBasis, pauliCoordinates, sigmaX, sigmaY, sigmaZ,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_succ,
    Matrix.conjTranspose_apply, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  nlinarith

/-- Bloch 相对旋转的平均迹保真度与原2×2门保真度精确一致。 -/
theorem blochRotation_fidelity {ux uy : ℝ → ℝ} {U : ℝ → ℝ → QubitMatrix} {T : ℝ}
    (hU : IsQubitEvolution ux uy U T) (δ : ℝ) :
    (Matrix.trace ((blochRotation (U 0 T)).transpose * blochRotation (U δ T)) + 3) / 6 =
      avgGateFidelity U 1 T δ := by
  rw [← blochRotation_star, ← blochRotation_mul _ _ (qubit_unitary hU δ right_mem_uIcc),
    trace_blochRotation _ (interaction_unitary hU δ)]
  unfold avgGateFidelity
  simp only [one_mul]
  ring

/-- 真实Bloch静态失谐保真度的二阶系数，没有额外系数假设。 -/
theorem blochRotation_sensitivity_limit {ux uy : ℝ → ℝ}
    {U : ℝ → ℝ → QubitMatrix} {T : ℝ} (hU : IsQubitEvolution ux uy U T) :
    Tendsto (fun δ =>
      (1 - (Matrix.trace ((blochRotation (U 0 T)).transpose * blochRotation (U δ T)) + 3) / 6) / δ ^ 2)
      (𝓝[≠] 0) (𝓝 (‖∫ t in 0..T, noiseVec (U 0 t)‖ ^ 2 / 6)) := by
  simpa only [blochRotation_fidelity hU, one_pow, one_mul] using avgGateFidelity_sensitivity_limit hU 1

/-- 把单个Pauli像写入三维矩阵的一列的连续线性映射。 -/
def rotationColumnCLM (j : Fin 3) : QubitMatrix →L[ℝ] QubitBlochMatrix :=
  LinearMap.toContinuousLinearMap {
    toFun := fun A i k => if k = j then pauliCoordinates A i else 0
    map_add' := by
      intro A B
      ext i k
      change (if k = j then pauliCoordinates (A + B) i else 0) =
        (if k = j then pauliCoordinates A i else 0) + (if k = j then pauliCoordinates B i else 0)
      by_cases h : k = j
      · fin_cases i <;> simp [h, pauliCoordinates] <;> ring
      · simp [h]
    map_smul' := by
      intro r A
      ext i k
      change (if k = j then pauliCoordinates (r • A) i else 0) =
        r * (if k = j then pauliCoordinates A i else 0)
      by_cases h : k = j
      · fin_cases i <;> simp [h, pauliCoordinates, Complex.real_smul] <;> ring
      · simp [h] }

@[simp] theorem rotationColumnCLM_apply (j : Fin 3) (A : QubitMatrix) (i k : Fin 3) :
    rotationColumnCLM j A i k = if k = j then pauliCoordinates A i else 0 := rfl

theorem blochRotation_eq_columns (U : QubitMatrix) :
    blochRotation U =
      rotationColumnCLM 0 (U * sigmaX * U.conjTranspose) +
      rotationColumnCLM 1 (U * sigmaY * U.conjTranspose) +
      rotationColumnCLM 2 (U * sigmaZ * U.conjTranspose) := by
  ext i j
  fin_cases j <;> simp [blochRotation, pauliBasis]

theorem blochRotation_ac {U : ℝ → QubitMatrix} {p q : ℝ}
    (hU : AbsolutelyContinuousOnInterval U p q) :
    AbsolutelyContinuousOnInterval (fun t => blochRotation (U t)) p q := by
  have hp (P : QubitMatrix) : AbsolutelyContinuousOnInterval
      (fun t => U t * P * (U t).conjTranspose) p q := by
    exact ac_mul (ac_mul hU
      ((LipschitzWith.const P).lipschitzOnWith.absolutelyContinuousOnInterval)) (ac_star hU)
  have hx := (rotationColumnCLM 0).lipschitzWith.comp_absolutelyContinuousOnInterval (hp sigmaX)
  have hy := (rotationColumnCLM 1).lipschitzWith.comp_absolutelyContinuousOnInterval (hp sigmaY)
  have hz := (rotationColumnCLM 2).lipschitzWith.comp_absolutelyContinuousOnInterval (hp sigmaZ)
  apply ((hx.add hy).add hz).congr
  intro t _
  exact (blochRotation_eq_columns (U t)).symm

theorem hasDerivAt_conjugatedPauli {U : ℝ → QubitMatrix} {G : QubitMatrix} {t : ℝ}
    (hd : HasDerivAt U (G * U t) t) (hG : star G = -G) (P : QubitMatrix) :
    HasDerivAt (fun s => U s * P * (U s).conjTranspose)
      (G * (U t * P * (U t).conjTranspose) - (U t * P * (U t).conjTranspose) * G) t := by
  have h := (hd.mul_const P).mul hd.star
  apply h.congr_deriv
  simp only [star_mul, hG, mul_neg, Matrix.star_eq_conjTranspose]
  noncomm_ring

theorem pauliCoordinates_commutator (ux uy δ : ℝ) (A : QubitMatrix) :
    pauliCoordinates ((transverseGenerator ux uy + δ • detuningGenerator) * A -
      A * (transverseGenerator ux uy + δ • detuningGenerator)) =
      (FrontierNoise.rotationGenerator ux uy δ).mulVec (pauliCoordinates A) := by
  ext i
  fin_cases i <;>
    simp [pauliCoordinates, transverseGenerator, detuningGenerator, sigmaX, sigmaY, sigmaZ,
      FrontierNoise.rotationGenerator, Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_two, Fin.sum_univ_succ, Complex.real_smul,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem rotationColumnCLM_commutator (j : Fin 3) (ux uy δ : ℝ) (A : QubitMatrix) :
    rotationColumnCLM j ((transverseGenerator ux uy + δ • detuningGenerator) * A -
      A * (transverseGenerator ux uy + δ • detuningGenerator)) =
      FrontierNoise.rotationGenerator ux uy δ * rotationColumnCLM j A := by
  ext i k
  by_cases hk : k = j
  · subst k
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using
      congrFun (pauliCoordinates_commutator ux uy δ A) i
  · simp [Matrix.mul_apply, hk]

theorem hasDerivAt_blochRotation {U : ℝ → QubitMatrix} {ux uy δ t : ℝ}
    (hd : HasDerivAt U ((transverseGenerator ux uy + δ • detuningGenerator) * U t) t) :
    HasDerivAt (fun s => blochRotation (U s))
      (FrontierNoise.rotationGenerator ux uy δ * blochRotation (U t)) t := by
  have hG : star (transverseGenerator ux uy + δ • detuningGenerator) =
      -(transverseGenerator ux uy + δ • detuningGenerator) := by
    simp only [star_add, star_smul, star_trivial, Matrix.star_eq_conjTranspose,
      transverseGenerator_skew, detuningGenerator_skew, smul_neg, neg_add_rev]
    abel
  have hx := (rotationColumnCLM 0).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_conjugatedPauli hd hG sigmaX)
  have hy := (rotationColumnCLM 1).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_conjugatedPauli hd hG sigmaY)
  have hz := (rotationColumnCLM 2).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_conjugatedPauli hd hG sigmaZ)
  have h := (hx.add hy).add hz
  simp only [rotationColumnCLM_commutator, ← mul_add, ← blochRotation_eq_columns] at h
  apply h.congr_of_eventuallyEq
  filter_upwards with s
  exact blochRotation_eq_columns (U s)

/-- 原2×2失谐ODE诱导真实3×3Bloch ODE，包含AC与初始矩阵条件。 -/
theorem blochRotation_isACSolution {ux uy : ℝ → ℝ}
    {U : ℝ → ℝ → QubitMatrix} {T : ℝ} (hU : IsQubitEvolution ux uy U T) (δ : ℝ) :
    IsACSolution (fun t => FrontierNoise.rotationGenerator (ux t) (uy t) δ)
      (fun t => blochRotation (U δ t)) T := by
  refine ⟨blochRotation_ac (hU δ).ac, ?_, ?_⟩
  · rw [(hU δ).initial, blochRotation_one]
  · filter_upwards [(hU δ).equation] with t ht htI
    exact hasDerivAt_blochRotation (ht htI)

def blochTraceCLM : QubitBlochMatrix →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 3) ℝ ℝ)

@[simp] theorem blochTraceCLM_apply (M : QubitBlochMatrix) :
    blochTraceCLM M = Matrix.trace M := rfl

theorem bloch_static_first_trace_zero {ux uy : ℝ → ℝ}
    {U : ℝ → ℝ → QubitMatrix} {T : ℝ} (hU : IsQubitEvolution ux uy U T) :
    Matrix.trace (FrontierDyson.word (fun t => blochRotation (U 0 t))
      [FrontierNoise.rotationGenerator 0 0 1] T) = 0 := by
  let O : ℝ → QubitBlochMatrix := fun t => blochRotation (U 0 t)
  let B : QubitBlochMatrix := FrontierNoise.rotationGenerator 0 0 1
  have hO := blochRotation_isACSolution hU 0
  change blochTraceCLM (∫ s in 0..T, FrontierDyson.kernel O B s * 1) = 0
  simp only [mul_one]
  rw [← blochTraceCLM.intervalIntegral_comp_comm
    (FrontierDyson.continuousOn_kernel hO B).intervalIntegrable]
  calc
    _ = ∫ s in 0..T, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hu := blochRotation_unitary (U 0 t) (qubit_unitary hU 0 ht)
      change Matrix.trace (star (O t) * B * O t) = 0
      rw [Matrix.trace_mul_cycle, hu.2, one_mul]
      simp [B, FrontierNoise.rotationGenerator, Matrix.trace, Fin.sum_univ_succ]
    _ = 0 := by simp

/-- 原2×2传播子对应的Dyson静态二阶有序积分系数。 -/
def blochStaticDysonCoefficient (U : ℝ → ℝ → QubitMatrix) (T : ℝ) : ℝ :=
  -Matrix.trace (FrontierDyson.word (fun t => blochRotation (U 0 t))
    [FrontierNoise.rotationGenerator 0 0 1, FrontierNoise.rotationGenerator 0 0 1] T) / 6

/-- 用实际ODE导出的三阶余项界识别静态二阶系数。 -/
theorem blochStaticDysonCoefficient_limit {ux uy : ℝ → ℝ}
    {U : ℝ → ℝ → QubitMatrix} {T : ℝ} (hU : IsQubitEvolution ux uy U T) :
    Tendsto (fun δ =>
      (1 - (Matrix.trace ((blochRotation (U 0 T)).transpose * blochRotation (U δ T)) + 3) / 6) / δ ^ 2)
      (𝓝[≠] 0) (𝓝 (blochStaticDysonCoefficient U T)) := by
  let O : ℝ → ℝ → QubitBlochMatrix := fun δ t => blochRotation (U δ t)
  let G : ℝ → QubitBlochMatrix := fun t => FrontierNoise.rotationGenerator (ux t) (uy t) 0
  let B : QubitBlochMatrix := FrontierNoise.rotationGenerator 0 0 1
  let W₁ := FrontierDyson.word (O 0) [B] T
  let W₂ := FrontierDyson.word (O 0) [B,B] T
  let R : ℝ → QubitBlochMatrix := fun δ => FrontierDyson.frame (O 0) (O δ) T -
    (1 + δ • W₁ + δ ^ 2 • W₂)
  have hO : IsACSolution G (O 0) T := blochRotation_isACSolution hU 0
  have hV (δ : ℝ) : IsACSolution (fun t => G t + δ • B) (O δ) T := by
    simpa only [G, B, ← FrontierNoise.rotationGenerator_detuning] using blochRotation_isACSolution hU δ
  have hG : ∀ᵐ t, t ∈ uIcc 0 T → star (G t) = -G t :=
    Filter.Eventually.of_forall (fun t _ => FrontierNoise.rotationGenerator_skew _ _ _)
  have hnorm (δ : ℝ) : ∀ t ∈ uIcc 0 T, ‖O δ t‖ ≤ (1 : ℝ) := by
    intro t ht
    have hu := blochRotation_unitary (U δ t) (qubit_unitary hU δ ht)
    have hn := CStarRing.norm_mem_unitary_mul (1 : QubitBlochMatrix) hu
    simpa only [mul_one, norm_one] using hn.le
  have hW₁ : Matrix.trace W₁ = 0 := bloch_static_first_trace_zero hU
  have hsum (δ : ℝ) :
      (∑ i ∈ Finset.range 3, FrontierDyson.term (FrontierDyson.kernel (O 0) (δ • B)) i T) =
        1 + δ • W₁ + δ ^ 2 • W₂ := by
    have h1 := FrontierDyson.term_one_expansion (B := B) (D := (0 : QubitBlochMatrix))
      (δ := δ) (Γ := 0) hO right_mem_uIcc
    have h2 := FrontierDyson.term_two_expansion (B := B) (D := (0 : QubitBlochMatrix))
      (δ := δ) (Γ := 0) hO right_mem_uIcc
    simp only [zero_smul, add_zero, mul_zero, zero_pow (by decide : 2 ≠ 0)] at h1 h2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [h1, h2]
    rfl
  have hR (δ : ℝ) : ‖R δ‖ ≤ (‖B‖ * |T|) ^ 3 * ‖δ ^ 3‖ := by
    have h := FrontierDyson.norm_dyson_remainder_le hO (hV δ) hG (hnorm δ) 3
    rw [hsum δ, one_mul] at h
    calc
      ‖R δ‖ ≤ (‖δ • B‖ * |T|) ^ 3 := h
      _ = (‖B‖ * |T|) ^ 3 * ‖δ ^ 3‖ := by
        rw [norm_smul, norm_pow, Real.norm_eq_abs]
        ring
  have hbig : (fun δ => blochTraceCLM (R δ)) =O[𝓝 (0 : ℝ)] (fun δ : ℝ => δ ^ 3) := by
    apply Asymptotics.IsBigO.of_bound (‖blochTraceCLM‖ * (‖B‖ * |T|) ^ 3)
    filter_upwards with δ
    calc
      ‖blochTraceCLM (R δ)‖ ≤ ‖blochTraceCLM‖ * ‖R δ‖ := blochTraceCLM.le_opNorm _
      _ ≤ ‖blochTraceCLM‖ * ((‖B‖ * |T|) ^ 3 * ‖δ ^ 3‖) :=
        mul_le_mul_of_nonneg_left (hR δ) (norm_nonneg blochTraceCLM)
      _ = _ := by ring
  have hsmall := hbig.trans_isLittleO
    (Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (m := 2) (n := 3) (by decide))
  have hlim : Tendsto (fun δ => blochTraceCLM (R δ) / δ ^ 2) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    hsmall.tendsto_div_nhds_zero.mono_left nhdsWithin_le_nhds
  have htrace (δ : ℝ) : blochTraceCLM (R δ) =
      Matrix.trace ((O 0 T).transpose * O δ T) - 3 - δ ^ 2 * Matrix.trace W₂ := by
    simp only [R, blochTraceCLM_apply, FrontierDyson.frame, Matrix.trace_sub,
      Matrix.trace_add, Matrix.trace_smul, hW₁, smul_eq_mul, mul_zero, add_zero]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat]
    ring
  have hh := (tendsto_const_nhds (x := blochStaticDysonCoefficient U T)).sub (hlim.div_const 6)
  simp only [zero_div, sub_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ0 : δ ≠ 0 := hδ
  rw [htrace]
  change -Matrix.trace W₂ / 6 -
    ((Matrix.trace ((O 0 T).transpose * O δ T) - 3 - δ ^ 2 * Matrix.trace W₂) / δ ^ 2) / 6 = _
  dsimp only [O]
  field_simp [hδ0]
  <;> ring

/-- Dyson的静态二阶迹系数等于已证明的原模型噪声积分系数。 -/
theorem blochStaticDysonCoefficient_eq {ux uy : ℝ → ℝ}
    {U : ℝ → ℝ → QubitMatrix} {T : ℝ} (hU : IsQubitEvolution ux uy U T) :
    blochStaticDysonCoefficient U T = ‖∫ t in 0..T, noiseVec (U 0 t)‖ ^ 2 / 6 :=
  tendsto_nhds_unique (blochStaticDysonCoefficient_limit hU) (blochRotation_sensitivity_limit hU)

theorem blochStaticDysonCoefficient_scaled {ux uy : ℝ → ℝ}
    {U : ℝ → ℝ → QubitMatrix} {T : ℝ} (hU : IsQubitEvolution ux uy U T) (Ω : ℝ) :
    Ω ^ 2 * blochStaticDysonCoefficient U T = detuningSensitivity U Ω T := by
  rw [blochStaticDysonCoefficient_eq hU, detuningSensitivity_eq hU]
  ring

end
end RobustPiGate.Quantum

#print axioms RobustPiGate.Quantum.blochRotation_isACSolution
#print axioms RobustPiGate.Quantum.blochRotation_fidelity
#print axioms RobustPiGate.Quantum.blochStaticDysonCoefficient_eq
#print axioms RobustPiGate.Quantum.blochStaticDysonCoefficient_scaled
