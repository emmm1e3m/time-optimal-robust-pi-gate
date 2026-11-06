import RobustPiGate.PhysicalMain
import RobustPiGate.FrontierBasic

noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology NNReal Matrix ComplexConjugate Matrix.Norms.L2Operator
namespace RobustPiGate
open Quantum RobustPiGate.Dynamics

/-- 控制为可测且幅度有界，并实现完整目标门；此处不预设鲁棒。 -/
structure AdmissiblePi (Ω : ℝ≥0) (T : ℝ)
    (ux uy : ℝ → ℝ) (U : ℝ → ℝ → QubitMatrix) : Prop where
  nonneg_duration : 0 ≤ T
  measurable_x : AEMeasurable ux (volume.restrict (uIcc 0 T))
  measurable_y : AEMeasurable uy (volume.restrict (uIcc 0 T))
  evolution : IsQubitEvolution ux uy U T
  amplitude : ∀ᵐ t, t ∈ uIcc 0 T → (ux t) ^ 2 + (uy t) ^ 2 ≤ (Ω : ℝ) ^ 2
  gate : U 0 T = rx Real.pi ∨ U 0 T = -rx Real.pi

namespace Quantum

/-- 原传播子的平均门保真度，以无量纲失谐 f=δ/Ω 为变量。 -/
def avgGateFidelity (U : ℝ → ℝ → QubitMatrix) (Ω T f : ℝ) : ℝ :=
  (Complex.normSq (Matrix.trace ((U 0 T).conjTranspose * U (Ω * f) T)) + 2) / 6

/-- 物理敏感度直接定义为保真度的穿孔极限，下面证明该极限存在。 -/
def detuningSensitivity (U : ℝ → ℝ → QubitMatrix) (Ω T : ℝ) : ℝ :=
  limUnder (𝓝[≠] 0) (fun f => (1 - avgGateFidelity U Ω T f) / f ^ 2)

/-- 相对于单位矩阵的无迹部分。 -/
def tracelessPart (M : QubitMatrix) : QubitMatrix :=
  M - (Matrix.trace M / 2) • (1 : QubitMatrix)

def tracelessCLM : QubitMatrix →L[ℝ] QubitMatrix :=
  LinearMap.toContinuousLinearMap {
    toFun := tracelessPart
    map_add' := by
      intro A B
      simp [tracelessPart, add_div, add_smul]
      abel
    map_smul' := by
      intro r A
      ext i j
      simp [tracelessPart, Matrix.trace, Fin.sum_univ_two, Complex.real_smul]
      ring }

/-- 只作代数用途的 Frobenius 平方，避免改变矩阵算子范数实例。 -/
def frobeniusSq (M : QubitMatrix) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (M i j)

theorem frobeniusSq_continuous : Continuous frobeniusSq := by
  unfold frobeniusSq
  fun_prop

theorem frobeniusSq_real_smul (r : ℝ) (M : QubitMatrix) :
    frobeniusSq (r • M) = r ^ 2 * frobeniusSq M := by
  simp [frobeniusSq, Complex.real_smul, Complex.normSq_mul, pow_two]
  ring

@[simp] theorem tracelessPart_one : tracelessPart (1 : QubitMatrix) = 0 := by
  simp [tracelessPart, Matrix.trace]

@[simp] theorem tracelessPart_pauli (x y z : ℝ) :
    tracelessPart (pauli x y z) = pauli x y z := by
  simp [tracelessPart, pauli_trace]

/-- 任意2×2酉矩阵都满足该恒等式，不需要另加行列式条件。 -/
theorem unitary_infidelity_identity (M : QubitMatrix)
    (hM : M.conjTranspose * M = 1) :
    1 - (Complex.normSq (Matrix.trace M) + 2) / 6 =
      frobeniusSq (tracelessPart M) / 3 := by
  have h0 := congrArg (fun A : QubitMatrix => (A 0 0).re) hM
  have h1 := congrArg (fun A : QubitMatrix => (A 1 1).re) hM
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    Complex.mul_re] at h0 h1
  simp [frobeniusSq, tracelessPart, Matrix.trace, Fin.sum_univ_two,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  nlinarith

def pauliCLM : Vec3 →L[ℝ] QubitMatrix :=
  LinearMap.toContinuousLinearMap {
    toFun := fun r => pauli (r 0) (r 1) (r 2)
    map_add' := by
      intro r s
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pauli] <;> ring
    map_smul' := by
      intro c r
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pauli, Complex.real_smul] <;> ring }

theorem qubit_unitary {ux uy : ℝ → ℝ} {U : ℝ → ℝ → QubitMatrix} {T t : ℝ}
    (hU : IsQubitEvolution ux uy U T) (δ : ℝ) (ht : t ∈ uIcc 0 T) :
    U δ t ∈ unitary QubitMatrix := by
  apply (hU δ).unitary _ ht
  filter_upwards with s _
  simp only [star_add, star_smul, star_trivial, Matrix.star_eq_conjTranspose,
    transverseGenerator_skew, detuningGenerator_skew, smul_neg, neg_add_rev]
  abel

theorem noise_integral_eq_pauli {ux uy : ℝ → ℝ} {U : ℝ → ℝ → QubitMatrix} {T : ℝ}
    (hU : IsQubitEvolution ux uy U T) :
    (∫ t in 0..T, noiseMatrix (U 0 t)) =
      pauliCLM (∫ t in 0..T, noiseVec (U 0 t)) := by
  have hi : IntervalIntegrable (fun t => noiseVec (U 0 t)) volume 0 T :=
    (noiseVec_ac (qubit_nominal_solution hU).ac).continuousOn.intervalIntegrable
  rw [← pauliCLM.intervalIntegral_comp_comm hi]
  apply intervalIntegral.integral_congr
  intro t ht
  exact noiseMatrix_eq_pauli _ (qubit_nominal_unitary hU ht).2

/-- 真实相互作用绘景的一阶切向量。 -/
def sensitivityTangent (Ω : ℝ) (r : Vec3) : QubitMatrix :=
  Ω • ((-Complex.I / 2) • pauli (r 0) (r 1) (r 2))

theorem sensitivityTangent_traceless (Ω : ℝ) (r : Vec3) :
    tracelessPart (sensitivityTangent Ω r) = sensitivityTangent Ω r := by
  simp [tracelessPart, sensitivityTangent, pauli_trace]

theorem frobeniusSq_sensitivityTangent (Ω : ℝ) (r : Vec3) :
    frobeniusSq (sensitivityTangent Ω r) = Ω ^ 2 * ‖r‖ ^ 2 / 2 := by
  rw [sensitivityTangent, frobeniusSq_real_smul, EuclideanSpace.real_norm_sq_eq]
  simp [frobeniusSq, pauli, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Fin.sum_univ_succ]
  ring

theorem interaction_hasDerivAt {ux uy : ℝ → ℝ} {U : ℝ → ℝ → QubitMatrix} {T : ℝ}
    (hU : IsQubitEvolution ux uy U T) (Ω : ℝ) :
    HasDerivAt (fun f => (U 0 T).conjTranspose * U (Ω * f) T)
      (sensitivityTangent Ω (∫ t in 0..T, noiseVec (U 0 t))) 0 := by
  have hu : (U 0 T).conjTranspose * U 0 T = 1 :=
    (qubit_nominal_unitary hU (right_mem_uIcc : T ∈ uIcc 0 T)).1
  have hd := (qubit_parameter_hasDerivAt hU).const_mul (U 0 T).conjTranspose
  have he : (U 0 T).conjTranspose *
      ((-Complex.I / 2) • (U 0 T * (∫ t in 0..T, noiseMatrix (U 0 t)))) =
      (-Complex.I / 2) • pauliCLM (∫ t in 0..T, noiseVec (U 0 t)) := by
    rw [mul_smul_comm, ← mul_assoc, hu, one_mul, noise_integral_eq_pauli hU]
  change HasDerivAt (fun δ => (U 0 T).conjTranspose * U δ T) _ 0 at hd
  change HasDerivAt _ ((U 0 T).conjTranspose *
    ((-Complex.I / 2) • (U 0 T * (∫ t in 0..T, noiseMatrix (U 0 t))))) 0 at hd
  rw [he] at hd
  have hl : HasDerivAt (fun f : ℝ => Ω * f) Ω 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul Ω
  have hd' : HasDerivAt (fun δ => (U 0 T).conjTranspose * U δ T)
      ((-Complex.I / 2) • pauliCLM (∫ t in 0..T, noiseVec (U 0 t))) (Ω * 0) := by
    simpa using hd
  exact hd'.scomp 0 hl

theorem interaction_unitary {ux uy : ℝ → ℝ} {U : ℝ → ℝ → QubitMatrix} {T : ℝ}
    (hU : IsQubitEvolution ux uy U T) (δ : ℝ) :
    (U 0 T).conjTranspose * U δ T ∈ unitary QubitMatrix :=
  (unitary QubitMatrix).mul_mem
    (Unitary.star_mem (qubit_nominal_unitary hU right_mem_uIcc))
    (qubit_unitary hU δ right_mem_uIcc)

/-- 原平均门保真度的真实穿孔极限；Ω为任意实数，尤其覆盖所有Ω>0。 -/
theorem avgGateFidelity_sensitivity_limit {ux uy : ℝ → ℝ}
    {U : ℝ → ℝ → QubitMatrix} {T : ℝ}
    (hU : IsQubitEvolution ux uy U T) (Ω : ℝ) :
    Tendsto (fun f => (1 - avgGateFidelity U Ω T f) / f ^ 2)
      (𝓝[≠] 0) (𝓝 (Ω ^ 2 * ‖∫ t in 0..T, noiseVec (U 0 t)‖ ^ 2 / 6)) := by
  let r := ∫ t in 0..T, noiseVec (U 0 t)
  let V := fun f => (U 0 T).conjTranspose * U (Ω * f) T
  have hd : HasDerivAt (fun f => tracelessPart (V f)) (sensitivityTangent Ω r) 0 := by
    have h := tracelessCLM.hasFDerivAt.comp_hasDerivAt 0 (interaction_hasDerivAt hU Ω)
    change HasDerivAt (fun f => tracelessPart (V f))
      (tracelessPart (sensitivityTangent Ω r)) 0 at h
    rw [sensitivityTangent_traceless] at h
    exact h
  have hz : tracelessPart (V 0) = 0 := by
    dsimp [V]
    have hu : (U 0 T).conjTranspose * U 0 T = 1 :=
      (qubit_nominal_unitary hU right_mem_uIcc).1
    rw [mul_zero, hu, tracelessPart_one]
  have hl : Tendsto (fun f : ℝ => f⁻¹ • tracelessPart (V f))
      (𝓝[≠] 0) (𝓝 (sensitivityTangent Ω r)) := by
    simpa only [zero_add, hz, sub_zero] using hd.tendsto_slope_zero
  have hs := (frobeniusSq_continuous.continuousAt.tendsto.comp hl).div_const 3
  rw [frobeniusSq_sensitivityTangent] at hs
  have hv : Ω ^ 2 * ‖r‖ ^ 2 / 2 / 3 = Ω ^ 2 * ‖r‖ ^ 2 / 6 := by ring
  rw [hv] at hs
  apply hs.congr'
  filter_upwards with f
  dsimp only [Function.comp_def]
  rw [frobeniusSq_real_smul]
  have hi := unitary_infidelity_identity (V f) (interaction_unitary hU (Ω * f)).1
  change _ = (1 - (Complex.normSq (Matrix.trace (V f)) + 2) / 6) / f ^ 2
  rw [hi]
  ring

theorem detuningSensitivity_eq {ux uy : ℝ → ℝ} {U : ℝ → ℝ → QubitMatrix} {T : ℝ}
    (hU : IsQubitEvolution ux uy U T) (Ω : ℝ) :
    detuningSensitivity U Ω T = Ω ^ 2 * ‖∫ t in 0..T, noiseVec (U 0 t)‖ ^ 2 / 6 :=
  (avgGateFidelity_sensitivity_limit hU Ω).limUnder_eq

end Quantum

/-- 任何可行门都产生具有正确端点的实际噪声曲线。 -/
theorem AdmissiblePi.noise_curve {Ω T ux uy U} (h : AdmissiblePi Ω T ux uy U) :
    (∀ t ∈ uIcc 0 T, ‖noiseVec (U 0 t)‖ = 1) ∧
    LipschitzOnWith Ω (fun t => noiseVec (U 0 t)) (uIcc 0 T) ∧
    noiseVec (U 0 T) = -noiseVec (U 0 0) := by
  have hnom := qubit_nominal_solution h.evolution
  have hunitary : ∀ t ∈ uIcc 0 T,
      (U 0 t).conjTranspose * U 0 t = 1 ∧ U 0 t * (U 0 t).conjTranspose = 1 := by
    intro t ht
    exact qubit_nominal_unitary h.evolution ht
  have hd : ∀ᵐ t, t ∈ uIcc 0 T →
      HasDerivAt (U 0) ((-Complex.I / 2) • (pauli (ux t) (uy t) 0 * U 0 t)) t := by
    filter_upwards [hnom.equation] with t ht htI
    simpa only [transverseGenerator, pauli_eq, Complex.ofReal_zero, zero_smul,
      add_zero, smul_mul_assoc] using ht htI
  refine ⟨fun t ht => noiseVec_unit _ (hunitary t ht).1 (hunitary t ht).2,
    noiseVec_lipschitz hnom.ac hunitary hd h.amplitude, ?_⟩
  rw [hnom.initial, noiseVec_one]
  exact noiseVec_gate_antipode h.gate

/-- 固定物理时长下，完整可行门的实际敏感度集合。 -/
def piSensitivities (Ω : ℝ≥0) (T : ℝ) : Set ℝ :=
  {χ | ∃ ux uy U, AdmissiblePi Ω T ux uy U ∧ χ = detuningSensitivity U Ω T}
end RobustPiGate

#print axioms RobustPiGate.Quantum.avgGateFidelity_sensitivity_limit
#print axioms RobustPiGate.Quantum.detuningSensitivity_eq
