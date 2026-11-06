import RobustPiGate.FrontierFidelity

noncomputable section
open Real MeasureTheory Set Filter
open scoped Topology Matrix ComplexConjugate Matrix.Norms.L2Operator
namespace RobustPiGate.Quantum
open RobustPiGate.Dynamics

abbrev FrobeniusSpace := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- 把矩阵条目放入欧氏空间，保持原矩阵算子范数实例不变。 -/
def frobeniusCLM : QubitMatrix →L[ℝ] FrobeniusSpace :=
  LinearMap.toContinuousLinearMap {
    toFun := fun M => WithLp.toLp 2 (fun ij => M ij.1 ij.2)
    map_add' := by intros; ext; rfl
    map_smul' := by intros; ext; rfl }

theorem norm_frobeniusCLM_sq (M : QubitMatrix) :
    ‖frobeniusCLM M‖ ^ 2 = frobeniusSq M := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [frobeniusCLM, frobeniusSq, Fintype.sum_prod_type, Complex.normSq_eq_norm_sq]

def tracelessFrobeniusCLM : QubitMatrix →L[ℝ] FrobeniusSpace :=
  frobeniusCLM.comp tracelessCLM

/-- 实际相互作用绘景的统一二阶矩阵余项。 -/
theorem interaction_remainder_le {ux uy : ℝ → ℝ}
    {U : ℝ → ℝ → QubitMatrix} {T : ℝ}
    (hU : IsQubitEvolution ux uy U T) (Ω f : ℝ) :
    ‖(U 0 T).conjTranspose * U (Ω * f) T - 1 -
      f • sensitivityTangent Ω (∫ t in 0..T, noiseVec (U 0 t))‖ ≤
      |f| ^ 2 * (|Ω| * (‖detuningGenerator‖ * |T|)) ^ 2 := by
  have hG : ∀ᵐ t, t ∈ uIcc 0 T →
      star (transverseGenerator (ux t) (uy t)) = -transverseGenerator (ux t) (uy t) :=
    Filter.Eventually.of_forall (fun t _ => transverseGenerator_skew (ux t) (uy t))
  have hrem := norm_solution_remainder_le (qubit_nominal_solution hU)
    (hU (Ω * f)) hG detuningGenerator_skew
  have hu := qubit_nominal_unitary hU right_mem_uIcc
  have hs := Unitary.star_mem hu
  let K := ∫ t in 0..T, star (U 0 t) * detuningGenerator * U 0 t
  have hk : K = (-Complex.I / 2) • pauliCLM (∫ t in 0..T, noiseVec (U 0 t)) := by
    dsimp only [K]
    rw [detuning_integral_eq]
    exact congrArg (fun M : QubitMatrix => (-Complex.I / 2) • M) (noise_integral_eq_pauli hU)
  have he : star (U 0 T) *
      (U (Ω * f) T - U 0 T - (Ω * f) • (U 0 T * K)) =
      (U 0 T).conjTranspose * U (Ω * f) T - 1 -
        f • sensitivityTangent Ω (∫ t in 0..T, noiseVec (U 0 t)) := by
    rw [mul_sub, mul_sub, mul_smul_comm, ← mul_assoc, hu.1, one_mul, hk]
    simp only [sensitivityTangent, ← smul_smul]
    rw [smul_comm]
    rfl
  have hn := CStarRing.norm_mem_unitary_mul
    (U (Ω * f) T - U 0 T - (Ω * f) • (U 0 T * K)) hs
  rw [he] at hn
  rw [hn]
  convert hrem using 1
  simp only [abs_mul, mul_pow]
  ring

private theorem norm_sq_difference_le {E : Type*} [NormedAddCommGroup E] (x y : E) :
    |‖x‖ ^ 2 - ‖y‖ ^ 2| ≤ ‖x - y‖ * (‖x‖ + ‖y‖) := by
  calc
    _ = |‖x‖ - ‖y‖| * (‖x‖ + ‖y‖) := by
      rw [← abs_of_nonneg (add_nonneg (norm_nonneg x) (norm_nonneg y)), ← abs_mul]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le x y) (by positivity)

/-- 二阶向量余项经过平方后产生显式三阶余项，常数不依赖f。 -/
theorem norm_sq_linear_remainder_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x d : E) {C f : ℝ} (hC : 0 ≤ C) (hf : |f| ≤ 1)
    (hr : ‖x - f • d‖ ≤ C * |f| ^ 2) :
    |‖x‖ ^ 2 - f ^ 2 * ‖d‖ ^ 2| ≤ C * (C + 2 * ‖d‖) * |f| ^ 3 := by
  have hx : ‖x‖ ≤ C * |f| ^ 2 + |f| * ‖d‖ := by
    calc
      _ ≤ ‖x - f • d‖ + ‖f • d‖ := norm_le_norm_sub_add _ _
      _ ≤ _ := by rw [norm_smul, Real.norm_eq_abs]; gcongr
  have hf2 : |f| ^ 2 ≤ |f| := by nlinarith [abs_nonneg f]
  calc
    _ = |‖x‖ ^ 2 - ‖f • d‖ ^ 2| := by rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    _ ≤ ‖x - f • d‖ * (‖x‖ + ‖f • d‖) := norm_sq_difference_le _ _
    _ ≤ (C * |f| ^ 2) * (C * |f| ^ 2 + 2 * |f| * ‖d‖) := by
      rw [norm_smul, Real.norm_eq_abs]
      apply mul_le_mul hr ?_ (by positivity) (by positivity)
      linarith
    _ ≤ (C * |f| ^ 2) * (C * |f| + 2 * |f| * ‖d‖) := by gcongr
    _ = _ := by ring

/-- 固定演化区间和幅度尺度下，一个显式且有限的三阶余项常数。 -/
def fidelityCubicConstant (Ω T : ℝ) (r : Vec3) : ℝ :=
  let C := ‖tracelessFrobeniusCLM‖ * (|Ω| * (‖detuningGenerator‖ * |T|)) ^ 2
  C * (C + 2 * ‖frobeniusCLM (sensitivityTangent Ω r)‖) / 3

/-- 原平均门保真度的明确近零三阶余项界，适用于所有真实演化。 -/
theorem avgGateFidelity_cubic_remainder_le {ux uy : ℝ → ℝ}
    {U : ℝ → ℝ → QubitMatrix} {T : ℝ}
    (hU : IsQubitEvolution ux uy U T) (Ω f : ℝ) (hf : |f| ≤ 1) :
    |(1 - avgGateFidelity U Ω T f) -
      (Ω ^ 2 * ‖∫ t in 0..T, noiseVec (U 0 t)‖ ^ 2 / 6) * f ^ 2| ≤
      fidelityCubicConstant Ω T (∫ t in 0..T, noiseVec (U 0 t)) * |f| ^ 3 := by
  let r := ∫ t in 0..T, noiseVec (U 0 t)
  let V := (U 0 T).conjTranspose * U (Ω * f) T
  let D := sensitivityTangent Ω r
  let C := ‖tracelessFrobeniusCLM‖ * (|Ω| * (‖detuningGenerator‖ * |T|)) ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm : tracelessFrobeniusCLM (V - 1 - f • D) =
      frobeniusCLM (tracelessPart V) - f • frobeniusCLM D := by
    rw [map_sub, map_sub, map_smul]
    have h1 : tracelessFrobeniusCLM (1 : QubitMatrix) = 0 := by
      simp [tracelessFrobeniusCLM, tracelessCLM, tracelessPart_one]
    have hd : tracelessFrobeniusCLM D = frobeniusCLM D := by
      change frobeniusCLM (tracelessPart D) = frobeniusCLM D
      rw [sensitivityTangent_traceless]
    rw [h1, sub_zero, hd]
    rfl
  have hr : ‖frobeniusCLM (tracelessPart V) - f • frobeniusCLM D‖ ≤ C * |f| ^ 2 := by
    calc
      _ = ‖tracelessFrobeniusCLM (V - 1 - f • D)‖ := congrArg norm hm.symm
      _ ≤ ‖tracelessFrobeniusCLM‖ * ‖V - 1 - f • D‖ :=
        tracelessFrobeniusCLM.le_opNorm _
      _ ≤ ‖tracelessFrobeniusCLM‖ *
          (|f| ^ 2 * (|Ω| * (‖detuningGenerator‖ * |T|)) ^ 2) :=
        mul_le_mul_of_nonneg_left (interaction_remainder_le hU Ω f) (norm_nonneg _)
      _ = C * |f| ^ 2 := by dsimp [C]; ring
  have hb := norm_sq_linear_remainder_le
    (frobeniusCLM (tracelessPart V)) (frobeniusCLM D) hC hf hr
  have hi : 1 - avgGateFidelity U Ω T f = ‖frobeniusCLM (tracelessPart V)‖ ^ 2 / 3 := by
    rw [norm_frobeniusCLM_sq]
    exact unitary_infidelity_identity V (interaction_unitary hU (Ω * f)).1
  have hd : ‖frobeniusCLM D‖ ^ 2 = Ω ^ 2 * ‖r‖ ^ 2 / 2 := by
    rw [norm_frobeniusCLM_sq, frobeniusSq_sensitivityTangent]
  have he : (1 - avgGateFidelity U Ω T f) - (Ω ^ 2 * ‖r‖ ^ 2 / 6) * f ^ 2 =
      (‖frobeniusCLM (tracelessPart V)‖ ^ 2 - f ^ 2 * ‖frobeniusCLM D‖ ^ 2) / 3 := by
    rw [hi, hd]
    ring
  change |(1 - avgGateFidelity U Ω T f) - (Ω ^ 2 * ‖r‖ ^ 2 / 6) * f ^ 2| ≤ _
  rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  have hb' := div_le_div_of_nonneg_right hb (by norm_num : (0 : ℝ) ≤ 3)
  convert hb' using 1
  dsimp [fidelityCubicConstant, C, D]
  ring

/-- 论文O(f³)记号的实际函数版本，由上面的明确近零界直接推出。 -/
theorem avgGateFidelity_cubic_remainder_isBigO {ux uy : ℝ → ℝ}
    {U : ℝ → ℝ → QubitMatrix} {T : ℝ}
    (hU : IsQubitEvolution ux uy U T) (Ω : ℝ) :
    (fun f => (1 - avgGateFidelity U Ω T f) -
      (Ω ^ 2 * ‖∫ t in 0..T, noiseVec (U 0 t)‖ ^ 2 / 6) * f ^ 2)
      =O[𝓝 0] (fun f : ℝ => f ^ 3) := by
  apply Asymptotics.IsBigO.of_bound (fidelityCubicConstant Ω T (∫ t in 0..T, noiseVec (U 0 t)))
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with f hf
  have hf' : |f| ≤ 1 := by
    simpa only [Real.dist_eq, sub_zero] using (Metric.mem_ball.mp hf).le
  simpa only [Real.norm_eq_abs, abs_pow] using avgGateFidelity_cubic_remainder_le hU Ω f hf'

end RobustPiGate.Quantum

#print axioms RobustPiGate.Quantum.interaction_remainder_le
#print axioms RobustPiGate.Quantum.avgGateFidelity_cubic_remainder_le
#print axioms RobustPiGate.Quantum.avgGateFidelity_cubic_remainder_isBigO
