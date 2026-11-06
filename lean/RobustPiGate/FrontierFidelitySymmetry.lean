import RobustPiGate.FrontierFidelity

noncomputable section
open Real MeasureTheory Set Filter
open scoped Topology Matrix ComplexConjugate Matrix.Norms.L2Operator
namespace RobustPiGate.Quantum
open RobustPiGate.Dynamics

/-- X共轭保持单轴控制，并翻转真实失谐。 -/
def xConjugate (A : QubitMatrix) : QubitMatrix := sigmaX * A * sigmaX

theorem sigmaX_square : sigmaX * sigmaX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaX, Matrix.mul_apply, Fin.sum_univ_two]

theorem sigmaX_star : star sigmaX = sigmaX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaX]

theorem sigmaX_unitary : sigmaX ∈ unitary QubitMatrix := by
  exact ⟨by rw [sigmaX_star, sigmaX_square], by rw [sigmaX_star, sigmaX_square]⟩

theorem x_generator_intertwine (ux δ : ℝ) :
    sigmaX * (transverseGenerator ux 0 + δ • detuningGenerator) =
      (transverseGenerator ux 0 + (-δ) • detuningGenerator) * sigmaX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transverseGenerator, detuningGenerator, sigmaX, sigmaY, sigmaZ,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul]

theorem xConjugate_generator_mul (ux δ : ℝ) (A : QubitMatrix) :
    xConjugate ((transverseGenerator ux 0 + δ • detuningGenerator) * A) =
      (transverseGenerator ux 0 + (-δ) • detuningGenerator) * xConjugate A := by
  unfold xConjugate
  rw [← mul_assoc sigmaX, x_generator_intertwine]
  simp only [mul_assoc]

theorem xConjugate_ac {U : ℝ → QubitMatrix} {a b : ℝ}
    (hU : AbsolutelyContinuousOnInterval U a b) :
    AbsolutelyContinuousOnInterval (fun t => xConjugate (U t)) a b := by
  have hX : AbsolutelyContinuousOnInterval (fun _ : ℝ => sigmaX) a b :=
    (LipschitzWith.const sigmaX).lipschitzOnWith.absolutelyContinuousOnInterval
  exact ac_mul (ac_mul hX hU) hX

/-- 共轭后的路径直接满足负失谐的原ODE。 -/
theorem x_conjugate_single_axis_solution {ux : ℝ → ℝ}
    {U : ℝ → ℝ → QubitMatrix} {T : ℝ}
    (hU : IsQubitEvolution ux (fun _ => 0) U T) (δ : ℝ) :
    IsACSolution (fun t => transverseGenerator (ux t) 0 + (-δ) • detuningGenerator)
      (fun t => xConjugate (U δ t)) T := by
  refine { ac := xConjugate_ac (hU δ).ac, initial := ?_, equation := ?_ }
  · simp only [xConjugate, (hU δ).initial, mul_one, sigmaX_square]
  · filter_upwards [(hU δ).equation] with t ht htI
    have hd := ((ht htI).const_mul sigmaX).mul_const sigmaX
    change HasDerivAt (fun s => xConjugate (U δ s))
      (xConjugate ((transverseGenerator (ux t) 0 + δ • detuningGenerator) * U δ t)) t at hd
    rw [xConjugate_generator_mul] at hd
    exact hd

/-- 原ODE唯一性给出精确失谐对称，适用于任意单轴可测控制。 -/
theorem single_axis_detuning_symmetry {ux : ℝ → ℝ}
    {U : ℝ → ℝ → QubitMatrix} {T t : ℝ}
    (hU : IsQubitEvolution ux (fun _ => 0) U T) (δ : ℝ) (ht : t ∈ uIcc 0 T) :
    U (-δ) t = xConjugate (U δ t) := by
  apply (solution_unique (hU (-δ)) (x_conjugate_single_axis_solution hU δ) _ ht).symm
  filter_upwards with s _
  simp only [star_add, star_smul, star_trivial, Matrix.star_eq_conjTranspose,
    transverseGenerator_skew, detuningGenerator_skew, smul_neg, neg_add_rev]
  abel

theorem xConjugate_mul (A B : QubitMatrix) :
    xConjugate (A * B) = xConjugate A * xConjugate B := by
  simp only [xConjugate, mul_assoc]
  rw [← mul_assoc sigmaX sigmaX, sigmaX_square, one_mul]

theorem xConjugate_star (A : QubitMatrix) :
    xConjugate (star A) = star (xConjugate A) := by
  simp only [xConjugate, star_mul, sigmaX_star, mul_assoc]

theorem trace_xConjugate (A : QubitMatrix) : Matrix.trace (xConjugate A) = Matrix.trace A := by
  rw [xConjugate, Matrix.trace_mul_cycle, sigmaX_square, one_mul]

/-- 保真度相对于真实名义传播子取值，因此甚至不需要另加目标门假设。 -/
theorem single_axis_avgGateFidelity_even {ux : ℝ → ℝ}
    {U : ℝ → ℝ → QubitMatrix} {T : ℝ}
    (hU : IsQubitEvolution ux (fun _ => 0) U T) (Ω f : ℝ) :
    avgGateFidelity U Ω T (-f) = avgGateFidelity U Ω T f := by
  have hzero : xConjugate (U 0 T) = U 0 T := by
    simpa only [neg_zero] using (single_axis_detuning_symmetry hU 0 right_mem_uIcc).symm
  have hs : star (U 0 T) = xConjugate (star (U 0 T)) := by
    rw [xConjugate_star, hzero]
  unfold avgGateFidelity
  rw [mul_neg, single_axis_detuning_symmetry hU (Ω * f) right_mem_uIcc]
  change (Complex.normSq (Matrix.trace (star (U 0 T) * xConjugate (U (Ω * f) T))) + 2) / 6 = _
  rw [hs, ← xConjugate_mul, trace_xConjugate]
  rfl

end RobustPiGate.Quantum

#print axioms RobustPiGate.Quantum.single_axis_detuning_symmetry
#print axioms RobustPiGate.Quantum.single_axis_avgGateFidelity_even
