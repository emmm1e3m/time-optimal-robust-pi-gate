import RobustPiGate.ShortEvolution

open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator
open Real MeasureTheory Set

namespace RobustPiGate.Quantum

noncomputable section

-- Z 共轭翻转两个横向控制，并保持真实失谐项不变。
def zConjugate (A : QubitMatrix) : QubitMatrix := sigmaZ * A * sigmaZ

theorem sigmaZ_square : sigmaZ * sigmaZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem sigmaZ_star : star sigmaZ = sigmaZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaZ, Matrix.star_eq_conjTranspose]

theorem sigmaZ_unitary : sigmaZ ∈ unitary QubitMatrix := by
  exact ⟨by rw [sigmaZ_star, sigmaZ_square], by rw [sigmaZ_star, sigmaZ_square]⟩

theorem zConjugate_unitary {A : QubitMatrix} (hA : A ∈ unitary QubitMatrix) :
    zConjugate A ∈ unitary QubitMatrix :=
  (unitary QubitMatrix).mul_mem ((unitary QubitMatrix).mul_mem sigmaZ_unitary hA) sigmaZ_unitary

theorem z_generator_intertwine (ux uy δ : ℝ) :
    sigmaZ * (transverseGenerator ux uy + δ • detuningGenerator) =
      (transverseGenerator (-ux) (-uy) + δ • detuningGenerator) * sigmaZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transverseGenerator, detuningGenerator, sigmaX, sigmaY, sigmaZ,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul] <;> ring

theorem zConjugate_generator_mul (ux uy δ : ℝ) (A : QubitMatrix) :
    zConjugate ((transverseGenerator ux uy + δ • detuningGenerator) * A) =
      (transverseGenerator (-ux) (-uy) + δ • detuningGenerator) * zConjugate A := by
  unfold zConjugate
  rw [← mul_assoc sigmaZ, z_generator_intertwine]
  simp only [mul_assoc]

theorem zConjugate_ac {U : ℝ → QubitMatrix} {a b : ℝ}
    (hU : AbsolutelyContinuousOnInterval U a b) :
    AbsolutelyContinuousOnInterval (fun t => zConjugate (U t)) a b := by
  have hZ : AbsolutelyContinuousOnInterval (fun _ : ℝ => sigmaZ) a b :=
    (LipschitzWith.const sigmaZ).lipschitzOnWith.absolutelyContinuousOnInterval
  exact Dynamics.ac_mul (Dynamics.ac_mul hZ hU) hZ

theorem z_conjugate_isQubitEvolution {ux uy : ℝ → ℝ}
    {U : ℝ → ℝ → QubitMatrix} {T : ℝ}
    (hU : Dynamics.IsQubitEvolution ux uy U T) :
    Dynamics.IsQubitEvolution (fun t => -ux t) (fun t => -uy t)
      (fun δ t => zConjugate (U δ t)) T := by
  intro δ
  refine {
    ac := zConjugate_ac (hU δ).ac
    initial := ?_
    equation := ?_
  }
  · simp only [zConjugate, (hU δ).initial, mul_one, sigmaZ_square]
  · filter_upwards [(hU δ).equation] with t ht htI
    have hd := ((ht htI).const_mul sigmaZ).mul_const sigmaZ
    change HasDerivAt (fun s => zConjugate (U δ s))
      (zConjugate ((transverseGenerator (ux t) (uy t) + δ • detuningGenerator) * U δ t)) t at hd
    rw [zConjugate_generator_mul] at hd
    exact hd

theorem zConjugate_neg_rx_pi : zConjugate (-rx Real.pi) = rx Real.pi := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zConjugate, rx, sigmaZ, Matrix.mul_apply, Fin.sum_univ_two]

def negativeScaledShortControl (Ω t : ℝ) : ℝ := -scaledShortControl Ω t

def negativeScaledShortPropagator (Ω δ t : ℝ) : QubitMatrix :=
  zConjugate (scaledShortPropagator Ω δ t)

theorem negativeScaledShortControl_measurable (Ω : ℝ) :
    Measurable (negativeScaledShortControl Ω) := (scaledShortControl_measurable Ω).neg

theorem negativeScaledShortControl_amplitude (Ω t : ℝ) :
    negativeScaledShortControl Ω t ^ 2 + (0 : ℝ) ^ 2 ≤ Ω ^ 2 := by
  simpa only [negativeScaledShortControl, neg_sq] using scaledShortControl_amplitude Ω t

theorem negativeScaledShortPropagator_isQubitEvolution {Ω : ℝ} (hΩ : Ω ≠ 0) (T : ℝ) :
    Dynamics.IsQubitEvolution (negativeScaledShortControl Ω) (fun _ => 0)
      (negativeScaledShortPropagator Ω) T := by
  change Dynamics.IsQubitEvolution (fun t => -scaledShortControl Ω t) (fun _ => 0)
    (fun δ t => zConjugate (scaledShortPropagator Ω δ t)) T
  simpa only [neg_zero] using
    z_conjugate_isQubitEvolution (scaledShortPropagator_isQubitEvolution hΩ T)

theorem negativeScaledShortPropagator_unitary (Ω δ t : ℝ) :
    negativeScaledShortPropagator Ω δ t ∈ unitary QubitMatrix :=
  zConjugate_unitary (scaledShortPropagator_unitary Ω δ t)

theorem negativeScaledShortPropagator_gate {Ω : ℝ} (hΩ : Ω ≠ 0) :
    negativeScaledShortPropagator Ω 0 (scaledShortTime Ω) = rx Real.pi := by
  rw [negativeScaledShortPropagator, scaledShortPropagator_gate hΩ, zConjugate_neg_rx_pi]

theorem negativeScaledShortPropagator_first_order_robust {Ω : ℝ} (hΩ : Ω ≠ 0) :
    HasDerivAt (fun δ => negativeScaledShortPropagator Ω δ (scaledShortTime Ω)) 0 0 := by
  change HasDerivAt (fun δ => sigmaZ * scaledShortPropagator Ω δ (scaledShortTime Ω) * sigmaZ) 0 0
  have hd := ((scaledShortPropagator_first_order_robust hΩ).const_mul sigmaZ).mul_const sigmaZ
  simpa only [mul_zero, zero_mul] using hd

-- 负控制是真实可行解，且终门为正号 Rx(π)。
theorem negativeScaledShortPropagator_certificate {Ω : ℝ} (hΩ : 0 < Ω) :
    0 < scaledShortTime Ω ∧
    Measurable (negativeScaledShortControl Ω) ∧
    (∀ t, negativeScaledShortControl Ω t ^ 2 + (0 : ℝ) ^ 2 ≤ Ω ^ 2) ∧
    Dynamics.IsQubitEvolution (negativeScaledShortControl Ω) (fun _ => 0)
      (negativeScaledShortPropagator Ω) (scaledShortTime Ω) ∧
    (∀ δ t, negativeScaledShortPropagator Ω δ t ∈ unitary QubitMatrix) ∧
    negativeScaledShortPropagator Ω 0 (scaledShortTime Ω) = rx Real.pi ∧
    HasDerivAt (fun δ => negativeScaledShortPropagator Ω δ (scaledShortTime Ω)) 0 0 := by
  exact ⟨(scaledShortPropagator_certificate hΩ).1,
    negativeScaledShortControl_measurable Ω, negativeScaledShortControl_amplitude Ω,
    negativeScaledShortPropagator_isQubitEvolution hΩ.ne' _,
    negativeScaledShortPropagator_unitary Ω, negativeScaledShortPropagator_gate hΩ.ne',
    negativeScaledShortPropagator_first_order_robust hΩ.ne'⟩

end
end RobustPiGate.Quantum
