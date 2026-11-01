import RobustPiGate.Quantum
import RobustPiGate.Dynamics

noncomputable section
open MeasureTheory Set Filter
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator Topology Interval
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace RobustPiGate.Quantum

theorem transverseGenerator_eq_pauli (ax ay : ℝ) :
    transverseGenerator ax ay = (-Complex.I / 2) • pauli ax ay 0 := by
  simp [transverseGenerator, pauli_eq]

/-- 任意横向轴的真实二阶矩阵旋转。 -/
def axisRotation (ax ay θ : ℝ) : QubitMatrix :=
  Real.cos (θ / 2) • (1 : QubitMatrix) +
    Real.sin (θ / 2) • ((-Complex.I) • pauli ax ay 0)

def rotatedShort (ax ay t : ℝ) : QubitMatrix := axisRotation ax ay (shortPhase t)

theorem axisRotation_zero (ax ay : ℝ) : axisRotation ax ay 0 = 1 := by
  simp [axisRotation]

theorem hasDerivAt_axisRotation {ax ay : ℝ} (haxis : ax ^ 2 + ay ^ 2 = 1) (θ : ℝ) :
    HasDerivAt (axisRotation ax ay)
      (transverseGenerator ax ay * axisRotation ax ay θ) θ := by
  have ht : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) θ := (hasDerivAt_id θ).div_const 2
  have hd := (ht.cos.smul_const (1 : QubitMatrix)).add
    (ht.sin.smul_const ((-Complex.I) • pauli ax ay 0))
  have haxisC : (ax : ℂ) ^ 2 + (ay : ℂ) ^ 2 = 1 := by exact_mod_cast haxis
  have heq : (-Real.sin (θ / 2) * (1 / 2)) • (1 : QubitMatrix) +
      (Real.cos (θ / 2) * (1 / 2)) • ((-Complex.I) • pauli ax ay 0) =
      transverseGenerator ax ay * axisRotation ax ay θ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [transverseGenerator_eq_pauli, axisRotation, pauli, Matrix.mul_apply,
        Fin.sum_univ_two, Complex.real_smul, -Complex.ofReal_sin, -Complex.ofReal_cos] <;>
      push_cast <;> ring_nf <;> simp [Complex.I_sq] <;>
      first | (solve | ring) |
        linear_combination -(Complex.sin ((θ : ℂ) * (2 : ℂ)⁻¹)) / 2 * haxisC
  exact hd.congr_deriv heq

theorem axisRotation_conjugates_z {ax ay : ℝ}
    (haxis : ax ^ 2 + ay ^ 2 = 1) (θ : ℝ) :
    (axisRotation ax ay θ).conjTranspose * sigmaZ * axisRotation ax ay θ =
      pauli (-ay * Real.sin θ) (ax * Real.sin θ) (Real.cos θ) := by
  have haxisC : (ax : ℂ) ^ 2 + (ay : ℂ) ^ 2 = 1 := by exact_mod_cast haxis
  have hsin : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    convert Real.sin_two_mul (θ / 2) using 1
    congr 1
    ring
  have hcos : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
    convert Real.cos_two_mul' (θ / 2) using 1
    congr 1
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [axisRotation, Matrix.conjTranspose_apply, pauli, sigmaZ, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.real_smul, hsin, hcos,
      -Complex.ofReal_sin, -Complex.ofReal_cos] <;>
    push_cast <;> ring_nf <;> simp [Complex.I_sq] <;>
    first | (solve | ring) |
      (solve | linear_combination -(Complex.sin ((θ : ℂ) * (2 : ℂ)⁻¹)) ^ 2 * haxisC) |
      linear_combination (Complex.sin ((θ : ℂ) * (2 : ℂ)⁻¹)) ^ 2 * haxisC

theorem rotatedShort_initial (ax ay : ℝ) : rotatedShort ax ay 0 = 1 := by
  rw [rotatedShort, shortPhase_initial, axisRotation_zero]

theorem rotatedShort_terminal (ax ay : ℝ) :
    rotatedShort ax ay (7 * Real.pi / 3) = Complex.I • pauli ax ay 0 := by
  simp [rotatedShort, shortPhase_final, axisRotation, neg_div]

theorem rotatedShort_ac (ax ay a b : ℝ) :
    AbsolutelyContinuousOnInterval (rotatedShort ax ay) a b := by
  have hp : AbsolutelyContinuousOnInterval shortPhase a b :=
    shortPhase_lipschitz.lipschitzOnWith.absolutelyContinuousOnInterval
  have hh : AbsolutelyContinuousOnInterval (fun t => shortPhase t / 2) a b := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hp.const_mul (1 / 2)
  have hc := Real.lipschitzWith_cos.comp_absolutelyContinuousOnInterval hh
  have hs := Real.lipschitzWith_sin.comp_absolutelyContinuousOnInterval hh
  have hI : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : QubitMatrix)) a b :=
    (LipschitzWith.const (1 : QubitMatrix)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hP : AbsolutelyContinuousOnInterval (fun _ : ℝ => (-Complex.I) • pauli ax ay 0) a b :=
    (LipschitzWith.const ((-Complex.I) • pauli ax ay 0)).lipschitzOnWith.absolutelyContinuousOnInterval
  exact (hc.smul hI).add (hs.smul hP)

theorem rotatedShort_ae_ode {ax ay : ℝ} (haxis : ax ^ 2 + ay ^ 2 = 1) :
    ∀ᵐ t : ℝ, HasDerivAt (rotatedShort ax ay)
      (transverseGenerator (ax * shortControl t) (ay * shortControl t) * rotatedShort ax ay t) t := by
  filter_upwards [volume.ae_ne (Real.pi / 3), volume.ae_ne (2 * Real.pi)] with t h₁ h₂
  have hd := (hasDerivAt_axisRotation haxis (shortPhase t)).scomp t (hasDerivAt_shortPhase h₁ h₂)
  have heq : shortControl t • (transverseGenerator ax ay * axisRotation ax ay (shortPhase t)) =
      transverseGenerator (ax * shortControl t) (ay * shortControl t) * rotatedShort ax ay t := by
    have hscale : shortControl t • transverseGenerator ax ay =
        transverseGenerator (ax * shortControl t) (ay * shortControl t) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [transverseGenerator_eq_pauli, pauli, Complex.real_smul] <;> ring
    rw [← smul_mul_assoc, hscale]
    rfl
  exact hd.congr_deriv heq

theorem rotatedShort_solution {ax ay : ℝ} (haxis : ax ^ 2 + ay ^ 2 = 1) (T : ℝ) :
    Dynamics.IsACSolution
      (fun t => transverseGenerator (ax * shortControl t) (ay * shortControl t))
      (rotatedShort ax ay) T :=
  ⟨rotatedShort_ac ax ay 0 T, rotatedShort_initial ax ay,
    (rotatedShort_ae_ode haxis).mono (fun _ ht _ => ht)⟩

theorem rotatedShort_unitary {ax ay : ℝ} (haxis : ax ^ 2 + ay ^ 2 = 1) (t : ℝ) :
    rotatedShort ax ay t ∈ unitary QubitMatrix := by
  apply (rotatedShort_solution haxis t).unitary
  · exact Filter.Eventually.of_forall fun s _ => transverseGenerator_skew _ _
  · exact right_mem_uIcc

end RobustPiGate.Quantum

