import RobustPiGate.Dynamics
import RobustPiGate.Quantum

open MeasureTheory Set Filter
open scoped Topology Interval Matrix Matrix.Norms.L2Operator

namespace RobustPiGate.Dynamics
open Quantum

-- 本定义保留原量子ODE；只要求演化AC，方程几乎处处成立。
def IsQubitEvolution (ux uy : ℝ → ℝ) (U : ℝ → ℝ → QubitMatrix) (T : ℝ) : Prop :=
  ∀ δ, IsACSolution
    (fun t => transverseGenerator (ux t) (uy t) + δ • detuningGenerator) (U δ) T

theorem qubit_generator_model (ux uy δ : ℝ) :
    transverseGenerator ux uy + δ • detuningGenerator =
      (-Complex.I / 2) • ((ux : ℂ) • sigmaX + (uy : ℂ) • sigmaY + (δ : ℂ) • sigmaZ) := by
  simp only [transverseGenerator, detuningGenerator, smul_add]
  congr 1
  ext i j
  simp [Complex.real_smul]
  ring

theorem qubit_nominal_solution {ux uy : ℝ → ℝ} {U : ℝ → ℝ → QubitMatrix} {T : ℝ}
    (hU : IsQubitEvolution ux uy U T) :
    IsACSolution (fun t => transverseGenerator (ux t) (uy t)) (U 0) T := by
  simpa using hU 0

theorem qubit_nominal_unitary {ux uy : ℝ → ℝ} {U : ℝ → ℝ → QubitMatrix} {T t : ℝ}
    (hU : IsQubitEvolution ux uy U T) (ht : t ∈ uIcc 0 T) : U 0 t ∈ unitary QubitMatrix := by
  apply (qubit_nominal_solution hU).unitary _ ht
  exact Filter.Eventually.of_forall (fun s _ => transverseGenerator_skew (ux s) (uy s))

theorem detuning_integral_eq (V : ℝ → QubitMatrix) (T : ℝ) :
    (∫ t in 0..T, star (V t) * detuningGenerator * V t) =
      (-Complex.I / 2) • (∫ t in 0..T, (V t).conjTranspose * sigmaZ * V t) := by
  simp_rw [detuningGenerator, mul_smul_comm, smul_mul_assoc, Matrix.star_eq_conjTranspose]
  exact intervalIntegral.integral_smul _ _

-- 式(variation)直接在真实2×2矩阵模型中成立。
theorem qubit_parameter_hasDerivAt {ux uy : ℝ → ℝ} {U : ℝ → ℝ → QubitMatrix} {T : ℝ}
    (hU : IsQubitEvolution ux uy U T) :
    HasDerivAt (fun δ => U δ T)
      ((-Complex.I / 2) • (U 0 T * (∫ t in 0..T,
        (U 0 t).conjTranspose * sigmaZ * U 0 t))) 0 := by
  have hG : ∀ᵐ t, t ∈ uIcc 0 T →
      star (transverseGenerator (ux t) (uy t)) = -transverseGenerator (ux t) (uy t) :=
    Filter.Eventually.of_forall (fun t _ => transverseGenerator_skew (ux t) (uy t))
  have h := parameter_hasDerivAt hU hG detuningGenerator_skew
  simpa only [detuning_integral_eq, mul_smul_comm] using h

-- 此处的deriv不会利用不可导时默认等于0的约定：上一条已证明实际可导。
theorem qubit_first_order_robust_iff {ux uy : ℝ → ℝ} {U : ℝ → ℝ → QubitMatrix} {T : ℝ}
    (hU : IsQubitEvolution ux uy U T) :
    deriv (fun δ => U δ T) 0 = 0 ↔
      (∫ t in 0..T, (U 0 t).conjTranspose * sigmaZ * U 0 t) = 0 := by
  have hG : ∀ᵐ t, t ∈ uIcc 0 T →
      star (transverseGenerator (ux t) (uy t)) = -transverseGenerator (ux t) (uy t) :=
    Filter.Eventually.of_forall (fun t _ => transverseGenerator_skew (ux t) (uy t))
  rw [first_order_robust_iff hU hG detuningGenerator_skew, detuning_integral_eq]
  have hc : (-Complex.I / 2 : ℂ) ≠ 0 := by simp
  simp only [smul_eq_zero, hc, false_or]

end RobustPiGate.Dynamics
