import RobustPiGate.FrontierAverage
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory

namespace RobustPiGate.FrontierAverage

/-- 对称有限四阶矩分布的Mathlib方差正好为其二阶矩。 -/
theorem variance_id_of_symmetric_fourth {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hs : SymmetricLaw μ) (h4 : Integrable (fun x : ℝ => x ^ 4) μ) :
    ProbabilityTheory.variance (fun x : ℝ => x) μ = ∫ x : ℝ, x ^ 2 ∂μ := by
  exact ProbabilityTheory.variance_of_integral_eq_zero measurable_id.aemeasurable
    (mean_zero_of_symmetric_fourth hs h4)

/-- 正文联合缩放δ=ηξ的真实方差；无需额外零均值前提。 -/
theorem variance_scaled_of_symmetric_fourth {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hs : SymmetricLaw μ) (h4 : Integrable (fun x : ℝ => x ^ 4) μ) (η : ℝ) :
    ProbabilityTheory.variance (fun x : ℝ => η * x) μ =
      η ^ 2 * (∫ x : ℝ, x ^ 2 ∂μ) := by
  rw [ProbabilityTheory.variance_const_mul, variance_id_of_symmetric_fourth hs h4]

/-- 缩放后失谐仍具有有限二阶矩，方差不涉及无穷值截断。 -/
lemma integrable_sq_scaled_of_fourth {μ : Measure ℝ} [IsFiniteMeasure μ]
    (h4 : Integrable (fun x : ℝ => x ^ 4) μ) (η : ℝ) :
    Integrable (fun x : ℝ => (η * x) ^ 2) μ := by
  simpa only [mul_pow] using
    (integrable_pow_of_fourth h4 (n := 2) (by norm_num)).const_mul (η ^ 2)

end RobustPiGate.FrontierAverage
