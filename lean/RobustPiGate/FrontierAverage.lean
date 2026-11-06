import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic

open MeasureTheory Filter Asymptotics
open scoped Topology

namespace RobustPiGate.FrontierAverage

/-- 实噪声分布在取负映射下不变。 -/
def SymmetricLaw (μ : Measure ℝ) : Prop :=
  Measure.map (fun x : ℝ => -x) μ = μ

/-- 先将正负失谐配对；这一步不要求样本有界。 -/
noncomputable def pair (q : ℝ → ℝ) (x : ℝ) : ℝ := (q x + q (-x)) / 2

lemma integrable_comp_neg {μ : Measure ℝ} (hs : SymmetricLaw μ)
    {q : ℝ → ℝ} (hq : Integrable q μ) : Integrable (fun x => q (-x)) μ := by
  change Measure.map (fun x : ℝ => -x) μ = μ at hs
  have hqm : Integrable q (Measure.map (fun x : ℝ => -x) μ) := by
    simpa [hs] using hq
  exact hqm.comp_measurable measurable_neg

lemma integral_comp_neg {μ : Measure ℝ} (hs : SymmetricLaw μ)
    {q : ℝ → ℝ} (hq : Integrable q μ) :
    (∫ x, q (-x) ∂μ) = ∫ x, q x ∂μ := by
  change Measure.map (fun x : ℝ => -x) μ = μ at hs
  have hqm : AEStronglyMeasurable q (Measure.map (fun x : ℝ => -x) μ) := by
    simpa [hs] using hq.aestronglyMeasurable
  simpa [hs] using (integral_map measurable_neg.aemeasurable hqm).symm

lemma integrable_pair {μ : Measure ℝ} (hs : SymmetricLaw μ)
    {q : ℝ → ℝ} (hq : Integrable q μ) : Integrable (pair q) μ :=
  (hq.add (integrable_comp_neg hs hq)).div_const 2

lemma integral_pair {μ : Measure ℝ} (hs : SymmetricLaw μ)
    {q : ℝ → ℝ} (hq : Integrable q μ) :
    (∫ x, pair q x ∂μ) = ∫ x, q x ∂μ := by
  unfold pair
  rw [integral_div, integral_add hq (integrable_comp_neg hs hq), integral_comp_neg hs hq]
  ring

lemma integral_odd_zero {μ : Measure ℝ} (hs : SymmetricLaw μ)
    {q : ℝ → ℝ} (hq : Integrable q μ) (ho : ∀ x, q (-x) = -q x) :
    (∫ x, q x ∂μ) = 0 := by
  have he := integral_comp_neg hs hq
  simp_rw [ho, integral_neg] at he
  linarith

/-- 四阶矩有限蕴含所有更低自然数阶矩可积。 -/
lemma integrable_pow_of_fourth {μ : Measure ℝ} [IsFiniteMeasure μ]
    (h4 : Integrable (fun x : ℝ => x ^ 4) μ) {n : ℕ} (hn : n ≤ 4) :
    Integrable (fun x : ℝ => x ^ n) μ := by
  have h4n : Integrable (fun x : ℝ => ‖x‖ ^ 4) μ := by
    simpa only [Real.norm_eq_abs, (show Even (4 : ℕ) by decide).pow_abs] using h4
  have hn' := integrable_norm_pow_of_le (μ := μ)
    (f := fun x : ℝ => x) continuous_id.aestronglyMeasurable hn h4n
  apply (integrable_norm_iff (by fun_prop)).mp
  simpa only [norm_pow] using hn'

lemma mean_zero_of_symmetric_fourth {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hs : SymmetricLaw μ) (h4 : Integrable (fun x : ℝ => x ^ 4) μ) :
    (∫ x : ℝ, x ∂μ) = 0 := by
  apply integral_odd_zero hs
  · simpa using integrable_pow_of_fourth h4 (n := 1) (by norm_num)
  · simp

lemma third_moment_zero {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hs : SymmetricLaw μ) (h4 : Integrable (fun x : ℝ => x ^ 4) μ) :
    (∫ x : ℝ, x ^ 3 ∂μ) = 0 := by
  exact integral_odd_zero hs (integrable_pow_of_fourth h4 (by norm_num)) (by intro x; ring)

lemma integral_quadratic_budget {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h4 : Integrable (fun x : ℝ => x ^ 4) μ) (η A B : ℝ) :
    (∫ x : ℝ, η ^ 2 * (A * x ^ 2 + B) ∂μ) =
      η ^ 2 * (A * (∫ x : ℝ, x ^ 2 ∂μ) + B) := by
  rw [integral_const_mul, integral_add
    ((integrable_pow_of_fourth h4 (by norm_num)).const_mul A) (integrable_const B),
    integral_const_mul]
  simp

/-- 对称配对后的四阶界可直接积分，常数仅依赖第四矩。 -/
theorem averaged_remainder_bound {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : SymmetricLaw μ) (h4 : Integrable (fun x : ℝ => x ^ 4) μ)
    {q : ℝ → ℝ} (hq : Integrable q μ) (η A B K : ℝ)
    (hb : ∀ x, |pair q x - η ^ 2 * (A * x ^ 2 + B)| ≤
      K * η ^ 4 * (1 + x ^ 4)) :
    |(∫ x, q x ∂μ) - η ^ 2 * (A * (∫ x : ℝ, x ^ 2 ∂μ) + B)| ≤
      K * (1 + ∫ x : ℝ, x ^ 4 ∂μ) * η ^ 4 := by
  have hlead : Integrable (fun x : ℝ => η ^ 2 * (A * x ^ 2 + B)) μ :=
    (((integrable_pow_of_fourth h4 (by norm_num)).const_mul A).add
      (integrable_const B)).const_mul (η ^ 2)
  have hw : Integrable (fun x : ℝ => K * η ^ 4 * (1 + x ^ 4)) μ :=
    ((integrable_const 1).add h4).const_mul (K * η ^ 4)
  have hint := norm_integral_le_of_norm_le
    (f := fun x : ℝ => pair q x - η ^ 2 * (A * x ^ 2 + B)) hw (ae_of_all μ fun x => by
    simpa only [Real.norm_eq_abs] using hb x)
  rw [integral_sub (integrable_pair hs hq) hlead, integral_pair hs hq,
    integral_quadratic_budget h4 η A B] at hint
  have hwval : (∫ x : ℝ, K * η ^ 4 * (1 + x ^ 4) ∂μ) =
      K * (1 + ∫ x : ℝ, x ^ 4 ∂μ) * η ^ 4 := by
    rw [integral_const_mul, integral_add (integrable_const 1) h4]
    simp
    ring
  simpa only [Real.norm_eq_abs, hwval] using hint

/-- 从点态奇次展开得到配对界；odd 可含任意线性及三次混合项。 -/
lemma paired_bound_of_odd_expansion {q odd : ℝ → ℝ} (η A B K : ℝ)
    (ho : ∀ x, odd (-x) = -odd x)
    (hb : ∀ x, |q x - (η ^ 2 * (A * x ^ 2 + B) + odd x)| ≤
      K * η ^ 4 * (1 + x ^ 4)) :
    ∀ x, |pair q x - η ^ 2 * (A * x ^ 2 + B)| ≤
      K * η ^ 4 * (1 + x ^ 4) := by
  intro x
  have hp := hb x
  have hm := hb (-x)
  have hn2 : (-x) ^ 2 = x ^ 2 := by ring
  have hn4 : (-x) ^ 4 = x ^ 4 := by ring
  rw [ho, hn2, hn4] at hm

  have he : pair q x - η ^ 2 * (A * x ^ 2 + B) =
      ((q x - (η ^ 2 * (A * x ^ 2 + B) + odd x)) +
       (q (-x) - (η ^ 2 * (A * x ^ 2 + B) + -odd x))) / 2 := by
    unfold pair
    ring
  rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have ht := abs_add_le
    (q x - (η ^ 2 * (A * x ^ 2 + B) + odd x))
    (q (-x) - (η ^ 2 * (A * x ^ 2 + B) + -odd x))
  linarith

/-- 线性和三次系数允许包含η及耗散参数。 -/
lemma odd_linear_cubic (a b : ℝ) :
    ∀ x : ℝ, a * (-x) + b * (-x) ^ 3 = -(a * x + b * x ^ 3) := by
  intro x
  ring

/-- 将统一的点态四阶余项转换为η趋零时的平均大O。 -/
theorem averaged_remainder_isBigO {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : SymmetricLaw μ) (h4 : Integrable (fun x : ℝ => x ^ 4) μ)
    {q : ℝ → ℝ → ℝ} (A B K : ℝ)
    (hq : ∀ᶠ η in 𝓝 (0 : ℝ), Integrable (q η) μ)
    (hb : ∀ᶠ η in 𝓝 (0 : ℝ), ∀ x,
      |pair (q η) x - η ^ 2 * (A * x ^ 2 + B)| ≤ K * η ^ 4 * (1 + x ^ 4)) :
    (fun η => (∫ x, q η x ∂μ) - η ^ 2 * (A * (∫ x : ℝ, x ^ 2 ∂μ) + B))
      =O[𝓝 (0 : ℝ)] (fun η => η ^ 4) := by
  apply IsBigO.of_bound (K * (1 + ∫ x : ℝ, x ^ 4 ∂μ))
  filter_upwards [hq, hb] with η hi he
  have h := averaged_remainder_bound hs h4 hi η A B K he
  simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ η ^ 4)] using h

/-- 低阶绝对矩由概率总质量和四阶矩控制。 -/
lemma lower_abs_moment_bound {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h4 : Integrable (fun x : ℝ => x ^ 4) μ) {n : ℕ} (hn : n ≤ 4) :
    (∫ x : ℝ, |x| ^ n ∂μ) ≤ 1 + ∫ x : ℝ, x ^ 4 ∂μ := by
  have hpow (x : ℝ) : |x| ^ n ≤ 1 + x ^ 4 := by
    have hfour : |x| ^ 4 = x ^ 4 := (show Even (4 : ℕ) by decide).pow_abs x
    by_cases hx : |x| ≤ 1
    · have hn1 := pow_le_one₀ (abs_nonneg x) hx (n := n)
      have hx4 : 0 ≤ x ^ 4 := by positivity
      linarith
    · have hh := pow_le_pow_right₀ (le_of_not_ge hx) hn
      rw [hfour] at hh
      linarith
  have hnint : Integrable (fun x : ℝ => |x| ^ n) μ := by
    simpa only [Real.norm_eq_abs, norm_pow, abs_pow] using
      (integrable_pow_of_fourth h4 hn).norm
  have hh := integral_mono hnint ((integrable_const 1).add h4) hpow
  change (∫ x : ℝ, |x| ^ n ∂μ) ≤ ∫ x : ℝ, 1 + x ^ 4 ∂μ at hh
  rw [integral_add (integrable_const 1) h4] at hh
  simpa using hh

/-- 可测性加四阶控制已足以保证真实误差函数可积。 -/
lemma integrable_of_odd_expansion {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h4 : Integrable (fun x : ℝ => x ^ 4) μ) {q odd : ℝ → ℝ}
    (hq : AEStronglyMeasurable q μ) (ho : Integrable odd μ) (η A B K : ℝ)
    (hb : ∀ x, |q x - (η ^ 2 * (A * x ^ 2 + B) + odd x)| ≤
      K * η ^ 4 * (1 + x ^ 4)) : Integrable q μ := by
  have hp : Integrable (fun x : ℝ => η ^ 2 * (A * x ^ 2 + B) + odd x) μ :=
    ((((integrable_pow_of_fourth h4 (by norm_num)).const_mul A).add
      (integrable_const B)).const_mul (η ^ 2)).add ho
  apply integrable_of_norm_sub_le hq hp
    (((integrable_const 1).add h4).const_mul (K * η ^ 4))
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact hb x

/-- 供真实Dyson展开赋值：线性、三次系数任意，平均后仅留下二次预算。 -/
theorem averaged_polynomial_expansion_isBigO {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : SymmetricLaw μ) (h4 : Integrable (fun x : ℝ => x ^ 4) μ)
    {q : ℝ → ℝ → ℝ} (A B K : ℝ) (a b : ℝ → ℝ)
    (hq : ∀ᶠ η in 𝓝 (0 : ℝ), AEStronglyMeasurable (q η) μ)
    (hb : ∀ᶠ η in 𝓝 (0 : ℝ), ∀ x,
      |q η x - (η ^ 2 * (A * x ^ 2 + B) + (a η * x + b η * x ^ 3))| ≤
        K * η ^ 4 * (1 + x ^ 4)) :
    (fun η => (∫ x, q η x ∂μ) - η ^ 2 * (A * (∫ x : ℝ, x ^ 2 ∂μ) + B))
      =O[𝓝 (0 : ℝ)] (fun η => η ^ 4) := by
  have ho (η : ℝ) : Integrable (fun x : ℝ => a η * x + b η * x ^ 3) μ := by
    have h1 : Integrable (fun x : ℝ => x) μ := by
      simpa using integrable_pow_of_fourth h4 (n := 1) (by norm_num)
    exact (h1.const_mul (a η)).add
      ((integrable_pow_of_fourth h4 (n := 3) (by norm_num)).const_mul (b η))
  apply averaged_remainder_isBigO hs h4 A B K
  · filter_upwards [hq, hb] with η hqm he
    exact integrable_of_odd_expansion h4 hqm (ho η) η A B K he
  · filter_upwards [hb] with η he
    exact paired_bound_of_odd_expansion η A B K (odd_linear_cubic (a η) (b η)) he

end RobustPiGate.FrontierAverage



