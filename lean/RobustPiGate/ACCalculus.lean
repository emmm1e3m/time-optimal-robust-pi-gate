import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Tactic

open MeasureTheory Set Filter
open scoped Topology Interval NNReal

set_option maxHeartbeats 800000

namespace RobustPiGate.Dynamics

-- 将实值绝对连续微积分基本定理推广到任意完备实范数空间。
theorem integral_eq_sub_of_ac_ae
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f g : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : IntervalIntegrable g volume a b)
    (hd : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt f (g t) t) :
    (∫ t in a..b, g t) = f b - f a := by
  have hdual : ∀ L : E →L[ℝ] ℝ,
      L (∫ t in a..b, g t) = L (f b - f a) := by
    intro L
    rw [← L.intervalIntegral_comp_comm hg, map_sub]
    have hac := L.lipschitzWith.comp_absolutelyContinuousOnInterval hf
    have heq : (∫ t in a..b, L (g t)) = ∫ t in a..b, deriv (fun s => L (f s)) t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hd] with t ht htI
      exact (L.hasFDerivAt.comp_hasDerivAt t (ht (uIoc_subset_uIcc htI))).deriv.symm
    rw [heq]
    exact hac.integral_deriv_eq_sub
  obtain ⟨L, _, hL⟩ := exists_dual_vector'' ℝ ((∫ t in a..b, g t) - (f b - f a))
  have hz : L ((∫ t in a..b, g t) - (f b - f a)) = 0 := by
    rw [map_sub, hdual L, sub_self]
  exact sub_eq_zero.mp (norm_eq_zero.mp (hL.symm.trans hz))

-- a.e. 导数界通过 AC 基本定理给出整个闭区间的 Lipschitz 界。
theorem lipschitzOnWith_of_ac_ae_deriv_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f g : ℝ → E} {a b : ℝ} {K : ℝ≥0}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : IntervalIntegrable g volume a b)
    (hd : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt f (g t) t)
    (hbound : ∀ᵐ t, t ∈ uIcc a b → ‖g t‖ ≤ K) :
    LipschitzOnWith K f (uIcc a b) := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro s hs t ht
  have hsub := uIcc_subset_uIcc ht hs
  have heq := integral_eq_sub_of_ac_ae (hf.mono hsub) (hg.mono_set hsub)
    (hd.mono fun x hx hxI => hx (hsub hxI))
  rw [← heq]
  simpa only [Real.norm_eq_abs, abs_sub_comm] using
    (intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (hbound.mono fun x hx hxI => hx (hsub (uIoc_subset_uIcc hxI))))

theorem lipschitzOnWith_of_ac_deriv_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {f : ℝ → E} {a b : ℝ} {K : ℝ≥0}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hbound : ∀ᵐ t, t ∈ uIcc a b → ‖deriv f t‖ ≤ K) :
    LipschitzOnWith K f (uIcc a b) := by
  apply lipschitzOnWith_of_ac_ae_deriv_bound hf (g := deriv f)
  · apply (intervalIntegrable_const (c := (K : ℝ))).mono_fun'
      (aestronglyMeasurable_deriv f (volume.restrict (uIoc a b)))
    change ∀ᵐ t ∂volume.restrict (uIoc a b), ‖deriv f t‖ ≤ (K : ℝ)
    rw [ae_restrict_iff' measurableSet_uIoc]
    exact hbound.mono fun x hx hxI => hx (uIoc_subset_uIcc hxI)
  · exact hf.boundedVariationOn.ae_differentiableAt_of_mem_uIcc.mono
      fun x hx hxI => (hx hxI).hasDerivAt
  · exact hbound

theorem eq_of_ac_ae_deriv_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt f 0 t) : f b = f a := by
  have h := integral_eq_sub_of_ac_ae hf (intervalIntegrable_const (c := (0 : E))) hd
  simpa only [intervalIntegral.integral_zero, eq_comm, sub_eq_zero] using h

section Algebra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

-- 环乘法是自身上的标量作用，因此 AC 曲线的乘积仍然 AC。
theorem ac_mul {f g : ℝ → A} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun t => f t * g t) a b := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  obtain ⟨D, hD⟩ := hg.exists_bound
  unfold AbsolutelyContinuousOnInterval at hf hg ⊢
  apply squeeze_zero' ?_ ?_ (by simpa using (hg.const_mul C).add (hf.const_mul D))
  · exact Filter.Eventually.of_forall <| fun _ => Finset.sum_nonneg (fun i hi => dist_nonneg)
  rw [eventually_inf_principal]
  filter_upwards with p hp
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hleft := hp.left i hi |>.left
  have hright := hp.left i hi |>.right
  calc
    dist (f (p.2 i).1 * g (p.2 i).1) (f (p.2 i).2 * g (p.2 i).2)
        ≤ dist (f (p.2 i).1 * g (p.2 i).1) (f (p.2 i).1 * g (p.2 i).2) +
          dist (f (p.2 i).1 * g (p.2 i).2) (f (p.2 i).2 * g (p.2 i).2) :=
      dist_triangle _ _ _
    _ ≤ C * dist (g (p.2 i).1) (g (p.2 i).2) +
          D * dist (f (p.2 i).1) (f (p.2 i).2) := by
      simp only [dist_eq_norm, ← mul_sub, ← sub_mul]
      apply add_le_add
      · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hC _ hleft) (norm_nonneg _))
      · rw [mul_comm D]
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hD _ hright) (norm_nonneg _))

-- a.e. 的乘积微分与 AC 基本定理；不要求控制连续。
theorem integral_product_deriv
    {f g f' g' : ℝ → A} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hfi : IntervalIntegrable f' volume a b)
    (hgi : IntervalIntegrable g' volume a b)
    (hfd : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt f (f' t) t)
    (hgd : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt g (g' t) t) :
    (∫ t in a..b, f' t * g t + f t * g' t) = f b * g b - f a * g a := by
  apply integral_eq_sub_of_ac_ae (ac_mul hf hg)
  · exact (hfi.mul_continuousOn hg.continuousOn).add
      (hgi.continuousOn_mul hf.continuousOn)
  · filter_upwards [hfd, hgd] with t hft hgt ht
    exact (hft ht).mul (hgt ht)

end Algebra
end RobustPiGate.Dynamics
