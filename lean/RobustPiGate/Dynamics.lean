import RobustPiGate.ACCalculus
import Mathlib.Analysis.CStarAlgebra.Basic

open MeasureTheory Set Filter
open scoped Topology Interval NNReal

set_option maxHeartbeats 800000

namespace RobustPiGate.Dynamics

section Evolution
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [StarRing A] [NormedStarGroup A] [StarModule ℝ A]

-- 原线性ODE的AC/a.e.语义，允许任意可测有界生成元。
structure IsACSolution (G U : ℝ → A) (T : ℝ) : Prop where
  ac : AbsolutelyContinuousOnInterval U 0 T
  initial : U 0 = 1
  equation : ∀ᵐ t, t ∈ uIcc 0 T → HasDerivAt U (G t * U t) t

theorem IsACSolution.restrict {G U : ℝ → A} {T t : ℝ}
    (hU : IsACSolution G U T) (ht : t ∈ uIcc 0 T) : IsACSolution G U t where
  ac := hU.ac.mono (uIcc_subset_uIcc_left ht)
  initial := hU.initial
  equation := hU.equation.mono fun _ hx hxI => hx (uIcc_subset_uIcc_left ht hxI)

theorem ac_star {f : ℝ → A} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => star (f t)) a b :=
  star_isometry.lipschitzWith.comp_absolutelyContinuousOnInterval hf

-- 原生成元的反厄米性保证幺正性；这里直接对 U†U 求导并使用AC FTC。
theorem IsACSolution.star_mul_self {G U : ℝ → A} {T : ℝ}
    (hU : IsACSolution G U T)
    (hG : ∀ᵐ t, t ∈ uIcc 0 T → star (G t) = -G t) :
    star (U T) * U T = 1 := by
  have hd : ∀ᵐ t, t ∈ uIcc 0 T →
      HasDerivAt (fun s => star (U s) * U s) 0 t := by
    filter_upwards [hU.equation, hG] with t hUt hGt ht
    convert (hUt ht).star.mul (hUt ht) using 1
    simp [star_mul, hGt ht, mul_assoc]
  have h := eq_of_ac_ae_deriv_zero (ac_mul (ac_star hU.ac) hU.ac) hd
  simpa [hU.initial] using h

theorem IsACSolution.unitary [IsDedekindFiniteMonoid A] {G U : ℝ → A} {T t : ℝ}
    (hU : IsACSolution G U T)
    (hG : ∀ᵐ s, s ∈ uIcc 0 T → star (G s) = -G s)
    (ht : t ∈ uIcc 0 T) : U t ∈ unitary A := by
  have hleft := (hU.restrict ht).star_mul_self
    (hG.mono fun _ hx hxI => hx (uIcc_subset_uIcc_left ht hxI))
  exact ⟨hleft, mul_eq_one_comm.mp hleft⟩

-- Duhamel恒等式从两条原ODE推得，没有将相互作用绘景方程作为假设。
theorem duhamel_frame {G U V : ℝ → A} {B : A} {δ T : ℝ}
    (hU : IsACSolution G U T)
    (hV : IsACSolution (fun t => G t + δ • B) V T)
    (hG : ∀ᵐ t, t ∈ uIcc 0 T → star (G t) = -G t) :
    star (U T) * V T - 1 = δ • (∫ t in 0..T, star (U t) * B * V t) := by
  have hc : ContinuousOn (fun t => star (U t) * B * V t) (uIcc 0 T) :=
    (hU.ac.continuousOn.star.mul_const B).mul hV.ac.continuousOn
  have hd : ∀ᵐ t, t ∈ uIcc 0 T →
      HasDerivAt (fun s => star (U s) * V s) (δ • (star (U t) * B * V t)) t := by
    filter_upwards [hU.equation, hV.equation, hG] with t hut hvt hgt ht
    convert (hut ht).star.mul (hvt ht) using 1
    simp [star_mul, hgt ht, add_mul, mul_add, mul_assoc, smul_mul_assoc, mul_smul_comm]
  have h := integral_eq_sub_of_ac_ae (ac_mul (ac_star hU.ac) hV.ac)
    (hc.const_smul δ).intervalIntegrable hd
  simpa [hU.initial, hV.initial, intervalIntegral.integral_smul] using h.symm

-- 将绘景恒等式还原为原演化算符差。
theorem duhamel [IsDedekindFiniteMonoid A] {G U V : ℝ → A} {B : A} {δ T : ℝ}
    (hU : IsACSolution G U T)
    (hV : IsACSolution (fun t => G t + δ • B) V T)
    (hG : ∀ᵐ t, t ∈ uIcc 0 T → star (G t) = -G t) :
    V T - U T = δ • (U T * (∫ t in 0..T, star (U t) * B * V t)) := by
  have h := congrArg (fun x => U T * x) (duhamel_frame hU hV hG)
  have hright := mul_eq_one_comm.mp (hU.star_mul_self hG)
  simpa [mul_sub, ← mul_assoc, hright, mul_smul_comm] using h

theorem solution_unique [IsDedekindFiniteMonoid A] {G U V : ℝ → A} {T t : ℝ}
    (hU : IsACSolution G U T) (hV : IsACSolution G V T)
    (hG : ∀ᵐ s, s ∈ uIcc 0 T → star (G s) = -G s)
    (ht : t ∈ uIcc 0 T) : V t = U t := by
  have hV' : IsACSolution (fun s => G s + (0 : ℝ) • (0 : A)) V t := by
    simpa using hV.restrict ht
  have h := duhamel (hU.restrict ht) hV'
    (hG.mono fun _ hx hxI => hx (uIcc_subset_uIcc_left ht hxI))
  simpa only [zero_smul, sub_eq_zero] using h

end Evolution

section Parameter
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [StarRing A] [CStarRing A] [StarModule ℝ A] [IsDedekindFiniteMonoid A]

theorem skew_perturbed {G : ℝ → A} {B : A} {T δ : ℝ}
    (hG : ∀ᵐ t, t ∈ uIcc 0 T → star (G t) = -G t) (hB : star B = -B) :
    ∀ᵐ t, t ∈ uIcc 0 T → star (G t + δ • B) = -(G t + δ • B) := by
  filter_upwards [hG] with t ht htI
  simp [star_add, star_smul, ht htI, hB, add_comm]

theorem norm_frame_integrand {G U V : ℝ → A} {B : A} {δ T t : ℝ}
    (hU : IsACSolution G U T)
    (hV : IsACSolution (fun s => G s + δ • B) V T)
    (hG : ∀ᵐ s, s ∈ uIcc 0 T → star (G s) = -G s)
    (hB : star B = -B) (ht : t ∈ uIcc 0 T) :
    ‖star (U t) * B * V t‖ = ‖B‖ := by
  have hu := hU.unitary hG ht
  have hv := hV.unitary (skew_perturbed hG hB) ht
  rw [CStarRing.norm_mul_mem_unitary _ hv]
  apply CStarRing.norm_mem_unitary_mul
  simpa only [Unitary.mem_iff, star_star] using And.intro hu.2 hu.1

-- Duhamel给出统一的参数Lipschitz估计，因此连续依赖不是额外假设。
theorem norm_solution_sub_le {G U V : ℝ → A} {B : A} {δ T : ℝ}
    (hU : IsACSolution G U T)
    (hV : IsACSolution (fun t => G t + δ • B) V T)
    (hG : ∀ᵐ t, t ∈ uIcc 0 T → star (G t) = -G t) (hB : star B = -B) :
    ‖V T - U T‖ ≤ |δ| * (‖B‖ * |T|) := by
  rw [duhamel hU hV hG, norm_smul,
    CStarRing.norm_mem_unitary_mul _ (hU.unitary hG right_mem_uIcc)]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg δ)
  simpa only [sub_zero] using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t ht => (norm_frame_integrand hU hV hG hB (uIoc_subset_uIcc ht)).le))

-- 参数一阶余项的二次界；常数只依赖持续时间和固定噪声生成元。
theorem norm_solution_remainder_le {G U V : ℝ → A} {B : A} {δ T : ℝ}
    (hU : IsACSolution G U T)
    (hV : IsACSolution (fun t => G t + δ • B) V T)
    (hG : ∀ᵐ t, t ∈ uIcc 0 T → star (G t) = -G t) (hB : star B = -B) :
    ‖V T - U T - δ • (U T * (∫ t in 0..T, star (U t) * B * U t))‖
      ≤ |δ| ^ 2 * (‖B‖ * |T|) ^ 2 := by
  have hiV : IntervalIntegrable (fun t => star (U t) * B * V t) volume 0 T :=
    ((hU.ac.continuousOn.star.mul_const B).mul hV.ac.continuousOn).intervalIntegrable
  have hiU : IntervalIntegrable (fun t => star (U t) * B * U t) volume 0 T :=
    ((hU.ac.continuousOn.star.mul_const B).mul hU.ac.continuousOn).intervalIntegrable
  have heq : V T - U T - δ • (U T * (∫ t in 0..T, star (U t) * B * U t)) =
      δ • (U T * (∫ t in 0..T, star (U t) * B * (V t - U t))) := by
    rw [duhamel hU hV hG, ← smul_sub, ← mul_sub, ← intervalIntegral.integral_sub hiV hiU]
    simp only [mul_sub]
  rw [heq, norm_smul, CStarRing.norm_mem_unitary_mul _ (hU.unitary hG right_mem_uIcc)]
  have hb : ∀ t ∈ uIoc 0 T, ‖star (U t) * B * (V t - U t)‖ ≤
      ‖B‖ * (|δ| * (‖B‖ * |T|)) := by
    intro t ht
    have htI := uIoc_subset_uIcc ht
    have hGt := hG.mono fun s hs hsI => hs (uIcc_subset_uIcc_left htI hsI)
    have hsub := norm_solution_sub_le (hU.restrict htI) (hV.restrict htI) hGt hB
    have habs : |t| ≤ |T| := by simpa using abs_sub_left_of_mem_uIcc htI
    have hu := hU.unitary hG htI
    have hstar : star (U t) ∈ unitary A := by
      simpa only [Unitary.mem_iff, star_star] using And.intro hu.2 hu.1
    calc
      ‖star (U t) * B * (V t - U t)‖ ≤ ‖star (U t) * B‖ * ‖V t - U t‖ := norm_mul_le _ _
      _ = ‖B‖ * ‖V t - U t‖ := by rw [CStarRing.norm_mem_unitary_mul B hstar]
      _ ≤ ‖B‖ * (|δ| * (‖B‖ * |t|)) := mul_le_mul_of_nonneg_left hsub (norm_nonneg B)
      _ ≤ ‖B‖ * (|δ| * (‖B‖ * |T|)) := by gcongr
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const hb
  have hmul := mul_le_mul_of_nonneg_left hI (abs_nonneg δ)
  simpa only [Real.norm_eq_abs, sub_zero] using hmul.trans_eq (by ring)

theorem parameter_hasDerivAt {G : ℝ → A} {U : ℝ → ℝ → A} {B : A} {T : ℝ}
    (hU : ∀ δ, IsACSolution (fun t => G t + δ • B) (U δ) T)
    (hG : ∀ᵐ t, t ∈ uIcc 0 T → star (G t) = -G t) (hB : star B = -B) :
    HasDerivAt (fun δ => U δ T)
      (U 0 T * (∫ t in 0..T, star (U 0 t) * B * U 0 t)) 0 := by
  have hzero : IsACSolution G (U 0) T := by simpa using hU 0
  rw [hasDerivAt_iff_tendsto]
  let C : ℝ := (‖B‖ * |T|) ^ 2
  have hbound : ∀ δ : ℝ,
      ‖δ - 0‖⁻¹ * ‖U δ T - U 0 T - (δ - 0) •
        (U 0 T * (∫ t in 0..T, star (U 0 t) * B * U 0 t))‖ ≤ |δ| * C := by
    intro δ
    have hrem := norm_solution_remainder_le hzero (hU δ) hG hB
    simp only [sub_zero, Real.norm_eq_abs]
    by_cases hδ : δ = 0
    · simp [hδ]
    calc
      _ ≤ |δ|⁻¹ * (|δ| ^ 2 * C) :=
        mul_le_mul_of_nonneg_left hrem (inv_nonneg.mpr (abs_nonneg δ))
      _ = |δ| * C := by field_simp
  apply squeeze_zero' (Filter.Eventually.of_forall (fun δ => by positivity))
    (Filter.Eventually.of_forall hbound)
  have hc : Continuous (fun δ : ℝ => |δ| * C) := by fun_prop
  simpa using hc.tendsto 0

theorem first_order_robust_iff {G : ℝ → A} {U : ℝ → ℝ → A} {B : A} {T : ℝ}
    (hU : ∀ δ, IsACSolution (fun t => G t + δ • B) (U δ) T)
    (hG : ∀ᵐ t, t ∈ uIcc 0 T → star (G t) = -G t) (hB : star B = -B) :
    deriv (fun δ => U δ T) 0 = 0 ↔
      (∫ t in 0..T, star (U 0 t) * B * U 0 t) = 0 := by
  rw [(parameter_hasDerivAt hU hG hB).deriv]
  constructor
  · intro h
    have hzero : IsACSolution G (U 0) T := by simpa using hU 0
    have hleft := hzero.star_mul_self hG
    have hh := congrArg (fun x => star (U 0 T) * x) h
    simpa only [← mul_assoc, hleft, one_mul, mul_zero] using hh
  · intro h
    simp only [h, mul_zero]

end Parameter
end RobustPiGate.Dynamics
