import RobustPiGate.SharpLength
import RobustPiGate.ACCalculus

noncomputable section
open Set Real MeasureTheory
open scoped NNReal
namespace RobustPiGate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- 原论文的绝对连续、几乎处处速度界版本。 -/
theorem ac_spherical_curve_length_lower_bound [FiniteDimensional ℝ E]
    {n : ℝ → E} {L : ℝ} (hL : 0 < L)
    (hac : AbsolutelyContinuousOnInterval n 0 L)
    (hunit : ∀ t ∈ Icc 0 L, ‖n t‖ = 1)
    (hderiv : ∀ᵐ t, t ∈ Icc 0 L → ‖deriv n t‖ ≤ 1)
    (hend : n L = -n 0) (hzero : (∫ t in 0..L, n t) = 0) :
    7 * Real.pi / 3 ≤ L := by
  have hLip := Dynamics.lipschitzOnWith_of_ac_deriv_bound (K := 1) hac
    (by simpa [uIcc_of_le hL.le] using hderiv)
  rw [uIcc_of_le hL.le] at hLip
  exact spherical_curve_length_lower_bound hL hLip.continuousOn hunit
    (sphericalSpeedBound_of_lipschitzOnWith hunit hLip) hend hzero

/-- 实际时间变量中的任意正速度上界；从路径重参数化推导缩放。 -/
theorem spherical_curve_time_lower_bound {n : ℝ → E} {T : ℝ} {Ω : ℝ≥0}
    (hΩ : 0 < Ω) (hT : 0 < T)
    (hLip : LipschitzOnWith Ω n (Icc 0 T))
    (hunit : ∀ t ∈ Icc 0 T, ‖n t‖ = 1)
    (hend : n T = -n 0) (hzero : (∫ t in 0..T, n t) = 0) :
    7 * Real.pi / (3 * (Ω : ℝ)) ≤ T := by
  have hΩr : 0 < (Ω : ℝ) := hΩ
  have hΩn : (Ω : ℝ) ≠ 0 := ne_of_gt hΩr
  let m : ℝ → E := fun s => n (s / (Ω : ℝ))
  have hmem {s : ℝ} (hs : s ∈ Icc 0 ((Ω : ℝ) * T)) : s / (Ω : ℝ) ∈ Icc 0 T := by
    exact ⟨div_nonneg hs.1 hΩr.le, (div_le_iff₀ hΩr).mpr (by simpa [mul_comm] using hs.2)⟩
  have hmLip : LipschitzOnWith 1 m (Icc 0 ((Ω : ℝ) * T)) := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro s hs t ht
    have h := (lipschitzOnWith_iff_norm_sub_le.mp hLip) (hmem hs) (hmem ht)
    change ‖n (s / (Ω : ℝ)) - n (t / (Ω : ℝ))‖ ≤ (1 : ℝ) * ‖s - t‖
    have hcancel : (Ω : ℝ) * (|s - t| / (Ω : ℝ)) = |s - t| := by
      field_simp
    simpa [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hΩr, hcancel] using h
  have hmUnit : ∀ s ∈ Icc 0 ((Ω : ℝ) * T), ‖m s‖ = 1 :=
    fun s hs => hunit _ (hmem hs)
  have hmEnd : m ((Ω : ℝ) * T) = -m 0 := by simpa [m, hΩn] using hend
  have hmZero : (∫ s in 0..(Ω : ℝ) * T, m s) = 0 := by
    dsimp [m]
    rw [intervalIntegral.integral_comp_div _ hΩn]
    simpa [hΩn] using congrArg (fun v : E => (Ω : ℝ) • v) hzero
  have hL := spherical_curve_length_lower_bound (mul_pos hΩr hT)
    hmLip.continuousOn hmUnit (sphericalSpeedBound_of_lipschitzOnWith hmUnit hmLip)
    hmEnd hmZero
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 3) hΩr)).mpr
  nlinarith

end RobustPiGate



