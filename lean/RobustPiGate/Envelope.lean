import RobustPiGate.Basic

noncomputable section
open Real MeasureTheory Set
namespace RobustPiGate

/-- 包络及其余弦是连续函数。 -/
theorem continuous_envelope (c β : ℝ) : Continuous (envelope c β) := by
  unfold envelope
  fun_prop

theorem continuous_cos_envelope (c β : ℝ) :
    Continuous (fun s => Real.cos (envelope c β s)) :=
  Real.continuous_cos.comp (continuous_envelope c β)

/-- 未触及球面距离上限时，包络积分由两个正弦端点值给出。 -/
theorem integral_cos_envelope_uncapped {c β : ℝ}
    (hβ0 : 0 ≤ β) (hβc : β ≤ c) (hcβ : c + β ≤ 2 * Real.pi) :
    (∫ s in 0..c, Real.cos (envelope c β s)) =
      2 * Real.sin ((c + β) / 2) - Real.sin β := by
  let a : ℝ := (c + β) / 2
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have hac : a ≤ c := by dsimp [a]; linarith
  have haπ : a ≤ Real.pi := by dsimp [a]; linarith
  have hi (x y : ℝ) : IntervalIntegrable (fun s => Real.cos (envelope c β s)) volume x y :=
    (continuous_cos_envelope c β).intervalIntegrable x y
  have hleft : (∫ s in 0..a, Real.cos (envelope c β s)) = Real.sin a := by
    calc
      _ = ∫ s in 0..a, Real.cos s := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le ha0] at hs
        have hsa : s ≤ c + β - s := by dsimp [a] at hs; linarith [hs.2]
        simp [envelope, min_eq_left hsa, min_eq_left (hs.2.trans haπ)]
      _ = _ := by rw [integral_cos]; simp
  have hright : (∫ s in a..c, Real.cos (envelope c β s)) =
      Real.sin a - Real.sin β := by
    calc
      _ = ∫ s in a..c, Real.cos (c + β - s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hac] at hs
        have hsa : c + β - s ≤ s := by dsimp [a] at hs; linarith [hs.1]
        have hsπ : c + β - s ≤ Real.pi := by dsimp [a] at haπ hs; linarith [hs.1]
        simp [envelope, min_eq_right hsa, min_eq_left hsπ]
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_left, integral_cos]
        have h₁ : c + β - a = a := by dsimp [a]; ring
        simp [h₁]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a c), hleft, hright]
  dsimp [a]
  ring

/-- 触及球面距离上限时，包络积分包含常值平台的贡献。 -/
theorem integral_cos_envelope_capped {c β : ℝ}
    (hβπ : β ≤ Real.pi) (_hc : Real.pi ≤ c) (hcβ : 2 * Real.pi ≤ c + β) :
    (∫ s in 0..c, Real.cos (envelope c β s)) =
      2 * Real.pi - c - β - Real.sin β := by
  let b : ℝ := c + β - Real.pi
  have hπb : Real.pi ≤ b := by dsimp [b]; linarith
  have hbc : b ≤ c := by dsimp [b]; linarith
  have hi (x y : ℝ) : IntervalIntegrable (fun s => Real.cos (envelope c β s)) volume x y :=
    (continuous_cos_envelope c β).intervalIntegrable x y
  have hleft : (∫ s in 0..Real.pi, Real.cos (envelope c β s)) = 0 := by
    calc
      _ = ∫ s in 0..Real.pi, Real.cos s := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le Real.pi_pos.le] at hs
        have hsa : s ≤ c + β - s := by linarith [hs.2]
        simp [envelope, min_eq_left hsa, min_eq_left hs.2]
      _ = _ := by rw [integral_cos]; simp
  have hmiddle : (∫ s in Real.pi..b, Real.cos (envelope c β s)) = Real.pi - b := by
    calc
      _ = ∫ _s in Real.pi..b, (-1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hπb] at hs
        have hsb : Real.pi ≤ c + β - s := by dsimp [b] at hs; linarith [hs.2]
        simp [envelope, min_eq_right (le_min hs.1 hsb)]
      _ = _ := by simp [intervalIntegral.integral_const]
  have hright : (∫ s in b..c, Real.cos (envelope c β s)) = -Real.sin β := by
    calc
      _ = ∫ s in b..c, Real.cos (c + β - s) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le hbc] at hs
        have hsa : c + β - s ≤ s := by dsimp [b] at hs; linarith [hs.1]
        have hsπ : c + β - s ≤ Real.pi := by dsimp [b] at hs; linarith [hs.1]
        simp [envelope, min_eq_right hsa, min_eq_left hsπ]
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_left, integral_cos]
        have h₁ : c + β - b = Real.pi := by dsimp [b]; ring
        simp [h₁]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 Real.pi) (hi Real.pi c),
    ← intervalIntegral.integral_add_adjacent_intervals (hi Real.pi b) (hi b c),
    hleft, hmiddle, hright]
  dsimp [b]
  ring

/-- 包络积分的显式公式；未增加任何积分取值假设。 -/
theorem integral_cos_envelope {c β : ℝ}
    (hβ0 : 0 ≤ β) (hβπ : β ≤ Real.pi) (hc : Real.pi ≤ c) :
    (∫ s in 0..c, Real.cos (envelope c β s)) = halfBound c β := by
  unfold halfBound
  split_ifs with h
  · exact integral_cos_envelope_uncapped hβ0 (hβπ.trans hc) h
  · exact integral_cos_envelope_capped hβπ hc (le_of_not_ge h)

/-- 连续投影满足逐点包络下界时，其积分至少为显式半段下界。 -/
theorem halfBound_le_integral {c β : ℝ} {g : ℝ → ℝ}
    (hβ0 : 0 ≤ β) (hβπ : β ≤ Real.pi) (hc : Real.pi ≤ c)
    (hg : ContinuousOn g (Icc 0 c))
    (hbound : ∀ s ∈ Icc 0 c, Real.cos (envelope c β s) ≤ g s) :
    halfBound c β ≤ ∫ s in 0..c, g s := by
  rw [← integral_cos_envelope hβ0 hβπ hc]
  exact intervalIntegral.integral_mono_on (Real.pi_pos.le.trans hc)
    ((continuous_cos_envelope c β).intervalIntegrable 0 c)
    (hg.intervalIntegrable_of_Icc (Real.pi_pos.le.trans hc)) hbound

/-- 中点投影的基础余弦积分。 -/
theorem integral_cos_abs_midpoint (c : ℝ) :
    (∫ t in 0..2 * c, Real.cos |t - c|) = 2 * Real.sin c := by
  simp_rw [Real.cos_abs]
  rw [intervalIntegral.integral_comp_sub_right, integral_cos]
  have h₁ : 2 * c - c = c := by ring
  simp [h₁]
  ring

/-- 正半时长小于 π 时，基础包络与投影零均值互相矛盾。 -/
theorem pi_le_of_zero_integral_midpoint_bound {c : ℝ} {g : ℝ → ℝ}
    (hc : 0 < c) (hg : ContinuousOn g (Icc 0 (2 * c)))
    (hzero : (∫ t in 0..2 * c, g t) = 0)
    (hbound : ∀ t ∈ Icc 0 (2 * c), Real.cos |t - c| ≤ g t) : Real.pi ≤ c := by
  by_contra h
  have hcp : c < Real.pi := lt_of_not_ge h
  have hpos : 0 < Real.sin c := Real.sin_pos_of_pos_of_lt_pi hc hcp
  have hcont : Continuous (fun t : ℝ => Real.cos |t - c|) := by fun_prop
  have hle := intervalIntegral.integral_mono_on (μ := volume) (by linarith : 0 ≤ 2 * c)
    (hcont.intervalIntegrable 0 (2 * c))
    (hg.intervalIntegrable_of_Icc (by linarith : 0 ≤ 2 * c)) hbound
  rw [integral_cos_abs_midpoint, hzero] at hle
  linarith

/-- 两个以中点为起点的半段，通过反向与平移换元拼接成整段下界。 -/
theorem sum_halfBound_le_integral {c α β : ℝ} {g : ℝ → ℝ}
    (hα0 : 0 ≤ α) (hαπ : α ≤ Real.pi) (hβ0 : 0 ≤ β) (hβπ : β ≤ Real.pi)
    (hc : Real.pi ≤ c) (hg : ContinuousOn g (Icc 0 (2 * c)))
    (hleft : ∀ s ∈ Icc 0 c, Real.cos (envelope c α s) ≤ g (c - s))
    (hright : ∀ s ∈ Icc 0 c, Real.cos (envelope c β s) ≤ g (c + s)) :
    halfBound c α + halfBound c β ≤ ∫ t in 0..2 * c, g t := by
  have hc0 : 0 ≤ c := Real.pi_pos.le.trans hc
  have hlc : ContinuousOn (fun s => g (c - s)) (Icc 0 c) := by
    apply hg.comp (by fun_prop)
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hrc : ContinuousOn (fun s => g (c + s)) (Icc 0 c) := by
    apply hg.comp (by fun_prop)
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hl := halfBound_le_integral hα0 hαπ hc hlc hleft
  have hr := halfBound_le_integral hβ0 hβπ hc hrc hright
  rw [intervalIntegral.integral_comp_sub_left] at hl
  simp only [sub_self, sub_zero] at hl
  rw [intervalIntegral.integral_comp_add_left] at hr
  simp only [add_zero, ← two_mul] at hr
  have hg0c : ContinuousOn g (Icc 0 c) := hg.mono (by
    intro t ht
    constructor <;> linarith [ht.1, ht.2])
  have hgc2c : ContinuousOn g (Icc c (2 * c)) := hg.mono (by
    intro t ht
    constructor <;> linarith [ht.1, ht.2])
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hg0c.intervalIntegrable_of_Icc hc0 (μ := volume))
    (hgc2c.intervalIntegrable_of_Icc (by linarith : c ≤ 2 * c) (μ := volume))
  rw [← hadd]
  exact add_le_add hl hr

end RobustPiGate
