import RobustPiGate.FrontierBasic
import RobustPiGate.Envelope
import RobustPiGate.Geometry
import RobustPiGate.ACCalculus
import RobustPiGate.Rigidity

noncomputable section
open Real Set MeasureTheory InnerProductGeometry
open scoped InnerProductSpace NNReal
namespace RobustPiGate

/-- 包络积分只要求实际端点可达；允许半时长小于 π。 -/
theorem integral_cos_envelope_of_feasible {c β : ℝ}
    (hβ0 : 0 ≤ β) (hβπ : β ≤ Real.pi) (hβc : β ≤ c) :
    (∫ s in 0..c, Real.cos (envelope c β s)) = halfBound c β := by
  unfold halfBound
  split_ifs with h
  · exact integral_cos_envelope_uncapped hβ0 hβc h
  · exact integral_cos_envelope_capped hβπ (by linarith) (le_of_not_ge h)

/-- 可达端点条件下，逐点包络可直接积分。 -/
theorem halfBound_le_integral_of_feasible {c β : ℝ} {g : ℝ → ℝ}
    (hβ0 : 0 ≤ β) (hβπ : β ≤ Real.pi) (hβc : β ≤ c)
    (hg : ContinuousOn g (Icc 0 c))
    (hbound : ∀ s ∈ Icc 0 c, Real.cos (envelope c β s) ≤ g s) :
    halfBound c β ≤ ∫ s in 0..c, g s := by
  rw [← integral_cos_envelope_of_feasible hβ0 hβπ hβc]
  exact intervalIntegral.integral_mono_on (hβ0.trans hβc)
    ((continuous_cos_envelope c β).intervalIntegrable 0 c)
    (hg.intervalIntegrable_of_Icc (hβ0.trans hβc)) hbound

/-- 中点两侧的标量积分经反向和平移换元等于整段积分。 -/
theorem integral_midpoint_halves {c : ℝ} {g : ℝ → ℝ}
    (hc : 0 ≤ c) (hg : ContinuousOn g (Icc 0 (2 * c))) :
    (∫ s in 0..c, g (c - s)) + (∫ s in 0..c, g (c + s)) =
      ∫ t in 0..2 * c, g t := by
  rw [intervalIntegral.integral_comp_sub_left, intervalIntegral.integral_comp_add_left]
  simp only [sub_self, sub_zero, add_zero, ← two_mul]
  apply intervalIntegral.integral_add_adjacent_intervals
  · exact (hg.mono (by intro t ht; constructor <;> linarith [ht.1, ht.2])).intervalIntegrable_of_Icc hc
  · exact (hg.mono (by intro t ht; constructor <;> linarith [ht.1, ht.2])).intervalIntegrable_of_Icc (by linarith)

/-- 两个可达端点的半段包络给出整段积分下界。 -/
theorem sum_halfBound_le_integral_of_feasible {c α β : ℝ} {g : ℝ → ℝ}
    (hα0 : 0 ≤ α) (hαπ : α ≤ Real.pi) (hαc : α ≤ c)
    (hβ0 : 0 ≤ β) (hβπ : β ≤ Real.pi) (hβc : β ≤ c)
    (hg : ContinuousOn g (Icc 0 (2 * c)))
    (hleft : ∀ s ∈ Icc 0 c, Real.cos (envelope c α s) ≤ g (c - s))
    (hright : ∀ s ∈ Icc 0 c, Real.cos (envelope c β s) ≤ g (c + s)) :
    halfBound c α + halfBound c β ≤ ∫ t in 0..2 * c, g t := by
  have hc0 := hα0.trans hαc
  have hlc : ContinuousOn (fun s => g (c - s)) (Icc 0 c) := by
    apply hg.comp (by fun_prop)
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hrc : ContinuousOn (fun s => g (c + s)) (Icc 0 c) := by
    apply hg.comp (by fun_prop)
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  rw [← integral_midpoint_halves hc0 hg]
  exact add_le_add (halfBound_le_integral_of_feasible hα0 hαπ hαc hlc hleft)
    (halfBound_le_integral_of_feasible hβ0 hβπ hβc hrc hright)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- 中点向左重参数化保持球面单位速度界。 -/
theorem sphericalSpeedBound_midpoint_left {n : ℝ → E} {c : ℝ}
    (hc : 0 ≤ c) (hspeed : SphericalSpeedBound n 0 (2 * c)) :
    SphericalSpeedBound (fun s => n (c - s)) 0 c := by
  intro s hs t ht
  have hcs : c - s ∈ Icc 0 (2 * c) := by constructor <;> linarith [hs.1, hs.2]
  have hct : c - t ∈ Icc 0 (2 * c) := by constructor <;> linarith [ht.1, ht.2]
  have h := hspeed (c - s) hcs (c - t) hct
  convert h using 1
  rw [show c - t - (c - s) = -(t - s) by ring, abs_neg]

/-- 中点向右重参数化保持球面单位速度界。 -/
theorem sphericalSpeedBound_midpoint_right {n : ℝ → E} {c : ℝ}
    (hc : 0 ≤ c) (hspeed : SphericalSpeedBound n 0 (2 * c)) :
    SphericalSpeedBound (fun s => n (c + s)) 0 c := by
  intro s hs t ht
  have hcs : c + s ∈ Icc 0 (2 * c) := by constructor <;> linarith [hs.1, hs.2]
  have hct : c + t ∈ Icc 0 (2 * c) := by constructor <;> linarith [ht.1, ht.2]
  have h := hspeed (c + s) hcs (c + t) hct
  convert h using 1
  congr 1
  ring

/-- 反极端点和速度界给出两个实际半曲线的端点可达条件。 -/
theorem midpoint_angle_feasible {n : ℝ → E} {c : ℝ}
    (hc : 0 ≤ c) (hspeed : SphericalSpeedBound n 0 (2 * c))
    (hend : n (2 * c) = -n 0) :
    angle (n c) (n 0) ≤ c ∧ Real.pi - angle (n c) (n 0) ≤ c := by
  have hcm : c ∈ Icc 0 (2 * c) := ⟨hc, by linarith⟩
  constructor
  · simpa [abs_of_nonneg hc] using hspeed c hcm 0 ⟨le_rfl, by linarith⟩
  · have h := hspeed c hcm (2 * c) ⟨by linarith, le_rfl⟩
    rw [hend, angle_neg_right, show 2 * c - c = c by ring, abs_of_nonneg hc] at h
    exact h

/-- 两半真实曲线的中点投影逐点受各自端点包络约束。 -/
theorem midpoint_cos_envelope_bounds {n : ℝ → E} {c : ℝ}
    (hc : 0 ≤ c) (hunit : ∀ t ∈ Icc 0 (2 * c), ‖n t‖ = 1)
    (hspeed : SphericalSpeedBound n 0 (2 * c))
    (hend : n (2 * c) = -n 0) :
    (∀ s ∈ Icc 0 c, Real.cos (envelope c (angle (n c) (n 0)) s) ≤
      ⟪n c, n (c - s)⟫_ℝ) ∧
    (∀ s ∈ Icc 0 c, Real.cos (envelope c (Real.pi - angle (n c) (n 0)) s) ≤
      ⟪n c, n (c + s)⟫_ℝ) := by
  have hlu : ∀ t ∈ Icc 0 c, ‖n (c - t)‖ = 1 := by
    intro t ht
    apply hunit
    constructor <;> linarith [ht.1, ht.2]
  have hru : ∀ t ∈ Icc 0 c, ‖n (c + t)‖ = 1 := by
    intro t ht
    apply hunit
    constructor <;> linarith [ht.1, ht.2]
  constructor
  · intro s hs
    simpa using cos_envelope_le_inner hc hs hlu (sphericalSpeedBound_midpoint_left hc hspeed)
  · intro s hs
    simpa [← two_mul, hend, angle_neg_right] using
      cos_envelope_le_inner hc hs hru (sphericalSpeedBound_midpoint_right hc hspeed)

variable [CompleteSpace E]

/-- 向量积分的中点投影至少等于两个真实半曲线的显式包络积分。 -/
theorem midpoint_halfBound_le_integral {n : ℝ → E} {c : ℝ}
    (hc : 0 ≤ c) (hcont : ContinuousOn n (Icc 0 (2 * c)))
    (hunit : ∀ t ∈ Icc 0 (2 * c), ‖n t‖ = 1)
    (hspeed : SphericalSpeedBound n 0 (2 * c))
    (hend : n (2 * c) = -n 0) :
    halfBound c (angle (n c) (n 0)) + halfBound c (Real.pi - angle (n c) (n 0)) ≤
      ⟪n c, ∫ t in 0..2 * c, n t⟫_ℝ := by
  obtain ⟨hαc, hβc⟩ := midpoint_angle_feasible hc hspeed hend
  obtain ⟨hl, hr⟩ := midpoint_cos_envelope_bounds hc hunit hspeed hend
  have hg : ContinuousOn (fun t => ⟪n c, n t⟫_ℝ) (Icc 0 (2 * c)) :=
    continuousOn_const.inner hcont
  have h := sum_halfBound_le_integral_of_feasible (angle_nonneg _ _) (angle_le_pi _ _)
    hαc (by linarith [angle_le_pi (n c) (n 0)])
    (by linarith [angle_nonneg (n c) (n 0)]) hβc hg hl hr
  have hi := (innerSL ℝ (n c)).intervalIntegral_comp_comm
    (hcont.intervalIntegrable_of_Icc (μ := volume) (by linarith : 0 ≤ 2 * c))
  exact h.trans_eq hi

/-- 包络积分和等于真实投影时，两半连续非负差逐点为零。 -/
theorem midpoint_projection_eq_envelopes {n : ℝ → E} {c : ℝ}
    (hc : 0 < c) (hcont : ContinuousOn n (Icc 0 (2 * c)))
    (hunit : ∀ t ∈ Icc 0 (2 * c), ‖n t‖ = 1)
    (hspeed : SphericalSpeedBound n 0 (2 * c))
    (hend : n (2 * c) = -n 0)
    (heq : halfBound c (angle (n c) (n 0)) +
      halfBound c (Real.pi - angle (n c) (n 0)) =
      ⟪n c, ∫ t in 0..2 * c, n t⟫_ℝ) :
    (∀ s ∈ Icc 0 c, ⟪n c, n (c - s)⟫_ℝ =
      Real.cos (envelope c (angle (n c) (n 0)) s)) ∧
    (∀ s ∈ Icc 0 c, ⟪n c, n (c + s)⟫_ℝ =
      Real.cos (envelope c (Real.pi - angle (n c) (n 0)) s)) := by
  let α := angle (n c) (n 0)
  let g : ℝ → ℝ := fun t => ⟪n c, n t⟫_ℝ
  have hα0 : 0 ≤ α := angle_nonneg _ _
  have hαπ : α ≤ Real.pi := angle_le_pi _ _
  have hβ0 : 0 ≤ Real.pi - α := by linarith
  have hβπ : Real.pi - α ≤ Real.pi := by linarith
  obtain ⟨hαc, hβc⟩ := midpoint_angle_feasible hc.le hspeed hend
  obtain ⟨hl, hr⟩ := midpoint_cos_envelope_bounds hc.le hunit hspeed hend
  have hg : ContinuousOn g (Icc 0 (2 * c)) := continuousOn_const.inner hcont
  have hlc : ContinuousOn (fun s => g (c - s)) (Icc 0 c) := by
    apply hg.comp (by fun_prop)
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hrc : ContinuousOn (fun s => g (c + s)) (Icc 0 c) := by
    apply hg.comp (by fun_prop)
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hsum :
      (∫ s in 0..c, (g (c - s) - Real.cos (envelope c α s))) +
        (∫ s in 0..c, (g (c + s) - Real.cos (envelope c (Real.pi - α) s))) = 0 := by
    rw [intervalIntegral.integral_sub (hlc.intervalIntegrable_of_Icc hc.le)
        ((continuous_cos_envelope c α).intervalIntegrable 0 c),
      intervalIntegral.integral_sub (hrc.intervalIntegrable_of_Icc hc.le)
        ((continuous_cos_envelope c (Real.pi - α)).intervalIntegrable 0 c),
      integral_cos_envelope_of_feasible hα0 hαπ hαc,
      integral_cos_envelope_of_feasible hβ0 hβπ hβc]
    have hsplit := integral_midpoint_halves hc.le hg
    have hinner := (innerSL ℝ (n c)).intervalIntegral_comp_comm
      (hcont.intervalIntegrable_of_Icc (μ := volume) (by linarith : 0 ≤ 2 * c))
    change (∫ t in 0..2 * c, g t) = ⟪n c, ∫ t in 0..2 * c, n t⟫_ℝ at hinner
    change halfBound c α + halfBound c (Real.pi - α) = _ at heq
    linarith
  obtain ⟨hleft, hright⟩ := Rigidity.continuous_nonneg_pair_integral_zero hc
    (hlc.sub (continuous_cos_envelope c α).continuousOn)
    (hrc.sub (continuous_cos_envelope c (Real.pi - α)).continuousOn)
    (fun s hs => sub_nonneg.mpr (hl s hs))
    (fun s hs => sub_nonneg.mpr (hr s hs)) hsum
  exact ⟨fun s hs => sub_eq_zero.mp (hleft s hs),
    fun s hs => sub_eq_zero.mp (hright s hs)⟩

/-- 可行区间上的包络确为合法的球面角距离。 -/
theorem envelope_mem_Icc {c β s : ℝ} (hβ : 0 ≤ β) (hs : s ∈ Icc 0 c) :
    envelope c β s ∈ Icc 0 Real.pi := by
  constructor
  · exact le_min (le_min hs.1 (by linarith [hs.2])) Real.pi_pos.le
  · exact min_le_right _ _

/-- 在整个前沿区间，中点角 π/2 对应的包络从不触及 π 截顶。 -/
theorem envelope_midpoint_eq {c s : ℝ} (hc : c ≤ criticalHalf) :
    envelope c (Real.pi / 2) s = min s (c + Real.pi / 2 - s) := by
  unfold envelope
  apply min_eq_left
  by_cases hs : s ≤ (c + Real.pi / 2) / 2
  · exact (min_le_left _ _).trans (by dsimp [criticalHalf] at hc; linarith [Real.pi_pos])
  · exact (min_le_right _ _).trans (by dsimp [criticalHalf] at hc; linarith [Real.pi_pos])

end RobustPiGate
