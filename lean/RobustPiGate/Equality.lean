import RobustPiGate.SharpLength
import RobustPiGate.Rigidity

noncomputable section
open Real Set MeasureTheory InnerProductGeometry
open scoped InnerProductSpace
namespace RobustPiGate
open Rigidity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- 临界直角端点的半段积分下界恰好为零。 -/
theorem critical_halfBound_right_angle : halfBound halfDuration (Real.pi / 2) = 0 := by
  have h := (critical_sum_eq_zero_iff
    (by linarith [Real.pi_pos] : 0 ≤ Real.pi / 2)
    (by linarith [Real.pi_pos] : Real.pi / 2 ≤ Real.pi)).2 rfl
  rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring] at h
  change halfBound criticalHalf (Real.pi / 2) = 0
  linarith

/-- 临界直角包络在整个半区间内都低于 π，因此就是刚性模块的径向包络。 -/
theorem envelope_critical_right_angle {s : ℝ} (hs : s ∈ Icc 0 halfDuration) :
    envelope halfDuration (Real.pi / 2) s = radialEnvelope s := by
  have heq : halfDuration + Real.pi / 2 = 5 * Real.pi / 3 := by
    dsimp [halfDuration]; ring
  unfold envelope
  rw [heq]
  change min (radialEnvelope s) Real.pi = radialEnvelope s
  exact min_eq_left (radialEnvelope_range hs).2

/-- 刚性径向包络的投影积分为零。 -/
theorem integral_cos_radialEnvelope :
    (∫ s in (0 : ℝ)..halfDuration, Real.cos (radialEnvelope s)) = 0 := by
  calc
    _ = ∫ s in (0 : ℝ)..halfDuration,
        Real.cos (envelope halfDuration (Real.pi / 2) s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le halfDuration_pos.le] at hs
      exact congrArg Real.cos (envelope_critical_right_angle hs).symm
    _ = halfBound halfDuration (Real.pi / 2) :=
      integral_cos_envelope (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
        (by dsimp [halfDuration]; linarith [Real.pi_pos])
    _ = 0 := critical_halfBound_right_angle

/-- 临界半曲线的零投影积分使全部逐点径向角界饱和。 -/
theorem radial_angle_eq_of_zero_projection {m : ℝ → E} {v : E}
    (hv : ‖v‖ = 1) (hm : ∀ s ∈ Icc 0 halfDuration, ‖m s‖ = 1)
    (hmc : ContinuousOn m (Icc 0 halfDuration))
    (hproj : ∀ s ∈ Icc 0 halfDuration,
      Real.cos (radialEnvelope s) ≤ ⟪v, m s⟫_ℝ)
    (hint : (∫ s in (0 : ℝ)..halfDuration, ⟪v, m s⟫_ℝ) = 0) :
    ∀ s ∈ Icc 0 halfDuration, angle v (m s) = radialEnvelope s := by
  have hpcont : ContinuousOn (fun s => ⟪v, m s⟫_ℝ) (Icc 0 halfDuration) :=
    continuousOn_const.inner hmc
  have hfcont : ContinuousOn (fun s => Real.cos (radialEnvelope s))
      (Icc 0 halfDuration) :=
    (Real.continuous_cos.comp continuous_radialEnvelope).continuousOn
  have hgap : ∀ s ∈ Icc 0 halfDuration,
      ⟪v, m s⟫_ℝ - Real.cos (radialEnvelope s) = 0 := by
    apply continuous_nonneg_zero_integral_eq_zero halfDuration_pos (hpcont.sub hfcont)
    · intro s hs; exact sub_nonneg.mpr (hproj s hs)
    · change (∫ s in (0 : ℝ)..halfDuration,
        (⟪v, m s⟫_ℝ - Real.cos (radialEnvelope s))) = 0
      rw [intervalIntegral.integral_sub
        (hpcont.intervalIntegrable_of_Icc halfDuration_pos.le)
        (hfcont.intervalIntegrable_of_Icc halfDuration_pos.le),
        hint, integral_cos_radialEnvelope, sub_self]
  intro s hs
  exact angle_eq_of_projection_eq hv (hm s hs) (radialEnvelope_range hs)
    (sub_eq_zero.mp (hgap s hs))

variable [CompleteSpace E]

/-- 临界零均值球面曲线的真实条件强制两个半段的全部径向角界取等号。 -/
theorem radial_equalities_of_critical_curve {n : ℝ → E}
    (hcont : ContinuousOn n (Icc 0 (2 * halfDuration)))
    (hunit : ∀ t ∈ Icc 0 (2 * halfDuration), ‖n t‖ = 1)
    (hspeed : SphericalSpeedBound n 0 (2 * halfDuration))
    (hend : n (2 * halfDuration) = -n 0)
    (hzero : (∫ t in 0..2 * halfDuration, n t) = 0) :
    angle (n halfDuration) (n 0) = Real.pi / 2 ∧
    (∀ s ∈ Icc 0 halfDuration,
      angle (n halfDuration) (n (halfDuration - s)) = radialEnvelope s) ∧
    (∀ s ∈ Icc 0 halfDuration,
      angle (n halfDuration) (n (halfDuration + s)) = radialEnvelope s) := by
  let c : ℝ := halfDuration
  have hendc : n (2 * c) = -n 0 := hend
  have hc0 : 0 ≤ c := halfDuration_pos.le
  have hcπ : Real.pi ≤ c := by dsimp [c, halfDuration]; linarith [Real.pi_pos]
  have hcm : c ∈ Icc 0 (2 * c) := ⟨hc0, by linarith⟩
  have hL (s : ℝ) (hs : s ∈ Icc 0 c) : c - s ∈ Icc 0 (2 * c) := by
    constructor <;> linarith [hs.1, hs.2]
  have hR (s : ℝ) (hs : s ∈ Icc 0 c) : c + s ∈ Icc 0 (2 * c) := by
    constructor <;> linarith [hs.1, hs.2]
  let g : ℝ → ℝ := fun t => ⟪n c, n t⟫_ℝ
  have hg : ContinuousOn g (Icc 0 (2 * c)) := continuousOn_const.inner hcont
  have hgzero : (∫ t in 0..2 * c, g t) = 0 :=
    integral_inner_eq_zero (n c) (hcont.intervalIntegrable_of_Icc (by linarith)) hzero
  let α : ℝ := angle (n c) (n 0)
  have hα0 : 0 ≤ α := angle_nonneg _ _
  have hαπ : α ≤ Real.pi := angle_le_pi _ _
  have hleftunit : ∀ t ∈ Icc 0 c, ‖n (c - t)‖ = 1 :=
    fun t ht => hunit _ (hL t ht)
  have hrightunit : ∀ t ∈ Icc 0 c, ‖n (c + t)‖ = 1 :=
    fun t ht => hunit _ (hR t ht)
  have hleftspeed : SphericalSpeedBound (fun t => n (c - t)) 0 c := by
    intro s hs t ht
    have h := hspeed (c - s) (hL s hs) (c - t) (hL t ht)
    convert h using 1
    rw [show c - t - (c - s) = -(t - s) by ring, abs_neg]
  have hrightspeed : SphericalSpeedBound (fun t => n (c + t)) 0 c := by
    intro s hs t ht
    have h := hspeed (c + s) (hR s hs) (c + t) (hR t ht)
    convert h using 1
    congr 1
    ring
  have hleft : ∀ s ∈ Icc 0 c, Real.cos (envelope c α s) ≤ g (c - s) := by
    intro s hs
    simpa [α, g] using cos_envelope_le_inner hc0 hs hleftunit hleftspeed
  have hright : ∀ s ∈ Icc 0 c,
      Real.cos (envelope c (Real.pi - α) s) ≤ g (c + s) := by
    intro s hs
    have h := cos_envelope_le_inner hc0 hs hrightunit hrightspeed
    simpa [α, g, ← two_mul, hendc, angle_neg_right] using h
  have hsum := sum_halfBound_le_integral hα0 hαπ
    (by linarith : 0 ≤ Real.pi - α) (by linarith : Real.pi - α ≤ Real.pi)
    hcπ hg hleft hright
  rw [hgzero] at hsum
  have hnonneg : 0 ≤ halfBound c α + halfBound c (Real.pi - α) :=
    critical_sum_nonneg hα0 hαπ
  have hα : α = Real.pi / 2 :=
    (critical_sum_eq_zero_iff hα0 hαπ).mp (le_antisymm hsum hnonneg)
  have hπsub : Real.pi - α = Real.pi / 2 := by rw [hα]; ring
  have hlc : ContinuousOn (fun s => n (c - s)) (Icc 0 c) :=
    hcont.comp (by fun_prop) hL
  have hrc : ContinuousOn (fun s => n (c + s)) (Icc 0 c) :=
    hcont.comp (by fun_prop) hR
  have hlg : ContinuousOn (fun s => g (c - s)) (Icc 0 c) :=
    continuousOn_const.inner hlc
  have hrg : ContinuousOn (fun s => g (c + s)) (Icc 0 c) :=
    continuousOn_const.inner hrc
  have hlower := halfBound_le_integral hα0 hαπ hcπ hlg hleft
  have hrlower := halfBound_le_integral
    (by linarith : 0 ≤ Real.pi - α) (by linarith : Real.pi - α ≤ Real.pi)
    hcπ hrg hright
  rw [hα, critical_halfBound_right_angle] at hlower
  rw [hπsub, critical_halfBound_right_angle] at hrlower
  have hsumint : (∫ s in 0..c, g (c - s)) + (∫ s in 0..c, g (c + s)) = 0 := by
    rw [intervalIntegral.integral_comp_sub_left, intervalIntegral.integral_comp_add_left]
    simp only [sub_self, sub_zero, add_zero, ← two_mul]
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact hgzero
    · exact (hg.mono (by intro t ht; constructor <;> linarith [ht.1, ht.2])).intervalIntegrable_of_Icc hc0
    · exact (hg.mono (by intro t ht; constructor <;> linarith [ht.1, ht.2])).intervalIntegrable_of_Icc
        (by linarith : c ≤ 2 * c)
  have hlzero : (∫ s in 0..c, g (c - s)) = 0 := by linarith
  have hrzero : (∫ s in 0..c, g (c + s)) = 0 := by linarith
  have hleftproj : ∀ s ∈ Icc 0 halfDuration,
      Real.cos (radialEnvelope s) ≤ ⟪n c, n (c - s)⟫_ℝ := by
    intro s hs
    have h := hleft s hs
    rw [hα, envelope_critical_right_angle hs] at h
    exact h
  have hrightproj : ∀ s ∈ Icc 0 halfDuration,
      Real.cos (radialEnvelope s) ≤ ⟪n c, n (c + s)⟫_ℝ := by
    intro s hs
    have h := hright s hs
    rw [hπsub, envelope_critical_right_angle hs] at h
    exact h
  exact ⟨hα, radial_angle_eq_of_zero_projection (hunit c hcm) hleftunit hlc hleftproj hlzero,
    radial_angle_eq_of_zero_projection (hunit c hcm) hrightunit hrc hrightproj hrzero⟩

/-- 临界零均值、反极端点和球面速度界直接决定整条三弧最优轨道。 -/
theorem spherical_curve_equality_rigidity {n : ℝ → E}
    (hcont : ContinuousOn n (Icc 0 (7 * Real.pi / 3)))
    (hunit : ∀ t ∈ Icc 0 (7 * Real.pi / 3), ‖n t‖ = 1)
    (hspeed : SphericalSpeedBound n 0 (7 * Real.pi / 3))
    (hend : n (7 * Real.pi / 3) = -n 0)
    (hzero : (∫ t in 0..7 * Real.pi / 3, n t) = 0) :
    ⟪n halfDuration, n 0⟫_ℝ = 0 ∧
    ∀ t ∈ Icc 0 (7 * Real.pi / 3),
      n t = Real.cos (threeArcPhase t) • n halfDuration +
        Real.sin (threeArcPhase t) • n 0 := by
  have hlength : 2 * halfDuration = 7 * Real.pi / 3 := by dsimp [halfDuration]; ring
  rw [← hlength] at hcont hunit hspeed hend hzero ⊢
  obtain ⟨_, hl, hr⟩ := radial_equalities_of_critical_curve hcont hunit hspeed hend hzero
  exact Rigidity.spherical_equality_rigidity hunit hend
    (by intro s hs t ht; simpa [abs_sub_comm] using hspeed s hs t ht) hl hr

end RobustPiGate

#print axioms RobustPiGate.radial_equalities_of_critical_curve
#print axioms RobustPiGate.spherical_curve_equality_rigidity
