import RobustPiGate.Scalar
import RobustPiGate.Envelope
import RobustPiGate.Geometry

noncomputable section
open Real Set MeasureTheory InnerProductGeometry
open scoped InnerProductSpace
namespace RobustPiGate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- 零向量积分的任意固定方向投影也是零。 -/
theorem integral_inner_eq_zero {n : ℝ → E} {a b : ℝ} (v : E)
    (hn : IntervalIntegrable n volume a b) (hz : (∫ t in a..b, n t) = 0) :
    (∫ t in a..b, ⟪v, n t⟫_ℝ) = 0 := by
  have h := (innerSL ℝ v).intervalIntegral_comp_comm hn
  simpa [hz] using h

/-- 用实际球面路径和零向量积分表述的中点锐下界。 -/
theorem criticalHalf_le_of_spherical_curve {n : ℝ → E} {c : ℝ}
    (hc : 0 < c) (hcont : ContinuousOn n (Icc 0 (2 * c)))
    (hunit : ∀ t ∈ Icc 0 (2 * c), ‖n t‖ = 1)
    (hspeed : SphericalSpeedBound n 0 (2 * c))
    (hend : n (2 * c) = - n 0)
    (hzero : (∫ t in 0..2 * c, n t) = 0) : criticalHalf ≤ c := by
  have hc0 : 0 ≤ c := hc.le
  have hcm : c ∈ Icc 0 (2 * c) := ⟨hc0, by linarith⟩
  let g : ℝ → ℝ := fun t => ⟪n c, n t⟫_ℝ
  have hg : ContinuousOn g (Icc 0 (2 * c)) := continuousOn_const.inner hcont
  have hgzero : (∫ t in 0..2 * c, g t) = 0 :=
    integral_inner_eq_zero (n c) (hcont.intervalIntegrable_of_Icc (by linarith)) hzero
  have hcpi : Real.pi ≤ c := by
    by_contra h
    have hcp : c < Real.pi := lt_of_not_ge h
    have hbound : ∀ t ∈ Icc 0 (2 * c), Real.cos |t - c| ≤ g t := by
      intro t ht
      dsimp [g]
      rw [inner_eq_cos_angle_of_norm_eq_one (hunit c hcm) (hunit t ht)]
      have habs : |t - c| ≤ Real.pi := by
        rw [abs_le]
        constructor <;> linarith [ht.1, ht.2]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (angle_nonneg _ _) habs
        (hspeed c hcm t ht)
    have := pi_le_of_zero_integral_midpoint_bound hc hg hgzero hbound
    linarith
  let α := angle (n c) (n 0)
  have hleftunit : ∀ t ∈ Icc 0 c, ‖n (c - t)‖ = 1 := by
    intro t ht
    apply hunit
    constructor <;> linarith [ht.1, ht.2]
  have hrightunit : ∀ t ∈ Icc 0 c, ‖n (c + t)‖ = 1 := by
    intro t ht
    apply hunit
    constructor <;> linarith [ht.1, ht.2]
  have hleftspeed : SphericalSpeedBound (fun t => n (c - t)) 0 c := by
    intro s hs t ht
    have hcs : c - s ∈ Icc 0 (2 * c) := by constructor <;> linarith [hs.1, hs.2]
    have hct : c - t ∈ Icc 0 (2 * c) := by constructor <;> linarith [ht.1, ht.2]
    have h := hspeed (c - s) hcs (c - t) hct
    convert h using 1
    rw [show c - t - (c - s) = -(t - s) by ring, abs_neg]
  have hrightspeed : SphericalSpeedBound (fun t => n (c + t)) 0 c := by
    intro s hs t ht
    have hcs : c + s ∈ Icc 0 (2 * c) := by constructor <;> linarith [hs.1, hs.2]
    have hct : c + t ∈ Icc 0 (2 * c) := by constructor <;> linarith [ht.1, ht.2]
    have h := hspeed (c + s) hcs (c + t) hct
    convert h using 1 <;> congr 1 <;> ring
  have hleft : ∀ s ∈ Icc 0 c, Real.cos (envelope c α s) ≤ g (c - s) := by
    intro s hs
    simpa [α, g] using cos_envelope_le_inner hc0 hs hleftunit hleftspeed
  have hright : ∀ s ∈ Icc 0 c,
      Real.cos (envelope c (Real.pi - α) s) ≤ g (c + s) := by
    intro s hs
    have h := cos_envelope_le_inner hc0 hs hrightunit hrightspeed
    simpa [α, g, ← two_mul, hend, angle_neg_right] using h
  have hsum := sum_halfBound_le_integral (angle_nonneg (n c) (n 0))
    (angle_le_pi (n c) (n 0))
    (by dsimp [α]; linarith [angle_le_pi (n c) (n 0)] : 0 ≤ Real.pi - α)
    (by dsimp [α]; linarith [angle_nonneg (n c) (n 0)] : Real.pi - α ≤ Real.pi)
    hcpi hg hleft hright
  rw [hgzero] at hsum
  exact criticalHalf_le_of_sum_nonpos (angle_nonneg _ _) (angle_le_pi _ _) hcpi hsum

/-- 任意维的球面反极零均值路径长度下界。 -/
theorem spherical_curve_length_lower_bound {n : ℝ → E} {L : ℝ}
    (hL : 0 < L) (hcont : ContinuousOn n (Icc 0 L))
    (hunit : ∀ t ∈ Icc 0 L, ‖n t‖ = 1)
    (hspeed : SphericalSpeedBound n 0 L)
    (hend : n L = -n 0) (hzero : (∫ t in 0..L, n t) = 0) :
    7 * Real.pi / 3 ≤ L := by
  have heq : 2 * (L / 2) = L := by ring
  have h := criticalHalf_le_of_spherical_curve (c := L / 2) (by linarith)
    (by simpa [heq] using hcont) (by simpa [heq] using hunit)
    (by simpa [heq] using hspeed) (by simpa [heq] using hend)
    (by simpa [heq] using hzero)
  dsimp [criticalHalf] at h
  linarith

end RobustPiGate

