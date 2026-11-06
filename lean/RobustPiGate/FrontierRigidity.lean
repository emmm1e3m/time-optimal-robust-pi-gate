import RobustPiGate.Rigidity

noncomputable section
open Set MeasureTheory InnerProductGeometry
open scoped RealInnerProductSpace

namespace RobustPiGate.FrontierRigidity
open RobustPiGate.Rigidity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- 任意前沿半时长对应的转折时刻与未截顶径向包络。 -/
def turningTime (c : ℝ) : ℝ := (c + Real.pi / 2) / 2
def radialEnvelope (c s : ℝ) : ℝ := min s (c + Real.pi / 2 - s)

theorem halfDuration_pos {c : ℝ} (hc : c ∈ Icc (Real.pi / 2) (7 * Real.pi / 6)) :
    0 < c := by linarith [hc.1, Real.pi_pos]

theorem turningTime_mem {c : ℝ} (hc : c ∈ Icc (Real.pi / 2) (7 * Real.pi / 6)) :
    turningTime c ∈ Icc 0 c := by
  dsimp [turningTime]
  constructor <;> linarith [hc.1, Real.pi_pos]

theorem turningTime_range {c : ℝ} (hc : c ∈ Icc (Real.pi / 2) (7 * Real.pi / 6)) :
    0 < turningTime c ∧ turningTime c < Real.pi := by
  dsimp [turningTime]
  constructor <;> linarith [hc.1, hc.2, Real.pi_pos]

theorem radialEnvelope_turning (c : ℝ) : radialEnvelope c (turningTime c) = turningTime c := by
  dsimp [radialEnvelope, turningTime]
  rw [show c + Real.pi / 2 - (c + Real.pi / 2) / 2 = (c + Real.pi / 2) / 2 by ring, min_self]

theorem radialEnvelope_endpoint {c : ℝ} (hc : Real.pi / 2 ≤ c) :
    radialEnvelope c c = Real.pi / 2 := by
  dsimp [radialEnvelope]
  rw [show c + Real.pi / 2 - c = Real.pi / 2 by ring, min_eq_right hc]

theorem radialEnvelope_range {c s : ℝ}
    (hc : c ∈ Icc (Real.pi / 2) (7 * Real.pi / 6)) (hs : s ∈ Icc 0 c) :
    radialEnvelope c s ∈ Icc 0 Real.pi := by
  dsimp [radialEnvelope]
  constructor
  · exact le_min hs.1 (by linarith [hs.2, Real.pi_pos])
  · by_cases h : s ≤ turningTime c
    · exact (min_le_left _ _).trans (h.trans (turningTime_range hc).2.le)
    · exact (min_le_right _ _).trans (by dsimp [turningTime] at h; linarith [hc.2, Real.pi_pos])

theorem distance_to_turning (c s : ℝ) :
    |s - turningTime c| = turningTime c - radialEnvelope c s := by
  by_cases hs : s ≤ turningTime c
  · rw [abs_of_nonpos (sub_nonpos.mpr hs)]
    dsimp [radialEnvelope]
    rw [min_eq_left (by dsimp [turningTime] at hs; linarith)]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hs))]
    dsimp [radialEnvelope]
    rw [min_eq_right (by dsimp [turningTime] at hs; linarith)]
    dsimp [turningTime]
    ring

/-- 整个时长区间中，精确径向角与球面速度界强制半曲线沿固定大圆。 -/
theorem half_curve_rigidity {c : ℝ}
    (hc : c ∈ Icc (Real.pi / 2) (7 * Real.pi / 6))
    {m : ℝ → E} {v : E} (hv : ‖v‖ = 1)
    (hm : ∀ s ∈ Icc 0 c, ‖m s‖ = 1)
    (hd : ∀ s ∈ Icc 0 c, angle v (m s) = radialEnvelope c s)
    (hLip : ∀ s ∈ Icc 0 c, ∀ t ∈ Icc 0 c, angle (m s) (m t) ≤ |s - t|) :
    ∀ s ∈ Icc 0 c,
      m s = Real.cos (radialEnvelope c s) • v + Real.sin (radialEnvelope c s) • m c := by
  have hcm : c ∈ Icc 0 c := ⟨(halfDuration_pos hc).le, le_rfl⟩
  have hsin : Real.sin (turningTime c) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (turningTime_range hc).1 (turningTime_range hc).2).ne'
  have H : ∀ s ∈ Icc 0 c,
      Real.sin (turningTime c) • m s =
        Real.sin (turningTime c - radialEnvelope c s) • v +
        Real.sin (radialEnvelope c s) • m (turningTime c) := by
    intro s hs
    apply geodesic_interpolation hv (hm s hs) (hm (turningTime c) (turningTime_mem hc))
      (turningTime_range hc) (hd s hs)
    · simpa only [radialEnvelope_turning] using hd (turningTime c) (turningTime_mem hc)
    · simpa only [distance_to_turning] using hLip s hs (turningTime c) (turningTime_mem hc)
  have Hc := H c hcm
  rw [radialEnvelope_endpoint hc.1, Real.sin_sub_pi_div_two, Real.sin_pi_div_two, one_smul] at Hc
  intro s hs
  apply smul_right_injective E hsin
  calc
    Real.sin (turningTime c) • m s =
        Real.sin (turningTime c - radialEnvelope c s) • v +
        Real.sin (radialEnvelope c s) • m (turningTime c) := H s hs
    _ = (Real.sin (turningTime c) * Real.cos (radialEnvelope c s)) • v +
        Real.sin (radialEnvelope c s) •
          ((-Real.cos (turningTime c)) • v + m (turningTime c)) := by
      rw [Real.sin_sub]
      module
    _ = Real.sin (turningTime c) •
        (Real.cos (radialEnvelope c s) • v + Real.sin (radialEnvelope c s) • m c) := by
      rw [← Hc]
      module

theorem half_endpoint_orthogonal {c : ℝ}
    (hc : c ∈ Icc (Real.pi / 2) (7 * Real.pi / 6)) {m : ℝ → E} {v : E}
    (hd : ∀ s ∈ Icc 0 c, angle v (m s) = radialEnvelope c s) : ⟪v, m c⟫ = 0 := by
  apply (inner_eq_zero_iff_angle_eq_pi_div_two _ _).2
  simpa only [radialEnvelope_endpoint hc.1] using hd c ⟨(halfDuration_pos hc).le, le_rfl⟩

/-- 原时间方向的三弧相位；端点 c=π/2 时允许外段退化。 -/
def threeArcPhase (c t : ℝ) : ℝ :=
  if t ≤ (c - Real.pi / 2) / 2 then Real.pi / 2 + t
  else if t ≤ (3 * c + Real.pi / 2) / 2 then c - t
  else t - 2 * c - Real.pi / 2

theorem threeArcPhase_eq_left {c t : ℝ}
    (hc : Real.pi / 2 ≤ c) (ht : t ≤ c) :
    threeArcPhase c t = radialEnvelope c (c - t) := by
  by_cases h : t ≤ (c - Real.pi / 2) / 2
  · simp only [threeArcPhase, ite_eq_left h]
    dsimp [radialEnvelope]
    rw [min_eq_right (by linarith)]
    ring
  · have ht2 : t ≤ (3 * c + Real.pi / 2) / 2 := by linarith [Real.pi_pos]
    simp only [threeArcPhase, ite_eq_right h, ite_eq_left ht2]
    dsimp [radialEnvelope]
    rw [min_eq_left (by linarith)]

theorem threeArcPhase_eq_right {c t : ℝ}
    (hc : Real.pi / 2 ≤ c) (ht : c ≤ t) :
    threeArcPhase c t = -radialEnvelope c (t - c) := by
  have ht1 : ¬ t ≤ (c - Real.pi / 2) / 2 := by linarith [Real.pi_pos]
  by_cases h : t ≤ (3 * c + Real.pi / 2) / 2
  · simp only [threeArcPhase, ite_eq_right ht1, ite_eq_left h]
    dsimp [radialEnvelope]
    rw [min_eq_left (by linarith)]
    ring
  · simp only [threeArcPhase, ite_eq_right ht1, ite_eq_right h]
    dsimp [radialEnvelope]
    rw [min_eq_right (by linarith)]
    ring

theorem three_arc_of_two_halves {c : ℝ} (hc : Real.pi / 2 ≤ c)
    {n : ℝ → E} {v e : E}
    (hl : ∀ s ∈ Icc 0 c,
      n (c - s) = Real.cos (radialEnvelope c s) • v + Real.sin (radialEnvelope c s) • e)
    (hr : ∀ s ∈ Icc 0 c,
      n (c + s) = Real.cos (radialEnvelope c s) • v + Real.sin (radialEnvelope c s) • (-e)) :
    ∀ t ∈ Icc 0 (2 * c),
      n t = Real.cos (threeArcPhase c t) • v + Real.sin (threeArcPhase c t) • e := by
  intro t ht
  by_cases htc : t ≤ c
  · have hs : c - t ∈ Icc 0 c := ⟨sub_nonneg.mpr htc, by linarith [ht.1]⟩
    have h := hl (c - t) hs
    rw [show c - (c - t) = t by ring] at h
    rw [threeArcPhase_eq_left hc htc]
    exact h
  · have hct : c ≤ t := le_of_not_ge htc
    have hs : t - c ∈ Icc 0 c := ⟨sub_nonneg.mpr hct, by linarith [ht.2]⟩
    have h := hr (t - c) hs
    rw [show c + (t - c) = t by ring] at h
    rw [threeArcPhase_eq_right hc hct, Real.cos_neg, Real.sin_neg]
    simpa only [smul_neg, neg_smul] using h

/-- 前沿的全部逐点径向等号决定整条轨迹，不预设固定轴或分段控制。 -/
theorem spherical_equality_rigidity {c : ℝ}
    (hc : c ∈ Icc (Real.pi / 2) (7 * Real.pi / 6)) {n : ℝ → E}
    (hn : ∀ t ∈ Icc 0 (2 * c), ‖n t‖ = 1)
    (hend : n (2 * c) = -n 0)
    (hLip : ∀ s ∈ Icc 0 (2 * c), ∀ t ∈ Icc 0 (2 * c), angle (n s) (n t) ≤ |s - t|)
    (hleft : ∀ s ∈ Icc 0 c, angle (n c) (n (c - s)) = radialEnvelope c s)
    (hright : ∀ s ∈ Icc 0 c, angle (n c) (n (c + s)) = radialEnvelope c s) :
    ⟪n c, n 0⟫ = 0 ∧ ∀ t ∈ Icc 0 (2 * c),
      n t = Real.cos (threeArcPhase c t) • n c + Real.sin (threeArcPhase c t) • n 0 := by
  have hc0 := halfDuration_pos hc
  have hL : ∀ s ∈ Icc 0 c, c - s ∈ Icc 0 (2 * c) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hR : ∀ s ∈ Icc 0 c, c + s ∈ Icc 0 (2 * c) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hv : ‖n c‖ = 1 := hn c ⟨hc0.le, by linarith⟩
  have hl := half_curve_rigidity hc hv (fun s hs => hn _ (hL s hs)) hleft
    (fun s hs t ht => (hLip _ (hL s hs) _ (hL t ht)).trans_eq (by
      rw [show (c - s) - (c - t) = -(s - t) by ring, abs_neg]))
  have hr := half_curve_rigidity hc hv (fun s hs => hn _ (hR s hs)) hright
    (fun s hs t ht => (hLip _ (hR s hs) _ (hR t ht)).trans_eq (by
      rw [show (c + s) - (c + t) = s - t by ring]))
  have horth := half_endpoint_orthogonal hc hleft
  simp only [sub_self] at hl horth
  simp only [← two_mul, hend] at hr
  exact ⟨horth, three_arc_of_two_halves hc.1 hl hr⟩

end RobustPiGate.FrontierRigidity

#print axioms RobustPiGate.FrontierRigidity.spherical_equality_rigidity
