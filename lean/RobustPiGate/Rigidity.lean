import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

noncomputable section
open Set MeasureTheory InnerProductGeometry
open scoped RealInnerProductSpace

namespace RobustPiGate.Rigidity

/-- 连续非负投影差的积分为零时，差在闭区间上逐点为零。 -/
theorem continuous_nonneg_zero_integral_eq_zero
    {g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn g (Icc a b))
    (hn : ∀ s ∈ Icc a b, 0 ≤ g s)
    (hi : (∫ s in a..b, g s) = 0) :
    ∀ s ∈ Icc a b, g s = 0 := by
  intro s hs
  by_contra h
  have hpos : 0 < g s := lt_of_le_of_ne (hn s hs) (Ne.symm h)
  have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hab (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc a b)) hc
    (fun t ht => hn t ⟨ht.1.le, ht.2⟩) ⟨s, hs, hpos⟩
  simp only [intervalIntegral.integral_zero, hi, lt_self_iff_false] at hlt

/-- 两个连续非负投影差的积分之和为零时，两者都逐点为零。 -/
theorem continuous_nonneg_pair_integral_zero
    {g h : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hgc : ContinuousOn g (Icc a b)) (hhc : ContinuousOn h (Icc a b))
    (hgn : ∀ s ∈ Icc a b, 0 ≤ g s) (hhn : ∀ s ∈ Icc a b, 0 ≤ h s)
    (hi : (∫ s in a..b, g s) + (∫ s in a..b, h s) = 0) :
    (∀ s ∈ Icc a b, g s = 0) ∧ (∀ s ∈ Icc a b, h s = 0) := by
  have hg0 := intervalIntegral.integral_nonneg (μ := volume) hab.le hgn
  have hh0 := intervalIntegral.integral_nonneg (μ := volume) hab.le hhn
  exact ⟨continuous_nonneg_zero_integral_eq_zero hab hgc hgn (by linarith),
    continuous_nonneg_zero_integral_eq_zero hab hhc hhn (by linarith)⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- 单位向量的投影等号可恢复其球面距离。 -/
theorem angle_eq_of_projection_eq {v x : E} {α : ℝ}
    (hv : ‖v‖ = 1) (hx : ‖x‖ = 1)
    (hα : α ∈ Icc 0 Real.pi) (hp : ⟪v, x⟫ = Real.cos α) :
    angle v x = α := by
  apply Real.injOn_cos ⟨angle_nonneg _ _, angle_le_pi _ _⟩ hα
  simpa only [cos_angle, hv, hx, mul_one, div_one] using hp

/-- 径向角的增长已耗尽全部角距离时，中间点满足球面线性插值公式。 -/
theorem geodesic_interpolation
    {v x p : E} {α β : ℝ}
    (hv : ‖v‖ = 1) (hx : ‖x‖ = 1) (hp : ‖p‖ = 1)
    (hβ : 0 < β ∧ β < Real.pi)
    (hvx : angle v x = α) (hvp : angle v p = β)
    (hxp : angle x p ≤ β - α) :
    Real.sin β • x = Real.sin (β - α) • v + Real.sin α • p := by
  have heq : angle v p = angle v x + angle x p := by
    have ht := angle_le_angle_add_angle v x p
    rw [hvp, hvx] at ht ⊢
    linarith
  have hxp' : angle x p = β - α := by rw [hvp, hvx] at heq; linarith
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hmem : x ∈ Submodule.span NNReal {v, p} := by
    rcases (angle_eq_angle_add_angle_iff hx0).1 heq with h | h
    · rw [hvp] at h; exact (ne_of_lt hβ.2 h).elim
    · exact h
  rw [Submodule.mem_span_pair] at hmem
  obtain ⟨a, b, hrep⟩ := hmem
  have hrep' : (a : ℝ) • v + (b : ℝ) • p = x := by
    simpa only [NNReal.smul_def] using hrep
  have hvv : ⟪v, v⟫ = (1 : ℝ) := by simp [hv]
  have hpp : ⟪p, p⟫ = (1 : ℝ) := by simp [hp]
  have hvp' : ⟪v, p⟫ = Real.cos β := by
    rw [inner_eq_cos_angle_of_norm_eq_one hv hp, hvp]
  have hpv : ⟪p, v⟫ = Real.cos β := by rw [real_inner_comm, hvp']
  have h1 : (a : ℝ) + (b : ℝ) * Real.cos β = Real.cos α := by
    have h := congrArg (fun z => ⟪v, z⟫) hrep'
    simpa only [inner_add_right, real_inner_smul_right, hvv, hvp', mul_one,
      inner_eq_cos_angle_of_norm_eq_one hv hx, hvx] using h
  have h2 : (a : ℝ) * Real.cos β + (b : ℝ) = Real.cos (β - α) := by
    have h := congrArg (fun z => ⟪p, z⟫) hrep'
    simpa only [inner_add_right, real_inner_smul_right, hpv, hpp, mul_one,
      inner_eq_cos_angle_of_norm_eq_one hp hx, angle_comm p x, hxp'] using h
  have hsin : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβ.1 hβ.2
  have hsquare := Real.sin_sq_add_cos_sq β
  have hb : Real.sin β * (b : ℝ) = Real.sin α := by
    apply mul_left_cancel₀ hsin.ne'
    rw [Real.cos_sub] at h2
    linear_combination (b : ℝ) * hsquare - Real.cos β * h1 + h2
  have ha : Real.sin β * (a : ℝ) = Real.sin (β - α) := by
    rw [Real.sin_sub]
    linear_combination Real.sin β * h1 - Real.cos β * hb
  rw [← hrep', smul_add, smul_smul, smul_smul, ha, hb]

/-- 临界半曲线的半时长、转折时刻和径向角。 -/
def halfDuration : ℝ := 7 * Real.pi / 6
def turningTime : ℝ := 5 * Real.pi / 6
def radialEnvelope (s : ℝ) : ℝ := min s (5 * Real.pi / 3 - s)

theorem halfDuration_pos : 0 < halfDuration := by
  dsimp [halfDuration]; positivity

theorem turningTime_mem : turningTime ∈ Icc 0 halfDuration := by
  dsimp [turningTime, halfDuration]
  constructor <;> linarith [Real.pi_pos]

theorem turningTime_range : 0 < turningTime ∧ turningTime < Real.pi := by
  dsimp [turningTime]
  constructor <;> linarith [Real.pi_pos]

theorem radialEnvelope_turning : radialEnvelope turningTime = turningTime := by
  dsimp [radialEnvelope, turningTime]
  have h : 5 * Real.pi / 3 - 5 * Real.pi / 6 = 5 * Real.pi / 6 := by ring
  rw [h, min_self]

theorem radialEnvelope_endpoint : radialEnvelope halfDuration = Real.pi / 2 := by
  dsimp [radialEnvelope, halfDuration]
  rw [min_eq_right (by linarith [Real.pi_pos])]
  ring

theorem radialEnvelope_range {s : ℝ} (hs : s ∈ Icc 0 halfDuration) :
    radialEnvelope s ∈ Icc 0 Real.pi := by
  dsimp [radialEnvelope]
  dsimp [halfDuration] at hs
  constructor
  · exact le_min hs.1 (by linarith [hs.2, Real.pi_pos])
  · by_cases h : s ≤ 5 * Real.pi / 6
    · exact (min_le_left _ _).trans (by linarith [Real.pi_pos])
    · exact (min_le_right _ _).trans (by linarith [Real.pi_pos])

theorem distance_to_turning (s : ℝ) :
    |s - turningTime| = turningTime - radialEnvelope s := by
  by_cases hs : s ≤ turningTime
  · rw [abs_of_nonpos (sub_nonpos.mpr hs)]
    dsimp [radialEnvelope]
    rw [min_eq_left (by dsimp [turningTime] at hs; linarith)]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hs))]
    dsimp [radialEnvelope]
    rw [min_eq_right (by dsimp [turningTime] at hs; linarith)]
    dsimp [turningTime]
    ring

/-- 只用球面角距离的速度界和精确距离包络，恢复固定大圆上的全部半曲线。 -/
theorem half_curve_rigidity
    {m : ℝ → E} {v : E} (hv : ‖v‖ = 1)
    (hm : ∀ s ∈ Icc 0 halfDuration, ‖m s‖ = 1)
    (hd : ∀ s ∈ Icc 0 halfDuration, angle v (m s) = radialEnvelope s)
    (hLip : ∀ s ∈ Icc 0 halfDuration, ∀ t ∈ Icc 0 halfDuration,
      angle (m s) (m t) ≤ |s - t|) :
    ∀ s ∈ Icc 0 halfDuration,
      m s = Real.cos (radialEnvelope s) • v +
        Real.sin (radialEnvelope s) • m halfDuration := by
  have hc : halfDuration ∈ Icc 0 halfDuration := ⟨halfDuration_pos.le, le_rfl⟩
  have hsin : Real.sin turningTime ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi turningTime_range.1 turningTime_range.2).ne'
  have H : ∀ s ∈ Icc 0 halfDuration,
      Real.sin turningTime • m s =
        Real.sin (turningTime - radialEnvelope s) • v +
        Real.sin (radialEnvelope s) • m turningTime := by
    intro s hs
    apply geodesic_interpolation hv (hm s hs) (hm turningTime turningTime_mem)
      turningTime_range (hd s hs)
    · simpa only [radialEnvelope_turning] using hd turningTime turningTime_mem
    · simpa only [distance_to_turning] using hLip s hs turningTime turningTime_mem
  have Hc := H halfDuration hc
  rw [radialEnvelope_endpoint, Real.sin_sub_pi_div_two, Real.sin_pi_div_two,
    one_smul] at Hc
  intro s hs
  apply smul_right_injective E hsin
  calc
    Real.sin turningTime • m s =
        Real.sin (turningTime - radialEnvelope s) • v +
          Real.sin (radialEnvelope s) • m turningTime := H s hs
    _ = (Real.sin turningTime * Real.cos (radialEnvelope s)) • v +
        Real.sin (radialEnvelope s) •
          ((-Real.cos turningTime) • v + m turningTime) := by
      rw [Real.sin_sub]
      module
    _ = Real.sin turningTime •
        (Real.cos (radialEnvelope s) • v +
          Real.sin (radialEnvelope s) • m halfDuration) := by
      rw [← Hc]
      module

/-- 半曲线的端点就是与中点垂直的单位大圆方向。 -/
theorem half_endpoint_orthogonal
    {m : ℝ → E} {v : E}
    (hd : ∀ s ∈ Icc 0 halfDuration, angle v (m s) = radialEnvelope s) :
    ⟪v, m halfDuration⟫ = 0 := by
  apply (inner_eq_zero_iff_angle_eq_pi_div_two _ _).2
  simpa only [radialEnvelope_endpoint] using
    hd halfDuration ⟨halfDuration_pos.le, le_rfl⟩

/-- 论文中归一化的横向方向 e(s)，在每个 s>0 处恰等于固定端点。 -/
theorem half_direction_eq_endpoint
    {m : ℝ → E} {v : E} (hv : ‖v‖ = 1)
    (hm : ∀ s ∈ Icc 0 halfDuration, ‖m s‖ = 1)
    (hd : ∀ s ∈ Icc 0 halfDuration, angle v (m s) = radialEnvelope s)
    (hLip : ∀ s ∈ Icc 0 halfDuration, ∀ t ∈ Icc 0 halfDuration,
      angle (m s) (m t) ≤ |s - t|)
    {s : ℝ} (hs : s ∈ Ioc 0 halfDuration) :
    (Real.sin (radialEnvelope s))⁻¹ •
      (m s - Real.cos (radialEnvelope s) • v) = m halfDuration := by
  have hfpos : 0 < radialEnvelope s := by
    dsimp [radialEnvelope]
    apply lt_min hs.1
    have hu := hs.2
    dsimp [halfDuration] at hu
    linarith [Real.pi_pos]
  have hfle : radialEnvelope s ≤ turningTime := by
    have h := abs_nonneg (s - turningTime)
    rw [distance_to_turning] at h
    linarith
  have hsin : Real.sin (radialEnvelope s) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hfpos (hfle.trans_lt turningTime_range.2)).ne'
  have hform := half_curve_rigidity hv hm hd hLip s ⟨hs.1.le, hs.2⟩
  rw [hform]
  have hcancel : Real.cos (radialEnvelope s) • v +
      Real.sin (radialEnvelope s) • m halfDuration -
      Real.cos (radialEnvelope s) • v =
      Real.sin (radialEnvelope s) • m halfDuration := by module
  rw [hcancel, smul_smul, inv_mul_cancel₀ hsin, one_smul]

theorem continuous_radialEnvelope : Continuous radialEnvelope := by
  exact continuous_id.min (continuous_const.sub continuous_id)

/-- 连续投影下界的积分取等号，足以触发大圆刚性。 -/
theorem half_curve_rigidity_of_integral_eq
    {m : ℝ → E} {v : E} (hv : ‖v‖ = 1)
    (hm : ∀ s ∈ Icc 0 halfDuration, ‖m s‖ = 1)
    (hmc : ContinuousOn m (Icc 0 halfDuration))
    (hproj : ∀ s ∈ Icc 0 halfDuration,
      Real.cos (radialEnvelope s) ≤ ⟪v, m s⟫)
    (hint : (∫ s in (0 : ℝ)..halfDuration, ⟪v, m s⟫) =
      ∫ s in (0 : ℝ)..halfDuration, Real.cos (radialEnvelope s))
    (hLip : ∀ s ∈ Icc 0 halfDuration, ∀ t ∈ Icc 0 halfDuration,
      angle (m s) (m t) ≤ |s - t|) :
    ⟪v, m halfDuration⟫ = 0 ∧
    ∀ s ∈ Icc 0 halfDuration,
      m s = Real.cos (radialEnvelope s) • v +
        Real.sin (radialEnvelope s) • m halfDuration := by
  have hpcont : ContinuousOn (fun s => ⟪v, m s⟫) (Icc 0 halfDuration) :=
    continuousOn_const.inner hmc
  have hfcont : ContinuousOn (fun s => Real.cos (radialEnvelope s))
      (Icc 0 halfDuration) :=
    (Real.continuous_cos.comp continuous_radialEnvelope).continuousOn
  have hgap : ∀ s ∈ Icc 0 halfDuration,
      ⟪v, m s⟫ - Real.cos (radialEnvelope s) = 0 := by
    apply continuous_nonneg_zero_integral_eq_zero halfDuration_pos (hpcont.sub hfcont)
    · intro s hs; exact sub_nonneg.mpr (hproj s hs)
    · change (∫ s in (0 : ℝ)..halfDuration,
        (⟪v, m s⟫ - Real.cos (radialEnvelope s))) = 0
      rw [intervalIntegral.integral_sub
        (hpcont.intervalIntegrable_of_Icc halfDuration_pos.le)
        (hfcont.intervalIntegrable_of_Icc halfDuration_pos.le), hint, sub_self]
  have hd : ∀ s ∈ Icc 0 halfDuration, angle v (m s) = radialEnvelope s := by
    intro s hs
    exact angle_eq_of_projection_eq hv (hm s hs) (radialEnvelope_range hs)
      (sub_eq_zero.mp (hgap s hs))
  exact ⟨half_endpoint_orthogonal hd, half_curve_rigidity hv hm hd hLip⟩

/-- 原时间方向中的三弧相位，转折点为 π/3 和 2π。 -/
def threeArcPhase (t : ℝ) : ℝ :=
  if t ≤ Real.pi / 3 then Real.pi / 2 + t
  else if t ≤ 2 * Real.pi then 7 * Real.pi / 6 - t
  else t - 17 * Real.pi / 6

theorem threeArcPhase_eq_left {t : ℝ} (ht : t ≤ halfDuration) :
    threeArcPhase t = radialEnvelope (halfDuration - t) := by
  by_cases h : t ≤ Real.pi / 3
  · simp only [threeArcPhase, ite_eq_left h]
    dsimp [radialEnvelope, halfDuration]
    rw [min_eq_right (by linarith)]
    ring
  · have ht2 : t ≤ 2 * Real.pi := by dsimp [halfDuration] at ht; linarith [Real.pi_pos]
    simp only [threeArcPhase, ite_eq_right h, ite_eq_left ht2]
    dsimp [radialEnvelope, halfDuration]
    rw [min_eq_left (by linarith)]

theorem threeArcPhase_eq_right {t : ℝ} (ht : halfDuration ≤ t) :
    threeArcPhase t = -radialEnvelope (t - halfDuration) := by
  have ht1 : ¬ t ≤ Real.pi / 3 := by dsimp [halfDuration] at ht; linarith [Real.pi_pos]
  by_cases h : t ≤ 2 * Real.pi
  · simp only [threeArcPhase, ite_eq_right ht1, ite_eq_left h]
    dsimp [radialEnvelope, halfDuration]
    rw [min_eq_left (by linarith)]
    ring
  · simp only [threeArcPhase, ite_eq_right ht1, ite_eq_right h]
    dsimp [radialEnvelope, halfDuration]
    rw [min_eq_right (by linarith)]
    ring

/-- 两个同向端点相反的刚性半曲线，拼接后恰为三弧公式。 -/
theorem three_arc_of_two_halves {n : ℝ → E} {v e : E}
    (hl : ∀ s ∈ Icc 0 halfDuration,
      n (halfDuration - s) = Real.cos (radialEnvelope s) • v +
        Real.sin (radialEnvelope s) • e)
    (hr : ∀ s ∈ Icc 0 halfDuration,
      n (halfDuration + s) = Real.cos (radialEnvelope s) • v +
        Real.sin (radialEnvelope s) • (-e)) :
    ∀ t ∈ Icc 0 (2 * halfDuration),
      n t = Real.cos (threeArcPhase t) • v + Real.sin (threeArcPhase t) • e := by
  intro t ht
  by_cases htc : t ≤ halfDuration
  · have hs : halfDuration - t ∈ Icc 0 halfDuration :=
      ⟨sub_nonneg.mpr htc, by linarith [ht.1]⟩
    have h := hl (halfDuration - t) hs
    rw [show halfDuration - (halfDuration - t) = t by ring] at h
    rw [threeArcPhase_eq_left htc]
    exact h
  · have hct : halfDuration ≤ t := (le_of_not_ge htc)
    have hs : t - halfDuration ∈ Icc 0 halfDuration :=
      ⟨sub_nonneg.mpr hct, by linarith [ht.2]⟩
    have h := hr (t - halfDuration) hs
    rw [show halfDuration + (t - halfDuration) = t by ring] at h
    rw [threeArcPhase_eq_right hct, Real.cos_neg, Real.sin_neg]
    simpa only [smul_neg, neg_smul] using h

/-- 单位球面曲线的两半径向包络取等号时，全部轨道由三弧公式唯一确定。 -/
theorem spherical_equality_rigidity {n : ℝ → E}
    (hn : ∀ t ∈ Icc 0 (2 * halfDuration), ‖n t‖ = 1)
    (hend : n (2 * halfDuration) = -n 0)
    (hLip : ∀ s ∈ Icc 0 (2 * halfDuration), ∀ t ∈ Icc 0 (2 * halfDuration),
      angle (n s) (n t) ≤ |s - t|)
    (hleft : ∀ s ∈ Icc 0 halfDuration,
      angle (n halfDuration) (n (halfDuration - s)) = radialEnvelope s)
    (hright : ∀ s ∈ Icc 0 halfDuration,
      angle (n halfDuration) (n (halfDuration + s)) = radialEnvelope s) :
    ⟪n halfDuration, n 0⟫ = 0 ∧
    ∀ t ∈ Icc 0 (2 * halfDuration),
      n t = Real.cos (threeArcPhase t) • n halfDuration +
        Real.sin (threeArcPhase t) • n 0 := by
  have hL : ∀ s ∈ Icc 0 halfDuration,
      halfDuration - s ∈ Icc 0 (2 * halfDuration) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2, halfDuration_pos]
  have hR : ∀ s ∈ Icc 0 halfDuration,
      halfDuration + s ∈ Icc 0 (2 * halfDuration) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2, halfDuration_pos]
  have hv : ‖n halfDuration‖ = 1 :=
    hn halfDuration ⟨halfDuration_pos.le, by linarith [halfDuration_pos]⟩
  have hl := half_curve_rigidity hv (fun s hs => hn _ (hL s hs)) hleft
    (fun s hs t ht => (hLip _ (hL s hs) _ (hL t ht)).trans_eq (by
      rw [show (halfDuration - s) - (halfDuration - t) = -(s - t) by ring,
        abs_neg]))
  have hr := half_curve_rigidity hv (fun s hs => hn _ (hR s hs)) hright
    (fun s hs t ht => (hLip _ (hR s hs) _ (hR t ht)).trans_eq (by
      rw [show (halfDuration + s) - (halfDuration + t) = s - t by ring]))
  have horth := half_endpoint_orthogonal hleft
  simp only [sub_self] at hl horth
  simp only [← two_mul, hend] at hr
  exact ⟨horth, three_arc_of_two_halves hl hr⟩

end RobustPiGate.Rigidity

#print axioms RobustPiGate.Rigidity.continuous_nonneg_pair_integral_zero
#print axioms RobustPiGate.Rigidity.half_direction_eq_endpoint
#print axioms RobustPiGate.Rigidity.half_curve_rigidity_of_integral_eq
#print axioms RobustPiGate.Rigidity.spherical_equality_rigidity
