import RobustPiGate.Basic

set_option autoImplicit false
noncomputable section
open Real
namespace RobustPiGate

private theorem sin_five_pi_div_six : sin (5 * Real.pi / 6) = 1 / 2 := by
  rw [show 5 * Real.pi / 6 = Real.pi - Real.pi / 6 by ring, sin_pi_sub, sin_pi_div_six]

private theorem critical_middle_formula {α : ℝ}
    (hαlo : Real.pi / 6 ≤ α) (hαhi : α ≤ 5 * Real.pi / 6) :
    halfBound criticalHalf α + halfBound criticalHalf (Real.pi - α) =
      2 * (1 - cos (α / 2 - Real.pi / 4)) * (2 * cos (α / 2 - Real.pi / 4) + 1) := by
  have h₁ : criticalHalf + α ≤ 2 * Real.pi := by dsimp [criticalHalf]; linarith
  have h₂ : criticalHalf + (Real.pi - α) ≤ 2 * Real.pi := by dsimp [criticalHalf]; linarith
  simp only [halfBound, ite_eq_left h₁, ite_eq_left h₂, sin_pi_sub]
  have hs := Real.sin_add_sin ((criticalHalf + α) / 2)
    ((criticalHalf + (Real.pi - α)) / 2)
  rw [show (((criticalHalf + α) / 2 + (criticalHalf + (Real.pi - α)) / 2) / 2) =
    5 * Real.pi / 6 by dsimp [criticalHalf]; ring,
    show (((criticalHalf + α) / 2 - (criticalHalf + (Real.pi - α)) / 2) / 2) =
    α / 2 - Real.pi / 4 by ring, sin_five_pi_div_six] at hs
  have hd := Real.cos_two_mul (α / 2 - Real.pi / 4)
  rw [show 2 * (α / 2 - Real.pi / 4) = α - Real.pi / 2 by ring, cos_sub_pi_div_two] at hd
  nlinarith

-- 饱和区间用统一的严格正粗界，避免额外的微分论证。
private theorem critical_edge_pos {α : ℝ} (hα0 : 0 ≤ α) (hαhi : α < Real.pi / 6) :
    0 < halfBound criticalHalf α + halfBound criticalHalf (Real.pi - α) := by
  have hp := Real.pi_pos
  have h₁ : criticalHalf + α ≤ 2 * Real.pi := by dsimp [criticalHalf]; linarith
  have h₂ : ¬criticalHalf + (Real.pi - α) ≤ 2 * Real.pi := by dsimp [criticalHalf]; linarith
  simp only [halfBound, ite_eq_left h₁, ite_eq_right h₂, sin_pi_sub]
  have hsinα : sin α ≤ 1 / 2 := by
    rw [← sin_pi_div_six]
    exact sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hαhi.le
  have hsin : sqrt 3 / 2 ≤ sin ((criticalHalf + α) / 2) := by
    rw [← sin_pi_div_three, ← sin_pi_sub ((criticalHalf + α) / 2)]
    apply sin_le_sin_of_le_of_le_pi_div_two
    · linarith
    · dsimp [criticalHalf]; linarith
    · dsimp [criticalHalf]; linarith
  have hsqrt : (5 : ℝ) / 3 < sqrt 3 := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have hn := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  have hp4 := Real.pi_lt_four
  dsimp [criticalHalf] at hsin ⊢
  linarith

private theorem critical_sum_half_nonneg {α : ℝ} (hα0 : 0 ≤ α) (hαhi : α ≤ Real.pi / 2) :
    0 ≤ halfBound criticalHalf α + halfBound criticalHalf (Real.pi - α) := by
  by_cases he : α < Real.pi / 6
  · exact (critical_edge_pos hα0 he).le
  · rw [critical_middle_formula (le_of_not_gt he) (by linarith [Real.pi_pos])]
    have hx0 : 0 ≤ cos (α / 2 - Real.pi / 4) :=
      cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos])
    have hx1 := Real.cos_le_one (α / 2 - Real.pi / 4)
    positivity

/-- 临界半时长处的锐标量不等式。 -/
theorem critical_sum_nonneg {α : ℝ} (hα0 : 0 ≤ α) (hαπ : α ≤ Real.pi) :
    0 ≤ halfBound criticalHalf α + halfBound criticalHalf (Real.pi - α) := by
  by_cases hmid : α ≤ Real.pi / 2
  · exact critical_sum_half_nonneg hα0 hmid
  · have hh := critical_sum_half_nonneg (α := Real.pi - α) (by linarith) (by linarith)
    simpa only [sub_sub_cancel, add_comm] using hh

private theorem critical_sum_half_eq {α : ℝ} (hα0 : 0 ≤ α) (hαhi : α ≤ Real.pi / 2)
    (hz : halfBound criticalHalf α + halfBound criticalHalf (Real.pi - α) = 0) :
    α = Real.pi / 2 := by
  by_cases he : α < Real.pi / 6
  · have := critical_edge_pos hα0 he
    linarith
  · rw [critical_middle_formula (le_of_not_gt he) (by linarith [Real.pi_pos])] at hz
    have hx0 : 0 ≤ cos (α / 2 - Real.pi / 4) :=
      cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos])
    have hx1 := Real.cos_le_one (α / 2 - Real.pi / 4)
    have heq : cos (α / 2 - Real.pi / 4) = 1 := by nlinarith
    have hzero := (cos_eq_one_iff_of_lt_of_lt
      (show -(2 * Real.pi) < α / 2 - Real.pi / 4 by linarith [Real.pi_pos])
      (show α / 2 - Real.pi / 4 < 2 * Real.pi by linarith [Real.pi_pos])).mp heq
    linarith

/-- 临界标量不等式仅在两个端点角均为直角时取等号。 -/
theorem critical_sum_eq_zero_iff {α : ℝ} (hα0 : 0 ≤ α) (hαπ : α ≤ Real.pi) :
    halfBound criticalHalf α + halfBound criticalHalf (Real.pi - α) = 0 ↔ α = Real.pi / 2 := by
  constructor
  · intro hz
    by_cases hmid : α ≤ Real.pi / 2
    · exact critical_sum_half_eq hα0 hmid hz
    · have hz' : halfBound criticalHalf (Real.pi - α) +
          halfBound criticalHalf (Real.pi - (Real.pi - α)) = 0 := by
        simpa only [sub_sub_cancel, add_comm] using hz
      have := critical_sum_half_eq (α := Real.pi - α) (by linarith) (by linarith) hz'
      linarith
  · intro hα
    subst α
    rw [critical_middle_formula (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
    rw [show Real.pi / 2 / 2 - Real.pi / 4 = 0 by ring, cos_zero]
    ring

/-- 固定非负端点角后，半段下界在半时长至少为 π 时严格递减。 -/
theorem halfBound_strictAntiOn {β : ℝ} (hβ0 : 0 ≤ β) :
    StrictAntiOn (fun c => halfBound c β) (Set.Ici Real.pi) := by
  intro c₁ hc₁ c₂ _hc₂ hc
  change Real.pi ≤ c₁ at hc₁
  have hp := Real.pi_pos
  by_cases hcrit : c₂ + β ≤ 2 * Real.pi
  · have hcur : c₁ + β ≤ 2 * Real.pi := by linarith
    simp only [halfBound, ite_eq_left hcrit, ite_eq_left hcur]
    have hs : sin ((c₂ + β) / 2) < sin ((c₁ + β) / 2) := by
      rw [← sin_pi_sub ((c₂ + β) / 2), ← sin_pi_sub ((c₁ + β) / 2)]
      apply sin_lt_sin_of_lt_of_le_pi_div_two <;> linarith
    linarith
  · by_cases hcur : c₁ + β ≤ 2 * Real.pi
    · simp only [halfBound, ite_eq_right hcrit, ite_eq_left hcur]
      have hs : 0 ≤ sin ((c₁ + β) / 2) :=
        sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      linarith
    · simp only [halfBound, ite_eq_right hcrit, ite_eq_right hcur]
      linarith

/-- 固定端点角时，临界时长之前的半段下界严格更大。 -/
theorem halfBound_lt_critical {β c : ℝ} (hβ0 : 0 ≤ β) (_hβπ : β ≤ Real.pi)
    (hcπ : Real.pi ≤ c) (hc : c < criticalHalf) :
    halfBound criticalHalf β < halfBound c β := by
  apply halfBound_strictAntiOn hβ0 hcπ _ hc
  change Real.pi ≤ criticalHalf
  dsimp [criticalHalf]
  linarith [Real.pi_pos]

/-- 几何积分给出的非正约束蕴含锐半时长下界。 -/
theorem criticalHalf_le_of_sum_nonpos {α c : ℝ} (hα0 : 0 ≤ α) (hαπ : α ≤ Real.pi)
    (hcπ : Real.pi ≤ c) (hsum : halfBound c α + halfBound c (Real.pi - α) ≤ 0) :
    criticalHalf ≤ c := by
  by_contra hc
  have hlt : c < criticalHalf := lt_of_not_ge hc
  have h₁ := halfBound_lt_critical hα0 hαπ hcπ hlt
  have h₂ := halfBound_lt_critical (β := Real.pi - α) (by linarith) (by linarith) hcπ hlt
  have h₃ := critical_sum_nonneg hα0 hαπ
  linarith

end RobustPiGate

#print axioms RobustPiGate.critical_sum_nonneg
#print axioms RobustPiGate.critical_sum_eq_zero_iff
#print axioms RobustPiGate.halfBound_strictAntiOn
#print axioms RobustPiGate.criticalHalf_le_of_sum_nonpos

