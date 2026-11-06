import RobustPiGate.FrontierBasic

set_option autoImplicit false
noncomputable section
open Real
namespace RobustPiGate

/-- 三角恒等式把余弦形式的边界改写成半时长形式。 -/
theorem frontierResidual_two_mul (c : ℝ) :
    frontierResidual (2 * c) = 4 * sin (c / 2 + Real.pi / 4) - 2 := by
  rw [frontierResidual, ← sin_pi_div_two_sub]
  rw [show Real.pi / 2 - (2 * c - Real.pi) / 4 =
    Real.pi - (c / 2 + Real.pi / 4) by ring, sin_pi_sub]

/-- 整个目标时长区间内残差边界非负。 -/
theorem frontierResidual_nonneg {L : ℝ} (hL0 : Real.pi ≤ L)
    (hL1 : L ≤ 2 * criticalHalf) : 0 ≤ frontierResidual L := by
  have hx0 : 0 ≤ (L - Real.pi) / 4 := by linarith
  have hx1 : (L - Real.pi) / 4 ≤ Real.pi / 3 := by
    dsimp [criticalHalf] at hL1
    linarith
  have hh := cos_le_cos_of_nonneg_of_le_pi hx0
    (show Real.pi / 3 ≤ Real.pi by linarith [Real.pi_pos]) hx1
  rw [cos_pi_div_three] at hh
  dsimp [frontierResidual]
  linarith

private theorem frontier_uncapped_factor {c α : ℝ}
    (h₁ : c + α ≤ 2 * Real.pi) (h₂ : c + (Real.pi - α) ≤ 2 * Real.pi) :
    halfBound c α + halfBound c (Real.pi - α) - frontierResidual (2 * c) =
      4 * (1 - cos (α / 2 - Real.pi / 4)) *
        (1 + cos (α / 2 - Real.pi / 4) - sin (c / 2 + Real.pi / 4)) := by
  rw [frontierResidual_two_mul]
  simp only [halfBound, ite_eq_left h₁, ite_eq_left h₂, sin_pi_sub]
  have hs := Real.sin_add_sin ((c + α) / 2) ((c + (Real.pi - α)) / 2)
  rw [show (((c + α) / 2 + (c + (Real.pi - α)) / 2) / 2) =
    c / 2 + Real.pi / 4 by ring,
    show (((c + α) / 2 - (c + (Real.pi - α)) / 2) / 2) =
    α / 2 - Real.pi / 4 by ring] at hs
  have hd := Real.cos_two_mul (α / 2 - Real.pi / 4)
  rw [show 2 * (α / 2 - Real.pi / 4) = α - Real.pi / 2 by ring,
    cos_sub_pi_div_two] at hd
  nlinarith

private theorem frontier_angle_cos_pos {α : ℝ} (hα0 : 0 ≤ α) (hαπ : α ≤ Real.pi) :
    0 < cos (α / 2 - Real.pi / 4) := by
  apply cos_pos_of_mem_Ioo
  constructor <;> linarith [Real.pi_pos]

private theorem frontier_uncapped_ge {c α : ℝ}
    (hα0 : 0 ≤ α) (hαπ : α ≤ Real.pi)
    (h₁ : c + α ≤ 2 * Real.pi) (h₂ : c + (Real.pi - α) ≤ 2 * Real.pi) :
    frontierResidual (2 * c) ≤ halfBound c α + halfBound c (Real.pi - α) := by
  have hf := frontier_uncapped_factor h₁ h₂
  have hx0 := frontier_angle_cos_pos hα0 hαπ
  have hx1 := cos_le_one (α / 2 - Real.pi / 4)
  have hK := sin_le_one (c / 2 + Real.pi / 4)
  have hprod : 0 ≤ 4 * (1 - cos (α / 2 - Real.pi / 4)) *
        (1 + cos (α / 2 - Real.pi / 4) - sin (c / 2 + Real.pi / 4)) := by
    apply mul_nonneg
    · positivity
    · linarith
  linarith

private theorem frontier_uncapped_eq {c α : ℝ}
    (hα0 : 0 ≤ α) (hαπ : α ≤ Real.pi)
    (h₁ : c + α ≤ 2 * Real.pi) (h₂ : c + (Real.pi - α) ≤ 2 * Real.pi)
    (heq : halfBound c α + halfBound c (Real.pi - α) = frontierResidual (2 * c)) :
    α = Real.pi / 2 := by
  have hf := frontier_uncapped_factor h₁ h₂
  have hx0 := frontier_angle_cos_pos hα0 hαπ
  have hx1 := cos_le_one (α / 2 - Real.pi / 4)
  have hK := sin_le_one (c / 2 + Real.pi / 4)
  have hfactor : 0 < 1 + cos (α / 2 - Real.pi / 4) - sin (c / 2 + Real.pi / 4) := by
    linarith
  have hcos : cos (α / 2 - Real.pi / 4) = 1 := by nlinarith
  have hzero := (cos_eq_one_iff_of_lt_of_lt
    (show -(2 * Real.pi) < α / 2 - Real.pi / 4 by linarith [Real.pi_pos])
    (show α / 2 - Real.pi / 4 < 2 * Real.pi by linarith [Real.pi_pos])).mp hcos
  linarith

private def frontierCapSum (c α : ℝ) : ℝ :=
  2 * sin ((c + α) / 2) + Real.pi - c + α - 2 * sin α

private theorem frontier_cap_formula {c α : ℝ} (hc1 : c ≤ criticalHalf)
    (hα0 : 0 ≤ α) (hαd : α ≤ c - Real.pi) :
    halfBound c α + halfBound c (Real.pi - α) = frontierCapSum c α := by
  have h₁ : c + α ≤ 2 * Real.pi := by
    dsimp [criticalHalf] at hc1
    linarith [Real.pi_pos]
  by_cases h₂ : c + (Real.pi - α) ≤ 2 * Real.pi
  · have hseam : (c + (Real.pi - α)) / 2 = Real.pi := by linarith
    simp only [halfBound, ite_eq_left h₁, ite_eq_left h₂, hseam, sin_pi, sin_pi_sub,
      frontierCapSum]
    linarith
  · simp only [halfBound, ite_eq_left h₁, ite_eq_right h₂, sin_pi_sub, frontierCapSum]
    ring

private theorem frontier_cap_antitone {c : ℝ} (hc0 : Real.pi ≤ c)
    (hc1 : c ≤ criticalHalf) :
    AntitoneOn (frontierCapSum c) (Set.Icc 0 (c - Real.pi)) := by
  apply StrictAntiOn.antitoneOn
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · unfold frontierCapSum
    fun_prop
  · intro x hx
    have hxm := interior_subset hx
    have hx0 : 0 ≤ x := hxm.1
    have hx1 : x ≤ c - Real.pi := hxm.2
    have hd : HasDerivAt (frontierCapSum c)
        (cos ((c + x) / 2) + 1 - 2 * cos x) x := by
      unfold frontierCapSum
      convert ((((((hasDerivAt_id x).const_add c).div_const 2).sin.const_mul 2).add_const
        Real.pi).sub_const c).add (hasDerivAt_id x) |>.sub ((hasDerivAt_sin x).const_mul 2)
        using 1
      · funext y
        dsimp
      · dsimp
        ring
    rw [hd.deriv]
    have hm : cos ((c + x) / 2) ≤ 0 := by
      apply cos_nonpos_of_pi_div_two_le_of_le
      · linarith
      · dsimp [criticalHalf] at hc1
        linarith [Real.pi_pos]
    have hcx : 1 / 2 < cos x := by
      rw [← cos_pi_div_three]
      apply cos_lt_cos_of_nonneg_of_le_pi hx0
      · linarith [Real.pi_pos]
      · dsimp [criticalHalf] at hc1
        linarith [Real.pi_pos]
    linarith

private theorem frontier_capped_gt {c α : ℝ} (hc1 : c ≤ criticalHalf)
    (hα0 : 0 ≤ α) (hαd : α ≤ c - Real.pi) :
    frontierResidual (2 * c) < halfBound c α + halfBound c (Real.pi - α) := by
  have hc0 : Real.pi ≤ c := by linarith
  have hd0 : 0 ≤ c - Real.pi := by linarith
  have hdπ : c - Real.pi ≤ Real.pi := by
    dsimp [criticalHalf] at hc1
    linarith [Real.pi_pos]
  have h₁ : c + (c - Real.pi) ≤ 2 * Real.pi := by
    dsimp [criticalHalf] at hc1
    linarith [Real.pi_pos]
  have h₂ : c + (Real.pi - (c - Real.pi)) ≤ 2 * Real.pi := by linarith
  have hge := frontier_uncapped_ge hd0 hdπ h₁ h₂
  have hne : halfBound c (c - Real.pi) + halfBound c (Real.pi - (c - Real.pi)) ≠
      frontierResidual (2 * c) := by
    intro heq
    have hh := frontier_uncapped_eq hd0 hdπ h₁ h₂ heq
    dsimp [criticalHalf] at hc1
    linarith [Real.pi_pos]
  have hgt := lt_of_le_of_ne hge (Ne.symm hne)
  have hmono := frontier_cap_antitone hc0 hc1
    (show α ∈ Set.Icc 0 (c - Real.pi) from ⟨hα0, hαd⟩)
    (show c - Real.pi ∈ Set.Icc 0 (c - Real.pi) from ⟨hd0, le_rfl⟩) hαd
  rw [frontier_cap_formula hc1 hd0 le_rfl] at hgt
  rw [frontier_cap_formula hc1 hα0 hαd]
  exact hgt.trans_le hmono

/-- 对称中点角恰好达到整个时长区间的标量边界。 -/
theorem frontier_sum_midpoint {c : ℝ} (hc1 : c ≤ criticalHalf) :
    halfBound c (Real.pi / 2) + halfBound c (Real.pi - Real.pi / 2) =
      frontierResidual (2 * c) := by
  have h₁ : c + Real.pi / 2 ≤ 2 * Real.pi := by
    dsimp [criticalHalf] at hc1
    linarith [Real.pi_pos]
  have h₂ : c + (Real.pi - Real.pi / 2) ≤ 2 * Real.pi := by linarith
  have hf := frontier_uncapped_factor h₁ h₂
  rw [show Real.pi / 2 / 2 - Real.pi / 4 = 0 by ring, cos_zero] at hf
  linarith

/-- 全部可行中点角的锐标量边界，包含截顶区间。 -/
theorem frontier_sum_ge {c α : ℝ} (_hc0 : Real.pi / 2 ≤ c) (hc1 : c ≤ criticalHalf)
    (hα0 : 0 ≤ α) (hαπ : α ≤ Real.pi) (_hαc : α ≤ c) (_hαc' : Real.pi - α ≤ c) :
    frontierResidual (2 * c) ≤ halfBound c α + halfBound c (Real.pi - α) := by
  by_cases h₁ : c + α ≤ 2 * Real.pi
  · by_cases h₂ : c + (Real.pi - α) ≤ 2 * Real.pi
    · exact frontier_uncapped_ge hα0 hαπ h₁ h₂
    · exact (frontier_capped_gt hc1 hα0 (by linarith)).le
  · have hh := frontier_capped_gt (α := Real.pi - α) hc1 (by linarith) (by linarith)
    simpa only [sub_sub_cancel, add_comm] using hh.le

/-- 标量边界的等号当且仅当两个端点角均为直角。 -/
theorem frontier_sum_eq_iff {c α : ℝ} (_hc0 : Real.pi / 2 ≤ c) (hc1 : c ≤ criticalHalf)
    (hα0 : 0 ≤ α) (hαπ : α ≤ Real.pi) (_hαc : α ≤ c) (_hαc' : Real.pi - α ≤ c) :
    halfBound c α + halfBound c (Real.pi - α) = frontierResidual (2 * c) ↔
      α = Real.pi / 2 := by
  constructor
  · intro heq
    by_cases h₁ : c + α ≤ 2 * Real.pi
    · by_cases h₂ : c + (Real.pi - α) ≤ 2 * Real.pi
      · exact frontier_uncapped_eq hα0 hαπ h₁ h₂ heq
      · have hh := frontier_capped_gt hc1 hα0 (by linarith)
        linarith
    · have hh := frontier_capped_gt (α := Real.pi - α) hc1 (by linarith) (by linarith)
      simp only [sub_sub_cancel] at hh
      linarith
  · intro hα
    subst α
    exact frontier_sum_midpoint hc1

/-- 矩形脉冲端点的无量纲残差为二。 -/
theorem frontierResidual_pi : frontierResidual Real.pi = 2 := by
  norm_num [frontierResidual]

/-- 最短一阶鲁棒门端点的残差为零。 -/
theorem frontierResidual_critical : frontierResidual (2 * criticalHalf) = 0 := by
  unfold frontierResidual criticalHalf
  rw [show (2 * (7 * Real.pi / 6) - Real.pi) / 4 = Real.pi / 3 by ring,
    cos_pi_div_three]
  norm_num

end RobustPiGate

#print axioms RobustPiGate.frontier_sum_ge
#print axioms RobustPiGate.frontier_sum_eq_iff
#print axioms RobustPiGate.frontierResidual_nonneg
