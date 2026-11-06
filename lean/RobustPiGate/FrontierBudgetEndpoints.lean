import RobustPiGate.FrontierBudget

noncomputable section
open Set Real

namespace RobustPiGate

/-- 一个明确充分条件：较大耗散比下，整个区间的预算导数非负。 -/
lemma budget_deriv_nonneg_of_large_ratio {lam L : ℝ}
    (hlam : (2 : ℝ) / 3 ≤ lam) (hL : L ∈ Icc Real.pi budgetEndpoint) :
    0 ≤ deriv (frontierBudget lam) L := by
  rw [(budget_hasDerivAt lam L).deriv]
  have ha0 : 0 ≤ (L - Real.pi) / 4 := by linarith [hL.1]
  have ha1 : (L - Real.pi) / 4 ≤ Real.pi := by
    have ht := hL.2
    unfold budgetEndpoint at ht
    linarith [Real.pi_pos]
  have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi ha0 ha1
  have hsin := Real.sin_le_one ((L - Real.pi) / 4)
  have hg : frontierResidual L ≤ 2 := by
    unfold frontierResidual
    linarith [Real.cos_le_one ((L - Real.pi) / 4)]
  have hprod := mul_le_mul_of_nonneg_right hg hs0
  linarith

/-- lam≥2/3 时预算在完整可行时长区间上单调不减。 -/
theorem budget_monotoneOn_of_large_ratio {lam : ℝ} (hlam : (2 : ℝ) / 3 ≤ lam) :
    MonotoneOn (frontierBudget lam) (Icc Real.pi budgetEndpoint) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc Real.pi budgetEndpoint)
  · intro L _
    exact (budget_hasDerivAt lam L).continuousAt.continuousWithinAt
  · intro L _
    exact (budget_hasDerivAt lam L).differentiableAt.differentiableWithinAt
  · intro L hL
    exact budget_deriv_nonneg_of_large_ratio hlam (interior_subset hL)

/-- 较大耗散比下矩形脉冲全局最优的明确充分条件，无须精确切换阈值。 -/
theorem budget_rectangular_global_min_of_large_ratio {lam : ℝ}
    (hlam : (2 : ℝ) / 3 ≤ lam) :
    IsMinOn (frontierBudget lam) (Icc Real.pi budgetEndpoint) Real.pi := by
  intro L hL
  exact budget_monotoneOn_of_large_ratio hlam
    ⟨le_rfl, budgetEndpoint_gt_pi.le⟩ hL hL.1

end RobustPiGate

#print axioms RobustPiGate.budget_monotoneOn_of_large_ratio
#print axioms RobustPiGate.budget_rectangular_global_min_of_large_ratio
