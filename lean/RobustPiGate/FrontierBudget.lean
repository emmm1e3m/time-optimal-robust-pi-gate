import RobustPiGate.FrontierBasic

noncomputable section
open Set Real Filter
open scoped Topology
namespace RobustPiGate

/-- 完全补偿的临界时长。 -/
def budgetEndpoint : ℝ := 7 * Real.pi / 3

/-- 按静态噪声方差归一化的前导预算。 -/
def frontierBudget (lam L : ℝ) : ℝ := frontierSensitivity L + lam * L

@[simp] theorem residual_at_budgetEndpoint : frontierResidual budgetEndpoint = 0 := by
  unfold frontierResidual budgetEndpoint
  have h : (7 * Real.pi / 3 - Real.pi) / 4 = Real.pi / 3 := by ring
  rw [h, Real.cos_pi_div_three]
  norm_num

@[simp] theorem sensitivity_at_budgetEndpoint : frontierSensitivity budgetEndpoint = 0 := by
  simp [frontierSensitivity]

@[simp] theorem budget_at_endpoint (lam : ℝ) : frontierBudget lam budgetEndpoint = lam * budgetEndpoint := by
  simp [frontierBudget]

lemma budgetEndpoint_gt_pi : Real.pi < budgetEndpoint := by
  unfold budgetEndpoint
  linarith [Real.pi_pos]

lemma budgetEndpoint_sub_pi_gt_one : 1 < budgetEndpoint - Real.pi := by
  unfold budgetEndpoint
  linarith [Real.pi_gt_three]

lemma residual_hasDerivAt (L : ℝ) :
    HasDerivAt frontierResidual (-Real.sin ((L - Real.pi) / 4)) L := by
  unfold frontierResidual
  convert (((hasDerivAt_id L).sub_const Real.pi).div_const 4).cos.const_mul 4 |>.sub_const 2 using 1 <;> try dsimp only [id_eq]
  all_goals ring

lemma sensitivity_hasDerivAt (L : ℝ) :
    HasDerivAt frontierSensitivity
      (-frontierResidual L * Real.sin ((L - Real.pi) / 4) / 3) L := by
  unfold frontierSensitivity
  convert ((residual_hasDerivAt L).pow 2).div_const 6 using 1
  ring

lemma budget_hasDerivAt (lam L : ℝ) :
    HasDerivAt (frontierBudget lam)
      (lam - frontierResidual L * Real.sin ((L - Real.pi) / 4) / 3) L := by
  unfold frontierBudget
  convert (sensitivity_hasDerivAt L).add ((hasDerivAt_id L).const_mul lam) using 1
  · rfl
  · ring

theorem budget_stationary_iff (lam L : ℝ) :
    deriv (frontierBudget lam) L = 0 ↔
      lam = frontierResidual L * Real.sin ((L - Real.pi) / 4) / 3 := by
  rw [(budget_hasDerivAt lam L).deriv, sub_eq_zero]

/-- 紧区间上的每个预算均存在全局最小点。 -/
theorem budget_exists_global_min (lam : ℝ) :
    ∃ L ∈ Icc Real.pi budgetEndpoint, IsMinOn (frontierBudget lam) (Icc Real.pi budgetEndpoint) L := by
  apply isCompact_Icc.exists_isMinOn
  · exact nonempty_Icc.mpr budgetEndpoint_gt_pi.le
  · intro L _
    exact (budget_hasDerivAt lam L).continuousAt.continuousWithinAt

/-- 内部全局最小点满足论文中的驻点方程。 -/
theorem budget_global_min_stationary {lam L : ℝ}
    (hL : L ∈ Ioo Real.pi budgetEndpoint)
    (hm : IsMinOn (frontierBudget lam) (Icc Real.pi budgetEndpoint) L) :
    lam = frontierResidual L * Real.sin ((L - Real.pi) / 4) / 3 := by
  have hz := (hm.isLocalMin (Icc_mem_nhds hL.1 hL.2)).deriv_eq_zero
  rw [(budget_hasDerivAt lam L).deriv] at hz
  linarith

/-- 候选集包括两个端点与全部内部驻点，不需要凸性。 -/
def budgetCandidate (lam L : ℝ) : Prop :=
  L = Real.pi ∨ L = budgetEndpoint ∨
    (L ∈ Ioo Real.pi budgetEndpoint ∧
      lam = frontierResidual L * Real.sin ((L - Real.pi) / 4) / 3)

lemma budget_global_min_is_candidate {lam L : ℝ}
    (hL : L ∈ Icc Real.pi budgetEndpoint)
    (hm : IsMinOn (frontierBudget lam) (Icc Real.pi budgetEndpoint) L) :
    budgetCandidate lam L := by
  by_cases h1 : L = Real.pi
  · exact Or.inl h1
  by_cases h2 : L = budgetEndpoint
  · exact Or.inr (Or.inl h2)
  have hi : L ∈ Ioo Real.pi budgetEndpoint :=
    ⟨lt_of_le_of_ne hL.1 (Ne.symm h1), lt_of_le_of_ne hL.2 h2⟩
  exact Or.inr (Or.inr ⟨hi, budget_global_min_stationary hi hm⟩)

/-- 和全部候选点比较等价于全区间比较。 -/
theorem budget_global_min_iff_candidates {lam L : ℝ}
    (_hL : L ∈ Icc Real.pi budgetEndpoint) :
    IsMinOn (frontierBudget lam) (Icc Real.pi budgetEndpoint) L ↔
    ∀ x ∈ Icc Real.pi budgetEndpoint, budgetCandidate lam x →
      frontierBudget lam L ≤ frontierBudget lam x := by
  constructor
  · intro hm x hx _
    exact hm hx
  · intro hc
    obtain ⟨x, hx, hm⟩ := budget_exists_global_min lam
    intro y hy
    exact le_trans (hc x hx (budget_global_min_is_candidate hx hm)) (hm hy)

/-- 临界端点以后的任意非负静态成本都严格受端点预算支配。 -/
theorem budget_longer_dominated {κ q L : ℝ} (hκ : 0 < κ) (hq : 0 ≤ q)
    (hL : budgetEndpoint < L) : κ * budgetEndpoint < q + κ * L := by
  nlinarith

/-- 余弦的全局 Lipschitz 界给出线性的残差上界。 -/
lemma residual_shortening_abs_le (h : ℝ) :
    |frontierResidual (budgetEndpoint - h)| ≤ |h| := by
  have H := Real.abs_cos_sub_cos_le ((budgetEndpoint - h - Real.pi) / 4) (Real.pi / 3)
  have he : (budgetEndpoint - h - Real.pi) / 4 - Real.pi / 3 = -h / 4 := by
    unfold budgetEndpoint
    ring
  rw [he, abs_div, abs_neg] at H
  norm_num at H
  have hr : frontierResidual (budgetEndpoint - h) =
      4 * (Real.cos ((budgetEndpoint - h - Real.pi) / 4) - 1 / 2) := by
    unfold frontierResidual
    ring
  rw [hr, abs_mul]
  norm_num
  linarith

lemma sensitivity_shortening_le (h : ℝ) :
    frontierSensitivity (budgetEndpoint - h) ≤ h ^ 2 / 6 := by
  have H := sq_le_sq₀ (abs_nonneg (frontierResidual (budgetEndpoint - h))) (abs_nonneg h) |>.mpr
    (residual_shortening_abs_le h)
  simp only [sq_abs] at H
  unfold frontierSensitivity
  linarith

/-- 任意正耗散比都存在一个严格优于完全补偿端点的较短时长。 -/
theorem budget_endpoint_not_min {lam : ℝ} (hlam : 0 < lam) :
    ¬IsMinOn (frontierBudget lam) (Icc Real.pi budgetEndpoint) budgetEndpoint := by
  intro hm
  let h := min 1 (3 * lam)
  have hp : 0 < h := lt_min (by norm_num) (by positivity)
  have h1 : h ≤ 1 := min_le_left _ _
  have hlam3 : h ≤ 3 * lam := min_le_right _ _
  have hmem : budgetEndpoint - h ∈ Icc Real.pi budgetEndpoint := by
    constructor <;> linarith [budgetEndpoint_sub_pi_gt_one]
  have H := hm hmem
  rw [budget_at_endpoint] at H
  change lam * budgetEndpoint ≤ frontierSensitivity (budgetEndpoint - h) + lam * (budgetEndpoint - h) at H
  have hs := sensitivity_shortening_le h
  nlinarith [mul_pos hlam hp, mul_nonneg hp.le (sub_nonneg.mpr hlam3)]

lemma residual_shortening_angle (h : ℝ) :
    frontierResidual (budgetEndpoint - h) = 4 * Real.cos (Real.pi / 3 - h / 4) - 2 := by
  unfold frontierResidual budgetEndpoint
  congr 2
  ring

/-- 残差的一阶展开具有显式二阶误差界。 -/
lemma residual_shortening_taylor {h : ℝ} (hh : |h| ≤ 1) :
    |frontierResidual (budgetEndpoint - h) - Real.sqrt 3 / 2 * h| ≤ h ^ 2 / 4 := by
  let x := h / 4
  have hx : |x| ≤ 1 := by dsimp [x]; rw [abs_div]; norm_num; linarith
  have hc : |Real.cos x - 1| ≤ x ^ 2 / 2 := by
    rw [abs_le]
    constructor <;> nlinarith [Real.cos_le_one x, Real.one_sub_sq_div_two_le_cos (x := x)]
  have hs : |Real.sin x - x| ≤ x ^ 2 / 6 := by
    have H := Real.abs_sub_sin_le x
    rw [abs_sub_comm] at H
    have Hpow : |x| ^ 3 ≤ |x| ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg |x|) (sub_nonneg.mpr hx)]
    rw [sq_abs] at Hpow
    linarith
  have hr0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hr2 : Real.sqrt 3 ≤ 2 := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have he : frontierResidual (budgetEndpoint - h) - Real.sqrt 3 / 2 * h =
      2 * (Real.cos x - 1) + 2 * Real.sqrt 3 * (Real.sin x - x) := by
    rw [residual_shortening_angle, Real.cos_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
    dsimp [x]
    ring
  rw [he]
  calc
    |2 * (Real.cos x - 1) + 2 * Real.sqrt 3 * (Real.sin x - x)|
        ≤ |2 * (Real.cos x - 1)| + |2 * Real.sqrt 3 * (Real.sin x - x)| := abs_add_le _ _
    _ = 2 * |Real.cos x - 1| + 2 * Real.sqrt 3 * |Real.sin x - x| := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hr0]
      norm_num
    _ ≤ 2 * (x ^ 2 / 2) + 2 * Real.sqrt 3 * (x ^ 2 / 6) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hc (by norm_num))
        (mul_le_mul_of_nonneg_left hs (by positivity))
    _ ≤ h ^ 2 / 4 := by
      dsimp [x]
      nlinarith [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hr2)]

/-- 论文二次成本展开的定量版本，足以直接推出 O(h³)。 -/
theorem sensitivity_shortening_taylor {h : ℝ} (hh : |h| ≤ 1) :
    |frontierSensitivity (budgetEndpoint - h) - h ^ 2 / 8| ≤ |h| ^ 3 / 12 := by
  have hr := residual_shortening_taylor hh
  have hb := residual_shortening_abs_le h
  have hroot0 := Real.sqrt_nonneg (3 : ℝ)
  have hroot2 : Real.sqrt 3 ≤ 2 := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have he : frontierSensitivity (budgetEndpoint - h) - h ^ 2 / 8 =
      (frontierResidual (budgetEndpoint - h) - Real.sqrt 3 / 2 * h) *
      (frontierResidual (budgetEndpoint - h) + Real.sqrt 3 / 2 * h) / 6 := by
    unfold frontierSensitivity
    nlinarith [congrArg (fun x : ℝ => x * h ^ 2) hsqrt]
  have hs : |frontierResidual (budgetEndpoint - h) + Real.sqrt 3 / 2 * h| ≤ 2 * |h| := by
    calc
      _ ≤ |frontierResidual (budgetEndpoint - h)| + |Real.sqrt 3 / 2 * h| := abs_add_le _ _
      _ ≤ 2 * |h| := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt 3 / 2)]
        nlinarith [abs_nonneg h]
  rw [he, abs_div, abs_mul]
  norm_num
  have H := mul_le_mul hr hs (abs_nonneg _) (by positivity : 0 ≤ h ^ 2 / 4)
  have Hsq : h ^ 2 = |h| ^ 2 := (sq_abs h).symm
  rw [Hsq] at H
  nlinarith

/-- 全区间上的残差下界，将全局最优点限制到端点附近。 -/
lemma residual_shortening_lower {h : ℝ}
    (hh0 : 0 ≤ h) (hh1 : h ≤ budgetEndpoint - Real.pi) :
    h / Real.pi ≤ frontierResidual (budgetEndpoint - h) := by
  have hp := Real.pi_pos
  have hbound : h ≤ 4 * Real.pi / 3 := by
    unfold budgetEndpoint at hh1
    linarith
  have hs1 : 1 / 2 ≤ Real.sin (Real.pi / 3 - h / 8) := by
    rw [← Real.sin_pi_div_six]
    apply Real.sin_le_sin_of_le_of_le_pi_div_two <;> linarith
  have hs2 : 2 / Real.pi * (h / 8) ≤ Real.sin (h / 8) :=
    Real.mul_le_sin (by positivity) (by linarith)
  have hs20 : 0 ≤ Real.sin (h / 8) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith)
  have he : frontierResidual (budgetEndpoint - h) =
      8 * Real.sin (Real.pi / 3 - h / 8) * Real.sin (h / 8) := by
    rw [residual_shortening_angle]
    have H := Real.cos_sub_cos (Real.pi / 3 - h / 4) (Real.pi / 3)
    rw [Real.cos_pi_div_three] at H
    have h1 : (Real.pi / 3 - h / 4 + Real.pi / 3) / 2 = Real.pi / 3 - h / 8 := by ring
    have h2 : (Real.pi / 3 - h / 4 - Real.pi / 3) / 2 = -(h / 8) := by ring
    rw [h1, h2, Real.sin_neg] at H
    nlinarith
  rw [he]
  have H := mul_le_mul_of_nonneg_right hs1 hs20
  have hs2' : h / Real.pi ≤ 4 * Real.sin (h / 8) := by
    calc
      _ = 4 * (2 / Real.pi * (h / 8)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs2 (by norm_num)
  nlinarith

/-- 全局比较直接给出每个最小点的 O(lam) 缩短上界。 -/
theorem budget_global_shortening_bound {lam L : ℝ} (hlam : 0 ≤ lam)
    (hL : L ∈ Icc Real.pi budgetEndpoint)
    (hm : IsMinOn (frontierBudget lam) (Icc Real.pi budgetEndpoint) L) :
    budgetEndpoint - L ≤ 6 * Real.pi ^ 2 * lam := by
  let h := budgetEndpoint - L
  have hh0 : 0 ≤ h := sub_nonneg.mpr hL.2
  have hh1 : h ≤ budgetEndpoint - Real.pi := by dsimp [h]; linarith [hL.1]
  have hr := residual_shortening_lower hh0 hh1
  have hb := hm (show budgetEndpoint ∈ Icc Real.pi budgetEndpoint from
    ⟨budgetEndpoint_gt_pi.le, le_rfl⟩)
  change frontierBudget lam L ≤ frontierBudget lam budgetEndpoint at hb
  rw [budget_at_endpoint] at hb
  have he : budgetEndpoint - h = L := by dsimp [h]; ring
  have hc : frontierResidual (budgetEndpoint - h) ^ 2 ≤ 6 * lam * h := by
    rw [he]
    unfold frontierBudget frontierSensitivity at hb
    dsimp [h]
    nlinarith
  have hr' : h ≤ Real.pi * frontierResidual (budgetEndpoint - h) := by
    exact (div_le_iff₀ Real.pi_pos).mp hr |>.trans_eq (mul_comm _ _)
  have hs := pow_le_pow_left₀ hh0 hr' 2
  rw [mul_pow] at hs
  have hc' := mul_le_mul_of_nonneg_left hc (sq_nonneg Real.pi)
  by_cases hh : h = 0
  · change h ≤ _
    rw [hh]
    positivity
  · have hhp : 0 < h := lt_of_le_of_ne hh0 (Ne.symm hh)
    change h ≤ _
    by_contra hn
    have H := mul_pos hhp (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith

/-- 驻点方程在端点附近的显式误差估计。 -/
lemma budget_slope_shortening_taylor {h : ℝ} (hh : |h| ≤ 1) :
    |frontierResidual (budgetEndpoint - h) *
      Real.sin ((budgetEndpoint - h - Real.pi) / 4) / 3 - h / 4| ≤ h ^ 2 / 6 := by
  let s := Real.sin ((budgetEndpoint - h - Real.pi) / 4)
  let b := Real.sqrt 3 / 2
  let r := frontierResidual (budgetEndpoint - h)
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by
    dsimp [b]
    nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hb2 : b ^ 2 = 3 / 4 := by
    dsimp [b]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hs1 : |s| ≤ 1 := Real.abs_sin_le_one _
  have hs : |s - b| ≤ |h| / 4 := by
    have H := Real.abs_sin_sub_sin_le ((budgetEndpoint - h - Real.pi) / 4) (Real.pi / 3)
    have he : (budgetEndpoint - h - Real.pi) / 4 - Real.pi / 3 = -h / 4 := by
      unfold budgetEndpoint
      ring
    rw [he, abs_div, abs_neg, Real.sin_pi_div_three] at H
    norm_num at H
    exact H
  have hr : |r - b * h| ≤ h ^ 2 / 4 := residual_shortening_taylor hh
  have he : r * s / 3 - h / 4 = ((r - b * h) * s + b * h * (s - b)) / 3 := by
    nlinarith [congrArg (fun x : ℝ => x * h) hb2]
  change |r * s / 3 - h / 4| ≤ _
  rw [he, abs_div]
  norm_num
  have H1 : |(r - b * h) * s| ≤ h ^ 2 / 4 := by
    rw [abs_mul]
    exact (mul_le_mul hr hs1 (abs_nonneg s) (by positivity)).trans_eq (mul_one _)
  have H2 : |b * h * (s - b)| ≤ h ^ 2 / 4 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hb0]
    have Hbh : b * |h| ≤ |h| := by nlinarith [abs_nonneg h]
    have H := mul_le_mul Hbh hs (abs_nonneg _) (abs_nonneg h)
    nlinarith [sq_abs h]
  have H := abs_add_le ((r - b * h) * s) (b * h * (s - b))
  linarith

/-- 对每个全局最优点成立的二阶误差界，严格强于仅求某个局部根。 -/
theorem budget_global_shortening_asymptotic_bound {lam L : ℝ}
    (hlam : 0 < lam) (hsmall : 6 * Real.pi ^ 2 * lam < 1)
    (hL : L ∈ Icc Real.pi budgetEndpoint)
    (hm : IsMinOn (frontierBudget lam) (Icc Real.pi budgetEndpoint) L) :
    |budgetEndpoint - L - 4 * lam| ≤ 24 * Real.pi ^ 4 * lam ^ 2 := by
  let h := budgetEndpoint - L
  have hh0 : 0 ≤ h := sub_nonneg.mpr hL.2
  have hbound : h ≤ 6 * Real.pi ^ 2 * lam := budget_global_shortening_bound hlam.le hL hm
  have hh1 : |h| ≤ 1 := by rw [abs_of_nonneg hh0]; linarith
  have hne : L ≠ budgetEndpoint := by
    intro he
    subst L
    exact budget_endpoint_not_min hlam hm
  have hi : L ∈ Ioo Real.pi budgetEndpoint := by
    constructor
    · have H := budgetEndpoint_sub_pi_gt_one
      dsimp [h] at hbound
      linarith
    · exact lt_of_le_of_ne hL.2 hne
  have hz := budget_global_min_stationary hi hm
  have H := budget_slope_shortening_taylor hh1
  have he : budgetEndpoint - h = L := by dsimp [h]; ring
  rw [he, ← hz] at H
  have Hab : |h - 4 * lam| = 4 * |lam - h / 4| := by
    have : h - 4 * lam = -4 * (lam - h / 4) := by ring
    rw [this, abs_mul]
    norm_num
  change |h - 4 * lam| ≤ _
  rw [Hab]
  have Hpow := pow_le_pow_left₀ hh0 hbound 2
  nlinarith

/-- 二次静态成本展开的通常 Big-O 表述，实际上双侧成立。 -/
theorem sensitivity_shortening_isBigO :
    (fun h : ℝ => frontierSensitivity (budgetEndpoint - h) - h ^ 2 / 8)
      =O[𝓝 0] (fun h => h ^ 3) := by
  apply Asymptotics.IsBigO.of_bound (1 / 12)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < 1 by norm_num)] with h hh
  have hh' : |h| ≤ 1 := (show |h| < 1 by simpa [mem_ball_zero_iff, Real.norm_eq_abs] using hh).le
  simpa only [Real.norm_eq_abs, abs_pow, div_eq_mul_inv, mul_comm, one_mul] using
    sensitivity_shortening_taylor hh'

/-- 前导预算增量的显式三阶余项界。 -/
theorem weighted_budget_shortening_taylor (v κ : ℝ) {h : ℝ} (hh : |h| ≤ 1) :
    |(v * frontierSensitivity (budgetEndpoint - h) + κ * (budgetEndpoint - h)) -
      κ * budgetEndpoint - (-κ * h + v * h ^ 2 / 8)| ≤ |v| * |h| ^ 3 / 12 := by
  have he : (v * frontierSensitivity (budgetEndpoint - h) + κ * (budgetEndpoint - h)) -
      κ * budgetEndpoint - (-κ * h + v * h ^ 2 / 8) =
      v * (frontierSensitivity (budgetEndpoint - h) - h ^ 2 / 8) := by ring
  rw [he, abs_mul]
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left (sensitivity_shortening_taylor hh) (abs_nonneg v)

/-- 即使静态方差为零，任意正耗散也使完全补偿端点非最优。 -/
theorem weighted_budget_endpoint_not_min {v κ : ℝ} (hv : 0 ≤ v) (hκ : 0 < κ) :
    ¬IsMinOn (fun L => v * frontierSensitivity L + κ * L)
      (Icc Real.pi budgetEndpoint) budgetEndpoint := by
  intro hm
  rcases eq_or_lt_of_le hv with he | hvp
  · have H := hm (show Real.pi ∈ Icc Real.pi budgetEndpoint from
      ⟨le_rfl, budgetEndpoint_gt_pi.le⟩)
    change v * frontierSensitivity budgetEndpoint + κ * budgetEndpoint ≤
      v * frontierSensitivity Real.pi + κ * Real.pi at H
    rw [← he] at H
    nlinarith [mul_pos hκ (sub_pos.mpr budgetEndpoint_gt_pi)]
  · apply budget_endpoint_not_min (div_pos hκ hvp)
    intro L hL
    change frontierBudget (κ / v) budgetEndpoint ≤ frontierBudget (κ / v) L
    apply (mul_le_mul_iff_right₀ hvp).mp
    have heq (x : ℝ) : v * frontierBudget (κ / v) x =
        v * frontierSensitivity x + κ * x := by
      unfold frontierBudget
      field_simp
    rw [heq, heq]
    exact hm hL

/-- 任意选取全局最小点的函数均满足 h=4lam+O(lam²)，无需选择连续性。 -/
theorem budget_global_shortening_isBigO (m : ℝ → ℝ)
    (hm : ∀ lam, 0 < lam → m lam ∈ Icc Real.pi budgetEndpoint ∧
      IsMinOn (frontierBudget lam) (Icc Real.pi budgetEndpoint) (m lam)) :
    (fun lam : ℝ => budgetEndpoint - m lam - 4 * lam)
      =O[𝓝[>] 0] (fun lam => lam ^ 2) := by
  apply Asymptotics.IsBigO.of_bound (24 * Real.pi ^ 4)
  have hc : ContinuousAt (fun lam : ℝ => 6 * Real.pi ^ 2 * lam) 0 := by fun_prop
  have hs : ∀ᶠ lam : ℝ in 𝓝 0, 6 * Real.pi ^ 2 * lam < 1 :=
    hc.eventually_lt continuousAt_const (by norm_num)
  have hp : ∀ᶠ lam : ℝ in 𝓝[>] 0, 0 < lam := self_mem_nhdsWithin
  filter_upwards [hs.filter_mono nhdsWithin_le_nhds, hp] with lam hsmall hlam
  obtain ⟨hmem, hmin⟩ := hm lam hlam
  simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using
    budget_global_shortening_asymptotic_bound hlam hsmall hmem hmin

/-- 图中示例参数下，两端点的预算完全相等。 -/
theorem budget_example_endpoints_equal :
    frontierBudget (1 / (2 * Real.pi)) Real.pi =
      frontierBudget (1 / (2 * Real.pi)) budgetEndpoint := by
  rw [budget_at_endpoint]
  simp only [frontierBudget, frontierSensitivity, frontierResidual, sub_self, zero_div,
    Real.cos_zero]
  unfold budgetEndpoint
  field_simp
  ring

end RobustPiGate

-- 核验关键结论仅使用 Lean 与 Mathlib 的标准公理。
#print axioms RobustPiGate.budget_exists_global_min
#print axioms RobustPiGate.budget_stationary_iff
#print axioms RobustPiGate.budget_global_min_iff_candidates
#print axioms RobustPiGate.budget_longer_dominated
#print axioms RobustPiGate.weighted_budget_endpoint_not_min
#print axioms RobustPiGate.sensitivity_shortening_isBigO
#print axioms RobustPiGate.weighted_budget_shortening_taylor
#print axioms RobustPiGate.budget_global_shortening_asymptotic_bound
#print axioms RobustPiGate.budget_global_shortening_isBigO
#print axioms RobustPiGate.budget_example_endpoints_equal
