import RobustPiGate.OptimalControls

noncomputable section
open MeasureTheory Set Filter
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator Topology Interval NNReal

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace RobustPiGate.Quantum

-- 非零线性时间变换保持零测集；控制的a.e.性质在此真实换元。
theorem ae_comp_mul {P : ℝ → Prop} {r : ℝ} (hr : r ≠ 0)
    (hP : ∀ᵐ t, P t) : ∀ᵐ t, P (r * t) := by
  simpa only [smul_eq_mul] using (Measure.quasiMeasurePreserving_smul volume hr).ae hP

theorem ae_comp_div {P : ℝ → Prop} {r : ℝ} (hr : r ≠ 0)
    (hP : ∀ᵐ t, P t) : ∀ᵐ t, P (t / r) := by
  simpa only [div_eq_mul_inv, mul_comm] using ae_comp_mul (inv_ne_zero hr) hP

theorem transverseGenerator_real_smul (r x y : ℝ) :
    r • transverseGenerator x y = transverseGenerator (r * x) (r * y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transverseGenerator, sigmaX, sigmaY, Complex.real_smul] <;> ring

-- 只为得到名义传播子的Lipschitz性，使用粗的固定算符范数常数即可。
theorem transverseGenerator_norm_le {x y Ω : ℝ} (hΩ : 0 ≤ Ω)
    (hamp : x ^ 2 + y ^ 2 ≤ Ω ^ 2) :
    ‖transverseGenerator x y‖ ≤
      ‖(-Complex.I / 2 : ℂ)‖ * (Ω * (‖sigmaX‖ + ‖sigmaY‖)) := by
  have hx : |x| ≤ Ω := (sq_le_sq₀ (abs_nonneg x) hΩ).mp (by nlinarith [sq_nonneg y, sq_abs x])
  have hy : |y| ≤ Ω := (sq_le_sq₀ (abs_nonneg y) hΩ).mp (by nlinarith [sq_nonneg x, sq_abs y])
  unfold transverseGenerator
  rw [norm_smul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ‖(x : ℂ) • sigmaX‖ + ‖(y : ℂ) • sigmaY‖ := norm_add_le _ _
    _ = |x| * ‖sigmaX‖ + |y| * ‖sigmaY‖ := by simp [norm_smul]
    _ ≤ Ω * ‖sigmaX‖ + Ω * ‖sigmaY‖ := by gcongr
    _ = Ω * (‖sigmaX‖ + ‖sigmaY‖) := by ring

theorem nominal_solution_lipschitz {ux uy : ℝ → ℝ} {U : ℝ → QubitMatrix}
    {T : ℝ} {Ω : ℝ≥0}
    (hsol : Dynamics.IsACSolution (fun t => transverseGenerator (ux t) (uy t)) U T)
    (hamp : ∀ᵐ t, t ∈ uIcc 0 T → (ux t) ^ 2 + (uy t) ^ 2 ≤ (Ω : ℝ) ^ 2) :
    LipschitzOnWith (‖(-Complex.I / 2 : ℂ)‖₊ * (Ω * (‖sigmaX‖₊ + ‖sigmaY‖₊)))
      U (uIcc 0 T) := by
  apply Dynamics.lipschitzOnWith_of_ac_deriv_bound hsol.ac
  filter_upwards [hsol.equation, hamp] with t ht ha htI
  rw [(ht htI).deriv]
  have hunit := hsol.unitary
    (Filter.Eventually.of_forall (fun s _ => transverseGenerator_skew (ux s) (uy s))) htI
  rw [CStarRing.norm_mul_mem_unitary _ hunit]
  exact transverseGenerator_norm_le Ω.coe_nonneg (ha htI)

-- 任意AC解在幅度约束下的名义演化缩放；不需要构造全失谐参数族。
theorem nominal_time_rescale {ux uy : ℝ → ℝ} {U : ℝ → QubitMatrix} {T Ω : ℝ}
    (hΩ : 0 < Ω) (hT : 0 ≤ T)
    (hsol : Dynamics.IsACSolution (fun t => transverseGenerator (ux t) (uy t)) U T)
    (hamp : ∀ᵐ t, t ∈ uIcc 0 T → (ux t) ^ 2 + (uy t) ^ 2 ≤ Ω ^ 2) :
    Dynamics.IsACSolution
      (fun s => transverseGenerator (ux (s / Ω) / Ω) (uy (s / Ω) / Ω))
      (fun s => U (s / Ω)) (Ω * T) := by
  let K : ℝ≥0 := ‖(-Complex.I / 2 : ℂ)‖₊ *
    ((NNReal.mk Ω hΩ.le) * (‖sigmaX‖₊ + ‖sigmaY‖₊))
  have hLip : LipschitzOnWith K U (uIcc 0 T) := nominal_solution_lipschitz (Ω := NNReal.mk Ω hΩ.le) hsol hamp
  have hmem {s : ℝ} (hs : s ∈ uIcc 0 (Ω * T)) : s / Ω ∈ uIcc 0 T := by
    rw [uIcc_of_le hT]
    rw [uIcc_of_le (mul_nonneg hΩ.le hT)] at hs
    exact ⟨div_nonneg hs.1 hΩ.le, (div_le_iff₀ hΩ).mpr (by simpa [mul_comm] using hs.2)⟩
  have hWLip : LipschitzOnWith (K * ‖Ω⁻¹‖₊) (fun s => U (s / Ω)) (uIcc 0 (Ω * T)) := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro s hs t ht
    have h := (lipschitzOnWith_iff_norm_sub_le.mp hLip) (hmem hs) (hmem ht)
    calc
      _ ≤ (K : ℝ) * ‖s / Ω - t / Ω‖ := h
      _ = ((K * ‖Ω⁻¹‖₊ : ℝ≥0) : ℝ) * ‖s - t‖ := by
        simp only [NNReal.coe_mul, coe_nnnorm, norm_inv, Real.norm_eq_abs,
          ← sub_div, abs_div]
        ring
  refine ⟨hWLip.absolutelyContinuousOnInterval, ?_, ?_⟩
  · simpa using hsol.initial
  · filter_upwards [ae_comp_div hΩ.ne' hsol.equation] with s hs hsI
    have hlin : HasDerivAt (fun t : ℝ => t / Ω) (1 / Ω) s :=
      (hasDerivAt_id s).div_const Ω
    have hd := (hs (hmem hsI)).scomp s hlin
    rw [← smul_mul_assoc, transverseGenerator_real_smul] at hd
    simpa only [Function.comp_def, one_div, div_eq_mul_inv, mul_one, mul_comm] using hd

-- 规范噪声曲线的时间缩放把Ω-Lipschitz界变成1-Lipschitz界。
theorem noise_lipschitz_rescale {n : ℝ → Vec3} {T Ω : ℝ}
    (hΩ : 0 < Ω)
    (hLip : LipschitzOnWith (NNReal.mk Ω hΩ.le) n (Icc 0 T)) :
    LipschitzOnWith 1 (fun s => n (s / Ω)) (Icc 0 (Ω * T)) := by
  have hmem {s : ℝ} (hs : s ∈ Icc 0 (Ω * T)) : s / Ω ∈ Icc 0 T :=
    ⟨div_nonneg hs.1 hΩ.le, (div_le_iff₀ hΩ).mpr (by simpa [mul_comm] using hs.2)⟩
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro s hs t ht
  have h := (lipschitzOnWith_iff_norm_sub_le.mp hLip) (hmem hs) (hmem ht)
  have hcancel : Ω * (|s - t| / Ω) = |s - t| := by field_simp
  simpa only [NNReal.coe_mk, NNReal.coe_one, one_mul, Real.norm_eq_abs,
    ← sub_div, abs_div, abs_of_pos hΩ, hcancel] using h

/-- 任意正幅度下，全部达到最短时间的真实稳健π门控制仅有整体正负两个。 -/
theorem optimal_controls_unique_scaled
    {ux uy : ℝ → ℝ} {U : ℝ → ℝ → QubitMatrix} {Ω : ℝ}
    (hΩ : 0 < Ω)
    (hU : Dynamics.IsQubitEvolution ux uy U (7 * Real.pi / (3 * Ω)))
    (hamp : ∀ᵐ t, t ∈ Icc 0 (7 * Real.pi / (3 * Ω)) →
      (ux t) ^ 2 + (uy t) ^ 2 ≤ Ω ^ 2)
    (hgate : U 0 (7 * Real.pi / (3 * Ω)) = rx Real.pi ∨
      U 0 (7 * Real.pi / (3 * Ω)) = -rx Real.pi)
    (hrobust : deriv (fun δ => U δ (7 * Real.pi / (3 * Ω))) 0 = 0) :
    (∀ᵐ t, t ∈ Icc 0 (7 * Real.pi / (3 * Ω)) →
      ux t = Ω * shortControl (Ω * t) ∧ uy t = 0) ∨
    (∀ᵐ t, t ∈ Icc 0 (7 * Real.pi / (3 * Ω)) →
      ux t = -(Ω * shortControl (Ω * t)) ∧ uy t = 0) := by
  let T : ℝ := 7 * Real.pi / (3 * Ω)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hscale : Ω * T = 7 * Real.pi / 3 := by dsimp [T]; field_simp
  have hdiv : (7 * Real.pi / 3) / Ω = T := by dsimp [T]; field_simp
  have hampU : ∀ᵐ t, t ∈ uIcc 0 T → (ux t) ^ 2 + (uy t) ^ 2 ≤ Ω ^ 2 := by
    simpa only [uIcc_of_le hT] using hamp
  have hsol := nominal_time_rescale hΩ hT (Dynamics.qubit_nominal_solution hU) hampU
  rw [hscale] at hsol
  obtain ⟨_, hLip, _, hzero⟩ := actual_noise_curve (Ω := NNReal.mk Ω hΩ.le) hU hampU hgate hrobust
  have hLipI : LipschitzOnWith (NNReal.mk Ω hΩ.le) (fun t => noiseVec (U 0 t)) (Icc 0 T) := by
    change LipschitzOnWith (NNReal.mk Ω hΩ.le) (fun t => noiseVec (U 0 t)) (uIcc 0 T) at hLip
    simpa only [uIcc_of_le hT] using hLip
  have hLipN := noise_lipschitz_rescale hΩ hLipI
  rw [hscale] at hLipN
  have hgateN : U 0 ((7 * Real.pi / 3) / Ω) = rx Real.pi ∨
      U 0 ((7 * Real.pi / 3) / Ω) = -rx Real.pi := by
    simpa only [hdiv] using hgate
  have hzeroN : (∫ s in 0..7 * Real.pi / 3, noiseVec (U 0 (s / Ω))) = 0 := by
    rw [intervalIntegral.integral_comp_div (fun t => noiseVec (U 0 t)) hΩ.ne',
      zero_div, hdiv, hzero, smul_zero]
  have hmem {t : ℝ} (ht : t ∈ Icc 0 T) : Ω * t ∈ Icc 0 (7 * Real.pi / 3) := by
    refine ⟨mul_nonneg hΩ.le ht.1, ?_⟩
    rw [← hscale]
    exact mul_le_mul_of_nonneg_left ht.2 hΩ.le
  rcases optimal_controls_of_critical_noise hsol hLipN hgateN hzeroN with hpos | hneg
  · left
    filter_upwards [ae_comp_mul hΩ.ne' hpos] with t ht htI
    have hh := ht (hmem htI)
    have hx : ux t / Ω = shortControl (Ω * t) := by simpa [hΩ.ne'] using hh.1
    have hy : uy t / Ω = 0 := by simpa [hΩ.ne'] using hh.2
    exact ⟨by simpa only [mul_comm] using (div_eq_iff hΩ.ne').mp hx,
      by simpa only [zero_mul] using (div_eq_iff hΩ.ne').mp hy⟩
  · right
    filter_upwards [ae_comp_mul hΩ.ne' hneg] with t ht htI
    have hh := ht (hmem htI)
    have hx : ux t / Ω = -shortControl (Ω * t) := by simpa [hΩ.ne'] using hh.1
    have hy : uy t / Ω = 0 := by simpa [hΩ.ne'] using hh.2
    exact ⟨by simpa only [neg_mul, mul_neg, mul_comm] using (div_eq_iff hΩ.ne').mp hx,
      by simpa only [zero_mul] using (div_eq_iff hΩ.ne').mp hy⟩

end RobustPiGate.Quantum

#print axioms RobustPiGate.Quantum.optimal_controls_unique_scaled

