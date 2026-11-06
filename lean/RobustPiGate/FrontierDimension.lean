import RobustPiGate.DimensionSharpness
import RobustPiGate.FrontierBounds
import RobustPiGate.FrontierEvolution

noncomputable section
open Real Set MeasureTheory
open scoped InnerProductSpace

namespace RobustPiGate.FrontierDimension
open Quantum DimensionSharpness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- 参数化三段相位嵌入任意正交二维平面。 -/
def planePath (e f : E) (a t : ℝ) : E := planeArc e f (frontierPhase a t)

theorem planePath_unit {e f : E}
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫_ℝ = 0) (a t : ℝ) :
    ‖planePath e f a t‖ = 1 := by
  have h : ‖planePath e f a t‖ ^ 2 = 1 := by
    rw [planePath, planeArc, norm_plane_combination_sq he hf hef]
    exact Real.sin_sq_add_cos_sq _
  nlinarith [norm_nonneg (planePath e f a t)]

theorem planePath_lipschitz {e f : E} {a : ℝ}
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫_ℝ = 0) (ha : 0 ≤ a) :
    LipschitzWith 1 (planePath e f a) := by
  change LipschitzWith 1 (planeArc e f ∘ frontierPhase a)
  simpa only [mul_one] using (planeArc_lipschitz he hf hef).comp (frontierPhase_lipschitz ha)

theorem planePath_antipodal (e f : E) {a : ℝ} (ha : 0 ≤ a) :
    planePath e f a (frontierDuration a) = -planePath e f a 0 := by
  simp [planePath, planeArc, frontierPhase_initial ha, frontierPhase_final ha]

theorem planePath_integral (e f : E) {a : ℝ} (ha : 0 ≤ a) :
    (∫ t in 0..frontierDuration a, planePath e f a t) = -(4 * cos a - 2) • e := by
  have hs : Continuous (fun t => sin (frontierPhase a t) • e) :=
    (continuous_sin.comp (continuous_frontierPhase a)).smul continuous_const
  have hc : Continuous (fun t => cos (frontierPhase a t) • f) :=
    (continuous_cos.comp (continuous_frontierPhase a)).smul continuous_const
  change (∫ t in 0..frontierDuration a,
    sin (frontierPhase a t) • e + cos (frontierPhase a t) • f) = _
  rw [intervalIntegral.integral_add (hs.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_smul_const, frontier_integral_sin ha,
    frontier_integral_cos ha, zero_smul, add_zero]

/-- 与论文相同的 AC/a.e. 速度前提下，固定长度的实际残差集合。 -/
def residuals (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : ℝ) : Set ℝ :=
  {r | ∃ n : ℝ → E, AbsolutelyContinuousOnInterval n 0 L ∧
    (∀ᵐ t, t ∈ Icc 0 L → ‖deriv n t‖ ≤ 1) ∧
    (∀ t ∈ Icc 0 L, ‖n t‖ = 1) ∧ n L = -n 0 ∧ r = ‖∫ t in 0..L, n t‖}

theorem minimum_of_orthogonal_unit_vectors [FiniteDimensional ℝ E]
    {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫_ℝ = 0)
    {L : ℝ} (hL0 : Real.pi ≤ L) (hL1 : L ≤ 7 * Real.pi / 3) :
    IsLeast (residuals E L) (frontierResidual L) := by
  let a := (L - Real.pi) / 4
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hduration : frontierDuration a = L := by dsimp [frontierDuration, a]; ring
  have hLip := planePath_lipschitz he hf hef ha
  have hnonneg := frontierResidual_nonneg hL0 (by dsimp [criticalHalf]; linarith)
  constructor
  · refine ⟨planePath e f a, hLip.lipschitzOnWith.absolutelyContinuousOnInterval, ?_,
      fun t _ => planePath_unit he hf hef a t, ?_, ?_⟩
    · exact Filter.Eventually.of_forall fun t _ => norm_deriv_le_of_lipschitz hLip
    · simpa only [hduration] using planePath_antipodal e f ha
    · have hint := planePath_integral e f ha
      rw [hduration] at hint
      rw [hint, norm_smul, he, mul_one, Real.norm_eq_abs, abs_neg]
      exact (abs_of_nonneg hnonneg).symm
  · intro r hr
    obtain ⟨n, hac, hderiv, hunit, hend, rfl⟩ := hr
    exact ac_spherical_curve_frontier_lower_bound hL0 hL1 hac hunit hderiv hend

/-- 每个 d≥2 与区间中的每个 L 都有实际达到者，且残差最小值恰为 g(L)。 -/
theorem euclidean_minimum {d : ℕ} (hd : 2 ≤ d) {L : ℝ}
    (hL0 : Real.pi ≤ L) (hL1 : L ≤ 7 * Real.pi / 3) :
    IsLeast (residuals (EuclideanSpace ℝ (Fin d)) L) (frontierResidual L) := by
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    simp [i, j] at this
  apply minimum_of_orthogonal_unit_vectors
    (e := EuclideanSpace.single i (1 : ℝ)) (f := EuclideanSpace.single j (1 : ℝ))
    (L := L) _ _ _ hL0 hL1
  · simp [EuclideanSpace.single, PiLp.norm_single]
  · simp [EuclideanSpace.single, PiLp.norm_single]
  · simp [EuclideanSpace.inner_single_left, EuclideanSpace.single, PiLp.single_apply, hij]

end RobustPiGate.FrontierDimension

#print axioms RobustPiGate.FrontierDimension.euclidean_minimum
