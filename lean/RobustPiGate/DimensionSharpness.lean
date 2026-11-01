import RobustPiGate.Quantum
import RobustPiGate.SharpLength

noncomputable section
open Real Set MeasureTheory
open scoped InnerProductSpace

namespace RobustPiGate.DimensionSharpness
open Quantum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- 同一短 CORPSE 角函数可放入任意正交二维平面。
def planeArc (e f : E) (θ : ℝ) : E := Real.sin θ • e + Real.cos θ • f

def planePath (e f : E) (t : ℝ) : E := planeArc e f (shortPhase t)

theorem norm_plane_combination_sq {e f : E}
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫_ℝ = 0) (a b : ℝ) :
    ‖a • e + b • f‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_add_sq_real]
  simp [norm_smul, he, hf, real_inner_smul_left, real_inner_smul_right, hef]

theorem planePath_unit {e f : E}
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫_ℝ = 0) (t : ℝ) :
    ‖planePath e f t‖ = 1 := by
  have h : ‖planePath e f t‖ ^ 2 = 1 := by
    rw [planePath, planeArc, norm_plane_combination_sq he hf hef]
    exact Real.sin_sq_add_cos_sq _
  nlinarith [norm_nonneg (planePath e f t)]

theorem planePath_antipodal (e f : E) :
    planePath e f (7 * Real.pi / 3) = -planePath e f 0 := by
  simp [planePath, planeArc, shortPhase_initial, shortPhase_final]

theorem planePath_integral_zero (e f : E) :
    (∫ t in 0..7 * Real.pi / 3, planePath e f t) = 0 := by
  have hs : Continuous (fun t => Real.sin (shortPhase t) • e) :=
    (Real.continuous_sin.comp continuous_shortPhase).smul continuous_const
  have hc : Continuous (fun t => Real.cos (shortPhase t) • f) :=
    (Real.continuous_cos.comp continuous_shortPhase).smul continuous_const
  change (∫ t in 0..7 * Real.pi / 3,
    Real.sin (shortPhase t) • e + Real.cos (shortPhase t) • f) = 0
  rw [intervalIntegral.integral_add (hs.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_smul_const, short_integral_sin_zero,
    short_integral_cos_zero, zero_smul, add_zero]

theorem hasDerivAt_planeArc (e f : E) (θ : ℝ) :
    HasDerivAt (planeArc e f) (Real.cos θ • e + (-Real.sin θ) • f) θ := by
  exact ((Real.hasDerivAt_sin θ).smul_const e).add ((Real.hasDerivAt_cos θ).smul_const f)

theorem planeArc_derivative_norm {e f : E}
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫_ℝ = 0) (θ : ℝ) :
    ‖Real.cos θ • e + (-Real.sin θ) • f‖ = 1 := by
  have h : ‖Real.cos θ • e + (-Real.sin θ) • f‖ ^ 2 = 1 := by
    rw [norm_plane_combination_sq he hf hef]
    simpa [add_comm] using Real.sin_sq_add_cos_sq θ
  nlinarith [norm_nonneg (Real.cos θ • e + (-Real.sin θ) • f)]

theorem planeArc_lipschitz {e f : E}
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫_ℝ = 0) :
    LipschitzWith 1 (planeArc e f) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun θ => (hasDerivAt_planeArc e f θ).differentiableAt)
  intro θ
  rw [(hasDerivAt_planeArc e f θ).deriv]
  exact_mod_cast le_of_eq (planeArc_derivative_norm he hf hef θ)

theorem planePath_lipschitz {e f : E}
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫_ℝ = 0) :
    LipschitzWith 1 (planePath e f) := by
  change LipschitzWith 1 (planeArc e f ∘ shortPhase)
  simpa only [mul_one] using (planeArc_lipschitz he hf hef).comp shortPhase_lipschitz

theorem planePath_certificate {e f : E}
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫_ℝ = 0) :
    (∀ t, ‖planePath e f t‖ = 1) ∧
    LipschitzWith 1 (planePath e f) ∧
    planePath e f (7 * Real.pi / 3) = -planePath e f 0 ∧
    (∫ t in 0..7 * Real.pi / 3, planePath e f t) = 0 :=
  ⟨planePath_unit he hf hef, planePath_lipschitz he hf hef,
    planePath_antipodal e f, planePath_integral_zero e f⟩

def durations (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : Set ℝ :=
  {L | 0 < L ∧ ∃ n : ℝ → E, LipschitzOnWith 1 n (Icc 0 L) ∧
    (∀ t ∈ Icc 0 L, ‖n t‖ = 1) ∧ n L = -n 0 ∧ (∫ t in 0..L, n t) = 0}

theorem minimum_of_orthogonal_unit_vectors {e f : E}
    (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫_ℝ = 0) :
    IsLeast (durations E) (7 * Real.pi / 3) := by
  constructor
  · refine ⟨by positivity, planePath e f, (planePath_lipschitz he hf hef).lipschitzOnWith,
      fun t _ => planePath_unit he hf hef t, planePath_antipodal e f,
      planePath_integral_zero e f⟩
  · intro L hL
    rcases hL with ⟨hpos, n, hLip, hunit, hend, hzero⟩
    exact spherical_curve_length_lower_bound hpos hLip.continuousOn hunit
      (sphericalSpeedBound_of_lipschitzOnWith hunit hLip) hend hzero

-- 在每个 d≥2 的欧氏空间中明确选取前两个标准坐标向量。
theorem euclidean_minimum {d : ℕ} (hd : 2 ≤ d) :
    IsLeast (durations (EuclideanSpace ℝ (Fin d))) (7 * Real.pi / 3) := by
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    simp [i, j] at this
  apply minimum_of_orthogonal_unit_vectors
    (e := EuclideanSpace.single i (1 : ℝ)) (f := EuclideanSpace.single j (1 : ℝ))
  · simp [EuclideanSpace.single, PiLp.norm_single]
  · simp [EuclideanSpace.single, PiLp.norm_single]
  · simp [EuclideanSpace.inner_single_left, EuclideanSpace.single, PiLp.single_apply, hij]

theorem euclidean_sInf {d : ℕ} (hd : 2 ≤ d) :
    sInf (durations (EuclideanSpace ℝ (Fin d))) = 7 * Real.pi / 3 :=
  (euclidean_minimum hd).csInf_eq

end RobustPiGate.DimensionSharpness
