import RobustPiGate.QubitDynamics

open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator
open Real MeasureTheory Set

namespace RobustPiGate.Quantum

noncomputable section

local instance : NormedAlgebra ℚ QubitMatrix :=
  NormedAlgebra.restrictScalars ℚ ℝ QubitMatrix

/-- 恒定横向控制 s 与真实失谐 δ 的原方程生成元。 -/
def detunedGenerator (s δ : ℝ) : QubitMatrix :=
  transverseGenerator s 0 + δ • detuningGenerator

theorem detunedGenerator_skew (s δ : ℝ) :
    star (detunedGenerator s δ) = -detunedGenerator s δ := by
  have hs : star (transverseGenerator s 0) = -transverseGenerator s 0 :=
    transverseGenerator_skew s 0
  have hd : star detuningGenerator = -detuningGenerator := detuningGenerator_skew
  simp [detunedGenerator, hs, hd, smul_neg, add_comm]

/-- 每段的精确矩阵指数传播，适用于任意实失谐。 -/
def detunedSegment (s δ t : ℝ) : QubitMatrix :=
  NormedSpace.exp (t • detunedGenerator s δ)

theorem detunedSegment_zero (s δ : ℝ) : detunedSegment s δ 0 = 1 := by
  simp [detunedSegment]

theorem detunedSegment_unitary (s δ t : ℝ) :
    detunedSegment s δ t ∈ unitary QubitMatrix := by
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff]
  simp [star_smul, detunedGenerator_skew, smul_neg]

theorem hasDerivAt_detunedSegment (s δ t : ℝ) :
    HasDerivAt (detunedSegment s δ)
      (detunedGenerator s δ * detunedSegment s δ t) t :=
  hasDerivAt_exp_smul_const' (detunedGenerator s δ) t

theorem detunedSegment_lipschitz (s δ : ℝ) :
    LipschitzWith ‖detunedGenerator s δ‖₊ (detunedSegment s δ) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t => (hasDerivAt_detunedSegment s δ t).differentiableAt)
  intro t
  rw [(hasDerivAt_detunedSegment s δ t).deriv]
  exact_mod_cast le_of_eq
    (CStarRing.norm_mul_mem_unitary _ (detunedSegment_unitary s δ t))

def shortElapsedFirst (t : ℝ) : ℝ := min t (Real.pi / 3)
def shortElapsedMiddle (t : ℝ) : ℝ :=
  min (max (t - Real.pi / 3) 0) (5 * Real.pi / 3)
def shortElapsedLast (t : ℝ) : ℝ := max (t - 2 * Real.pi) 0

theorem shortElapsedFirst_lipschitz : LipschitzWith 1 shortElapsedFirst :=
  LipschitzWith.id.min_const _

theorem shift_lipschitz (a : ℝ) : LipschitzWith 1 (fun t : ℝ => t - a) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rw [show s - a - (t - a) = s - t by ring]

theorem shortElapsedMiddle_lipschitz : LipschitzWith 1 shortElapsedMiddle := by
  exact ((shift_lipschitz _).max_const _).min_const _

theorem shortElapsedLast_lipschitz : LipschitzWith 1 shortElapsedLast :=
  (shift_lipschitz _).max_const _

/-- 三段按时间顺序相乘的真实带失谐演化族。 -/
def shortDetunedPropagator (δ t : ℝ) : QubitMatrix :=
  detunedSegment 1 δ (shortElapsedLast t) *
  detunedSegment (-1) δ (shortElapsedMiddle t) *
  detunedSegment 1 δ (shortElapsedFirst t)

theorem shortDetunedPropagator_unitary (δ t : ℝ) :
    shortDetunedPropagator δ t ∈ unitary QubitMatrix :=
  (unitary QubitMatrix).mul_mem
    ((unitary QubitMatrix).mul_mem (detunedSegment_unitary _ _ _)
      (detunedSegment_unitary _ _ _)) (detunedSegment_unitary _ _ _)

theorem shortDetunedPropagator_ac (δ a b : ℝ) :
    AbsolutelyContinuousOnInterval (shortDetunedPropagator δ) a b := by
  have h₁ := (detunedSegment_lipschitz 1 δ).comp_absolutelyContinuousOnInterval
    (shortElapsedFirst_lipschitz.lipschitzOnWith.absolutelyContinuousOnInterval
      (a := a) (b := b))
  have h₂ := (detunedSegment_lipschitz (-1) δ).comp_absolutelyContinuousOnInterval
    (shortElapsedMiddle_lipschitz.lipschitzOnWith.absolutelyContinuousOnInterval
      (a := a) (b := b))
  have h₃ := (detunedSegment_lipschitz 1 δ).comp_absolutelyContinuousOnInterval
    (shortElapsedLast_lipschitz.lipschitzOnWith.absolutelyContinuousOnInterval
      (a := a) (b := b))
  exact Dynamics.ac_mul (Dynamics.ac_mul h₃ h₂) h₁

theorem shortDetunedPropagator_first (δ : ℝ) {t : ℝ} (ht : t ≤ Real.pi / 3) :
    shortDetunedPropagator δ t = detunedSegment 1 δ t := by
  have ht2 : t - 2 * Real.pi ≤ 0 := by linarith [Real.pi_pos]
  have hcap : 0 ≤ 5 * Real.pi / 3 := by positivity
  simp [shortDetunedPropagator, shortElapsedLast, shortElapsedMiddle, shortElapsedFirst,
    max_eq_right ht2, max_eq_right (sub_nonpos.mpr ht), min_eq_left ht,
    min_eq_left hcap, detunedSegment_zero]

theorem shortDetunedPropagator_middle (δ : ℝ) {t : ℝ}
    (ht1 : Real.pi / 3 ≤ t) (ht2 : t ≤ 2 * Real.pi) :
    shortDetunedPropagator δ t =
      detunedSegment (-1) δ (t - Real.pi / 3) * detunedSegment 1 δ (Real.pi / 3) := by
  have hcap : t - Real.pi / 3 ≤ 5 * Real.pi / 3 := by linarith
  simp [shortDetunedPropagator, shortElapsedLast, shortElapsedMiddle, shortElapsedFirst,
    max_eq_right (sub_nonpos.mpr ht2), max_eq_left (sub_nonneg.mpr ht1),
    min_eq_right ht1, min_eq_left hcap, detunedSegment_zero]

theorem shortDetunedPropagator_last (δ : ℝ) {t : ℝ} (ht : 2 * Real.pi ≤ t) :
    shortDetunedPropagator δ t =
      detunedSegment 1 δ (t - 2 * Real.pi) *
      detunedSegment (-1) δ (5 * Real.pi / 3) * detunedSegment 1 δ (Real.pi / 3) := by
  have ht1 : Real.pi / 3 ≤ t := by linarith [Real.pi_pos]
  have hcap : 5 * Real.pi / 3 ≤ t - Real.pi / 3 := by linarith
  simp [shortDetunedPropagator, shortElapsedLast, shortElapsedMiddle, shortElapsedFirst,
    max_eq_left (sub_nonneg.mpr ht), max_eq_left (sub_nonneg.mpr ht1),
    min_eq_right ht1, min_eq_right hcap]

theorem shortDetunedPropagator_initial (δ : ℝ) : shortDetunedPropagator δ 0 = 1 := by
  rw [shortDetunedPropagator_first δ (by positivity), detunedSegment_zero]

/-- 除两个开关点外，真实演化族逐点满足原来的带失谐微分方程。 -/
theorem hasDerivAt_shortDetunedPropagator (δ : ℝ) {t : ℝ}
    (h₁ : t ≠ Real.pi / 3) (h₂ : t ≠ 2 * Real.pi) :
    HasDerivAt (shortDetunedPropagator δ)
      (detunedGenerator (shortControl t) δ * shortDetunedPropagator δ t) t := by
  unfold shortControl
  split_ifs with hfirst hmiddle
  · rw [shortDetunedPropagator_first δ hfirst.le]
    apply (hasDerivAt_detunedSegment 1 δ t).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hfirst] with s hs
    exact shortDetunedPropagator_first δ hs.le
  · have hleft : Real.pi / 3 < t :=
      lt_of_le_of_ne (le_of_not_gt hfirst) (Ne.symm h₁)
    have hd := ((hasDerivAt_detunedSegment (-1) δ (t - Real.pi / 3)).scomp t
      ((hasDerivAt_id t).sub_const (Real.pi / 3))).mul_const
      (detunedSegment 1 δ (Real.pi / 3))
    simp only [one_smul, mul_assoc] at hd
    rw [shortDetunedPropagator_middle δ hleft.le hmiddle.le]
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hleft, eventually_lt_nhds hmiddle] with s hs₁ hs₂
    exact shortDetunedPropagator_middle δ hs₁.le hs₂.le
  · have hright : 2 * Real.pi < t :=
      lt_of_le_of_ne (le_of_not_gt hmiddle) (Ne.symm h₂)
    have hd := (((hasDerivAt_detunedSegment 1 δ (t - 2 * Real.pi)).scomp t
      ((hasDerivAt_id t).sub_const (2 * Real.pi))).mul_const
      (detunedSegment (-1) δ (5 * Real.pi / 3))).mul_const
      (detunedSegment 1 δ (Real.pi / 3))
    simp only [one_smul, mul_assoc] at hd
    rw [shortDetunedPropagator_last δ hright.le, mul_assoc]
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hright] with s hs
    simpa only [mul_assoc, Function.comp_apply, id_eq] using
      shortDetunedPropagator_last δ hs.le

theorem shortDetunedPropagator_ae_ode (δ : ℝ) :
    ∀ᵐ t : ℝ, HasDerivAt (shortDetunedPropagator δ)
      ((transverseGenerator (shortControl t) 0 + δ • detuningGenerator) *
        shortDetunedPropagator δ t) t := by
  filter_upwards [volume.ae_ne (Real.pi / 3), volume.ae_ne (2 * Real.pi)] with t h₁ h₂
  exact hasDerivAt_shortDetunedPropagator δ h₁ h₂

theorem detunedGenerator_eq_pauli (s δ : ℝ) :
    detunedGenerator s δ = (-Complex.I / 2) • pauli s 0 δ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [detunedGenerator, transverseGenerator, detuningGenerator, pauli,
      sigmaX, sigmaY, sigmaZ, Complex.real_smul] <;> ring

/-- 明确构造的演化族满足任意失谐下的原量子ODE。 -/
theorem shortDetunedPropagator_isQubitEvolution (T : ℝ) :
    Dynamics.IsQubitEvolution shortControl (fun _ => 0) shortDetunedPropagator T := by
  intro δ
  exact {
    ac := shortDetunedPropagator_ac δ 0 T
    initial := shortDetunedPropagator_initial δ
    equation := (shortDetunedPropagator_ae_ode δ).mono (fun _ h _ => h)
  }

/-- 零失谐时，真实指数演化与既有名义 short-CORPSE 传播子完全相同。 -/
theorem shortDetunedPropagator_nominal (t : ℝ) :
    shortDetunedPropagator 0 t = shortPropagator t := by
  have hnom : Dynamics.IsACSolution
      (fun s => transverseGenerator (shortControl s) 0) shortPropagator t := {
    ac := shortPropagator_ac 0 t
    initial := shortPropagator_initial
    equation := shortPropagator_ae_ode.mono (fun _ h _ => h)
  }
  have hdet := Dynamics.qubit_nominal_solution (shortDetunedPropagator_isQubitEvolution t)
  apply Dynamics.solution_unique hnom hdet
  · exact Filter.Eventually.of_forall (fun s _ => transverseGenerator_skew (shortControl s) 0)
  · exact right_mem_uIcc

theorem shortDetunedPropagator_gate :
    shortDetunedPropagator 0 (7 * Real.pi / 3) = -rx Real.pi := by
  rw [shortDetunedPropagator_nominal, shortPropagator_gate]

theorem shortDetunedPropagator_matrix_integral_zero :
    (∫ t in 0..7 * Real.pi / 3,
      (shortDetunedPropagator 0 t).conjTranspose * sigmaZ * shortDetunedPropagator 0 t) = 0 := by
  simpa only [shortDetunedPropagator_nominal, shortPropagator] using short_matrix_integral_zero

/-- 真正的失谐参数导数为零，而非以不可导时的默认 deriv 值代替。 -/
theorem shortDetunedPropagator_first_order_robust :
    HasDerivAt (fun δ => shortDetunedPropagator δ (7 * Real.pi / 3)) 0 0 := by
  have h := Dynamics.qubit_parameter_hasDerivAt
    (shortDetunedPropagator_isQubitEvolution (7 * Real.pi / 3))
  simpa only [shortDetunedPropagator_matrix_integral_zero, mul_zero, smul_zero] using h

theorem shortControl_measurable : Measurable shortControl := by
  unfold shortControl
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const)

/-- 有界可测控制及其真实失谐演化族，在 7π/3 达到目标门和一阶稳健性。 -/
theorem shortDetunedPropagator_certificate :
    Measurable shortControl ∧
    (∀ t, shortControl t ^ 2 + (0 : ℝ) ^ 2 ≤ 1) ∧
    Dynamics.IsQubitEvolution shortControl (fun _ => 0) shortDetunedPropagator (7 * Real.pi / 3) ∧
    (∀ δ t, shortDetunedPropagator δ t ∈ unitary QubitMatrix) ∧
    shortDetunedPropagator 0 (7 * Real.pi / 3) = -rx Real.pi ∧
    HasDerivAt (fun δ => shortDetunedPropagator δ (7 * Real.pi / 3)) 0 0 :=
  ⟨shortControl_measurable, (fun t => by rw [shortControl_amplitude]; norm_num),
    shortDetunedPropagator_isQubitEvolution _, shortDetunedPropagator_unitary,
    shortDetunedPropagator_gate, shortDetunedPropagator_first_order_robust⟩

/-- 物理时间下的幅度 Ω 控制，以及相应的真实失谐演化。 -/
def scaledShortControl (Ω t : ℝ) : ℝ := Ω * shortControl (Ω * t)
def scaledShortPropagator (Ω δ t : ℝ) : QubitMatrix :=
  shortDetunedPropagator (δ / Ω) (Ω * t)
def scaledShortTime (Ω : ℝ) : ℝ := 7 * Real.pi / (3 * Ω)

theorem dilate_lipschitz (Ω : ℝ) : LipschitzWith ‖Ω‖₊ (fun t : ℝ => Ω * t) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [Real.dist_eq, coe_nnnorm, Real.norm_eq_abs, ← mul_sub, abs_mul]
  exact le_rfl

theorem scaledShortPropagator_ac (Ω δ a b : ℝ) :
    AbsolutelyContinuousOnInterval (scaledShortPropagator Ω δ) a b := by
  have h₁ := (detunedSegment_lipschitz 1 (δ / Ω)).comp_absolutelyContinuousOnInterval
    ((shortElapsedFirst_lipschitz.comp (dilate_lipschitz Ω)).lipschitzOnWith.absolutelyContinuousOnInterval
      (a := a) (b := b))
  have h₂ := (detunedSegment_lipschitz (-1) (δ / Ω)).comp_absolutelyContinuousOnInterval
    ((shortElapsedMiddle_lipschitz.comp (dilate_lipschitz Ω)).lipschitzOnWith.absolutelyContinuousOnInterval
      (a := a) (b := b))
  have h₃ := (detunedSegment_lipschitz 1 (δ / Ω)).comp_absolutelyContinuousOnInterval
    ((shortElapsedLast_lipschitz.comp (dilate_lipschitz Ω)).lipschitzOnWith.absolutelyContinuousOnInterval
      (a := a) (b := b))
  exact Dynamics.ac_mul (Dynamics.ac_mul h₃ h₂) h₁

theorem transverseGenerator_scale (Ω s : ℝ) :
    Ω • transverseGenerator s 0 = transverseGenerator (Ω * s) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transverseGenerator, sigmaX, sigmaY, Complex.real_smul] <;> ring

theorem detunedGenerator_scale {Ω : ℝ} (hΩ : Ω ≠ 0) (δ s : ℝ) :
    Ω • detunedGenerator s (δ / Ω) = detunedGenerator (Ω * s) δ := by
  have hcancel : Ω * (δ / Ω) = δ := by field_simp
  simp only [detunedGenerator, smul_add, smul_smul, transverseGenerator_scale, hcancel]

theorem hasDerivAt_scaledShortPropagator {Ω : ℝ} (hΩ : Ω ≠ 0) (δ : ℝ) {t : ℝ}
    (h₁ : t ≠ (Real.pi / 3) / Ω) (h₂ : t ≠ (2 * Real.pi) / Ω) :
    HasDerivAt (scaledShortPropagator Ω δ)
      ((transverseGenerator (scaledShortControl Ω t) 0 + δ • detuningGenerator) *
        scaledShortPropagator Ω δ t) t := by
  have hs₁ : Ω * t ≠ Real.pi / 3 := by
    intro heq
    apply h₁
    apply (eq_div_iff hΩ).2
    simpa only [mul_comm] using heq
  have hs₂ : Ω * t ≠ 2 * Real.pi := by
    intro heq
    apply h₂
    apply (eq_div_iff hΩ).2
    simpa only [mul_comm] using heq
  have hlin : HasDerivAt (fun s : ℝ => Ω * s) Ω t := by
    simpa only [mul_one, id_eq] using (hasDerivAt_id t).const_mul Ω
  have hd := (hasDerivAt_shortDetunedPropagator (δ / Ω) hs₁ hs₂).scomp t hlin
  rw [← smul_mul_assoc, detunedGenerator_scale hΩ] at hd
  exact hd

theorem scaledShortPropagator_ae_ode {Ω : ℝ} (hΩ : Ω ≠ 0) (δ : ℝ) :
    ∀ᵐ t : ℝ, HasDerivAt (scaledShortPropagator Ω δ)
      ((transverseGenerator (scaledShortControl Ω t) 0 + δ • detuningGenerator) *
        scaledShortPropagator Ω δ t) t := by
  filter_upwards [volume.ae_ne ((Real.pi / 3) / Ω),
    volume.ae_ne ((2 * Real.pi) / Ω)] with t h₁ h₂
  exact hasDerivAt_scaledShortPropagator hΩ δ h₁ h₂

theorem scaledShortPropagator_isQubitEvolution {Ω : ℝ} (hΩ : Ω ≠ 0) (T : ℝ) :
    Dynamics.IsQubitEvolution (scaledShortControl Ω) (fun _ => 0) (scaledShortPropagator Ω) T := by
  intro δ
  exact {
    ac := scaledShortPropagator_ac Ω δ 0 T
    initial := by simp only [scaledShortPropagator, mul_zero, shortDetunedPropagator_initial]
    equation := (scaledShortPropagator_ae_ode hΩ δ).mono (fun _ h _ => h)
  }

theorem scaledShortPropagator_unitary (Ω δ t : ℝ) :
    scaledShortPropagator Ω δ t ∈ unitary QubitMatrix :=
  shortDetunedPropagator_unitary _ _

theorem scaledShortTime_mul {Ω : ℝ} (hΩ : Ω ≠ 0) :
    Ω * scaledShortTime Ω = 7 * Real.pi / 3 := by
  unfold scaledShortTime
  field_simp

theorem scaledShortPropagator_gate {Ω : ℝ} (hΩ : Ω ≠ 0) :
    scaledShortPropagator Ω 0 (scaledShortTime Ω) = -rx Real.pi := by
  simp only [scaledShortPropagator, zero_div, scaledShortTime_mul hΩ,
    shortDetunedPropagator_gate]

theorem scaledShortPropagator_first_order_robust {Ω : ℝ} (hΩ : Ω ≠ 0) :
    HasDerivAt (fun δ => scaledShortPropagator Ω δ (scaledShortTime Ω)) 0 0 := by
  have hd : HasDerivAt (fun δ => shortDetunedPropagator δ (7 * Real.pi / 3)) 0
      ((0 : ℝ) / Ω) := by
    simpa only [zero_div] using shortDetunedPropagator_first_order_robust
  have hp := hd.scomp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).div_const Ω)
  simpa only [scaledShortPropagator, scaledShortTime_mul hΩ, smul_zero,
    Function.comp_def, id_eq] using hp

theorem scaledShortControl_measurable (Ω : ℝ) : Measurable (scaledShortControl Ω) :=
  measurable_const.mul (shortControl_measurable.comp (measurable_const.mul measurable_id))

theorem scaledShortControl_amplitude (Ω t : ℝ) :
    scaledShortControl Ω t ^ 2 + (0 : ℝ) ^ 2 ≤ Ω ^ 2 := by
  simp only [scaledShortControl, mul_pow, shortControl_amplitude, mul_one, zero_pow (by decide : 2 ≠ 0),
    add_zero, le_refl]

/-- 任意正幅度 Ω 下，原控制模型在精确物理时长 7π/(3Ω) 上的达到证书。 -/
theorem scaledShortPropagator_certificate {Ω : ℝ} (hΩ : 0 < Ω) :
    0 < scaledShortTime Ω ∧
    Measurable (scaledShortControl Ω) ∧
    (∀ t, scaledShortControl Ω t ^ 2 + (0 : ℝ) ^ 2 ≤ Ω ^ 2) ∧
    Dynamics.IsQubitEvolution (scaledShortControl Ω) (fun _ => 0)
      (scaledShortPropagator Ω) (scaledShortTime Ω) ∧
    (∀ δ t, scaledShortPropagator Ω δ t ∈ unitary QubitMatrix) ∧
    scaledShortPropagator Ω 0 (scaledShortTime Ω) = -rx Real.pi ∧
    HasDerivAt (fun δ => scaledShortPropagator Ω δ (scaledShortTime Ω)) 0 0 := by
  refine ⟨?_, scaledShortControl_measurable Ω, scaledShortControl_amplitude Ω,
    scaledShortPropagator_isQubitEvolution hΩ.ne' _, scaledShortPropagator_unitary Ω,
    scaledShortPropagator_gate hΩ.ne', scaledShortPropagator_first_order_robust hΩ.ne'⟩
  unfold scaledShortTime
  positivity

end
end RobustPiGate.Quantum

#print axioms RobustPiGate.Quantum.shortDetunedPropagator_isQubitEvolution
#print axioms RobustPiGate.Quantum.shortDetunedPropagator_nominal
#print axioms RobustPiGate.Quantum.shortDetunedPropagator_first_order_robust
#print axioms RobustPiGate.Quantum.shortDetunedPropagator_certificate
#print axioms RobustPiGate.Quantum.scaledShortPropagator_certificate
