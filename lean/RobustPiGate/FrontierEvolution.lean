import RobustPiGate.SignSymmetry
import RobustPiGate.RotatedShort
import RobustPiGate.BlochBridge
import RobustPiGate.FrontierBasic

open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator
open Real MeasureTheory Set

namespace RobustPiGate.Quantum
noncomputable section
set_option maxHeartbeats 1200000

/-- 包含零端段的三段累积角。 -/
def frontierPhase (a t : ℝ) : ℝ :=
  t - 2 * max (t - a) 0 + 2 * max (t - (3 * a + Real.pi)) 0

def frontierControl (a t : ℝ) : ℝ :=
  if t < a then 1 else if t < 3 * a + Real.pi then -1 else 1

def frontierPath (a t : ℝ) : Vec3 := unitArc (frontierPhase a t)
def frontierPropagator (a t : ℝ) : QubitMatrix := rx (frontierPhase a t)

theorem continuous_frontierPhase (a : ℝ) : Continuous (frontierPhase a) := by
  unfold frontierPhase
  fun_prop

theorem frontierPhase_first {a t : ℝ} (ha : 0 ≤ a) (ht : t ≤ a) :
    frontierPhase a t = t := by
  have h : t - (3 * a + Real.pi) ≤ 0 := by linarith [Real.pi_pos]
  simp [frontierPhase, max_eq_right (sub_nonpos.mpr ht), max_eq_right h]

theorem frontierPhase_middle {a t : ℝ} (ht₁ : a ≤ t) (ht₂ : t ≤ 3 * a + Real.pi) :
    frontierPhase a t = 2 * a - t := by
  rw [frontierPhase, max_eq_left (sub_nonneg.mpr ht₁), max_eq_right (sub_nonpos.mpr ht₂)]
  ring

theorem frontierPhase_last {a t : ℝ} (ha : 0 ≤ a) (ht : 3 * a + Real.pi ≤ t) :
    frontierPhase a t = t - (4 * a + 2 * Real.pi) := by
  have h : 0 ≤ t - a := by linarith [Real.pi_pos]
  rw [frontierPhase, max_eq_left h, max_eq_left (sub_nonneg.mpr ht)]
  ring

theorem frontierPhase_initial {a : ℝ} (ha : 0 ≤ a) : frontierPhase a 0 = 0 :=
  frontierPhase_first ha ha

theorem frontierPhase_final {a : ℝ} (ha : 0 ≤ a) :
    frontierPhase a (frontierDuration a) = -Real.pi := by
  rw [frontierPhase_last ha (by unfold frontierDuration; linarith)]
  unfold frontierDuration
  ring

theorem frontierPhase_lipschitz {a : ℝ} (ha : 0 ≤ a) : LipschitzWith 1 (frontierPhase a) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  wlog hst : s ≤ t generalizing s t
  · simpa only [abs_sub_comm] using this t s (le_of_not_ge hst)
  rw [abs_of_nonpos (sub_nonpos.mpr hst)]
  simp only [frontierPhase, max_def]
  split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith [Real.pi_pos]

theorem frontierControl_amplitude (a t : ℝ) : frontierControl a t ^ 2 = 1 := by
  unfold frontierControl
  split_ifs <;> norm_num

theorem frontierControl_measurable (a : ℝ) : Measurable (frontierControl a) := by
  unfold frontierControl
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const)

theorem hasDerivAt_frontierPhase {a t : ℝ} (ha : 0 ≤ a)
    (h₁ : t ≠ a) (h₂ : t ≠ 3 * a + Real.pi) :
    HasDerivAt (frontierPhase a) (frontierControl a t) t := by
  unfold frontierControl
  split_ifs with hfirst hmiddle
  · apply (hasDerivAt_id t).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hfirst] with s hs
    exact frontierPhase_first ha hs.le
  · have hleft : a < t := lt_of_le_of_ne (le_of_not_gt hfirst) (Ne.symm h₁)
    have hd : HasDerivAt (fun s : ℝ => 2 * a - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (2 * a)
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hleft, eventually_lt_nhds hmiddle] with s hs₁ hs₂
    exact frontierPhase_middle hs₁.le hs₂.le
  · have hright : 3 * a + Real.pi < t := lt_of_le_of_ne (le_of_not_gt hmiddle) (Ne.symm h₂)
    have hd : HasDerivAt (fun s : ℝ => s - (4 * a + 2 * Real.pi)) 1 t :=
      (hasDerivAt_id t).sub_const (4 * a + 2 * Real.pi)
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hright] with s hs
    exact frontierPhase_last ha hs.le

theorem frontier_integral {a : ℝ} (ha : 0 ≤ a) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ t in 0..frontierDuration a, f (frontierPhase a t)) =
      (∫ t in 0..a, f t) + (∫ t in -(a + Real.pi)..a, f t) +
      (∫ t in -(a + Real.pi)..-Real.pi, f t) := by
  have hcont : Continuous (fun t => f (frontierPhase a t)) := hf.comp (continuous_frontierPhase a)
  have h₁ : (∫ t in 0..a, f (frontierPhase a t)) = ∫ t in 0..a, f t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le ha] at ht
    exact congrArg f (frontierPhase_first ha ht.2)
  have h₂ : (∫ t in a..3 * a + Real.pi, f (frontierPhase a t)) =
      ∫ t in -(a + Real.pi)..a, f t := by
    calc
      _ = ∫ t in a..3 * a + Real.pi, f (2 * a - t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : a ≤ 3 * a + Real.pi)] at ht
        exact congrArg f (frontierPhase_middle ht.1 ht.2)
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_left]
        congr 1 <;> ring
  have h₃ : (∫ t in 3 * a + Real.pi..frontierDuration a, f (frontierPhase a t)) =
      ∫ t in -(a + Real.pi)..-Real.pi, f t := by
    calc
      _ = ∫ t in 3 * a + Real.pi..frontierDuration a, f (t - (4 * a + 2 * Real.pi)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by unfold frontierDuration; linarith : 3 * a + Real.pi ≤ frontierDuration a)] at ht
        exact congrArg f (frontierPhase_last ha ht.1)
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_right]
        unfold frontierDuration
        congr 1 <;> ring
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable 0 (3 * a + Real.pi))
    (hcont.intervalIntegrable (3 * a + Real.pi) (frontierDuration a))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable 0 a) (hcont.intervalIntegrable a (3 * a + Real.pi))]
  rw [h₁, h₂, h₃]

theorem frontier_integral_sin {a : ℝ} (ha : 0 ≤ a) :
    (∫ t in 0..frontierDuration a, Real.sin (frontierPhase a t)) = -(4 * Real.cos a - 2) := by
  rw [frontier_integral ha Real.sin Real.continuous_sin]
  simp only [integral_sin, Real.cos_neg, Real.cos_add_pi, Real.cos_zero, Real.cos_pi]
  ring

theorem frontier_integral_cos {a : ℝ} (ha : 0 ≤ a) :
    (∫ t in 0..frontierDuration a, Real.cos (frontierPhase a t)) = 0 := by
  rw [frontier_integral ha Real.cos Real.continuous_cos]
  simp only [integral_cos, Real.sin_neg, Real.sin_add_pi, Real.sin_zero, Real.sin_pi]
  ring

theorem frontierPath_integral {a : ℝ} (ha : 0 ≤ a) :
    (∫ t in 0..frontierDuration a, frontierPath a t) = -(4 * Real.cos a - 2) • ey := by
  have hs : Continuous (fun t => Real.sin (frontierPhase a t) • ey) :=
    (Real.continuous_sin.comp (continuous_frontierPhase a)).smul continuous_const
  have hc : Continuous (fun t => Real.cos (frontierPhase a t) • ez) :=
    (Real.continuous_cos.comp (continuous_frontierPhase a)).smul continuous_const
  change (∫ t in 0..frontierDuration a, Real.sin (frontierPhase a t) • ey +
    Real.cos (frontierPhase a t) • ez) = _
  rw [intervalIntegral.integral_add (hs.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_smul_const, frontier_integral_sin ha,
    frontier_integral_cos ha, zero_smul, add_zero]

theorem frontier_matrix_integral {a : ℝ} (ha : 0 ≤ a) :
    (∫ t in 0..frontierDuration a,
      (frontierPropagator a t).conjTranspose * sigmaZ * frontierPropagator a t) =
      -(4 * Real.cos a - 2) • sigmaY := by
  have hs : Continuous (fun t => (Real.sin (frontierPhase a t) : ℂ) • sigmaY) :=
    (Complex.continuous_ofReal.comp (Real.continuous_sin.comp (continuous_frontierPhase a))).smul continuous_const
  have hc : Continuous (fun t => (Real.cos (frontierPhase a t) : ℂ) • sigmaZ) :=
    (Complex.continuous_ofReal.comp (Real.continuous_cos.comp (continuous_frontierPhase a))).smul continuous_const
  simp only [frontierPropagator, rx_conjugates_z, pauli_eq, Complex.ofReal_zero, zero_smul, zero_add]
  rw [intervalIntegral.integral_add (hs.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_smul_const, intervalIntegral.integral_ofReal,
    frontier_integral_sin ha, frontier_integral_cos ha, Complex.ofReal_zero, zero_smul, add_zero]
  exact Complex.coe_smul _ _

def rotatedFrontier (a ax ay t : ℝ) : QubitMatrix := axisRotation ax ay (frontierPhase a t)

theorem rotatedFrontier_initial {a : ℝ} (ha : 0 ≤ a) (ax ay : ℝ) :
    rotatedFrontier a ax ay 0 = 1 := by
  rw [rotatedFrontier, frontierPhase_initial ha, axisRotation_zero]

theorem rotatedFrontier_terminal {a : ℝ} (ha : 0 ≤ a) (ax ay : ℝ) :
    rotatedFrontier a ax ay (frontierDuration a) = Complex.I • pauli ax ay 0 := by
  simp [rotatedFrontier, frontierPhase_final ha, axisRotation, neg_div]

theorem rotatedFrontier_ac {a : ℝ} (ha : 0 ≤ a) (ax ay p q : ℝ) :
    AbsolutelyContinuousOnInterval (rotatedFrontier a ax ay) p q := by
  have hp : AbsolutelyContinuousOnInterval (frontierPhase a) p q :=
    (frontierPhase_lipschitz ha).lipschitzOnWith.absolutelyContinuousOnInterval
  have hh : AbsolutelyContinuousOnInterval (fun t => frontierPhase a t / 2) p q := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hp.const_mul (1 / 2)
  have hc := Real.lipschitzWith_cos.comp_absolutelyContinuousOnInterval hh
  have hs := Real.lipschitzWith_sin.comp_absolutelyContinuousOnInterval hh
  have hI : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : QubitMatrix)) p q :=
    (LipschitzWith.const (1 : QubitMatrix)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hP : AbsolutelyContinuousOnInterval (fun _ : ℝ => (-Complex.I) • pauli ax ay 0) p q :=
    (LipschitzWith.const ((-Complex.I) • pauli ax ay 0)).lipschitzOnWith.absolutelyContinuousOnInterval
  exact (hc.smul hI).add (hs.smul hP)

theorem rotatedFrontier_ae_ode {a ax ay : ℝ} (ha : 0 ≤ a) (haxis : ax ^ 2 + ay ^ 2 = 1) :
    ∀ᵐ t : ℝ, HasDerivAt (rotatedFrontier a ax ay)
      (transverseGenerator (ax * frontierControl a t) (ay * frontierControl a t) * rotatedFrontier a ax ay t) t := by
  filter_upwards [volume.ae_ne a, volume.ae_ne (3 * a + Real.pi)] with t h₁ h₂
  have hd := (hasDerivAt_axisRotation haxis (frontierPhase a t)).scomp t (hasDerivAt_frontierPhase ha h₁ h₂)
  have hscale : frontierControl a t • transverseGenerator ax ay =
      transverseGenerator (ax * frontierControl a t) (ay * frontierControl a t) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [transverseGenerator_eq_pauli, pauli, Complex.real_smul] <;> ring
  rw [← smul_mul_assoc, hscale] at hd
  exact hd

theorem rotatedFrontier_solution {a ax ay : ℝ} (ha : 0 ≤ a)
    (haxis : ax ^ 2 + ay ^ 2 = 1) (T : ℝ) :
    Dynamics.IsACSolution
      (fun t => transverseGenerator (ax * frontierControl a t) (ay * frontierControl a t))
      (rotatedFrontier a ax ay) T :=
  ⟨rotatedFrontier_ac ha ax ay 0 T, rotatedFrontier_initial ha ax ay,
    (rotatedFrontier_ae_ode ha haxis).mono (fun _ ht _ => ht)⟩

theorem rotatedFrontier_unitary {a ax ay : ℝ} (ha : 0 ≤ a)
    (haxis : ax ^ 2 + ay ^ 2 = 1) (t : ℝ) : rotatedFrontier a ax ay t ∈ unitary QubitMatrix := by
  apply (rotatedFrontier_solution ha haxis t).unitary
  · exact Filter.Eventually.of_forall fun s _ => transverseGenerator_skew _ _
  · exact right_mem_uIcc

theorem rotatedFrontier_x (a t : ℝ) : rotatedFrontier a 1 0 t = frontierPropagator a t := by
  rw [rotatedFrontier, frontierPropagator, rx_real_decomposition]
  simp [axisRotation, pauli_eq]

theorem frontierPropagator_solution {a : ℝ} (ha : 0 ≤ a) (T : ℝ) :
    Dynamics.IsACSolution (fun t => transverseGenerator (frontierControl a t) 0)
      (frontierPropagator a) T := by
  have heq : rotatedFrontier a 1 0 = frontierPropagator a := funext (rotatedFrontier_x a)
  simpa only [one_mul, zero_mul, heq] using
    rotatedFrontier_solution ha (ax := 1) (ay := 0) (by norm_num) T

theorem frontierPropagator_gate {a : ℝ} (ha : 0 ≤ a) :
    frontierPropagator a (frontierDuration a) = -rx Real.pi := by
  rw [frontierPropagator, frontierPhase_final ha, rx_neg_pi]

def frontierElapsedFirst (a t : ℝ) : ℝ := min t a
def frontierElapsedMiddle (a t : ℝ) : ℝ := min (max (t - a) 0) (2 * a + Real.pi)
def frontierElapsedLast (a t : ℝ) : ℝ := max (t - (3 * a + Real.pi)) 0

theorem frontierElapsedFirst_lipschitz (a : ℝ) : LipschitzWith 1 (frontierElapsedFirst a) :=
  LipschitzWith.id.min_const _
theorem frontierElapsedMiddle_lipschitz (a : ℝ) : LipschitzWith 1 (frontierElapsedMiddle a) :=
  ((shift_lipschitz _).max_const _).min_const _
theorem frontierElapsedLast_lipschitz (a : ℝ) : LipschitzWith 1 (frontierElapsedLast a) :=
  (shift_lipschitz _).max_const _

/-- 按真实时间顺序相乘的全失谐传播子。 -/
def frontierDetunedPropagator (a δ t : ℝ) : QubitMatrix :=
  detunedSegment 1 δ (frontierElapsedLast a t) *
  detunedSegment (-1) δ (frontierElapsedMiddle a t) *
  detunedSegment 1 δ (frontierElapsedFirst a t)

theorem frontierDetunedPropagator_unitary (a δ t : ℝ) :
    frontierDetunedPropagator a δ t ∈ unitary QubitMatrix :=
  (unitary QubitMatrix).mul_mem
    ((unitary QubitMatrix).mul_mem (detunedSegment_unitary _ _ _)
      (detunedSegment_unitary _ _ _)) (detunedSegment_unitary _ _ _)

theorem frontierDetunedPropagator_ac (a δ p q : ℝ) :
    AbsolutelyContinuousOnInterval (frontierDetunedPropagator a δ) p q := by
  have h₁ := (detunedSegment_lipschitz 1 δ).comp_absolutelyContinuousOnInterval
    ((frontierElapsedFirst_lipschitz a).lipschitzOnWith.absolutelyContinuousOnInterval
      (a := p) (b := q))
  have h₂ := (detunedSegment_lipschitz (-1) δ).comp_absolutelyContinuousOnInterval
    ((frontierElapsedMiddle_lipschitz a).lipschitzOnWith.absolutelyContinuousOnInterval
      (a := p) (b := q))
  have h₃ := (detunedSegment_lipschitz 1 δ).comp_absolutelyContinuousOnInterval
    ((frontierElapsedLast_lipschitz a).lipschitzOnWith.absolutelyContinuousOnInterval
      (a := p) (b := q))
  exact Dynamics.ac_mul (Dynamics.ac_mul h₃ h₂) h₁

theorem frontierDetunedPropagator_first {a : ℝ} (ha : 0 ≤ a) (δ : ℝ) {t : ℝ} (ht : t ≤ a) :
    frontierDetunedPropagator a δ t = detunedSegment 1 δ t := by
  have ht2 : t - (3 * a + Real.pi) ≤ 0 := by linarith [Real.pi_pos]
  have hcap : 0 ≤ 2 * a + Real.pi := by positivity
  simp [frontierDetunedPropagator, frontierElapsedLast, frontierElapsedMiddle, frontierElapsedFirst,
    max_eq_right ht2, max_eq_right (sub_nonpos.mpr ht), min_eq_left ht,
    min_eq_left hcap, detunedSegment_zero]

theorem frontierDetunedPropagator_middle {a : ℝ} (δ : ℝ) {t : ℝ}
    (ht1 : a ≤ t) (ht2 : t ≤ 3 * a + Real.pi) :
    frontierDetunedPropagator a δ t =
      detunedSegment (-1) δ (t - a) * detunedSegment 1 δ a := by
  have hcap : t - a ≤ 2 * a + Real.pi := by linarith
  simp [frontierDetunedPropagator, frontierElapsedLast, frontierElapsedMiddle, frontierElapsedFirst,
    max_eq_right (sub_nonpos.mpr ht2), max_eq_left (sub_nonneg.mpr ht1),
    min_eq_right ht1, min_eq_left hcap, detunedSegment_zero]

theorem frontierDetunedPropagator_last {a : ℝ} (ha : 0 ≤ a) (δ : ℝ) {t : ℝ}
    (ht : 3 * a + Real.pi ≤ t) :
    frontierDetunedPropagator a δ t =
      detunedSegment 1 δ (t - (3 * a + Real.pi)) *
      detunedSegment (-1) δ (2 * a + Real.pi) * detunedSegment 1 δ a := by
  have ht1 : a ≤ t := by linarith [Real.pi_pos]
  have hcap : 2 * a + Real.pi ≤ t - a := by linarith
  simp [frontierDetunedPropagator, frontierElapsedLast, frontierElapsedMiddle, frontierElapsedFirst,
    max_eq_left (sub_nonneg.mpr ht), max_eq_left (sub_nonneg.mpr ht1),
    min_eq_right ht1, min_eq_right hcap]

theorem frontierDetunedPropagator_initial {a : ℝ} (ha : 0 ≤ a) (δ : ℝ) :
    frontierDetunedPropagator a δ 0 = 1 := by
  rw [frontierDetunedPropagator_first ha δ ha, detunedSegment_zero]

theorem hasDerivAt_frontierDetunedPropagator {a : ℝ} (ha : 0 ≤ a) (δ : ℝ) {t : ℝ}
    (h₁ : t ≠ a) (h₂ : t ≠ 3 * a + Real.pi) :
    HasDerivAt (frontierDetunedPropagator a δ)
      (detunedGenerator (frontierControl a t) δ * frontierDetunedPropagator a δ t) t := by
  unfold frontierControl
  split_ifs with hfirst hmiddle
  · rw [frontierDetunedPropagator_first ha δ hfirst.le]
    apply (hasDerivAt_detunedSegment 1 δ t).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hfirst] with s hs
    exact frontierDetunedPropagator_first ha δ hs.le
  · have hleft : a < t := lt_of_le_of_ne (le_of_not_gt hfirst) (Ne.symm h₁)
    have hd := ((hasDerivAt_detunedSegment (-1) δ (t - a)).scomp t
      ((hasDerivAt_id t).sub_const a)).mul_const (detunedSegment 1 δ a)
    simp only [one_smul, mul_assoc] at hd
    rw [frontierDetunedPropagator_middle δ hleft.le hmiddle.le]
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hleft, eventually_lt_nhds hmiddle] with s hs₁ hs₂
    exact frontierDetunedPropagator_middle δ hs₁.le hs₂.le
  · have hright : 3 * a + Real.pi < t :=
      lt_of_le_of_ne (le_of_not_gt hmiddle) (Ne.symm h₂)
    have hd := (((hasDerivAt_detunedSegment 1 δ (t - (3 * a + Real.pi))).scomp t
      ((hasDerivAt_id t).sub_const (3 * a + Real.pi))).mul_const
      (detunedSegment (-1) δ (2 * a + Real.pi))).mul_const (detunedSegment 1 δ a)
    simp only [one_smul, mul_assoc] at hd
    rw [frontierDetunedPropagator_last ha δ hright.le, mul_assoc]
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hright] with s hs
    simpa only [mul_assoc, Function.comp_apply, id_eq] using
      frontierDetunedPropagator_last ha δ hs.le

theorem frontierDetunedPropagator_ae_ode {a : ℝ} (ha : 0 ≤ a) (δ : ℝ) :
    ∀ᵐ t : ℝ, HasDerivAt (frontierDetunedPropagator a δ)
      ((transverseGenerator (frontierControl a t) 0 + δ • detuningGenerator) *
        frontierDetunedPropagator a δ t) t := by
  filter_upwards [volume.ae_ne a, volume.ae_ne (3 * a + Real.pi)] with t h₁ h₂
  exact hasDerivAt_frontierDetunedPropagator ha δ h₁ h₂

theorem frontierDetunedPropagator_isQubitEvolution {a : ℝ} (ha : 0 ≤ a) (T : ℝ) :
    Dynamics.IsQubitEvolution (frontierControl a) (fun _ => 0) (frontierDetunedPropagator a) T := by
  intro δ
  exact {
    ac := frontierDetunedPropagator_ac a δ 0 T
    initial := frontierDetunedPropagator_initial ha δ
    equation := (frontierDetunedPropagator_ae_ode ha δ).mono (fun _ h _ => h)
  }

theorem frontierDetunedPropagator_nominal {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    frontierDetunedPropagator a 0 t = frontierPropagator a t := by
  have hnom := frontierPropagator_solution ha t
  have hdet := Dynamics.qubit_nominal_solution (frontierDetunedPropagator_isQubitEvolution ha t)
  apply Dynamics.solution_unique hnom hdet
  · exact Filter.Eventually.of_forall (fun s _ => transverseGenerator_skew (frontierControl a s) 0)
  · exact right_mem_uIcc

theorem frontierDetunedPropagator_gate {a : ℝ} (ha : 0 ≤ a) :
    frontierDetunedPropagator a 0 (frontierDuration a) = -rx Real.pi := by
  rw [frontierDetunedPropagator_nominal ha, frontierPropagator_gate ha]

theorem frontierDetunedPropagator_matrix_integral {a : ℝ} (ha : 0 ≤ a) :
    (∫ t in 0..frontierDuration a,
      (frontierDetunedPropagator a 0 t).conjTranspose * sigmaZ * frontierDetunedPropagator a 0 t) =
      -(4 * Real.cos a - 2) • sigmaY := by
  simpa only [frontierDetunedPropagator_nominal ha] using frontier_matrix_integral ha

theorem frontierPropagator_noiseVec (a t : ℝ) :
    noiseVec (frontierPropagator a t) = frontierPath a t := by
  simp only [noiseVec, noiseMatrix, frontierPropagator, rx_conjugates_z]
  ext i
  fin_cases i <;> simp [blochVec, pauli, frontierPath, unitArc, ey, ez,
    -Complex.ofReal_sin, -Complex.ofReal_cos]

theorem frontierDetunedPropagator_noise_integral {a : ℝ} (ha : 0 ≤ a) :
    (∫ t in 0..frontierDuration a, noiseVec (frontierDetunedPropagator a 0 t)) =
      -(4 * Real.cos a - 2) • ey := by
  simp only [frontierDetunedPropagator_nominal ha, frontierPropagator_noiseVec,
    frontierPath_integral ha]

/-- 幅度 Ω 下的物理控制和原失谐参数族。 -/
def scaledFrontierControl (a Ω t : ℝ) : ℝ := Ω * frontierControl a (Ω * t)
def scaledFrontierPropagator (a Ω δ t : ℝ) : QubitMatrix :=
  frontierDetunedPropagator a (δ / Ω) (Ω * t)
def scaledFrontierTime (a Ω : ℝ) : ℝ := frontierDuration a / Ω

theorem scaledFrontierTime_mul (a : ℝ) {Ω : ℝ} (hΩ : Ω ≠ 0) :
    Ω * scaledFrontierTime a Ω = frontierDuration a := by
  unfold scaledFrontierTime
  field_simp

theorem scaledFrontierPropagator_ac (a Ω δ p q : ℝ) :
    AbsolutelyContinuousOnInterval (scaledFrontierPropagator a Ω δ) p q := by
  have h₁ := (detunedSegment_lipschitz 1 (δ / Ω)).comp_absolutelyContinuousOnInterval
    (((frontierElapsedFirst_lipschitz a).comp (dilate_lipschitz Ω)).lipschitzOnWith.absolutelyContinuousOnInterval
      (a := p) (b := q))
  have h₂ := (detunedSegment_lipschitz (-1) (δ / Ω)).comp_absolutelyContinuousOnInterval
    (((frontierElapsedMiddle_lipschitz a).comp (dilate_lipschitz Ω)).lipschitzOnWith.absolutelyContinuousOnInterval
      (a := p) (b := q))
  have h₃ := (detunedSegment_lipschitz 1 (δ / Ω)).comp_absolutelyContinuousOnInterval
    (((frontierElapsedLast_lipschitz a).comp (dilate_lipschitz Ω)).lipschitzOnWith.absolutelyContinuousOnInterval
      (a := p) (b := q))
  exact Dynamics.ac_mul (Dynamics.ac_mul h₃ h₂) h₁

theorem hasDerivAt_scaledFrontierPropagator {a Ω : ℝ} (ha : 0 ≤ a) (hΩ : Ω ≠ 0)
    (δ : ℝ) {t : ℝ} (h₁ : t ≠ a / Ω) (h₂ : t ≠ (3 * a + Real.pi) / Ω) :
    HasDerivAt (scaledFrontierPropagator a Ω δ)
      ((transverseGenerator (scaledFrontierControl a Ω t) 0 + δ • detuningGenerator) *
        scaledFrontierPropagator a Ω δ t) t := by
  have hs₁ : Ω * t ≠ a := by
    intro heq
    apply h₁
    apply (eq_div_iff hΩ).2
    simpa only [mul_comm] using heq
  have hs₂ : Ω * t ≠ 3 * a + Real.pi := by
    intro heq
    apply h₂
    apply (eq_div_iff hΩ).2
    simpa only [mul_comm] using heq
  have hlin : HasDerivAt (fun s : ℝ => Ω * s) Ω t := by
    simpa only [mul_one, id_eq] using (hasDerivAt_id t).const_mul Ω
  have hd := (hasDerivAt_frontierDetunedPropagator ha (δ / Ω) hs₁ hs₂).scomp t hlin
  rw [← smul_mul_assoc, detunedGenerator_scale hΩ] at hd
  exact hd

theorem scaledFrontierPropagator_ae_ode {a Ω : ℝ} (ha : 0 ≤ a) (hΩ : Ω ≠ 0) (δ : ℝ) :
    ∀ᵐ t : ℝ, HasDerivAt (scaledFrontierPropagator a Ω δ)
      ((transverseGenerator (scaledFrontierControl a Ω t) 0 + δ • detuningGenerator) *
        scaledFrontierPropagator a Ω δ t) t := by
  filter_upwards [volume.ae_ne (a / Ω), volume.ae_ne ((3 * a + Real.pi) / Ω)] with t h₁ h₂
  exact hasDerivAt_scaledFrontierPropagator ha hΩ δ h₁ h₂

theorem scaledFrontierPropagator_isQubitEvolution {a Ω : ℝ} (ha : 0 ≤ a) (hΩ : Ω ≠ 0) (T : ℝ) :
    Dynamics.IsQubitEvolution (scaledFrontierControl a Ω) (fun _ => 0)
      (scaledFrontierPropagator a Ω) T := by
  intro δ
  exact {
    ac := scaledFrontierPropagator_ac a Ω δ 0 T
    initial := by simp only [scaledFrontierPropagator, mul_zero, frontierDetunedPropagator_initial ha]
    equation := (scaledFrontierPropagator_ae_ode ha hΩ δ).mono (fun _ h _ => h)
  }

theorem scaledFrontierPropagator_unitary (a Ω δ t : ℝ) :
    scaledFrontierPropagator a Ω δ t ∈ unitary QubitMatrix :=
  frontierDetunedPropagator_unitary _ _ _

theorem scaledFrontierPropagator_gate {a Ω : ℝ} (ha : 0 ≤ a) (hΩ : Ω ≠ 0) :
    scaledFrontierPropagator a Ω 0 (scaledFrontierTime a Ω) = -rx Real.pi := by
  simp only [scaledFrontierPropagator, zero_div, scaledFrontierTime_mul a hΩ,
    frontierDetunedPropagator_gate ha]

theorem scaledFrontierControl_measurable (a Ω : ℝ) : Measurable (scaledFrontierControl a Ω) :=
  measurable_const.mul ((frontierControl_measurable a).comp (measurable_const.mul measurable_id))

theorem scaledFrontierControl_amplitude (a Ω t : ℝ) :
    scaledFrontierControl a Ω t ^ 2 + (0 : ℝ) ^ 2 ≤ Ω ^ 2 := by
  simp only [scaledFrontierControl, mul_pow, frontierControl_amplitude, mul_one,
    zero_pow (by decide : 2 ≠ 0), add_zero, le_refl]

theorem scaledFrontierPropagator_noise_integral {a Ω : ℝ} (ha : 0 ≤ a) (hΩ : Ω ≠ 0) :
    (∫ t in 0..scaledFrontierTime a Ω, noiseVec (scaledFrontierPropagator a Ω 0 t)) =
      (-(4 * Real.cos a - 2) / Ω) • ey := by
  simp only [scaledFrontierPropagator, zero_div]
  rw [intervalIntegral.integral_comp_mul_left
    (fun t => noiseVec (frontierDetunedPropagator a 0 t)) hΩ,
    mul_zero, scaledFrontierTime_mul a hΩ, frontierDetunedPropagator_noise_integral ha,
    smul_smul]
  congr 1
  ring

theorem frontier_ey_norm : ‖ey‖ = 1 := by
  have h : ‖ey‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [ey, Fin.sum_univ_succ]
  nlinarith [norm_nonneg ey]

theorem frontier_residual_nonneg {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ Real.pi / 3) :
    0 ≤ 4 * Real.cos a - 2 := by
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi ha (by linarith [Real.pi_pos] : Real.pi / 3 ≤ Real.pi) ha'
  rw [Real.cos_pi_div_three] at hc
  linarith

theorem scaledFrontierPropagator_noise_integral_norm {a Ω : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ Real.pi / 3) (hΩ : 0 < Ω) :
    ‖∫ t in 0..scaledFrontierTime a Ω, noiseVec (scaledFrontierPropagator a Ω 0 t)‖ =
      (4 * Real.cos a - 2) / Ω := by
  rw [scaledFrontierPropagator_noise_integral ha hΩ.ne', norm_smul, frontier_ey_norm,
    mul_one, Real.norm_eq_abs, abs_div, abs_neg,
    abs_of_nonneg (frontier_residual_nonneg ha ha'), abs_of_pos hΩ]

/-- 完整实际达到证书：可测有界控制、任意失谐的原ODE、全门及精确噪声积分。 -/
theorem scaledFrontierPropagator_certificate {a Ω : ℝ} (ha : 0 ≤ a) (hΩ : 0 < Ω) :
    0 < scaledFrontierTime a Ω ∧
    Measurable (scaledFrontierControl a Ω) ∧
    (∀ t, scaledFrontierControl a Ω t ^ 2 + (0 : ℝ) ^ 2 ≤ Ω ^ 2) ∧
    Dynamics.IsQubitEvolution (scaledFrontierControl a Ω) (fun _ => 0)
      (scaledFrontierPropagator a Ω) (scaledFrontierTime a Ω) ∧
    (∀ δ t, scaledFrontierPropagator a Ω δ t ∈ unitary QubitMatrix) ∧
    scaledFrontierPropagator a Ω 0 (scaledFrontierTime a Ω) = -rx Real.pi ∧
    (∫ t in 0..scaledFrontierTime a Ω, noiseVec (scaledFrontierPropagator a Ω 0 t)) =
      (-(4 * Real.cos a - 2) / Ω) • ey := by
  refine ⟨?_, scaledFrontierControl_measurable a Ω, scaledFrontierControl_amplitude a Ω,
    scaledFrontierPropagator_isQubitEvolution ha hΩ.ne' _, scaledFrontierPropagator_unitary a Ω,
    scaledFrontierPropagator_gate ha hΩ.ne', scaledFrontierPropagator_noise_integral ha hΩ.ne'⟩
  unfold scaledFrontierTime frontierDuration
  positivity

def negativeScaledFrontierControl (a Ω t : ℝ) : ℝ := -scaledFrontierControl a Ω t
def negativeScaledFrontierPropagator (a Ω δ t : ℝ) : QubitMatrix :=
  zConjugate (scaledFrontierPropagator a Ω δ t)

theorem negativeScaledFrontierControl_measurable (a Ω : ℝ) :
    Measurable (negativeScaledFrontierControl a Ω) := (scaledFrontierControl_measurable a Ω).neg

theorem negativeScaledFrontierControl_amplitude (a Ω t : ℝ) :
    negativeScaledFrontierControl a Ω t ^ 2 + (0 : ℝ) ^ 2 ≤ Ω ^ 2 := by
  simpa only [negativeScaledFrontierControl, neg_sq] using scaledFrontierControl_amplitude a Ω t

theorem negativeScaledFrontierPropagator_isQubitEvolution {a Ω : ℝ}
    (ha : 0 ≤ a) (hΩ : Ω ≠ 0) (T : ℝ) :
    Dynamics.IsQubitEvolution (negativeScaledFrontierControl a Ω) (fun _ => 0)
      (negativeScaledFrontierPropagator a Ω) T := by
  change Dynamics.IsQubitEvolution (fun t => -scaledFrontierControl a Ω t) (fun _ => 0)
    (fun δ t => zConjugate (scaledFrontierPropagator a Ω δ t)) T
  simpa only [neg_zero] using
    z_conjugate_isQubitEvolution (scaledFrontierPropagator_isQubitEvolution ha hΩ T)

theorem negativeScaledFrontierPropagator_unitary (a Ω δ t : ℝ) :
    negativeScaledFrontierPropagator a Ω δ t ∈ unitary QubitMatrix :=
  zConjugate_unitary (scaledFrontierPropagator_unitary a Ω δ t)

theorem negativeScaledFrontierPropagator_gate {a Ω : ℝ} (ha : 0 ≤ a) (hΩ : Ω ≠ 0) :
    negativeScaledFrontierPropagator a Ω 0 (scaledFrontierTime a Ω) = rx Real.pi := by
  rw [negativeScaledFrontierPropagator, scaledFrontierPropagator_gate ha hΩ, zConjugate_neg_rx_pi]

theorem zConjugate_rx (θ : ℝ) : zConjugate (rx θ) = rx (-θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zConjugate, rx, sigmaZ, Matrix.mul_apply, Fin.sum_univ_two, neg_div,
      -Complex.ofReal_cos, -Complex.ofReal_sin]

theorem negativeScaledFrontierPropagator_noiseVec {a Ω : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    noiseVec (negativeScaledFrontierPropagator a Ω 0 t) =
      -Real.sin (frontierPhase a (Ω * t)) • ey + Real.cos (frontierPhase a (Ω * t)) • ez := by
  simp only [negativeScaledFrontierPropagator, scaledFrontierPropagator, zero_div,
    frontierDetunedPropagator_nominal ha, frontierPropagator, zConjugate_rx,
    noiseVec, noiseMatrix, rx_conjugates_z, Real.sin_neg, Real.cos_neg]
  ext i
  fin_cases i <;> simp [blochVec, pauli, ey, ez, -Complex.ofReal_sin, -Complex.ofReal_cos]

theorem negativeScaledFrontierPropagator_noise_integral {a Ω : ℝ} (ha : 0 ≤ a) (hΩ : Ω ≠ 0) :
    (∫ t in 0..scaledFrontierTime a Ω, noiseVec (negativeScaledFrontierPropagator a Ω 0 t)) =
      ((4 * Real.cos a - 2) / Ω) • ey := by
  simp only [negativeScaledFrontierPropagator_noiseVec ha]
  have hs : Continuous (fun t => -Real.sin (frontierPhase a (Ω * t)) • ey) := by
    exact ((Real.continuous_sin.comp ((continuous_frontierPhase a).comp
      (continuous_const.mul continuous_id))).neg).smul continuous_const
  have hc : Continuous (fun t => Real.cos (frontierPhase a (Ω * t)) • ez) := by
    exact (Real.continuous_cos.comp ((continuous_frontierPhase a).comp
      (continuous_const.mul continuous_id))).smul continuous_const
  rw [intervalIntegral.integral_add (hs.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_smul_const, intervalIntegral.integral_neg]
  rw [intervalIntegral.integral_comp_mul_left (fun t => Real.sin (frontierPhase a t)) hΩ,
    intervalIntegral.integral_comp_mul_left (fun t => Real.cos (frontierPhase a t)) hΩ,
    mul_zero, scaledFrontierTime_mul a hΩ, frontier_integral_sin ha, frontier_integral_cos ha]
  simp only [smul_eq_mul, mul_zero, zero_smul, add_zero]
  congr 1
  ring

theorem negativeScaledFrontierPropagator_noise_integral_norm {a Ω : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ Real.pi / 3) (hΩ : 0 < Ω) :
    ‖∫ t in 0..scaledFrontierTime a Ω, noiseVec (negativeScaledFrontierPropagator a Ω 0 t)‖ =
      (4 * Real.cos a - 2) / Ω := by
  rw [negativeScaledFrontierPropagator_noise_integral ha hΩ.ne', norm_smul, frontier_ey_norm,
    mul_one, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (frontier_residual_nonneg ha ha'), abs_of_pos hΩ]

/-- 整体负控制实现另一全门符号，具有相同的噪声积分范数。 -/
theorem negativeScaledFrontierPropagator_certificate {a Ω : ℝ} (ha : 0 ≤ a) (hΩ : 0 < Ω) :
    0 < scaledFrontierTime a Ω ∧
    Measurable (negativeScaledFrontierControl a Ω) ∧
    (∀ t, negativeScaledFrontierControl a Ω t ^ 2 + (0 : ℝ) ^ 2 ≤ Ω ^ 2) ∧
    Dynamics.IsQubitEvolution (negativeScaledFrontierControl a Ω) (fun _ => 0)
      (negativeScaledFrontierPropagator a Ω) (scaledFrontierTime a Ω) ∧
    (∀ δ t, negativeScaledFrontierPropagator a Ω δ t ∈ unitary QubitMatrix) ∧
    negativeScaledFrontierPropagator a Ω 0 (scaledFrontierTime a Ω) = rx Real.pi ∧
    (∫ t in 0..scaledFrontierTime a Ω, noiseVec (negativeScaledFrontierPropagator a Ω 0 t)) =
      ((4 * Real.cos a - 2) / Ω) • ey := by
  exact ⟨(scaledFrontierPropagator_certificate ha hΩ).1,
    negativeScaledFrontierControl_measurable a Ω, negativeScaledFrontierControl_amplitude a Ω,
    negativeScaledFrontierPropagator_isQubitEvolution ha hΩ.ne' _,
    negativeScaledFrontierPropagator_unitary a Ω,
    negativeScaledFrontierPropagator_gate ha hΩ.ne',
    negativeScaledFrontierPropagator_noise_integral ha hΩ.ne'⟩

end
end RobustPiGate.Quantum

#print axioms RobustPiGate.Quantum.frontierDetunedPropagator_isQubitEvolution
#print axioms RobustPiGate.Quantum.frontierDetunedPropagator_nominal
#print axioms RobustPiGate.Quantum.scaledFrontierPropagator_certificate
#print axioms RobustPiGate.Quantum.negativeScaledFrontierPropagator_noise_integral
#print axioms RobustPiGate.Quantum.negativeScaledFrontierPropagator_certificate
