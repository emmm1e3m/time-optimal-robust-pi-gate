import Mathlib

open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator
open Real MeasureTheory

namespace RobustPiGate.Quantum

noncomputable section

abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ

def sigmaX : QubitMatrix := !![0, 1; 1, 0]
def sigmaY : QubitMatrix := !![0, -Complex.I; Complex.I, 0]
def sigmaZ : QubitMatrix := !![1, 0; 0, -1]

def pauli (x y z : ℝ) : QubitMatrix :=
  !![(z : ℂ), (x : ℂ) - Complex.I * y;
     (x : ℂ) + Complex.I * y, -(z : ℂ)]

def rx (θ : ℝ) : QubitMatrix :=
  !![(Real.cos (θ / 2) : ℂ), -Complex.I * Real.sin (θ / 2);
     -Complex.I * Real.sin (θ / 2), (Real.cos (θ / 2) : ℂ)]

theorem pauli_eq (x y z : ℝ) :
    pauli x y z = (x : ℂ) • sigmaX + (y : ℂ) • sigmaY + (z : ℂ) • sigmaZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli, sigmaX, sigmaY, sigmaZ] <;> ring

theorem pauli_sq (x y z : ℝ) :
    pauli x y z * pauli x y z = ((x * x + y * y + z * z : ℝ) : ℂ) • (1 : QubitMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq] <;>
    push_cast <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem pauli_injective {x y z x' y' z' : ℝ}
    (h : pauli x y z = pauli x' y' z') : x = x' ∧ y = y' ∧ z = z' := by
  have hz := congrArg (fun M : QubitMatrix => (M 0 0).re) h
  have hx := congrArg (fun M : QubitMatrix => (M 0 1).re) h
  have hy := congrArg (fun M : QubitMatrix => (M 0 1).im) h
  simp [pauli] at hz hx hy
  exact ⟨hx, hy, hz⟩

theorem rx_zero : rx 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rx]

theorem rx_add (a b : ℝ) : rx (a + b) = rx a * rx b := by
  have hab : (a + b) / 2 = a / 2 + b / 2 := by ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rx, Matrix.mul_apply, Fin.sum_univ_two, hab, Real.cos_add, Real.sin_add] <;>
    push_cast <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem rx_conjTranspose (θ : ℝ) : (rx θ).conjTranspose = rx (-θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rx, Matrix.conjTranspose_apply, neg_div, -Complex.ofReal_cos, -Complex.ofReal_sin]

theorem rx_unitary (θ : ℝ) : (rx θ).conjTranspose * rx θ = 1 := by
  rw [rx_conjTranspose, ← rx_add, neg_add_cancel, rx_zero]

theorem rx_conjugates_z (θ : ℝ) :
    (rx θ).conjTranspose * sigmaZ * rx θ = pauli 0 (Real.sin θ) (Real.cos θ) := by
  have hsin : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    convert Real.sin_two_mul (θ / 2) using 1 <;> congr 1 <;> ring
  have hcos : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
    convert Real.cos_two_mul' (θ / 2) using 1 <;> congr 1 <;> ring
  rw [rx_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rx, sigmaZ, pauli, Matrix.mul_apply, Fin.sum_univ_two, neg_div,
      hsin, hcos, -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
    push_cast <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem rx_pi_antipode : (rx Real.pi).conjTranspose * sigmaZ * rx Real.pi = -sigmaZ := by
  rw [rx_conjugates_z]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli, sigmaZ]

theorem rx_neg_pi : rx (-Real.pi) = -rx Real.pi := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rx, neg_div, -Complex.ofReal_cos, -Complex.ofReal_sin]

-- 分段累积角用两个连续折线函数表示，避免开关点的任意约定。
def shortPhase (t : ℝ) : ℝ :=
  t - 2 * max (t - Real.pi / 3) 0 + 2 * max (t - 2 * Real.pi) 0

def shortNoise (t : ℝ) : Fin 3 → ℝ :=
  ![0, Real.sin (shortPhase t), Real.cos (shortPhase t)]

theorem continuous_shortPhase : Continuous shortPhase := by
  unfold shortPhase
  fun_prop

theorem phase_first {t : ℝ} (h : t ≤ Real.pi / 3) : shortPhase t = t := by
  have h' : t - 2 * Real.pi ≤ 0 := by linarith [Real.pi_pos]
  simp [shortPhase, max_eq_right (sub_nonpos.mpr h), max_eq_right h']

theorem phase_middle {t : ℝ} (h₁ : Real.pi / 3 ≤ t) (h₂ : t ≤ 2 * Real.pi) :
    shortPhase t = 2 * Real.pi / 3 - t := by
  rw [shortPhase, max_eq_left (sub_nonneg.mpr h₁), max_eq_right (sub_nonpos.mpr h₂)]
  ring

theorem phase_last {t : ℝ} (h : 2 * Real.pi ≤ t) :
    shortPhase t = t - 10 * Real.pi / 3 := by
  have h' : 0 ≤ t - Real.pi / 3 := by linarith [Real.pi_pos]
  rw [shortPhase, max_eq_left h', max_eq_left (sub_nonneg.mpr h)]
  ring

theorem shortPhase_initial : shortPhase 0 = 0 := phase_first (by positivity)

theorem shortPhase_final : shortPhase (7 * Real.pi / 3) = -Real.pi := by
  rw [phase_last (by linarith [Real.pi_pos])]
  ring

theorem short_gate : rx (shortPhase (7 * Real.pi / 3)) = -rx Real.pi := by
  rw [shortPhase_final, rx_neg_pi]

theorem short_noise_unit (t : ℝ) :
    ∑ i : Fin 3, shortNoise t i ^ 2 = 1 := by
  simpa [shortNoise, Fin.sum_univ_succ] using Real.sin_sq_add_cos_sq (shortPhase t)

theorem short_noise_initial : shortNoise 0 = ![0, 0, 1] := by
  simp [shortNoise, shortPhase_initial]

theorem short_noise_final : shortNoise (7 * Real.pi / 3) = ![0, 0, -1] := by
  simp [shortNoise, shortPhase_final]

theorem short_integral (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ t in 0..7 * Real.pi / 3, f (shortPhase t)) =
      (∫ t in 0..Real.pi / 3, f t) +
      (∫ t in -(4 * Real.pi / 3)..Real.pi / 3, f t) +
      (∫ t in -(4 * Real.pi / 3)..-Real.pi, f t) := by
  have hcont : Continuous (fun t => f (shortPhase t)) := hf.comp continuous_shortPhase
  have h₁ : (∫ t in 0..Real.pi / 3, f (shortPhase t)) =
      ∫ t in 0..Real.pi / 3, f t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 3)] at ht
    exact congrArg f (phase_first ht.2)
  have h₂ : (∫ t in Real.pi / 3..2 * Real.pi, f (shortPhase t)) =
      ∫ t in -(4 * Real.pi / 3)..Real.pi / 3, f t := by
    calc
      _ = ∫ t in Real.pi / 3..2 * Real.pi, f (2 * Real.pi / 3 - t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : Real.pi / 3 ≤ 2 * Real.pi)] at ht
        exact congrArg f (phase_middle ht.1 ht.2)
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_left]
        congr 1 <;> ring
  have h₃ : (∫ t in 2 * Real.pi..7 * Real.pi / 3, f (shortPhase t)) =
      ∫ t in -(4 * Real.pi / 3)..-Real.pi, f t := by
    calc
      _ = ∫ t in 2 * Real.pi..7 * Real.pi / 3, f (t - 10 * Real.pi / 3) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : 2 * Real.pi ≤ 7 * Real.pi / 3)] at ht
        exact congrArg f (phase_last ht.1)
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_right]
        congr 1 <;> ring
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable 0 (2 * Real.pi))
    (hcont.intervalIntegrable (2 * Real.pi) (7 * Real.pi / 3))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable 0 (Real.pi / 3))
    (hcont.intervalIntegrable (Real.pi / 3) (2 * Real.pi))]
  rw [h₁, h₂, h₃]

theorem cos_second_corner : Real.cos (-(4 * Real.pi / 3)) = -(1 / 2 : ℝ) := by
  rw [show -(4 * Real.pi / 3) = -(Real.pi / 3 + Real.pi) by ring,
    Real.cos_neg, Real.cos_add_pi, Real.cos_pi_div_three]

theorem sin_second_corner : Real.sin (-(4 * Real.pi / 3)) = Real.sin (Real.pi / 3) := by
  rw [show -(4 * Real.pi / 3) = -(Real.pi / 3 + Real.pi) by ring,
    Real.sin_neg, Real.sin_add_pi, neg_neg]

theorem short_integral_sin_zero :
    (∫ t in 0..7 * Real.pi / 3, Real.sin (shortPhase t)) = 0 := by
  rw [short_integral Real.sin Real.continuous_sin]
  simp only [integral_sin]
  rw [cos_second_corner]
  simp only [Real.cos_pi_div_three, Real.cos_zero, Real.cos_neg, Real.cos_pi]
  norm_num

theorem short_integral_cos_zero :
    (∫ t in 0..7 * Real.pi / 3, Real.cos (shortPhase t)) = 0 := by
  rw [short_integral Real.cos Real.continuous_cos]
  simp only [integral_cos]
  rw [sin_second_corner]
  simp only [Real.sin_zero, Real.sin_neg, Real.sin_pi]
  ring

theorem short_noise_integral_zero : (∫ t in 0..7 * Real.pi / 3, shortNoise t) = 0 := by
  have hf : shortNoise = fun t =>
      Real.sin (shortPhase t) • (![0, 1, 0] : Fin 3 → ℝ) +
      Real.cos (shortPhase t) • (![0, 0, 1] : Fin 3 → ℝ) := by
    funext t i
    fin_cases i <;> simp [shortNoise]
  have hs : Continuous (fun t => Real.sin (shortPhase t) • (![0, 1, 0] : Fin 3 → ℝ)) :=
    (Real.continuous_sin.comp continuous_shortPhase).smul continuous_const
  have hc : Continuous (fun t => Real.cos (shortPhase t) • (![0, 0, 1] : Fin 3 → ℝ)) :=
    (Real.continuous_cos.comp continuous_shortPhase).smul continuous_const
  rw [hf, intervalIntegral.integral_add (hs.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_smul_const, short_integral_sin_zero,
    short_integral_cos_zero, zero_smul, add_zero]

theorem short_matrix_integral_zero :
    (∫ t in 0..7 * Real.pi / 3,
      (rx (shortPhase t)).conjTranspose * sigmaZ * rx (shortPhase t)) = 0 := by
  have hs : Continuous (fun t => (Real.sin (shortPhase t) : ℂ) • sigmaY) :=
    (Complex.continuous_ofReal.comp (Real.continuous_sin.comp continuous_shortPhase)).smul
      continuous_const
  have hc : Continuous (fun t => (Real.cos (shortPhase t) : ℂ) • sigmaZ) :=
    (Complex.continuous_ofReal.comp (Real.continuous_cos.comp continuous_shortPhase)).smul
      continuous_const
  simp only [rx_conjugates_z, pauli_eq, Complex.ofReal_zero, zero_smul, zero_add]
  rw [intervalIntegral.integral_add (hs.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_smul_const, intervalIntegral.integral_ofReal,
    short_integral_sin_zero, short_integral_cos_zero, Complex.ofReal_zero, zero_smul, add_zero]

-- Pauli 平方把矩阵共轭化为普通三维欧氏平方范数恒等式。
theorem conjugation_preserves_square_norm
    (U : QubitMatrix) (hU : U.conjTranspose * U = 1) (hUU : U * U.conjTranspose = 1)
    (x y z a b c : ℝ) (h : U.conjTranspose * pauli x y z * U = pauli a b c) :
    a * a + b * b + c * c = x * x + y * y + z * z := by
  have heq : pauli a b c * pauli a b c =
      ((x * x + y * y + z * z : ℝ) : ℂ) • (1 : QubitMatrix) := by
    calc
      _ = U.conjTranspose * (pauli x y z * pauli x y z) * U := by
        rw [← h]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc U U.conjTranspose, hUU]
        simp
      _ = _ := by
        rw [pauli_sq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU]
  rw [pauli_sq] at heq
  have he := congrArg (fun M : QubitMatrix => (M 0 0).re) heq
  simpa using he

theorem transverse_commutator (ux uy : ℝ) :
    (Complex.I / 2) •
      (((ux : ℂ) • sigmaX + (uy : ℂ) • sigmaY) * sigmaZ -
       sigmaZ * ((ux : ℂ) • sigmaX + (uy : ℂ) • sigmaY)) = pauli (-uy) ux 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaX, sigmaY, sigmaZ, pauli, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem transverse_noise_speed_squared
    (U : QubitMatrix) (hU : U.conjTranspose * U = 1) (hUU : U * U.conjTranspose = 1)
    (ux uy a b c : ℝ)
    (h : U.conjTranspose * pauli (-uy) ux 0 * U = pauli a b c) :
    a * a + b * b + c * c = ux * ux + uy * uy := by
  have hn := conjugation_preserves_square_norm U hU hUU (-uy) ux 0 a b c h
  nlinarith

abbrev Vec3 := EuclideanSpace ℝ (Fin 3)

def ey : Vec3 := WithLp.toLp 2 ![0, 1, 0]
def ez : Vec3 := WithLp.toLp 2 ![0, 0, 1]
def unitArc (θ : ℝ) : Vec3 := Real.sin θ • ey + Real.cos θ • ez
def shortPath (t : ℝ) : Vec3 := unitArc (shortPhase t)

theorem shortPath_coordinates (t : ℝ) : shortPath t = WithLp.toLp 2 (shortNoise t) := by
  ext i
  fin_cases i <;> simp [shortPath, unitArc, ey, ez, shortNoise]

theorem shortPath_unit (t : ℝ) : ‖shortPath t‖ = 1 := by
  have h : ‖shortPath t‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, shortPath_coordinates]
    exact short_noise_unit t
  nlinarith [norm_nonneg (shortPath t)]

theorem shortPath_antipodal : shortPath (7 * Real.pi / 3) = -shortPath 0 := by
  simp [shortPath, unitArc, shortPhase_initial, shortPhase_final]

theorem shortPath_integral_zero : (∫ t in 0..7 * Real.pi / 3, shortPath t) = 0 := by
  have hs : Continuous (fun t => Real.sin (shortPhase t) • ey) :=
    (Real.continuous_sin.comp continuous_shortPhase).smul continuous_const
  have hc : Continuous (fun t => Real.cos (shortPhase t) • ez) :=
    (Real.continuous_cos.comp continuous_shortPhase).smul continuous_const
  change (∫ t in 0..7 * Real.pi / 3, Real.sin (shortPhase t) • ey +
    Real.cos (shortPhase t) • ez) = 0
  rw [intervalIntegral.integral_add (hs.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_smul_const, short_integral_sin_zero,
    short_integral_cos_zero, zero_smul, add_zero]

theorem shortPhase_lipschitz : LipschitzWith 1 shortPhase := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  wlog hst : s ≤ t generalizing s t
  · simpa only [abs_sub_comm] using this t s (le_of_not_ge hst)
  rw [abs_of_nonpos (sub_nonpos.mpr hst)]
  simp only [shortPhase, max_def]
  split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith [Real.pi_pos]

theorem hasDerivAt_unitArc (θ : ℝ) :
    HasDerivAt unitArc (Real.cos θ • ey + (-Real.sin θ) • ez) θ := by
  exact ((Real.hasDerivAt_sin θ).smul_const ey).add ((Real.hasDerivAt_cos θ).smul_const ez)

theorem unitArc_derivative_norm (θ : ℝ) : ‖Real.cos θ • ey + (-Real.sin θ) • ez‖ = 1 := by
  have h : ‖Real.cos θ • ey + (-Real.sin θ) • ez‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa [ey, ez, Fin.sum_univ_succ, add_comm] using Real.sin_sq_add_cos_sq θ
  nlinarith [norm_nonneg (Real.cos θ • ey + (-Real.sin θ) • ez)]

theorem unitArc_lipschitz : LipschitzWith 1 unitArc := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun θ => (hasDerivAt_unitArc θ).differentiableAt)
  intro θ
  rw [(hasDerivAt_unitArc θ).deriv]
  exact_mod_cast le_of_eq (unitArc_derivative_norm θ)

theorem shortPath_lipschitz : LipschitzWith 1 shortPath := by
  change LipschitzWith 1 (unitArc ∘ shortPhase)
  exact (by simpa only [mul_one] using unitArc_lipschitz.comp shortPhase_lipschitz)

theorem shortPath_certificate :
    (∀ t, ‖shortPath t‖ = 1) ∧
    LipschitzWith 1 shortPath ∧
    shortPath (7 * Real.pi / 3) = -shortPath 0 ∧
    (∫ t in 0..7 * Real.pi / 3, shortPath t) = 0 :=
  ⟨shortPath_unit, shortPath_lipschitz, shortPath_antipodal, shortPath_integral_zero⟩

def transverseGenerator (ux uy : ℝ) : QubitMatrix :=
  (-Complex.I / 2) • ((ux : ℂ) • sigmaX + (uy : ℂ) • sigmaY)

def detuningGenerator : QubitMatrix := (-Complex.I / 2) • sigmaZ

theorem transverseGenerator_skew (ux uy : ℝ) :
    (transverseGenerator ux uy).conjTranspose = -transverseGenerator ux uy := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transverseGenerator, sigmaX, sigmaY, Matrix.conjTranspose_apply] <;> ring

theorem detuningGenerator_skew : detuningGenerator.conjTranspose = -detuningGenerator := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [detuningGenerator, sigmaZ, Matrix.conjTranspose_apply] <;> ring

theorem rx_real_decomposition (θ : ℝ) :
    rx θ = Real.cos (θ / 2) • (1 : QubitMatrix) +
      Real.sin (θ / 2) • ((-Complex.I) • sigmaX) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rx, sigmaX, Complex.real_smul] <;> ring

theorem hasDerivAt_rx (θ : ℝ) :
    HasDerivAt rx (transverseGenerator 1 0 * rx θ) θ := by
  have ht : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) θ := (hasDerivAt_id θ).div_const 2
  have hd := (ht.cos.smul_const (1 : QubitMatrix)).add
    (ht.sin.smul_const ((-Complex.I) • sigmaX))
  have heq : (-Real.sin (θ / 2) * (1 / 2)) • (1 : QubitMatrix) +
      (Real.cos (θ / 2) * (1 / 2)) • ((-Complex.I) • sigmaX) =
      transverseGenerator 1 0 * rx θ := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [transverseGenerator, sigmaX, sigmaY, rx, Matrix.mul_apply, Fin.sum_univ_two,
        Complex.real_smul, -Complex.ofReal_sin, -Complex.ofReal_cos] <;>
      push_cast <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  rw [heq] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards with s
  exact rx_real_decomposition s

def shortControl (t : ℝ) : ℝ :=
  if t < Real.pi / 3 then 1 else if t < 2 * Real.pi then -1 else 1

def shortPropagator (t : ℝ) : QubitMatrix := rx (shortPhase t)

theorem shortControl_amplitude (t : ℝ) : shortControl t ^ 2 = 1 := by
  unfold shortControl
  split_ifs <;> norm_num

theorem hasDerivAt_shortPhase {t : ℝ}
    (h₁ : t ≠ Real.pi / 3) (h₂ : t ≠ 2 * Real.pi) :
    HasDerivAt shortPhase (shortControl t) t := by
  unfold shortControl
  split_ifs with hfirst hmiddle
  · apply (hasDerivAt_id t).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hfirst] with s hs
    exact phase_first hs.le
  · have hleft : Real.pi / 3 < t := lt_of_le_of_ne (le_of_not_gt hfirst) (Ne.symm h₁)
    have hd : HasDerivAt (fun s : ℝ => 2 * Real.pi / 3 - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub (2 * Real.pi / 3)
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hleft, eventually_lt_nhds hmiddle] with s hs₁ hs₂
    exact phase_middle hs₁.le hs₂.le
  · have hright : 2 * Real.pi < t := lt_of_le_of_ne (le_of_not_gt hmiddle) (Ne.symm h₂)
    have hd : HasDerivAt (fun s : ℝ => s - 10 * Real.pi / 3) 1 t :=
      (hasDerivAt_id t).sub_const (10 * Real.pi / 3)
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hright] with s hs
    exact phase_last hs.le

theorem hasDerivAt_shortPropagator {t : ℝ}
    (h₁ : t ≠ Real.pi / 3) (h₂ : t ≠ 2 * Real.pi) :
    HasDerivAt shortPropagator
      (transverseGenerator (shortControl t) 0 * shortPropagator t) t := by
  have hd := (hasDerivAt_rx (shortPhase t)).scomp t (hasDerivAt_shortPhase h₁ h₂)
  have heq : shortControl t • (transverseGenerator 1 0 * rx (shortPhase t)) =
      transverseGenerator (shortControl t) 0 * shortPropagator t := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [transverseGenerator, sigmaX, sigmaY, rx, shortPropagator,
        Matrix.mul_apply, Fin.sum_univ_two, Complex.real_smul] <;> ring
  rw [heq] at hd
  exact hd

theorem shortPropagator_initial : shortPropagator 0 = 1 := by
  rw [shortPropagator, shortPhase_initial, rx_zero]

theorem shortPropagator_gate : shortPropagator (7 * Real.pi / 3) = -rx Real.pi := short_gate

theorem shortPropagator_ac (a b : ℝ) : AbsolutelyContinuousOnInterval shortPropagator a b := by
  have hp : AbsolutelyContinuousOnInterval shortPhase a b :=
    shortPhase_lipschitz.lipschitzOnWith.absolutelyContinuousOnInterval
  have hh : AbsolutelyContinuousOnInterval (fun t => shortPhase t / 2) a b := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hp.const_mul (1 / 2)
  have hc := Real.lipschitzWith_cos.comp_absolutelyContinuousOnInterval hh
  have hs := Real.lipschitzWith_sin.comp_absolutelyContinuousOnInterval hh
  have hI : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : QubitMatrix)) a b :=
    (LipschitzWith.const (1 : QubitMatrix)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hX : AbsolutelyContinuousOnInterval (fun _ : ℝ => (-Complex.I) • sigmaX) a b :=
    (LipschitzWith.const ((-Complex.I) • sigmaX)).lipschitzOnWith.absolutelyContinuousOnInterval
  apply ((hc.smul hI).add (hs.smul hX)).congr
  intro t _
  exact (rx_real_decomposition (shortPhase t)).symm

theorem shortPropagator_ae_ode :
    ∀ᵐ t : ℝ, HasDerivAt shortPropagator
      (transverseGenerator (shortControl t) 0 * shortPropagator t) t := by
  filter_upwards [volume.ae_ne (Real.pi / 3), volume.ae_ne (2 * Real.pi)] with t h₁ h₂
  exact hasDerivAt_shortPropagator h₁ h₂

end
end RobustPiGate.Quantum
