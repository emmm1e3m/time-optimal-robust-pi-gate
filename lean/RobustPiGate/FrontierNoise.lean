import RobustPiGate.QubitDynamics
import RobustPiGate.FrontierDyson

open MeasureTheory Set Filter
open scoped Topology Interval Matrix ComplexConjugate Matrix.Norms.L2Operator

set_option maxHeartbeats 1200000

namespace RobustPiGate.FrontierNoise
open Quantum RobustPiGate.Dynamics

noncomputable section

abbrev BlochVector := Fin 3 → ℝ
abbrev BlochMatrix := Matrix (Fin 3) (Fin 3) ℝ

-- 密度矩阵与真实 Lindblad 生成元；采用论文的 σ₋ 与 Γφ/2 规范。
def density (q : BlochVector) : QubitMatrix :=
  (1 / 2 : ℝ) • (1 + pauli (q 0) (q 1) (q 2))

def sigmaMinus : QubitMatrix := (1 / 2 : ℂ) • (sigmaX - Complex.I • sigmaY)

def dissipator (a ρ : QubitMatrix) : QubitMatrix :=
  a * ρ * a.conjTranspose - (1 / 2 : ℝ) •
    (a.conjTranspose * a * ρ + ρ * (a.conjTranspose * a))

def lindblad (ux uy δ Γ₁ Γφ : ℝ) (ρ : QubitMatrix) : QubitMatrix :=
  (-Complex.I) • (((1 / 2 : ℝ) • pauli ux uy δ) * ρ -
    ρ * ((1 / 2 : ℝ) • pauli ux uy δ)) +
    Γ₁ • dissipator sigmaMinus ρ + (Γφ / 2) • dissipator sigmaZ ρ

def rotationGenerator (ux uy δ : ℝ) : BlochMatrix :=
  !![0, -δ, uy; δ, 0, -ux; -uy, ux, 0]

def damping (Γ₁ Γφ : ℝ) : BlochMatrix :=
  Matrix.diagonal ![-(Γ₁ / 2 + Γφ), -(Γ₁ / 2 + Γφ), -Γ₁]

def translation (Γ₁ : ℝ) : BlochVector := ![0, 0, -Γ₁]

def blochRHS (ux uy δ Γ₁ Γφ : ℝ) (q : BlochVector) : BlochVector :=
  (rotationGenerator ux uy δ + damping Γ₁ Γφ).mulVec q + translation Γ₁

theorem sigmaMinus_entries : sigmaMinus = !![0, 0; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaMinus, sigmaX, sigmaY, Complex.I_sq] <;> ring

-- 本恒等式逐项核对 Hamiltonian、振幅阻尼与纯退相干，未预设 Bloch 方程。
theorem lindblad_density (ux uy δ Γ₁ Γφ : ℝ) (q : BlochVector) :
    lindblad ux uy δ Γ₁ Γφ (density q) =
      (1 / 2 : ℝ) • pauli
        (blochRHS ux uy δ Γ₁ Γφ q 0)
        (blochRHS ux uy δ Γ₁ Γφ q 1)
        (blochRHS ux uy δ Γ₁ Γφ q 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lindblad, density, dissipator, sigmaMinus_entries, sigmaZ, pauli,
      blochRHS, rotationGenerator, damping, translation, Matrix.mul_apply,
      Matrix.mulVec, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Fin.sum_univ_succ,
      Matrix.one_apply, Matrix.conjTranspose_apply, Complex.real_smul, Complex.I_sq] <;>
    push_cast <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem rotationGenerator_skew (ux uy δ : ℝ) :
    star (rotationGenerator ux uy δ) = -rotationGenerator ux uy δ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotationGenerator, Matrix.star_apply]

theorem damping_trace (Γ₁ Γφ : ℝ) :
    Matrix.trace (damping Γ₁ Γφ) = -2 * (Γ₁ + Γφ) := by
  simp [damping, Matrix.trace, Fin.sum_univ_succ]
  ring

theorem damping_scaling (η Γ₁ Γφ : ℝ) :
    damping (η * Γ₁) (η * Γφ) = η • damping Γ₁ Γφ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [damping] <;> ring

theorem rotationGenerator_detuning (ux uy δ : ℝ) :
    rotationGenerator ux uy δ =
      rotationGenerator ux uy 0 + δ • rotationGenerator 0 0 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotationGenerator]

theorem density_pair_trace (q r : BlochVector) :
    (Matrix.trace (density q * density r)).re = (1 + dotProduct q r) / 2 := by
  simp [density, pauli, Matrix.trace, Matrix.mul_apply, Matrix.vecMul,
    dotProduct, Fin.sum_univ_succ, Matrix.one_apply, Complex.real_smul]
  ring

def linearDensity : BlochVector →L[ℝ] QubitMatrix :=
  LinearMap.toContinuousLinearMap
    { toFun := fun q => (1 / 2 : ℝ) • pauli (q 0) (q 1) (q 2)
      map_add' := by
        intro q r
        ext i j
        fin_cases i <;> fin_cases j <;> simp [pauli, Complex.real_smul] <;> ring
      map_smul' := by
        intro r q
        ext i j
        fin_cases i <;> fin_cases j <;> simp [pauli, Complex.real_smul] <;> ring }

def linearBloch : QubitMatrix →L[ℝ] BlochVector :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ρ => ![2 * (ρ 0 1).re, -2 * (ρ 0 1).im, 2 * (ρ 0 0).re]
      map_add' := by intro ρ σ; ext i; fin_cases i <;> simp <;> ring
      map_smul' := by
        intro r ρ
        ext i
        fin_cases i <;> simp [Complex.real_smul] <;> ring }

theorem density_linear (q : BlochVector) :
    density q = (1 / 2 : ℝ) • (1 : QubitMatrix) + linearDensity q := by
  simp [density, linearDensity, smul_add]

@[simp] theorem linearBloch_linearDensity (q : BlochVector) :
    linearBloch (linearDensity q) = q := by
  ext i
  fin_cases i <;> simp [linearBloch, linearDensity, pauli, Complex.real_smul] <;> ring

@[simp] theorem linearBloch_density (q : BlochVector) :
    linearBloch (density q) - ![0, 0, 1] = q := by
  ext i
  fin_cases i <;> simp [linearBloch, density, pauli, Complex.real_smul] <;> ring

theorem density_hasDerivAt_iff {q : ℝ → BlochVector} {v : BlochVector} {t : ℝ} :
    HasDerivAt (fun s => density (q s)) (linearDensity v) t ↔ HasDerivAt q v t := by
  constructor
  · intro h
    have hh := ((linearBloch.hasFDerivAt.comp_hasDerivAt t h).sub_const ![0, 0, 1])
    simpa only [Function.comp_def, linearBloch_density, linearBloch_linearDensity] using hh
  · intro h
    simpa only [Function.comp_def, ← density_linear] using
      (linearDensity.hasFDerivAt.comp_hasDerivAt t h).const_add
        ((1 / 2 : ℝ) • (1 : QubitMatrix))

theorem density_ac_iff {q : ℝ → BlochVector} {T : ℝ} :
    AbsolutelyContinuousOnInterval (fun s => density (q s)) 0 T ↔
      AbsolutelyContinuousOnInterval q 0 T := by
  constructor
  · intro h
    have hh := (linearBloch.lipschitzWith.comp_absolutelyContinuousOnInterval h).sub
      (LipschitzWith.const (α := ℝ) ![0, 0, 1]).lipschitzOnWith.absolutelyContinuousOnInterval
    apply hh.congr
    intro t _
    exact linearBloch_density (q t)
  · intro h
    have hh := (LipschitzWith.const (α := ℝ)
      ((1 / 2 : ℝ) • (1 : QubitMatrix))).lipschitzOnWith.absolutelyContinuousOnInterval.add
      (linearDensity.lipschitzWith.comp_absolutelyContinuousOnInterval h)
    apply hh.congr
    intro t _
    exact (density_linear (q t)).symm

-- AC/a.e. 微分方程之间的精确共轭：两边都保留真实时间导数。
theorem lindblad_ode_iff_bloch_ode
    {ux uy : ℝ → ℝ} {δ Γ₁ Γφ T : ℝ} {q : ℝ → BlochVector} :
    (AbsolutelyContinuousOnInterval (fun s => density (q s)) 0 T ∧
      ∀ᵐ t, t ∈ uIcc 0 T → HasDerivAt (fun s => density (q s))
        (lindblad (ux t) (uy t) δ Γ₁ Γφ (density (q t))) t) ↔
    (AbsolutelyContinuousOnInterval q 0 T ∧
      ∀ᵐ t, t ∈ uIcc 0 T →
        HasDerivAt q (blochRHS (ux t) (uy t) δ Γ₁ Γφ (q t)) t) := by
  rw [density_ac_iff]
  have heq : ∀ t, lindblad (ux t) (uy t) δ Γ₁ Γφ (density (q t)) =
      linearDensity (blochRHS (ux t) (uy t) δ Γ₁ Γφ (q t)) := by
    intro t
    exact lindblad_density _ _ _ _ _ _
  simp only [heq, density_hasDerivAt_iff]

def mulVecCLM (q : BlochVector) : BlochMatrix →L[ℝ] BlochVector :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M.mulVec q
      map_add' := by intros; simp [Matrix.add_mulVec]
      map_smul' := by intros; simp [Matrix.smul_mulVec] }

@[simp] theorem mulVecCLM_apply (q : BlochVector) (M : BlochMatrix) :
    mulVecCLM q M = M.mulVec q := rfl

-- 齐次矩阵和仿射平移的真实ODE产生完整Lindblad信道，而非只产生一个形式展开。
theorem affine_bloch_is_lindblad
    {ux uy : ℝ → ℝ} {δ Γ₁ Γφ T : ℝ}
    {V : ℝ → BlochMatrix} {c : ℝ → BlochVector}
    (hV : IsACSolution (fun t => rotationGenerator (ux t) (uy t) δ + damping Γ₁ Γφ) V T)
    (hc : AbsolutelyContinuousOnInterval c 0 T)
    (hdc : ∀ᵐ t, t ∈ uIcc 0 T →
      HasDerivAt c (blochRHS (ux t) (uy t) δ Γ₁ Γφ (c t)) t)
    (q : BlochVector) :
    AbsolutelyContinuousOnInterval (fun t => density ((V t).mulVec q + c t)) 0 T ∧
      ∀ᵐ t, t ∈ uIcc 0 T →
        HasDerivAt (fun s => density ((V s).mulVec q + c s))
          (lindblad (ux t) (uy t) δ Γ₁ Γφ (density ((V t).mulVec q + c t))) t := by
  apply lindblad_ode_iff_bloch_ode.mpr
  constructor
  · have hh := ((mulVecCLM q).lipschitzWith.comp_absolutelyContinuousOnInterval hV.ac).add hc
    apply hh.congr
    intro t _
    rfl
  · filter_upwards [hV.equation, hdc] with t hvt hct ht
    have h := ((mulVecCLM q).hasFDerivAt.comp_hasDerivAt t (hvt ht)).add (hct ht)
    convert h using 1
    · rfl
    · simp only [blochRHS, mulVecCLM_apply, Matrix.mulVec_add, Matrix.mulVec_mulVec]
      abel

abbrev BlochSpace := EuclideanSpace ℝ (Fin 3)

def blochApply (q : BlochSpace) : BlochMatrix →L[ℝ] BlochSpace :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3) M q
      map_add' := by intros; simp
      map_smul' := by intros; simp }

@[simp] theorem blochApply_apply (q : BlochSpace) (M : BlochMatrix) :
    blochApply q M = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3) M q := rfl

-- 控制部分反对称，故平方范数的变化只含负半定阻尼项。
theorem inner_generator (ux uy δ Γ₁ Γφ : ℝ) (q : BlochSpace) :
    inner ℝ q (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3)
      (rotationGenerator ux uy δ + damping Γ₁ Γφ) q) =
      -(Γ₁ / 2 + Γφ) * ((q 0)^2 + (q 1)^2) - Γ₁ * (q 2)^2 := by
  rw [Matrix.inner_toEuclideanCLM]
  simp [rotationGenerator, damping, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

-- 从原 AC/a.e. Bloch ODE 推出收缩；不把有界传播子作为物理模型的额外前提。
theorem bloch_solution_contraction
    {ux uy : ℝ → ℝ} {δ Γ₁ Γφ T : ℝ} {V : ℝ → BlochMatrix}
    (hT : 0 ≤ T) (h₁ : 0 ≤ Γ₁) (hφ : 0 ≤ Γφ)
    (hV : IsACSolution (fun t => rotationGenerator (ux t) (uy t) δ + damping Γ₁ Γφ) V T) :
    ‖V T‖ ≤ 1 := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  let f : ℝ → BlochSpace := fun t => Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3) (V t) q
  have hf : AbsolutelyContinuousOnInterval f 0 T := by
    simpa only [Function.comp_def, blochApply_apply, f] using
      (blochApply q).lipschitzWith.comp_absolutelyContinuousOnInterval hV.ac
  have hn := lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hf
  have hs : AbsolutelyContinuousOnInterval (fun t => ‖f t‖^2) 0 T := by
    simpa only [Function.comp_def, pow_two] using hn.fun_mul hn
  let d : ℝ → ℝ := fun t =>
    2 * (-(Γ₁ / 2 + Γφ) * ((f t 0)^2 + (f t 1)^2) - Γ₁ * (f t 2)^2)
  have hd : ∀ᵐ t, t ∈ uIcc 0 T → HasDerivAt (fun t => ‖f t‖^2) (d t) t := by
    filter_upwards [hV.equation] with t ht htI
    have hq := (blochApply q).hasFDerivAt.comp_hasDerivAt t (ht htI)
    have hq' : HasDerivAt f (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3)
        (rotationGenerator (ux t) (uy t) δ + damping Γ₁ Γφ) (f t)) t := by
      simpa only [Function.comp_def, blochApply_apply, map_mul, mul_apply_eq_comp, f] using hq
    simpa only [d, inner_generator] using hq'.norm_sq
  have hc : ContinuousOn d (uIcc 0 T) := by
    have hfc := hf.continuousOn
    dsimp [d]
    fun_prop
  have hi : IntervalIntegrable d volume 0 T := hc.intervalIntegrable
  have heq := integral_eq_sub_of_ac_ae hs hi hd
  have hneg : (∫ t in 0..T, d t) ≤ 0 := by
    have hmono := intervalIntegral.integral_mono_on hT hi
      (intervalIntegrable_const (c := (0 : ℝ))) (fun t _ => show d t ≤ 0 by
        dsimp [d]
        have ha : 0 ≤ Γ₁ / 2 + Γφ := by positivity
        have hb : 0 ≤ (f t 0)^2 + (f t 1)^2 := by positivity
        nlinarith [mul_nonneg ha hb, mul_nonneg h₁ (sq_nonneg (f t 2))])
    simpa using hmono
  have hnorm : ‖f T‖^2 ≤ ‖q‖^2 := by
    have hz : f 0 = q := by simp [f, hV.initial]
    rw [heq, hz] at hneg
    linarith
  simpa only [one_mul, f] using
    (sq_le_sq₀ (norm_nonneg (f T)) (norm_nonneg q)).mp hnorm

theorem bloch_solution_contraction_on
    {ux uy : ℝ → ℝ} {δ Γ₁ Γφ T t : ℝ} {V : ℝ → BlochMatrix}
    (hT : 0 ≤ T) (h₁ : 0 ≤ Γ₁) (hφ : 0 ≤ Γφ)
    (hV : IsACSolution (fun t => rotationGenerator (ux t) (uy t) δ + damping Γ₁ Γφ) V T)
    (ht : t ∈ uIcc 0 T) : ‖V t‖ ≤ 1 := by
  exact bloch_solution_contraction ((uIcc_of_le hT ▸ ht).1) h₁ hφ (hV.restrict ht)

def traceCLM : BlochMatrix →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 3) ℝ ℝ)

@[simp] theorem traceCLM_apply (M : BlochMatrix) : traceCLM M = Matrix.trace M := rfl

theorem trace_rotated_damping {ux uy : ℝ → ℝ} {T t Γ₁ Γφ : ℝ}
    {O : ℝ → BlochMatrix}
    (hO : IsACSolution (fun t => rotationGenerator (ux t) (uy t) 0) O T)
    (ht : t ∈ uIcc 0 T) :
    Matrix.trace (star (O t) * damping Γ₁ Γφ * O t) = -2 * (Γ₁ + Γφ) := by
  have hu := hO.unitary
    (Filter.Eventually.of_forall fun s _ => rotationGenerator_skew (ux s) (uy s) 0) ht
  rw [Matrix.trace_mul_cycle, hu.2, one_mul, damping_trace]

theorem trace_damping_integral {ux uy : ℝ → ℝ} {T Γ₁ Γφ : ℝ}
    {O : ℝ → BlochMatrix}
    (hO : IsACSolution (fun t => rotationGenerator (ux t) (uy t) 0) O T) :
    Matrix.trace (∫ t in 0..T, star (O t) * damping Γ₁ Γφ * O t) =
      -2 * (Γ₁ + Γφ) * T := by
  have hi : IntervalIntegrable (fun t => star (O t) * damping Γ₁ Γφ * O t) volume 0 T :=
    ((hO.ac.continuousOn.star.mul_const _).mul hO.ac.continuousOn).intervalIntegrable
  change traceCLM (∫ t in 0..T, star (O t) * damping Γ₁ Γφ * O t) = _
  rw [← traceCLM.intervalIntegral_comp_comm hi]
  have heq : (∫ t in 0..T, traceCLM (star (O t) * damping Γ₁ Γφ * O t)) =
      ∫ _t in 0..T, -2 * (Γ₁ + Γφ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact trace_rotated_damping hO ht
  rw [heq]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring

-- 该量在065的真实球面平均中等于1-Favg；平移项已由球面平均消去。
def channelInfidelity (M : BlochMatrix) : ℝ := (3 - Matrix.trace M) / 6

-- 一阶耗散系数由原ODE及迹不变性推出，并给出显式二阶误差界。
theorem weak_dissipation_remainder
    {ux uy : ℝ → ℝ} {T Γ₁ Γφ : ℝ} {O V : ℝ → BlochMatrix}
    (hT : 0 ≤ T) (h₁ : 0 ≤ Γ₁) (hφ : 0 ≤ Γφ)
    (hO : IsACSolution (fun t => rotationGenerator (ux t) (uy t) 0) O T)
    (hV : IsACSolution
      (fun t => rotationGenerator (ux t) (uy t) 0 + damping Γ₁ Γφ) V T) :
    |channelInfidelity (star (O T) * V T) - (Γ₁ + Γφ) * T / 3| ≤
      ‖traceCLM‖ / 6 * (‖damping Γ₁ Γφ‖ * |T|)^2 := by
  let I : BlochMatrix := ∫ t in 0..T, star (O t) * damping Γ₁ Γφ * O t
  have hr := FrontierDyson.norm_dyson_remainder_le hO hV
    (Filter.Eventually.of_forall fun t _ => rotationGenerator_skew (ux t) (uy t) 0)
    (fun t ht => bloch_solution_contraction_on hT h₁ hφ hV ht) 2
  have hr' : ‖star (O T) * V T - (1 + I)‖ ≤ (‖damping Γ₁ Γφ‖ * |T|)^2 := by
    simpa [FrontierDyson.frame, FrontierDyson.term, FrontierDyson.iterate,
      FrontierDyson.step, FrontierDyson.kernel, Finset.sum_range_succ, I] using hr
  have htrace : Matrix.trace I = -2 * (Γ₁ + Γφ) * T := trace_damping_integral hO
  have heq : channelInfidelity (star (O T) * V T) - (Γ₁ + Γφ) * T / 3 =
      -(traceCLM (star (O T) * V T - (1 + I))) / 6 := by
    simp [channelInfidelity, traceCLM_apply, Matrix.trace_sub, Matrix.trace_add,
      Matrix.trace_one, htrace]
    ring
  rw [heq, abs_div, abs_neg]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  have hb := traceCLM.le_opNorm (star (O T) * V T - (1 + I))
  rw [Real.norm_eq_abs] at hb
  have hb' := hb.trans (mul_le_mul_of_nonneg_left hr' (norm_nonneg traceCLM))
  apply (div_le_div_of_nonneg_right hb' (by norm_num : (0:ℝ) ≤ 6)).trans_eq
  ring

end
end RobustPiGate.FrontierNoise

