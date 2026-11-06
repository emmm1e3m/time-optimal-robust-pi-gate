import RobustPiGate.FrontierNoise
import RobustPiGate.FrontierDyson
import RobustPiGate.FrontierAverage
import RobustPiGate.FrontierSphere
import RobustPiGate.FrontierBlochUnitary
import RobustPiGate.FrontierContinuity
import RobustPiGate.FrontierVariance

open MeasureTheory Set Filter Asymptotics
open scoped Topology Interval Matrix Matrix.Norms.L2Operator

set_option maxHeartbeats 1200000

namespace RobustPiGate.FrontierNoise
open Quantum RobustPiGate.Dynamics FrontierDyson
noncomputable section

-- 真实纯输入态的球面平均；不是直接以矩阵迹作为保真度定义。
def averageStateFidelity (M : BlochMatrix) (c : BlochVector) : ℝ :=
  FrontierSphere.sphereAverage
    (fun q => (Matrix.trace (density q * density (M.mulVec q + c))).re)

theorem averageStateFidelity_eq (M : BlochMatrix) (c : BlochVector) :
    averageStateFidelity M c = 1 / 2 + Matrix.trace M / 6 := by
  simp only [averageStateFidelity, density_pair_trace]
  exact FrontierSphere.sphereAverage_fidelity M c

theorem averageStateInfidelity_eq (M : BlochMatrix) (c : BlochVector) :
    1 - averageStateFidelity M c = channelInfidelity M := by
  rw [averageStateFidelity_eq]
  unfold channelInfidelity
  ring

def lossFunctional : BlochMatrix →L[ℝ] ℝ := (-1 / 6 : ℝ) • traceCLM

@[simp] theorem lossFunctional_apply (M : BlochMatrix) :
    lossFunctional M = -Matrix.trace M / 6 := by
  simp [lossFunctional]
  ring

theorem lossFunctional_sub_one (M : BlochMatrix) :
    lossFunctional (M - 1) = channelInfidelity M := by
  simp [channelInfidelity, Matrix.trace_sub, Matrix.trace_one]

theorem lossFunctional_damping_word {ux uy : ℝ → ℝ} {T γ₁ γφ : ℝ}
    {O : ℝ → BlochMatrix}
    (hO : IsACSolution (fun t => rotationGenerator (ux t) (uy t) 0) O T) :
    lossFunctional (word O [damping γ₁ γφ] T) = (γ₁ + γφ) * T / 3 := by
  simp only [lossFunctional_apply, word, step, kernel, mul_one]
  rw [trace_damping_integral hO]
  ring

-- 固定控制，η和随机样本x只进入真实失谐/耗散生成元。
def IsNoisyBlochEvolution (ux uy : ℝ → ℝ) (γ₁ γφ : ℝ)
    (V : ℝ → ℝ → ℝ → BlochMatrix) (T : ℝ) : Prop :=
  ∀ η x, IsACSolution (fun t => rotationGenerator (ux t) (uy t) (η*x) +
    damping (η^2*γ₁) (η^2*γφ)) (V η x) T

-- 完整仿射信道的ODE数据，含实际输入初值所需的c(0)=0。
structure IsNoisyLindbladChannel (ux uy : ℝ → ℝ) (γ₁ γφ : ℝ)
    (V : ℝ → ℝ → ℝ → BlochMatrix) (c : ℝ → ℝ → ℝ → BlochVector) (T : ℝ) : Prop where
  homogeneous : IsNoisyBlochEvolution ux uy γ₁ γφ V T
  translation_ac : ∀ η x, AbsolutelyContinuousOnInterval (c η x) 0 T
  translation_initial : ∀ η x, c η x 0 = 0
  translation_ode : ∀ η x, ∀ᵐ t, t ∈ uIcc 0 T →
    HasDerivAt (c η x)
      (blochRHS (ux t) (uy t) (η*x) (η^2*γ₁) (η^2*γφ) (c η x t)) t

def lindbladOutput (V : ℝ → ℝ → ℝ → BlochMatrix)
    (c : ℝ → ℝ → ℝ → BlochVector) (η x t : ℝ) (q : BlochVector) : QubitMatrix :=
  density ((V η x t).mulVec q + c η x t)

theorem IsNoisyLindbladChannel.original_ode
    {ux uy : ℝ → ℝ} {γ₁ γφ T : ℝ}
    {V : ℝ → ℝ → ℝ → BlochMatrix} {c : ℝ → ℝ → ℝ → BlochVector}
    (h : IsNoisyLindbladChannel ux uy γ₁ γφ V c T) (η x : ℝ) (q : BlochVector) :
    lindbladOutput V c η x 0 q = density q ∧
      AbsolutelyContinuousOnInterval (fun t => lindbladOutput V c η x t q) 0 T ∧
      ∀ᵐ t, t ∈ uIcc 0 T →
        HasDerivAt (fun s => lindbladOutput V c η x s q)
          (lindblad (ux t) (uy t) (η*x) (η^2*γ₁) (η^2*γφ)
            (lindbladOutput V c η x t q)) t := by
  constructor
  · simp [lindbladOutput, (h.homogeneous η x).initial, h.translation_initial]
  · exact affine_bloch_is_lindblad (h.homogeneous η x)
      (h.translation_ac η x) (h.translation_ode η x) q

theorem noisy_evolution_as_perturbation
    {ux uy : ℝ → ℝ} {γ₁ γφ T : ℝ} {V : ℝ → ℝ → ℝ → BlochMatrix}
    (hV : IsNoisyBlochEvolution ux uy γ₁ γφ V T) (η x : ℝ) :
    IsACSolution (fun t => rotationGenerator (ux t) (uy t) 0 +
      ((η*x) • rotationGenerator 0 0 1 + η^2 • damping γ₁ γφ)) (V η x) T := by
  have heq : (fun t => rotationGenerator (ux t) (uy t) (η*x) + damping (η^2*γ₁) (η^2*γφ)) =
      (fun t => rotationGenerator (ux t) (uy t) 0 +
        ((η*x) • rotationGenerator 0 0 1 + η^2 • damping γ₁ γφ)) := by
    funext t
    rw [rotationGenerator_detuning (ux t) (uy t) (η*x), damping_scaling]
    exact add_assoc _ _ _
  rw [← heq]
  exact hV η x

def noiseRemainderConstant (O : ℝ → BlochMatrix) (γ₁ γφ T : ℝ) : ℝ :=
  ‖lossFunctional‖ * mixedConstant O (rotationGenerator 0 0 1) (damping γ₁ γφ) T 1

def staticDysonCoefficient (O : ℝ → BlochMatrix) (T : ℝ) : ℝ :=
  lossFunctional (word O [rotationGenerator 0 0 1, rotationGenerator 0 0 1] T)

def oddLinearLoss (O : ℝ → BlochMatrix) (γ₁ γφ T η : ℝ) : ℝ :=
  lossFunctional (oddLinear O (rotationGenerator 0 0 1) (damping γ₁ γφ) η T)

def oddCubicLoss (O : ℝ → BlochMatrix) (T η : ℝ) : ℝ :=
  lossFunctional (oddCubic O (rotationGenerator 0 0 1) η T)

-- 原ODE给出的全x余项界；对无界支撑分布也有效。
theorem noisy_pointwise_expansion
    {ux uy : ℝ → ℝ} {γ₁ γφ T η x : ℝ}
    {O : ℝ → BlochMatrix} {V : ℝ → ℝ → ℝ → BlochMatrix}
    (hT : 0 ≤ T) (h₁ : 0 ≤ γ₁) (hφ : 0 ≤ γφ)
    (hO : IsACSolution (fun t => rotationGenerator (ux t) (uy t) 0) O T)
    (hV : IsNoisyBlochEvolution ux uy γ₁ γφ V T) (hη : |η| ≤ 1) :
    |channelInfidelity (star (O T) * V η x T) -
      (η^2 * (staticDysonCoefficient O T * x^2 + (γ₁ + γφ) * T / 3) +
        (oddLinearLoss O γ₁ γφ T η * x + oddCubicLoss O T η * x^3))| ≤
      noiseRemainderConstant O γ₁ γφ T * η^4 * (1+x^4) := by
  have h := functional_mixed_remainder_le hO (noisy_evolution_as_perturbation hV η x)
    (Filter.Eventually.of_forall fun t _ => rotationGenerator_skew (ux t) (uy t) 0)
    (fun t ht => bloch_solution_contraction_on hT (mul_nonneg (sq_nonneg η) h₁)
      (mul_nonneg (sq_nonneg η) hφ) (hV η x) ht) hη lossFunctional
  rw [lossFunctional_damping_word hO] at h
  simp only [frame, lossFunctional_sub_one] at h
  convert h using 1
  · congr 1
    dsimp [staticDysonCoefficient, oddLinearLoss, oddCubicLoss]
    ring
  · rfl

-- 先提供可测性接口；最终定理由参数连续性模块消除此中间前提。
theorem averaged_noise_expansion_of_measurable
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {ux uy : ℝ → ℝ} {γ₁ γφ T : ℝ}
    {O : ℝ → BlochMatrix} {V : ℝ → ℝ → ℝ → BlochMatrix}
    (hT : 0 ≤ T) (h₁ : 0 ≤ γ₁) (hφ : 0 ≤ γφ)
    (hO : IsACSolution (fun t => rotationGenerator (ux t) (uy t) 0) O T)
    (hV : IsNoisyBlochEvolution ux uy γ₁ γφ V T)
    (hs : FrontierAverage.SymmetricLaw μ)
    (h4 : Integrable (fun x : ℝ => x^4) μ)
    (hq : ∀ᶠ η in 𝓝 (0 : ℝ), AEStronglyMeasurable
      (fun x => channelInfidelity (star (O T) * V η x T)) μ) :
    (fun η => (∫ x, channelInfidelity (star (O T) * V η x T) ∂μ) -
      η^2 * (staticDysonCoefficient O T * (∫ x : ℝ, x^2 ∂μ) + (γ₁ + γφ) * T / 3))
      =O[𝓝 (0 : ℝ)] (fun η => η^4) := by
  apply FrontierAverage.averaged_polynomial_expansion_isBigO hs h4
    (staticDysonCoefficient O T) ((γ₁ + γφ) * T / 3)
    (noiseRemainderConstant O γ₁ γφ T)
    (oddLinearLoss O γ₁ γφ T) (oddCubicLoss O T) hq
  have hη : ∀ᶠ η : ℝ in 𝓝 0, |η| ≤ 1 := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) zero_lt_one] with η hη
    exact abs_le.mpr ⟨hη.1.le, hη.2.le⟩
  filter_upwards [hη] with η hη x
  exact noisy_pointwise_expansion hT h₁ hφ hO hV hη

theorem noisy_channelInfidelity_continuous
    {ux uy : ℝ → ℝ} {γ₁ γφ T : ℝ}
    {O : ℝ → BlochMatrix} {V : ℝ → ℝ → ℝ → BlochMatrix}
    (hT : 0 ≤ T) (h₁ : 0 ≤ γ₁) (hφ : 0 ≤ γφ)
    (hO : IsACSolution (fun t => rotationGenerator (ux t) (uy t) 0) O T)
    (hV : IsNoisyBlochEvolution ux uy γ₁ γφ V T) (η : ℝ) :
    Continuous (fun x => channelInfidelity (star (O T) * V η x T)) := by
  have hv : ∀ x, IsACSolution (fun t => rotationGenerator (ux t) (uy t) 0 +
      (x • (η • rotationGenerator 0 0 1) + η^2 • damping γ₁ γφ)) (V η x) T := by
    intro x
    simpa only [smul_smul, mul_comm x η] using noisy_evolution_as_perturbation hV η x
  have h := FrontierContinuity.continuous_parameter_readout hT hO hv
    (Filter.Eventually.of_forall fun t _ => rotationGenerator_skew (ux t) (uy t) 0)
    (fun x t ht => bloch_solution_contraction_on hT (mul_nonneg (sq_nonneg η) h₁)
      (mul_nonneg (sq_nonneg η) hφ) (hV η x) ht) lossFunctional 1
  simpa only [one_mul, frame, lossFunctional_sub_one] using h

-- 可测性由真实ODE连续依赖导出；本定理没有保真度展开或可测性假设。
theorem averaged_noise_expansion
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {ux uy : ℝ → ℝ} {γ₁ γφ T : ℝ}
    {O : ℝ → BlochMatrix} {V : ℝ → ℝ → ℝ → BlochMatrix}
    (hT : 0 ≤ T) (h₁ : 0 ≤ γ₁) (hφ : 0 ≤ γφ)
    (hO : IsACSolution (fun t => rotationGenerator (ux t) (uy t) 0) O T)
    (hV : IsNoisyBlochEvolution ux uy γ₁ γφ V T)
    (hs : FrontierAverage.SymmetricLaw μ)
    (h4 : Integrable (fun x : ℝ => x^4) μ) :
    (fun η => (∫ x, channelInfidelity (star (O T) * V η x T) ∂μ) -
      η^2 * (staticDysonCoefficient O T * (∫ x : ℝ, x^2 ∂μ) + (γ₁ + γφ) * T / 3))
      =O[𝓝 (0 : ℝ)] (fun η => η^4) := by
  apply averaged_noise_expansion_of_measurable hT h₁ hφ hO hV hs h4
  exact Filter.Eventually.of_forall fun η =>
    (noisy_channelInfidelity_continuous hT h₁ hφ hO hV η).aestronglyMeasurable

theorem staticDysonCoefficient_quantum {ux uy : ℝ → ℝ}
    {U : ℝ → ℝ → QubitMatrix} {T : ℝ} (hU : IsQubitEvolution ux uy U T) :
    staticDysonCoefficient (fun t => blochRotation (U 0 t)) T =
      ‖∫ t in 0..T, noiseVec (U 0 t)‖^2 / 6 := by
  simpa only [staticDysonCoefficient, lossFunctional_apply, blochStaticDysonCoefficient] using
    blochStaticDysonCoefficient_eq hU

theorem density_blochRotation (W : QubitMatrix) (hW : W ∈ unitary QubitMatrix)
    (q : BlochVector) :
    density ((blochRotation W).mulVec q) = W * density q * star W := by
  rw [density, blochRotation_pauli W hW q]
  simp only [density, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one,
    smul_add, hW.2]
  simp only [Matrix.star_eq_conjTranspose]

-- 此处直接平均真实Lindblad输出与名义目标纯态之间的态保真度。
def lindbladGateFidelity (W : QubitMatrix) (M : BlochMatrix) (c : BlochVector) : ℝ :=
  FrontierSphere.sphereAverage (fun q =>
    (Matrix.trace (density q * (star W * density (M.mulVec q + c) * W))).re)

theorem lindbladGateFidelity_eq (W : QubitMatrix) (hW : W ∈ unitary QubitMatrix)
    (M : BlochMatrix) (c : BlochVector) :
    lindbladGateFidelity W M c =
      averageStateFidelity (star (blochRotation W) * M) ((star (blochRotation W)).mulVec c) := by
  unfold lindbladGateFidelity averageStateFidelity
  congr 1
  funext q
  have h := density_blochRotation (star W) (Unitary.star_mem hW) (M.mulVec q + c)
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, blochRotation_star] at h
  simp only [Matrix.star_eq_conjTranspose]
  rw [← h]
  congr 3
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.mulVec_add, Matrix.mulVec_mulVec]

theorem lindbladGateInfidelity_eq (W : QubitMatrix) (hW : W ∈ unitary QubitMatrix)
    (M : BlochMatrix) (c : BlochVector) :
    1 - lindbladGateFidelity W M c = channelInfidelity (star (blochRotation W) * M) := by
  rw [lindbladGateFidelity_eq W hW M c, averageStateInfidelity_eq]

-- 全部噪声系数已经识别为原2×2传播子的χ，平移项为真实信道的任意平移。
theorem averaged_lindblad_infidelity
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {ux uy : ℝ → ℝ} {γ₁ γφ T : ℝ}
    {U : ℝ → ℝ → QubitMatrix} {V : ℝ → ℝ → ℝ → BlochMatrix}
    (hT : 0 ≤ T) (h₁ : 0 ≤ γ₁) (hφ : 0 ≤ γφ)
    (hU : IsQubitEvolution ux uy U T)
    (hV : IsNoisyBlochEvolution ux uy γ₁ γφ V T)
    (hs : FrontierAverage.SymmetricLaw μ)
    (h4 : Integrable (fun x : ℝ => x^4) μ)
    (c : ℝ → ℝ → BlochVector) :
    (fun η => (∫ x, 1 - lindbladGateFidelity (U 0 T) (V η x T) (c η x) ∂μ) -
      η^2 * ((‖∫ t in 0..T, noiseVec (U 0 t)‖^2 / 6) *
        (∫ x : ℝ, x^2 ∂μ) + (γ₁ + γφ) * T / 3))
      =O[𝓝 (0 : ℝ)] (fun η => η^4) := by
  have h := averaged_noise_expansion hT h₁ hφ (blochRotation_isACSolution hU 0) hV hs h4
  rw [staticDysonCoefficient_quantum hU] at h
  simpa only [lindbladGateInfidelity_eq _ (qubit_nominal_unitary hU right_mem_uIcc)] using h

theorem weak_dissipation_state_remainder
    {ux uy : ℝ → ℝ} {T Γ₁ Γφ : ℝ}
    {U : ℝ → ℝ → QubitMatrix} {V : ℝ → BlochMatrix}
    (hT : 0 ≤ T) (h₁ : 0 ≤ Γ₁) (hφ : 0 ≤ Γφ)
    (hU : IsQubitEvolution ux uy U T)
    (hV : IsACSolution
      (fun t => rotationGenerator (ux t) (uy t) 0 + damping Γ₁ Γφ) V T)
    (c : BlochVector) :
    |(1 - lindbladGateFidelity (U 0 T) (V T) c) - (Γ₁ + Γφ) * T / 3| ≤
      ‖traceCLM‖ / 6 * (‖damping Γ₁ Γφ‖ * |T|)^2 := by
  rw [lindbladGateInfidelity_eq _ (qubit_nominal_unitary hU right_mem_uIcc)]
  have h := weak_dissipation_remainder
    (ux := ux) (uy := uy) (T := T) (Γ₁ := Γ₁) (Γφ := Γφ)
    (O := fun t => blochRotation (U 0 t)) (V := V)
    hT h₁ hφ (blochRotation_isACSolution hU 0) hV
  exact h

theorem damping_norm_le_rates {Γ₁ Γφ : ℝ} (h₁ : 0 ≤ Γ₁) (hφ : 0 ≤ Γφ) :
    ‖damping Γ₁ Γφ‖ ≤ Γ₁ + Γφ := by
  rw [damping, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (add_nonneg h₁ hφ)).mpr
  intro i
  fin_cases i
  · change |-(Γ₁ / 2 + Γφ)| ≤ Γ₁ + Γφ
    rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ Γ₁ / 2 + Γφ)]
    linarith
  · change |-(Γ₁ / 2 + Γφ)| ≤ Γ₁ + Γφ
    rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ Γ₁ / 2 + Γφ)]
    linarith
  · change |-Γ₁| ≤ Γ₁ + Γφ
    rw [abs_neg, abs_of_nonneg h₁]
    linarith

-- 显式得到论文O((ΓT)²)中的Γ=Γ₁+Γφ；系数与控制波形无关。
theorem weak_dissipation_rate_remainder
    {ux uy : ℝ → ℝ} {T Γ₁ Γφ : ℝ}
    {U : ℝ → ℝ → QubitMatrix} {V : ℝ → BlochMatrix}
    (hT : 0 ≤ T) (h₁ : 0 ≤ Γ₁) (hφ : 0 ≤ Γφ)
    (hU : IsQubitEvolution ux uy U T)
    (hV : IsACSolution
      (fun t => rotationGenerator (ux t) (uy t) 0 + damping Γ₁ Γφ) V T)
    (c : BlochVector) :
    |(1 - lindbladGateFidelity (U 0 T) (V T) c) - (Γ₁ + Γφ) * T / 3| ≤
      ‖traceCLM‖ / 6 * ((Γ₁ + Γφ) * T)^2 := by
  apply (weak_dissipation_state_remainder hT h₁ hφ hU hV c).trans
  rw [abs_of_nonneg hT]
  have hd := damping_norm_le_rates h₁ hφ
  gcongr

-- s²使用Mathlib真实方差，χ使用真实传播子保真度极限；κL保留论文规范。
theorem averaged_lindblad_budget
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {ux uy : ℝ → ℝ} {γ₁ γφ Ω T : ℝ}
    {U : ℝ → ℝ → QubitMatrix} {V : ℝ → ℝ → ℝ → BlochMatrix}
    (hT : 0 ≤ T) (hΩ : 0 < Ω) (h₁ : 0 ≤ γ₁) (hφ : 0 ≤ γφ)
    (hU : IsQubitEvolution ux uy U T)
    (hV : IsNoisyBlochEvolution ux uy γ₁ γφ V T)
    (hs : FrontierAverage.SymmetricLaw μ)
    (h4 : Integrable (fun x : ℝ => x^4) μ)
    (c : ℝ → ℝ → BlochVector) :
    (fun η => (∫ x, 1 - lindbladGateFidelity (U 0 T) (V η x T) (c η x) ∂μ) -
      (ProbabilityTheory.variance (fun x : ℝ => η*x) μ / Ω^2) * detuningSensitivity U Ω T -
      ((η^2*γ₁ + η^2*γφ) / (3*Ω)) * (Ω*T))
      =O[𝓝 (0 : ℝ)] (fun η => η^4) := by
  apply (averaged_lindblad_infidelity hT h₁ hφ hU hV hs h4 c).congr_left
  intro η
  rw [FrontierAverage.variance_scaled_of_symmetric_fourth hs h4 η,
    detuningSensitivity_eq hU Ω]
  field_simp [hΩ.ne']
  ring

-- 最终物理入口：同时交付原Lindblad初值问题与其实际门保真度平均预算。
theorem lindblad_weak_noise_budget
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {ux uy : ℝ → ℝ} {γ₁ γφ Ω T : ℝ}
    {U : ℝ → ℝ → QubitMatrix} {V : ℝ → ℝ → ℝ → BlochMatrix}
    {c : ℝ → ℝ → ℝ → BlochVector}
    (hT : 0 ≤ T) (hΩ : 0 < Ω) (h₁ : 0 ≤ γ₁) (hφ : 0 ≤ γφ)
    (hU : IsQubitEvolution ux uy U T)
    (hchannel : IsNoisyLindbladChannel ux uy γ₁ γφ V c T)
    (hs : FrontierAverage.SymmetricLaw μ)
    (h4 : Integrable (fun x : ℝ => x^4) μ) :
    (∀ η x q,
      lindbladOutput V c η x 0 q = density q ∧
      AbsolutelyContinuousOnInterval (fun t => lindbladOutput V c η x t q) 0 T ∧
      ∀ᵐ t, t ∈ uIcc 0 T →
        HasDerivAt (fun s => lindbladOutput V c η x s q)
          (lindblad (ux t) (uy t) (η*x) (η^2*γ₁) (η^2*γφ)
            (lindbladOutput V c η x t q)) t) ∧
    ((fun η => (∫ x, 1 - lindbladGateFidelity (U 0 T) (V η x T) (c η x T) ∂μ) -
      (ProbabilityTheory.variance (fun x : ℝ => η*x) μ / Ω^2) * detuningSensitivity U Ω T -
      ((η^2*γ₁ + η^2*γφ) / (3*Ω)) * (Ω*T))
      =O[𝓝 (0 : ℝ)] (fun η => η^4)) := by
  exact ⟨hchannel.original_ode,
    averaged_lindblad_budget hT hΩ h₁ hφ hU hchannel.homogeneous hs h4 (fun η x => c η x T)⟩

end
end RobustPiGate.FrontierNoise

#print axioms RobustPiGate.FrontierNoise.lindblad_weak_noise_budget
#print axioms RobustPiGate.FrontierNoise.weak_dissipation_rate_remainder
