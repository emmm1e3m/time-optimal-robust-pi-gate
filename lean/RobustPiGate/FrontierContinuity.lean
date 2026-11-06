import RobustPiGate.FrontierDyson
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set Filter
open scoped Topology Interval

set_option maxHeartbeats 1200000

namespace RobustPiGate.FrontierContinuity
open Dynamics FrontierDyson
noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [StarRing A] [CStarRing A] [StarModule ℝ A] [IsDedekindFiniteMonoid A]

-- 原控制可以仅 a.e. 可导；绘景的连续核提升了绘景解的右可导性。
theorem frame_hasDerivWithinAt_right {G U V : ℝ → A} {E : A} {T t : ℝ}
    (hT : 0 ≤ T) (hU : IsACSolution G U T)
    (hV : IsACSolution (fun s => G s + E) V T)
    (hG : ∀ᵐ s, s ∈ uIcc 0 T → star (G s) = -G s)
    (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (frame U V) (kernel U E t * frame U V t) (Ici t) t := by
  have htI : t ∈ uIcc 0 T := by rw [uIcc_of_le hT]; exact ⟨ht.1, ht.2.le⟩
  have hXi : ContinuousOn (fun s => kernel U E s * frame U V s) (Icc 0 T) := by
    rw [← uIcc_of_le hT]
    exact (continuousOn_kernel hU E).mul (hU.ac.continuousOn.star.mul hV.ac.continuousOn)
  haveI : Fact (t ∈ Icc 0 T) := ⟨⟨ht.1, ht.2.le⟩⟩
  have hder : HasDerivWithinAt (fun b => ∫ s in 0..b, kernel U E s * frame U V s)
      (kernel U E t * frame U V t) (Icc 0 T) t := by
    apply intervalIntegral.integral_hasDerivWithinAt_right
      ((hXi.mono (uIcc_subset_Icc ⟨le_rfl, hT⟩ ⟨ht.1, ht.2.le⟩)).intervalIntegrable)
      (hXi.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t)
      (hXi t ⟨ht.1, ht.2.le⟩)
  have hd : HasDerivWithinAt (frame U V) (kernel U E t * frame U V t) (Icc 0 T) t := by
    apply (hder.const_add 1).congr
    · intro s hs
      exact frame_volterra hU hV hG s (by rwa [uIcc_of_le hT])
    · exact frame_volterra hU hV hG t htI
  exact hd.mono_of_mem_nhdsWithin
    (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1))

-- 对参考失谐固定的Grönwall估计；实际失谐可以任意大。
theorem norm_parameter_sub_le {G U V W : ℝ → A} {B D : A} {T C δ δ₀ : ℝ}
    (hT : 0 ≤ T) (hU : IsACSolution G U T)
    (hV : IsACSolution (fun t => G t + (δ • B + D)) V T)
    (hW : IsACSolution (fun t => G t + (δ₀ • B + D)) W T)
    (hG : ∀ᵐ t, t ∈ uIcc 0 T → star (G t) = -G t)
    (hVnorm : ∀ t ∈ uIcc 0 T, ‖V t‖ ≤ C) :
    ‖V T - W T‖ ≤ gronwallBound 0 ‖δ₀ • B + D‖ (|δ-δ₀| * ‖B‖ * C) T := by
  let X := frame U V
  let Y := frame U W
  let d := fun t => kernel U (δ • B + D) t * X t - kernel U (δ₀ • B + D) t * Y t
  have hcont : ContinuousOn (fun t => X t - Y t) (Icc 0 T) := by
    rw [← uIcc_of_le hT]
    exact (hU.ac.continuousOn.star.mul hV.ac.continuousOn).sub
      (hU.ac.continuousOn.star.mul hW.ac.continuousOn)
  have hder : ∀ t ∈ Ico 0 T, HasDerivWithinAt (fun s => X s - Y s) (d t) (Ici t) t := by
    intro t ht
    exact (frame_hasDerivWithinAt_right hT hU hV hG ht).sub
      (frame_hasDerivWithinAt_right hT hU hW hG ht)
  have hb : ∀ t ∈ Ico 0 T, ‖d t‖ ≤ ‖δ₀ • B + D‖ * ‖X t - Y t‖ + |δ-δ₀| * ‖B‖ * C := by
    intro t ht
    have htI : t ∈ uIcc 0 T := by rw [uIcc_of_le hT]; exact ⟨ht.1, ht.2.le⟩
    have hX : ‖X t‖ ≤ C := by
      have hu := hU.unitary hG htI
      have hs : star (U t) ∈ unitary A := by
        simpa only [Unitary.mem_iff, star_star] using And.intro hu.2 hu.1
      simpa only [X, frame, CStarRing.norm_mem_unitary_mul _ hs] using hVnorm t htI
    have hk : kernel U (δ • B + D) t = kernel U (δ₀ • B + D) t +
        (δ-δ₀) • kernel U B t := by
      simp only [kernel, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
      module
    have heq : d t = kernel U (δ₀ • B + D) t * (X t - Y t) +
        (δ-δ₀) • (kernel U B t * X t) := by
      dsimp only [d]
      rw [hk]
      simp only [add_mul, smul_mul_assoc, mul_sub]
      abel
    rw [heq]
    calc
      _ ≤ ‖kernel U (δ₀ • B + D) t * (X t - Y t)‖ + ‖(δ-δ₀) • (kernel U B t * X t)‖ := norm_add_le _ _
      _ ≤ ‖kernel U (δ₀ • B + D) t‖ * ‖X t-Y t‖ + |δ-δ₀| * (‖kernel U B t‖ * ‖X t‖) := by
        apply add_le_add (norm_mul_le _ _)
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (abs_nonneg _)
      _ = ‖δ₀ • B + D‖ * ‖X t-Y t‖ + |δ-δ₀| * ‖B‖ * ‖X t‖ := by
        rw [norm_kernel hU hG htI, norm_kernel hU hG htI]
        ring
      _ ≤ _ := by gcongr
  have hz : ‖X 0-Y 0‖ ≤ 0 := by simp [X, Y, frame, hU.initial, hV.initial, hW.initial]
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le hcont hder hz hb T ⟨hT, le_rfl⟩
  have hu := hU.unitary hG right_mem_uIcc
  have hs : star (U T) ∈ unitary A := by
    simpa only [Unitary.mem_iff, star_star] using And.intro hu.2 hu.1
  simpa only [X, Y, frame, ← mul_sub, CStarRing.norm_mem_unitary_mul _ hs, sub_zero] using hg

-- 真实解族本身给出参数连续性；没有加入可测性或连续依赖假设。
theorem continuous_parameter_solution {G U : ℝ → A} {V : ℝ → ℝ → A}
    {B D : A} {T C : ℝ}
    (hT : 0 ≤ T) (hU : IsACSolution G U T)
    (hV : ∀ δ, IsACSolution (fun t => G t + (δ • B + D)) (V δ) T)
    (hG : ∀ᵐ t, t ∈ uIcc 0 T → star (G t) = -G t)
    (hVnorm : ∀ δ t, t ∈ uIcc 0 T → ‖V δ t‖ ≤ C) :
    Continuous (fun δ => V δ T) := by
  rw [continuous_iff_continuousAt]
  intro δ₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have heps : Tendsto (fun δ : ℝ => |δ-δ₀| * ‖B‖ * C) (𝓝 δ₀) (𝓝 0) := by
    have hc : Continuous (fun δ : ℝ => |δ-δ₀| * ‖B‖ * C) := by fun_prop
    simpa using hc.tendsto δ₀
  have hg : Tendsto (fun δ : ℝ => gronwallBound 0 ‖δ₀ • B + D‖ (|δ-δ₀| * ‖B‖ * C) T)
      (𝓝 δ₀) (𝓝 0) := by
    simpa only [gronwallBound_ε0_δ0, Function.comp_def] using
      (gronwallBound_continuous_ε 0 ‖δ₀ • B + D‖ T).continuousAt.tendsto.comp heps
  exact squeeze_zero' (Filter.Eventually.of_forall fun δ => norm_nonneg _)
    (Filter.Eventually.of_forall fun δ => norm_parameter_sub_le hT hU (hV δ) (hV δ₀) hG (hVnorm δ)) hg

theorem continuous_parameter_readout {G U : ℝ → A} {V : ℝ → ℝ → A}
    {B D : A} {T C : ℝ}
    (hT : 0 ≤ T) (hU : IsACSolution G U T)
    (hV : ∀ δ, IsACSolution (fun t => G t + (δ • B + D)) (V δ) T)
    (hG : ∀ᵐ t, t ∈ uIcc 0 T → star (G t) = -G t)
    (hVnorm : ∀ δ t, t ∈ uIcc 0 T → ‖V δ t‖ ≤ C) (L : A →L[ℝ] ℝ) (η : ℝ) :
    Continuous (fun x => L (frame U (V (η*x)) T - 1)) := by
  have hv := (continuous_parameter_solution hT hU hV hG hVnorm).comp
    (continuous_const.mul continuous_id : Continuous (fun x : ℝ => η*x))
  exact L.continuous.comp ((continuous_const.mul hv).sub continuous_const)

theorem measurable_parameter_readout {G U : ℝ → A} {V : ℝ → ℝ → A}
    {B D : A} {T C : ℝ}
    (hT : 0 ≤ T) (hU : IsACSolution G U T)
    (hV : ∀ δ, IsACSolution (fun t => G t + (δ • B + D)) (V δ) T)
    (hG : ∀ᵐ t, t ∈ uIcc 0 T → star (G t) = -G t)
    (hVnorm : ∀ δ t, t ∈ uIcc 0 T → ‖V δ t‖ ≤ C) (L : A →L[ℝ] ℝ) (η : ℝ) :
    Measurable (fun x => L (frame U (V (η*x)) T - 1)) :=
  (continuous_parameter_readout hT hU hV hG hVnorm L η).measurable

-- 有限测度下由真实收缩得到常数支配，因此可积性也不需要另作假设。
theorem integrable_parameter_readout {G U : ℝ → A} {V : ℝ → ℝ → A}
    {B D : A} {T C : ℝ}
    (hT : 0 ≤ T) (hU : IsACSolution G U T)
    (hV : ∀ δ, IsACSolution (fun t => G t + (δ • B + D)) (V δ) T)
    (hG : ∀ᵐ t, t ∈ uIcc 0 T → star (G t) = -G t)
    (hVnorm : ∀ δ t, t ∈ uIcc 0 T → ‖V δ t‖ ≤ C) (L : A →L[ℝ] ℝ) (η : ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (fun x => L (frame U (V (η*x)) T - 1)) μ := by
  have hu := hU.unitary hG right_mem_uIcc
  have hs : star (U T) ∈ unitary A := by
    simpa only [Unitary.mem_iff, star_star] using And.intro hu.2 hu.1
  have hb : ∀ x : ℝ, ‖L (frame U (V (η*x)) T - 1)‖ ≤ ‖L‖*(C+‖(1:A)‖) := by
    intro x
    have hframe : ‖frame U (V (η*x)) T‖ ≤ C := by
      simpa only [frame, CStarRing.norm_mem_unitary_mul _ hs] using hVnorm (η*x) T right_mem_uIcc
    calc
      _ ≤ ‖L‖ * ‖frame U (V (η*x)) T - 1‖ := L.le_opNorm _
      _ ≤ ‖L‖ * (‖frame U (V (η*x)) T‖ + ‖(1:A)‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg L)
      _ ≤ _ := by gcongr
  exact (integrable_const (‖L‖*(C+‖(1:A)‖))).mono'
    (continuous_parameter_readout hT hU hV hG hVnorm L η).aestronglyMeasurable
    (Filter.Eventually.of_forall hb)

end
end RobustPiGate.FrontierContinuity



