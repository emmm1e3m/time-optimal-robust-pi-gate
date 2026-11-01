import RobustPiGate.Quantum
import RobustPiGate.ACCalculus

open MeasureTheory Set Filter
open scoped Matrix ComplexConjugate Matrix.Norms.L2Operator Topology Interval

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace RobustPiGate.Quantum
noncomputable section

/-- 同一个噪声方向的两个酉提升，其相对矩阵与 σz 对易。 -/
theorem relative_commutes_sigmaZ (U V : QubitMatrix)
    (hU : U ∈ unitary QubitMatrix) (hV : V ∈ unitary QubitMatrix)
    (hnoise : star U * sigmaZ * U = star V * sigmaZ * V) :
    sigmaZ * (U * star V) = (U * star V) * sigmaZ := by
  calc
    _ = (U * star U) * sigmaZ * (U * star V) := by rw [hU.2]; simp
    _ = U * (star U * sigmaZ * U) * star V := by noncomm_ring
    _ = U * (star V * sigmaZ * V) * star V := by rw [hnoise]
    _ = (U * star V) * sigmaZ * (V * star V) := by noncomm_ring
    _ = _ := by rw [hV.2]; simp

/-- σz 的两个不同本征值强迫其交换子中的非对角元消失。 -/
theorem offdiag_zero_of_commutes_sigmaZ {W : QubitMatrix}
    (hW : sigmaZ * W = W * sigmaZ) : W 0 1 = 0 ∧ W 1 0 = 0 := by
  have h01 := congrArg (fun M : QubitMatrix => M 0 1) hW
  have h10 := congrArg (fun M : QubitMatrix => M 1 0) hW
  simp [sigmaZ, Matrix.mul_apply, Fin.sum_univ_two] at h01 h10
  constructor
  · linear_combination (1 / 2 : ℂ) * h01
  · linear_combination (-1 / 2 : ℂ) * h10

/-- 相对导数同时对角和由横向生成元产生时，整个导数为零。 -/
theorem relative_derivative_zero (W D G K : QubitMatrix)
    (hW : sigmaZ * W = W * sigmaZ) (hD : sigmaZ * D = D * sigmaZ)
    (hG : ∀ i, G i i = 0) (hK : ∀ i, K i i = 0)
    (heq : D = G * W - W * K) : D = 0 := by
  obtain ⟨hW01, hW10⟩ := offdiag_zero_of_commutes_sigmaZ hW
  obtain ⟨hD01, hD10⟩ := offdiag_zero_of_commutes_sigmaZ hD
  ext i j
  fin_cases i <;> fin_cases j
  · have hh := congrArg (fun M : QubitMatrix => M 0 0) heq
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hW01, hW10, hG, hK] using hh
  · exact hD01
  · exact hD10
  · have hh := congrArg (fun M : QubitMatrix => M 1 1) heq
    simpa [Matrix.mul_apply, Fin.sum_univ_two, hW01, hW10, hG, hK] using hh

private theorem eqOn_eventuallyEq_Ioo {f g : ℝ → QubitMatrix} {a b t : ℝ}
    (heq : EqOn f g (Icc a b)) (ht : t ∈ Ioo a b) : f =ᶠ[𝓝 t] g := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact heq ⟨hs.1.le, hs.2.le⟩

/-- 从原矩阵 ODE、局部同噪声恒等式和横向约束推导相对矩阵的零导数。 -/
theorem relative_hasDerivAt_zero
    {U V : ℝ → QubitMatrix} {G K : QubitMatrix} {a b t : ℝ}
    (ht : t ∈ Ioo a b)
    (hU : ∀ s ∈ Icc a b, U s ∈ unitary QubitMatrix)
    (hV : ∀ s ∈ Icc a b, V s ∈ unitary QubitMatrix)
    (hnoise : ∀ s ∈ Icc a b, star (U s) * sigmaZ * U s = star (V s) * sigmaZ * V s)
    (hdU : HasDerivAt U (G * U t) t) (hdV : HasDerivAt V (K * V t) t)
    (hG : ∀ i, G i i = 0) (hK : ∀ i, K i i = 0) :
    HasDerivAt (fun s => U s * star (V s)) 0 t := by
  let W : ℝ → QubitMatrix := fun s => U s * star (V s)
  let D : QubitMatrix := (G * U t) * star (V t) + U t * star (K * V t)
  have hdW : HasDerivAt W D t := hdU.mul hdV.star
  have htcc : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  have hW : ∀ s ∈ Icc a b, sigmaZ * W s = W s * sigmaZ := by
    intro s hs
    exact relative_commutes_sigmaZ (U s) (V s) (hU s hs) (hV s hs) (hnoise s hs)
  have hDeq : sigmaZ * D = D * sigmaZ := by
    have heq : (fun s => sigmaZ * W s) =ᶠ[𝓝 t] (fun s => W s * sigmaZ) :=
      eqOn_eventuallyEq_Ioo hW ht
    exact (hdW.const_mul sigmaZ).unique
      ((hdW.mul_const sigmaZ).congr_of_eventuallyEq heq)
  have hUV : EqOn U (fun s => W s * V s) (Icc a b) := by
    intro s hs
    dsimp [W]
    rw [mul_assoc, (hV s hs).1, mul_one]
  have hderiv : G * U t = D * V t + W t * (K * V t) :=
    hdU.unique ((hdW.mul hdV).congr_of_eventuallyEq (eqOn_eventuallyEq_Ioo hUV ht))
  have hprod := congrArg (fun M : QubitMatrix => M * star (V t)) hderiv
  have hprod' : G * W t = D + W t * K := by
    simpa only [add_mul, mul_assoc, (hV t htcc).2, mul_one] using hprod
  have heqD : D = G * W t - W t * K := (eq_sub_iff_add_eq).2 hprod'.symm
  have hz : D = 0 := relative_derivative_zero (W t) D G K (hW t htcc) hDeq hG hK heqD
  exact hdW.congr_deriv hz

/-- 完整 AC 横向提升唯一性；生成元和路径均无连续可微假设。 -/
theorem transverse_lift_unique
    {U V G K : ℝ → QubitMatrix} {a b : ℝ} (hab : a < b)
    (hUac : AbsolutelyContinuousOnInterval U a b)
    (hVac : AbsolutelyContinuousOnInterval V a b)
    (hU : ∀ t ∈ Icc a b, U t ∈ unitary QubitMatrix)
    (hV : ∀ t ∈ Icc a b, V t ∈ unitary QubitMatrix)
    (hnoise : ∀ t ∈ Icc a b, star (U t) * sigmaZ * U t = star (V t) * sigmaZ * V t)
    (hdU : ∀ᵐ t, t ∈ Icc a b → HasDerivAt U (G t * U t) t)
    (hdV : ∀ᵐ t, t ∈ Icc a b → HasDerivAt V (K t * V t) t)
    (hG : ∀ᵐ t, t ∈ Icc a b → ∀ i, G t i i = 0)
    (hK : ∀ᵐ t, t ∈ Icc a b → ∀ i, K t i i = 0)
    (hinit : U a = V a) : EqOn U V (Icc a b) := by
  let W : ℝ → QubitMatrix := fun t => U t * star (V t)
  have hVstar : AbsolutelyContinuousOnInterval (fun t => star (V t)) a b :=
    star_isometry.lipschitzWith.comp_absolutelyContinuousOnInterval hVac
  have hWac : AbsolutelyContinuousOnInterval W a b := Dynamics.ac_mul hUac hVstar
  have hdW : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt W 0 t := by
    filter_upwards [hdU, hdV, hG, hK, volume.ae_ne a, volume.ae_ne b]
      with t hut hvt hgt hkt hta htb ht
    rw [uIcc_of_le hab.le] at ht
    apply relative_hasDerivAt_zero (a := a) (b := b)
      (show t ∈ Ioo a b by constructor <;> rcases ht with ⟨ha, hb⟩ <;> order)
      hU hV hnoise (hut ht) (hvt ht) (hgt ht) (hkt ht)
  have hWa : W a = 1 := by
    dsimp [W]
    rw [hinit, (hV a ⟨le_rfl, hab.le⟩).2]
  intro t ht
  have ht' : t ∈ uIcc a b := by rwa [uIcc_of_le hab.le]
  have hsub : uIcc a t ⊆ uIcc a b := uIcc_subset_uIcc_left ht'
  have hWt : W t = 1 := by
    rw [← hWa]
    exact Dynamics.eq_of_ac_ae_deriv_zero (hWac.mono hsub)
      (hdW.mono fun s hs hst => hs (hsub hst))
  have he := congrArg (fun M : QubitMatrix => M * V t) hWt
  simpa only [W, mul_assoc, (hV t ht).1, mul_one, one_mul] using he

/-- 相同提升的原 ODE 再迫使两个横向生成元几乎处处相同。 -/
theorem generators_eq_ae_of_lift_eq
    {U V G K : ℝ → QubitMatrix} {a b : ℝ}
    (hV : ∀ t ∈ Icc a b, V t ∈ unitary QubitMatrix)
    (heq : EqOn U V (Icc a b))
    (hdU : ∀ᵐ t, t ∈ Icc a b → HasDerivAt U (G t * U t) t)
    (hdV : ∀ᵐ t, t ∈ Icc a b → HasDerivAt V (K t * V t) t) :
    ∀ᵐ t, t ∈ Icc a b → G t = K t := by
  filter_upwards [hdU, hdV, volume.ae_ne a, volume.ae_ne b] with t hut hvt hta htb ht
  have htoo : t ∈ Ioo a b := by constructor <;> rcases ht with ⟨ha, hb⟩ <;> order
  have hderiv := (hut ht).unique ((hvt ht).congr_of_eventuallyEq
    (eqOn_eventuallyEq_Ioo heq htoo))
  rw [heq ht] at hderiv
  have hh := congrArg (fun M : QubitMatrix => M * star (V t)) hderiv
  simpa only [mul_assoc, (hV t ht).2, mul_one] using hh

/-- 以薛定谔方程的实际 `-i H U` 形式陈述提升与哈密顿量唯一性。 -/
theorem hamiltonian_lift_unique
    {U V H K : ℝ → QubitMatrix} {a b : ℝ} (hab : a < b)
    (hUac : AbsolutelyContinuousOnInterval U a b)
    (hVac : AbsolutelyContinuousOnInterval V a b)
    (hU : ∀ t ∈ Icc a b, U t ∈ unitary QubitMatrix)
    (hV : ∀ t ∈ Icc a b, V t ∈ unitary QubitMatrix)
    (hnoise : ∀ t ∈ Icc a b, star (U t) * sigmaZ * U t = star (V t) * sigmaZ * V t)
    (hdU : ∀ᵐ t, t ∈ Icc a b → HasDerivAt U ((-Complex.I) • (H t * U t)) t)
    (hdV : ∀ᵐ t, t ∈ Icc a b → HasDerivAt V ((-Complex.I) • (K t * V t)) t)
    (hH : ∀ᵐ t, t ∈ Icc a b → ∀ i, H t i i = 0)
    (hK : ∀ᵐ t, t ∈ Icc a b → ∀ i, K t i i = 0)
    (hinit : U a = V a) :
    EqOn U V (Icc a b) ∧ (∀ᵐ t, t ∈ Icc a b → H t = K t) := by
  let G : ℝ → QubitMatrix := fun t => (-Complex.I) • H t
  let J : ℝ → QubitMatrix := fun t => (-Complex.I) • K t
  have hdG : ∀ᵐ t, t ∈ Icc a b → HasDerivAt U (G t * U t) t := by
    simpa only [G, smul_mul_assoc] using hdU
  have hdJ : ∀ᵐ t, t ∈ Icc a b → HasDerivAt V (J t * V t) t := by
    simpa only [J, smul_mul_assoc] using hdV
  have hG : ∀ᵐ t, t ∈ Icc a b → ∀ i, G t i i = 0 := by
    filter_upwards [hH] with t ht htI i
    simp [G, ht htI i]
  have hJ : ∀ᵐ t, t ∈ Icc a b → ∀ i, J t i i = 0 := by
    filter_upwards [hK] with t ht htI i
    simp [J, ht htI i]
  have heq := transverse_lift_unique hab hUac hVac hU hV hnoise hdG hdJ hG hJ hinit
  refine ⟨heq, ?_⟩
  filter_upwards [generators_eq_ae_of_lift_eq hV heq hdG hdJ] with t ht htI
  exact smul_right_injective QubitMatrix (by simp : -Complex.I ≠ 0) (ht htI)

/-- 原始两个实横向控制由同噪声曲线与同初值唯一确定，允许可测切换。 -/
theorem transverse_controls_unique
    {U V : ℝ → QubitMatrix} {ux uy vx vy : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hUac : AbsolutelyContinuousOnInterval U a b)
    (hVac : AbsolutelyContinuousOnInterval V a b)
    (hU : ∀ t ∈ Icc a b, U t ∈ unitary QubitMatrix)
    (hV : ∀ t ∈ Icc a b, V t ∈ unitary QubitMatrix)
    (hnoise : ∀ t ∈ Icc a b, star (U t) * sigmaZ * U t = star (V t) * sigmaZ * V t)
    (hdU : ∀ᵐ t, t ∈ Icc a b →
      HasDerivAt U ((-Complex.I / 2) • (pauli (ux t) (uy t) 0 * U t)) t)
    (hdV : ∀ᵐ t, t ∈ Icc a b →
      HasDerivAt V ((-Complex.I / 2) • (pauli (vx t) (vy t) 0 * V t)) t)
    (hinit : U a = V a) :
    EqOn U V (Icc a b) ∧ (∀ᵐ t, t ∈ Icc a b → ux t = vx t ∧ uy t = vy t) := by
  let G : ℝ → QubitMatrix := fun t => (-Complex.I / 2) • pauli (ux t) (uy t) 0
  let K : ℝ → QubitMatrix := fun t => (-Complex.I / 2) • pauli (vx t) (vy t) 0
  have hdG : ∀ᵐ t, t ∈ Icc a b → HasDerivAt U (G t * U t) t := by
    simpa only [G, smul_mul_assoc] using hdU
  have hdK : ∀ᵐ t, t ∈ Icc a b → HasDerivAt V (K t * V t) t := by
    simpa only [K, smul_mul_assoc] using hdV
  have hG : ∀ᵐ t, t ∈ Icc a b → ∀ i, G t i i = 0 := by
    apply Filter.Eventually.of_forall
    intro t _ i
    fin_cases i <;> simp [G, pauli]
  have hK : ∀ᵐ t, t ∈ Icc a b → ∀ i, K t i i = 0 := by
    apply Filter.Eventually.of_forall
    intro t _ i
    fin_cases i <;> simp [K, pauli]
  have heq := transverse_lift_unique hab hUac hVac hU hV hnoise hdG hdK hG hK hinit
  refine ⟨heq, ?_⟩
  filter_upwards [generators_eq_ae_of_lift_eq hV heq hdG hdK] with t ht htI
  have hpauli : pauli (ux t) (uy t) 0 = pauli (vx t) (vy t) 0 :=
    smul_right_injective QubitMatrix (by simp : -Complex.I / 2 ≠ 0) (ht htI)
  obtain ⟨hx, hy, _⟩ := pauli_injective hpauli
  exact ⟨hx, hy⟩

/-- 固定终门为 ±Rx(π) 时，横向旋转轴只能为 ±ex。 -/
theorem terminal_axis_unique {ax ay : ℝ}
    (hgate : Complex.I • pauli ax ay 0 = rx Real.pi ∨
      Complex.I • pauli ax ay 0 = -rx Real.pi) :
    (ax = 1 ∧ ay = 0) ∨ (ax = -1 ∧ ay = 0) := by
  rcases hgate with hgate | hgate
  · have hx := congrArg (fun M : QubitMatrix => (M 0 1).im) hgate
    have hy := congrArg (fun M : QubitMatrix => (M 0 1).re) hgate
    simp [pauli, rx] at hx hy
    exact Or.inr ⟨hx, hy⟩
  · have hx := congrArg (fun M : QubitMatrix => (M 0 1).im) hgate
    have hy := congrArg (fun M : QubitMatrix => (M 0 1).re) hgate
    simp [pauli, rx] at hx hy
    exact Or.inl ⟨hx, hy⟩

end
end RobustPiGate.Quantum

#print axioms RobustPiGate.Quantum.relative_hasDerivAt_zero
#print axioms RobustPiGate.Quantum.hamiltonian_lift_unique
#print axioms RobustPiGate.Quantum.transverse_controls_unique
#print axioms RobustPiGate.Quantum.terminal_axis_unique

