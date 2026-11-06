import Mathlib

open scoped Matrix
open Real MeasureTheory

namespace RobustPiGate.FrontierSphere

noncomputable section

abbrev BlochVector := Fin 3 → ℝ
abbrev BlochMatrix := Matrix (Fin 3) (Fin 3) ℝ

-- 使用 z = cos θ 的等面积坐标；面积元为 dz dφ。
def spherePoint (z φ : ℝ) : BlochVector :=
  ![Real.sqrt (1 - z ^ 2) * Real.cos φ,
    Real.sqrt (1 - z ^ 2) * Real.sin φ, z]

def sphereAverage (f : BlochVector → ℝ) : ℝ :=
  (∫ z in (-1 : ℝ)..1, ∫ φ in 0..2 * Real.pi, f (spherePoint z φ)) /
    (4 * Real.pi)

theorem spherePoint_continuous :
    Continuous (fun p : ℝ × ℝ => spherePoint p.1 p.2) := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [spherePoint] <;> fun_prop

theorem spherePoint_unit {z : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) (φ : ℝ) :
    dotProduct (spherePoint z φ) (spherePoint z φ) = 1 := by
  have hs : Real.sqrt (1 - z ^ 2) ^ 2 = 1 - z ^ 2 :=
    Real.sq_sqrt (by nlinarith [hz.1, hz.2])
  simp only [dotProduct, Fin.sum_univ_succ, spherePoint, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
  calc
    _ = Real.sqrt (1 - z ^ 2) ^ 2 * (Real.sin φ ^ 2 + Real.cos φ ^ 2) + z ^ 2 := by ring
    _ = 1 := by rw [Real.sin_sq_add_cos_sq, hs]; ring

theorem cos_period_integral : (∫ φ in 0..2 * Real.pi, Real.cos φ) = 0 := by
  simp [integral_cos]

theorem sin_period_integral : (∫ φ in 0..2 * Real.pi, Real.sin φ) = 0 := by
  simp [integral_sin]

theorem cos_sq_period_integral : (∫ φ in 0..2 * Real.pi, Real.cos φ ^ 2) = Real.pi := by
  simp [integral_cos_sq]

theorem sin_sq_period_integral : (∫ φ in 0..2 * Real.pi, Real.sin φ ^ 2) = Real.pi := by
  simp [integral_sin_sq]

theorem sin_cos_period_integral :
    (∫ φ in 0..2 * Real.pi, Real.sin φ * Real.cos φ) = 0 := by
  simp [integral_sin_mul_cos₁]

theorem cos_sin_period_integral :
    (∫ φ in 0..2 * Real.pi, Real.cos φ * Real.sin φ) = 0 := by
  simpa only [mul_comm] using sin_cos_period_integral

theorem z_integral : (∫ z in (-1 : ℝ)..1, z) = 0 := by
  simp [integral_id]

theorem z_sq_integral : (∫ z in (-1 : ℝ)..1, z ^ 2) = 2 / 3 := by
  norm_num [integral_pow]

theorem radial_sq_integral : (∫ z in (-1 : ℝ)..1, 1 - z ^ 2) = 4 / 3 := by
  rw [intervalIntegral.integral_sub
    ((show Continuous (fun _ : ℝ => (1 : ℝ)) by fun_prop).intervalIntegrable _ _)
    ((show Continuous (fun z : ℝ => z ^ 2) by fun_prop).intervalIntegrable _ _), z_sq_integral]
  norm_num

theorem sphereAverage_const (a : ℝ) : sphereAverage (fun _ => a) = a := by
  simp only [sphereAverage, intervalIntegral.integral_const, smul_eq_mul]
  field_simp [Real.pi_ne_zero]
  ring

theorem sphereAverage_const_mul (a : ℝ) (f : BlochVector → ℝ) :
    sphereAverage (fun q => a * f q) = a * sphereAverage f := by
  simp only [sphereAverage, intervalIntegral.integral_const_mul]
  ring

theorem sphereAverage_add (f g : BlochVector → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    sphereAverage (fun q => f q + g q) = sphereAverage f + sphereAverage g := by
  have hfc : Continuous (Function.uncurry (fun z φ => f (spherePoint z φ))) :=
    hf.comp spherePoint_continuous
  have hgc : Continuous (Function.uncurry (fun z φ => g (spherePoint z φ))) :=
    hg.comp spherePoint_continuous
  have hfi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hfc 0
    (2 * Real.pi)
  have hgi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hgc 0
    (2 * Real.pi)
  unfold sphereAverage
  simp_rw [intervalIntegral.integral_add
    ((hfc.uncurry_left _).intervalIntegrable _ _)
    ((hgc.uncurry_left _).intervalIntegrable _ _)]
  rw [intervalIntegral.integral_add (hfi.intervalIntegrable _ _) (hgi.intervalIntegrable _ _)]
  ring

theorem sphereAverage_sum {ι : Type*} (s : Finset ι) (f : ι → BlochVector → ℝ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    sphereAverage (fun q => ∑ i ∈ s, f i q) = ∑ i ∈ s, sphereAverage (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sphereAverage_const]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [sphereAverage_add _ _ (hf a (Finset.mem_insert_self _ _))
      (continuous_finsetSum _ fun i hi => hf i (Finset.mem_insert_of_mem hi))]
    rw [ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem sphereAverage_coordinate (i : Fin 3) : sphereAverage (fun q => q i) = 0 := by
  fin_cases i
  · simp [sphereAverage, spherePoint, intervalIntegral.integral_const_mul]
  · simp [sphereAverage, spherePoint, intervalIntegral.integral_const_mul]
  · change (∫ z in (-1 : ℝ)..1, ∫ _φ in 0..2 * Real.pi, z) / (4 * Real.pi) = 0
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    rw [intervalIntegral.integral_const_mul, z_integral]
    simp

theorem azimuth_square (z : ℝ) (i : Fin 3) :
    (∫ φ in 0..2 * Real.pi, spherePoint z φ i ^ 2) =
      if i = 2 then 2 * Real.pi * z ^ 2 else
        Real.sqrt (1 - z ^ 2) ^ 2 * Real.pi := by
  fin_cases i
  · norm_num [spherePoint, mul_pow, intervalIntegral.integral_const_mul,
      cos_sq_period_integral]
  · norm_num [spherePoint, mul_pow, intervalIntegral.integral_const_mul,
      sin_sq_period_integral]
  · simp [spherePoint]

theorem sphereAverage_square (i : Fin 3) : sphereAverage (fun q => q i ^ 2) = 1 / 3 := by
  unfold sphereAverage
  simp_rw [azimuth_square]
  by_cases hi : i = 2
  · simp only [ite_eq_left hi, intervalIntegral.integral_const_mul, z_sq_integral]
    field_simp [Real.pi_ne_zero]
    ring
  · simp only [ite_eq_right hi]
    have heq : (∫ z in (-1 : ℝ)..1, Real.sqrt (1 - z ^ 2) ^ 2 * Real.pi) =
        ∫ z in (-1 : ℝ)..1, (1 - z ^ 2) * Real.pi := by
      apply intervalIntegral.integral_congr
      intro z hz
      rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hz
      change Real.sqrt (1 - z ^ 2) ^ 2 * Real.pi = (1 - z ^ 2) * Real.pi
      rw [Real.sq_sqrt (show 0 ≤ 1 - z ^ 2 by nlinarith [hz.1, hz.2])]
    rw [heq, intervalIntegral.integral_mul_const, radial_sq_integral]
    field_simp [Real.pi_ne_zero]

theorem azimuth_xy (z : ℝ) :
    (∫ φ in 0..2 * Real.pi, spherePoint z φ 0 * spherePoint z φ 1) = 0 := by
  have heq : (fun φ => spherePoint z φ 0 * spherePoint z φ 1) =
      fun φ => Real.sqrt (1 - z ^ 2) ^ 2 * (Real.cos φ * Real.sin φ) := by
    funext φ
    simp [spherePoint]
    ring
  rw [heq, intervalIntegral.integral_const_mul, cos_sin_period_integral, mul_zero]

theorem azimuth_xz (z : ℝ) :
    (∫ φ in 0..2 * Real.pi, spherePoint z φ 0 * spherePoint z φ 2) = 0 := by
  have heq : (fun φ => spherePoint z φ 0 * spherePoint z φ 2) =
      fun φ => (Real.sqrt (1 - z ^ 2) * z) * Real.cos φ := by
    funext φ
    simp [spherePoint]
    ring
  rw [heq, intervalIntegral.integral_const_mul, cos_period_integral, mul_zero]

theorem azimuth_yz (z : ℝ) :
    (∫ φ in 0..2 * Real.pi, spherePoint z φ 1 * spherePoint z φ 2) = 0 := by
  have heq : (fun φ => spherePoint z φ 1 * spherePoint z φ 2) =
      fun φ => (Real.sqrt (1 - z ^ 2) * z) * Real.sin φ := by
    funext φ
    simp [spherePoint]
    ring
  rw [heq, intervalIntegral.integral_const_mul, sin_period_integral, mul_zero]

theorem sphereAverage_xy : sphereAverage (fun q => q 0 * q 1) = 0 := by
  simp [sphereAverage, azimuth_xy]

theorem sphereAverage_xz : sphereAverage (fun q => q 0 * q 2) = 0 := by
  simp [sphereAverage, azimuth_xz]

theorem sphereAverage_yz : sphereAverage (fun q => q 1 * q 2) = 0 := by
  simp [sphereAverage, azimuth_yz]

theorem sphereAverage_product_comm (i j : Fin 3) :
    sphereAverage (fun q => q i * q j) = sphereAverage (fun q => q j * q i) := by
  congr 1
  funext q
  ring

theorem sphereAverage_second_moment (i j : Fin 3) :
    sphereAverage (fun q => q i * q j) = if i = j then 1 / 3 else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num
  · simpa only [sq] using sphereAverage_square 0
  · exact sphereAverage_xy
  · exact sphereAverage_xz
  · rw [sphereAverage_product_comm]; exact sphereAverage_xy
  · simpa only [sq] using sphereAverage_square 1
  · exact sphereAverage_yz
  · rw [sphereAverage_product_comm]; exact sphereAverage_xz
  · rw [sphereAverage_product_comm]; exact sphereAverage_yz
  · simpa only [sq] using sphereAverage_square 2

theorem sphereAverage_translation (c : BlochVector) :
    sphereAverage (fun q => dotProduct q c) = 0 := by
  have heq : (fun q => dotProduct q c) = fun q => ∑ i : Fin 3, c i * q i := by
    funext q
    simp only [dotProduct, mul_comm]
  rw [heq, sphereAverage_sum _ _ (by intros; fun_prop)]
  simp [sphereAverage_const_mul, sphereAverage_coordinate]

theorem sphereAverage_matrix_component (M : BlochMatrix) (i : Fin 3) :
    sphereAverage (fun q => q i * (M.mulVec q) i) = M i i / 3 := by
  have heq : (fun q => q i * (M.mulVec q) i) =
      fun q => ∑ j : Fin 3, M i j * (q i * q j) := by
    funext q
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq, sphereAverage_sum _ _ (by intros; fun_prop)]
  simp_rw [sphereAverage_const_mul, sphereAverage_second_moment]
  simp [mul_ite, div_eq_mul_inv]

theorem sphereAverage_homogeneous (M : BlochMatrix) :
    sphereAverage (fun q => dotProduct q (M.mulVec q)) = Matrix.trace M / 3 := by
  unfold dotProduct
  rw [sphereAverage_sum _ _ (by intro i _; unfold Matrix.mulVec dotProduct; fun_prop)]
  simp_rw [sphereAverage_matrix_component]
  simp [Matrix.trace, Matrix.diag, Finset.sum_div]

theorem sphereAverage_affine (M : BlochMatrix) (c : BlochVector) :
    sphereAverage (fun q => dotProduct q (M.mulVec q + c)) = Matrix.trace M / 3 := by
  have heq : (fun q => dotProduct q (M.mulVec q + c)) =
      fun q => dotProduct q (M.mulVec q) + dotProduct q c := by
    funext q
    simp [dotProduct, mul_add, Finset.sum_add_distrib]
  rw [heq, sphereAverage_add _ _ (by unfold Matrix.mulVec dotProduct; fun_prop)
    (by unfold dotProduct; fun_prop), sphereAverage_homogeneous, sphereAverage_translation,
    add_zero]

-- 单位纯态的点保真度经 061 的矩阵恒等式连接到此式。
theorem sphereAverage_fidelity (M : BlochMatrix) (c : BlochVector) :
    sphereAverage (fun q => (1 + dotProduct q (M.mulVec q + c)) / 2) =
      1 / 2 + Matrix.trace M / 6 := by
  have heq : (fun q => (1 + dotProduct q (M.mulVec q + c)) / 2) =
      fun q => (1 / 2 : ℝ) * (1 + dotProduct q (M.mulVec q + c)) := by
    funext q
    ring
  rw [heq, sphereAverage_const_mul,
    sphereAverage_add _ _ continuous_const (by unfold Matrix.mulVec dotProduct; fun_prop),
    sphereAverage_const, sphereAverage_affine]
  ring

theorem sphereAverage_congr_on_unit (f g : BlochVector → ℝ)
    (hfg : ∀ q, dotProduct q q = 1 → f q = g q) : sphereAverage f = sphereAverage g := by
  unfold sphereAverage
  congr 1
  apply intervalIntegral.integral_congr
  intro z hz
  rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hz
  apply intervalIntegral.integral_congr
  intro φ _
  exact hfg (spherePoint z φ) (spherePoint_unit hz φ)

theorem sphereAverage_fidelity_of_pure_state (M : BlochMatrix) (c : BlochVector)
    (f : BlochVector → ℝ)
    (hf : ∀ q, dotProduct q q = 1 → f q = (1 + dotProduct q (M.mulVec q + c)) / 2) :
    sphereAverage f = 1 / 2 + Matrix.trace M / 6 := by
  rw [sphereAverage_congr_on_unit f _ hf, sphereAverage_fidelity]

#print axioms sphereAverage_fidelity
#print axioms sphereAverage_fidelity_of_pure_state

end
end RobustPiGate.FrontierSphere
