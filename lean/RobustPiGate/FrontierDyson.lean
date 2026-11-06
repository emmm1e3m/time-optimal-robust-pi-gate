import RobustPiGate.Dynamics
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set Filter
open scoped Topology Interval

set_option maxHeartbeats 1200000

namespace RobustPiGate.FrontierDyson
open Dynamics
noncomputable section

section Volterra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def step (K f : ℝ → A) (t : ℝ) : A := ∫ s in 0..t, K s * f s

def iterate (K f : ℝ → A) : ℕ → ℝ → A
  | 0 => f
  | n + 1 => step K (iterate K f n)

def partialSum (K : ℝ → A) : ℕ → ℝ → A
  | 0 => fun _ => 0
  | n + 1 => fun t => 1 + step K (partialSum K n) t

def term (K : ℝ → A) (n : ℕ) : ℝ → A := iterate K (fun _ => 1) n

theorem continuousOn_step {K f : ℝ → A} {T : ℝ}
    (hK : ContinuousOn K (uIcc 0 T)) (hf : ContinuousOn f (uIcc 0 T)) :
    ContinuousOn (step K f) (uIcc 0 T) :=
  intervalIntegral.continuousOn_primitive_interval' (hK.mul hf).intervalIntegrable left_mem_uIcc

theorem continuousOn_iterate {K f : ℝ → A} {T : ℝ}
    (hK : ContinuousOn K (uIcc 0 T)) (hf : ContinuousOn f (uIcc 0 T)) (n : ℕ) :
    ContinuousOn (iterate K f n) (uIcc 0 T) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact continuousOn_step hK ih

theorem continuousOn_partial {K : ℝ → A} {T : ℝ}
    (hK : ContinuousOn K (uIcc 0 T)) (n : ℕ) :
    ContinuousOn (partialSum K n) (uIcc 0 T) := by
  induction n with
  | zero => exact continuousOn_const
  | succ n ih => exact continuousOn_const.add (continuousOn_step hK ih)

theorem step_sub {K f g : ℝ → A} {T t : ℝ}
    (hK : ContinuousOn K (uIcc 0 T)) (hf : ContinuousOn f (uIcc 0 T))
    (hg : ContinuousOn g (uIcc 0 T)) (ht : t ∈ uIcc 0 T) :
    step K (fun s => f s - g s) t = step K f t - step K g t := by
  simp only [step, mul_sub]
  exact intervalIntegral.integral_sub ((hK.mul hf).mono (uIcc_subset_uIcc_left ht)).intervalIntegrable
    ((hK.mul hg).mono (uIcc_subset_uIcc_left ht)).intervalIntegrable

theorem remainder_eq_iterate {K X : ℝ → A} {T : ℝ}
    (hK : ContinuousOn K (uIcc 0 T)) (hX : ContinuousOn X (uIcc 0 T))
    (hEq : ∀ t ∈ uIcc 0 T, X t = 1 + step K X t) (n : ℕ) :
    ∀ t ∈ uIcc 0 T, X t - partialSum K n t = iterate K X n t := by
  induction n with
  | zero => intro t ht; simp [partialSum, iterate]
  | succ n ih =>
    intro t ht
    change X t - (1 + step K (partialSum K n) t) = step K (iterate K X n) t
    calc
      _ = step K X t - step K (partialSum K n) t := by rw [hEq t ht]; abel
      _ = step K (fun s => X s - partialSum K n s) t :=
        (step_sub hK hX (continuousOn_partial hK n) ht).symm
      _ = step K (iterate K X n) t := by
        apply intervalIntegral.integral_congr
        intro s hs
        dsimp only
        rw [ih s (uIcc_subset_uIcc_left ht hs)]

theorem partial_eq_sum {K : ℝ → A} {T : ℝ}
    (hK : ContinuousOn K (uIcc 0 T)) (n : ℕ) :
    ∀ t ∈ uIcc 0 T, partialSum K n t = ∑ i ∈ Finset.range n, term K i t := by
  induction n with
  | zero => intro t ht; simp [partialSum]
  | succ n ih =>
    intro t ht
    change 1 + step K (partialSum K n) t = _
    have heq : step K (partialSum K n) t = ∑ i ∈ Finset.range n, term K (i+1) t := by
      unfold step
      calc
        _ = ∫ s in 0..t, ∑ i ∈ Finset.range n, K s * term K i s := by
          apply intervalIntegral.integral_congr
          intro s hs
          dsimp only
          rw [ih s (uIcc_subset_uIcc_left ht hs), Finset.mul_sum]
        _ = ∑ i ∈ Finset.range n, ∫ s in 0..t, K s * term K i s := by
          apply intervalIntegral.integral_finsetSum
          intro i hi
          exact ((hK.mul (continuousOn_iterate hK continuousOn_const i)).mono
            (uIcc_subset_uIcc_left ht)).intervalIntegrable
        _ = _ := rfl
    rw [heq, Finset.sum_range_succ']
    simp [term, iterate, add_comm]

-- 使用全区间一致界，故无需参数的小量假设或指数矩。
theorem norm_iterate_le {K f : ℝ → A} {T M C : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hK : ∀ t ∈ uIcc 0 T, ‖K t‖ ≤ M)
    (hf : ∀ t ∈ uIcc 0 T, ‖f t‖ ≤ C) (n : ℕ) :
    ∀ t ∈ uIcc 0 T, ‖iterate K f n t‖ ≤ C * (M * |T|)^n := by
  induction n with
  | zero => intro t ht; simpa [iterate] using hf t ht
  | succ n ih =>
    intro t ht
    have hb : ∀ s ∈ uIoc 0 t, ‖K s * iterate K f n s‖ ≤ M * (C * (M * |T|)^n) := by
      intro s hs
      have hsT := uIcc_subset_uIcc_left ht (uIoc_subset_uIcc hs)
      exact (norm_mul_le _ _).trans (mul_le_mul (hK s hsT) (ih s hsT) (norm_nonneg _) hM)
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
    have htabs : |t| ≤ |T| := by simpa using abs_sub_left_of_mem_uIcc ht
    calc
      ‖iterate K f (n+1) t‖ ≤ M * (C * (M * |T|)^n) * |t| := by simpa [iterate, step] using hi
      _ ≤ M * (C * (M * |T|)^n) * |T| := by gcongr
      _ = C * (M * |T|)^(n+1) := by ring

end Volterra

section Dynamics
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [StarRing A] [CStarRing A] [StarModule ℝ A] [IsDedekindFiniteMonoid A]

def kernel (U : ℝ → A) (E : A) (t : ℝ) : A := star (U t) * E * U t

def frame (U V : ℝ → A) (t : ℝ) : A := star (U t) * V t

theorem continuousOn_kernel {G U : ℝ → A} {T : ℝ}
    (hU : IsACSolution G U T) (E : A) :
    ContinuousOn (kernel U E) (uIcc 0 T) :=
  (hU.ac.continuousOn.star.mul_const E).mul hU.ac.continuousOn

theorem frame_volterra {G U V : ℝ → A} {E : A} {T : ℝ}
    (hU : IsACSolution G U T)
    (hV : IsACSolution (fun t => G t + E) V T)
    (hG : ∀ᵐ t, t ∈ uIcc 0 T → star (G t) = -G t) :
    ∀ t ∈ uIcc 0 T, frame U V t = 1 + step (kernel U E) (frame U V) t := by
  intro t ht
  have hV' : IsACSolution (fun s => G s + (1:ℝ) • E) V t := by simpa using hV.restrict ht
  have hd := duhamel_frame (hU.restrict ht) hV'
    (hG.mono fun s hs hsI => hs (uIcc_subset_uIcc_left ht hsI))
  have heq : step (kernel U E) (frame U V) t = ∫ s in 0..t, star (U s) * E * V s := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hu := hU.unitary hG (uIcc_subset_uIcc_left ht hs)
    change (star (U s) * E * U s) * (star (U s) * V s) = _
    calc
      _ = (star (U s) * E) * (U s * star (U s)) * V s := by noncomm_ring
      _ = _ := by rw [hu.2, mul_one]
  rw [heq]
  simpa only [one_smul, sub_eq_iff_eq_add, add_comm, frame] using hd

theorem norm_kernel {G U : ℝ → A} {E : A} {T t : ℝ}
    (hU : IsACSolution G U T)
    (hG : ∀ᵐ s, s ∈ uIcc 0 T → star (G s) = -G s) (ht : t ∈ uIcc 0 T) :
    ‖kernel U E t‖ = ‖E‖ := by
  have hu := hU.unitary hG ht
  have hs : star (U t) ∈ unitary A := by
    simpa only [Unitary.mem_iff, star_star] using And.intro hu.2 hu.1
  rw [kernel, CStarRing.norm_mul_mem_unitary _ hu, CStarRing.norm_mem_unitary_mul _ hs]

-- 任意阶截断；四阶余项由 n=4 直接得到，对任意实失谐一致成立。
theorem norm_dyson_remainder_le {G U V : ℝ → A} {E : A} {T C : ℝ}
    (hU : IsACSolution G U T)
    (hV : IsACSolution (fun t => G t + E) V T)
    (hG : ∀ᵐ t, t ∈ uIcc 0 T → star (G t) = -G t)
    (hVnorm : ∀ t ∈ uIcc 0 T, ‖V t‖ ≤ C) (n : ℕ) :
    ‖frame U V T - ∑ i ∈ Finset.range n, term (kernel U E) i T‖ ≤ C * (‖E‖ * |T|)^n := by
  have hK := continuousOn_kernel hU E
  have hX : ContinuousOn (frame U V) (uIcc 0 T) := hU.ac.continuousOn.star.mul hV.ac.continuousOn
  rw [← partial_eq_sum hK n T right_mem_uIcc,
    remainder_eq_iterate hK hX (frame_volterra hU hV hG) n T right_mem_uIcc]
  apply norm_iterate_le (norm_nonneg E) ((norm_nonneg (V 0)).trans (hVnorm 0 left_mem_uIcc))
    (fun t ht => (norm_kernel hU hG ht).le) _ n T right_mem_uIcc
  intro t ht
  have hu := hU.unitary hG ht
  have hs : star (U t) ∈ unitary A := by
    simpa only [Unitary.mem_iff, star_star] using And.intro hu.2 hu.1
  simpa only [frame, CStarRing.norm_mem_unitary_mul _ hs] using hVnorm t ht


-- 有序积分词保留所有时间顺序；不交换静态扰动与耗散生成元。
def word (U : ℝ → A) : List A → ℝ → A
  | [] => fun _ => 1
  | E :: es => step (kernel U E) (word U es)

theorem continuousOn_word {G U : ℝ → A} {T : ℝ}
    (hU : IsACSolution G U T) (es : List A) :
    ContinuousOn (word U es) (uIcc 0 T) := by
  induction es with
  | nil => exact continuousOn_const
  | cons E es ih => exact continuousOn_step (continuousOn_kernel hU E) ih

theorem term_eq_word (U : ℝ → A) (E : A) (n : ℕ) :
    term (kernel U E) n = word U (List.replicate n E) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [term, iterate, List.replicate_succ, word] using congrArg (step (kernel U E)) ih

theorem step_linear_right {G U f g : ℝ → A} {T t a b : ℝ} {E : A}
    (hU : IsACSolution G U T) (hf : ContinuousOn f (uIcc 0 T))
    (hg : ContinuousOn g (uIcc 0 T)) (ht : t ∈ uIcc 0 T) :
    step (kernel U E) (fun s => a • f s + b • g s) t =
      a • step (kernel U E) f t + b • step (kernel U E) g t := by
  have hi (F : ℝ → A) (hF : ContinuousOn F (uIcc 0 T)) (c : ℝ) :
      IntervalIntegrable (fun s => c • (kernel U E s * F s)) volume 0 t :=
    (((continuousOn_kernel hU E).mul hF).const_smul c).mono (uIcc_subset_uIcc_left ht) |>.intervalIntegrable
  simp only [step, mul_add, mul_smul_comm]
  rw [intervalIntegral.integral_add (hi f hf a) (hi g hg b)]
  simp only [intervalIntegral.integral_smul, kernel]

theorem step_linear_left {G U f : ℝ → A} {T t a b : ℝ} {B D : A}
    (hU : IsACSolution G U T) (hf : ContinuousOn f (uIcc 0 T))
    (ht : t ∈ uIcc 0 T) :
    step (kernel U (a • B + b • D)) f t =
      a • step (kernel U B) f t + b • step (kernel U D) f t := by
  have hi (E : A) (c : ℝ) :
      IntervalIntegrable (fun s => c • (kernel U E s * f s)) volume 0 t :=
    (((continuousOn_kernel hU E).mul hf).const_smul c).mono (uIcc_subset_uIcc_left ht) |>.intervalIntegrable
  simp only [step, kernel, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  change (∫ s in 0..t, a • (kernel U B s * f s) + b • (kernel U D s * f s)) = _
  rw [intervalIntegral.integral_add (hi B a) (hi D b)]
  simp only [intervalIntegral.integral_smul, kernel]

-- 每个积分槽都线性，因此下述展开对任意实参数成立。
theorem word_linear {G U : ℝ → A} {T t a b : ℝ} {B D : A}
    (hU : IsACSolution G U T) (xs ys : List A) (ht : t ∈ uIcc 0 T) :
    word U (xs ++ (a • B + b • D) :: ys) t =
      a • word U (xs ++ B :: ys) t + b • word U (xs ++ D :: ys) t := by
  induction xs generalizing t with
  | nil => exact step_linear_left hU (continuousOn_word hU ys) ht
  | cons E xs ih =>
    change step (kernel U E) (word U (xs ++ (a • B + b • D) :: ys)) t = _
    calc
      _ = step (kernel U E) (fun s =>
            a • word U (xs ++ B :: ys) s + b • word U (xs ++ D :: ys) s) t := by
        apply intervalIntegral.integral_congr
        intro s hs
        dsimp only
        rw [ih (uIcc_subset_uIcc_left ht hs)]
      _ = _ := step_linear_right hU (continuousOn_word hU _) (continuousOn_word hU _) ht

theorem term_one_expansion {G U : ℝ → A} {T t δ Γ : ℝ} {B D : A}
    (hU : IsACSolution G U T) (ht : t ∈ uIcc 0 T) :
    term (kernel U (δ • B + Γ • D)) 1 t =
      δ • word U [B] t + Γ • word U [D] t := by
  rw [term_eq_word]
  exact word_linear (a := δ) (b := Γ) (B := B) (D := D) hU [] [] ht

theorem term_two_expansion {G U : ℝ → A} {T t δ Γ : ℝ} {B D : A}
    (hU : IsACSolution G U T) (ht : t ∈ uIcc 0 T) :
    term (kernel U (δ • B + Γ • D)) 2 t =
      δ^2 • word U [B,B] t + (δ*Γ) • (word U [B,D] t + word U [D,B] t) +
        Γ^2 • word U [D,D] t := by
  rw [term_eq_word]
  change word U [δ • B + Γ • D, δ • B + Γ • D] t = _
  have h0 := word_linear (a := δ) (b := Γ) (B := B) (D := D) hU [] [δ • B + Γ • D] ht
  have h1 := word_linear (a := δ) (b := Γ) (B := B) (D := D) hU [B] [] ht
  have h2 := word_linear (a := δ) (b := Γ) (B := B) (D := D) hU [D] [] ht
  simp only [List.nil_append, List.cons_append] at h0 h1 h2
  rw [h0, h1, h2]
  module

theorem term_three_expansion {G U : ℝ → A} {T t δ Γ : ℝ} {B D : A}
    (hU : IsACSolution G U T) (ht : t ∈ uIcc 0 T) :
    term (kernel U (δ • B + Γ • D)) 3 t =
      δ^3 • word U [B,B,B] t +
      (δ^2*Γ) • (word U [B,B,D] t + word U [B,D,B] t + word U [D,B,B] t) +
      (δ*Γ^2) • (word U [B,D,D] t + word U [D,B,D] t + word U [D,D,B] t) +
      Γ^3 • word U [D,D,D] t := by
  rw [term_eq_word]
  let E := δ • B + Γ • D
  change word U [E,E,E] t = _
  have h0 := word_linear (a := δ) (b := Γ) (B := B) (D := D) hU [] [E,E] ht
  have h1 := word_linear (a := δ) (b := Γ) (B := B) (D := D) hU [B] [E] ht
  have h2 := word_linear (a := δ) (b := Γ) (B := B) (D := D) hU [D] [E] ht
  have h3 := word_linear (a := δ) (b := Γ) (B := B) (D := D) hU [B,B] [] ht
  have h4 := word_linear (a := δ) (b := Γ) (B := B) (D := D) hU [B,D] [] ht
  have h5 := word_linear (a := δ) (b := Γ) (B := B) (D := D) hU [D,B] [] ht
  have h6 := word_linear (a := δ) (b := Γ) (B := B) (D := D) hU [D,D] [] ht
  simp only [List.nil_append, List.cons_append] at h0 h1 h2 h3 h4 h5 h6
  dsimp [E] at *
  rw [h0, h1, h2, h3, h4, h5, h6]
  module

theorem norm_word_le [Nontrivial A] {G U : ℝ → A} {T : ℝ}
    (hU : IsACSolution G U T)
    (hG : ∀ᵐ t, t ∈ uIcc 0 T → star (G t) = -G t) (es : List A) :
    ∀ t ∈ uIcc 0 T, ‖word U es t‖ ≤ (es.map (fun E => ‖E‖ * |T|)).prod := by
  induction es with
  | nil => intro t ht; simpa [word] using (norm_one : ‖(1 : A)‖ = 1).le
  | cons E es ih =>
    intro t ht
    have hp : 0 ≤ (es.map (fun E => ‖E‖ * |T|)).prod := by
      apply List.prod_nonneg
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      positivity
    have h := norm_iterate_le (norm_nonneg E) hp
      (fun s hs => (norm_kernel hU hG hs).le) ih 1 t ht
    simpa [iterate, word, mul_comm] using h

-- 奇次失谐项集中到两个固定的有序积分系数。
def oddLinear (U : ℝ → A) (B D : A) (η t : ℝ) : A :=
  η • word U [B] t + η^3 • (word U [B,D] t + word U [D,B] t) +
    η^5 • (word U [B,D,D] t + word U [D,B,D] t + word U [D,D,B] t)

def oddCubic (U : ℝ → A) (B : A) (η t : ℝ) : A := η^3 • word U [B,B,B] t

def mixedApprox (U : ℝ → A) (B D : A) (η x t : ℝ) : A :=
  1 + η^2 • (x^2 • word U [B,B] t + word U [D] t) +
    x • oddLinear U B D η t + x^3 • oddCubic U B η t

def mixedEven (U : ℝ → A) (B D : A) (η x t : ℝ) : A :=
  η^4 • word U [D,D] t +
    (η^4*x^2) • (word U [B,B,D] t + word U [B,D,B] t + word U [D,B,B] t) +
    η^6 • word U [D,D,D] t

def mixedConstant (U : ℝ → A) (B D : A) (T C : ℝ) : ℝ :=
  8*C*((‖B‖+‖D‖)* |T|)^4 + ‖word U [D,D] T‖ +
    ‖word U [B,B,D] T + word U [B,D,B] T + word U [D,B,B] T‖ + ‖word U [D,D,D] T‖

theorem scaled_sum_expansion {G U : ℝ → A} {T t η x : ℝ} {B D : A}
    (hU : IsACSolution G U T) (ht : t ∈ uIcc 0 T) :
    (∑ i ∈ Finset.range 4, term (kernel U ((η*x) • B + η^2 • D)) i t) =
      mixedApprox U B D η x t + mixedEven U B D η x t := by
  have hz : term (kernel U ((η*x) • B + η^2 • D)) 0 t = 1 := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hz]
  rw [term_one_expansion hU ht, term_two_expansion hU ht, term_three_expansion hU ht]
  dsimp only [mixedApprox, mixedEven, oddLinear, oddCubic]
  module

theorem abs_pow_four (x : ℝ) : |x|^4 = x^4 := (by norm_num : Even (4 : ℕ)).pow_abs x

theorem norm_scaled_perturbation_four_le (B D : A) {η x T : ℝ} (hη : |η| ≤ 1) :
    (‖(η*x) • B + η^2 • D‖* |T|)^4 ≤
      8*((‖B‖+‖D‖)* |T|)^4 * η^4 * (1+x^4) := by
  have hηsq : η^2 ≤ |η| := by
    nlinarith [sq_abs η, mul_le_mul_of_nonneg_left hη (abs_nonneg η)]
  have he : ‖(η*x) • B + η^2 • D‖ ≤ |η| * ((|x|+1)*(‖B‖+‖D‖)) := by
    calc
      _ ≤ ‖(η*x) • B‖ + ‖η^2 • D‖ := norm_add_le _ _
      _ = |η| * |x| * ‖B‖ + η^2*‖D‖ := by simp [norm_smul, abs_mul, abs_of_nonneg (sq_nonneg η)]
      _ ≤ |η| * |x| * ‖B‖ + |η| * ‖D‖ := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (abs_nonneg η) (norm_nonneg B),
        mul_nonneg (abs_nonneg η) (mul_nonneg (abs_nonneg x) (norm_nonneg D))]
  have hx : (|x|+1)^4 ≤ 8*(1+x^4) := by
    have hp := add_pow_le (abs_nonneg x) (by norm_num : (0:ℝ) ≤ 1) 4
    norm_num [abs_pow_four] at hp
    linarith
  calc
    _ ≤ (|η| * ((|x|+1)*(‖B‖+‖D‖)) * |T|)^4 := by gcongr
    _ = |η|^4 * ((‖B‖+‖D‖)* |T|)^4 * (|x|+1)^4 := by ring
    _ ≤ |η|^4 * ((‖B‖+‖D‖)* |T|)^4 * (8*(1+x^4)) := by gcongr
    _ = _ := by rw [abs_pow_four]; ring

theorem norm_even_tail_le (a b c : A) {η x : ℝ} (hη : |η| ≤ 1) :
    ‖η^4 • a + (η^4*x^2) • b + η^6 • c‖ ≤
      (‖a‖+‖b‖+‖c‖) * η^4 * (1+x^4) := by
  have hηsq : η^2 ≤ 1 := by nlinarith [sq_abs η, abs_nonneg η]
  have hx : x^2 ≤ 1+x^4 := by nlinarith [sq_nonneg (x^2-1), sq_nonneg x]
  have hη6 : η^6 ≤ η^4 := by nlinarith [mul_le_mul_of_nonneg_left hηsq (by positivity : 0 ≤ η^4)]
  have h4 : 1 ≤ 1+x^4 := by nlinarith [sq_nonneg (x^2)]
  calc
    _ ≤ ‖η^4 • a‖ + ‖(η^4*x^2) • b‖ + ‖η^6 • c‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = η^4*‖a‖ + (η^4*x^2)*‖b‖ + η^6*‖c‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ η^4 by positivity),
        abs_of_nonneg (show 0 ≤ η^4*x^2 by positivity), abs_of_nonneg (show 0 ≤ η^6 by positivity)]
    _ ≤ η^4*‖a‖*(1+x^4) + η^4*‖b‖*(1+x^4) + η^4*‖c‖*(1+x^4) := by
      apply add_le_add
      · apply add_le_add
        · nlinarith [mul_nonneg (show 0 ≤ η^4*‖a‖ by positivity) (show 0 ≤ x^4 by positivity)]
        · calc
            _ = η^4*‖b‖*x^2 := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hx (by positivity)
      · calc
          _ ≤ η^4*‖c‖ := mul_le_mul_of_nonneg_right hη6 (norm_nonneg c)
          _ ≤ _ := le_mul_of_one_le_right (by positivity) h4
    _ = _ := by ring

-- 核心弱噪声界：x 无界，常数不依赖 η 或 x，只需 |η|≤1。
theorem norm_mixed_remainder_le {G U V : ℝ → A} {B D : A} {T C η x : ℝ}
    (hU : IsACSolution G U T)
    (hV : IsACSolution (fun t => G t + ((η*x) • B + η^2 • D)) V T)
    (hG : ∀ᵐ t, t ∈ uIcc 0 T → star (G t) = -G t)
    (hVnorm : ∀ t ∈ uIcc 0 T, ‖V t‖ ≤ C) (hη : |η| ≤ 1) :
    ‖frame U V T - mixedApprox U B D η x T‖ ≤
      mixedConstant U B D T C * η^4 * (1+x^4) := by
  have hC : 0 ≤ C := (norm_nonneg (V 0)).trans (hVnorm 0 left_mem_uIcc)
  have hd := norm_dyson_remainder_le hU hV hG hVnorm 4
  have hp := norm_scaled_perturbation_four_le B D (T := T) (x := x) hη
  have he := norm_even_tail_le (word U [D,D] T)
    (word U [B,B,D] T + word U [B,D,B] T + word U [D,B,B] T)
    (word U [D,D,D] T) (x := x) hη
  rw [scaled_sum_expansion hU right_mem_uIcc] at hd
  have hdecomp : frame U V T - mixedApprox U B D η x T =
      (frame U V T - (mixedApprox U B D η x T + mixedEven U B D η x T)) +
        mixedEven U B D η x T := by abel
  rw [hdecomp]
  calc
    _ ≤ ‖frame U V T - (mixedApprox U B D η x T + mixedEven U B D η x T)‖ +
          ‖mixedEven U B D η x T‖ := norm_add_le _ _
    _ ≤ C * (8*((‖B‖+‖D‖)* |T|)^4 * η^4 * (1+x^4)) +
        (‖word U [D,D] T‖ +
        ‖word U [B,B,D] T + word U [B,D,B] T + word U [D,B,B] T‖ +
        ‖word U [D,D,D] T‖) * η^4 * (1+x^4) :=
      add_le_add (hd.trans (mul_le_mul_of_nonneg_left hp hC)) he
    _ = _ := by dsimp only [mixedConstant]; ring

-- 连续线性读出后，直接形成对称分布平均层所需的 x、x³ 奇项接口。
theorem functional_mixed_remainder_le {G U V : ℝ → A} {B D : A} {T C η x : ℝ}
    (hU : IsACSolution G U T)
    (hV : IsACSolution (fun t => G t + ((η*x) • B + η^2 • D)) V T)
    (hG : ∀ᵐ t, t ∈ uIcc 0 T → star (G t) = -G t)
    (hVnorm : ∀ t ∈ uIcc 0 T, ‖V t‖ ≤ C) (hη : |η| ≤ 1) (L : A →L[ℝ] ℝ) :
    |L (frame U V T - 1) - η^2*(L (word U [B,B] T)*x^2 + L (word U [D] T)) -
      L (oddLinear U B D η T)*x - L (oddCubic U B η T)*x^3| ≤
      (‖L‖ * mixedConstant U B D T C) * η^4 * (1+x^4) := by
  have h := (L.le_opNorm (frame U V T - mixedApprox U B D η x T)).trans
    (mul_le_mul_of_nonneg_left (norm_mixed_remainder_le hU hV hG hVnorm hη) (norm_nonneg L))
  have heq : L (frame U V T - mixedApprox U B D η x T) =
      L (frame U V T - 1) - η^2*(L (word U [B,B] T)*x^2 + L (word U [D] T)) -
      L (oddLinear U B D η T)*x - L (oddCubic U B η T)*x^3 := by
    simp only [mixedApprox, map_sub, map_add, map_smul, smul_eq_mul]
    ring
  rw [heq, Real.norm_eq_abs] at h
  simpa only [mul_assoc] using h

end Dynamics
end
end RobustPiGate.FrontierDyson







