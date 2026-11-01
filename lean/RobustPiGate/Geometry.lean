import RobustPiGate.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

noncomputable section
open Real Set MeasureTheory InnerProductGeometry
open scoped InnerProductSpace

namespace RobustPiGate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- 单位向量在另一单位向量正交补上的投影长度。 -/
theorem norm_perp_eq_sin_angle {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x - (Real.cos (angle x y)) • y‖ = Real.sin (angle x y) := by
  have hi := inner_eq_cos_angle_of_norm_eq_one hx hy
  have hsq : ‖x - (Real.cos (angle x y)) • y‖ ^ 2 = Real.sin (angle x y) ^ 2 := by
    rw [norm_sub_pow_two_real]
    simp only [hx, norm_smul, Real.norm_eq_abs, hy, mul_one,
      real_inner_smul_right, hi, sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq (angle x y)]
  nlinarith [norm_nonneg (x - Real.cos (angle x y) • y), sin_angle_nonneg x y]

/-- 单位球面上无向角满足三角不等式。 -/
theorem angle_triangle_unit {x y z : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    angle x z ≤ angle x y + angle y z := by
  exact angle_le_angle_add_angle x y z

/-- 弦长和半角正弦的恒等式。 -/
theorem norm_sub_eq_two_sin_half_angle {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x - y‖ = 2 * Real.sin (angle x y / 2) := by
  have hnorm := norm_sub_pow_two_real x y
  rw [hx, hy, inner_eq_cos_angle_of_norm_eq_one hx hy] at hnorm
  have hsin := Real.sin_sq_eq_half_sub (angle x y / 2)
  rw [show 2 * (angle x y / 2) = angle x y by ring] at hsin
  have hp : 0 ≤ Real.sin (angle x y / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [angle_nonneg x y])
      (by linarith [angle_le_pi x y, Real.pi_pos])
  nlinarith [norm_nonneg (x - y)]

/-- 球面角距离与弦长的粗比较。 -/
theorem angle_le_pi_div_two_mul_norm_sub {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    angle x y ≤ Real.pi / 2 * ‖x - y‖ := by
  rw [norm_sub_eq_two_sin_half_angle hx hy]
  have h := Real.mul_le_sin (x := angle x y / 2) (by linarith [angle_nonneg x y])
    (by linarith [angle_le_pi x y])
  have hp := Real.pi_pos
  field_simp at h
  nlinarith

/-- 弦长比较的二阶余项；细分后此余项趋于零。 -/
theorem angle_le_norm_sub_add_sq {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    angle x y ≤ ‖x - y‖ + Real.pi ^ 2 * ‖x - y‖ ^ 2 := by
  let θ := angle x y
  let d := ‖x - y‖
  have hθ : 0 ≤ θ := angle_nonneg _ _
  have hd : 0 ≤ d := norm_nonneg _
  have hupper : θ ≤ Real.pi := angle_le_pi _ _
  have hcrude : θ ≤ Real.pi / 2 * d := angle_le_pi_div_two_mul_norm_sub hx hy
  have hchord : d = 2 * Real.sin (θ / 2) := norm_sub_eq_two_sin_half_angle hx hy
  have htaylor := Real.sin_ge_sub_cube (x := θ / 2) (by positivity)
  have hsmall : θ ≤ 4 := hupper.trans (le_of_lt Real.pi_lt_four)
  have hcube : θ ^ 3 ≤ 4 * θ ^ 2 := by nlinarith [sq_nonneg θ, mul_nonneg (sq_nonneg θ) (sub_nonneg.mpr hsmall)]
  have hsquare : θ ^ 2 ≤ (Real.pi / 2 * d) ^ 2 := pow_le_pow_left₀ hθ hcrude 2
  change θ ≤ d + Real.pi ^ 2 * d ^ 2
  nlinarith [sq_nonneg d, Real.pi_pos]

/-- 路径在球面角距离下的单位 Lipschitz 条件；此条件区别于弦长条件。 -/
def SphericalSpeedBound (n : ℝ → E) (a b : ℝ) : Prop :=
  ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, angle (n s) (n t) ≤ |t - s|

/-- 欧氏弦长的单位 Lipschitz 条件。 -/
def EuclideanSpeedBound (n : ℝ → E) (a b : ℝ) : Prop :=
  ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖n s - n t‖ ≤ |t - s|

/-- 等分曲线并累加角距离，得到余项随分段数衰减的估计。 -/
theorem angle_le_partition_bound {n : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hunit : ∀ t ∈ Icc a b, ‖n t‖ = 1)
    (hspeed : EuclideanSpeedBound n a b) (N : ℕ) (hN : 0 < N) :
    angle (n a) (n b) ≤ b - a + Real.pi ^ 2 * (b - a) ^ 2 / N := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let h : ℝ := (b - a) / N
  have hh : 0 ≤ h := div_nonneg (sub_nonneg.mpr hab) hNr.le
  have hNh : (N : ℝ) * h = b - a := by dsimp [h]; field_simp
  have hmem (k : ℕ) (hk : k ≤ N) : a + k * h ∈ Icc a b := by
    have hkr : (k : ℝ) ≤ N := Nat.cast_le.mpr hk
    constructor
    · linarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hh]
    · nlinarith [mul_le_mul_of_nonneg_right hkr hh]
  have hleft : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbase : n a ≠ 0 := by
    intro hz
    have := hunit a hleft
    simp [hz] at this
  have hchain : ∀ k : ℕ, k ≤ N →
      angle (n a) (n (a + k * h)) ≤ (k : ℝ) * (h + Real.pi ^ 2 * h ^ 2) := by
    intro k
    induction k with
    | zero => simp [angle_self hbase]
    | succ k ih =>
      intro hk
      have hk' : k ≤ N := (Nat.le_succ k).trans hk
      have htri := angle_triangle_unit (hunit a hleft) (hunit _ (hmem k hk'))
        (hunit _ (hmem (k + 1) hk))
      have hchord := hspeed _ (hmem k hk') _ (hmem (k + 1) hk)
      have hdiff : a + (↑(k + 1) : ℝ) * h - (a + k * h) = h := by push_cast; ring
      rw [hdiff, abs_of_nonneg hh] at hchord
      have hsquare := pow_le_pow_left₀ (norm_nonneg _) hchord 2
      have hlocal := angle_le_norm_sub_add_sq (hunit _ (hmem k hk'))
        (hunit _ (hmem (k + 1) hk))
      have herror := mul_le_mul_of_nonneg_left hsquare (sq_nonneg Real.pi)
      have hprev := ih hk'
      push_cast at htri hlocal hchord herror hsquare ⊢
      nlinarith
  have hfinal := hchain N le_rfl
  have hend : a + (N : ℝ) * h = b := by linarith
  rw [hend] at hfinal
  have heq : (N : ℝ) * (h + Real.pi ^ 2 * h ^ 2) =
      b - a + Real.pi ^ 2 * (b - a) ^ 2 / N := by
    dsimp [h]
    field_simp
  exact hfinal.trans_eq heq

/-- 曲线全程位于单位球上时，欧氏单位 Lipschitz 界蕴含球面单位 Lipschitz 界。 -/
theorem sphericalSpeedBound_of_euclideanSpeedBound {n : ℝ → E} {a b : ℝ}
    (hunit : ∀ t ∈ Icc a b, ‖n t‖ = 1)
    (hspeed : EuclideanSpeedBound n a b) : SphericalSpeedBound n a b := by
  have ordered {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
      angle (n s) (n t) ≤ t - s := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (max 0 (Real.pi ^ 2 * (t - s) ^ 2 / ε))
    have hNr : (0 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
    have hnat : 0 < N := Nat.cast_pos.mp hNr
    have herror : Real.pi ^ 2 * (t - s) ^ 2 / N ≤ ε := by
      have h := lt_of_le_of_lt (le_max_right _ _) hN
      have h' : Real.pi ^ 2 * (t - s) ^ 2 < (N : ℝ) * ε := (div_lt_iff₀ hε).mp h
      exact (div_le_iff₀ hNr).mpr (by nlinarith)
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    exact (angle_le_partition_bound hst (fun x hx => hunit x (hsub hx))
      (fun x hx y hy => hspeed x (hsub hx) y (hsub hy)) N hnat).trans
      (by linarith)
  intro s hs t ht
  rcases le_total s t with hst | hts
  · simpa [abs_of_nonneg (sub_nonneg.mpr hst)] using ordered hs ht hst
  · rw [angle_comm]
    simpa [abs_of_nonpos (sub_nonpos.mpr hts)] using ordered ht hs hts

/-- mathlib 的欧氏 Lipschitz 接口到球面速度接口的包装。 -/
theorem sphericalSpeedBound_of_lipschitzOnWith {n : ℝ → E} {a b : ℝ}
    (hunit : ∀ t ∈ Icc a b, ‖n t‖ = 1)
    (hspeed : LipschitzOnWith 1 n (Icc a b)) : SphericalSpeedBound n a b := by
  apply sphericalSpeedBound_of_euclideanSpeedBound hunit
  intro s hs t ht
  simpa [dist_eq_norm, Real.norm_eq_abs, abs_sub_comm] using hspeed.dist_le_mul s hs t ht

/-- 端点反极时，两个端点到中点的夹角之和为 π。 -/
theorem midpoint_angles_add_pi {n : ℝ → E} {c : ℝ}
    (hend : n (2 * c) = -n 0) :
    angle (n c) (n 0) + angle (n c) (n (2 * c)) = Real.pi := by
  rw [hend, angle_neg_right]
  ring

/-- 从中点向外参数化的半曲线满足三项角距离包络。 -/
theorem angle_le_envelope {m : ℝ → E} {c s : ℝ}
    (hc : 0 ≤ c) (hs : s ∈ Icc 0 c)
    (hunit : ∀ t ∈ Icc 0 c, ‖m t‖ = 1)
    (hspeed : SphericalSpeedBound m 0 c) :
    angle (m 0) (m s) ≤ envelope c (angle (m 0) (m c)) s := by
  have h0 : (0 : ℝ) ∈ Icc 0 c := ⟨le_rfl, hc⟩
  have hC : c ∈ Icc 0 c := ⟨hc, le_rfl⟩
  have hfirst : angle (m 0) (m s) ≤ s := by
    simpa [abs_of_nonneg hs.1] using hspeed 0 h0 s hs
  have hlast : angle (m c) (m s) ≤ c - s := by
    simpa [abs_of_nonpos (sub_nonpos.mpr hs.2)] using hspeed c hC s hs
  have hsecond : angle (m 0) (m s) ≤ c + angle (m 0) (m c) - s := by
    have ht := angle_triangle_unit (hunit 0 h0) (hunit c hC) (hunit s hs)
    linarith
  exact le_min (le_min hfirst hsecond) (angle_le_pi _ _)

/-- 球面角距离包络给出用于积分的逐点投影下界。 -/
theorem cos_envelope_le_inner {m : ℝ → E} {c s : ℝ}
    (hc : 0 ≤ c) (hs : s ∈ Icc 0 c)
    (hunit : ∀ t ∈ Icc 0 c, ‖m t‖ = 1)
    (hspeed : SphericalSpeedBound m 0 c) :
    Real.cos (envelope c (angle (m 0) (m c)) s) ≤ ⟪m 0, m s⟫_ℝ := by
  rw [inner_eq_cos_angle_of_norm_eq_one (hunit 0 ⟨le_rfl, hc⟩) (hunit s hs)]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (angle_nonneg _ _)
    (min_le_right _ _) (angle_le_envelope hc hs hunit hspeed)

end RobustPiGate


