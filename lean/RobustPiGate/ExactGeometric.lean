import RobustPiGate.SharpLength
import RobustPiGate.Quantum

noncomputable section
open Real Set MeasureTheory InnerProductGeometry
open scoped InnerProductSpace
namespace RobustPiGate
open Quantum

/-- 归一化三维球面问题的实际可行时长集合。 -/
def geometricDurations : Set ℝ := {L | 0 < L ∧ ∃ n : ℝ → Vec3,
  LipschitzOnWith 1 n (Icc 0 L) ∧ (∀ t ∈ Icc 0 L, ‖n t‖ = 1) ∧
  n L = -n 0 ∧ (∫ t in 0..L, n t) = 0}

/-- 已知三段控制的实际球面轨道证明可行性。 -/
theorem short_duration_mem : 7 * Real.pi / 3 ∈ geometricDurations := by
  refine ⟨by positivity, shortPath, shortPath_lipschitz.lipschitzOnWith, ?_,
    shortPath_antipodal, shortPath_integral_zero⟩
  exact fun t _ => shortPath_unit t

/-- 锐下界和真实达到轨道合并为最小元定理。 -/
theorem geometric_minimum : IsLeast geometricDurations (7 * Real.pi / 3) := by
  refine ⟨short_duration_mem, ?_⟩
  intro L hL
  rcases hL with ⟨hpos, n, hLip, hunit, hend, hzero⟩
  exact spherical_curve_length_lower_bound hpos hLip.continuousOn hunit
    (sphericalSpeedBound_of_lipschitzOnWith hunit hLip) hend hzero

/-- 最小元因此也是下确界；这里不需要最优解存在性公理。 -/
theorem geometric_sInf : sInf geometricDurations = 7 * Real.pi / 3 :=
  geometric_minimum.csInf_eq

end RobustPiGate
