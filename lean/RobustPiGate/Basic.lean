import Mathlib

noncomputable section
open Real
namespace RobustPiGate

/-- 临界半时长。 -/
def criticalHalf : ℝ := 7 * Real.pi / 6

/-- 从中点向外行走时的球面距离包络。 -/
def envelope (c β s : ℝ) : ℝ := min (min s (c + β - s)) Real.pi

/-- 每半段的投影积分下界。 -/
def halfBound (c β : ℝ) : ℝ :=
  if c + β ≤ 2 * Real.pi then
    2 * Real.sin ((c + β) / 2) - Real.sin β
  else
    2 * Real.pi - c - β - Real.sin β

end RobustPiGate
