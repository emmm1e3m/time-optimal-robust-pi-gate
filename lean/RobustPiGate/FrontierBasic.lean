import RobustPiGate.Basic

noncomputable section
namespace RobustPiGate

/-- 无量纲时长所对应的最小失谐残差。 -/
def frontierResidual (L : ℝ) : ℝ := 4 * Real.cos ((L - Real.pi) / 4) - 2

/-- 无量纲失谐的平均门不保真度二次系数下界。 -/
def frontierSensitivity (L : ℝ) : ℝ := (frontierResidual L) ^ 2 / 6

/-- 三段达到族的无量纲总时长。 -/
def frontierDuration (a : ℝ) : ℝ := 4 * a + Real.pi

end RobustPiGate
