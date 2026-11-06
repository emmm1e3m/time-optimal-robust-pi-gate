import RobustPiGate
import Lean.Util.CollectAxioms

open Lean Elab Command
open scoped Matrix Matrix.Norms.L2Operator

-- 按所属模块枚举，覆盖私有引理和自动生成声明，不只检查人工挑选的出口。
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let owner := env.header.moduleNames[idx]!
      if (`RobustPiGate).isPrefixOf owner then
        names := names.push name
  names := names.qsort Name.lt
  if names.isEmpty then
    throwError "No project declarations found"
  let mut theoremCount := 0
  for name in names do
    let info ← getConstInfo name
    if info matches .axiomInfo _ then
      throwError "Project axiom: {name}"
    if info matches .thmInfo _ then
      theoremCount := theoremCount + 1
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"AUDIT {name}: {axioms}"
  logInfo m!"PASS declarations={names.size} theorems={theoremCount}; only propext, Classical.choice, Quot.sound allowed"

-- 将实际可导的稳健性与可行集中的 deriv 写法作双向对照。
example {Ω : NNReal} {T : ℝ} {ux uy : ℝ → ℝ}
    {U : ℝ → ℝ → RobustPiGate.Quantum.QubitMatrix}
    (hU : RobustPiGate.Dynamics.IsQubitEvolution ux uy U T) :
    deriv (fun δ => U δ T) 0 = 0 ↔ HasDerivAt (fun δ => U δ T) 0 0 := by
  constructor
  · intro h
    have hd := RobustPiGate.Dynamics.qubit_parameter_hasDerivAt hU
    rw [← hd.deriv, h] at hd
    exact hd
  · intro h
    exact h.deriv

#check @RobustPiGate.exact_time_and_all_minimizers
#check @RobustPiGate.both_short_signs_attain
#check @RobustPiGate.robust_pi_infimum
#print RobustPiGate.AdmissibleRobustPi
#print RobustPiGate.Dynamics.IsQubitEvolution
#print RobustPiGate.Dynamics.IsACSolution
