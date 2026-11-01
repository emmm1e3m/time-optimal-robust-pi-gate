# Lean 4 proof

This project formalizes the exact time and all minimizing controls for a
first-order detuning-robust full qubit π gate with arbitrary measurable
transverse controls and a joint amplitude bound Ω>0.

## Main statements

All names below are in namespace `RobustPiGate`.

| Theorem | Statement |
| --- | --- |
| `exact_time_and_all_minimizers` | The physical feasible-time set has minimum 7π/(3Ω), with the complete a.e. control classification |
| `robust_pi_infimum` | The corresponding infimum equals 7π/(3Ω) |
| `both_short_signs_attain` | Both signs of short-CORPSE have actual detuned evolution families that attain the minimum |
| `Quantum.optimal_controls_unique_scaled` | Every minimizing control is a.e. ±Ωq(Ωt) along x, with zero y control |
| `ac_spherical_curve_length_lower_bound` | The finite-dimensional AC spherical-curve lower bound |
| `spherical_curve_equality_rigidity` | Every critical curve follows the same great-circle three-arc pattern |
| `DimensionSharpness.euclidean_minimum` | The spherical minimum is attained in every dimension d≥2 |
| `Dynamics.qubit_parameter_hasDerivAt` | The actual derivative with respect to the physical detuning parameter |

Start with [Main.lean](RobustPiGate/Main.lean) and
[PhysicalMain.lean](RobustPiGate/PhysicalMain.lean).

## Build

Lean **4.35.0**; mathlib **v4.35.0** at commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
The manifest pins all dependencies.

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

The project was successfully built with this toolchain. The axiom audit
uses only `propext`, `Classical.choice`, and `Quot.sound`; no project axiom,
`sorry`, `admit`, or `native_decide` is used. Dependency caches and build
products are intentionally not versioned.

## Model and proof chain

`AdmissibleRobustPi` uses actual complex 2×2 matrices, controls that are
`AEMeasurable` on the evolution interval, an a.e. amplitude disk bound,
absolutely continuous propagators satisfying the original ODE a.e., a
unit initial propagator, the full target ±Rx(π), and zero first-order
detuning derivative. The controls do not depend on the static detuning.

Unitarity, Duhamel's identity, parameter differentiability and the Bloch
curve are derived from the ODE. In particular, the `deriv = 0` condition
does not use the default value of `deriv` at a nondifferentiable point:
actual `HasDerivAt` is proved. Admissible objects pair a control with its
ODE solution family. Solution uniqueness and the explicit attaining
families are proved; a separate general existence theorem for every
measurable linear ODE is not needed for these statements.

1. `ACCalculus`, `Dynamics`, `QubitDynamics`: AC calculus, unitarity,
   Duhamel and the detuning derivative with a quadratic remainder.
2. `Quantum`, `BlochBridge`: Pauli algebra and the actual noise curve,
   including its unit norm, speed, antipodal endpoints and zero integral.
3. `Geometry`, `Envelope`, `Scalar`, `SharpLength`, `TimeScaling`:
   angular-distance bounds and the sharp midpoint comparison.
4. `ShortEvolution`, `SignSymmetry`: both actual attaining evolution families.
5. `Rigidity`, `Equality`, `RotatedShort`, `LiftUniqueness`,
   `OptimalControls`, `EvolutionScaling`: geometric rigidity, unique
   transverse lifts and all minimizing controls in the original time variable.
6. `DimensionSharpness`, `PhysicalMain`, `Main`: sharpness in every
   dimension and the physical minimum.

The formal proof follows the manuscript's midpoint argument. Some local
steps use equivalent proofs, including subdivision for the angular speed
bound and spherical-geodesic equality for rigidity. Literature attribution,
figures and floating-point calculations are not Lean propositions.
