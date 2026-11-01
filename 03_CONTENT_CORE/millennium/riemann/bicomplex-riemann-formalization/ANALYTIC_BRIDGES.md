# Analytic bridge register

This file restores the analytic/Riemann continuation of the project. Each
entry distinguishes a conditional arithmetic result from the still-open
analytic theorem. No entry below claims a proof of the Riemann Hypothesis.

| Bridge | Formal artifact | Status | Remaining obligation |
|---|---|---|---|
| Bicomplex lift of classical `ζ` | `Formal/BicomplexLift.lean`; `Formal/AnalyticBridgeContracts.lean` | Algebraic coordinate model only | Define a complex/bicomplex analytic extension, prove its compatibility with classical `ζ`, and characterize its full zero set. |
| Critical-line consequence | `both_half_components_force_center` | Conditional arithmetic contract | Prove that the relevant two component values are classical nontrivial zeta zeros and establish the RH premise; the lemma itself does not prove either premise. |
| Fourfold zero symmetry | `four_point_orbit` | Conditional set-theoretic contract | Prove reflection and conjugation closure for the exact zero set under study. The Lean theorem assumes these closure properties. |
| Hadamard product / zero product | Registry only | Open analytic bridge | Specify the entire function, canonical factors, multiplicities, and convergence; connect the product to `ζ` or `ξ`. |
| Mollification | Registry only | Open analytic bridge | Define the mollifier, estimates, uniformity, and the implication from the estimates to the desired zero statement. |
| Explicit formula and primes | Registry only | Open analytic bridge | Derive the formula with convergence/error terms and show exactly how the proposed zero information controls prime-counting terms. |
| Hilbert–Pólya / Berry–Keating | Registry only | Open spectral bridge | Construct a specified operator, prove the required self-adjointness/domain facts, and identify its spectrum with the ordinates of zeta zeros. |
| Conditional consequences of RH | Registry only | Conditional, not a proof of RH | State each consequence with its hypotheses and prove it from an explicit RH assumption; do not reverse an implication without proof. |
| “After infinity” index | `Formal/AfterInfinity.lean` | Standard `Nat` has no last element; an added point is a different type | Any proposed extension must specify its algebra, order, topology, and analytic meaning. The adjoined constructor gives no zeta-zero result. |
| Componentwise zero condition | `Formal/ComponentLift.lean` | Generic product value is zero iff both components are zero | Instantiate with an analytic lift and prove compatibility with classical `ζ`/`ξ`; one zero component alone is insufficient. |
| Exact source/target bridge | `Formal/BridgeContracts.lean` | Conditional transfer from target-axis theorem to source zero-location theorem | Construct an instance and prove both zero correspondence and axis correspondence without assuming RH. |
| Centered reflection arithmetic | `Formal/CenteredSymmetry.lean` | Reflection negates displacement and exchanges the tenths pair `(0.7,0.3)` | Prove functional-equation closure for the actual completed zeta zero set; the arithmetic theorem does not assert existence. |

## Conditional component arithmetic

In tenths, let the two proposed component real coordinates be `sigma+b` and
`sigma-b`. If **both** are assumed to equal `5` (the scaled value 1/2), then
`sigma=5` and `b=0`. This is the theorem
`BicomplexRiemann.AnalyticContracts.both_half_components_force_center`.
It is conditional coordinate algebra. It does not supply zeta zeros or prove
RH.

## Symmetry contract

The four-point statement is represented in centered coordinates by reflection
`x ↦ -x` and conjugation `t ↦ -t`. The theorem derives the orbit only for a
set supplied with both closure assumptions. A symmetry orbit does not imply
`x=0`; the critical-line conclusion requires additional mathematics.

## Scope boundary

The finite algebraic and conditional Lean files are separated from the open
analytic bridges above. The application bridges in `APPLICATION_BRIDGES.md`
are a different layer: their shared coordinate registry is not evidence for a
physical system and is not a theorem about `ζ`.
