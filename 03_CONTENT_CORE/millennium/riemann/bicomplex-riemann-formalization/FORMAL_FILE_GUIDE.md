# File-by-file guide and proof inventory

This guide accounts for every file in the archive. “Proved in Lean source”
means a theorem has a proof term written in the source. It does **not** mean
the current archive has passed Lean compilation: the runtime used to prepare
this version has no `lean` or `lake` executable. No file claims a proof of RH.

## Lean project files

| File | Contents | Proofs/results in the file | Boundary |
|---|---|---|---|
| `lean-toolchain` | Requested Lean toolchain identifier. | None. | A version request is not evidence that this toolchain is installed. |
| `lakefile.toml` | Minimal Lake package and `Formal` library target. | None. | No Mathlib dependency is declared, so classical complex analysis is not formalized here. |
| `Formal/BicomplexLift.lean` | Four-integer-coordinate algebra with commuting square-roots of −1. | Unit squares, `ij=ji=k`, `k²=1`, the nonzero zero-divisor factors, ordinary-complex versus independent-`j` multiplication, and integer coordinate projections. | Coordinates are integer models; no `ℂ`, analytic function, or zeta function is defined. |
| `Formal/ShiftModel.lean` | Tenths-scaled shift convention. | `5-(-2)=7`, opposite coordinate `3`, pair `(3,7)`, and correspondence with the minus projection. | Arithmetic in a chosen model; parameters are not measured domain values. |
| `Formal/ApplicationBridges.lean` | Nine labels for proposed domains 7–15 and a common coordinate assignment. | Every constructor receives the registry pair `(3,7)`. | The shared pair follows from the definition; it proves no chemical, medical, economic, or physical prediction. |
| `Formal/AnalyticBridgeContracts.lean` | Abstract centered points and conditional symmetry assumptions. | Involutions commute; reflection/conjugation closure gives the four-point orbit; two assumed half-line component coordinates force center `5` and shift `0`. | The set is not instantiated as the zero set of `ζ` or `ξ`; the symmetry fields are hypotheses. |
| `Formal/AfterInfinity.lean` | Standard naturals plus a separately adjoined constructor. | Every natural has a successor; the adjoined constructor is not a finite constructor. | It does not define an ordered completion of the naturals or an analytic value “after infinity.” |
| `Formal/ComponentLift.lean` | Generic two-component value and a real-coordinate shift pair. | A pair is zero iff both components are zero; if one component is zero and the other is not, the pair is not zero; two assumed half coordinates force the center/shift conclusion. | Generic component algebra only; there is no analytic bicomplex zeta lift. |
| `Formal/CenteredSymmetry.lean` | Centered coordinates with displacement from `1/2`. | Reflection negates displacement; reflection preserves being off the line; the `(0.7,0.3)` tenths pair exchanges under reflection. | The arithmetic action is proved; analytic closure of a zeta zero set is not. |
| `Formal/BridgeContracts.lean` | Exact abstract contract for source/target zero and axis correspondence. | Given explicit zero-equivalence and axis-equivalence fields, off-axis/off-line statements and a target-axis theorem transfer in both directions. | There is no instance for `ζ`, `ξ`, a physical model, or a self-adjoint operator. The contract displays the obligations rather than assuming they are solved. |
| `Formal/ExplicitFormulaScaling.lean` | Tenths-scaled exponent difference for a hypothetical explicit-formula zero term. | `7−5=2`; under an abstract exponent-addition law, growth at 0.7 factors into growth at 0.5 times growth at 0.2. | No real powers, complex modulus, explicit formula, numerical approximation, or zeta zero is formalized. |
| `Formal/ProofMap.lean` | Imports and short names for representative results. | Re-exports the algebra, coordinate, symmetry, infinity, and component theorems. | It is an index module, not an additional analytic proof. |

## Mathematical records and ledgers

| File | Role | Status convention |
|---|---|---|
| `README.md` | Project overview, scope, build instructions, and limits. | Separates source proof terms from kernel-checked results. |
| `CLAIMS.md` | Claim-by-claim truth/status ledger. | Distinguishes proved arithmetic, conditional implications, unsupported interpretations, and open RH claims. |
| `FORMULA_CATALOG.md` | Formula inventory for the algebra, proposed bridges, and classical zeta theory. | Classical formulas are references, not Lean proofs; proposed application formulas are not fitted models. |
| `APPLICATION_BRIDGES.md` | Items 7–15 with the proposed mapping and missing empirical/model equations. | “Proposed correspondence” is not a result about the domain. |
| `ANALYTIC_BRIDGES.md` | Bicomplex, symmetry, factorization, mollifier, prime, spectral, and after-infinity bridge obligations. | Conditional or open, as stated in each row. |
| `CLASSICAL_RH_BRIDGES.md` | Standard analytic foundations and equivalent RH criteria. | Open formalization work; equivalence alone does not prove RH. |
| `FORMAL_BRIDGE_CONTRACTS.md` | Exact source/target proof obligations and implementation sequence. | Records what an actual bridge instance must prove. |
| `FORMAL_FILE_GUIDE.md` | This inventory. | Accounts for every archive file. |
| `OPEN_BRIDGE_REGISTRY.csv` | Machine-readable status for the earlier bridge families. | Open statuses are not promoted. |
| `CLASSICAL_RH_REGISTRY.csv` | Machine-readable status for classical RH routes. | Each open route retains its required theorem. |
| `FORMAL_PROOF_STATUS.md` | Human-readable theorem verification status. | Source written versus kernel-checked are separate labels. |
| `FORMAL_PROOF_STATUS.csv` | Machine-readable theorem status and assumptions. | The new modules are listed as source-written, kernel-check pending. |

## Dependency map

```text
Formal/BicomplexLift
  └─ Formal/ShiftModel
       └─ Formal/ApplicationBridges

Formal/AnalyticBridgeContracts     Formal/AfterInfinity
Formal/ComponentLift               Formal/CenteredSymmetry
Formal/BridgeContracts             Formal/ExplicitFormulaScaling
                 └─ Formal/ProofMap (index/import module)
```

## What is actually formalized now

The completed source-level mathematics is finite algebra, integer arithmetic,
and implications whose assumptions are explicit. The analytic bridge now has
a precise generic shape: a source zero must correspond **iff** its image is a
target zero, and the source critical line must correspond **iff** the target
spectral axis. Only with both equivalences can a target axis theorem transfer
to a source zero-location theorem. The archive does not provide those
equivalences for the Riemann zeta function.

The nine application labels share a pair because the registry defines them
that way. For a scientific bridge, each label still needs a domain equation,
derived operator or characteristic function, parameter units/calibration,
and a proved map to the analytic source/target objects. No such instances are
included.
