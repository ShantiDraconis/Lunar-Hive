# Riemann hypothesis: formalization archive

This directory links the recovered bicomplex coordinate model to the classical Riemann-hypothesis question and nine proposed application analogies (chemistry, epidemics, acoustics, lasers, seismic waves, EEG, aeroelasticity, markets, and social spread).

## Scope and evidence

The Lean sources encode elementary algebra, integer-coordinate arithmetic, generic componentwise statements, and conditional bridge contracts. They do not define an analytic continuation of ζ, establish an application-specific dynamical model, or prove the Riemann hypothesis. Application labels and outcomes are hypotheses unless their models and evidence are separately supplied.

The identity `(1+k)(1-k)=0` follows from `k²=1`; it is a zero-divisor identity in bicomplex algebra, not a physical cancellation law. Likewise, `sigma-b=0.7` for `sigma=0.5, b=-0.2` is coordinate arithmetic, not evidence for an off-line zero of ζ.

## Navigation and bridge map

- [Public bridge index](PUBLIC_BRIDGE_INDEX.md): domain analogies, modeling obligations, and formal file links.
- [24-file package](bicomplex-riemann-formalization/README.md): formula catalog, claim ledger, registries, contracts, Lean sources, and build files.
- [Formal file guide](bicomplex-riemann-formalization/FORMAL_FILE_GUIDE.md), [claim ledger](bicomplex-riemann-formalization/CLAIMS.md), and [proof status](bicomplex-riemann-formalization/FORMAL_PROOF_STATUS.md).
- [Open bridge registry](bicomplex-riemann-formalization/OPEN_BRIDGE_REGISTRY.csv) and [classical RH registry](bicomplex-riemann-formalization/CLASSICAL_RH_REGISTRY.csv).

| Bridge family | Formal entry points | Established scope |
|---|---|---|
| Bicomplex algebra and component lift | `Formal/BicomplexLift.lean`, `Formal/ComponentLift.lean` | Algebra and generic two-component zero criterion |
| Shift/application coordinates | `Formal/ShiftModel.lean`, `Formal/ApplicationBridges.lean` | Exact coordinate arithmetic only |
| Symmetry/transfer contracts | `Formal/CenteredSymmetry.lean`, `Formal/BridgeContracts.lean`, `Formal/AnalyticBridgeContracts.lean` | Conditional results; no zeta instance |
| Explicit-formula scaling | `Formal/ExplicitFormulaScaling.lean` | Abstract exponent bookkeeping, not the explicit formula |
| Other RH routes | `ANALYTIC_BRIDGES.md`, `CLASSICAL_RH_BRIDGES.md` | Open analytic, spectral, and classical obligations |

## Verification

[The Lean workflow](../../../.github/workflows/riemann-formalization.yml) runs `lake build` and an axiom audit. A passing run covers the submitted Lean declarations under the pinned toolchain and configured audit; it does not certify the prose, empirical interpretations, or RH. Entries marked `WRITTEN_UNCHECKED` remain unchecked until a successful run covers the exact commit. RH remains open.
