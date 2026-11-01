# Public bridge index

“Bridge” here means a proposed correspondence or proof obligation, not a validated transfer theorem.

| Item | Domain analogy | Required mathematical/empirical bridge | Package references |
|---:|---|---|---|
| 7 | Belousov–Zhabotinsky chemistry | Define a reaction-diffusion model and derive any relation between its stability/oscillation parameter and a zeta coordinate. | `APPLICATION_BRIDGES.md`, `FORMULA_CATALOG.md`, `OPEN_BRIDGE_REGISTRY.csv` |
| 8 | SIR epidemic | Specify equations, units, thresholds, and evidence for the proposed `0.3/0.7` coordinates. | Same application registry; `Formal/ApplicationBridges.lean` proves arithmetic only. |
| 9 | Room acoustics | Derive growth/decay and phase behavior from boundary conditions and measured geometry. | `APPLICATION_BRIDGES.md`; zero-divisor identity does not prove acoustic cancellation. |
| 10 | Laser mode | Define the cavity operator and derive a threshold; distinguish instability from a zeta zero. | `APPLICATION_BRIDGES.md`; no physical model is formalized. |
| 11 | Seismic fault | Specify PDE/interface conditions and wavenumber convention; prove any link to bicomplex factors. | `APPLICATION_BRIDGES.md`; no geophysical theorem is asserted. |
| 12 | EEG | Supply a neural model and clinically grounded criteria; spectral coordinates alone cannot diagnose seizure/sleep. | `APPLICATION_BRIDGES.md`; no data or clinical inference is formalized. |
| 13 | Aeroelastic flutter | Derive coupled bending/torsion eigenvalues and instability threshold from a stated model. | `APPLICATION_BRIDGES.md`; no bridge to `(1+k)(1-k)=0` is proved. |
| 14 | Markets/leverage | Define a stochastic/agent model and test leverage claims; “2008 as a 0.7/0.3 rectangle” is unestablished. | `APPLICATION_BRIDGES.md`; no market-data theorem is supplied. |
| 15 | Social spread | Specify transmission model and validate any reproduction-number interpretation; algorithm/sharing scenarios need evidence. | `APPLICATION_BRIDGES.md`; no platform data are supplied. |

## Classical and analytic routes

| Route | References | Status in this package |
|---|---|---|
| Explicit formula/prime-counting scale | `FORMULA_CATALOG.md`, `CLASSICAL_RH_BRIDGES.md`, `Formal/ExplicitFormulaScaling.lean` | Exponent bookkeeping only; analytic explicit formula and RH equivalence remain open. |
| Zeta continuation, functional equation, completed ξ | `CLASSICAL_RH_BRIDGES.md`, `CLASSICAL_RH_REGISTRY.csv` | Formalization obligations, not proofs here. |
| Zero symmetries/four-point orbit | `Formal/CenteredSymmetry.lean`, `Formal/AnalyticBridgeContracts.lean` | Abstract conditional results; no zeta zero set instantiated. |
| Hilbert–Pólya/spectral operator | `ANALYTIC_BRIDGES.md`, `OPEN_BRIDGE_REGISTRY.csv` | Research route only. |
| Nyman–Beurling, Li, de Bruijn–Newman, certified zero counts | `CLASSICAL_RH_BRIDGES.md`, `CLASSICAL_RH_REGISTRY.csv` | Registry entries/open obligations only. |

The coordinate identity `sigma_eff=sigma-b` with `sigma=0.5, b=-0.2` gives `0.7`, with paired coordinate `0.3`. Neither implies a zeta zero there. Davenport–Heilbronn examples concern another function. A Lean build checks formal declarations only; it cannot make an analogy or registry entry into an empirical or analytic theorem.
