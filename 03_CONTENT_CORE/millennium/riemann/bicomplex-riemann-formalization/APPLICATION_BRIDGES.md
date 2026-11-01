# Proposed application bridges (items 7–15)

This registry separates a shared arithmetic pattern from claims about real
systems. `Formal/ApplicationBridges.lean` proves that the nine named entries
are assigned the same exact scaled pair, `(3, 7)`, representing `(0.3, 0.7)`.
That is a formal encoding of the proposed mapping; it is not evidence that the
systems share one physical law.

The convention is `effective = sigma - b`. With tenths as the integer scale,
`sigma = 5` and `b = -2` give `effective = 7` (0.7); the opposite component
with `b = 2` gives `3` (0.3). The imaginary ordinate/frequency is recorded
separately and is not numerically combined with a dimensionless zeta input.

| # | Domain | Proposed correspondence | Missing bridge / limit |
|---|---|---|---|
| 7 | Belousov–Zhabotinsky reaction | Oscillatory reaction; bromate concentration proposed as `b` | Oscillation in a beaker does not establish `sigma-b` or a zeta-zero correspondence. A reaction-kinetics model and parameter fit are needed. |
| 8 | SIR epidemic | Proposed 0.7/0.3 outcomes and four vaccine/ wave scenarios | Standard SIR reproduction number is real. `0.7+14i` is not a standard reproduction number; define a separate complex spectral parameter and derive its relation to incidence. |
| 9 | Acoustic echo | Proposed 440 Hz mode with 0.7 growth / 0.3 decay | Specify the linear acoustic operator, boundary conditions, units, and sign convention for modal growth. Spatial cancellation requires phase/amplitude equations. |
| 10 | Laser mode | `sigma` as modal growth; `b` as a coupled-mirror/alignment term | Derive the mode equation from gain, loss, cavity length, and mirror coupling. `b != 0` alone does not imply misalignment or firing. |
| 11 | Seismic wave | Complex wavenumber and attenuation near a fault | Attenuation depends on the sign convention and propagation direction. It does not by itself imply a wave disappears on one side and reappears on the other, or connect to zeta zeros. |
| 12 | EEG | Proposed 10 Hz alpha mode and 0.7/0.3 interpretations | These values do not diagnose seizure or deep sleep. A validated signal model and clinical data would be required; the zeta connection is not established. |
| 13 | Aeroelastic flutter | Positive modal growth associated with instability | A positive eigenvalue can indicate instability in a specified linearized model. The bicomplex zero-divisor identity is not a derivation of torsion-flexion cancellation or a bridge to structural failure. |
| 14 | Economy | 0.7/0.3 assigned to bubble/crash and leverage as `b` | The 2008 crisis is not shown to be simultaneous cancellation of two coordinates. Define and estimate an economic dynamical model before assigning these values. |
| 15 | Social spread | Proposed algorithm/sharing scenarios and `R0=0.5+delta` | In ordinary contagion models `R0` is real; `0.7+14i` is not a standard reproduction number. Use a separately defined network growth eigenvalue and validate it against data. |

## Algebraic identity and physical interpretation

The existing Lean file proves in its four-coordinate bicomplex algebra that
`k^2 = 1` and `(1+k)(1-k)=0` while each factor is nonzero. This is a zero-
divisor identity. It does not prove that sound cancels, a wing's torsion
cancels flexure, or a geological wave vanishes and reappears. Each such claim
needs its own equations and measurable variables.

## Riemann-hypothesis boundary

None of these entries defines the analytic zeta function, proves a zero exists,
or proves/refutes the Riemann Hypothesis. The common pair is conditional on the
chosen coordinate map and is not an empirical bridge or a proof about zeta.
