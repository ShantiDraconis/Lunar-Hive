# Claim ledger

| Claim | Status in this bundle | Reason |
|---|---|---|
| `k = ij` has square `+1` when commuting `i,j` each square to `−1` | Lean proof term included; kernel check unavailable here | `(ij)^2 = i²j² = 1` |
| `(1+k)(1−k)=0` with both factors nonzero | Lean proof terms included; kernel check unavailable here | These are zero divisors; neither factor is zero |
| If `y=a+ib` in ordinary `ℂ`, then `−1+iy=−1−b+ia` | Lean proof terms included; kernel check unavailable here | `i²=−1`; for `b=−3`, the real part is `2` |
| If `y=a+jb` with an independent commuting bicomplex `j`, then `i(a+jb)=ia+kb` | Lean proof term included; kernel check unavailable here | The scalar real coefficient stays unchanged; component shifts arise in idempotent coordinates |
| `z=σ+it+kb` has idempotent components `(σ+b)+it` and `(σ−b)+it` | Coordinate identities included; kernel check unavailable here | Use `e±=(1±k)/2`; `ke±=±e±` |
| A zero in one component alone is a zero of the full bicomplex value | False | It is a zero divisor situation; the other component may be nonzero |
| Setting `b=0` sends every off-line component zero to a classical zero on the critical line | Not established; does not follow | The argument changes, and `σ` is not thereby constrained to `1/2` |
| No classical off-line zeta zeros exist because a second coordinate is absent in `ℂ` | Not established | This is the RH assertion, not a consequence of changing number systems |
| In tenths, `5 - (-2) = 7` and the paired coordinates are `(3,7)` | Lean theorem and proof term written in `Formal/ShiftModel.lean`; kernel check pending | Exact integer arithmetic for the proposed coordinate convention |
| Each of the nine application entries maps to `(0.3,0.7)` | Lean theorem and proof term written in `Formal/ApplicationBridges.lean`; kernel check pending | The registry assigns the same numbers by definition; it proves no domain behavior |
| The 0.7/0.3 pair predicts EEG, chemical, acoustic, laser, seismic, aeroelastic, economic, epidemic, or social outcomes | Not established | Domain-specific dynamics, units, parameter estimates, and independent validation are absent |
| `(1+k)(1-k)=0` means physical cancellation in each listed domain | Not established | It is an algebraic zero-divisor identity in the bicomplex model, not a physical law |
| Reflection/conjugation assumptions produce a four-point orbit | Lean theorem and proof term written in `Formal/AnalyticBridgeContracts.lean`; kernel check pending | The theorem is conditional on both closure assumptions for an abstract set |
| Two component real coordinates both equal to 1/2 force the center to 1/2 and shift to 0 | Lean theorem and proof term written in `Formal/AnalyticBridgeContracts.lean`; kernel check pending | Coordinate arithmetic only; no zeta-zero or RH premise is proved |
| There is a last natural number, or a standard natural “after infinity” | Refuted within the standard `Nat` model by `Formal/AfterInfinity.lean` | Every natural has a successor; an adjoined point belongs to a different type |
| Hadamard, mollifier, explicit-formula, Hilbert–Pólya/Berry–Keating, or RH-consequence bridges close the RH proof | Open / not established | Their definitions, analytic estimates, operator construction, or producer proofs are not present |
| Euler product proves zero-freeness for `Re(s)>1` | Established classical result, not formalized here | The convergence and nonvanishing proof is outside this package |
| Nyman–Beurling, Li, de Bruijn–Newman, zero-counting, and prime-error criteria prove RH | Established equivalences or conditional criteria, not formalized here | An equivalent criterion proves RH only after its all-parameter target is proved; finite checks do not suffice |
| The current algebraic and conditional theorem terms are kernel-verified | Not verified | Lean/Lake are unavailable in this environment; see `FORMAL_PROOF_STATUS.md` |
| A full bicomplex pair is zero iff both component values are zero | Lean source theorem written, kernel check pending | `Formal/ComponentLift.lean`; generic product-value statement, not an analytic zeta lift |
| One zero component with a nonzero other component is a zero of the full pair | False; the source proves it is not the pair zero | `one_zero_component_not_pair_zero`; zero-divisor terminology is algebraic |
| Reflection in centered coordinates exchanges the 0.7 and 0.3 tenths values | Lean source theorem written, kernel check pending | `Formal/CenteredSymmetry.lean`; coordinate arithmetic only, no existence of zeta zeros |
| An abstract target-axis theorem transfers to source zeros through an exact bridge | Lean source theorem written, kernel check pending | `Formal/BridgeContracts.lean`; requires both zero correspondence and axis correspondence fields |
| `Formal/BridgeContracts.lean` supplies a bridge instance for classical `ζ` or a physical system | False | No concrete bridge instance, analytic continuation, calibrated operator, or empirical model is included |
| Moving the real exponent from 0.5 to 0.7 changes the numerator power by (x^{0.2}) | Exact exponent difference; multiplicative consequence conditional on an abstract exponent law | `Formal/ExplicitFormulaScaling.lean`; the denominator `|ρ|` also changes slightly when the ordinate is fixed and the real part changes |
| The 251 ratio at (x=10^{12}) is the exact total error in (pi(x)-\operatorname{Li}(x)) | False | It is a rounded ratio of individual zero-term amplitude bounds; phases and other zeros affect the full sum, and passage to `π(x)` uses partial summation |
| A Davenport–Heilbronn off-line zero is an off-line zero of Riemann `ζ` | False | It is a zero of a different function and cannot be inserted into Riemann's prime explicit formula |

The modules formalize only finite algebraic identities, conditional symmetry/arithmetic contracts, and the explicitly defined coordinate registry. They contain no definition of `ζ` or analytic continuation. The new Lean source has not been kernel-checked in this environment.
