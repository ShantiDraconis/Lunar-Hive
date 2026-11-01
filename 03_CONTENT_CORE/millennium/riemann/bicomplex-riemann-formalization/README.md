# Bicomplex lift and the Riemann zeta function

This formalization isolates what follows algebraically from a two-component (idempotent) extension and what does not. It also records nine proposed application-coordinate bridges (items 7–15) without treating their physical or social interpretations as proven.

## Coordinate model

Let `i² = j² = -1`, with `i` and `j` commuting, and put `k = ij`, so `k² = 1`. The idempotents are `e₊ = (1+k)/2` and `e₋ = (1-k)/2`. For

\[
z=\sigma+it+kb,
\]

the two complex components are

\[
s_+=(\sigma+b)+it,\qquad s_-=(\sigma-b)+it.
\]

Thus one component has effective real part `σ − b`, while the other has `σ + b`. The scalar coefficient called the real part of the bicomplex number remains `σ`; `σ±b` are the real parts of its two idempotent complex components.

This distinction matters for the calculation with `y`. If `y=a+ib` uses the **same** complex unit `i`, then this is already ordinary complex arithmetic:

\[
-1+i(a+ib)=(-1-b)+ia.
\]

Its real part is `−1−b`; it equals `2` when `b=−3`. If `y=a+jb` uses an independent commuting bicomplex unit `j`, then `i(a+jb)=ia+kb`, where `k=ij`; the scalar real coefficient does not change. The component shifts `σ±b` appear only after idempotent decomposition. Neither calculation says anything about where a zero of classical `ζ` exists.

## What the formal file establishes

`Formal/BicomplexLift.lean` gives a four-coordinate integer model and contains proof terms for:

1. `i² = j² = −1`, `ij = ji = k`, and `k² = 1`;
2. `(1+k)(1−k)=0` although both factors are nonzero;
3. `i(a+ib)=−b+ia`, including the example `Re(−1+i(−3i))=2`;
4. with independent `j`, `i(a+jb)=ia+kb`, so the scalar real coefficient stays unchanged;
5. the two idempotent real coordinates are `σ+b` and `σ−b`, and they coincide at `b=0`.

The results are elementary algebra over integers. Lean is not installed in the current execution environment, so these proof terms have not been kernel-checked here. They do not formalize analytic continuation or the Riemann zeta function, and they do not prove or refute RH.

## Logical limit

In the idempotent model, a full bicomplex value is zero only when both component values are zero; a zero divisor is nonzero and noninvertible, not a hidden zero. If one component satisfies `ζ(σ − b + it) = 0`, setting `b := 0` changes that argument to `σ + it`; it does not establish `ζ(σ + it) = 0`, nor establish `σ = 1/2`. If both components vanish and `b=0`, this gives an ordinary zero `ζ(σ+it)=0`, but the projection does not constrain `σ` to `1/2`.

The Riemann Hypothesis remains the separate assertion that every nontrivial zero of the classical zeta function has real part `1/2`.

## Application bridges

`APPLICATION_BRIDGES.md` lists the proposed bridges for chemical oscillation,
SIR epidemics, acoustic modes, lasers, seismic waves, EEG, aeroelastic flutter,
markets, and social spread. `Formal/ShiftModel.lean` contains a Lean theorem
and proof term for the exact tenths arithmetic of `sigma-b`;
`Formal/ApplicationBridges.lean` contains a theorem and proof term for the
registry pair `(0.3,0.7)`. Neither file proves the domain interpretations or a
result about zeta zeros. See `CLAIMS.md` for the claim ledger and verification
status.

## Analytic and RH bridge register

`ANALYTIC_BRIDGES.md` and `OPEN_BRIDGE_REGISTRY.csv` restore the remaining
analytic/spectral routes: the bicomplex zeta extension, conditional RH
coordinate consequence, zero symmetries, Hadamard product, mollification,
explicit formula/primes, Hilbert–Pólya/Berry–Keating, conditional consequences,
and the “after infinity” proposal. `Formal/AnalyticBridgeContracts.lean`
contains conditional coordinate/symmetry lemmas only. `Formal/AfterInfinity.lean`
records that standard naturals have no last element and an adjoined index is a
new type. None closes RH.

`CLASSICAL_RH_BRIDGES.md` and `CLASSICAL_RH_REGISTRY.csv` extend the scope to
the standard analytic foundations and criteria: Euler product, continuation,
functional equation, completed xi, zero counting, Nyman–Beurling, Li,
de Bruijn–Newman, certified zero counts, and prime-counting equivalences.
These are recorded as open formalization obligations, not completed Lean
proofs.

`Formal/ComponentLift.lean` states the exact product-component zero
condition: both components must vanish. `Formal/CenteredSymmetry.lean` proves
the centered-coordinate reflection arithmetic, and
`Formal/BridgeContracts.lean` gives the exact source/target equivalences that
a genuine analytic or spectral bridge must prove before a zero-location
theorem can transfer. These contracts have no instance for zeta or an
application model. `Formal/ExplicitFormulaScaling.lean` proves the exact
tenths exponent shift from 0.5 to 0.7 under an abstract multiplicative growth
law; it does not formalize real powers or the explicit formula itself.
`Formal/ProofMap.lean` indexes representative results.

`FORMAL_FILE_GUIDE.md` describes every file; `FORMAL_BRIDGE_CONTRACTS.md`
records the obligations for bicomplex, spectral, dynamical, reflection, and
application bridges. The available environment has no `lean` or `lake`
executable, so the Lean source has not been kernel-verified. The theorem ledger
distinguishes written proof terms from verified source and preserves all open
analytic obligations.

`FORMULA_CATALOG.md` collects the core algebra, the proposed application
formulas for items 7–15, and the standard zeta/RH formulas cited by the bridge
registers. It labels model proposals separately from classical formulas and
states their domains, units, and open proof conditions.

## Build configuration

The package is configured as a Lean 4 project without Mathlib dependencies.
Run `lake build` in an environment with the toolchain named by `lean-toolchain`
to kernel-check the sources. This environment did not have Lean or Lake
installed, so the new sources have not been compiled here.
