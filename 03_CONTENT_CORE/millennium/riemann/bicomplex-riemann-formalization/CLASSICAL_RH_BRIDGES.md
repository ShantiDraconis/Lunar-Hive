# Classical analytic bridges still to formalize

These are standard routes connecting the classical zeta function, its zeros,
and the prime numbers. They extend the earlier bicomplex, application, and
spectral registries. **None is formalized by the present package.** The status
column identifies the exact mathematical gap instead of promoting a known
equivalence into a proof of RH.

| Bridge | Established mathematical statement | Package status / work needed |
|---|---|---|
| Dirichlet series and analytic continuation | `ζ(s)=Σ n^{-s}` is initially defined for `Re(s)>1`; continuation gives a meromorphic function with a simple pole at `s=1`. | OPEN_FORMALIZATION: define the function and convergence/continuation in the selected Lean analysis library. |
| Euler product and zero-free region | For `Re(s)>1`, `ζ(s)=∏ₚ(1-p^{-s})^{-1}`, hence no zeros there. The zero-free line `Re(s)=1` is a separate theorem, not a consequence of the product alone. | OPEN_FORMALIZATION: prove the product and nonvanishing with convergence hypotheses; do not extend this conclusion into the critical strip. |
| Functional equation and trivial zeros | The functional equation yields the trivial zeros at negative even integers and reflects the nontrivial zero region. | OPEN_FORMALIZATION: formalize gamma factors, continuation, and the functional equation before deriving zero locations. |
| Completed xi function | The completed function `ξ(s)=½s(s−1)π^(−s/2)Γ(s/2)ζ(s)` is entire and symmetric under `s ↦ 1−s`; RH is equivalent to all its zeros having real part 1/2. | OPEN_FORMALIZATION: define `ξ`, prove its analytic properties and the equivalence. The current integer-coordinate model is not sufficient. |
| Critical strip and trivial/nontrivial classification | Apart from trivial zeros, ζ has no zeros for `Re(s)≤0`; the nontrivial zeros lie in `0<Re(s)<1`, with reflection symmetries. | OPEN_FORMALIZATION: prove the boundary and classification lemmas from the functional equation and zero-free results. |
| Riemann–von Mangoldt zero count | `N(T)` counts zeros up to height `T` and has a known asymptotic formula. A count alone does not locate every zero on the critical line. | OPEN_FORMALIZATION: prove the argument-principle/counting formula and explicit error bound; connect it to certified zero counting. |
| Nyman–Beurling criterion | RH is equivalent to a specified density statement in `L²(0,1)` for a span of fractional-part functions. | OPEN_FORMALIZATION: fix one exact version, define the Hilbert-space objects, and formalize both directions. Density must not be inferred from finite computation. |
| Li criterion | RH is equivalent to nonnegativity of every Li coefficient. Checking finitely many coefficients is not enough. | OPEN_FORMALIZATION: define the coefficients using the completed function/zeros and prove the all-indices equivalence. |
| de Bruijn–Newman flow | In standard conventions RH is equivalent to `Λ≤0`; Rodgers–Tao proved `Λ≥0`, so RH is equivalent to `Λ=0`. | OPEN_FORMALIZATION: define the heat-flow family and constant, formalize the equivalence and the lower bound. This is another formulation, not a proof that `Λ=0`. |
| Riemann–Siegel/Turing certification | Certified values and zero counts can establish that a finite range contains no unaccounted zeros; finite verification does not settle all heights. | OPEN_FORMALIZATION: provide interval-certified numerics, an explicit global counting theorem, and a proof that the two counts agree. |
| Prime-counting error equivalence | RH has equivalent quantitative formulations for errors in prime-counting functions. | OPEN_FORMALIZATION: choose a precise statement (`ψ(x)`, `π(x)`, or another function), track constants and quantifiers, and prove both implications. |

## Dependency order

1. Define classical `ζ` and establish its initial series/product facts.
2. Build analytic continuation, the functional equation, and the completed `ξ`.
3. Prove the critical-strip, trivial-zero, symmetry, and zero-count results.
4. Add one RH criterion at a time (Nyman–Beurling, Li, or de Bruijn–Newman),
   with both directions and all quantifiers.
5. Only then connect a criterion to primes, a spectral operator, mollifiers,
   or the bicomplex coordinate model.

No stage above follows from `sigma_eff = sigma - b` or from the bicomplex
zero-divisor identity. Those are separate algebraic facts.

## References

- NIST Digital Library of Mathematical Functions, [§25.2: definition, series,
  Euler product, and product over zeros](https://dlmf.nist.gov/25.2) and
  [§25.10: zeros and zero symmetries](https://dlmf.nist.gov/25.10).
- Xian-Jin Li, [The Positivity of a Sequence of Numbers and the Riemann
  Hypothesis](https://www.sciencedirect.com/science/article/pii/S0022314X97921375),
  *Journal of Number Theory* 65 (1997), 325–333.
- Luis Báez-Duarte, [New versions of the Nyman–Beurling criterion for the
  Riemann hypothesis](https://doi.org/10.1155/S0161171202013248), 2002.
- Brad Rodgers and Terence Tao, [The de Bruijn–Newman constant is
  non-negative](https://doi.org/10.1017/fmp.2020.6), *Forum of Mathematics, Pi*
  8 (2020), e6.
