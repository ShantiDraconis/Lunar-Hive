# Formal proof status

## Proof terms written

`Formal/ProofMap.lean` gathers theorem references for the following results:

- the bicomplex zero-divisor identity and nonzero factors;
- the exact scaled-coordinate shift `5 - (-2) = 7` and paired coordinates
  `(3,7)`;
- the registry identity assigning `(3,7)` to each of the nine application
  names;
- the four-point orbit **conditional on** reflection and conjugation closure;
- the center/shift consequence **conditional on both** component real
  coordinates being 1/2;
- no last element of standard `Nat`, and the distinction between a natural
  number and an explicitly adjoined index.
- a generic componentwise zero condition: a pair is zero iff both components
  are zero, and a one-zero/one-nonzero pair is not zero;
- centered reflection arithmetic, including the exchange of tenths values
  0.7 and 0.3;
- the exact two-tenths exponent shift and conditional factorization of an
  abstract numerator-growth scale;
- conditional transfer through an exact source/target bridge, provided both
  zerohood and axis correspondence are supplied.

These are genuine theorem statements with proof terms in Lean source. The
package has not been compiled or kernel-checked in this environment, so their
verification status is `WRITTEN_UNCHECKED`, not `KERNEL_VERIFIED`.

## Still open

There is no proof here of the analytic continuation or functional equation of
`ζ`, the Euler product nonvanishing theorem, the Hadamard product, a mollifier
estimate, the explicit formula, the Nyman–Beurling or Li criterion, the
de Bruijn–Newman equivalence, a Hilbert–Pólya operator, or RH itself. The
registries specify these as separate proof obligations. The known criteria
would yield RH only after their full hypotheses and all-index/all-height
claims were proved.

The application names (EEG, flutter, markets, epidemics, and the other listed
domains) receive only the defined coordinate pair. No theorem maps those
coordinates to measured outcomes. No concrete `ExactBridge` instance is
provided for `ζ`, `ξ`, a self-adjoint operator, or an application model. The
explicit-formula calculation in the catalog is not kernel-checked and its
Lean module proves only exponent bookkeeping under a stated abstract law.
