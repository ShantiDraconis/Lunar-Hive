/-!
Boundary between standard natural numbers and an explicitly adjoined symbol.

The adjoined constructor below is a new index, not a natural number and not a
claim about analytic continuation or zeta zeros.
-/

namespace BicomplexRiemann.AfterInfinity

theorem every_natural_has_a_larger_natural (n : Nat) : n < Nat.succ n :=
  Nat.lt_succ_self n

inductive ExtendedIndex where
  | finite : Nat → ExtendedIndex
  | adjoinedAfterAll : ExtendedIndex
  deriving DecidableEq, Repr

def afterAll : ExtendedIndex := .adjoinedAfterAll

theorem afterAll_is_not_finite : ¬ ∃ n : Nat, afterAll = .finite n := by
  intro h
  rcases h with ⟨n, hEq⟩
  cases hEq

end BicomplexRiemann.AfterInfinity
