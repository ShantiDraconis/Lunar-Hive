/-!
Exact componentwise lift contracts.

This module formalizes the elementary product-algebra meaning of a
bicomplex-valued function. A lifted value is zero exactly when both complex
components are zero. It deliberately does not define analytic continuation
or instantiate the function with the Riemann zeta function.
-/

import Lean

namespace BicomplexRiemann.ComponentLift

/-- A value in a two-component product algebra. -/
structure PairValue (α : Type) where
  plus : α
  minus : α
  deriving Repr

/-- The componentwise zero predicate, stated without assuming a ring. -/
def IsZero {α : Type} [Zero α] (z : PairValue α) : Prop :=
  z.plus = 0 ∧ z.minus = 0

theorem pair_zero_iff_components_zero {α : Type} [Zero α]
    (z : PairValue α) : IsZero z ↔ z.plus = 0 ∧ z.minus = 0 := Iff.rfl

/-- If one component vanishes and the other does not, the pair is not zero. -/
theorem one_zero_component_not_pair_zero {α : Type} [Zero α]
    (z : PairValue α) (hPlus : z.plus = 0) (hMinus : z.minus ≠ 0) :
    ¬ IsZero z := by
  intro h
  exact hMinus (h.2)

/-- Integer model of the two real coordinates `sigma+b` and `sigma-b`. -/
def shiftedReals (sigma b : Int) : PairValue Int :=
  ⟨sigma + b, sigma - b⟩

theorem shifted_reals_zero_iff (sigma b : Int) :
    IsZero (shiftedReals sigma b) ↔ sigma + b = 0 ∧ sigma - b = 0 := Iff.rfl

theorem both_coordinates_half_force_center (sigma b : Int)
    (hPlus : (shiftedReals sigma b).plus = 5)
    (hMinus : (shiftedReals sigma b).minus = 5) :
    sigma = 5 ∧ b = 0 := by
  dsimp [shiftedReals] at hPlus hMinus
  omega

end BicomplexRiemann.ComponentLift
