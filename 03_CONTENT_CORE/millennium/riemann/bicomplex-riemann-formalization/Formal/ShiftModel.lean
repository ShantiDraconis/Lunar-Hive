/-!
Shared fixed-point arithmetic for the proposed application bridges.

Coordinates are stored in tenths so that 0.5, 0.3, and 0.7 are represented
exactly by 5, 3, and 7. This file proves arithmetic only; it assigns no
physical or social meaning to these values.
-/

import Formal.BicomplexLift

namespace BicomplexRiemann

/-- The user's effective-coordinate convention, in tenths. -/
def effectiveTenths (sigma b : Int) : Int := sigma - b

/-- The two idempotent real coordinates, ordered as sigma+b, sigma-b. -/
def idempotentRealPair (sigma b : Int) : Int × Int :=
  (sigma + b, sigma - b)

/-- The user's proposed second-universe shift: sigma=0.5, b=-0.2. -/
theorem second_universe_pair : idempotentRealPair 5 (-2) = (3, 7) := by
  decide

theorem effective_second_universe_is_seven_tenths :
    effectiveTenths 5 (-2) = 7 := by
  decide

theorem opposite_component_is_three_tenths :
    effectiveTenths 5 2 = 3 := by
  decide

/-- The effective coordinate agrees with the minus idempotent projection. -/
theorem effective_is_minus_component (sigma t b : Int) :
    effectiveTenths sigma b = (componentMinus sigma t b).1 := by
  rfl

/-- The plus idempotent projection has real coordinate sigma+b. -/
theorem plus_component_is_sigma_add_b (sigma t b : Int) :
    (componentPlus sigma t b).1 = sigma + b := by
  rfl

end BicomplexRiemann
