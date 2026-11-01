/-!
Index of proof terms already present in this package.

These theorems re-export the proved algebraic/conditional results under one
module. They do not add analytic assumptions or claim RH.
-/

import Formal.BicomplexLift
import Formal.ShiftModel
import Formal.ApplicationBridges
import Formal.AnalyticBridgeContracts
import Formal.AfterInfinity
import Formal.ComponentLift
import Formal.CenteredSymmetry
import Formal.BridgeContracts
import Formal.ExplicitFormulaScaling

namespace BicomplexRiemann.ProofMap

theorem bicomplex_zero_divisor_identity :
    _root_.BicomplexRiemann.mul
      (_root_.BicomplexRiemann.add _root_.BicomplexRiemann.one _root_.BicomplexRiemann.basisK)
      (_root_.BicomplexRiemann.sub _root_.BicomplexRiemann.one _root_.BicomplexRiemann.basisK)
      = _root_.BicomplexRiemann.zero :=
  _root_.BicomplexRiemann.idempotent_zero_divisors

theorem second_universe_shift_is_seven_tenths :
    _root_.BicomplexRiemann.effectiveTenths 5 (-2) = 7 :=
  _root_.BicomplexRiemann.effective_second_universe_is_seven_tenths

theorem paired_component_coordinates_are_three_and_seven :
    _root_.BicomplexRiemann.idempotentRealPair 5 (-2) = (3, 7) :=
  _root_.BicomplexRiemann.second_universe_pair

theorem all_registered_applications_have_the_assigned_pair
    (d : _root_.BicomplexRiemann.ApplicationBridge) :
    _root_.BicomplexRiemann.bridgeCoordinates d = (3, 7) :=
  _root_.BicomplexRiemann.bridge_coordinates_are_three_and_seven d

theorem symmetry_assumptions_give_four_point_orbit
    {S : _root_.BicomplexRiemann.AnalyticContracts.CenteredPoint → Prop}
    (hS : _root_.BicomplexRiemann.AnalyticContracts.SymmetryAssumptions S)
    (p : _root_.BicomplexRiemann.AnalyticContracts.CenteredPoint)
    (hp : S p) :
    S p ∧
      S (_root_.BicomplexRiemann.AnalyticContracts.conjugate p) ∧
      S (_root_.BicomplexRiemann.AnalyticContracts.reflect p) ∧
      S (_root_.BicomplexRiemann.AnalyticContracts.reflect
        (_root_.BicomplexRiemann.AnalyticContracts.conjugate p)) :=
  _root_.BicomplexRiemann.AnalyticContracts.four_point_orbit hS p hp

theorem two_half_components_force_center
    (sigma b : Int)
    (hPlus : sigma + b = 5)
    (hMinus : sigma - b = 5) :
    sigma = 5 ∧ b = 0 :=
  _root_.BicomplexRiemann.AnalyticContracts.both_half_components_force_center
    sigma b hPlus hMinus

theorem every_natural_has_a_larger_natural (n : Nat) :
    n < Nat.succ n :=
  _root_.BicomplexRiemann.AfterInfinity.every_natural_has_a_larger_natural n

theorem adjoined_after_all_is_not_a_natural :
    ¬ ∃ n : Nat,
      _root_.BicomplexRiemann.AfterInfinity.afterAll =
        _root_.BicomplexRiemann.AfterInfinity.ExtendedIndex.finite n :=
  _root_.BicomplexRiemann.AfterInfinity.afterAll_is_not_finite

theorem bicomplex_pair_zero_iff_both_components_zero
    {α : Type} [Zero α] (z : _root_.BicomplexRiemann.ComponentLift.PairValue α) :
    _root_.BicomplexRiemann.ComponentLift.IsZero z ↔
      z.plus = 0 ∧ z.minus = 0 :=
  _root_.BicomplexRiemann.ComponentLift.pair_zero_iff_components_zero z

theorem seven_three_reflection_pair :
    _root_.BicomplexRiemann.CenteredSymmetry.pairedTenths 2 = (7, 3) := by
  decide

theorem off_line_growth_exponent_shift_is_two_tenths :
    _root_.BicomplexRiemann.ExplicitFormulaScaling.exponentShiftTenths = 2 :=
  _root_.BicomplexRiemann.ExplicitFormulaScaling.off_line_shift_is_two_tenths

end BicomplexRiemann.ProofMap
