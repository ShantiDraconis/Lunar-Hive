/-!
Abstract contract for transferring zero-location statements across a bridge.

The structure records the exact obligations a proposed analytic or spectral
construction must discharge. A theorem using the contract is conditional on
those fields; this module supplies no instance for zeta, an operator, or any
application model.
-/

namespace BicomplexRiemann.BridgeContracts

structure ExactBridge (Source Target : Type) where
  map : Source → Target
  sourceZero : Source → Prop
  targetZero : Target → Prop
  sourceOnLine : Source → Prop
  targetOnAxis : Target → Prop
  zeros_correspond : ∀ x, sourceZero x ↔ targetZero (map x)
  line_corresponds : ∀ x, sourceOnLine x ↔ targetOnAxis (map x)

/-- A genuine bridge transports both zerohood and the distinguished axis. -/
theorem source_zero_off_line_implies_target_zero_off_axis
    {Source Target : Type} (B : ExactBridge Source Target) (x : Source)
    (hz : B.sourceZero x) (ho : ¬ B.sourceOnLine x) :
    B.targetZero (B.map x) ∧ ¬ B.targetOnAxis (B.map x) := by
  constructor
  · exact (B.zeros_correspond x).mp hz
  · intro ht
    exact ho ((B.line_corresponds x).mpr ht)

/-- Conversely, a target zero off its axis yields a source zero off its line. -/
theorem target_zero_off_axis_implies_source_zero_off_line
    {Source Target : Type} (B : ExactBridge Source Target) (x : Source)
    (hz : B.targetZero (B.map x)) (ho : ¬ B.targetOnAxis (B.map x)) :
    B.sourceZero x ∧ ¬ B.sourceOnLine x := by
  constructor
  · exact (B.zeros_correspond x).mpr hz
  · intro hs
    exact ho ((B.line_corresponds x).mp hs)

/-- If every target zero lies on its axis, the exact bridge implies the
source zero-location theorem. The target theorem must be supplied separately. -/
theorem target_axis_theorem_transfers
    {Source Target : Type} (B : ExactBridge Source Target)
    (hTarget : ∀ y, B.targetZero y → B.targetOnAxis y) :
    ∀ x, B.sourceZero x → B.sourceOnLine x := by
  intro x hx
  apply (B.line_corresponds x).mpr
  apply hTarget
  exact (B.zeros_correspond x).mp hx

end BicomplexRiemann.BridgeContracts
