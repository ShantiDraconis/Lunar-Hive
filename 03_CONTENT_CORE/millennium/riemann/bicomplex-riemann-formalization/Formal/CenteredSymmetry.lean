/-!
Centered-coordinate form of the functional-equation reflection.

Coordinates are scaled by ten: `5` represents 1/2, and a displacement `d`
means real part `1/2+d/10`. Reflection `s ↦ 1-s` negates the displacement;
complex conjugation negates the ordinate. These are coordinate theorems. The
analytic fact that the completed zeta zero set has these symmetries remains a
separate theorem in complex analysis.
-/

import Lean

namespace BicomplexRiemann.CenteredSymmetry

structure Point where
  displacement : Int
  ordinate : Int
  deriving DecidableEq, Repr

def reflect (p : Point) : Point := ⟨-p.displacement, p.ordinate⟩
def conjugate (p : Point) : Point := ⟨p.displacement, -p.ordinate⟩

def isOnCriticalLine (p : Point) : Prop := p.displacement = 0

theorem reflection_involutive (p : Point) : reflect (reflect p) = p := by
  cases p
  simp [reflect]

theorem conjugation_involutive (p : Point) : conjugate (conjugate p) = p := by
  cases p
  simp [conjugate]

theorem reflection_preserves_off_line (p : Point)
    (h : ¬ isOnCriticalLine p) : ¬ isOnCriticalLine (reflect p) := by
  intro hr
  apply h
  change p.displacement = 0
  have : -p.displacement = 0 := hr
  omega

def pairedTenths (d : Int) : Int × Int := (5 + d, 5 - d)

theorem paired_tenths_exchange (d : Int) :
    pairedTenths (-d) = (pairedTenths d).swap := by
  simp [pairedTenths, Prod.swap]

theorem seven_and_three_are_reflections :
    (5 + 2, 5 - 2) = (7, 3) := by decide

end BicomplexRiemann.CenteredSymmetry
