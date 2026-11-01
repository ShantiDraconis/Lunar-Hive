/-!
Elementary bicomplex coordinate calculations over integers.

This file checks algebraic identities only. It does not define the analytic
continuation of zeta or prove any statement about its zeros.
-/

namespace BicomplexRiemann

/-- Coordinates `r + i*iPart + j*jPart + (ij)*kPart`, with commuting `i,j`
and `i² = j² = -1`. -/
structure BC where
  re : Int
  iPart : Int
  jPart : Int
  kPart : Int
  deriving DecidableEq, Repr

def zero : BC := ⟨0, 0, 0, 0⟩
def one : BC := ⟨1, 0, 0, 0⟩
def basisI : BC := ⟨0, 1, 0, 0⟩
def basisJ : BC := ⟨0, 0, 1, 0⟩
def basisK : BC := ⟨0, 0, 0, 1⟩

def add (x y : BC) : BC :=
  ⟨x.re + y.re, x.iPart + y.iPart, x.jPart + y.jPart,
    x.kPart + y.kPart⟩

def neg (x : BC) : BC :=
  ⟨-x.re, -x.iPart, -x.jPart, -x.kPart⟩

def sub (x y : BC) : BC := add x (neg y)

/-- Bicomplex multiplication in the basis `1,i,j,k`, where `k=ij`. -/
def mul (x y : BC) : BC :=
  ⟨ x.re * y.re - x.iPart * y.iPart - x.jPart * y.jPart
        + x.kPart * y.kPart,
    x.re * y.iPart + x.iPart * y.re - x.jPart * y.kPart
        - x.kPart * y.jPart,
    x.re * y.jPart + x.jPart * y.re - x.iPart * y.kPart
        - x.kPart * y.iPart,
    x.re * y.kPart + x.kPart * y.re + x.iPart * y.jPart
        + x.jPart * y.iPart ⟩

theorem i_sq : mul basisI basisI = neg one := by decide
theorem j_sq : mul basisJ basisJ = neg one := by decide
theorem ij_eq_k : mul basisI basisJ = basisK := by decide
theorem ji_eq_k : mul basisJ basisI = basisK := by decide
theorem k_sq : mul basisK basisK = one := by decide

/-- The two nonzero idempotent factors multiply to zero. -/
theorem idempotent_zero_divisors :
    mul (add one basisK) (sub one basisK) = zero := by decide

theorem one_add_k_ne_zero : add one basisK ≠ zero := by decide
theorem one_sub_k_ne_zero : sub one basisK ≠ zero := by decide

/-- Embed `a + i b` in the bicomplex algebra's first complex plane. -/
def complexEmbed (a b : Int) : BC := ⟨a, b, 0, 0⟩
def secondPlaneEmbed (a b : Int) : BC := ⟨a, 0, b, 0⟩

def iTimes (x : BC) : BC := mul basisI x

/-- `i(a+ib) = -b + ia`; the second imaginary coordinate becomes real. -/
theorem i_mul_complex (a b : Int) :
    iTimes (complexEmbed a b) = ⟨-b, a, 0, 0⟩ := by
  simp [iTimes, mul, basisI, complexEmbed]

/-- With an independent commuting `j`, multiplication by `i` creates a `k=ij`
coordinate; the scalar real coordinate is not shifted. -/
theorem i_mul_second_plane (a b : Int) :
    iTimes (secondPlaneEmbed a b) = ⟨0, a, 0, b⟩ := by
  simp [iTimes, mul, basisI, secondPlaneEmbed]

theorem real_minus_one_plus_i_complex_y (a b : Int) :
    (add (complexEmbed (-1) 0) (iTimes (complexEmbed a b))).re = -1 - b := by
  simp [add, i_mul_complex, complexEmbed]

/-- If `y` is real, changing its value changes only the imaginary coordinate. -/
theorem real_minus_one_plus_i_real_y (a : Int) :
    (add (complexEmbed (-1) 0) (iTimes (complexEmbed a 0))).re = -1 := by
  simp [add, i_mul_complex, complexEmbed]

theorem real_minus_one_plus_i_independent_j (a b : Int) :
    (add (complexEmbed (-1) 0) (iTimes (secondPlaneEmbed a b))).re = -1 := by
  simp [add, i_mul_second_plane, complexEmbed]

/-- The real part becomes `2` exactly in the example `y = 0 - 3i`. -/
theorem complex_y_example_re_two :
    (add (complexEmbed (-1) 0)
      (iTimes (complexEmbed 0 (-3)))).re = 2 := by
  decide

/-- The two idempotent components of `σ + it + kb` have real coordinates
`σ+b` and `σ-b`. -/
def componentPlus (sigma t b : Int) : Int × Int := (sigma + b, t)
def componentMinus (sigma t b : Int) : Int × Int := (sigma - b, t)

theorem projection_b_zero (sigma t : Int) :
    componentPlus sigma t 0 = (sigma, t) ∧
    componentMinus sigma t 0 = (sigma, t) := by
  simp [componentPlus, componentMinus]

end BicomplexRiemann
