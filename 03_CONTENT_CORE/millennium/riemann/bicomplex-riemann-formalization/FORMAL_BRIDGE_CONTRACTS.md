# Exact proof obligations for the proposed bridges

## A. What a bridge must preserve

`Formal/BridgeContracts.lean` defines an abstract `ExactBridge`. An instance
must supply a map (T) from source objects to target objects and prove both

\[
Z_S(x)\iff Z_T(Tx),\qquad
C_S(x)\iff C_T(Tx),
\]

where (Z) is the relevant zero predicate and (C) is the distinguished-line
or spectral-axis predicate. The Lean theorem
`target_axis_theorem_transfers` then proves

\[
\bigl(\forall y,\ Z_T(y)\to C_T(y)\bigr)
\Longrightarrow
\bigl(\forall x,\ Z_S(x)\to C_S(x)\bigr).
\]

This is a conditional theorem schema. It contains no instance for the
classical zeta function. For RH, the source must be a precisely defined set of
nontrivial zeros of `ξ` (or an equivalent formulation), and the target must
have a theorem placing every corresponding target zero on its axis.

## B. Spectral route

The proposed Hilbert–Pólya route needs all of the following, not just a matrix
with suggestive eigenvalues:

1. Define a Hilbert space, a densely defined operator, and its domain.
2. Prove the operator is self-adjoint (formal symmetry alone is insufficient).
3. Define a spectral determinant or equivalent target zero function.
4. Prove its zeros correspond to the nontrivial zeros of `ξ`, with
   multiplicities and exceptional factors accounted for.
5. Prove the spectral axis theorem from self-adjointness and the chosen
   parameterization.
6. Instantiate `ExactBridge` and apply `target_axis_theorem_transfers`.

Items 1–5 are not in this package. A desired identity such as
`det(H - parameter(s)) = nonvanishing_factor(s) * ξ(s)` is a research
obligation, not a definition that can be assumed without proof.

## C. Dynamical-systems route

For a linearized mode

\[
\dot q=(\sigma+i\omega)q,\qquad
q(t)=q(0)e^{(\sigma+i\omega)t},\qquad
|q(t)|=|q(0)|e^{\sigma t},
\]

the sign of \(\sigma\) classifies growth or decay under this mode convention.
This is a valid stability statement after a real system has been linearized
and its eigenvalue computed. Identifying \(\sigma\) with
\(\Re(s)-1/2\) is a coordinate choice; it is not a theorem that the mode
characteristic function equals `ξ(s)`. Such equality and its zero-preserving
map are required to instantiate `ExactBridge`.

## D. Bicomplex lift route

The idempotent basis has

\[
e_+=(1+k)/2,\quad e_-=(1-k)/2,\quad e_+e_-=0.
\]

A lifted function value is componentwise, schematically

\[
\mathcal Z(s,b)=\zeta(s+b)e_+ + \zeta(s-b)e_-.
\]

The algebraic zero condition is

\[
\mathcal Z(s,b)=0
\iff \zeta(s+b)=0\ \text{and}\ \zeta(s-b)=0.
\]

If exactly one component vanishes, the value is a nonzero zero divisor, not
the zero element. `Formal/ComponentLift.lean` proves the component logic at a
generic product-value level; it does not establish that this displayed
analytic lift is holomorphic, compatible with classical `ζ`, or useful for
RH. Those are separate analytic obligations.

## E. Reflection and the 0.3/0.7 coordinates

In centered coordinates \(s=1/2+\delta+it\), the functional-equation
reflection sends \(\delta\) to \(-\delta\). Thus a hypothetical point at
real part \(0.7\) has a reflected point at \(0.3\), with the same imaginary
part; conjugation additionally changes the sign of the imaginary part. This
generates a symmetry orbit when the relevant zero-set closure theorems are
proved. It does not establish that either point is a zero, nor that
\(\delta=0\).

The entries 7–15 use tenths arithmetic and, in some entries, attach domain
labels to 0.7 and 0.3. Those labels (seizure/sleep, bubble/crash, viral/dead,
and similar interpretations) are hypotheses to model and validate, not
consequences of this reflection theorem.

## F. Explicit-formula scaling calculation

For a zero \(\rho=\beta+i\gamma\), the magnitude of its individual
\(\psi\)-formula term is \(x^\beta/|\rho|\). The conjugate pair contributes
an oscillatory real term bounded by \(2x^\beta/|\rho|\). Comparing
\(\beta=0.5\) and \(\beta=0.7\) at the same ordinate gives the exact
amplitude-bound ratio

\[
x^{0.2}\,\frac{|0.5+14.13i|}{|0.7+14.13i|},
\]

not just \(x^{0.2}\); the latter is the rounded approximation when both
denominators are replaced by about 14. The growth factors are approximately
2.512 at \(x=100\) and 251.189 at \(x=10^{12}\). The full zero sum has
oscillatory phases and can cancel, so this is not an exact value of the
prime-counting error at either input.

`Formal/ExplicitFormulaScaling.lean` proves `7-5=2` in tenths and proves
that an abstract numerator scale with an exponent-addition law factors as
`growth(7)=growth(5)*growth(2)`. The abstract law is a parameter, not a
formalization of real exponentials. The exact explicit formula, complex
moduli, numerical estimates, and RH-equivalent error theorem remain outside
the Lean development. Also, an off-line zero of the Davenport–Heilbronn
function is not a zero of Riemann's `ζ` and cannot be substituted into its
prime explicit formula.

The ordinary-complex expression
\(0.5+i(14.13-0.2i)=0.7+14.13i\) uses the same unit \(i\) inside and
outside the parentheses. In the independent-unit bicomplex convention,
\(b=-0.2\) means \(0.5+14.13i-0.2k\), whose idempotent real coordinates
are \(0.3\) and \(0.7\); the 0.7 value is the minus component. Accordingly,
\(x^{0.5-0.2k}=x^{0.3}e_+ + x^{0.7}e_-\). These expressions are not
interchangeable without specifying which imaginary unit and projection are
being used.

## G. Exact status by bridge family

| Family | Formal result in this archive | Missing theorem before it is a genuine bridge |
|---|---|---|
| Bicomplex coordinates | Product components and zero condition | Analytic lift of `ζ`/`ξ`, compatibility, complete zero characterization |
| RH reflection | Abstract reflection/conjugation orbit | Functional-equation theorem applied to the exact completed zero set |
| Stability | Standard modal growth equation in documentation | Derive and calibrate the domain operator; prove its characteristic function corresponds to `ξ` |
| Selberg/function-field analogies | Described in research notes/formula catalog | No transfer theorem from those distinct zeta functions to classical `ζ` |
| Items 7–15 | Shared registry arithmetic | Domain models, parameter estimates, validation, and a zero-preserving map |
| After infinity | Standard `Nat` has no final element; a fresh constructor is distinct | Specify a new structure and prove its relation to complex analysis and `ξ` |
| Classical RH criteria | Exact statements cataloged | Formalize the chosen criterion and prove its all-parameters hypothesis, not a finite sample |
| Explicit formula exponent scaling | Tenths exponent shift and abstract multiplicative factorization | Formalize the classical explicit formula, complex modulus bound, and global error-term implication |

## H. Proof integrity rules for future additions

- Do not fill a bridge field with the desired RH conclusion itself; that would
  only restate the goal.
- Keep assumptions visible in theorem signatures and status tables.
- Track poles, trivial zeros, multiplicity, convergence, exceptional factors,
  and parameter domains when moving between functions.
- Distinguish a nonzero zero divisor from the zero element.
- Do not translate a finite numerical check into a universal zero-location
  theorem.
- Before calling any source kernel-checked, compile the exact archive with the
  pinned Lean toolchain and inspect the theorem assumptions.
