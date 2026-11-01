# Formula catalog for the recovered chain

This catalog collects the formulas actually used or proposed in this project,
then gives the standard zeta formulas needed to state the classical bridges.
The tags distinguish exact identities from model proposals and from theorems
that are known mathematically but not proved by this Lean package.

## 1. Shared coordinate model

### Limit term

The expression from the conversation is

\[
E_{\mathrm{fail}}=\lim_{t\to\infty}0=0.
\]

As a constant zero term, it changes no function and creates no zero of
\(\zeta\). To alter a zero set, a nonzero, explicitly defined analytic term
and a theorem about its zeros would be needed.

### Bicomplex algebra

\[
i^2=j^2=-1,\qquad ij=ji=k,\qquad k^2=1,
\]
\[
e_+=\frac{1+k}{2},\qquad e_-=\frac{1-k}{2},\qquad
e_+e_-=0,
\]
\[
(1+k)(1-k)=1-k^2=0.
\]

In this algebra both factors \(1+k\) and \(1-k\) are nonzero zero divisors.
The identity is exact algebra; a physical cancellation interpretation needs
separate equations for the physical system.

For \(z=\sigma+it+kb\), the idempotent coordinates are

\[
s_+=(\sigma+b)+it,\qquad s_-=(\sigma-b)+it.
\]

The shared proposal names the second coordinate

\[
\sigma_{\mathrm{eff}}=\sigma-b.
\]

With tenths as an exact integer scale, \(\sigma=5\) represents 0.5 and
\(b=-2\) represents −0.2:

\[
5-(-2)=7\;(0.7),\qquad 5-2=3\;(0.3),\qquad
(\sigma+b,\sigma-b)=(3,7).
\]

These are coordinate identities conditional on the chosen model; they do not
show a measured system has those coordinates.

For a componentwise lift of an ordinary complex function \(f\), the exact
algebraic model is

\[
\mathcal F(s,b)=f(s+b)e_+ + f(s-b)e_-,\qquad
\mathcal F(s,b)=0
\iff f(s+b)=0\ \text{and}\ f(s-b)=0.
\]

If just one component vanishes and the other does not, \(\mathcal F(s,b)\)
is a nonzero zero divisor. `Formal/ComponentLift.lean` proves the generic
two-component zero condition; it does not establish that this proposed
analytic expression is an RH-preserving extension of \(\zeta\).

For a componentwise lift of an ordinary complex function \(f\), the exact
algebraic model is

\[
\mathcal F(s,b)=f(s+b)e_+ + f(s-b)e_-,\qquad
\mathcal F(s,b)=0
\iff f(s+b)=0\ \text{and}\ f(s-b)=0.
\]

If just one component vanishes and the other does not, \(\mathcal F(s,b)\)
is a nonzero zero divisor. `Formal/ComponentLift.lean` proves the generic
two-component zero condition; it does not establish that this proposed
analytic expression is an RH-preserving extension of \(\zeta\).

### Classical zero symmetries and RH

For a nontrivial zero \(\rho=\sigma+i\gamma\), the standard symmetries are
conjugation and reflection across \(\operatorname{Re}s=1/2\):

\[
\rho,\quad \bar\rho=\sigma-i\gamma,\quad
1-\rho=1-\sigma-i\gamma,\quad
1-\bar\rho=1-\sigma+i\gamma.
\]

The Riemann Hypothesis is

\[
\zeta(\rho)=0,\quad 0<\operatorname{Re}\rho<1
\quad\Longrightarrow\quad \operatorname{Re}\rho=\frac12.
\]

For Chebyshev's \(\psi\)-function, one standard explicit-formula shape is

\[
\psi(x)=x-\sum_\rho\frac{x^\rho}{\rho}+\text{lower-order/pole terms},
\qquad x>1,
\]

with a specified limiting convention for the zero sum. If
\(\rho=\beta+i\gamma\), then

\[
\left|\frac{x^\rho}{\rho}\right|=\frac{x^\beta}{|\rho|}.
\]

For the conjugate pair \(\rho,\bar\rho\), its contribution is
\(-2\operatorname{Re}(x^\rho/\rho)\), whose magnitude is at most
\(2x^\beta/|\rho|\). This is an amplitude bound for that pair, not the
actual total prime-counting error: the phase varies with \(\gamma\log x\),
and contributions from different zeros can cancel.

For the illustrative equal-ordinate comparison
\(\rho_0=0.5+14.13i\) and a **hypothetical** \(\rho_1=0.7+14.13i\), the
exact ratio of the
single-zero amplitude bounds is

\[
\frac{x^{0.7}/|\rho_1|}{x^{0.5}/|\rho_0|}
=x^{0.2}\frac{|\rho_0|}{|\rho_1|}.
\]

The denominator ratio is close to 1 here, so the rounded comparisons that
replace both moduli by about 14 give \(100^{0.2}\approx2.512\) and
\((10^{12})^{0.2}\approx251.189\). Using those rounded denominators, the
individual amplitudes are about 0.71 versus 1.78 at \(x=100\), and about
\(7.08\times10^4\) versus \(1.78\times10^7\) at \(x=10^{12}\). These are
not predictions that \(\pi(x)-\operatorname{Li}(x)\) itself is exactly
251 times larger at a particular \(x\).

An off-line zero of the **Riemann zeta function** would contradict RH and
therefore the RH-equivalent global error bounds, such as
\(\psi(x)-x=O(x^{1/2}\log^2x)\). The one-term calculation illustrates the
scale; the implication from a zero to failure of a global bound uses the
analytic zero-count/explicit-formula theory, not just this numerical ratio.
The corresponding classical bound for \(\pi(x)-\operatorname{Li}(x)\) is
also an RH equivalence, but deriving it from \(\psi\) requires partial
summation. See the NIST DLMF explicit-formula section and the classical
von Koch equivalence in the references below.

The example near \(0.8+85i\) attributed to Davenport–Heilbronn belongs to a
different function, not to \(\zeta(s)\). It can illustrate that a functional
equation and reflection symmetry alone need not force all zeros onto the
symmetry line; it supplies no off-line zero of the Riemann zeta function.

The ordinary-complex calculation
\[
0.5+i(14.13-0.2i)=0.7+14.13i
\]
uses the same unit \(i\) twice; it is not multiplication by an independent
bicomplex unit \(j\). In the package convention
\(z=\sigma+it+kb\), the choice \(b=-0.2\) gives components 0.3 and 0.7.
For the hyperbolic coordinate, with \(k^2=1\) and \(x>0\), the matching
formal exponential identity is

\[
x^{0.5-0.2k}
=x^{0.5}\bigl(\cosh(0.2\log x)-k\sinh(0.2\log x)\bigr)
=x^{0.3}e_+ + x^{0.7}e_-.
\]

Thus the minus component carries the factor \(x^{0.7}\), and the plus
component carries \(x^{0.3}\), for \(b=-0.2\). This is a bicomplex
algebra/analytic expression only after a
power and exponential are defined in that algebra. It does **not** establish
a bicomplex explicit formula for primes: such a formula would require a
separate derivation, convergence theorem, and a proven relation to classical
\(\zeta\). `Formal/ExplicitFormulaScaling.lean` proves the exact tenths
exponent shift and its abstract multiplicative-law consequence, not the
complex-analysis estimate or numerical approximations.

The equation written in the lost conversation, \(2\operatorname{Re}(s)=-s\),
does not express this symmetry. If \(s=\sigma+it\), literal equality forces
\(2\sigma=-\sigma\) and \(t=0\), hence \(s=0\). The correct real-coordinate
reflection is \(\sigma\mapsto1-\sigma\), or in centered coordinates
\(x=\sigma-\tfrac12\), \(x\mapsto-x\).

The abstract bridge contract in `Formal/BridgeContracts.lean` requires both
equivalences

\[
Z_S(x)\iff Z_T(Tx),\qquad C_S(x)\iff C_T(Tx),
\]

for source/target zerohood and source-line/target-axis membership. Under those
hypotheses, a theorem that every target zero lies on its axis transfers to a
theorem that every source zero lies on its line. The contract is generic; no
map or equivalence for \(\zeta\), \(\xi\), or an application model is
provided. See `FORMAL_BRIDGE_CONTRACTS.md` for the proof obligations.

## 2. Proposed application mappings (items 7–15)

In the table, \(\sigma_{\mathrm{eff}}=\sigma-b\) is the proposed common
coordinate map. The right-hand interpretations are proposals from the
conversation, not theorems derived from the listed domain equations.

| # | Domain | Formula or assignment in the proposal | Status / precise boundary |
|---|---|---|---|
| 7 | Belousov–Zhabotinsky chemistry | \(\operatorname{Re}>0\mapsto\) oscillation; \(b=[\mathrm{BrO_3^-}]\) | An oscillating reaction is a real chemical phenomenon. No kinetics equation or scaling from bromate concentration to \(b\) has been supplied. |
| 8 | SIR epidemic | \(\delta=+0.2\mapsto0.7+14i\) (surge); \(\delta=-0.2\mapsto0.3+14i\) (extinction); four vaccine/wave scenarios | These complex coordinates are proposed. A standard SIR \(R_0\) is real; the imaginary ordinate must be a separately defined spectral variable. |
| 9 | Acoustic echo | \(f=0.5\pm0.2+i\,440\,\mathrm{Hz}\); 0.7 proposed as growing echo, 0.3 as decaying echo | Frequency units and a dimensionless real coordinate cannot be added without normalization. A room transfer function and boundary conditions are missing. |
| 10 | Laser | \(s=\sigma+i\omega\); \(\sigma>0\) proposed as growth; \(b\ne0\) as misalignment; \(j\) as coupled second mirror | No cavity/gain/loss equation has been supplied to derive these assignments. |
| 11 | Seismic wave | \(u(x,t)=e^{i(kx-\omega t)}\), \(k=k_r+ik_i\), \(k_i\ne0\) | Under this convention and real \(\omega\), the amplitude factor is \(e^{-k_i x}\). Attenuation does not imply disappearance on one side and reappearance on the other. Here \(k\) is a wave number, not the bicomplex unit \(k=ij\). |
| 12 | EEG | \(s=0.5\pm0.2+i\,10\,\mathrm{Hz}\); 0.7 proposed as seizure, 0.3 as deep sleep; \(b\) as thalamo-cortical coupling | A 10 Hz rhythm is a frequency description; the 0.7/0.3 clinical assignments are not established by this formula. Units need normalization and a validated signal model. |
| 13 | Aeroelastic flutter | \(\sigma>0\) proposed as growing wing vibration; \((1+k)(1-k)=0\) proposed as torsion-flexion cancellation | Positive real growth rate implies instability only within a specified linearized modal model. The bicomplex identity does not derive a structural equation. |
| 14 | Economy | 0.7 proposed as bubble, 0.3 as crash; \(b\) as leverage in universe \(j\); 2008 described as both coordinates at once | No economic state equation or calibration is supplied. “Bought and sold” does not algebraically cancel without a defined quantity and model. |
| 15 | Social spread | \(R_0=0.5+\delta\); \(\delta=\pm0.2\mapsto0.7/0.3\); four algorithm/sharing combinations | In standard contagion models \(R_0\) is real; both 0.7 and 0.3 are below the usual threshold 1. The term \(14i\) cannot be part of a conventional reproduction number. |

### Standard comparison equations (not fitted to the proposed bridges)

A continuous-time linear mode with exponent \(\lambda=\sigma+i\omega\) obeys

\[
\dot q=\lambda q,\qquad q(t)=q(0)e^{\lambda t},\qquad
|q(t)|=|q(0)|e^{\sigma t}.
\]

Thus \(\sigma>0\) means growth **in this mode convention**. A physical
acoustic, laser, EEG, or aeroelastic model still has to derive its own
operator/eigenvalue \(\lambda\).

For the classical homogeneous-mixing SIR model,

\[
\dot S=-\beta\frac{SI}{N},\qquad
\dot I=\beta\frac{SI}{N}-\gamma I,\qquad
\dot R=\gamma I,
\]

and the effective reproduction number is

\[
R_t=\frac{\beta S(t)}{\gamma N},\qquad
R_0=\frac{\beta S(0)}{\gamma N}
\quad\text{(equal to }\beta/\gamma\text{ if }S(0)=N\text{)}.
\]

These quantities are real and dimensionless in this model. The proposed
complex coordinates \(0.7+14i\) and \(0.3+14i\) are not standard SIR
reproduction numbers. No differential-equation model was supplied for the
Belousov–Zhabotinsky, economic, or social-network assignments; the catalog
does not infer one from the coordinate map.

For a wave with complex wave number, the amplitude calculation is

\[
i(kx-\omega t)=i(k_r x-\omega t)-k_i x,
\qquad
\left|e^{i(kx-\omega t)}\right|=e^{-k_i x}
\quad(\omega\in\mathbb R).
\]

For any frequency \(f\) measured in hertz, angular frequency is
\(\omega=2\pi f\) radians per second. A dimensionless spectral coordinate
requires a stated time scale before a frequency is inserted into it.

The four binary social scenarios can be indexed as

\[
\{0,1\}_{\mathrm{algorithm}}\times
\{0,1\}_{\mathrm{sharing}},
\]

which gives four combinations. This counting identity does not determine
which combination becomes viral.

## 3. Classical zeta formulas referenced by the bridge files

### Definition, continuation, and Euler product

For \(\operatorname{Re}s>1\),

\[
\zeta(s)=\sum_{n=1}^{\infty}n^{-s}
       =\prod_{p\;\mathrm{prime}}(1-p^{-s})^{-1}.
\]

The analytic continuation is meromorphic on \(\mathbb C\), with a simple
pole at \(s=1\) and residue 1. The Euler product gives nonvanishing for
\(\operatorname{Re}s>1\), not a zero-free theorem for the critical strip.

### Functional equation and completed function

One standard functional equation is

\[
\zeta(1-s)=2(2\pi)^{-s}\cos\!\left(\frac{\pi s}{2}\right)
\Gamma(s)\zeta(s),\qquad s\ne0,1.
\]

Equivalently, for

\[
\xi(s)=\frac12s(s-1)\Gamma\!\left(\frac{s}{2}\right)
\pi^{-s/2}\zeta(s),
\]

the symmetry is

\[
\xi(s)=\xi(1-s).
\]

The trivial zeros of \(\zeta\) are \(s=-2n\), \(n=1,2,\ldots\). The
nontrivial zeros are in the critical strip \(0<\operatorname{Re}s<1\).

### Hadamard product

For the order-one entire completed function, the genus-one product has the
form

\[
\xi(s)=e^{A+Bs}\prod_{\rho}E_1\!\left(\frac{s}{\rho}\right),
\qquad E_1(z)=(1-z)e^z,
\]

with zeros repeated according to multiplicity and the product taken with the
convergence convention required by the factorization theorem. Constants and
normalization must be fixed when formalizing this identity.

### Zero count and explicit formula

The Riemann–von Mangoldt formula is

\[
N(T)=\frac{T}{2\pi}\log\!\left(\frac{T}{2\pi}\right)
      -\frac{T}{2\pi}+O(\log T),
\]

where \(N(T)\) counts nontrivial zeros with \(0<\operatorname{Im}\rho\le T\),
including multiplicity. It counts zeros; it does not show each zero lies on
the critical line.

One standard explicit-formula shape is

\[
\psi_0(x)=x-\sum_{\rho}\frac{x^\rho}{\rho}
          -\log(2\pi)-\frac12\log(1-x^{-2}),\qquad x>1,
\]

with the zero sum interpreted using the stated symmetric limiting
convention. At prime powers, \(\psi_0\) uses half weight. The convergence
convention and endpoint convention are part of the theorem, not optional
notation.

### Equivalent criteria

The Nyman–Beurling form uses

\[
\rho_\theta(x)=\left\{\frac{\theta}{x}\right\}
                 -\theta\left\{\frac1x\right\},\qquad 0<\theta\le1,
\]

and the criterion states that RH is equivalent to

\[
\mathbf 1_{(0,1)}\in
\overline{\operatorname{span}\{\rho_\theta:0<\theta\le1\}}^{\,L^2(0,1)}.
\]

Li’s coefficients can be written

\[
\lambda_n=\sum_{\rho}\left[1-\left(1-\frac1\rho\right)^n\right],
\qquad n=1,2,\ldots,
\]

with the zero sum interpreted in the criterion’s convergence convention.
RH is equivalent to \(\lambda_n\ge0\) for every positive integer \(n\).
Checking finitely many \(n\) is not enough.

For the de Bruijn–Newman family \(H_t\),

\[
H_t\text{ has only real zeros}\quad\Longleftrightarrow\quad t\ge\Lambda,
\]
\[
\mathrm{RH}\quad\Longleftrightarrow\quad\Lambda\le0.
\]

Since the proven lower bound is \(\Lambda\ge0\), this is equivalently
\(\mathrm{RH}\Longleftrightarrow\Lambda=0\). This equivalence identifies
another target; it does not prove \(\Lambda=0\).

## 4. Formula status

| Status | Meaning |
|---|---|
| Exact algebra | Follows from the defined integer/bicomplex operations. |
| Standard analytic identity | Classical formula stated with its domain and convergence conditions; not Lean-verified in this package. |
| Conditional theorem | Follows only after the listed assumptions are supplied. |
| Proposed application map | A suggested correspondence; no domain-specific derivation is supplied. |
| Open theorem | A genuine analytic/spectral result still requiring a proof. |

## References

- NIST Digital Library of Mathematical Functions, [zeta definition and Euler
  product](https://dlmf.nist.gov/25.2), [functional equation and xi function](https://dlmf.nist.gov/25.4), and [zero distribution](https://dlmf.nist.gov/25.10).
- NIST Digital Library of Mathematical Functions, [§25.16: prime-counting
  functions and explicit formulas](https://dlmf.nist.gov/25.16).
- Mathematical Association of America, [Equivalents of the Riemann Hypothesis,
  Volume Two: Analytic Equivalents](https://old.maa.org/node/1401175), for
  classical prime-counting error-term equivalences.
- Helge von Koch, [Sur la distribution des nombres premiers](https://www.numdam.org/item/ASENS_1901_3_18__1_0/), *Annales scientifiques de l'École Normale Supérieure* (1901), establishing a classical RH-equivalent prime-counting error estimate.
- Xian-Jin Li, [The Positivity of a Sequence of Numbers and the Riemann
  Hypothesis](https://www.sciencedirect.com/science/article/pii/S0022314X97921375),
  *Journal of Number Theory* 65 (1997), 325–333.
- Luis Báez-Duarte, [New versions of the Nyman–Beurling criterion for the
  Riemann hypothesis](https://doi.org/10.1155/S0161171202013248), 2002.
- Brad Rodgers and Terence Tao, [The de Bruijn–Newman constant is
  non-negative](https://doi.org/10.1017/fmp.2020.6), *Forum of Mathematics, Pi*
  8 (2020), e6.
