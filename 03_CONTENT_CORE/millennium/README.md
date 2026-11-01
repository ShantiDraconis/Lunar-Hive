# Millennium Problems

## Overview

This directory contains observational analysis and documentation related to the **Millennium Prize Problems** — seven major unsolved mathematical challenges identified by the Clay Mathematics Institute.

**We do not claim to solve these problems.** We examine them as boundary phenomena that reveal how mathematical frameworks work at their limits.

---

## Contents

### `/riemann/`
Riemann Hypothesis and its connections to prime number theory, complex analysis, and limit behavior.

**Status**: Formalization package and bridge index published  
**Key files**:
- [`riemann/README.md`](riemann/README.md) — Scope, bridge map, and verification status
- [`riemann/PUBLIC_BRIDGE_INDEX.md`](riemann/PUBLIC_BRIDGE_INDEX.md) — Source-to-target map
- [`riemann/bicomplex-riemann-formalization/`](riemann/bicomplex-riemann-formalization/) — 24 individual source, registry, and Lean files
- [`riemann/bicomplex-riemann-formalization/FORMAL_PROOF_STATUS.md`](riemann/bicomplex-riemann-formalization/FORMAL_PROOF_STATUS.md) — Per-claim status

The package contains algebraic coordinate lemmas and explicit open obligations. It does not prove RH or validate the empirical application interpretations.

### `/p_vs_np/`
P vs NP problem: computational complexity, verification vs. discovery, algorithmic limits.

**Status**: Planned  

### `/navier_stokes/`
Navier-Stokes existence and smoothness: fluid dynamics, collapse in continuous systems.

**Status**: Planned  

### Others
Additional Millennium Problems (Yang-Mills, Birch and Swinnerton-Dyer, Hodge Conjecture) may be added as content develops.

---

## Approach

### What We Do
- Observe structural patterns
- Note connections to other axes (especially 0/0 and engineering)
- Document approaches and their boundaries
- Learn from failure modes

### What We Don't Do
- Claim to solve these problems without rigorous proof
- Propose solutions without expert review
- Oversimplify for popularity
- Pretend they're easy

---

## Resources

**Primary**: Clay Mathematics Institute (http://www.claymath.org/millennium-problems)

**Guide**: See `/docs/axes/MILLENNIUM_PROBLEMS.md` for overview and resources

---

## Contributing

If you have rigorous mathematical insights:
1. Read existing content
2. Check evidence standards (`/docs/policies/EVIDENCE_AND_CITATION_STANDARD.md`)
3. Propose via issue or discussion
4. Speculation must be labeled

We welcome deep analysis, not restatements.

---

**Status**: Early development (2025)
