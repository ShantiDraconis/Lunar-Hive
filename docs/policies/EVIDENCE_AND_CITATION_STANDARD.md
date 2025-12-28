# Evidence and Citation Standard

## Purpose

Claims require support. This document defines what counts as evidence and how to cite it properly.

**Why this matters**: Without standards, speculation becomes fact and quality deteriorates.

---

## Types of Claims

### 1. Mathematical Statements

**Requirement**: Proof or derivation from axioms

**Acceptable Support**:
- Formal proof (with axioms stated)
- Reference to published theorem
- Derivation from established results

**Example**:
✓ "The limit of sin(x)/x as x→0 equals 1 (by L'Hôpital's rule)"  
✓ "In ZFC set theory, the axiom of choice implies..."  
✗ "It seems like this limit should be 1"  

**Citation Format**: `[Source Author, Title, Year, Section/Theorem]`

---

### 2. Empirical Claims

**Requirement**: Observable data or published research

**Acceptable Support**:
- Peer-reviewed research papers
- Documented observations
- Reproducible measurements
- Historical records

**Example**:
✓ "The Harappan civilization existed from ~3300-1300 BCE [Archaeological Survey of India]"  
✓ "Water boils at 100°C at standard pressure [thermodynamics textbook]"  
✗ "Ancient people definitely understood advanced mathematics"  

**Citation Format**: `[Author(s), "Title", Journal/Publisher, Year, DOI/URL]`

---

### 3. Hypotheses

**Requirement**: Logical structure and falsifiability criteria

**Acceptable Support**:
- Internal logical consistency
- Testable predictions
- Comparison to alternatives
- Evidence that would disprove it

**Example**:
✓ "Hypothesis: Symbol X represents sound /da/ because [frequency analysis]. Falsifiable by [finding contradictory contexts]"  
✗ "I think this symbol means something spiritual"  

**Label Required**: "**Hypothesis:**" at start of claim

---

### 4. Interpretations

**Requirement**: Clear reasoning from established facts

**Acceptable Support**:
- Logical inference from data
- Framework for interpretation
- Alternative interpretations considered
- Limitations acknowledged

**Example**:
✓ "Given symbols A, B, C appear together in 87% of inscriptions [data], one interpretation is grammatical function [reasoning], though they could also represent [alternative]"  
✗ "These symbols obviously mean family relationships"  

**Label Required**: "**Interpretation:**" or "**One reading:**"

---

### 5. Speculation

**Requirement**: Labeled as exploratory, not stated as fact

**Acceptable Support**:
- Analogies to known patterns
- Intuition based on experience
- Preliminary patterns

**Example**:
✓ "**Speculation**: The collapse behavior at 0/0 may suggest a deeper topological structure (exploratory, not established)"  
✗ "The collapse at 0/0 proves there's a hidden dimension"  

**Label Required**: "**Speculation:**" or "**Exploratory:**"

---

## Citation Requirements

### When Citation Is Required

**Always cite when**:
- Making factual claims about history, science, or mathematics
- Referencing published work
- Using data or measurements
- Building on others' ideas

**Citation not required for**:
- Original analysis (but label as such)
- Common knowledge (but be conservative)
- Personal experience (if labeled)

### How to Cite

#### Academic Papers
```
[Author(s), "Paper Title", Journal Name, Vol(Issue), Year, pp. X-Y]
DOI or URL if available
```

#### Books
```
[Author, Book Title, Publisher, Year, Chapter/Page]
ISBN if available
```

#### Websites
```
[Author/Organization, "Page Title", Website Name, Access Date, URL]
```

#### Mathematical References
```
[Author, Textbook/Paper, Year, Theorem X.Y or Section Z]
```

#### Historical Sources
```
[Author/Archive, Source Type, Date, Location]
```

---

## Evidence Quality Hierarchy

### Tier 1: Strongest
- Published peer-reviewed research
- Mathematical proofs
- Direct physical evidence
- Reproducible experiments

### Tier 2: Strong
- Scholarly books from reputable publishers
- Technical reports from recognized institutions
- Documented historical records
- Expert consensus in field

### Tier 3: Moderate
- Pre-prints (arXiv, bioRxiv, etc.)
- Conference proceedings
- Technical blogs from experts
- Well-documented case studies

### Tier 4: Weak
- Unpublished analyses
- Personal observations
- Anecdotal evidence
- Secondary sources without primary citation

### Tier 5: Unacceptable
- "Everyone knows..."
- "I read somewhere..."
- Social media posts without backup
- Wikipedia without checking original sources
- Opinion pieces without data

---

## Standards by Content Type

### Mathematics
- State axioms if non-standard
- Cite theorems used
- Show key steps in proofs
- Reference textbooks for standard results

### Harappan/Linguistics
- Cite symbol inventories
- Reference frequency analyses
- Link to archaeological sources
- Acknowledge competing theories

### Engineering
- Cite design principles
- Reference safety standards
- Link to case studies
- Include risk assessments

### Sustainability
- Cite resource data
- Reference environmental studies
- Link to international standards
- Include ethical frameworks

### Olympics/Culture
- Cite historical records
- Reference sociological studies
- Link to primary sources
- Acknowledge cultural sensitivity

---

## Common Mistakes to Avoid

### Over-Claiming
❌ "This proves that..." (when it only suggests)  
✓ "This evidence supports..." or "This is consistent with..."

### Under-Citing
❌ Making claims without any source  
✓ Every factual claim has a trail back to evidence

### Circular Reasoning
❌ "X is true because of Y, and Y is true because of X"  
✓ Ground claims in independent evidence

### Cherry-Picking
❌ Citing only supporting evidence  
✓ Acknowledge counter-evidence and alternative interpretations

### Appeal to Authority
❌ "Einstein said X, therefore it's true"  
✓ "Einstein demonstrated X [citation], and this has been confirmed by [further evidence]"

---

## Enforcement

### Self-Check Before Posting
1. Have I labeled the type of claim (proof, hypothesis, speculation)?
2. Have I provided appropriate evidence?
3. Have I cited sources properly?
4. Have I acknowledged limitations?

### Review Process
- Pull requests checked for citation quality
- Discussions may request citations if claims are unsupported
- Issues may be closed if evidence standard not met
- Content may be labeled "needs evidence" or "speculative"

### Corrections
If someone points out missing citations or weak evidence:
1. Thank them
2. Add proper citations or
3. Reclassify claim (e.g., from fact to hypothesis) or
4. Remove unsupported claim

No penalty for honest mistakes. Refusing to correct is a problem.

---

## Examples

### Good: Mathematical Claim
> The Riemann Hypothesis states that all non-trivial zeros of the Riemann zeta function have real part 1/2 [Riemann, 1859]. This remains unproven but is supported by computational verification up to 10^13 zeros [Platt & Trudgian, 2020, arXiv:2004.09765].

### Good: Historical Claim
> The Indus Valley Civilization had standardized weights and measures across a large geographic area [Kenoyer, Ancient Cities of the Indus Valley Civilization, 1998, pp. 97-98], suggesting centralized administration or strong cultural norms.

### Good: Hypothesis
> **Hypothesis**: The repeated sequence of symbols A-B-C in Harappan inscriptions represents a grammatical marker rather than lexical content, because it appears independent of context [Parpola, Deciphering the Indus Script, 1994, pp. 123-125]. This is falsifiable by finding contexts where ABC has clear semantic meaning.

### Good: Speculation
> **Speculation**: The behavior of 0/0 in limit theory may have analogies to phase transitions in physical systems (exploratory observation, not established theory).

### Bad: Unsupported Claim
> ❌ "The Harappan script is obviously related to Sanskrit."  
> (No evidence, no citation, stated as fact when it's speculation)

### Bad: Wrong Evidence Tier
> ❌ "According to this YouTube video, ancient civilizations had advanced technology."  
> (Unreliable source, no academic backing)

---

## Resources

### Citation Management
- Use reference manager (Zotero, Mendeley, etc.) for complex projects
- Keep a references list in each content directory
- Cross-reference between related documents

### Verification
- Check DOIs actually work
- Verify quotes are accurate
- Ensure URLs are stable (use DOI or archive.org when possible)

---

## Questions?

If you're unsure whether your evidence meets standards, ask in discussions **before** submitting.

Better to ask than to submit poor-quality work.
