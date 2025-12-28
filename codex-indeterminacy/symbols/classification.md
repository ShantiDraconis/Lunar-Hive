# Symbol Classification

## Purpose

This document presents classification systems for organizing symbols based on observable properties, not semantic interpretations.

## Classification Principles

1. **Multiple systems** - symbols can belong to multiple categories
2. **Observable criteria** - based on form, not meaning
3. **Provisional** - classifications may be revised
4. **Non-exclusive** - overlap is expected and documented

## Primary Classification Systems

### By Visual Complexity

#### Simple Forms
**Criteria:**
- 1-3 basic geometric elements
- No internal detail
- Minimal strokes

**Examples (Harappan):**
- Single lines (vertical, horizontal, diagonal)
- Simple crosses
- Basic circles
- Elementary angles

**Frequency:** High (often functional/grammatical?)
**Confidence:** High (clear classification)

#### Intermediate Forms
**Criteria:**
- 4-8 geometric elements
- Some internal structure
- Moderate detail

**Examples:**
- Compound geometric shapes
- Simple pictographs
- Combined basic forms

**Frequency:** Medium
**Confidence:** Medium (some ambiguity at boundaries)

#### Complex Forms
**Criteria:**
- 9+ elements
- Detailed internal structure
- Elaborate composition

**Examples:**
- Detailed pictographs
- Multi-element compounds
- Highly specific representations

**Frequency:** Lower
**Confidence:** Medium-High (clear complexity, but count subjective)

### By Representational Nature

#### Abstract/Geometric
**Criteria:**
- No obvious representational content
- Pure geometric forms
- Non-mimetic

**Hypothesis:** May represent phonetic values, grammatical markers, or abstract concepts.

**Examples:**
- Horizontal lines
- Jar-like shapes (if abstract, not representational)
- Cross patterns
- Enclosed spaces

**Note:** Boundary with "stylized" is fuzzy.

#### Pictographic/Representational
**Criteria:**
- Recognizable object, being, or action
- Mimetic intent apparent
- Identifiable referent

**Hypothesis:** May represent words, concepts, or phonetic values (rebus).

**Categories:**
- Anthropomorphic (human figures, body parts)
- Zoomorphic (animals, animal parts)
- Botanical (plants, trees, leaves)
- Objects (tools, vessels, structures)
- Natural phenomena (sun, water, mountains)

**Note:** Pictographic ≠ meaning is transparent.

#### Ambiguous/Stylized
**Criteria:**
- May be representational but highly abstracted
- Could be geometric with incidental resemblance
- Classification uncertain

**Status:** Requires further analysis or remains indeterminate.

### By Symmetry

#### Vertically Symmetric
- Mirror image across vertical axis
- Examples: some cross forms, certain compound shapes

#### Horizontally Symmetric
- Mirror image across horizontal axis
- Less common in Harappan corpus

#### Rotationally Symmetric
- Invariant under rotation (90°, 180°, etc.)
- Examples: some stellar or radial patterns

#### Asymmetric
- No symmetry axes
- Most pictographic symbols

**Analytical value:** Symmetry may correlate with function or origin.

### By Stroke Count

#### Single-stroke symbols
- Simple lines, curves
- Quick to inscribe
- Often high frequency

#### Multi-stroke symbols
- Require multiple actions to create
- More complex
- Variable frequency

**Note:** Stroke count reconstruction is hypothetical for carved symbols.

### By Orientation Stability

#### Fixed Orientation
- Always appear in same orientation
- Rotation would be recognized as different/error
- Most symbols fall here

#### Variable Orientation
- May appear rotated or flipped
- Orientation not semantically significant
- Rare in most scripts

**Caution:** Apparent variation may be:
- Scribal error
- Different scribal traditions
- Our misunderstanding of canonical form

### By Frequency-Based Tiers

See `inventory.md` for detailed frequency distribution.

#### Very High Frequency (Top 10)
- May indicate functional/grammatical role
- Or very common words/phonemes
- Priority for analysis

#### High Frequency (Next 20-30)
- Core symbolic set
- Essential for understanding system

#### Medium Frequency (Next 50-70)
- Extended vocabulary
- Mixed functional roles likely

#### Low Frequency (Remaining)
- Rare words, names, or specialized terms
- Or stylistic variants
- Lower priority but still documented

### By Positional Distribution

#### Initial Position Symbols
- Appear predominantly at text beginning
- Hypothesis: May include determinatives, titles, grammatical markers
- Requires statistical validation

#### Final Position Symbols
- Appear predominantly at text end
- Hypothesis: May include grammatical suffixes, punctuation, closure markers
- Requires statistical validation

#### Medial Position Symbols
- Appear primarily within text body
- Hypothesis: Core lexical or phonetic content
- Most symbols fall here

#### Position-Independent Symbols
- Appear in multiple positions with similar frequency
- Hypothesis: High versatility—phonetic or common grammatical elements
- Requires careful analysis

#### Isolated Symbols
- Appear only in single-symbol inscriptions
- Hypothesis: Complete messages, numerals, names, or markers
- Special analytical category

### By Combinatorial Behavior

#### Promiscuous Combiners
- Appear with many different symbols
- High combinatorial diversity
- Hypothesis: Phonetic or highly versatile grammatical elements

#### Restricted Combiners
- Appear with limited set of other symbols
- Low combinatorial diversity
- Hypothesis: Specialized function or limited distribution

#### Never-Combine Symbols
- Do not co-occur with certain other symbols
- May indicate mutual exclusivity
- Could be positional constraint or semantic incompatibility

#### Frequent Pair Members
- Consistently appear in specific bigrams
- May be compound symbols, fixed phrases, or grammatical constructions
- Requires separate analysis

## Cross-Classification Patterns

### Observations (Hypothetical)

**Pattern 1:** High-frequency symbols tend to be simple forms
- Possible explanation: Economy of effort for common elements
- Alternative: Functional markers are inherently simple

**Pattern 2:** Pictographic symbols tend to be lower frequency
- Possible explanation: Specific referents are less common
- Alternative: Pictographs are names or rare items

**Pattern 3:** Position-specific symbols tend to be abstract
- Possible explanation: Grammatical markers are non-representational
- Alternative: Sample bias or coincidence

**Confidence:** Low - requires statistical validation

## Machine-Readable Classification

For computational analysis, each symbol receives:

```
Symbol_ID: [unique identifier]
Complexity: [simple/intermediate/complex]
Representational: [abstract/pictographic/ambiguous]
Symmetry: [vertical/horizontal/rotational/asymmetric/none]
Frequency_tier: [1-4]
Position_primary: [initial/medial/final/isolated/distributed]
Combinatorial: [promiscuous/restricted/isolated]
```

## Classification Confidence

- **High confidence** - clear criteria, consistent across corpus
- **Medium confidence** - some ambiguity, but majority cases clear
- **Low confidence** - boundary cases, requires revision
- **Disputed** - conflicting classifications in literature

## Alternative Classification Systems

Different researchers propose different systems. Document alternatives:
- Classification system A (researcher/year)
- Classification system B (researcher/year)
- Points of agreement
- Points of divergence
- Rationale for choosing one system or maintaining multiple

## Falsification and Revision

Classifications are provisional and subject to:
- Revision based on new inscriptions
- Statistical analysis contradicting visual classification
- Better understanding of system structure
- Recognition of errors in previous classification

**Document all reclassifications with rationale.**

## Limitations

1. **Observer bias** - classifications reflect our cognitive categories
2. **Incomplete corpus** - new discoveries may require reclassification
3. **Preservation effects** - damaged symbols misclassified
4. **Cultural distance** - categories meaningful to original users may differ

## Future Directions

- Quantitative metrics for each classification dimension
- Machine learning clustering to test classifications
- Inter-rater reliability studies
- Cross-script classification comparisons

---

*Classifications organize data but do not determine meaning.*

**Status:** Preliminary framework. Detailed symbol-by-symbol classification in progress.
