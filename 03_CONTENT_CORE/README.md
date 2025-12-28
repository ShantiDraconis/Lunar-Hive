# 03_CONTENT_CORE

## Purpose

This directory contains the **actual content** of the Lunar Hive — the research, documentation, analysis, and accumulated knowledge across all axes.

This is where theory meets detail.

---

## Structure

Content is organized by **axis** (major conceptual domain):

### `/millennium/`
Millennium Prize Problems: Riemann Hypothesis, P vs NP, Navier-Stokes, etc.

**Entry point**: See `/docs/axes/MILLENNIUM_PROBLEMS.md`

### `/zero_over_zero/`
Indeterminate forms, limit theory, collapse phenomena

**Entry point**: See `/docs/axes/ZERO_OVER_ZERO.md`

### `/harappan/`
Harappan/Indus script research and linguistic analysis

**Entry point**: See `/docs/axes/HARAPPAN.md`

### `/engineering/`
System architecture, prototyping, risk assessment, safety frameworks

**Entry point**: See `/docs/axes/ENGINEERING.md`

### `/sustainability/`
Closed-loop models, resource accounting, human rights constraints

**Entry point**: See `/docs/axes/SUSTAINABILITY.md`

### `/olympics/`
Olympic Games as cultural system: ritual, cohesion, production

**Entry point**: See `/docs/axes/OLYMPICS.md`

### `/community/`
Curated contributions from the community

**Entry point**: See below

---

## Content Guidelines

### Every Major Directory Has
- **README.md** — Explains the directory's purpose and structure
- **Subdirectories** — Organized by topic
- **References** — Citations and sources (where applicable)

### Every File Should
- Have a clear title and purpose
- Follow markdown formatting standards
- Cite sources appropriately
- Label speculation vs. established fact
- Link to related content when relevant

### Quality Standards
- **Rigor**: Claims are supported or labeled as hypotheses/speculation
- **Clarity**: Accessible to serious readers
- **Completeness**: Self-contained or properly referenced
- **Falsifiability**: Hypotheses must be testable

See `/docs/policies/EVIDENCE_AND_CITATION_STANDARD.md`

---

## Navigation

### If You're New
1. Start with `/docs/START_HERE.md`
2. Read relevant axis overview in `/docs/axes/`
3. Dive into specific content here

### If You're Exploring
- Each major directory has a README explaining its contents
- Follow cross-references between related topics
- Check `references.md` files for sources to dig deeper

### If You're Contributing
- Read `/CONTRIBUTING.md` first
- Check existing content to avoid duplication
- Follow evidence and citation standards
- Propose additions via issues or discussions

---

## Growth Pattern

Content grows **vertically** (deeper detail) not **horizontally** (chaotic sprawl).

**Good**:
- Adding detailed analysis to existing topic
- Creating subdirectory for complex subject
- Linking related content across axes

**Bad**:
- Creating random files without structure
- Duplicating content in multiple places
- Adding off-topic material
- Ignoring existing organization

---

## Legacy Content

### `/concepts/`
**Status**: Pre-canonical structure content

Contains early conceptual work:
- `collapse_as_transition.md`
- `limit_vs_error.md`
- `silence_as_signal.md`

**Future**: May be reorganized into new structure or remain as foundational concepts.

### `/open_questions.md`
**Status**: General questions across axes

**Future**: May be split into axis-specific open questions.

---

## Community Contributions

### `/community/accepted_contributions/`

**Purpose**: High-quality contributions from community members that don't fit neatly into existing axes but add value.

**Requirements**:
- Must meet all evidence standards
- Must be reviewed and accepted by maintainers
- Must include proper attribution
- Must align with scope and principles

**Not**:
- A dumping ground for random ideas
- Unreviewed or low-quality content
- Commercial or promotional material

---

## Cross-Axis Integration

Content across axes is **connected**:

- Mathematics ↔ Engineering (computational methods, limits)
- Sustainability ↔ Engineering (resource constraints, safety)
- Harappan ↔ Sustainability (ancient resource management)
- Olympics ↔ Engineering (temporary infrastructure)
- Zero Over Zero ↔ Everything (collapse as universal pattern)

**Integration is central to Ecletic S.**

See `/00_MANIFEST/PRINCIPLES.md` #6: "Integration Over Isolation"

---

## Content Lifecycle

### New Content
1. Proposed via issue or discussion
2. Reviewed for alignment with scope
3. Created with proper structure
4. Cross-referenced as needed

### Existing Content
- Updated as knowledge evolves
- Corrected when errors found
- Expanded with new insights
- Maintained for accuracy

### Deprecated Content
- Marked clearly if superseded
- Kept for historical record (usually)
- Explained why deprecated

**Nothing disappears without reason.**

---

## Current Status (2025)

### Well-Developed
- Conceptual foundations (in `/concepts/`)
- Initial frameworks across axes

### In Development
- Millennium problems (some subdirs created)
- Zero over zero (structure defined)
- Other axes (structure ready, content growing)

### Planned
- Detailed case studies
- More cross-axis connections
- Community contributions integration

See `/docs/ROADMAP.md` for timeline.

---

## Technical Notes

### File Naming
- Use lowercase with underscores: `resource_accounting.md`
- Be descriptive: `riemann_hypothesis_overview.md` not `rh.md`
- Avoid special characters

### Directory Structure
- Maximum 3-4 levels deep (prevents chaos)
- Group related content
- Each directory has README

### Linking
- Use relative links: `../engineering/system_architecture.md`
- Check links don't break when moving files
- Use anchor links for sections: `#heading-name`

---

## Questions?

- Content questions → Discussions or research issues
- Structure questions → Proposal issue
- Found an error? → Bug report
- Want to contribute? → Read `/CONTRIBUTING.md` first

**This is the heart of the archive. Treat it with care.**
