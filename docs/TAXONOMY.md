# Taxonomy

## How the Lunar Hive Is Organized

This document maps the entire repository structure so you can navigate
effectively.

---

## Root Level: Identity & Governance

Located in `/`

### Core Files

- **README.md** — Public entry point and project overview
- **LICENSE** — Legal framework (MIT)
- **CODE_OF_CONDUCT.md** — Behavior standards
- **GOVERNANCE.md** — Decision-making structure
- **SECURITY.md** — Security policies and reporting
- **CONTRIBUTING.md** — How to participate
- **DISCUSSIONS_GUIDE.md** — Discussion guidelines

**Purpose**: Establish identity, legal standing, and interaction rules.

---

## 00_MANIFEST: Immutable Core

Located in `/00_MANIFEST/`

### Files

- **README.md** — Canonical declaration of the system
- **PRINCIPLES.md** — Foundational principles
- **SCOPE.md** — What is and isn't included
- **DEFINITIONS.md** — Precise term definitions
- **EPISTEMOLOGY.md** — Knowledge, proof, and evidence

**Purpose**: Define the conceptual foundation. **Start here if you are new.**

**Change Frequency**: Rare. These documents stabilize the entire system.

---

## docs/: Public Navigation

Located in `/docs/`

### Top-Level Guides

- **START_HERE.md** — New visitor orientation
- **TAXONOMY.md** — This file (structure map)
- **ROADMAP.md** — Future direction

### Subdirectories

#### `/docs/policies/`

Interaction and quality standards:

- **PUBLIC_INTERACTION_PROTOCOL.md** — How public engagement works
- **EVIDENCE_AND_CITATION_STANDARD.md** — How to support claims
- **MODERATION.md** — How moderation is conducted

#### `/docs/axes/`

Conceptual entry points to major domains:

- **MILLENNIUM_PROBLEMS.md** — Mathematics (Riemann, P vs NP, etc.)
- **ZERO_OVER_ZERO.md** — Indeterminate forms and limits
- **HARAPPAN.md** — Ancient Indus script research
- **ENGINEERING.md** — System design and prototyping
- **SUSTAINABILITY.md** — Closed-loop resource systems
- **OLYMPICS.md** — Cultural ritual and cohesion systems

**Purpose**: Guide readers to relevant content without overwhelming them.

---

## 03_CONTENT_CORE: Actual Content

Located in `/03_CONTENT_CORE/`

### Structure

Each major axis has its own directory:

#### `/03_CONTENT_CORE/millennium/`

Millennium Prize Problems from an observational perspective:

- Riemann Hypothesis
- P vs NP
- Navier-Stokes
- (others as developed)

Each subdirectory contains:

- `overview.md` — High-level summary
- `formal_notes.md` — Technical details
- `references.md` — Citations and sources

#### `/03_CONTENT_CORE/zero_over_zero/`

Deep exploration of 0/0 and indeterminate forms:

- `axioms.md` — Foundational assumptions
- `models.md` — Mathematical models
- `limits.md` — Limit theory connections
- `open_questions.md` — Unresolved issues

#### `/03_CONTENT_CORE/harappan/`

Harappan script decipherment research:

- `symbol_inventory.md` — Known symbols
- `mapping_hypotheses.md` — Proposed meanings
- `evidence.md` — Supporting data
- `falsifiability.md` — How to test claims

#### `/03_CONTENT_CORE/engineering/`

System architecture and methodology:

- `system_architecture.md` — Design principles
- `prototyping.md` — Development approach
- `risk_and_safety.md` — Safety frameworks
- `sustainability_links.md` — Connections to sustainability axis

#### `/03_CONTENT_CORE/sustainability/`

Resource systems and constraints:

- `closed_loop_models.md` — Circular economy designs
- `resource_accounting.md` — Tracking methods
- `human_rights_constraints.md` — Ethical boundaries

#### `/03_CONTENT_CORE/olympics/`

Cultural systems analysis:

- `narrative_systems.md` — Story structures
- `ritual_and_cohesion.md` — Social bonding mechanisms
- `production_constraints.md` — Practical limits

#### `/03_CONTENT_CORE/community/`

Space for vetted external contributions:

- `accepted_contributions/` — Curated submissions

**Purpose**: The actual research, documentation, and analysis.

**Change Frequency**: Regular. This is where active development happens.

---

## .github/: Technical Interaction

Located in `/.github/`

### Issue Templates (`/ISSUE_TEMPLATE/`)

- **bug_report.yml** — Report errors
- **proposal.yml** — Suggest additions
- **research.yml** — Propose research questions

### Pull Request Template

- **pull_request_template.md** — Contribution checklist

### Workflows (`/workflows/`)

- **markdown-lint.yml** — Automated formatting checks
- **link-check.yml** — Verify links work

**Purpose**: Channel public energy productively and maintain quality
automatically.

---

## Information Flow

```text
New Visitor
    ↓
START_HERE.md → 00_MANIFEST → TAXONOMY.md
    ↓
Choose an axis (docs/axes/)
    ↓
Dive into content (03_CONTENT_CORE/)
    ↓
Engage (Discussions, Issues, PRs)
```

---

## Design Principles

### Vertical Growth

Content grows **within** directories, not sprawling outward.

### Consistent Structure

Every major directory has a `README.md` explaining its contents.

### Clear Boundaries

The `/00_MANIFEST/SCOPE.md` defines what belongs and what doesn't.

### Minimal Redundancy

If information exists in one place, it's not duplicated elsewhere without good
reason.

---

## Finding What You Need

### "I want to understand the system"

→ Start with `00_MANIFEST/`

### "I want to see what's available"

→ Read `docs/axes/` summaries

### "I want to dive deep on a topic"

→ Go directly to `03_CONTENT_CORE/{topic}/`

### "I want to contribute"

→ Read `CONTRIBUTING.md`, then use GitHub features

### "I found an error"

→ Use `.github/ISSUE_TEMPLATE/bug_report.yml`

### "I have a question"

→ GitHub Discussions

---

## What's Not Here

- No scattered blog posts
- No marketing materials  
- No opinion pieces without evidence
- No code dumps without context
- No temporary experiments (those go elsewhere)

This is an **archive**, not a feed.

---

## Evolution

This taxonomy will:

- **Remain stable** in structure
- **Expand** as content grows
- **Be documented** when major changes occur

The goal is **durability and navigability**.

---

## Questions?

If this taxonomy doesn't answer your structural question, open a discussion.
