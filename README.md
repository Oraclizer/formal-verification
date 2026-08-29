<div align="center">
  <img src="docs/assets/formal-verification-banner.svg" alt="Oraclizer Formal Verification artifacts in Isabelle/HOL" width="860">

  <p><strong>Machine-checked model-level foundations for cross-domain state preservation and regulatory action composition, plus an independent protected-behavior obstruction companion.</strong></p>

  [![Proofs](https://github.com/Oraclizer/formal-verification/actions/workflows/proofs.yml/badge.svg)](https://github.com/Oraclizer/formal-verification/actions/workflows/proofs.yml)
  [![Repository health](https://github.com/Oraclizer/formal-verification/actions/workflows/repository-health.yml/badge.svg)](https://github.com/Oraclizer/formal-verification/actions/workflows/repository-health.yml)
  [![External dependencies](https://github.com/Oraclizer/formal-verification/actions/workflows/external-dependencies.yml/badge.svg)](https://github.com/Oraclizer/formal-verification/actions/workflows/external-dependencies.yml)
  [![arXiv](https://img.shields.io/badge/arXiv-2604.03844-b31b1b.svg)](https://arxiv.org/abs/2604.03844)
  [![Software Heritage](https://archive.softwareheritage.org/badge/origin/https://github.com/Oraclizer/formal-verification/)](https://archive.softwareheritage.org/browse/origin/?origin_url=https://github.com/Oraclizer/formal-verification)
  [![License](https://img.shields.io/github/license/Oraclizer/formal-verification?color=0b5cad)](LICENSE)

  [Proof scope](#verified-model-level-results) |
  [Artifacts](#formal-artifact-catalog) |
  [Architecture](#theory-architecture) |
  [Build](#reproduce-the-proofs) |
  [Mapping](FORMAL_MODEL_MAPPING.md)
</div>

> **Mechanized assurance.** The repository contains three Isabelle/HOL
> sessions. CDSP and RAC compose. `Protected_Behavior_Obstructions` is an
> independent HOL companion to an external Lean development: its rows are
> graded `PARTIAL`, never `SAME` (both grades are defined in
> [`Protected_Behavior_Obstructions/CROSS_PROVER_MAPPING.md`](Protected_Behavior_Obstructions/CROSS_PROVER_MAPPING.md)).
> The tracked theories are `sorry`/`oops`-free and
> reproducibly check under Isabelle2025-2 with the declared AFP dependency.
> Claims are model-level and bounded by the assumptions recorded here. The
> Oraclizer product mapping remains in
> [`FORMAL_MODEL_MAPPING.md`](FORMAL_MODEL_MAPPING.md); the independent
> companion's exact boundary is folder-local.

## Repository maintenance status

This is a **production-maintained public research repository**. The
designation covers repository operations: reviewable changes, reproducible
proof and document builds, session-scoped releases, integrity manifests,
automated public-surface checks, security reporting, and change governance.
It does not designate any artifact as a production implementation,
deployment, audit, legal opinion, or model-to-code refinement.

## Formal artifact catalog

This catalog lists the formal-verification artifacts released from this
repository. Each row is an independently buildable Isabelle session and a
separate review and release unit. **Source** opens the authoritative session
`ROOT`; **PDF** is the session-named reading copy; and **Manifest** records the
source and PDF hashes together with the document-build identity.

| Artifact | Role | Verification focus | Entry points |
| --- | --- | --- | --- |
| **CDSP** | Foundation | Preservation morphisms, priority and conditional progress, authenticated views, guarded convergence, and the synchronization-degree hierarchy | [Source](Cross_Domain_State_Preservation/ROOT) · [PDF](Cross_Domain_State_Preservation/release/Cross_Domain_State_Preservation.pdf) · [Manifest](Cross_Domain_State_Preservation/release/manifest.json) |
| **RAC** | Extension | Regulatory outcomes, pair commutativity, provenance, transfer gates, traces, atomic queues, and finite normal forms | [Source](Regulatory_Action_Composition/ROOT) · [PDF](Regulatory_Action_Composition/release/Regulatory_Action_Composition.pdf) · [Manifest](Regulatory_Action_Composition/release/manifest.json) |
| **Protected Behavior Obstructions** | Partial companion | Set/profile consequences, explicit stochastic assumptions, set-level morphism laws, preorder facts, and bounded controls | [Source](Protected_Behavior_Obstructions/ROOT) · [Scope](Protected_Behavior_Obstructions/README.md) · [Cross-prover map](Protected_Behavior_Obstructions/CROSS_PROVER_MAPPING.md) · PDF/manifest not produced (`document = false`) |

**Role taxonomy**

- **Foundation:** introduces reusable formal definitions and base laws.
- **Extension:** imports a repository session to establish an additional
  checked result set.
- **Bridge:** proves a correspondence with an external model or formalization.
- **Application:** instantiates a formal model for a bounded domain case.

The role classifies an artifact's primary formal relationship, not its
maturity, publication venue, or acceptance state. CDSP is the reusable
foundation; RAC is an extension because it imports CDSP's
`Regulatory_Instance`. RAC does not import or extend `ADS_Functor`.

An earlier version of CDSP was submitted to the Archive of Formal Proofs on
2026-03-25 but was not accepted as an AFP entry. None of these sessions is an
AFP entry. Repository publication, preprint publication,
submission, review, and acceptance are separate states.

## Verified model-level results

| Session | Representative results | Essential boundary |
| --- | --- | --- |
| CDSP: state preservation | `regulatory_homomorphism`, `valid_state_preservation`, `sequential_preservation` | Atomic finite-domain model |
| CDSP: priority and progress | unique maximum selection, `starvation_bound`, closed-count completion | Injective priorities and deterministic in-roster fairness assumptions |
| CDSP: composition and convergence | guarded safety and existential bounded run to validity | Recovery uses Hilbert choice and is not executable |
| CDSP: authenticated functor | identity/composition/associativity, merge and blinding soundness, Canton tree instance | Model-level authenticated views, not protocol traces |
| CDSP: degree hierarchy | natural transformations, capability-sensitive reconciliation, under-provisioning counterexample | Degree means coupling breadth, not operational S0-S3 semantics |
| RAC: action algebra | all 21 distinct-label pairs classified as 12 commuting and 9 noncommuting, with witnesses | Concrete five-state, seven-label machine |
| RAC: outcomes and traces | applied/rejected/operational-failure separation, trace and unrelated-asset frame properties | No authorization, replay, or concurrency model |
| RAC: atomic queues and normal forms | completed-step validity and consistency; exactly 60 reachable transformation vectors | Atomic completed steps, not partial propagation or rollback |
| Protected behavior obstructions | nested profile algebra, assumption-transparent T2/T3/T4/T5 consequences, set-level morphism laws, preorder facts, and direct finite witnesses | `PARTIAL`; no kernel-derived first-hit law, scheduler correspondence, quantitative pushforward, or `SAME` credit |

Every row is shorthand. The Oraclizer theorem-to-target map, assumptions, open
obligations, and proposed implementation correspondences are in
[`FORMAL_MODEL_MAPPING.md`](FORMAL_MODEL_MAPPING.md). The independent
protected-obstruction companion has no product target; its detailed
correspondence is in
[`Protected_Behavior_Obstructions/CROSS_PROVER_MAPPING.md`](Protected_Behavior_Obstructions/CROSS_PROVER_MAPPING.md).

## Theory architecture

<div align="center">
  <img src="docs/assets/theory-architecture.svg" alt="Import graph of the CDSP and RAC sessions. State_Preservation feeds Regulatory_Instance, Composition, Proof_Automation, Functor_Laws, Hierarchy and External_Instance. Priority_Resolution feeds DQuencer_Instance, which feeds Composition. Composition and Regulatory_Instance feed Functor_Laws, which feeds Hierarchy and Canton_Bridge. The external AFP session ADS_Functor feeds Functor_Laws and Canton_Bridge. Regulatory_Action_Composition in the RAC session imports Regulatory_Instance." width="900">
</div>

The CDSP session depends on `HOL-Library`, `HOL-Eisbach`, and the AFP session
`ADS_Functor`. RAC extends the built CDSP session and imports its regulatory
instance explicitly. `Protected_Behavior_Obstructions` extends `HOL`
independently and imports neither CDSP nor RAC.

## Assurance boundary

### Established within the models

- all three declared sessions and all fourteen tracked theories build;
- the theory sources contain no `sorry` or `oops`;
- named results follow from the definitions, locales, and assumptions stated
  in the theories;
- RAC's pair inventory, witnesses, and 60 normal forms are checked in the
  Isabelle kernel rather than asserted from an external enumeration.

### Not established

- model-to-code refinement (Isabelle to Rust, Solidity, or EVM);
- distributed-runtime correctness: locks, timeouts, rollback, finality,
  concurrent interleaving, network liveness, or adversarial BFT execution;
- external facts and operations: authorization and identity policy, replay
  protection, cryptographic implementation correctness, legal truth, live
  deployment, operational security, or audit status.

These are open or external obligations, not implied consequences of a green
proof build.

## Reproduce the proofs

For the independent protected-obstruction companion only, Isabelle2025-2 is
enough; it extends `HOL` and does not require AFP:

```bash
isabelle build -c -D Protected_Behavior_Obstructions Protected_Behavior_Obstructions
```

Read its [scope](Protected_Behavior_Obstructions/README.md) and
[cross-prover map](Protected_Behavior_Obstructions/CROSS_PROVER_MAPPING.md)
before comparing it with the canonical Lean development, published separately as
[observer-patch-holography](https://github.com/FloatingPragma/observer-patch-holography).

### Prerequisites

- Isabelle `2025-2`
- an AFP checkout compatible with that Isabelle release
- the AFP `ADS_Functor` session available through registration or `-d`

Register the AFP once:

```bash
isabelle components -u /path/to/afp/thys
```

Check all three sessions from the repository root:

```bash
isabelle build \
  -d . \
  -d /path/to/afp/thys \
  Cross_Domain_State_Preservation Regulatory_Action_Composition \
  Protected_Behavior_Obstructions
```

Expected completion includes:

```text
Finished Cross_Domain_State_Preservation
Finished Regulatory_Action_Composition
Finished Protected_Behavior_Obstructions
```

Generate a session document in a chosen output directory:

```bash
isabelle build \
  -d . \
  -d /path/to/afp/thys \
  -o document=pdf \
  -o document_output=/path/to/output \
  Regulatory_Action_Composition
```

Isabelle's build output may be named `document.pdf`. That is a transient build
artifact. A tracked public reading copy is accepted only under
`<Session>/release/<Session>.pdf`, with the exact case-sensitive session name.
Generic `document.pdf` files are not public release artifacts.

An independent assurance claim should identify the exact commit, Isabelle and
AFP revisions, command, and resulting session log.

## Repository map

Every released artifact follows one directory convention, so the map stays
this short as the catalog grows:

| Path | Purpose |
| --- | --- |
| `ROOTS` | Registers every released session |
| `<Session>/` | One directory per catalog artifact: the authoritative `*.thy` theories and the session `ROOT`. Sessions that produce a reading copy add `document/` (LaTeX source) and `release/` (session-named PDF and manifest); session-scoped docs such as a scope README or a cross-prover mapping live inside the same directory |
| `docs/assets/` | README banner and the theory-architecture diagram, with the diagram's Mermaid source |
| `FORMAL_MODEL_MAPPING.md` | Oraclizer theorem-to-target mapping, assumptions, gaps, and proposed tests |
| `CONTRIBUTING.md`, `SECURITY.md`, `CITATION.cff` | Review channels and proof reproduction, sensitive-report routing, and citation metadata |

Generated Isabelle heaps, transient `document.pdf` files, local output, editor
state, and machine-specific paths are excluded from the public tree.

## Independent review and contributions

The highest-value contributions are counterexamples, overly strong assumption
reports, model-scope challenges, reproduction results, and clarity fixes.
Theory changes are issue-first so that each session remains a coherent,
auditable artifact.

Read [CONTRIBUTING.md](CONTRIBUTING.md) before opening a Pull Request. Use the
issue forms for public proof or documentation questions. Report sensitive
vulnerabilities through [SECURITY.md](SECURITY.md), never in a public issue.
Support and project decision boundaries are in [SUPPORT.md](SUPPORT.md) and
[GOVERNANCE.md](GOVERNANCE.md).

## Publications and related work

- Jinwook Kim, *The Cross-Domain State Preservation Functor: A Mechanized
  Theory of Regulatory State Synchronization in Isabelle/HOL*,
  [arXiv:2604.03844](https://arxiv.org/abs/2604.03844).
- Jinwook Kim and Jonghun Hong, *A Regulatory Compliance Protocol for Asset
  Interoperability Between Traditional and Decentralized Finance in Tokenized
  Capital Markets*,
  [arXiv:2603.29278](https://arxiv.org/abs/2603.29278).
- Andreas Lochbihler and Ognjen Marić, *Authenticated Data Structures as
  Functors in Isabelle/HOL*,
  [AFP: ADS_Functor](https://www.isa-afp.org/entries/ADS_Functor.html).

Use [CITATION.cff](CITATION.cff), name the session used, and cite the exact
commit when referring to a mechanized artifact.

## License and disclaimer

The repository is licensed under the
[BSD 3-Clause License](LICENSE). The license includes warranty and liability
limitations. [DISCLAIMER.md](DISCLAIMER.md) summarizes the model, academic,
implementation, and deployment boundaries without replacing the license.

Maintainer: Jinwook Kim (Jay), `jay@oraclizer.io`.
