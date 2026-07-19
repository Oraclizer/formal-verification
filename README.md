# Oraclizer Formal Verification

Formal verification artifacts for the [Oraclizer](https://oraclizer.io) oracle state machine, verified in [Isabelle/HOL](https://isabelle.in.tum.de/).

[![License: BSD-3-Clause](https://img.shields.io/badge/License-BSD--3--Clause-blue.svg)](LICENSE)
[![Isabelle](https://img.shields.io/badge/Isabelle-2025--2-green.svg)](https://isabelle.in.tum.de/)
[![AFP Submission](https://img.shields.io/badge/AFP-resubmission_candidate-yellow.svg)](https://www.isa-afp.org/submission/?id=2026-03-25_06-34-01_784)
[![arXiv](https://img.shields.io/badge/arXiv-2604.03844-b31b1b.svg)](https://arxiv.org/abs/2604.03844)
[![SSRN](https://img.shields.io/badge/SSRN-6550359-006837.svg)](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6550359)

## Overview

This repository contains machine-checked model-level proofs for cross-domain state synchronization. The proofs establish two independent but complementary guarantees, and build on them a functor-level treatment of cross-domain state preservation together with a synchronization-degree hierarchy:

1. **Safety**: Regulatory actions (freeze, seize, confiscate, etc.) applied on one blockchain network are faithfully reflected across all connected networks, preserving the structure of state transitions.
2. **Deterministic selection and aggregate progress**: finite non-empty candidate sets have a unique maximum, and under a deterministic in-roster fair-leader assumption a positive pending count decreases within a bounded window and eventually reaches zero in the closed count model. Individual request fairness, concurrent lock persistence, VRF/BFT execution, and network behaviour are not proved.

The core abstractions are two hierarchies of Isabelle/HOL locales:

- **Cross-Domain State Preservation** (Property 1): A hierarchy of state-machine locales (pairwise state preservation with naturality, symmetric bidirectional preservation, multi-domain preservation) whose naturality condition guarantees structural preservation of transitions across domains.
- **Priority Resolution and Aggregate-Progress Locales** (Property 2): Capture deterministic maximum selection and bounded aggregate pending-count progress as reusable, domain-independent abstractions. They are order- and bound-theoretic and do not model request identities, concurrent execution, or message interleaving; the instantiating synchronization model is atomic.

`conditional_safety_preservation` is a conditional-safety corollary: from a valid global state and an enabled transition, validity supplies the no-lock fact, synchronization succeeds, and the result is again valid (`valid_state_preservation`). Its proof uses only the safety side; deterministic selection and aggregate progress are separate theorems (`select_highest_deterministic`, `starvation_bound`). `oraclizer_guarded_bounded_convergence` combines guarded safety with an existential, `SOME`-selected safe recovery under a deterministic fair-discharge schedule. It is not an executable queue, recovery, or BFT algorithm. Deadlock is out of scope because the atomic sync model has no concurrent lock contention.

Every generic locale in both hierarchies is instantiated with a concrete example drawn from the regulatory model.

**Design lineage.** Our use of locales for compositional, reusable abstractions follows the methodological tradition exemplified in the AFP by Lochbihler's [`ADS_Functor`](https://www.isa-afp.org/entries/ADS_Functor.html) entry, which structured authenticated data structures through composable building blocks. The functor-level layer in this repository couples the cross-domain state-preservation construction with that Merkle interface as an explicit formal dependency (see below); the safety and liveness core remains independent of `ADS_Functor`.

## Verified Properties

### Property 1: Cross-Domain State Preservation Homomorphism ✅

**Status:** Mechanized and `sorry`/`oops`-free. Included in the full ten-theory AFP resubmission candidate; that candidate has not yet been uploaded.

**What is proven:**

| Formal item | Statement |
|---|---|
| `regulatory_homomorphism` | After synchronization, all connected chains agree on the regulatory state |
| `valid_state_preservation` | Synchronization preserves the global validity invariant (consistency ∧ no spurious locks) |
| `reg_multi_domain_instantiation` | The generic framework applies parametrically to the regulatory model for any finite domain set |
| `sequential_preservation` | State preservation extends from single actions to arbitrary action sequences (naturality generalization) |
| `confiscated_terminal` | CONFISCATED is an absorbing terminal state |
| `confiscate_universal` | CONFISCATE is reachable from every non-terminal state |
| `no_self_loops` | No transition maps a state to itself |
| `sync_isolation` | Synchronization on one asset does not affect other assets |

**Model:**
- 5 regulatory states: ACTIVE, FROZEN, SEIZED, CONFISCATED, RESTRICTED
- 7 regulatory actions: FREEZE, SEIZE, CONFISCATE, RESTRICT, UNFREEZE, UNRESTRICT, RELEASE
- 35 transition rules (deterministic, partial)
- Atomic lock guard: a second acquire while the Boolean lock is held returns `None`; distributed contention and timeout recovery are outside the model
- Synchronization protocol: lock → update all connected chains → unlock

### Property 2: Deterministic Selection and Aggregate Pending-Count Progress ✅

**Status:** Mechanized and `sorry`/`oops`-free. Included in the full ten-theory AFP resubmission candidate. Deadlock is a scope note, not a proved result: the atomic `sync` model has no concurrent lock contention, so no deadlock-freedom theorem is stated.

**What is proven:**

| Theorem | Statement |
|---|---|
| `select_highest_deterministic` | Given a finite non-empty message set with injective priorities, the highest-priority message is uniquely determined |
| `select_highest_in_set` | The selected message is always a member of the input set |
| `select_highest_is_max` | The selected message has the maximum priority among all messages in the set |
| `starvation_bound` | Under the fair-leader assumption, a positive aggregate pending count strictly decreases within `fairness_bound` epochs |
| `eventual_completion` | The aggregate pending count eventually reaches zero in the closed count model; request identities and continuous arrivals are not represented |
| `priority_key_injectivity` | Within the stated timestamp and source-node upper bounds, the D-quencer priority key uniquely identifies messages that differ in authority/timestamp/action/node |
| `honest_majority` | Under the BFT threshold n ≥ 3f + 1, the number of honest nodes exceeds 2f |
| `conditional_safety_preservation` | From a valid global state and an enabled transition, synchronization succeeds and preserves validity; validity itself implies no outstanding lock |

**Model:**
- 3 authority levels: Regional, National, International (RCP jurisdictional hierarchy)
- 4-component priority key: (authority_rank, inverted_timestamp, action_severity, inverted_node_id)
- Static BFT-count assumptions: n ≥ 3f + 1 and at most f roster members tagged Byzantine; adversarial protocol behaviour is not modelled
- Fair-leader assumption: the schedule stays inside the roster and every `fairness_bound` window contains an honest-tagged leader

**Design pattern.** The proof uses assume-guarantee reasoning: bounded fair leadership and honest progress are deterministic assumptions, not consequences of a VRF probability model. The static threshold guarantees an honest node inside the roster (`honest_nonempty`), from which `fair_schedule_exists` constructs a constant roster-drawn witness and `liveness_inhabitable` proves the locale assumptions satisfiable (`range ls ⊆ nodes`); `bft_quorum` is a non-degenerate four-node cardinality witness. The convergence theorem consumes the fair-leader assumption directly and uses an existential safe-recovery choice; it does not route priority, queue identity, or consensus execution into recovery selection.

### Cross-Domain State Preservation Functor ✅

**Status:** Mechanized and `sorry`/`oops`-free. Included in the full ten-theory AFP resubmission candidate; not yet uploaded.

This layer establishes that the cross-domain state-preservation construction is a **functor**: it proves the category laws over state-preservation morphisms (identity preservation, composition preservation, associativity), and composes the construction with Lochbihler's Merkle interface (AFP entry [`ADS_Functor`](https://www.isa-afp.org/entries/ADS_Functor.html)) to obtain **authenticated cross-domain state soundness**. The Merkle interface is exercised inside the proofs (it is a formal dependency, not merely imported): merged authenticated values are shown to admit a valid join refining each input view, and blinded (need-to-know) views are shown to extract to valid states that refine the originals.

| Theorem | Statement |
|---|---|
| `preservation_id` | The identity pair is a state-preservation morphism from any state machine to itself |
| `preservation_compose` | The composite of two state-preservation morphisms is again a state-preservation morphism |
| `preservation_assoc` | Composition of state-preservation morphisms is associative |
| `merkle_interface_auth` | A state-keyed reveal-set witness forms a Merkle interface: the hash commits to the regulatory state, while blinding and merge operate on the revealed-chain set |
| `authenticated_preservation_soundness` | Merging two authenticated views yields a valid join refining each input view |
| `blinded_view_preserves_validity` | A blinded authenticated value extracts to a valid state refining the original (need-to-know guarantee) |
| `oraclizer_guarded_bounded_convergence` | From any finite-domain, unlocked global state, an existential run selected through `SOME` reaches a valid state within the bound |
| `safe_recovery_sync_no_fresh_terminal` | A safe-recovery synchronization never makes a terminal (confiscated) state appear on an asset that did not already carry it |
| `inconsistent_has_safe_recovery` | Any inconsistent, finite-domain, unlocked state admits a terminal-faithful safe recovery |

**Guarded bounded convergence.** Beyond conditional safety, this layer proves the existence of a bounded run from an arbitrary finite-domain, unlocked carrier state to a valid state. The fair-discharge event gates a non-constructively selected safe recovery (`SOME p. safe_recovery gs p`); the event itself is not used to compute the recovery. The result is therefore a convergence specification, not an executable reconciliation loop. The selected recovery is terminal-faithful within the model.

### Authenticated Functor and Canton Transaction-Tree Instantiation ✅

**Status:** Mechanized and `sorry`/`oops`-free. Included in the full ten-theory AFP resubmission candidate; not yet uploaded.

On the extractable sub-preorder, the authenticated extraction map preserves blinding composition as cross-domain refinement, and lifted merge is associative. The single-step guarantees extend to authenticated-view **blinding paths and merge folds**—not protocol execution traces. The construction is instantiated both on the concrete blindable-position functor of `ADS_Functor` and on a recursive model of the Canton transaction tree built from the public rose-tree Merkle machinery, with subview-level selective disclosure live in the proofs. The recursive view tree is further connected to the entry's generic rose-tree inclusion-proof machinery, sharpening inclusion from the state level to the concrete Merkle path.

| Formal item | Statement |
|---|---|
| `cdsp_ads_compose` | Composable blinding morphisms compose, and the extraction functor sends the composite to the composite of the extracted refinements |
| `cdsp_ads_merge_assoc` | The lifted merge of authenticated views is associative (composite-functor associativity) |
| `sequence_authenticity_preservation` | Along a blinding path, every intermediate view extracts to a valid state refining the most-revealed endpoint |
| `sequence_merge_soundness` | A non-empty list of partial views over one committed object folds into a valid combined view refining every contributor |
| `sequence_inclusion_integrity` | Every holding revealed by any view in a sequence is included in the endpoint with the same regulatory state |
| `reg_tx_authenticated` (`interpretation`) | Cross-domain state preservation is instantiated on a recursive model of the Canton transaction tree (public rose-tree machinery, concrete content) |
| `reg_view_inclusion_same_hash` / `reg_view_inclusion_blinding_of` | Path-level Merkle inclusion: each inclusion proof (target subview revealed, path to root and off-path siblings blinded) commits to the same authenticating root hash as the full view tree and is a blinding of it; no added assumption |

**Model-fidelity boundary.** The recursive instance is structurally faithful (subviews nest as in the public model and subview-level blinding is live), with two declared modelling choices: leaf content is concrete rather than the opaque content types of the public Canton model, and the consensus metadata is modelled as a shared, non-independently-blindable field, so a revealed view under a blinded consensus is outside this model's scope. These are model-fidelity items for confirmation against the Canton specification, not proof gaps; no axiom relates the opaque Canton types to the regulatory model.

### Synchronization-Degree Hierarchy ✅

**Status:** Mechanized and `sorry`/`oops`-free. Included in the full ten-theory AFP resubmission candidate; not yet uploaded.

This layer lays a synchronization-degree hierarchy over the cross-domain functor. It defines degree-indexed functors and proves their forgetful maps are **natural transformations closed under composition**, and establishes **degree-class monotonicity**:

| Theorem | Statement |
|---|---|
| `degree_natural_transformation` | The degree-forgetting map is a natural transformation between adjacent degree functors, with commuting naturality squares |
| `nt_compose` / `nt_vertical_compose` | Natural transformations of degree functors are closed under composition |
| `over_provisioning_guarantees` | Valid-state preservation corollary stated with an over-provisioning premise; the proof obtains agreement from validity, so this theorem alone does not make the degree premise load-bearing |
| `over_provisioning_reconciles` | From an arbitrary hub-defined state (no validity assumed), over-provisioning still drives every required chain to the hub value, so the degree hypothesis is load-bearing in its own right |
| `no_downward_safety` | Under under-provisioning (required degree exceeds system capability) there is a state that defeats every preservation guarantee (**under-provisioning is unsafe**) |
| `hierarchy_monotonicity` | Degree-free validity preservation: an auxiliary alias of `processing_preserves_validity` carrying no provisioning hypothesis |
| `boundary_well_defined` | A degree-2 threshold is compatible with a strict integer-timestamp order; no distributed causality or trace preservation is modelled |
| `static_promotion_safety` | A static re-assignment of an asset's degree within system capability transfers the over-provisioning guarantee verbatim |

**Product-fidelity boundary.** Here the degree index records only coupling breadth: chains `0..k` kept around a hub. It does not formalize the product's S₀–S₃ operational meanings, including directionality, bidirectional causal execution, atomic binding, or mutual rollback. Relating those meanings to `F k` remains a separate refinement obligation.

### Domain-Independence Instance ✅

**Status:** Mechanized and `sorry`/`oops`-free. Included in the full ten-theory AFP resubmission candidate; not yet uploaded.

To show the framework carries no hidden regulatory assumptions, a TCP-inspired toy endpoint lifecycle and an abstract tracker discharge the generic state-machine and state-preservation locales, with the modeled event sequences mirrored step-for-step (`tcp_conntrack_preservation`, `tracked_sequence_mirrored`). The example borrows RFC 793 names but is not trace-conformant to RFC 793 and does not model a concrete operating-system conntrack implementation.

### Proof Automation

A reusable Eisbach automation layer (`discharge_state_machine`, `discharge_preservation`) closes the instance obligations of the generic state-machine and state-preservation locales via named theorem collections, and is used to re-derive the regulatory instance bridges through a single automated discharge method.

## Scope Note

The repository and the current resubmission candidate contain all ten theories listed in `ROOT`: the safety and aggregate-progress cores, composition and functor laws, proof automation, authenticated/Canton instances, hierarchy, and the external instance. An earlier AFP submission was made on 2026-03-25; this full ten-theory resubmission candidate has not yet been uploaded and is not listed as an AFP entry.

## Repository Structure

```
.
├── Cross_Domain_State_Preservation/   # AFP entry
│   ├── State_Preservation.thy         # Property 1 generic theory
│   │                                  #   4 locales: state_machine,
│   │                                  #   state_preservation,
│   │                                  #   symmetric_state_preservation,
│   │                                  #   multi_domain_preservation
│   ├── Regulatory_Instance.thy        # Property 1 regulatory instance
│   │                                  #   State machine interpretation,
│   │                                  #   synchronization protocol,
│   │                                  #   regulatory homomorphism,
│   │                                  #   valid state preservation,
│   │                                  #   multi-domain instantiation,
│   │                                  #   heterogeneous-action instance
│   │                                  #     (escalation preservation),
│   │                                  #   layer-crossing instance
│   │                                  #     (onchain DAML bridge)
│   ├── Priority_Resolution.thy        # Property 2 generic theory
│   │                                  #   2 locales: priority_system,
│   │                                  #   fair_leader_system
│   ├── DQuencer_Instance.thy          # Property 2 D-quencer instance
│   │                                  #   Authority levels, priority keys,
│   │                                  #   BFT system locale,
│   │                                  #   liveness instantiation,
│   │                                  #   conditional-safety corollary
│   ├── Composition.thy                # Generic guarded-safety + bounded-fair
│   │                                  #   liveness composition; derives
│   │                                  #   guarded bounded convergence to an
│   │                                  #   invariant from an arbitrary carrier
│   │                                  #   state (system-independent locales)
│   ├── Proof_Automation.thy           # Eisbach automation methods
│   │                                  #   (discharge_state_machine,
│   │                                  #   discharge_preservation)
│   ├── Functor_Laws.thy               # Functor laws over state-preservation
│   │                                  #   morphisms (identity, composition,
│   │                                  #   associativity); ADS/Merkle
│   │                                  #   authenticated cross-domain state
│   │                                  #   soundness; oraclizer guarded
│   │                                  #   bounded convergence and
│   │                                  #   terminal-faithful safe recovery
│   ├── Hierarchy.thy                  # Synchronization-degree hierarchy:
│   │                                  #   degree functors, composable natural
│   │                                  #   transformations, degree-class
│   │                                  #   monotonicity, timestamp-order
│   │                                  #   degree boundary
│   ├── External_Instance.thy          # Domain-independence instance
│   │                                  #   (TCP-inspired toy endpoint vs.
│   │                                  #   abstract tracker)
│   ├── Canton_Bridge.thy              # Authenticated functor and instances:
│   │                                  #   extractable-subpreorder laws,
│   │                                  #   blinding paths / merge folds, ADS
│   │                                  #   and recursive Canton transaction-
│   │                                  #   tree instantiation
│   ├── ROOT                           # Isabelle session configuration
│   └── document/
│       └── root.tex                   # LaTeX document for AFP
├── FORMAL_MODEL_MAPPING.md            # Model-to-implementation correspondence
├── docs/
│   └── document.pdf                   # Generated theory document (from AFP build)
├── LICENSE
├── CONTRIBUTING.md
└── README.md
```

## Building

### Prerequisites

- [Isabelle 2025-2](https://isabelle.in.tum.de/website-Isabelle2025-2/index.html) (exact audited version)
- The AFP component must be available to Isabelle (the entry depends on the `ADS_Functor` session). Register the AFP with `isabelle components -u /path/to/afp/thys` or pass it via `-d`.

### Checking the Proofs

```bash
# Clone the repository
git clone https://github.com/oraclizer/formal-verification.git
cd formal-verification

# Build and check all proofs (point -d at both this repo and the AFP)
isabelle build -d . -d /path/to/afp/thys Cross_Domain_State_Preservation
```

Expected output: `Finished Cross_Domain_State_Preservation` with no errors.

### Generating the Document

```bash
isabelle build -d . -d /path/to/afp/thys -o document=pdf Cross_Domain_State_Preservation
```

The generated PDF will be in the session output directory.

## AFP Submission

An initial version was submitted to the [Archive of Formal Proofs](https://www.isa-afp.org/) under the entry name `Cross_Domain_State_Preservation`. This repository is the full ten-theory resubmission candidate.

- **Initial submission date:** 2026-03-25 (Property 1)
- **Current candidate status:** Prepared for resubmission; not yet uploaded or listed as an AFP entry
- **Submission URL:** [AFP Submission](https://www.isa-afp.org/submission/?id=2026-03-25_06-34-01_784)

The candidate includes all ten theories in `ROOT`. Upload, submission, and any associated correspondence remain separate release actions.

## Related Work

- Kim, Jinwook (2026). *The Cross-Domain State Preservation Functor: A Mechanized Theory of Regulatory State Synchronization in Isabelle/HOL.* arXiv:2604.03844 [cs.CR]. [https://arxiv.org/abs/2604.03844](https://arxiv.org/abs/2604.03844)
- Kim, Jinwook and Hong, Jonghun (2026). *A Regulatory Compliance Protocol for Asset Interoperability Between Traditional and Decentralized Finance in Tokenized Capital Markets.* arXiv:2603.29278 [cs.CY]. [https://arxiv.org/abs/2603.29278](https://arxiv.org/abs/2603.29278)
- Lochbihler, A. (2020). *Formalization of Authenticated Data Structures as Functors in Isabelle/HOL.* FMBC 2020. [AFP Entry: ADS_Functor](https://www.isa-afp.org/entries/ADS_Functor.html)

## Related Resources

- [Oraclizer Research: Proofs](https://research.oraclizer.io/category/proofs/): Research publications on formal verification
- [Oraclizer Documentation](https://docs.oraclizer.io/): Technical documentation

## License

BSD 3-Clause License. See [LICENSE](LICENSE) for details.

## Contact

- **Author:** Jinwook Kim (Jay), jay@oraclizer.io
- **Twitter/X:** [@Oraclizer](https://x.com/Oraclizer)
