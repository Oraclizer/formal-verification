# Oraclizer Formal Verification

Formal verification artifacts for the [Oraclizer](https://oraclizer.io) oracle state machine, verified in [Isabelle/HOL](https://isabelle.in.tum.de/).

[![License: BSD-3-Clause](https://img.shields.io/badge/License-BSD--3--Clause-blue.svg)](LICENSE)
[![Isabelle](https://img.shields.io/badge/Isabelle-2025--2-green.svg)](https://isabelle.in.tum.de/)
[![AFP Submission](https://img.shields.io/badge/AFP-submitted-orange.svg)](https://www.isa-afp.org/submission/?id=2026-03-25_06-34-01_784)
[![arXiv](https://img.shields.io/badge/arXiv-2604.03844-b31b1b.svg)](https://arxiv.org/abs/2604.03844)
[![SSRN](https://img.shields.io/badge/SSRN-6550359-006837.svg)](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6550359)

## Overview

This repository contains machine-checked proofs of safety and liveness properties for cross-domain state synchronization in Byzantine environments. The proofs establish two independent but complementary guarantees, and build on them a functor-level treatment of cross-domain state preservation together with a synchronization-degree hierarchy:

1. **Safety**: Regulatory actions (freeze, seize, confiscate, etc.) applied on one blockchain network are faithfully reflected across all connected networks, preserving the structure of state transitions.
2. **Liveness**: Under Byzantine faults (f < n/3), regulatory actions are resolved deterministically, no asset can be permanently locked, and no pending request is starved indefinitely.

The core abstractions are two hierarchies of Isabelle/HOL locales:

- **Cross-Domain State Preservation** (Property 1): A hierarchy of state-machine locales (pairwise state preservation with naturality, symmetric bidirectional preservation, multi-domain preservation) whose naturality condition guarantees structural preservation of transitions across domains.
- **Priority Resolution and Liveness Locales** (Property 2): Captures deterministic ordering, deadlock avoidance, and starvation freedom as reusable abstractions for leader-based Byzantine consensus systems.

The two properties are combined in the theorem `combined_safety_liveness`: from a valid, unlocked global state a synchronization succeeds and the result is again valid (`valid_state_preservation`), so safety holds on the post-sync state reached under the deterministic, deadlock-free, starvation-free resolution that Property 2 establishes.

Every generic locale in both hierarchies is instantiated with a concrete example drawn from the regulatory model.

**Design lineage.** Our use of locales for compositional, reusable abstractions follows the methodological tradition exemplified in the AFP by Lochbihler's [`ADS_Functor`](https://www.isa-afp.org/entries/ADS_Functor.html) entry, which structured authenticated data structures through composable building blocks. The functor-level layer in this repository couples the cross-domain state-preservation construction with that Merkle interface as an explicit formal dependency (see below); the safety and liveness core remains independent of `ADS_Functor`.

## Verified Properties

### Property 1: Cross-Domain State Preservation Homomorphism ✅

**Status:** Complete (2026-02-28). No `sorry` or `oops`. AFP submission under editor review.

**What is proven:**

| Theorem | Statement |
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
- Preemptive locking for concurrent regulatory action prevention
- Synchronization protocol: lock → update all connected chains → unlock

### Property 2: D-quencer Determinism, Deadlock Freedom, Starvation Freedom ✅

**Status:** Complete (2026-04-02). No `sorry` or `oops`. Consolidated with Property 1 in the current entry revision, now under editor review.

**What is proven:**

| Theorem | Statement |
|---|---|
| `select_highest_deterministic` | Given a finite non-empty message set with injective priorities, the highest-priority message is uniquely determined |
| `select_highest_in_set` | The selected message is always a member of the input set |
| `select_highest_is_max` | The selected message has the maximum priority among all messages in the set |
| `lock_eventually_expires` | Every lock has a bounded lifetime; no resource is locked indefinitely |
| `deadlock_freedom` | Any lock released within the timeout bound; no circular wait can persist |
| `starvation_bound` | Under the fair leader assumption, if there are pending requests, at least one is processed within `fairness_bound` epochs |
| `eventual_completion` | All pending requests are eventually processed (by well-founded induction on pending count) |
| `priority_key_injectivity` | The D-quencer priority key uniquely identifies messages given distinct authority/timestamp/action/node |
| `honest_majority` | Under the BFT threshold n ≥ 3f + 1, the number of honest nodes exceeds 2f |
| `combined_safety_liveness` | From a valid, unlocked global state a synchronization succeeds and preserves the global validity invariant (determinism, deadlock-freedom, and starvation-freedom are established separately by `select_highest_deterministic`, `deadlock_freedom`, and `starvation_bound`) |

**Model:**
- 3 authority levels: Regional, National, International (RCP jurisdictional hierarchy)
- 4-component priority key: (authority_rank, inverted_timestamp, action_severity, inverted_node_id)
- BFT threshold: n ≥ 3f + 1 (standard Byzantine fault tolerance)
- Timeout-based locking (models VRF-randomized leader election abstractly)
- Fair leader assumption: within any `fairness_bound` epochs, at least one honest leader is elected

**Design pattern.** The liveness proof uses assume-guarantee reasoning: the fairness assumption abstracts VRF randomness as a deterministic condition. The D-quencer liveness layer is what justifies the honest-behaviour premise relied on by the synchronization model in deployment; the two are combined in `combined_safety_liveness`.

### Cross-Domain State Preservation Functor ✅

**Status:** Mechanized, `sorry`/`oops`-free. Included in this repository; AFP registration pending (to be submitted as a revision of the entry once the current revision is registered).

This layer establishes that the cross-domain state-preservation construction is a **functor**: it proves the category laws over state-preservation morphisms (identity preservation, composition preservation, associativity), and composes the construction with Lochbihler's Merkle interface (AFP entry [`ADS_Functor`](https://www.isa-afp.org/entries/ADS_Functor.html)) to obtain **authenticated cross-domain state soundness**. The Merkle interface is exercised inside the proofs (it is a formal dependency, not merely imported): merged authenticated values are shown to admit a valid join refining each input view, and blinded (need-to-know) views are shown to extract to valid states that refine the originals.

| Theorem | Statement |
|---|---|
| `preservation_id` | The identity pair is a state-preservation morphism from any state machine to itself |
| `preservation_compose` | The composite of two state-preservation morphisms is again a state-preservation morphism |
| `preservation_assoc` | Composition of state-preservation morphisms is associative |
| `merkle_interface_auth` | The concrete authenticated-value triple over (regulatory state, chain-set) pairs forms a Merkle interface |
| `authenticated_preservation_soundness` | Merging two authenticated views yields a valid join refining each input view |
| `blinded_view_preserves_validity` | A blinded authenticated value extracts to a valid state refining the original (need-to-know guarantee) |
| `oraclizer_guarded_bounded_convergence` | From any finite-domain, unlocked global state (no initial consistency assumed) the oraclizer reaches a valid state within a bounded number of evolution steps |
| `safe_recovery_sync_no_fresh_terminal` | A safe-recovery synchronization never makes a terminal (confiscated) state appear on an asset that did not already carry it |
| `inconsistent_has_safe_recovery` | Any inconsistent, finite-domain, unlocked state admits a terminal-faithful safe recovery |

**Guarded bounded convergence.** Beyond the conditional safety invariant of Property 1, this layer derives that from an *arbitrary* carrier state (no initial consistency assumed) the system converges to a valid, consistent state within a bounded number of steps, by composing a guarded safety invariant with a bounded-fair liveness scheduler. The recovery is terminal-faithful: it neither erases an existing confiscation nor introduces one indiscriminately.

### Synchronization-Degree Hierarchy ✅

**Status:** Mechanized, `sorry`/`oops`-free. Included in this repository; AFP registration pending.

This layer lays a synchronization-degree hierarchy over the cross-domain functor. It defines degree-indexed functors and proves their forgetful maps are **natural transformations closed under composition**, and establishes **degree-class monotonicity**:

| Theorem | Statement |
|---|---|
| `degree_natural_transformation` | The degree-forgetting map is a natural transformation between adjacent degree functors, with commuting naturality squares |
| `nt_compose` / `nt_vertical_compose` | Natural transformations of degree functors are closed under composition |
| `hierarchy_monotonicity` | When the system's capability degree dominates the asset's required degree, processing preserves global validity (**over-provisioning is safe**) |
| `over_provisioning_guarantees` | Under over-provisioning, all required chains holding the asset agree on its regulatory state after processing |
| `no_downward_safety` | Under under-provisioning (required degree exceeds system capability) there is a state that defeats every preservation guarantee (**under-provisioning is unsafe**) |
| `boundary_well_defined` | The causal-consistency boundary is single-valued, met under over-provisioning, and induced by a strict happened-before order |
| `static_promotion_safety` | A static re-assignment of an asset's degree within system capability transfers the over-provisioning guarantee verbatim |

### Domain-Independence Instance ✅

**Status:** Mechanized, `sorry`/`oops`-free. Included in this repository; AFP registration pending.

To show the framework carries no hidden regulatory assumptions, an instance entirely outside the regulatory domain (a TCP/RFC 793 endpoint model versus a connection-tracker) discharges the generic state-machine and state-preservation locales, with the tracked packet sequences mirrored step-for-step (`tcp_conntrack_preservation`, `tracked_sequence_mirrored`).

### Proof Automation

A reusable Eisbach automation layer (`discharge_state_machine`, `discharge_preservation`) closes the instance obligations of the generic state-machine and state-preservation locales via named theorem collections, and is used to re-derive the regulatory instance bridges through a single automated discharge method.

## Scope Note

The AFP entry currently under editor review covers the cross-domain state-preservation safety core (Property 1) and the D-quencer liveness core (Property 2). The functor framework (composition, functor laws, guarded bounded convergence), the synchronization-degree hierarchy monotonicity, the domain-independence instance, and the proof-automation layer are included in this repository and are mechanized and `sorry`/`oops`-free; they will be submitted as a revision of the entry once the current revision is registered. AFP registration is pending.

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
│   │                                  #   3 locales: priority_system,
│   │                                  #   deadlock_free_locking,
│   │                                  #   fair_leader_system
│   ├── DQuencer_Instance.thy          # Property 2 D-quencer instance
│   │                                  #   Authority levels, priority keys,
│   │                                  #   BFT system locale,
│   │                                  #   liveness instantiation,
│   │                                  #   combined safety + liveness theorem
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
│   │                                  #   monotonicity, causal-consistency
│   │                                  #   boundary
│   ├── External_Instance.thy          # Domain-independence instance
│   │                                  #   (TCP/RFC 793 endpoint vs.
│   │                                  #   connection tracker)
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

- [Isabelle 2025-2](https://isabelle.in.tum.de/website-Isabelle2025-2/index.html) (or later)
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

This work is submitted to the [Archive of Formal Proofs](https://www.isa-afp.org/) under the entry name `Cross_Domain_State_Preservation`.

- **Initial submission date:** 2026-03-25 (Property 1)
- **Status:** Under editor review; AFP registration pending
- **Submission URL:** [AFP Submission](https://www.isa-afp.org/submission/?id=2026-03-25_06-34-01_784)

Property 1 (safety) and Property 2 (liveness) are consolidated in the current entry revision, now under editor review. The functor framework, degree hierarchy, domain-independence instance, and proof-automation layer in this repository are mechanized and `sorry`/`oops`-free, and will be submitted as a revision once the current revision is registered.

## Related Work

- Kim, Jinwook (2026). *Safety and Liveness of Cross-Domain State Preservation under Byzantine Faults: A Mechanized Proof in Isabelle/HOL.* arXiv:2604.03844 [cs.CR]. [https://arxiv.org/abs/2604.03844](https://arxiv.org/abs/2604.03844)
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