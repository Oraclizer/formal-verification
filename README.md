# Oraclizer Formal Verification

Formal verification artifacts for the [Oraclizer](https://oraclizer.io) oracle state machine, verified in [Isabelle/HOL](https://isabelle.in.tum.de/).

[![License: BSD](https://img.shields.io/badge/License-BSD-blue.svg)](LICENSE)
[![Isabelle](https://img.shields.io/badge/Isabelle-2025--2-green.svg)](https://isabelle.in.tum.de/)
[![AFP Submission](https://img.shields.io/badge/AFP-submitted-orange.svg)](https://www.isa-afp.org/submission/?id=2026-03-25_06-34-01_784)
[![arXiv](https://img.shields.io/badge/arXiv-2604.03844-b31b1b.svg)](https://arxiv.org/abs/2604.03844)
[![SSRN](https://img.shields.io/badge/SSRN-6550359-006837.svg)](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6550359)

## Overview

This repository contains machine-checked proofs of safety and liveness properties for cross-domain state synchronization in Byzantine environments. The proofs establish two independent but complementary guarantees:

1. **Safety**: Regulatory actions (freeze, seize, confiscate, etc.) applied on one blockchain network are faithfully reflected across all connected networks, preserving the structure of state transitions.
2. **Liveness**: Under Byzantine faults (f < n/3), regulatory actions are resolved deterministically, no asset can be permanently locked, and no pending request is starved indefinitely.

The core abstractions are two hierarchies of Isabelle/HOL locales:

- **Cross-Domain State Preservation** (Property 1): A hierarchy of state-machine locales (pairwise state preservation with naturality, symmetric bidirectional preservation, multi-domain preservation) whose naturality condition guarantees structural preservation of transitions across domains.
- **Priority Resolution and Liveness Locales** (Property 2): Captures deterministic ordering, deadlock avoidance, and starvation freedom as reusable abstractions for leader-based Byzantine consensus systems.

The two properties are connected via an assume-guarantee pattern: the liveness proof of Property 2 discharges the honest-node assumption in Property 1's safety proof, lifting conditional safety into unconditional guarantee under the Byzantine model.

Every generic locale in both hierarchies is instantiated with a concrete example drawn from the regulatory model, for eight locale interpretations in total.

**Design lineage.** Our use of locales for compositional, reusable abstractions follows the methodological tradition exemplified in the AFP by Lochbihler's [`ADS_Functor`](https://www.isa-afp.org/entries/ADS_Functor.html) entry, which structured authenticated data structures through composable building blocks. The technical content here is independent of `ADS_Functor`; the connection is one of design philosophy (locale-based reusable abstractions over functor-shaped data), not formal dependency.

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

**Status:** Complete (2026-04-02). No `sorry` or `oops`. Ready for AFP entry update after Property 1 acceptance.

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
| `combined_safety_liveness` | Connects Property 1's safety with Property 2's liveness: under Byzantine faults, cross-domain regulatory state is synchronized deterministically, without deadlock, and without starvation |

**Model:**
- 3 authority levels: Regional, National, International (RCP jurisdictional hierarchy)
- 4-component priority key: (authority_rank, inverted_timestamp, action_severity, inverted_node_id)
- BFT threshold: n ≥ 3f + 1 (standard Byzantine fault tolerance)
- Timeout-based locking (models VRF-randomized leader election abstractly)
- Fair leader assumption: within any `fairness_bound` epochs, at least one honest leader is elected

**Design pattern.** The liveness proof uses assume-guarantee reasoning: the fairness assumption abstracts VRF randomness as a deterministic condition, and Property 2 discharges the honest-node assumption that Property 1 implicitly required. Together they establish unconditional safety + liveness under the Byzantine model.

### Property 3: Heterogeneous Verification Composition

**Status:** Not started. Planned after Property 1 AFP acceptance.

Property 3 will compose the Cross-Domain State Preservation framework with Lochbihler's Merkle Functor (AFP entry `ADS_Functor`) to establish end-to-end assurance from Canton off-chain ledgers through OSS synchronization to on-chain EVM state.

## Repository Structure

```
.
├── Cross_Domain_State_Preservation/   # AFP entry
│   ├── State_Preservation.thy         # Property 1 generic theory (370 lines)
│   │                                  #   4 locales: state_machine,
│   │                                  #   state_preservation,
│   │                                  #   symmetric_state_preservation,
│   │                                  #   multi_domain_preservation
│   ├── Regulatory_Instance.thy        # Property 1 regulatory instance (1778 lines)
│   │                                  #   State machine interpretation,
│   │                                  #   synchronization protocol,
│   │                                  #   regulatory homomorphism,
│   │                                  #   valid state preservation,
│   │                                  #   multi-domain instantiation,
│   │                                  #   heterogeneous-action instance
│   │                                  #     (escalation preservation),
│   │                                  #   layer-crossing instance
│   │                                  #     (onchain DAML bridge)
│   ├── Priority_Resolution.thy        # Property 2 generic theory (407 lines)
│   │                                  #   3 locales: priority_system,
│   │                                  #   deadlock_free_locking,
│   │                                  #   fair_leader_system
│   ├── DQuencer_Instance.thy          # Property 2 D-quencer instance (660 lines)
│   │                                  #   Authority levels, priority keys,
│   │                                  #   BFT system locale,
│   │                                  #   liveness instantiation,
│   │                                  #   combined safety + liveness theorem
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

### Checking the Proofs

```bash
# Clone the repository
git clone https://github.com/oraclizer/formal-verification.git
cd formal-verification

# Build and check all proofs
isabelle build -d . Cross_Domain_State_Preservation
```

Expected output: `Finished Cross_Domain_State_Preservation` with no errors.

### Generating the Document

```bash
isabelle build -d . -o document=pdf Cross_Domain_State_Preservation
```

The generated PDF will be in the session output directory.

## AFP Submission

This work is submitted to the [Archive of Formal Proofs](https://www.isa-afp.org/) under the entry name `Cross_Domain_State_Preservation`.

- **Initial submission date:** 2026-03-25 (Property 1)
- **Status:** Under editor review
- **Submission URL:** [AFP Submission](https://www.isa-afp.org/submission/?id=2026-03-25_06-34-01_784)

Property 2 is complete and will be submitted as an entry update after Property 1 acceptance.

## Related Work

- Kim, Jinwook (2026). *Safety and Liveness of Cross-Domain State Preservation under Byzantine Faults: A Mechanized Proof in Isabelle/HOL.* arXiv:2604.03844 [cs.CR]. [https://arxiv.org/abs/2604.03844](https://arxiv.org/abs/2604.03844)
- Kim, Jinwook and Hong, Jonghun (2026). *A Regulatory Compliance Protocol for Asset Interoperability Between Traditional and Decentralized Finance in Tokenized Capital Markets.* arXiv:2603.29278 [cs.CY]. [https://arxiv.org/abs/2603.29278](https://arxiv.org/abs/2603.29278)
- Lochbihler, A. (2020). *Formalization of Authenticated Data Structures as Functors in Isabelle/HOL.* FMBC 2020. [AFP Entry: ADS_Functor](https://www.isa-afp.org/entries/ADS_Functor.html)

## Related Resources

- [Oraclizer Research: Proofs](https://research.oraclizer.io/category/proofs/): Research publications on formal verification
- [Oraclizer Documentation](https://docs.oraclizer.io/): Technical documentation

## License

BSD License. See [LICENSE](LICENSE) for details.

## Contact

- **Author:** Jinwook Kim (Jay), jay@oraclizer.io
- **Twitter/X:** [@Oraclizer](https://x.com/Oraclizer)
