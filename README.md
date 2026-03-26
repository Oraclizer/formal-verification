# Oraclizer Formal Verification

Formal verification artifacts for the [Oraclizer](https://oraclizer.io) oracle state machine, verified in [Isabelle/HOL](https://isabelle.in.tum.de/).

[![License: BSD](https://img.shields.io/badge/License-BSD-blue.svg)](LICENSE)
[![Isabelle](https://img.shields.io/badge/Isabelle-2025--2-green.svg)](https://isabelle.in.tum.de/)
[![AFP Submission](https://img.shields.io/badge/AFP-submitted-orange.svg)](https://www.isa-afp.org/submission/?id=2026-03-25_06-34-01_784)

## Overview

This repository contains machine-checked proofs that cross-domain state synchronization preserves the structure of state transitions. The proofs establish that regulatory actions (freeze, seize, confiscate, etc.) applied on one blockchain network are faithfully reflected across all connected networks.

The core abstraction is a **Cross-Domain State Preservation Functor**: a hierarchy of Isabelle/HOL locales that model state synchronization as a functor between categories of state machines, where the naturality condition guarantees structural preservation of transitions.

**Design lineage.** Inspired by Lochbihler's [Merkle Functor](https://www.isa-afp.org/entries/ADS_Functor.html) (AFP), which abstracted authenticated data structures into composable building blocks. This work extends that pattern to a different axis of abstraction: cross-domain state preservation targeting synchronization correctness rather than data structure integrity.

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

### Property 2: D-quencer Determinism, Deadlock Freedom, Starvation Freedom

**Status:** Not started. Planned after Property 1 publication.

### Property 3: Heterogeneous Verification Composition

**Status:** Not started. Long-term goal.

## Repository Structure

```
.
├── Cross_Domain_State_Preservation/   # AFP entry
│   ├── State_Preservation.thy         # Generic theory (383 lines)
│   │                                  #   4 locales: state_machine,
│   │                                  #   state_preservation,
│   │                                  #   symmetric_state_preservation,
│   │                                  #   multi_domain_preservation
│   ├── Regulatory_Instance.thy        # Regulatory instantiation (1053 lines)
│   │                                  #   State machine interpretation,
│   │                                  #   synchronization protocol,
│   │                                  #   regulatory homomorphism,
│   │                                  #   valid state preservation,
│   │                                  #   multi-domain instantiation
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

- **Submission date:** 2026-03-25
- **Status:** Under editor review
- **Submission URL:** [AFP Submission](https://www.isa-afp.org/submission/?id=2026-03-25_06-34-01_784)

## Related Work

- Lochbihler, A. (2020). *Formalization of Authenticated Data Structures as Functors in Isabelle/HOL.* FMBC 2020. [AFP Entry: ADS_Functor](https://www.isa-afp.org/entries/ADS_Functor.html)
- Regulatory Compliance Protocol (RCP) — Informational EIP in Draft status, systematically classifying requirements from 15 global financial regulatory authorities for tokenized capital markets.

## Related Resources

- [Oraclizer Research](https://research.oraclizer.io/) — Research blog covering the formal verification journey
- [Oraclizer Documentation](https://docs.oraclizer.io/) — Technical documentation

## License

BSD License. See [LICENSE](LICENSE) for details.

## Contact

- **Author:** Jinwook Kim (Jay) — jay@oraclizer.io
- **Twitter/X:** [@Oraclizer](https://x.com/Oraclizer)
