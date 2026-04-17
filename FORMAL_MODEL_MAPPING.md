# Formal Model to Implementation Mapping

**Version:** 0.3.0
**Last updated:** 2026-04-17
**Status:** Pre-implementation (model-only; implementation columns to be populated during development)

## Purpose

This document tracks the correspondence between formally verified model elements in the `.thy` files and their planned implementation in Oraclizer's codebase. It serves four purposes:

1. **Design reference:** Implementation code should match the verified model's state transition rules and liveness parameters.
2. **Traceability:** External reviewers can verify that the implementation follows the formal specification.
3. **Gap tracking:** Identifies where the model makes assumptions that the implementation must satisfy through other means. Assumption explicitness is treated as a design property, not a limitation.
4. **Assumption release roadmap:** Documents which future properties release which current assumptions, making the verification program's trajectory transparent.

## Coverage Scope

This mapping covers:

- **Property 1 (Cross-Domain State Preservation Homomorphism)** — safety
- **Property 2 (D-quencer Determinism, Deadlock Freedom, Starvation Freedom)** — liveness

Property 3 (Heterogeneous Verification Composition) will be added when it is completed.

## What Verification Establishes and What It Does Not

The Isabelle/HOL proofs in this repository establish properties at the **model level**. All proofs are mechanically checked by Isabelle/HOL 2025-2 with no `sorry` or `oops` occurrences. Mechanical correctness is thus established: the lemmas are valid within the stated assumptions.

The current proofs do **not** establish:

- Correspondence between the Isabelle/HOL model and the Rust implementation (refinement proof; scheduled for Phases 2–6 using Creusot/Kani).
- Probabilistic properties of VRF-based leader election (abstracted as the deterministic `fair_leader` assumption; see Assumption Gap Analysis below).
- Network-level properties such as message loss, partial synchrony, or dynamic topology changes (subject of Open Questions; see Assumption Release Roadmap below).
- Properties of unverified external components: P2P networking, external cryptographic libraries (BLS), UI, database layer.

---

# Property 1: State Preservation (Safety)

## State Transition Model

### Regulatory States

| Formal Model (`Regulatory_Instance.thy`) | Implementation Target | Notes |
|---|---|---|
| `datatype reg_state = ACTIVE \| FROZEN \| SEIZED \| CONFISCATED \| RESTRICTED` | `enum RegState` in Solidity (ERC-TRUST Core) + `RegState` enum in OSS (Rust) | Direct 1:1 mapping across both layers |
| `CONFISCATED` as terminal state | `require(state != RegState.CONFISCATED)` guard in Solidity; `match` arm returning `Err(TerminalState)` in Rust | Enforced by `confiscated_terminal` theorem |

### Regulatory Actions

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `datatype reg_action = FREEZE \| SEIZE \| CONFISCATE \| RESTRICT \| UNFREEZE \| UNRESTRICT \| RELEASE` | `enum RegAction` in Solidity + corresponding functions; mirrored as `RegAction` enum in OSS (Rust) | RECOVER and LIQUIDATE are force transfers, not state transitions (see Design Decisions) |

### Transition Function

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `fun reg_transition` (35 rules) | State transition logic: `require` + state update in Solidity; `match` expression in OSS (Rust) | Each `(state, action) → state'` rule maps to an exhaustive branch |
| `no_self_loops` theorem | Assertion: post-state ≠ pre-state | Implementation should include this as a post-condition check; candidate for Creusot annotation in Phase 2 |

### Design Decisions (Exclusions)

These exclusions are formally justified in `Regulatory_Instance.thy`:

| Exclusion | Formal Justification | Implementation Note |
|---|---|---|
| RECOVER excluded from state machine | Force transfer operation, not a state transition | Implemented as `_forceTransfer(current, original, amount)` |
| LIQUIDATE excluded from state machine | Force transfer + external DEX interaction | Implemented in ERC-TRUST Extensions |
| SEIZED → FROZEN direct transition | Seizure is strictly stronger than freezing (legal precedence) | Path: RELEASE → ACTIVE → FREEZE |
| FROZEN → RESTRICTED direct transition | Must pass through ACTIVE | Path: UNFREEZE → ACTIVE → RESTRICT |

## Synchronization Protocol

### Lock Mechanism

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `acquire_lock` / `release_lock` | OSS preemptive lock (Rust) | Model assumes atomic lock; implementation uses distributed locking. Refinement of atomicity is the subject of Property 5 |
| `is_locked` predicate | Lock status check in OSS State DB | |

### Sync Operation

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `sync` function (5-step protocol) | OSS sync workflow (Rust) | Model steps: verify → check transition → lock → update all → unlock. Implementation uses BVC (Bind-Verify-Commit) 3-phase execution which collectively satisfies the model's atomic sync specification |
| `connected_chains` | OSS chain registry | Set of chains holding a given asset; registry-backed dynamic lookup replaces the model's finite set |
| `update_all_chains` | OSS cross-chain message broadcast | Model is synchronous; implementation is asynchronous with finality tracking. Propagation failure recovery is subject of Property 8 |

### Global State

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `global_state` record | OSS State DB (RocksDB) | |
| `valid_state` invariant | Runtime invariant check | `consistent_state ∧ no_locked_without_reason` |
| `consistent_state` | Cross-chain state consistency check | All chains agree on regulatory state for each asset |

---

# Property 2: Priority Resolution and Liveness

## Priority Key Construction

### Authority Hierarchy

| Formal Model (`DQuencer_Instance.thy`) | Implementation Target | Notes |
|---|---|---|
| `datatype authority_level = Regional \| National \| International` | RCP authority hierarchy in OSS config (Rust) | Maps to RCP's jurisdictional priority model (international > national > regional) |
| `authority_rank` (Regional=1, National=2, International=3) | Priority weight in D-quencer sequencer (Rust) | Integer ranking for ordering |

### Priority Key Components

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `priority_key = nat × nat × nat × nat` | 4-tuple priority encoding in D-quencer (Rust) | Rust's derived `Ord` for tuples matches Isabelle's product linorder |
| `make_priority_key max_time max_node msg` | `compute_priority_key(msg)` in D-quencer | 4 components: authority, inverted timestamp, action severity, inverted node ID |
| `priority_key_injectivity` theorem | Tiebreaking guarantee | Distinct messages never share the same priority key; candidate for Creusot precondition in Phase 4 |
| `action_severity` (7 levels from UNRESTRICT=1 to CONFISCATE=7) | Action severity config in D-quencer | Stronger enforcement actions take precedence |

### Selection Algorithm

| Formal Model (`Priority_Resolution.thy`) | Implementation Target | Notes |
|---|---|---|
| `priority_system` locale | Generic priority-based selection interface | Reusable across any linorder-keyed selection |
| `select_highest_deterministic` theorem | BFT consensus output uniqueness | Guarantees deterministic consensus result |
| `bft_select` function | D-quencer consensus output function (Rust) | Filters valid messages + sorts by priority + returns highest |

## BFT Consensus Configuration

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `dquencer_system` locale | D-quencer system parameters | BFT threshold, lock timeout, fairness bound, max bounds |
| `bft_threshold: card nodes ≥ 3 * f_max + 1` | Network configuration constraint | Standard BFT (n ≥ 3f+1); enforced at genesis |
| `byzantine_bound: card byzantine_nodes ≤ f_max` | Byzantine fault assumption | Not directly enforced; ensured by honest majority assumption |
| `honest_majority` theorem | Security invariant | Honest nodes > 2f (derived from BFT threshold) |

## Deadlock Freedom

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `deadlock_free_locking` locale | OSS preemptive lock with timeout (Rust) | Generic timeout-based locking |
| `timeout: nat, timeout > 0` | `lock_timeout` config parameter | OSS configuration, must be positive; `Duration` type in Rust |
| `lock_effective` definition | Lock check with timestamp comparison | `current_time < lock_time + timeout` |
| `lock_eventually_expires` theorem | Byzantine lock resistance guarantee | Even indefinitely-held locks expire by timeout |
| `deadlock_freedom` theorem | Lock release bound | Lock released within `timeout` time units after acquisition; candidate for Kani model checking in Phase 3 |

## Starvation Freedom

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `fair_leader_system` locale | D-quencer VRF-based leader election + epoch management (Rust) | Abstracts VRF randomness as deterministic fairness assumption; see rationale in Assumption Gap Analysis |
| `fairness_bound: nat, fairness_bound > 0` | VRF election parameters | Probability of Byzantine leaders k times in a row is `(f/n)^k`, abstracted as deterministic bound |
| `fair_leader` assumption | Honest leader within bounded epochs | Holds probabilistically under BFT threshold |
| `honest_progress` assumption | Honest leader reduces pending count | Must be enforced in D-quencer implementation; synchronous network precondition |
| `starvation_bound` theorem | Pending count strictly decreases within fairness bound | Implementation: monitoring dashboard for pending count trends |
| `eventual_completion` theorem | All pending requests eventually processed | By well-founded induction on pending count |

## Combined Safety + Liveness

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `combined_safety_liveness` theorem | End-to-end guarantee: sync succeeds AND preserves validity | Ties Property 1's `valid_state_preservation` with Property 2's liveness guarantees |

---

## Assumption Gap Analysis

The formal model makes simplifying assumptions. This section documents each assumption and how the implementation addresses the gap. Assumption explicitness is a design property: it makes the scope of mechanical verification transparent and enables compositional refinement through subsequent properties.

### Property 1 Assumptions

| Model Assumption | Implementation Reality | Gap Mitigation | Release Plan |
|---|---|---|---|
| Synchronous execution (lock → update → unlock is atomic) | Asynchronous cross-chain communication with variable finality | OSS BVC (Bind-Verify-Commit) 3-phase execution collectively satisfies atomicity; per-chain finality tracked; commits only after all chains finalize | Partial release in Property 5 (lock atomicity), Property 8 (propagation failure recovery) |
| Honest nodes | Byzantine nodes possible | D-quencer BFT consensus with slashing | Released by Property 2 |
| Finite chain set | Chain set can change over time | RWA Registry manages chain membership; new chains require governance approval | Open Question 2 (dynamic domain topology) |
| Lock acquisition is instant | Network latency exists | Timeout-based lock expiration with automatic rollback | Property 5 (Preemptive Lock Correctness) |

### Property 2 Assumptions

| Model Assumption | Implementation Reality | Gap Mitigation | Release Plan |
|---|---|---|---|
| `fair_leader` deterministic guarantee | VRF-based probabilistic leader election | VRF + leader rotation enforcement + view change mechanisms + L3 force inclusion for extreme cases | Deterministic abstraction retained (see rationale below); probabilistic interpretation is composable but not formalized in current proofs |
| `honest_progress` (honest leader reduces pending) | Synchronous network with non-empty valid request queue | Standard BFT liveness model; bounded request arrival via admission control | Partial synchrony generalization is Open Question 1 |
| `non_honest_bounded` (closed system) | Dynamic request arrival | Open-system extension listed as open question | Open Question 3 (open system starvation freedom) |
| Atomic lock acquisition (Property 2) | Distributed lock contention | Lock queue + timeout + automatic release | Property 5 |

### Rationale for the Deterministic `fair_leader` Abstraction

The `fair_leader` assumption requires that within any `fairness_bound` consecutive epochs, at least one epoch has an honest leader. This is stated deterministically, but actual VRF leader election is probabilistic: under f < n/3 Byzantine faults, the probability of k consecutive Byzantine leaders is `(f/n)^k < (1/3)^k`, which decreases exponentially but is not zero.

The deterministic abstraction is retained for the following reasons:

- Direct probabilistic verification in Isabelle/HOL would require HOL-Probability and substantially complicate the proof. It would also change the nature of the result from "liveness guaranteed" to "liveness almost surely", which is a weaker claim.
- The deterministic abstraction belongs to the Heard-Of model tradition (Charron-Bost & Schiper 2009). Wanner et al. (SRDS 2020) applied this tradition to log replication protocols in Isabelle/HOL with successful academic reception.
- Probabilistic interpretation of VRF randomness is composable as an independent module on top of the deterministic guarantee. The `fairness_bound` k is an operational parameter chosen so that `(f/n)^k` is negligibly small (e.g., k=10 gives probability < 0.002% under f/n ≤ 1/3).
- Extreme failure cases (very long runs of Byzantine leaders) are covered at the implementation layer by view change mechanisms and L3 force inclusion.

This abstraction is a separation of concerns: the Isabelle/HOL proof establishes liveness conditional on the deterministic fairness, and the implementation provides the fairness through VRF + view change + force inclusion. Probabilistic composition with the model is possible but deferred.

---

## Assumption Release Roadmap

This section maps each model assumption to the future property (if any) that releases it.

| Current Assumption | Released By | Residual After Release | Final Resolution |
|---|---|---|---|
| Honest nodes (Property 1) | Property 2 (Byzantine consensus with f < n/3) | Byzantine consensus liveness | Released within the model |
| Atomic sync: lock acquisition and release atomicity | Property 5 (Preemptive Lock Correctness) | Multi-step protocol correctness under timing | Resolved at the preemptive lock layer |
| Atomic sync: cross-chain propagation success | Property 8 (Cross-Chain Pre-trading Finality) | Recovery from propagation failures | Resolved via pending sync queue mechanism |
| Fair leader (deterministic) | Not released within FV 1–9 scope | Probabilistic VRF composition | Deferred to separate probabilistic verification work (not currently scheduled) |
| Honest progress (synchronous network) | Partially addressed by Property 8 timing model | Full partial synchrony | Open Question 1 (future work) |
| Closed system (no dynamic arrivals) | Not released within FV 1–9 scope | Open system liveness | Open Question 3 (future work) |
| Finite connected_chains (static topology) | Not released within FV 1–9 scope | Dynamic topology | Open Question 2 (future work) |

The CDSP paper's four Open Questions are elaborated here:

1. **Partial synchrony extension**: Generalize `fair_leader` and `honest_progress` to partial synchrony. Related work: Castro & Liskov PBFT, HotStuff. Potential approach: Heard-Of model with partial synchrony variants.
2. **Dynamic topology**: Extend `multi_domain_preservation` to handle chains joining/leaving the connected set. Requires invariant-preserving topology updates.
3. **Open system starvation freedom**: Release `non_honest_bounded` assumption. Standard approach: admission control bounds + amortized analysis.
4. **Model-implementation refinement**: The subject of Phases 2–6 with Creusot/Kani. This document itself is the starting point.

---

## Verification Scope for Creusot and Kani (Phases 2–6)

When refinement proof work begins in Phase 2, the following scope applies:

- **In Creusot scope**: Function-level pre/postconditions derived from model theorems (state transition correctness, priority key injectivity, lock effectiveness predicate, no self-loops).
- **In Kani scope**: Bounded model checking for concurrency-sensitive code (lock acquisition races, consensus message ordering, timeout expiration races).
- **Out of both scopes**: Probabilistic VRF properties, network-level timing, cryptographic primitives (BLS signature correctness is assumed from the `bls-signatures` crate). These require either probabilistic verification tools (not currently scheduled) or acceptance as unverified external components.

Specific theorems targeted for refinement annotation in each phase are listed under "Candidate for Creusot annotation" and "Candidate for Kani model checking" notes in the mapping tables above.

---

## Theorem-to-Test Correspondence

Until formal refinement proofs (model → code) are available, the following test strategy bridges the gap. All tests will be implemented using `cargo test` + `proptest` for property-based testing.

### Property 1 Theorems

| Theorem | Test Strategy | Status |
|---|---|---|
| `confiscated_terminal` | Unit test: all actions on CONFISCATED return revert | Planned |
| `confiscate_universal` | Unit test: CONFISCATE succeeds from all non-CONFISCATED states | Planned |
| `no_self_loops` | Unit test: post-state ≠ pre-state for all valid transitions | Planned |
| `regulatory_homomorphism` | Integration test: sync produces consistent state across mock chains | Planned |
| `valid_state_preservation` | Integration test: valid_state holds before and after sync | Planned |
| `sync_isolation` | Integration test: sync on asset A does not affect asset B | Planned |

### Property 2 Theorems

| Theorem | Test Strategy | Status |
|---|---|---|
| `select_highest_deterministic` | Unit test: given same message set, D-quencer produces identical output across runs | Planned |
| `priority_key_injectivity` | Unit test: distinct messages (by any of 4 fields) produce distinct priority keys | Planned |
| `lock_eventually_expires` | Integration test: simulated Byzantine node holds lock; verify expiration by timeout | Planned |
| `deadlock_freedom` | Integration test: concurrent lock requests + timeout; verify no permanent block | Planned |
| `starvation_bound` | Integration test: repeated Byzantine leader attempts; verify honest leader within `fairness_bound` | Planned |
| `eventual_completion` | Integration test: simulated load with pending requests; verify queue drains | Planned |
| `combined_safety_liveness` | End-to-end test: Byzantine environment, cross-chain sync under concurrent regulatory actions | Planned |

---

## Update Policy

This document is updated when:

- New `.thy` files are added (Property 3 and beyond)
- Implementation code is written that corresponds to model elements
- A model-implementation gap is discovered
- Model assumptions change
- A new assumption release relationship is established by a completed property

Changes are committed with the message format: `mapping update: [reason]`

## Change Log

| Version | Date | Change |
|---|---|---|
| 0.3.0 | 2026-04-17 | Added "What Verification Establishes and What It Does Not" scope declaration. Added rationale for deterministic `fair_leader` abstraction (Heard-Of model tradition, Wanner et al. SRDS 2020 precedent). Added "Assumption Release Roadmap" section making the verification program's trajectory transparent. Added "Verification Scope for Creusot and Kani" section. Updated Implementation Target column: OSS and D-quencer language changed from Go to Rust (reflecting Oraclizer Core Rust transition). Added candidate annotations for Phase 2 Creusot and Phase 3 Kani work. |
| 0.2.0 | 2026-04-07 | Initial mapping for Properties 1 and 2. |
