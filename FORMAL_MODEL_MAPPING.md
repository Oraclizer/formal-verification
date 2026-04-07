# Formal Model to Implementation Mapping

**Version:** 0.2.0
**Last updated:** 2026-04-07
**Status:** Pre-implementation (model-only; implementation columns to be populated during development)

## Purpose

This document tracks the correspondence between formally verified model elements in the `.thy` files and their planned implementation in Oraclizer's codebase. It serves three purposes:

1. **Design reference:** Implementation code should match the verified model's state transition rules and liveness parameters
2. **Traceability:** External reviewers can verify that the implementation follows the formal specification
3. **Gap tracking:** Identifies where the model makes assumptions that the implementation must satisfy through other means

## Coverage Scope

This mapping covers:

- **Property 1 (Cross-Domain State Preservation Homomorphism)** — safety
- **Property 2 (D-quencer Determinism, Deadlock Freedom, Starvation Freedom)** — liveness

Property 3 (Heterogeneous Verification Composition) will be added when it is completed.

---

# Property 1: State Preservation (Safety)

## State Transition Model

### Regulatory States

| Formal Model (`Regulatory_Instance.thy`) | Implementation Target | Notes |
|---|---|---|
| `datatype reg_state = ACTIVE \| FROZEN \| SEIZED \| CONFISCATED \| RESTRICTED` | `enum RegState` in Solidity (ERC-TRUST Core) | Direct 1:1 mapping |
| `CONFISCATED` as terminal state | `require(state != RegState.CONFISCATED)` guard | Enforced by `confiscated_terminal` theorem |

### Regulatory Actions

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `datatype reg_action = FREEZE \| SEIZE \| CONFISCATE \| RESTRICT \| UNFREEZE \| UNRESTRICT \| RELEASE` | `enum RegAction` in Solidity + corresponding functions | RECOVER and LIQUIDATE are force transfers, not state transitions (see Design Decisions) |

### Transition Function

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `fun reg_transition` (35 rules) | State transition logic in Solidity | Each `(state, action) → state'` rule maps to a `require` + state update |
| `no_self_loops` theorem | Assertion: post-state ≠ pre-state | Implementation should include this as a post-condition check |

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
| `acquire_lock` / `release_lock` | OSS preemptive lock (Go) | Model assumes atomic lock; implementation uses distributed locking |
| `is_locked` predicate | Lock status check in OSS State DB | |

### Sync Operation

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `sync` function (5-step protocol) | OSS sync workflow (Go) | Steps: verify → check transition → lock → update all → unlock |
| `connected_chains` | OSS chain registry | Set of chains holding a given asset |
| `update_all_chains` | OSS cross-chain message broadcast | Model is synchronous; implementation is asynchronous with finality tracking |

### Global State

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `global_state` record | OSS State DB (LevelDB/RocksDB) | |
| `valid_state` invariant | Runtime invariant check | `consistent_state ∧ no_locked_without_reason` |
| `consistent_state` | Cross-chain state consistency check | All chains agree on regulatory state for each asset |

---

# Property 2: Priority Resolution and Liveness

## Priority Key Construction

### Authority Hierarchy

| Formal Model (`DQuencer_Instance.thy`) | Implementation Target | Notes |
|---|---|---|
| `datatype authority_level = Regional \| National \| International` | RCP authority hierarchy in OSS config | Maps to RCP's jurisdictional priority model (international > national > regional) |
| `authority_rank` (Regional=1, National=2, International=3) | Priority weight in D-quencer sequencer | Integer ranking for ordering |

### Priority Key Components

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `priority_key = nat × nat × nat × nat` | 4-tuple priority encoding in D-quencer (Go) | Lexicographic order from Isabelle's product linorder |
| `make_priority_key max_time max_node msg` | `computePriorityKey(msg)` in D-quencer | 4 components: authority, inverted timestamp, action severity, inverted node ID |
| `priority_key_injectivity` theorem | Tiebreaking guarantee | Distinct messages never share the same priority key |
| `action_severity` (7 levels from UNRESTRICT=1 to CONFISCATE=7) | Action severity config in D-quencer | Stronger enforcement actions take precedence |

### Selection Algorithm

| Formal Model (`Priority_Resolution.thy`) | Implementation Target | Notes |
|---|---|---|
| `priority_system` locale | Generic priority-based selection interface | Reusable across any linorder-keyed selection |
| `select_highest_deterministic` theorem | BFT consensus output uniqueness | Guarantees deterministic consensus result |
| `bft_select` function | D-quencer consensus output function | Filters valid messages + sorts by priority + returns highest |

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
| `deadlock_free_locking` locale | OSS preemptive lock with timeout (Go) | Generic timeout-based locking |
| `timeout: nat, timeout > 0` | `lock_timeout` config parameter | OSS configuration, must be positive |
| `lock_effective` definition | Lock check with timestamp comparison | `currentTime < lockTime + timeout` |
| `lock_eventually_expires` theorem | Byzantine lock resistance guarantee | Even indefinitely-held locks expire by timeout |
| `deadlock_freedom` theorem | Lock release bound | Lock released within `timeout` time units after acquisition |

## Starvation Freedom

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `fair_leader_system` locale | D-quencer VRF-based leader election + epoch management | Abstracts VRF randomness as fairness assumption |
| `fairness_bound: nat, fairness_bound > 0` | VRF election parameters | Probability of Byzantine leaders k times in a row is `(f/n)^k`, abstracted as deterministic bound |
| `fair_leader` assumption | Honest leader within bounded epochs | Holds probabilistically under BFT threshold |
| `honest_progress` assumption | Honest leader reduces pending count | Must be enforced in D-quencer implementation |
| `starvation_bound` theorem | Pending count strictly decreases within fairness bound | Implementation: monitoring dashboard for pending count trends |
| `eventual_completion` theorem | All pending requests eventually processed | By well-founded induction on pending count |

## Combined Safety + Liveness

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `combined_safety_liveness` theorem | End-to-end guarantee: sync succeeds AND preserves validity | Ties Property 1's `valid_state_preservation` with Property 2's liveness guarantees |

---

## Model Assumptions vs. Implementation Reality

The formal model makes simplifying assumptions. This section documents each assumption and how the implementation addresses the gap.

| Model Assumption | Reality | Implementation Mitigation |
|---|---|---|
| Synchronous execution (lock → update → unlock is atomic) | Asynchronous cross-chain communication with variable finality | OSS tracks per-chain finality; commits only after all chains finalize (BVC pattern) |
| Honest nodes (Property 1) | Byzantine nodes possible | D-quencer BFT consensus with slashing (addressed by Property 2) |
| Finite chain set | Chain set can change over time | RWA Registry manages chain membership; new chains require governance approval |
| Lock acquisition is instant | Network latency exists | Timeout-based lock expiration with automatic rollback |
| Fairness assumption (Property 2) | VRF-based probabilistic election | VRF + leader rotation enforcement; probability of k Byzantine leaders in a row is `(f/n)^k`, exponentially decreasing |
| Closed system (fixed request set) | Dynamic request arrival | Open-system extension is listed as an open question |
| Atomic lock acquisition (Property 2) | Distributed lock contention | Lock queue + timeout + automatic release |

---

## Theorem-to-Test Correspondence

Until formal refinement proofs (model → code) are available, the following test strategy bridges the gap:

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

- New `.thy` files are added (Property 3)
- Implementation code is written that corresponds to model elements
- A model-implementation gap is discovered
- Model assumptions change

Changes are committed with the message format: `mapping update: [reason]`
