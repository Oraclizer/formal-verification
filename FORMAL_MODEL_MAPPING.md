# Formal Model to Implementation Mapping

**Version:** 0.1.0
**Last updated:** 2026-03-27
**Status:** Pre-implementation (model-only; implementation columns to be populated during development)

## Purpose

This document tracks the correspondence between formally verified model elements in the `.thy` files and their planned implementation in Oraclizer's codebase. It serves three purposes:

1. **Design reference:** Implementation code should match the verified model's state transition rules
2. **Traceability:** External reviewers can verify that the implementation follows the formal specification
3. **Gap tracking:** Identifies where the model makes assumptions that the implementation must satisfy through other means

## Coverage Scope

This mapping covers **Property 1 (Cross-Domain State Preservation Homomorphism)** only. Properties 2 and 3 will be added to this document as they are completed.

---

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

---

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

## Model Assumptions vs. Implementation Reality

The formal model makes simplifying assumptions. This section documents each assumption and how the implementation addresses the gap.

| Model Assumption | Reality | Implementation Mitigation |
|---|---|---|
| Synchronous execution (lock → update → unlock is atomic) | Asynchronous cross-chain communication with variable finality | OSS tracks per-chain finality; commits only after all chains finalize (BVC pattern) |
| Honest nodes | Byzantine nodes possible | D-quencer BFT consensus with slashing (Property 2 scope) |
| Finite chain set | Chain set can change over time | RWA Registry manages chain membership; new chains require governance approval |
| Lock acquisition is instant | Network latency exists | Timeout-based lock expiration with automatic rollback |

---

## Theorem-to-Test Correspondence

Until formal refinement proofs (model → code) are available, the following test strategy bridges the gap:

| Theorem | Test Strategy | Status |
|---|---|---|
| `confiscated_terminal` | Unit test: all actions on CONFISCATED return revert | Planned |
| `confiscate_universal` | Unit test: CONFISCATE succeeds from all non-CONFISCATED states | Planned |
| `no_self_loops` | Unit test: post-state ≠ pre-state for all valid transitions | Planned |
| `regulatory_homomorphism` | Integration test: sync produces consistent state across mock chains | Planned |
| `valid_state_preservation` | Integration test: valid_state holds before and after sync | Planned |
| `sync_isolation` | Integration test: sync on asset A does not affect asset B | Planned |

---

## Update Policy

This document is updated when:

- New `.thy` files are added (Property 2, 3)
- Implementation code is written that corresponds to model elements
- A model-implementation gap is discovered
- Model assumptions change

Changes are committed with the message format: `mapping update: [reason]`
