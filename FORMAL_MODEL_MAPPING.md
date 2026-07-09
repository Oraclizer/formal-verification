# Formal Model to Implementation Mapping

**Version:** 0.5.2
**Last updated:** 2026-07-03
**Status:** Pre-implementation (model-only; implementation columns to be populated during development)

## Purpose

This document tracks the correspondence between formally verified model elements in the `.thy` files and their planned implementation in Oraclizer's codebase. It serves four purposes:

1. **Design reference:** Implementation code should match the verified model's state transition rules, liveness parameters, and degree-hierarchy guarantees.
2. **Traceability:** External reviewers can verify that the implementation follows the formal specification.
3. **Gap tracking:** Identifies where the model makes assumptions that the implementation must satisfy through other means. Assumption explicitness is treated as a design property, not a limitation.
4. **Assumption scope:** Documents, for each model assumption, whether it is discharged within the current proofs or handled at the implementation layer. Assumption explicitness is treated as a design property, not a limitation.

## Coverage Scope

This mapping covers:

- **Property 1 (Cross-Domain State Preservation Homomorphism)**: safety
- **Property 2 (D-quencer Determinism and Starvation Freedom)**: liveness (deadlock is a scope note, not a proved result; see the Deadlock section below)
- **Cross-Domain State Preservation Functor**: functor laws (identity / composition / associativity over state-preservation morphisms), authenticated cross-domain state soundness via the Merkle interface, and guarded bounded convergence with terminal-faithful safe recovery
- **Authenticated Functor and Canton Instantiation**: composite functor laws over the authenticated extraction map, sequence-level authenticity preservation (validity, need-to-know, hash soundness, state-level inclusion), and instantiation on the concrete ADS blindable functor and a recursive model of the Canton transaction tree
- **Synchronization-Degree Hierarchy**: composable natural transformations between degree functors and degree-class monotonicity (over-provisioning safe, under-provisioning unsafe)
- **Domain-Independence Instance**: an out-of-regulatory-domain instance discharging the generic locales
- **Proof Automation**: reusable Eisbach discharge methods for the generic locale obligations

All theory files mapped below are mechanically checked by Isabelle/HOL 2025-2 with no `sorry` or `oops` occurrences.

## What Verification Establishes and What It Does Not

The Isabelle/HOL proofs in this repository establish properties at the **model level**. All proofs are mechanically checked by Isabelle/HOL 2025-2 with no `sorry` or `oops` occurrences. Mechanical correctness is thus established: the lemmas are valid within the stated assumptions.

The current proofs do **not** establish:

- Correspondence between the Isabelle/HOL model and the Rust implementation (refinement proof; addressed during refinement-proof work using Creusot/Kani).
- Probabilistic properties of VRF-based leader election (abstracted as the deterministic `fair_leader` assumption; see Assumption Gap Analysis below).
- Network-level properties such as message loss, partial synchrony, or dynamic topology changes (handled at the implementation layer; see Assumption Disposition below).
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
| `no_self_loops` theorem | Assertion: post-state ≠ pre-state | Implementation should include this as a post-condition check; refinement-annotation candidate for Creusot |

### Design Decisions (Exclusions)

These exclusions are formally justified in `Regulatory_Instance.thy`:

| Exclusion | Formal Justification | Implementation Note |
|---|---|---|
| RECOVER excluded from state machine | Force transfer operation, not a state transition | Implemented as a force-transfer operation |
| LIQUIDATE excluded from state machine | Force transfer + external DEX interaction | Implemented in ERC-TRUST Extensions |
| SEIZED → FROZEN direct transition | Seizure is strictly stronger than freezing (legal precedence) | Path: RELEASE → ACTIVE → FREEZE |
| FROZEN → RESTRICTED direct transition | Must pass through ACTIVE | Path: UNFREEZE → ACTIVE → RESTRICT |

## Synchronization Protocol

### Lock Mechanism

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `acquire_lock` / `release_lock` | OSS preemptive lock (Rust) | Model assumes atomic lock; implementation uses distributed locking. Refinement of atomicity is the subject of the preemptive-lock layer |
| `is_locked` predicate | Lock status check in OSS State DB | |

### Sync Operation

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `sync` function (5-step protocol) | OSS sync workflow (Rust) | Model steps: verify → check transition → lock → update all → unlock. Implementation uses BVC (Bind-Verify-Commit) 3-phase execution which collectively satisfies the model's atomic sync specification |
| `connected_chains` | OSS chain registry | Set of chains holding a given asset; registry-backed dynamic lookup replaces the model's finite set |
| `update_all_chains` | OSS cross-chain message broadcast | Model is synchronous; implementation is asynchronous with finality tracking. Propagation failure recovery is the subject of the cross-chain finality layer |

### Global State

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `global_state` record | OSS State DB (embedded key-value store) | |
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
| `priority_key_injectivity` theorem | Tiebreaking guarantee | Distinct messages never share the same priority key; refinement-annotation candidate for a Creusot precondition |
| `action_severity` (7 levels from UNRESTRICT=1 to CONFISCATE=7) | Action severity config in D-quencer | Stronger enforcement actions take precedence |

### Selection Algorithm

| Formal Model (`Priority_Resolution.thy`) | Implementation Target | Notes |
|---|---|---|
| `priority_system` locale | Generic priority-based selection interface | Reusable across any linorder-keyed selection |
| `select_highest_deterministic` theorem | BFT consensus output uniqueness | Guarantees deterministic consensus result |
| `dq_select_highest_deterministic` corollary | D-quencer consensus output function (Rust) | Runs the generic `select_highest` on the D-quencer priority-key set and recovers the unique highest-priority well-formed message (via `recover_msg`); maximality over the whole message set is `dq_select_highest_message_maximal` |

## BFT Consensus Configuration

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `dquencer_system` locale | D-quencer system parameters | BFT threshold, fairness bound, max time/node bounds |
| `bft_threshold: card nodes ≥ 3 * f_max + 1` | Network configuration constraint | Standard BFT (n ≥ 3f+1); enforced at genesis |
| `byzantine_bound: card byzantine_nodes ≤ f_max` | Byzantine fault assumption | Not directly enforced; ensured by honest majority assumption |
| `honest_majority` theorem | Security invariant | Honest nodes > 2f (derived from BFT threshold) |

## Deadlock (Out of Scope)

The atomic `sync` model has no concurrent lock contention, so deadlock does not arise within the model's scope; forced lock release under contention is deferred to a preemptive-lock layer. No deadlock formal model is mapped here.

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
| `conditional_safety_preservation` theorem | Conditional safety: from valid + unlocked, sync succeeds and preserves validity | Restates `valid_state_preservation` under the unlocked precondition; its proof uses only the safety side (no liveness interpretations). The unconditional fusion of safety and liveness is `oraclizer_guarded_bounded_convergence` |
| `liveness_inhabitable` theorem | Satisfiability of the fair-leader assumption | Derives a roster-drawn fair schedule (`range ls ⊆ nodes`) from the in-roster honest node the BFT threshold guarantees (via `fair_schedule_exists`); a satisfiability witness for the liveness locale — the convergence headline consumes the fair-leader assumption directly rather than routing through this witness; `bft_quorum` is a non-degenerate (n=4, f=1) witness |

---

# Cross-Domain State Preservation Functor

## Functor Laws over State-Preservation Morphisms

| Formal Model (`Functor_Laws.thy`, `Composition.thy`) | Implementation Target | Notes |
|---|---|---|
| `preservation_id` | Identity adapter between OSS state-machine views (Rust) | The identity morphism (id, id) is a state-preservation morphism; corresponds to a no-op domain adapter |
| `preservation_compose` | Composed cross-domain adapter pipeline (Rust) | Chaining two domain adapters (e.g. DAML → regulatory → Chain B) is itself a valid preservation morphism; OSS composes adapters at the registry layer |
| `preservation_assoc` | Adapter pipeline reassociation | Composition order of adapter legs is associative; allows the OSS pipeline to group adapter stages freely |
| `daml_to_chain_b_composed` | Three-domain adapter (DAML record → regulatory enum → Chain B vocabulary) (Rust) | Obtained purely by composing two legs; mirrors the Canton/DAML → OSS → EVM adapter chain |
| `guard_is_load_bearing` | Domain-guard enforcement in adapters | The domain guard is essential; implementation must reject out-of-domain records (e.g. RELEASE outside the carved-out domain) rather than projecting blindly |

## Authenticated Cross-Domain State (Merkle Interface Coupling)

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `merkle_interface_auth` | Authenticated state commitment over (regulatory state, chain-set) pairs | OSS State DB commitment layer; the concrete triple (hash, blinding-order, merge) forms a Merkle interface (`ADS_Functor` dependency) |
| `authenticated_preservation_soundness` | Cross-chain view merge in OSS State DB (Rust) | Merging two authenticated views yields a valid join refining each input view; OSS merge of partial chain views must preserve this |
| `blinded_view_preserves_validity` | Need-to-know disclosure of cross-domain state (Rust) | A blinded view extracts to a valid state refining the original; supports selective disclosure (e.g. regulator-only views) without breaking validity |
| `state_refines_*` (refl / trans / preserves_consistency) | Partial-view refinement relation | OSS partial-view semantics; refinement is reflexive, transitive, and preserves consistency |
| `rogue_join_excluded` | Join admission control in OSS State DB | A rogue view adding a FROZEN holding on an unrevealed chain is rejected as a join; OSS must reject inconsistent merges |

## Guarded Bounded Convergence and Safe Recovery

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `oraclizer_guarded_bounded_convergence` | OSS recovery / reconciliation loop (Rust) | From any finite-domain, unlocked state (no initial consistency assumed) the system reaches a valid state within a bounded number of evolution steps; bounds the OSS reconciliation loop |
| `inconsistent_has_safe_recovery` | OSS recovery action selection (Rust) | Any inconsistent, unlocked state admits a terminal-faithful safe recovery; recovery selection must always find a measure-reducing, terminal-faithful step |
| `sync_reduces_inconsistency` | Recovery progress measure | A synchronization on a disagreeing asset strictly decreases the inconsistency measure; OSS reconciliation must make monotone progress |
| `safe_recovery_sync_no_fresh_terminal` | Recovery confiscation guard (Rust) | A safe recovery never makes CONFISCATED appear on an asset that did not already carry it; implementation must not synthesize confiscations during recovery |
| `blind_confiscate_excluded` / `terminal_overwrite_excluded` | Recovery action validation | Indiscriminate confiscation and confiscation erasure are both excluded as safe recoveries; OSS recovery validation must reject both |
| `fair_schedule_exists` | D-quencer fair scheduling (Rust) | Every D-quencer system admits a roster-drawn fair leader schedule under the BFT threshold (an in-roster honest node exists); witnesses that the fair-leader assumption the convergence layer consumes is satisfiable within the consensus roster |

---

# Authenticated Functor and Canton Transaction-Tree Instantiation

| Formal Model (`Canton_Bridge.thy`) | Implementation Target | Notes |
|---|---|---|
| `cdsp_ads_compose` / `cdsp_ads_merge_assoc` | OSS authenticated commitment layer (Rust) | The extraction map is a composite functor from the ADS blinding preorder to the cross-domain refinement preorder; composing two domain views composes their authenticated refinements, and the lifted merge is associative |
| `sequence_authenticity_preservation` / `sequence_merge_soundness` | OSS multi-step view reconciliation (Rust) | Single-step authenticity generalizes to a whole synchronization sequence: every partial view along a path of blindings, and an n-ary fold of merges, extracts to a valid state refining the endpoint |
| `sequence_inclusion_integrity` | OSS revealed-holding inclusion check | Any holding revealed by a view in a sequence is included in the most-revealed endpoint with the same regulatory state (state-level inclusion, sharpened to concrete Merkle-path inclusion by the inclusion-proof instantiation below) |
| `oss_blindable` | OSS State DB commitment over the ADS blindable functor | Instantiation on the concrete blindable-position functor of `ADS_Functor`, beyond the bespoke interface |
| `reg_tx_authenticated` / `demo_subview_disclosure` | OSS / Canton bridge transaction commitment (Rust) | Instantiation on a recursive model of the Canton transaction tree (public rose-tree Merkle machinery, concrete content); subview-level selective disclosure is preserved in the proofs |
| `reg_view_inclusion_same_hash` / `reg_view_inclusion_blinding_of` / `reg_view_inclusion_chains_sound` | OSS Merkle inclusion-proof verifier (Rust) | The recursive view tree is instantiated on the entry's generic rose-tree inclusion-proof (zipper) machinery: each inclusion proof commits to the same root hash as the full tree, is a blinding of it, and its attested chains are contained in the full set; no added assumption |

**Model-fidelity boundary (for confirmation against the Canton specification).** The recursive Canton instance is structurally faithful, with two declared modelling choices: concrete leaf content in place of the opaque content types of the public Canton model, and a shared, non-independently-blindable consensus field (so a revealed view under a blinded consensus is out of scope). These are model-fidelity items, not proof gaps; no axiom relates the opaque Canton types to the regulatory model.

---

# Synchronization-Degree Hierarchy

| Formal Model (`Hierarchy.thy`) | Implementation Target | Notes |
|---|---|---|
| degree functors `F k` (degree-indexed) | OSS degree-classed processing paths (Rust) | Per-degree processing functor; OSS routes assets to a degree-appropriate path |
| `degree_natural_transformation` | Degree demotion / blinding map (Rust) | The degree-forgetting map is a natural transformation between adjacent degree functors with commuting squares; OSS degree demotion must commute with processing |
| `nt_compose` / `nt_vertical_compose` | Multi-step degree demotion | Demotion across multiple degrees composes as a natural transformation; OSS may demote across several degree levels at once |
| `degree_forget_refines` | Demoted-view refinement | Degree demotion produces a blinding refinement of the original state; demoted views are partial views of the full state |
| `over_provisioning_guarantees` | Capability-vs-requirement check (Rust) | When system capability degree ≥ asset required degree, all required chains holding the asset agree on its regulatory state after processing (**over-provisioning is safe**); OSS must verify capability dominates requirement before processing |
| `over_provisioning_reconciles` | Reconciliation from an arbitrary state (Rust) | From an arbitrary hub-defined state (no validity assumed), over-provisioning still drives every required chain to the hub value; shows the degree hypothesis is load-bearing, not decorative |
| `no_downward_safety` | Under-provisioning rejection (Rust) | Under-provisioning (required degree > capability) admits a state defeating every guarantee; OSS must refuse to process assets whose required degree exceeds system capability |
| `hierarchy_monotonicity` | (auxiliary) | A degree-free alias of `processing_preserves_validity` carrying no provisioning hypothesis; the capability-sensitive guarantees are the three rows above |
| `boundary_well_defined` | Causal-consistency boundary check | The boundary separating adjacent degree classes is single-valued and induced by a strict happened-before order; OSS causal ordering must respect this boundary |
| `static_promotion_safety` | Static degree re-assignment (governance) | A static re-assignment within system capability transfers the guarantee verbatim; governance-time degree changes are safe within capability |

**Note.** In-flight promotion (a re-assignment crossing a live synchronization) is out of scope for this layer.

---

# Domain-Independence Instance

| Formal Model (`External_Instance.thy`) | Implementation Target | Notes |
|---|---|---|
| `tcp_state_machine` / `conntrack_state_machine` | (No Oraclizer implementation target) | An out-of-regulatory-domain instance (TCP/RFC 793 endpoint vs. connection tracker) discharging the generic state-machine locale; demonstrates the framework carries no hidden regulatory assumptions |
| `tcp_conntrack_preservation` | (No Oraclizer implementation target) | The representation map is a full state-preservation morphism over the tracked event subset; evidence of framework generality, not a deployed component |
| `tracked_sequence_mirrored` | (No Oraclizer implementation target) | Any tracked packet sequence accepted by the endpoint is mirrored step-for-step by the tracker |

---

# Proof Automation

| Formal Model (`Proof_Automation.thy`) | Implementation Target | Notes |
|---|---|---|
| `discharge_state_machine` (Eisbach method) | (No Oraclizer implementation target) | Reusable proof-automation method closing the generic `state_machine` locale obligations via named theorem collections |
| `discharge_preservation` (Eisbach method) | (No Oraclizer implementation target) | Reusable proof-automation method closing the generic `state_preservation` locale obligations; used to re-derive the regulatory bridges through a single automated discharge |

---

## Assumption Gap Analysis

The formal model makes simplifying assumptions. This section documents each assumption and how the implementation addresses the gap. Assumption explicitness is a design property: it makes the scope of mechanical verification transparent.

### Property 1 Assumptions

| Model Assumption | Implementation Reality | Gap Mitigation | Disposition |
|---|---|---|---|
| Synchronous execution (lock → update → unlock is atomic) | Asynchronous cross-chain communication with variable finality | OSS BVC (Bind-Verify-Commit) 3-phase execution collectively satisfies atomicity; per-chain finality tracked; commits only after all chains finalize | Handled at the implementation layer (BVC phased execution and per-chain finality tracking) |
| Honest nodes | Byzantine nodes possible | D-quencer BFT consensus with slashing | Discharged by the D-quencer liveness proof (Property 2) |
| Finite chain set | Chain set can change over time | RWA Registry manages chain membership; new chains require governance approval | Handled at the implementation layer (RWA Registry membership management) |
| Lock acquisition is instant | Network latency exists | Timeout-based lock expiration with automatic rollback | Handled at the implementation layer (timeout-based lock expiration with rollback) |

### Property 2 Assumptions

| Model Assumption | Implementation Reality | Gap Mitigation | Disposition |
|---|---|---|---|
| `fair_leader` deterministic guarantee | VRF-based probabilistic leader election | VRF + leader rotation enforcement + view change mechanisms + L3 force inclusion for extreme cases | Deterministic abstraction retained in the proofs (see rationale below); the probabilistic VRF behaviour is provided at the implementation layer |
| `honest_progress` (honest leader reduces pending) | Synchronous network with non-empty valid request queue | Standard BFT liveness model; bounded request arrival via admission control | Handled at the implementation layer (admission control bounding request arrival) |
| `non_honest_bounded` (closed system) | Dynamic request arrival | Admission control bounds the active request set | Handled at the implementation layer (admission control) |
| Atomic lock acquisition (Property 2) | Distributed lock contention | Lock queue + timeout + automatic release | Handled at the implementation layer (lock queue with timeout and automatic release) |

### Functor / Convergence Layer Assumptions

| Model Assumption | Implementation Reality | Gap Mitigation | Disposition |
|---|---|---|---|
| Atomic single evolution step | OSS reconciliation runs as discrete asynchronous rounds | Each reconciliation round corresponds to one evolution step; round boundaries enforce atomicity per step | Handled at the implementation layer (reconciliation-round boundaries enforce per-step atomicity) |
| Finite-domain global state | Chain/asset domains grow over time | RWA Registry bounds the active domain at any instant; convergence bound recomputed as domain changes | Handled at the implementation layer (RWA Registry bounds the active domain) |
| Bounded fairness window (from D-quencer) | VRF-based probabilistic fairness | Inherits the `fair_leader` deterministic abstraction from Property 2 | Same as the Property 2 fair-leader disposition (see rationale below) |

### Synchronization-Degree Hierarchy Assumptions

| Model Assumption | Implementation Reality | Gap Mitigation | Disposition |
|---|---|---|---|
| Static degree assignment | Degrees may need re-assignment during operation | `static_promotion_safety` covers governance-time re-assignment within capability; in-flight promotion is out of scope | Discharged in current proofs for governance-time re-assignment (`static_promotion_safety`); in-flight promotion is out of scope of this layer |
| System capability degree known and fixed | Capability may vary across deployments | Capability declared at genesis / governance; `hierarchy_monotonicity` requires capability ≥ requirement before processing | Handled at the implementation layer (capability declared at genesis / governance) |

### Rationale for the Deterministic `fair_leader` Abstraction

The `fair_leader` assumption requires that within any `fairness_bound` consecutive epochs, at least one epoch has an honest leader. This is stated deterministically, but actual VRF leader election is probabilistic: under f < n/3 Byzantine faults, the probability of k consecutive Byzantine leaders is `(f/n)^k`, which decreases exponentially but is not zero.

The deterministic abstraction is retained for the following reasons:

- Direct probabilistic verification in Isabelle/HOL would require HOL-Probability and substantially complicate the proof. It would also change the nature of the result from "liveness guaranteed" to "liveness almost surely", which is a weaker claim.
- The deterministic abstraction belongs to the Heard-Of model tradition (Charron-Bost & Schiper 2009). Wanner et al. (SRDS 2020) applied this tradition to log replication protocols in Isabelle/HOL with successful academic reception.
- Probabilistic interpretation of VRF randomness is composable as an independent module on top of the deterministic guarantee. The `fairness_bound` k is an operational parameter chosen so that `(f/n)^k` is negligibly small (e.g., k=10 gives probability < 0.002% under f/n ≤ 1/3).
- Extreme failure cases (very long runs of Byzantine leaders) are covered at the implementation layer by view change mechanisms and L3 force inclusion.

This abstraction is a separation of concerns: the Isabelle/HOL proof establishes liveness conditional on the deterministic fairness, and the implementation provides the fairness through VRF + view change + force inclusion. Probabilistic composition with the model is possible but deferred.

---

## Assumption Disposition (current scope)

This section records, for each model assumption, whether it is discharged within the current proofs or handled at the implementation layer.

| Model Assumption | Disposition |
|---|---|
| Honest nodes (Property 1) | Discharged in current proofs by the D-quencer liveness proof (Property 2, Byzantine consensus with f < n/3) |
| Conditional safety (consistency assumed at start) | Discharged in current proofs by guarded bounded convergence: the system converges to a valid state from an arbitrary unlocked state |
| Atomic sync: lock acquisition and release atomicity | Handled at the implementation layer (timeout-based locking with automatic rollback) |
| Atomic sync: cross-chain propagation success | Handled at the implementation layer (pending sync queue with finality tracking) |
| Fair leader (deterministic) | Deterministic abstraction retained in the proofs (see rationale above); the probabilistic VRF behaviour is provided at the implementation layer |
| Honest progress (synchronous network) | Handled at the implementation layer (admission control and the cross-chain timing model) |
| Closed system (no dynamic arrivals) | Handled at the implementation layer (admission control) |
| Finite connected_chains (static topology) | Handled at the implementation layer (RWA Registry membership management) |
| Static degree assignment (hierarchy layer) | Discharged in current proofs for governance-time re-assignment (`static_promotion_safety`); in-flight promotion is out of scope of this layer |

The CDSP paper states the following open questions:

1. **Partial synchrony extension**: Generalize `fair_leader` and `honest_progress` to partial synchrony. Related work: Castro & Liskov PBFT, HotStuff. Potential approach: Heard-Of model with partial synchrony variants.
2. **Dynamic topology**: Extend `multi_domain_preservation` to handle chains joining/leaving the connected set. Requires invariant-preserving topology updates.
3. **Open system starvation freedom**: Generalize the `non_honest_bounded` assumption. Standard approach: admission control bounds + amortized analysis.
4. **Model-implementation refinement**: Establishing correspondence between the Isabelle/HOL model and the Rust implementation. This document is the starting point.

---

## Verification Scope for Creusot and Kani

During refinement-proof work, the following scope applies:

- **In Creusot scope**: Function-level pre/postconditions derived from model theorems (state transition correctness, priority key injectivity, lock effectiveness predicate, no self-loops, degree capability-vs-requirement check, recovery confiscation guard).
- **In Kani scope**: Bounded model checking for concurrency-sensitive code (lock acquisition races, consensus message ordering, timeout expiration races, reconciliation-round atomicity).
- **Out of both scopes**: Probabilistic VRF properties, network-level timing, cryptographic primitives (BLS signature correctness is assumed from an external BLS signature library). These are handled either by probabilistic verification tools or by acceptance as unverified external components.

Specific theorems treated as refinement-annotation candidates are listed under the "refinement-annotation candidate for Creusot" and "refinement-annotation candidate for Kani model checking" notes in the mapping tables above.

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
| `starvation_bound` | Integration test: repeated Byzantine leader attempts; verify honest leader within `fairness_bound` | Planned |
| `eventual_completion` | Integration test: simulated load with pending requests; verify queue drains | Planned |
| `conditional_safety_preservation` | End-to-end test: from a valid, unlocked state with an enabled transition, verify sync succeeds and the result is valid (the corollary's conditional-safety scope) | Planned |

### Functor / Convergence and Hierarchy Theorems

| Theorem | Test Strategy | Status |
|---|---|---|
| `authenticated_preservation_soundness` | Property test: random pairs of authenticated views merge to a valid join refining each input | Planned |
| `blinded_view_preserves_validity` | Property test: blinded views extract to valid states refining the original | Planned |
| `oraclizer_guarded_bounded_convergence` | Integration test: random unlocked inconsistent state reaches a valid state within the computed bound | Planned |
| `safe_recovery_sync_no_fresh_terminal` | Integration test: recovery never introduces a fresh CONFISCATED holding | Planned |
| `hierarchy_monotonicity` | Property test: over-provisioned processing preserves validity | Planned |
| `no_downward_safety` | Property test: under-provisioned processing exhibits a guarantee-defeating state | Planned |

---

## Update Policy

This document is updated when:

- New `.thy` files are added
- Implementation code is written that corresponds to model elements
- A model-implementation gap is discovered
- Model assumptions change
- An assumption disposition changes (discharged in current proofs vs. handled at the implementation layer)

Changes are committed with the message format: `mapping update: [reason]`

## Change Log

| Version | Date | Change |
|---|---|---|
| 0.5.2 | 2026-07-03 | Documentation correction: dropped "Deadlock Freedom" from the Property 2 coverage title (deadlock is a scope note, no theorem is stated), replaced the non-existent `bft_select` row with the actual `dq_select_highest_deterministic` corollary, and removed the `lock timeout` parameter from the `dquencer_system` row (the vestigial `lock_timeout`/`timeout_positive` pair was removed from the locale). Retitled the degree-monotonicity rows so `over_provisioning_guarantees` carries the capability-vs-requirement headline, added the `over_provisioning_reconciles` row (load-bearing degree hypothesis from an arbitrary state), and recorded `hierarchy_monotonicity` as a degree-free auxiliary alias. Model-level facts unchanged; all theories remain `sorry`/`oops`-free. |
| 0.5.1 | 2026-06-25 | Added `Canton_Bridge.thy` path-level Merkle inclusion mappings (`reg_view_inclusion_same_hash` / `reg_view_inclusion_blinding_of` / `reg_view_inclusion_chains_sound`): the recursive view tree is instantiated on the entry's generic rose-tree inclusion-proof (zipper) machinery, sharpening sequence-level inclusion to the concrete Merkle path with no added assumption. Monotone addition; no change to existing theories, theorems, assumptions, or dispositions. |
| 0.5.0 | 2026-06-24 | Added `Canton_Bridge.thy` mappings: composite functor laws over the authenticated extraction map, sequence-level authenticity preservation (validity / need-to-know / hash soundness / state-level inclusion), and instantiation on the concrete ADS blindable functor and a recursive model of the Canton transaction tree, with the declared model-fidelity boundary. Monotone addition; no change to existing theories, theorems, assumptions, or dispositions. |
| 0.4.1 | 2026-06-23 | Editorial pass: generalized infrastructure-specific references in the implementation-target column (storage engine, a force-transfer signature, the BLS library reference). No change to theorems, assumptions, mappings, or dispositions. |
| 0.4.0 | 2026-06-23 | Added mappings for the new theories now in the repository: the Cross-Domain State Preservation Functor (`Composition.thy`, `Functor_Laws.thy`: functor laws over preservation morphisms, authenticated cross-domain state soundness via the Merkle interface, guarded bounded convergence and terminal-faithful safe recovery), the Synchronization-Degree Hierarchy (`Hierarchy.thy`: composable natural transformations and degree-class monotonicity), the domain-independence instance (`External_Instance.thy`), and the proof-automation layer (`Proof_Automation.thy`). Added corresponding assumption-gap rows (functor/convergence and hierarchy), assumption-disposition rows, and theorem-to-test rows. All mapped theories are mechanized and `sorry`/`oops`-free. No change to the Property 1/2 assumption set or implementation targets. |
| 0.3.0 | 2026-04-17 | Added "What Verification Establishes and What It Does Not" scope declaration. Added rationale for deterministic `fair_leader` abstraction (Heard-Of model tradition, Wanner et al. SRDS 2020 precedent). Added an assumption-disposition section recording, per assumption, whether it is discharged in the proofs or handled at the implementation layer. Added "Verification Scope for Creusot and Kani" section. Added refinement-annotation candidate notes for Creusot and Kani work. |
| 0.2.0 | 2026-04-07 | Initial mapping for Properties 1 and 2. |