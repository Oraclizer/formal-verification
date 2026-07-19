# Formal Model to Implementation Mapping

**Version:** 0.5.6
**Last updated:** 2026-07-20
**Status:** Pre-implementation (model-only; implementation columns to be populated during development)

## Purpose

This document tracks the correspondence between formally verified model elements in the `.thy` files and their planned implementation in Oraclizer's codebase. It serves four purposes:

1. **Design reference:** Implementation code should match the verified model's state transition rules, liveness parameters, and degree-hierarchy guarantees.
2. **Traceability:** External reviewers can verify that the implementation follows the formal specification.
3. **Gap tracking and assumption scope:** Documents where assumptions are discharged at the model level and where an external or refinement obligation remains open. Assumption explicitness is treated as a design property, not a limitation.

## Coverage Scope

This mapping covers:

- **Cross-Domain State Preservation Homomorphism**: safety
- **Deterministic Selection and Aggregate Pending-Count Progress**: finite maximum selection and closed-count progress (deadlock and individual request fairness are not proved)
- **Cross-Domain State Preservation Functor**: functor laws (identity / composition / associativity over state-preservation morphisms), authenticated cross-domain state soundness via the Merkle interface, and guarded bounded convergence with terminal-faithful safe recovery
- **Authenticated Functor and Canton Instantiation**: extraction laws on the extractable sub-preorder, authenticity along blinding paths and merge folds (validity, need-to-know, hash soundness, state-level inclusion), and instantiation on the concrete ADS blindable functor and a recursive model of the Canton transaction tree
- **Synchronization-Degree Hierarchy**: composable natural transformations between degree functors and degree-class monotonicity (over-provisioning safe, under-provisioning unsafe)
- **Domain-Independence Instance**: an out-of-regulatory-domain instance discharging the generic locales
- **Proof Automation**: reusable Eisbach discharge methods for the generic locale obligations

All theory files mapped below are mechanically checked by Isabelle/HOL 2025-2 with no `sorry` or `oops` occurrences.

## What Verification Establishes and What It Does Not

The Isabelle/HOL proofs in this repository establish properties at the **model level**. All proofs are mechanically checked by Isabelle/HOL 2025-2 with no `sorry` or `oops` occurrences. Mechanical correctness is thus established: the lemmas are valid within the stated assumptions.

The current proofs do **not** establish:

- Correspondence between the Isabelle/HOL model and the Rust implementation (refinement proof; addressed during refinement-proof work using Creusot/Kani).
- Probabilistic properties of VRF-based leader election (abstracted as the deterministic `fair_leader` assumption; see Assumption Gap Analysis below).
- Individual request starvation freedom or request-identity service order; the liveness theorems use only an aggregate pending count.
- Concurrent lock contention, permanent-lock recovery, or deadlock freedom; locking is atomic and Boolean in the model.
- An executable recovery, queue, priority, or BFT algorithm for convergence; `oss_realize` uses existential choice and ignores its event when selecting recovery.
- Network-level properties such as message loss, partial synchrony, or dynamic topology changes; these remain unverified external/refinement obligations.
- Properties of unverified external components: P2P networking, external cryptographic libraries (BLS), UI, database layer.

---

# State Preservation (Safety)

## State Transition Model

### Regulatory States

| Formal Model (`Regulatory_Instance.thy`) | Implementation Target | Notes |
|---|---|---|
| `datatype reg_state = ACTIVE \| FROZEN \| SEIZED \| CONFISCATED \| RESTRICTED` | `enum RegState` in Solidity (ERC-TRUST Core) + `RegState` enum in OSS (Rust) | Direct 1:1 mapping across both layers |
| `CONFISCATED` as terminal state | Planned `require(state != RegState.CONFISCATED)` guard in Solidity and `match` arm returning `Err(TerminalState)` in Rust | `confiscated_terminal` proves model-level terminality; implementation correspondence remains unverified |

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
| RECOVER excluded from state machine | Force transfer operation, not a state transition | Planned as a separate force-transfer operation; implementation/refinement evidence is not part of this document |
| LIQUIDATE excluded from state machine | Force transfer + external DEX interaction | Planned outside the core transition model; implementation/refinement evidence is not part of this document |
| SEIZED → FROZEN direct transition | Seizure is strictly stronger than freezing (legal precedence) | Path: RELEASE → ACTIVE → FREEZE |
| FROZEN → RESTRICTED direct transition | Must pass through ACTIVE | Path: UNFREEZE → ACTIVE → RESTRICT |

## Synchronization Protocol

### Lock Mechanism

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `acquire_lock` / `release_lock` | Planned distributed lock (Rust) | The formal model has an atomic Boolean guard. No model-to-code refinement, contention protocol, timeout, or rollback property is proved here |
| `is_locked` predicate | Lock status check in OSS State DB | |

### Sync Operation

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `sync` function (5-step protocol) | Planned OSS sync workflow (Rust) | Model steps: verify → check transition → lock → update all → unlock. BVC is a candidate refinement target; no proof currently shows that an implementation satisfies the atomic model |
| `connected_chains` | OSS chain registry | Set of chains holding a given asset; registry-backed dynamic lookup replaces the model's finite set |
| `update_all_chains` | OSS cross-chain message broadcast | Model is synchronous; implementation is asynchronous with finality tracking. Propagation failure recovery is the subject of the cross-chain finality layer |

### Global State

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `global_state` record | OSS State DB (embedded key-value store) | |
| `valid_state` invariant | Runtime invariant check | `consistent_state ∧ no_locked_without_reason` |
| `consistent_state` | Cross-chain state consistency check | All chains agree on regulatory state for each asset |

---

# Deterministic Selection and Aggregate Pending-Count Progress

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
| `priority_key_injectivity` theorem | Bounded tiebreaking guarantee | If timestamp and source node are within the supplied upper bounds, messages that differ in authority, timestamp, action, or source node have different keys; the bounds are required because natural-number subtraction saturates at zero |
| `action_severity` (7 levels from UNRESTRICT=1 to CONFISCATE=7) | Action severity config in D-quencer | Stronger enforcement actions take precedence |

### Selection Algorithm

| Formal Model (`Priority_Resolution.thy`) | Implementation Target | Notes |
|---|---|---|
| `priority_system` locale | Generic priority-based selection interface | Reusable across any linorder-keyed selection |
| `select_highest_deterministic` theorem | Planned finite-set priority selector | A finite non-empty set has one selected member whose priority is maximal; this is not a consensus-protocol theorem |
| `dq_select_highest_deterministic` corollary | Planned D-quencer priority selector (Rust) | Runs `select_highest` on a finite D-quencer message set and returns the unique selected member with maximal priority; BFT execution is outside the theorem |

## BFT Consensus Configuration

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `dquencer_system` locale | D-quencer system parameters | BFT threshold, fairness bound, max time/node bounds |
| `bft_threshold: card nodes ≥ 3 * f_max + 1` | Planned network configuration constraint | Standard static cardinality premise (n ≥ 3f+1); a genesis/configuration enforcement check remains unverified |
| `byzantine_bound: card byzantine_nodes ≤ f_max` | Byzantine fault assumption | Assumed directly; together with the threshold it yields `honest_majority`, not conversely |
| `honest_majority` theorem | Security invariant | Honest nodes > 2f (derived from BFT threshold) |

## Deadlock (Out of Scope)

The atomic `sync` model has no concurrent lock contention, so deadlock does not arise within the model's scope. No forced-release, timeout, or deadlock formal model is mapped here.

## Aggregate Pending-Count Progress

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `fair_leader_system` locale | Planned leader scheduling / epoch management | Deterministically assumes an honest-tagged leader in every bounded window; no VRF distribution or network semantics are present |
| `fairness_bound: nat, fairness_bound > 0` | Planned scheduling parameter | A logical window bound derived positive from the fairness assumption, not a probabilistic security parameter |
| `dquencer_liveness.fair_leader` assumption | In-roster schedule with honest-tagged leader within bounded epochs | Assumed; the BFT-count threshold only supplies a constant in-roster satisfiability witness, not an operational leader-election guarantee |
| `honest_progress` assumption | Honest-tagged scheduled event reduces aggregate pending count | Assumed; request identity, queue order, admission, and network delivery are not modelled |
| `non_honest_bounded` / `pending_non_increasing` assumption | Aggregate pending count never increases | Assumed globally, including at non-honest slots; encodes a closed non-increasing count trace |
| `starvation_bound` theorem | Aggregate pending count strictly decreases within fairness bound | Requires in-roster fair leadership, honest-slot progress, and global non-increase; does not identify the discharged request |
| `eventual_completion` theorem | Aggregate pending count eventually reaches zero | Requires the same three assumptions; closed-count result by well-founded induction, without continuous arrivals or per-request fairness |

## Combined Safety + Liveness

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `conditional_safety_preservation` theorem | Conditional safety: from valid state + enabled transition, sync succeeds and preserves validity | Validity itself supplies the no-lock fact. The proof uses only the safety side; bounded convergence is a separate fair-discharge composition |
| `liveness_inhabitable` theorem | Satisfiability of the fair-leader assumption | Derives a roster-drawn fair schedule (`range ls ⊆ nodes`) from the in-roster honest node the BFT threshold guarantees (via `fair_schedule_exists`); this is only a satisfiability witness for the scheduling assumption, while aggregate progress still assumes honest processing and global non-increase and guarded convergence has its own guard/recovery/progress assumptions; `bft_quorum` is a non-degenerate (n=4, f=1) witness |

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
| `merkle_interface_auth` | State-keyed reveal-set algebraic witness | `auth_hash = fst` commits only to the regulatory state; the chain set is manipulated by blinding and merge and is not itself cryptographically committed by this instance |
| `authenticated_preservation_soundness` | Cross-chain view merge in OSS State DB (Rust) | Merging two authenticated views yields a valid join that each input view refines; OSS merge of partial chain views must preserve this |
| `blinded_view_preserves_validity` | Need-to-know disclosure of cross-domain state (Rust) | A blinded view extracts to a valid state refining the original; supports selective disclosure (e.g. regulator-only views) without breaking validity |
| `state_refines_*` (refl / trans / preserves_consistency) | Partial-view refinement relation | OSS partial-view semantics; refinement is reflexive, transitive, and preserves consistency |
| `rogue_join_excluded` | Join admission control in OSS State DB | A rogue view adding a FROZEN holding on an unrevealed chain is rejected as a join; OSS must reject inconsistent merges |

## Guarded Bounded Convergence and Safe Recovery

| Formal Model | Implementation Target | Notes |
|---|---|---|
| `oraclizer_guarded_bounded_convergence` | Planned recovery/refinement target | Proves an existential bounded run. `oss_realize` uses `SOME` and does not derive recovery from the scheduled event, queue, priority selection, or BFT execution |
| `inconsistent_has_safe_recovery` | Planned recovery-selection specification | Any inconsistent finite-domain unlocked state admits a terminal-faithful safe recovery; no executable selector or model-to-code refinement is supplied |
| `sync_reduces_inconsistency` | Recovery progress measure | A synchronization on a disagreeing asset strictly decreases the inconsistency measure; OSS reconciliation must make monotone progress |
| `safe_recovery_sync_no_fresh_terminal` | Recovery confiscation guard (Rust) | A safe recovery never makes CONFISCATED appear on an asset that did not already carry it; implementation must not synthesize confiscations during recovery |
| `blind_confiscate_excluded` / `terminal_overwrite_excluded` | Recovery action validation | Indiscriminate confiscation and confiscation erasure are both excluded as safe recoveries; OSS recovery validation must reject both |
| `fair_schedule_exists` | D-quencer fair scheduling (Rust) | Every D-quencer system admits a roster-drawn fair leader schedule under the BFT threshold (an in-roster honest node exists); witnesses that the scheduling component used by the convergence interpretation is satisfiable within the roster, while the exported theorem remains in the full liveness locale |

---

# Authenticated Functor and Canton Transaction-Tree Instantiation

| Formal Model (`Canton_Bridge.thy`) | Implementation Target | Notes |
|---|---|---|
| `cdsp_ads_compose` / `cdsp_ads_merge_assoc` | Planned authenticated commitment layer (Rust) | On extractable endpoints/sub-preorder, composing blinding morphisms composes extracted refinements, and lifted merge is associative; extraction is partial in the generic locale |
| `sequence_authenticity_preservation` / `sequence_merge_soundness` | Planned authenticated-view handling | Guarantees range over a blinding path and an n-ary merge fold, not a protocol execution trace |
| `sequence_inclusion_integrity` | OSS revealed-holding inclusion check | Any holding revealed by a view in a sequence is included in the most-revealed endpoint with the same regulatory state (state-level inclusion, sharpened to concrete Merkle-path inclusion by the inclusion-proof instantiation below) |
| `oss_blindable` | OSS State DB commitment over the ADS blindable functor | Instantiation on the concrete blindable-position functor of `ADS_Functor`, beyond the bespoke interface |
| `reg_tx_authenticated` / `demo_subview_disclosure` | OSS / Canton bridge transaction commitment (Rust) | Instantiation on a recursive model of the Canton transaction tree (public rose-tree Merkle machinery, concrete content); subview-level selective disclosure is preserved in the proofs |
| `reg_view_inclusion_same_hash` / `reg_view_inclusion_blinding_of` / `reg_view_inclusion_chains_sound` | OSS Merkle inclusion-proof verifier (Rust) | The recursive view tree is instantiated on the entry's generic rose-tree inclusion-proof (zipper) machinery: each inclusion proof commits to the same root hash as the full tree, is a blinding of it, and its attested chains are contained in the full set; no added assumption |

**Model-fidelity boundary (for confirmation against the Canton specification).** The recursive Canton instance is structurally faithful, with two declared modelling choices: concrete leaf content in place of the opaque content types of the public Canton model, and a shared, non-independently-blindable consensus field (so a revealed view under a blinded consensus is out of scope). These are model-fidelity items, not proof gaps; no axiom relates the opaque Canton types to the regulatory model.

---

# Synchronization-Degree Hierarchy

| Formal Model (`Hierarchy.thy`) | Implementation Target | Notes |
|---|---|---|
| degree functors `F k` (degree-indexed) | Candidate coupling-breadth abstraction for OSS degree-classed processing paths | `k` records chains `0..k` coupled around a hub; no refinement to the product's S0--S3 operational meanings has been proved |
| `degree_natural_transformation` | Degree demotion / blinding map (Rust) | The degree-forgetting map is a natural transformation between adjacent degree functors with commuting squares; OSS degree demotion must commute with processing |
| `nt_compose` / `nt_vertical_compose` | Multi-step degree demotion | Demotion across multiple degrees composes as a natural transformation; OSS may demote across several degree levels at once |
| `degree_forget_refines` | Demoted-view refinement | Degree demotion produces a blinding refinement of the original state; demoted views are partial views of the full state |
| `over_provisioning_guarantees` | Valid-state preservation corollary | Stated with a capability premise, but the proof obtains agreement from the valid-state premise; use `over_provisioning_reconciles` for the load-bearing degree result |
| `over_provisioning_reconciles` | Reconciliation from an arbitrary state (Rust) | From an arbitrary hub-defined state (no validity assumed), over-provisioning still drives every required chain to the hub value; shows the degree hypothesis is load-bearing, not decorative |
| `no_downward_safety` | Under-provisioning rejection (Rust) | Under-provisioning (required degree > capability) admits a state defeating every guarantee; OSS must refuse to process assets whose required degree exceeds system capability |
| `hierarchy_monotonicity` | (auxiliary) | A degree-free alias of `processing_preserves_validity` carrying no provisioning hypothesis; the capability-sensitive guarantees are the three rows above |
| `boundary_well_defined` | Timestamp-order degree-boundary specification | Combines the degree-2 threshold with strict order on integer timestamps; it does not formalize distributed causality, traces, or causal preservation |
| `static_promotion_safety` | Static degree re-assignment (governance) | A static re-assignment within system capability transfers the guarantee verbatim; governance-time degree changes are safe within capability |

**Product-fidelity boundary.** The formal hierarchy proves properties of a coupling-breadth index. It does not formalize the product's S0--S3 operational meanings, including directional observation, bidirectional causal execution, atomic binding, or mutual rollback. A refinement from those meanings to `F k`, as well as in-flight promotion across a live synchronization, remains open.

---

# Domain-Independence Instance

| Formal Model (`External_Instance.thy`) | Implementation Target | Notes |
|---|---|---|
| `tcp_state_machine` / `conntrack_state_machine` | (No Oraclizer implementation target) | An out-of-regulatory-domain toy endpoint/tracker instance discharging the generic state-machine locale; it borrows RFC 793 names but is not trace-conformant to RFC 793 and is not a concrete conntrack model |
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

The formal model makes simplifying assumptions. Because this document is pre-implementation, the tables record proposed mitigation targets and whether any refinement evidence exists; they do not claim that an implementation already discharges the gap.

### State-Preservation Assumptions

| Model Assumption | Implementation Reality | Gap Mitigation | Disposition |
|---|---|---|---|
| Synchronous execution (lock → update → unlock is atomic) | Target deployment is expected to be asynchronous | BVC is a proposed refinement target with finality tracking | Open: no implementation or refinement proof currently establishes atomicity |
| Honest nodes | Not an assumption of the state-preservation safety locales | N/A | N/A for the safety layer; D-quencer node tags belong to the selection/progress layer and do not discharge safety assumptions |
| Finite chain set | A deployment may change membership over time | Registry-governed membership is a proposed design | Open: dynamic-topology refinement is unverified |
| Lock acquisition is atomic | A deployment may have latency and contention | Timeout/rollback is a proposed design | Open: no contention, timeout, rollback, or atomicity refinement is proved |

### Selection and Aggregate-Progress Assumptions

| Model Assumption | Implementation Reality | Gap Mitigation | Disposition |
|---|---|---|---|
| `fair_leader` deterministic guarantee | A target may use probabilistic leader election | VRF, rotation, view change, and force inclusion are proposed external mechanisms | Open: no probability model, independence assumption, or implementation/refinement evidence |
| `honest_progress` (honest-tagged event reduces pending count) | A target would have a request queue and network | Admission control and BFT liveness are proposed obligations | Open: request identities, queue service, and network progress are unverified |
| `non_honest_bounded` / aggregate non-increase | A target may receive dynamic arrivals | Admission control is a proposed mechanism | Open: continuous-arrival and per-request liveness are unverified |
| Atomic lock acquisition | A target may have distributed contention | Lock queue, timeout, and release are proposed mechanisms | Open: no lock-refinement evidence |

### Functor / Convergence Layer Assumptions

| Model Assumption | Implementation Reality | Gap Mitigation | Disposition |
|---|---|---|---|
| Atomic single evolution step | A target recovery loop may run asynchronously | Round boundaries are a proposed refinement design | Open: no model-to-code refinement |
| Finite-domain global state | Chain/asset domains may grow over time | Registry snapshots and bound recomputation are proposed | Open: dynamic-domain convergence is unverified |
| Bounded fairness window (from D-quencer) | A target may use probabilistic leader election | Reuses the deterministic `fair_leader` assumption | Open: same external fairness obligation as the selection/progress layer |
| Existential recovery choice | An implementation needs a constructive selector | A terminal-faithful measure-reducing selector must be designed and refined | Open: `oss_realize` uses `SOME` and ignores the event for selection |

### Synchronization-Degree Hierarchy Assumptions

| Model Assumption | Implementation Reality | Gap Mitigation | Disposition |
|---|---|---|---|
| Static degree assignment | Degrees may need re-assignment during operation | `static_promotion_safety` proves the model-level static transfer within capability | Model-level static case proved; operational governance mapping and in-flight promotion remain unverified |
| System capability degree known and fixed | Capability may vary across deployments | Genesis/governance declaration is proposed | Open: no implementation/refinement evidence; `hierarchy_monotonicity` itself is degree-free |

### Rationale for the Deterministic `fair_leader` Abstraction

The `fair_leader` assumption requires the schedule to stay inside the roster and every `fairness_bound` window to contain an honest-tagged leader. It is a deterministic premise. The formalization defines no probability space, sampling distribution, independence property, VRF mechanism, network schedule, or adversarial execution from which that premise could be derived.

The deterministic abstraction is retained for the following reasons:

- It isolates exactly the bounded-occurrence premise consumed by the aggregate pending-count proof.
- The static BFT-count assumptions imply that the roster contains an honest-tagged node, so a constant in-roster schedule witnesses locale satisfiability. They do not establish that an operational election mechanism produces that schedule.
- A probabilistic or implementation interpretation would require a separate model and a refinement/composition theorem. No such theorem is part of this entry.
- View change, force inclusion, admission control, and network timing remain proposed external mechanisms, not verified dispositions.

The Isabelle/HOL result is therefore conditional: if the deterministic in-roster fairness and aggregate-progress premises hold, the pending count decreases and reaches zero in the closed count model. Establishing those premises for VRF/BFT/network code is deferred and unverified.

---

## Assumption Disposition (current scope)

This section distinguishes model-level discharge from open external/refinement obligations. No row asserts implementation coverage while the project remains pre-implementation.

| Model Assumption | Disposition |
|---|---|
| Honest nodes (state-preservation layer) | N/A: the safety locales do not assume honest nodes |
| Conditional safety / initial inconsistency | Model-level existential bounded convergence proved for finite-domain unlocked states; no executable recovery refinement |
| Atomic sync: lock acquisition and release | Open external/refinement obligation; timeout/rollback is only a proposed design |
| Atomic sync: cross-chain propagation | Open external/refinement obligation; finality tracking is only a proposed design |
| Fair leader (deterministic) | Assumed; in-roster satisfiability witness proved, operational VRF/BFT realization unverified |
| Honest aggregate progress | Assumed; request/service/network realization unverified |
| Closed pending-count model | Assumed; dynamic arrivals and request-identity fairness unverified |
| Finite connected chains / static topology | Assumed; dynamic-topology refinement unverified |
| Static degree assignment | Model-level static transfer within capability proved; operational and in-flight changes unverified |

The CDSP paper states the following open questions:

1. **Partial synchrony extension**: Generalize `fair_leader` and `honest_progress` to partial synchrony. Related work: Castro & Liskov PBFT, HotStuff. Potential approach: Heard-Of model with partial synchrony variants.
2. **Dynamic topology**: Extend `multi_domain_preservation` to handle chains joining/leaving the connected set. Requires invariant-preserving topology updates.
3. **Open-system and request-identity liveness**: Add request identities, arrivals, queue/service semantics, and a fairness property stronger than aggregate count decrease.
4. **Model-implementation refinement**: Establishing correspondence between the Isabelle/HOL model and the Rust implementation. This document is the starting point.

---

## Verification Scope for Creusot and Kani

During refinement-proof work, the following scope applies:

- **In Creusot scope**: Function-level pre/postconditions derived from model theorems (state transition correctness, priority key injectivity, lock effectiveness predicate, no self-loops, degree capability-vs-requirement check, recovery confiscation guard).
- **In Kani scope**: Bounded model checking for concurrency-sensitive code (lock acquisition races, consensus message ordering, timeout expiration races, reconciliation-round atomicity).
- **Out of both scopes**: Probabilistic VRF properties, network-level timing, and cryptographic primitives such as BLS signature correctness. These remain open external obligations; a future target would need separate evidence or an explicit unverified-component boundary.

Specific theorems treated as refinement-annotation candidates are listed under the "refinement-annotation candidate for Creusot" and "refinement-annotation candidate for Kani model checking" notes in the mapping tables above.

---

## Theorem-to-Test Correspondence

Until formal refinement proofs (model → code) are available, the following planned tests can provide non-proof consistency checks; they do not establish refinement. The proposed implementation vehicle is `cargo test` plus `proptest` for property-based testing.

### State-Preservation Theorems

| Theorem | Test Strategy | Status |
|---|---|---|
| `confiscated_terminal` | Unit test: all actions on CONFISCATED return revert | Planned |
| `confiscate_universal` | Unit test: CONFISCATE succeeds from all non-CONFISCATED states | Planned |
| `no_self_loops` | Unit test: post-state ≠ pre-state for all valid transitions | Planned |
| `regulatory_homomorphism` | Integration test: sync produces consistent state across mock chains | Planned |
| `valid_state_preservation` | Integration test: valid_state holds before and after sync | Planned |
| `sync_isolation` | Integration test: sync on asset A does not affect asset B | Planned |

### Selection and Aggregate-Progress Theorems

| Theorem | Test Strategy | Status |
|---|---|---|
| `select_highest_deterministic` | Unit test: given same message set, D-quencer produces identical output across runs | Planned |
| `priority_key_injectivity` | Unit/property test: within timestamp/node upper bounds, any modeled field difference changes the key; add negative tests showing out-of-bound subtraction can saturate and therefore must be rejected before key construction | Planned |
| `starvation_bound` | Model/reference test: under a supplied in-roster fair schedule, honest-slot decrease, and globally non-increasing count trace, verify a positive aggregate count decreases within the bound | Planned |
| `eventual_completion` | Model/reference test: under the same assumptions, a closed aggregate pending-count trace reaches zero | Planned |
| `conditional_safety_preservation` | End-to-end refinement target: from a valid state with an enabled transition, verify sync succeeds and the result is valid | Planned |

### Functor / Convergence and Hierarchy Theorems

| Theorem | Test Strategy | Status |
|---|---|---|
| `authenticated_preservation_soundness` | Property test: random pairs of authenticated views merge to a valid join that each input refines | Planned |
| `blinded_view_preserves_validity` | Property test: blinded views extract to valid states refining the original | Planned |
| `oraclizer_guarded_bounded_convergence` | Reference-model test: an explicitly supplied safe-recovery witness yields a valid state within the computed bound; this does not validate an executable selector | Planned |
| `safe_recovery_sync_no_fresh_terminal` | Integration test: recovery never introduces a fresh CONFISCATED holding | Planned |
| `hierarchy_monotonicity` | Property test: processing preserves validity independently of degree | Planned |
| `over_provisioning_reconciles` | Property test: from a hub-defined state, sufficient capability reconciles every required chain to the hub value | Planned |
| `no_downward_safety` | Property test: under-provisioned processing exhibits a guarantee-defeating state | Planned |

---

## Update Policy

This document is updated when:

- New `.thy` files are added
- Implementation code is written that corresponds to model elements
- A model-implementation gap is discovered
- Model assumptions change
- An assumption disposition changes (model-level discharge vs. open external/refinement obligation)

Changes are committed with the message format: `mapping update: [reason]`

## Change Log

| Version | Date | Change |
|---|---|---|
| 0.5.6 | 2026-07-20 | Editorial: refinement-direction glosses aligned with the formal reading of `state_refines` (a partial view refines the fuller view), matching the theory sources. No change to theorems, assumptions, mappings, or dispositions. |
| 0.5.5 | 2026-07-20 | Editorial: numbered property labels replaced with the property names throughout the current document (coverage list, section headings, assumption and test tables); historical change-log rows retained verbatim. No change to theorems, assumptions, mappings, or dispositions. |
| 0.5.4 | 2026-07-19 | Scope and contract correction: retained the timestamp and source-node bounds of `priority_key_injectivity`; separated the formal coupling-breadth hierarchy from the product's S0--S3 operational meanings and left that refinement open; described the external domain-independence instance as a TCP-inspired toy endpoint/abstract tracker rather than an RFC 793 or concrete conntrack model; classified regulatory actions, genesis enforcement, tests, and external cryptography as open implementation or refinement obligations; consolidated the gap and assumption-scope description. |
| 0.5.3 | 2026-07-19 | Scope and theorem-contract correction: described Property 2 as aggregate pending-count progress; removed unsupported VRF probability and implementation-completeness claims; recorded in-roster fairness, request-identity/network/lock/refinement gaps, and the non-constructive `oss_realize` boundary; scoped authenticated mapping to an extractable sub-preorder and a state-keyed reveal-set witness; described the hierarchy as a timestamp-order degree boundary; synchronized theorem descriptions with the roster, selection, merge, associativity, and conditional-safety contracts. |
| 0.5.2 | 2026-07-03 | Documentation contract correction: aligned Property 2 with the available deterministic selection and aggregate-progress results; distinguished model-level safety facts from open implementation and refinement obligations; separated the degree-free validity alias from capability-sensitive reconciliation and under-provisioning results. |
| 0.5.1 | 2026-06-25 | Added `Canton_Bridge.thy` path-level Merkle inclusion mappings (`reg_view_inclusion_same_hash` / `reg_view_inclusion_blinding_of` / `reg_view_inclusion_chains_sound`): the recursive view tree is instantiated on the entry's generic rose-tree inclusion-proof (zipper) machinery, sharpening sequence-level inclusion to the concrete Merkle path with no added assumption. Monotone addition; no change to existing theories, theorems, assumptions, or dispositions. |
| 0.5.0 | 2026-06-24 | Added `Canton_Bridge.thy` mappings: composite functor laws over the authenticated extraction map, sequence-level authenticity preservation (validity / need-to-know / hash soundness / state-level inclusion), and instantiation on the concrete ADS blindable functor and a recursive model of the Canton transaction tree, with the declared model-fidelity boundary. Monotone addition; no change to existing theories, theorems, assumptions, or dispositions. |
| 0.4.1 | 2026-06-23 | Editorial pass: generalized infrastructure-specific references in the implementation-target column (storage engine, a force-transfer signature, the BLS library reference). No change to theorems, assumptions, mappings, or dispositions. |
| 0.4.0 | 2026-06-23 | Added mappings for the new theories now in the repository: the Cross-Domain State Preservation Functor (`Composition.thy`, `Functor_Laws.thy`: functor laws over preservation morphisms, authenticated cross-domain state soundness via the Merkle interface, guarded bounded convergence and terminal-faithful safe recovery), the Synchronization-Degree Hierarchy (`Hierarchy.thy`: composable natural transformations and degree-class monotonicity), the domain-independence instance (`External_Instance.thy`), and the proof-automation layer (`Proof_Automation.thy`). Added corresponding assumption-gap rows (functor/convergence and hierarchy), assumption-disposition rows, and theorem-to-test rows. All mapped theories are mechanized and `sorry`/`oops`-free. No change to the Property 1/2 assumption set or implementation targets. |
| 0.3.0 | 2026-04-17 | Added "What Verification Establishes and What It Does Not" scope declaration. Added rationale for deterministic `fair_leader` abstraction (Heard-Of model tradition, Wanner et al. SRDS 2020 precedent). Added an assumption-disposition section recording, per assumption, whether it is discharged in the proofs or handled at the implementation layer. Added "Verification Scope for Creusot and Kani" section. Added refinement-annotation candidate notes for Creusot and Kani work. |
| 0.2.0 | 2026-04-07 | Initial mapping for Properties 1 and 2. |
