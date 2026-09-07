<!-- SPDX-License-Identifier: BSD-3-Clause -->
# Model contract

This document describes the conditional formal contract of `Evidence_Atomic_Binding`. Its state transitions are Isabelle/HOL transition definitions over the existing reservation and message models. A reference to an actual callback or consumer below means that function is invoked in the formal execution. Physical implementations require the separate evidence recorded in [product-obligations.json](product-obligations.json) and [product-api-inventory.json](product-api-inventory.json).

## Identity, facts and terminal authority

The source key `K` is immutable. The complete `transfer_binding` contains the key, asset, amount, destination, recipient, source epoch, operation and domain separator. Worker generation, route, relay retry and a new call identifier do not create a new financial root.

A source statement reports `Observed`, `Finalized` or `Reversed`. A `terminal_record` separately stores the complete binding, `Confirmed_Decision` or `Reversed_Decision`, and supporting certificates. `Observed` has no terminal-kind translation. The attestation locale supplies signature soundness, honest-source evidence and uniqueness of a non-observed statement for the same key.

`record_terminal` checks the certificate and operation-specific source origin. Monetary origin requires a positive amount and the exact recorded source debit. A regulatory effect uses its authenticated finalized regulatory statement. The first accepted core is immutable; a matching binding and kind can acquire additional evidence. Conflicting bindings or kinds are rejected. See [Finality_Protocol](Finality_Protocol.thy) and [Finality_Records](Finality_Records.thy).

The source-fact threshold is not a distributed decision protocol. Agreement between executions using the same stable source is conditional on that common source. The model does not derive a persistent quorum/round/epoch authority from a local record update, certificate threshold, GKR proof hash or acknowledgment.

`Finalized` cannot later become `Reversed` for the same key in one source profile. A lawful later regulatory or compensating action needs its own identity and effect obligations. Neither timeout nor an administrator request supplies a missing terminal fact.

## Controlled source and receipt production

[Source_Effect_Boundary](Source_Effect_Boundary.thy) gives the source a persistent effect/fence record and available allocation. Applying an exact binding is idempotent. A successful no-effect fence prevents a delayed apply for that identity. Delivery of a command and delivery of its acknowledgment are separate inputs, so an external effect can exist while the local response is unavailable.

[Controlled_Source_Outcomes](Controlled_Source_Outcomes.thy) adds terminal outcomes and return history. Finalization and reversal require an existing effect and become immutable alternatives. Reversal restores the source allocation once while retaining the effect and terminal record. An unknown response remains unknown; it is not evidence that no effect occurred.

`issue_source_receipt` in [Source_Finality_Link](Source_Finality_Link.thy) checks the current `controlled_source_fact` against the exact certificate statement and enforces signature-slot consistency. Receipt verification reads issued receipts. The source-attestation interpretation is derived from the generated source history and issuance conditions, rather than defining verification to be source truth. Different incompatible source histories are not combined into one truth predicate.

The combined monetary/regulatory example uses an actual controlled monetary producer and a separate supplied regulatory source fact under different keys for the same asset. Its regulatory input is an abstract attestation profile; the example does not implement a physical regulatory-fact producer.

[Source_Coupling](Source_Coupling.thy) connects these operations to the child. `coupling_live_receipt` requires both issuance membership and the same current source fact. Source mirroring consumes effect evidence; post-dispatch cancellation/fencing requires source availability and no-effect evidence. Credit, return and reconciliation consume their applicable current receipt/outcome guards. Generated initial states and finite executions supply the parent reservation contract and source/mirror provenance.

## Consumers and publication

`invoke_protocol` checks the core epoch and `terminal_intent_guard`, then calls the parent operation using `current_lock_view`. That view combines authority-owned endpoint context with the actual regulatory receiver state. A request retains its submitted caller, authority epoch and version; the parent's current-use checks consume the authority's current permissions.

| Operation | Consumed reference and actual effect |
|---|---|
| Certificate publication | Exact binding, terminal kind and indexed evidence; `publish_source_certificate`. |
| Delivery, bypass and delivery retry | Exact confirmed binding/evidence; `deliver_reserved_credit`, including the parent's publication, current-use and once checks. |
| Return | Exact reversed binding/evidence and the current controlled reversal; `mirror_source_return` and `release_to_source`. The mirror update is not a second source refund. |
| Reconciliation | Exact confirmed binding/evidence; `reconcile_recorded_credit`, preserving the credited effect. |
| Ordinary or enforcement descendant | Stored confirmed root and primary publication; `execute_descendant` checks existing root credit, root funding, current authority and spend permissions, and regulatory state. Its certificate field does not authorize a new source effect. |
| Regulatory application | Exact confirmed binding/evidence; `apply_regulatory_message` performs the receiver update and regulatory synchronization. |
| Data read | `read_source_data` consumes current permission; where a terminal record exists, its exact reference is checked. Protected queries additionally bind the requested query scope. |
| Primary publication | `publish_primary` reads the stored record and `terminal_effect_completed`: actual credit, applied regulatory effect, or recorded returned phase, as appropriate. |

The theorem `intent_result_is_actual_parent_step` ties financial execution to the existing dispatcher. Parent contracts are preserved by actual initial/step/run proofs. The child adds guards to those functions; it does not reinterpret the parent or expose an unguarded child route.

Candidate evidence, prepare, terminal recording, local effect and primary publication are distinct stages. A current ready endpoint can consume primary state before secondary settlement completes. Primary publication does not assert that every physical domain has applied the effect. An implementation contract that also requires every domain's application before that same publication must reconcile those timing requirements explicitly.

## Source allocation and root funding

For one source pool, let `E` be the finite set of actual controlled source effects, `R` the set of returned bindings, `C` the set of bindings in the child credit history, and `U = E - (R union C)`. Binding mass counts only amounts belonging to that pool. Let `S_phys` be authoritative available source units, `F` destination funding attributed to roots from the pool, and `G` the genesis allocation.

```text
R intersect C = empty
E = U union C union R                  (disjoint partition)
S_phys + mass(U) + F = G
```

`coupling_credits_finalized` connects every child credit to the current finalized source fact. Together with the source return invariant it excludes membership in both `R` and `C`. [Source_Coupling_Conservation](Source_Coupling_Conservation.thy) derives the equation from generated joint executions. `actual_sourced_calls_preserve_the_physical_pool` in [Source_Observation_Projection](Source_Observation_Projection.thy) carries it through actual sourced calls. Independently valid source and mirror fragments are insufficient: mixing an unrelated reversed fragment with a credited fragment can count fifteen units against an allocation of ten.

The parent accounting view separately satisfies `S_local + U_local + F = G`, using its own unresolved mass. Source debit and return gaps describe delayed local mirroring. These two views do not authorize adding `S_phys` to `S_local`.

[Root_Funding_Bounds](Root_Funding_Bounds.thy) derives destination balance as a finite sum of account funding over financial roots. Consequently `funded_units(key, account) <= destination_units(account)`. Under the parent contract:

```text
0 <= F <= G - S_local <= G
F = G - S_local  iff  U_local = 0
F = G           iff  S_local = 0 and U_local = 0
```

Zero unresolved mass is not automatically an empty unresolved set. These are funding bounds, not permission grants: an accepted descendant amount is root-funded, but current policy can reject every positive amount despite positive funding.

For an already credited root, [Root_Continuation](Root_Continuation.thy) preserves account funding, that root's filtered descendant history and the actual descendant reply under any finite parent action list that excludes `Descendant_Action` for that root. Other roots may use the same asset and account. Reply equality fixes the same context, request, sender, recipient and amount; it does not preserve an old permission after a policy change or after spending that root.

`holder_funding_equality_iff_all_actual_descendant_decisions` in [Funding_Decision_Information](Funding_Decision_Information.thy) concerns two states satisfying financial history agreement with the same credited root. Equality of every holder's funding is equivalent to equality of actual descendant replies over all common contexts, requests and transfer quantities. The reverse direction constructs a current authorized probe. One fixed restrictive policy does not reveal funding.

[Root_Information](Root_Information.thy) erases only `funded_units` and `lawful_descendants` from `reservation_state`. Two generated roots and two holder accounts then admit equal erased states with different actual continuation replies. Restricted one-root and one-account results delimit that ambiguity. The erasure does not retain the machine journal; complete-journal reconstruction remains valid. No globally minimal trace, whole-machine sufficient statistic or arbitrary-record realization is claimed.

## Invocation, execution and completion

[Finality_Calls](Finality_Calls.thy) separates the durable authority from endpoint connection, volatile response state and completed calls. `execute_authority_once` associates an identifier with one exact command, reply and execution index. A conflicting command under that identifier does not execute. Crash and lost response do not create another execution of a recorded command.

Retransmission of an old identifier returns its existing result, even when policy has since changed. It is not a new current authorization decision. A new invocation goes through the actual current dispatcher. Once a result is completed it remains that result under finite continuation, including completed `Observation_Busy` and `Observation_Unavailable`; retrying after either result requires a fresh identifier.

[Call_Order](Call_Order.thy) and [Sourced_Call_Order](Sourced_Call_Order.thy) establish the applicable real-time order: if a successful current reply completes before a fresh later invocation begins, a successful current reply of that later invocation cannot have an older revision. Overlapping invocations can deliver replies later, and balances themselves need not be monotone.

## Observation contract

The concrete readers in [Finality_Observations](Finality_Observations.thy) read stored caches, histories and state. Their independent abstract readers are defined in [Abstract_Observation_Types](Abstract_Observation_Types.thy). The target retains application data, receipts, publication, phase, ownership, journal and revision in addition to the financial/regulatory product.

Unprotected current and historical requests admit source and destination balance queries. Root funding, application data, regulatory state and terminal receipts use the protected query path. The separately exposed raw path remains an observation of stored values.

| Reply family | Exact interpretation |
|---|---|
| Successful current value | Cache equals the current complete logical snapshot, and every query-relevant source effect or terminal record is published. Application data also requires no active owner. A matching revision number alone is insufficient. |
| Protected current value | Current reader permission, authority epoch, request scope and applicable terminal reference hold. The application-value branch additionally executes the actual parent data read. |
| Explicit historical value | The requested revision identifies a ready snapshot captured by an actual callback or initialization. Protected historical queries check current access to that historical data. |
| Raw value or journal | An explicit observation of stored fields or journal events. It is not labeled a coherent successful current value and carries no confidentiality claim for public storage. |
| Operational status | Reservation phase and reported secondary progress. Reporting progress does not perform settlement. |
| Physical source inspection | Available source units or effect history from the controlled source, subject to source availability. The local mirror cannot reconstruct every such reply. |
| Busy, unavailable or rejected | The actual branch's response, with the same durable completion semantics as success. A completed instance is not a pending call. |

`current_cache_valid` compares complete snapshots. Refresh reads the authority; a concurrent revision change invalidates that cache. The source-aware `Endpoint_Request` dispatcher in [Sourced_Observations](Sourced_Observations.thy) further restricts current `Source_Balance`: unavailable source yields `Unavailable`; a nonzero debit or return gap yields `Busy`. Secondary lag neither supplies nor replaces these checks.

[Historical_Snapshot_Provenance](Historical_Snapshot_Provenance.thy), [Abstract_Response_Link](Abstract_Response_Link.thy) and [Sourced_Response_Link](Sourced_Response_Link.thy) connect actual history capture to replay prefixes. For a completed historical call there are a snapshot index and execution index with `snapshot_index <= execution_index < journal_length`; its independent abstract value and revision come from that earlier cut. A completed current call instead agrees with its actual execution cut.

The sourced response proofs analyze `execute_sourced_request` and its callbacks directly. `every_completed_sourced_reply_has_its_actual_source` supplies the indexed callback for any completed sourced reply. More specific relations retain current guards, historical provenance, raw and operational fields, physical availability and immutable completed failures. They do not automatically inherit a result for a different callback/state/reply type.

## Product words and recovery

[Transfer_Ledger_Refinement](Transfer_Ledger_Refinement.thy) defines ledger fields and financial-event arithmetic independently, then compares them with actual reservation fields, committed events and journal suffixes. [Finality_Refinement](Finality_Refinement.thy) supplies the separate regulatory action word. Token quantity and regulatory holding support are distinct components.

[Observed_Protocol_Link](Observed_Protocol_Link.thy) and [Source_Observation_Projection](Source_Observation_Projection.thy) derive actual core operation words from callback branches and authority replay. Queries and rejected source admissions can stutter; accepted core operations consume the existing transfer and regulatory functions. The generated parent contract and valid regulatory initial state supply their applicable premises. Arbitrary accounting events are not asserted to be legal protocol executions.

`source_observation_alpha` additionally retains physical source units, effects and returns. A source effect with a lost acknowledgment can change those fields while leaving the entire local observation state unchanged. The product-word result is about the core projection, not a full simulation of this richer target. This target is also not a classifier for every API reply: availability, caches, historical cuts, secondary progress and permission inputs remain explicit in response relations.

[Finality_Recovery](Finality_Recovery.thy) distinguishes replay from current-source validation. `checked_current_replay` checks the candidate's genesis and exact journal against the current authority and validates the recorded callback history. A shortened, reordered, conflicting, duplicated or wrong-genesis candidate fails the applicable comparison. Internal replayability alone cannot establish completeness or freshness.

Accepted current replay restores the actual authority state, preserving terminal records, completed effects and descendant lineage. Sourced recovery additionally preserves the source projection and resumes through the actual source-aware dispatcher. Recovery does not issue a new credit or refund. The authenticated, complete, current authority source and its durability are physical implementation obligations, not consequences of list replay.

## Progress and controls

[Finality_Progress](Finality_Progress.thy) provides a finite begin/dispatch/collect/complete program for an uninterrupted fresh call with an available connected endpoint. It completes the actual callback reply, which can be a failure. A ready public read succeeds after refresh in a quiescent interval; the remaining program length decreases.

Retries and network connectivity alone do not guarantee a successful cached current read: an intervening context update can invalidate every refresh through arbitrarily long retry sequences. Unknown source effects are never made refundable to force termination.

[Finality_Terminal_Progress](Finality_Terminal_Progress.thy) supplies separate general conditional terminal programs from a state satisfying the joint invariant. Their inputs are a current controlled terminal fact, an admissible exact certificate, a free issuance slot, a positive mirrored monetary debit and an empty terminal-record slot. Confirmation additionally checks actual current credit admission and an unused credit marker. Reversal additionally checks current reservation ownership, the pending phase and relay epoch. A five-action source-aware suffix issues the evidence, records its terminal core, publishes the certificate, executes actual credit or return, and publishes primary state. The result retains the physical source and joint invariant. The suffix delivers those actions without intervening source or context changes; it does not guarantee eventual evidence or network delivery. A separate fresh durable call completes the final core publication response, rather than asserting completed source-aware client calls for every action in the suffix.

[Finality_Terminal_Scenarios](Finality_Terminal_Scenarios.thy) supplies the same-cut conditions from actual source-word prefixes. [Sourced_Completion_Scenarios](Sourced_Completion_Scenarios.thy) activates current/history completion and nonoverlapping revision order, including a completed Busy retained across catch-up and a successful fresh identifier. [Root_Continuation_Scenarios](Root_Continuation_Scenarios.thy) activates the general root frame with a successful nonempty other-root transfer between shared holders.

The scenario theories include normal credit, reversed outcome, bypass, recovery and current/history responses. [Regulatory_Finality_Scenarios](Regulatory_Finality_Scenarios.thy) executes monetary primary publication, a separate actual regulatory freeze, ordinary descendant rejection, lawful enforcement and reconciliation while preserving earlier funding and regulatory effects.

Controls remove particular terminal-reference, source-finalization, current-cache, source-gap or current-journal checks and expose the corresponding bad effect, provenance or response. The raw intermediate pair and lost-acknowledgment examples establish exact information limitations. These are formal-function controls, not evidence that a compiled product mutation has been run.

## Physical and implementation obligations

| Boundary | Evidence needed outside this model |
|---|---|
| Terminal authority | A production `PrimaryFinalityVerifier` and primary-finality record (PFR) producer binding the exact fields to signer identity, uniqueness and threshold, with persistent agreement across quorum, round, epoch changes and restart. |
| Source adapter | Immutable effect identity, atomic deduplication, persistent no-effect fences, authenticated current outcome queries, lost-ack recovery and one-time return behavior in the actual bank, chain or DAML API. |
| Durability and current journal | Atomic effect/result recording, exact invocation identity, retained completed failures, and an authenticated complete current genesis/journal or justified checkpoint source across restart. |
| Current consumption | The deployed authority/dependency/version owner and a barrier, fence or equivalent mechanism binding the current check to the effect. Full snapshot equality here is a logical contract, not a free network operation. |
| Observation and settlement | Correspondence for every declared API, raw getter, storage field and event; historical revision/timestamp mapping; actual primary application and secondary settlement execution. |
| Compiled consumer | Exact source, ABI, encoding and hash preimage, compiler target and runtime consumer, with a normal execution and a guard-removal control for each required connection. |

The inspected token already contains action identity/lifecycle, validity-window, current authority, dependency and nonce checks; reversal also checks the current original effect. Those defenses must be preserved and connected field by field. Its replay rejection is not automatically this model's retransmission of a completed reply. A distinct token reversal receipt and changed action lifecycle or case state are not a same-key change of the model's stable source fact.

The inspected settlement seam accepts external primary-finality and finalized-receipt-root providers. Its authorization result records a local settlement/claim identity; it does not itself execute a CDK application or declare secondary settlement complete.

The [product obligations](product-obligations.json) record the exact source findings and distinguish planned tests from unverified compiled consumers. The [API inventory](product-api-inventory.json) is a declaration inventory, not a compiler-derived ABI certificate. This model supplies no deployment conformance, universal source support, unconditional termination, universal raw-observation atomicity, complete runtime refinement or global information/representation characterization.
