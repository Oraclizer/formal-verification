<!-- SPDX-License-Identifier: BSD-3-Clause -->
# Model Boundary

[ROOT](ROOT) registers the defining theory sources. An actual operation invokes
an existing HOL function, without an implied compiled or deployed counterpart.

## Inherited contracts and added connections

The [parent contract](../Evidence_Atomic_Binding/model-contract.md) supplies source
bindings and attestation, terminal records, reservation accounting, current
authorization and durable calls. Its root-funding threshold and validation
against the complete current recovery source are inherited results.

The child connects finite allocation characterization and historical projection
to actual source, call and recovery programs. Standard finite transportation,
induction and projection arguments are not presented as new general mathematics.

## Allocation language and current permission

The equivalence in [Funding_Characterization](Funding_Characterization.thy)
assumes the parent reservation contract, already credited distinct root keys
and finite distinct holders. Natural-number targets must preserve selected
root totals and complete destination-account totals, including destination and
asset. Empty selections are handled by the empty transfer word.

The execution side consists of supported positive ordinary descendant effects.
The constructor supplies the current authorization and exact spend permission
for each chosen move. [Source_Realization_Link](Source_Realization_Link.thy)
additionally consumes confirmed terminal references, primary publication and
the receiver's current ACTIVE metadata before executing the parent operation.
Context installation is an explicit environment input. Authenticity and current
policy supply remain implementation obligations.

Final pooled equality does not hide intermediate balances. The non-lineage
comparison, `erase_lineage_state`, clears root funding and descendant history
from reservation state. Actual journals and completed observations remain.
No shortest plan, optimal cost, arbitrary normal-form realization or universal
reachability under a fixed policy follows.

## Why policy and order still matter

[Funding_Guard_Controls](Funding_Guard_Controls.thy) removes only the exact
spend-permission check and exposes a transfer the original consumer rejects.
[Even_Amount_Policy_Boundary](Even_Amount_Policy_Boundary.thy) uses a nonempty
policy permitting positive even amounts in both directions for both roots.
A two-unit request executes, while a one-unit request is rejected.

Under that fixed context, every finite descendant-only word preserves each
funding cell's parity, including rejected requests. The tables `[[0,5],[5,0]]`
and `[[1,4],[4,1]]` have equal root and account totals, but the latter changes
parity and cannot be reached by those words. Source support remains unchanged.

[Funding_Order_Boundary](Funding_Order_Boundary.thy) supplies two successful
orders with the same final selected funding. Their raw journal replies differ.
For successful canonical effects from the same start, equal complete journals
require the same ordered effect word. Ordered concatenation is preserved;
an unordered merge is not justified by final allocation equality.

## The projection is specific to the declared readers

[Historical_Decision_Projection](Historical_Decision_Projection.thy) normalizes
only historical snapshots' `reservation_at`, `asset_version`,
`issued_certificates`, `received_messages`, `lawful_descendants` and
`reservation_clock`. It preserves stored query values and readiness, then
derives reply and normalized-update equations for every observed and sourced
command and environment input. Finite call words retain their invocation,
execution-result, completion and history fields.

The current core, cache, raw journals, source-effect lists, source availability
and completed failures remain. [Integration_Boundaries](Integration_Boundaries.thy)
classifies current-cache injection, raw readers and the original recovery checks.
These necessary conditions apply to those interfaces, not to every possible
implementation or more restrictive observation language.

[Historical_Reachability_Boundary](Historical_Reachability_Boundary.thy) gives a
projected history that is not any original reachable call-authority state, despite
preserving callback replies. It cannot replace an original full recovery replica
and carries no global minimality claim.

## Completion, recovery and the two applications

[Source_Call_Realization](Source_Call_Realization.thy) translates each input from
the monetary example's actual sourced genesis. Fresh calls complete an
uninterrupted refresh and execution; replies may be rejected. This construction
does not guarantee delivery or successful completion under unbounded interference.

[Funding_Completion_Separation](Funding_Completion_Separation.thy) compares
the same fresh one-unit request after two source histories with equal pooled
balances and different root funding. Different completed replies originate in
the actual funding test, before any retransmission reuses a stored result.
[Regulatory_Composition_Example](Regulatory_Composition_Example.thy) separately
generates an observed call prefix with monetary credit, freeze, ordinary
rejection and enforcement. Its regulatory attestation remains a supplied input.

Recovery keeps each original generated machine and its earlier results.
The current-source checker compares the original genesis and complete ordered
entries; restored dispatch also checks the full replica. Only afterward does
the historical projection transport finite continuations. The block decoder in
[Integration_Transport](Integration_Transport.thy) is lossless for structured
HOL entries, not a byte-serialization theorem for arbitrary function-valued maps.

## Physical and implementation boundary

Implementations must supply authenticated source effects, persistent fences,
stable outcomes, authentic current policy, atomic durable effect/result records
and a complete current recovery source. A lost acknowledgment or timeout does
not justify a refund. Compensation uses a new identity rather than changing
a stable same-key finalized fact into a reversed fact.

Primary publication and secondary-settlement telemetry are separate modeled
operations. Publication does not establish simultaneous application at every
physical domain. Existing token replay rejection is also different from this
model's retransmission of an earlier completed reply.

The parent's [product obligations](../Evidence_Atomic_Binding/product-obligations.json)
and [API inventory](../Evidence_Atomic_Binding/product-api-inventory.json) retain
the work for getters, raw storage, events, authorization, encodings, compiler
output and settlement execution. Source inspection does not establish ABI or
runtime correspondence. Linearizability of the complete deployed API, distributed agreement,
deployed atomicity and complete implementation refinement are outside this result.
