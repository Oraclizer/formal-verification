<!-- SPDX-License-Identifier: BSD-3-Clause -->
# Evidence Atomic Binding

`Evidence_Atomic_Binding` is an Isabelle/HOL model of evidence-qualified terminal decisions, their actual financial and regulatory consumers, and the observations and recovery of those executions. It extends `Preemptive_Lock_Correctness` without changing the parent's operation semantics.

The results are conditional on the stated source-attestation, authority, source-control and durable-journal contracts. An actual operation in these theories refers to the defined HOL transition or reader. This does not establish correspondence to a deployed bank adapter, smart contract, sequencer or compiled runtime.

Read the [model contract](model-contract.md) for the precise assumptions and nonclaims. The [product obligations](product-obligations.json) identify implementation consumers and missing evidence; the [API inventory](product-api-inventory.json) retains public functions, storage getters and events that require their own correspondence.

## What the model connects

For monetary transfers, the modeled path is:

```text
controlled source effect and terminal outcome
  -> receipt issuance against the current exact source fact
  -> source-attestation checker and immutable terminal record
  -> guarded parent credit or return
  -> primary publication and current endpoint consumption
```

The source fact and the protocol decision are separate values. A record binds the immutable source key, the complete transfer binding and one terminal kind. Reauthentication can add evidence for that same core; it cannot replace the core. A proof hash, acknowledgment or timeout is insufficient to create a terminal outcome.

The child dispatcher consumes the record at the relevant publication, credit, return, reconciliation, descendant and regulatory operations. Its financial projection invokes the existing parent functions. The source-aware dispatcher additionally checks actual source effect, fence and current-outcome evidence. Arbitrary requests still enter the dispatcher and can be rejected.

The accounting result separates source effects into unresolved, credited and returned bindings. Credited and returned bindings are disjoint, and authoritative available source units plus unresolved mass plus destination root funding equal the original allocation. A local mirror and the physical source represent the same allocation; they are not additive balances.

## Calls and observations

Calls record invocation, authority execution, response collection and completion separately. One invocation identifier has at most one durable execution result. Repeating that identifier retrieves the recorded result; a new invocation executes against current guards. Completing `Busy` or `Unavailable` fixes that result, so a later attempt for a different result uses a new identifier.

Current reads require a cache equal to the current logical snapshot and a ready query. Protected application reads also consume current authorization and the actual parent data-read operation. Historical reads identify a stored snapshot from an actual execution prefix. Raw values, journals, operational status and physical source inspection remain separate observable interfaces.

A successful current source-balance response additionally requires source availability and zero debit and return reconciliation gaps. Secondary settlement progress is separate telemetry. A ready endpoint can consume primary state while secondary progress lags; a stale endpoint cannot label its cached value current.

The response theorems connect completed calls to the actual indexed callback and independently defined abstract values. The product-word theorems concern the core transfer ledger and regulatory state. The richer source projection is neither a classifier for every API reply nor a full transition simulation of all source and observation state.

## Source guide

| Area | Files and principal interfaces |
|---|---|
| Source effects and evidence | [Source_Effect_Boundary](Source_Effect_Boundary.thy), [Controlled_Source_Outcomes](Controlled_Source_Outcomes.thy), [Source_Finality_Link](Source_Finality_Link.thy): persistent effect identity, no-effect fences, immutable outcomes and `issue_source_receipt`. |
| Joint source execution | [Source_Coupling](Source_Coupling.thy), [Source_Coupling_Conservation](Source_Coupling_Conservation.thy): `source_coupling_step`, generated contracts, credit/return exclusion and `actual_source_pool_is_conserved`. |
| Terminal consumers | [Finality_Types](Finality_Types.thy), [Finality_Protocol](Finality_Protocol.thy), [Finality_Records](Finality_Records.thy): exact records, `terminal_intent_guard`, `invoke_protocol`, `invoke_regulatory` and `publish_primary`. |
| Funding and information | [Root_Funding_Bounds](Root_Funding_Bounds.thy), [Root_Continuation](Root_Continuation.thy), [Root_Information](Root_Information.thy), [Funding_Decision_Information](Funding_Decision_Information.thy): allocation bounds, preservation under other-root actions, lineage erasure and the funding/decision equivalence. |
| Independent product transitions | [Transfer_Ledger_Refinement](Transfer_Ledger_Refinement.thy), [Finality_Refinement](Finality_Refinement.thy): independent ledger arithmetic and actual finite transfer/regulatory action words. |
| Durable calls and order | [Finality_Calls](Finality_Calls.thy), [Call_Order](Call_Order.thy), [Sourced_Call_Order](Sourced_Call_Order.thy): `execute_authority_once`, completion provenance and ordering for later fresh invocations. |
| Local observations | [Finality_Observations](Finality_Observations.thy), [Abstract_Observation_Types](Abstract_Observation_Types.thy), [Historical_Snapshot_Provenance](Historical_Snapshot_Provenance.thy), [Abstract_Response_Link](Abstract_Response_Link.thy): actual readers, independent targets and indexed historical values. |
| Callback connections | [Observed_Protocol_Link](Observed_Protocol_Link.thy), [Sourced_Observations](Sourced_Observations.thy), [Sourced_Response_Link](Sourced_Response_Link.thy), [Source_Observation_Projection](Source_Observation_Projection.thy): actual callbacks, source guards, completed replies and core product words. |
| Recovery and progress | [Finality_Recovery](Finality_Recovery.thy), [Finality_Progress](Finality_Progress.thy), [Finality_Terminal_Progress](Finality_Terminal_Progress.thy): checked current replay, restored guarded dispatch, finite call completion, conditional terminal programs and the retry-interference obstruction. |
| Concrete examples | [Finality_Scenarios](Finality_Scenarios.thy), [Observation_Scenarios](Observation_Scenarios.thy), [Regulatory_Finality_Scenarios](Regulatory_Finality_Scenarios.thy), [Sourced_Completion_Scenarios](Sourced_Completion_Scenarios.thy), [Root_Continuation_Scenarios](Root_Continuation_Scenarios.thy), [Finality_Terminal_Scenarios](Finality_Terminal_Scenarios.thy): actual normal programs, theorem-premise activations and controls that remove a specific consumer check. |

## Representative boundaries and controls

- Normal paths include terminal-qualified bypass credit, a distinct reversed source outcome, exact recovery, fresh current reads, and monetary primary publication followed by an actual regulatory freeze, ordinary-transfer rejection and authorized enforcement.
- Removing a terminal-reference check permits an effect without the required record reference. Removing the source finalization barrier permits a refund after credit and breaks the allocation equation.
- Removing the current-state barrier admits an older cache. Checking only a revision number admits an invented value with the matching revision. Removing the source-gap guard exposes a stale local source balance after a lost acknowledgment.
- An internally replayable but truncated journal can omit a completed descendant effect. Comparison with the complete current authority source is therefore a separate requirement from replay.
- Two roots and two holder accounts can have equal pooled state after lineage erasure but different actual descendant decisions. A complete journal supplies different information and reconstructs the distinction.
- Raw source/destination observations can expose an intermediate pair that is neither atomic endpoint state. The raw interface remains visible; it receives no successful-current or confidentiality guarantee from the protected reader.

These controls establish the meaning of particular model guards and observation boundaries. They are not compiled-product mutation tests.

The conditional terminal programs start in a valid joint state with a current controlled terminal fact, an exact admissible certificate, an available issuance slot, an already mirrored source debit and an empty terminal-record slot. Under current credit admission and an unused credit marker, or current reservation ownership, pending phase and relay epoch, five delivered source-aware actions reach actual credit or return and primary publication. The source and context remain unchanged during this specified suffix. This does not ensure eventual evidence or delivery. A separate fresh durable call completes the final core publication response; it is not a theorem that all five actions are completed source-aware client calls.

## Implementation boundary

The model does not supply distributed terminal agreement across quorum, round, epoch changes and restart; a physical source adapter with durable effect/fence APIs; or the authentic complete current journal used by recovery. It also does not certify ABI encodings, hash preimages, compiler output, deployment behavior or secondary settlement execution.

Existing token authorization, dependency, replay and current-effect checks are recorded in the product obligations. A token action reversal with its own identity and parent action is distinct from changing an immutable source terminal fact. Local product defenses require an explicit connection to this model before they support its cross-domain claims.

The session declaration is in [ROOT](ROOT). The theory statements and their locale assumptions are the specification; repository prose and source-inspection inventories do not replace those premises or establish runtime conformance.

## Reproduce the proofs and technical guide

Use **Isabelle2025-2** and the pinned [ADS_Functor archive](https://isa-afp.org/release/afp-ADS_Functor-2026-02-06.tar.gz), SHA-256 `10d6fa8671c461022ae5e71859a07610d616681fed79e2f1c81029a124203c85`. The parent input baseline is repository commit `de8b06972347f31c38401c70160501664c98ed01`.

From the repository root, with the archive extracted so the given directory contains its `ROOT`:

```bash
node Evidence_Atomic_Binding/verify-source.mjs
isabelle build -b -j 1 -o threads=1 -o parallel_proofs=0 \
  -d /path/to/ADS_Functor -d . Evidence_Atomic_Binding
```

The named session includes every formal theory and control. Unchanged parent heaps can be reused after verifying their source and dependency hashes. To rebuild the standalone technical guide, install TeX Live with `pdflatex` and `bibtex` on `PATH`, then run:

```bash
node Evidence_Atomic_Binding/build-document.mjs /path/to/document-output
```

This produces `Evidence_Atomic_Binding.pdf` and TeX intermediates in the chosen directory. Relative source links in the PDF resolve from a sibling `release/` or `document/` directory inside the session; when using a separate output directory, read the linked theory files in the repository. The PDF summarizes the contract; all definitions and proofs remain in the theory sources. Generated PDFs and private audit logs are not tracked. The [claim ledger](claims.json) records checked statements, and the [source manifest](source-manifest.json) binds the public source and documentation bytes.
