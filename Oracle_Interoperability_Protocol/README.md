# OIP prototype models and source correspondence

This namespace contains Isabelle/HOL models for the Oracle Interoperability
Protocol and selected interfaces of its Rust reference implementation. The
[OIP repository](https://github.com/Oraclizer/oip-spec) contains the prototype
wire specification, Rust reference code and Go message implementation. The
[versioned documentation](https://docs.oraclizer.io/oip-v06/oip-overview/) describes the
protocol and its implementation boundaries.

The assurance scope has three parts:

- **Conditional HOL results.** Definitions, locale assumptions and theorem
  statements describe the modeled product, reference profile, record reopening,
  recovery boundary and message interfaces.
- **Manual Rust source correspondence.** Source-facing models and named
  correspondence statements expose selected Rust operations and assumptions.
  This is a manually maintained source relationship, not a verified Rust
  compiler or an automatic theorem about every compiled Rust execution.
- **Bounded executable wire comparisons.** The consumers compare fixed and
  seeded inputs, typed values, response construction, current-client
  admission and the signature step of raw THRESHOLD packets. Agreement on
  those inputs is separate from universal refinement.

The reference implementation is **prototype-stage, unaudited and not for
production**. This material does not establish an operational Witness service,
distributed deployment correctness, whole-product or financial implementation
refinement, or production safety. External source, cryptographic primitive and
storage assumptions remain explicit in the relevant statements.

## Source organization

| Session | Source relationship |
| --- | --- |
| `OIP_Product_Base` | Base model extending `Evidence_Atomic_Binding` |
| `OIP_Product` | Modeled product operations and completed observations |
| `OIP_Reference_Profile` | Reference authority and source-facing profile |
| `OIP_Reference_Execution` | Selected reference execution interfaces |
| `OIP_Record_Reopening` | Separate record-reopening model |
| `OIP_Recovery_Boundary` | Recovery provenance and storage-boundary statements |
| `OIP_Message_Code` | Canonical wire, admission and typed operand interfaces |
| `OIP_Message_Response` | Correlation, response boundary and client-facing interfaces |
| `OIP_Message_Egress` | Sender, primitive-query and current-client interfaces |

The [ROOT](ROOT) declares the base sessions and the v0.6.1 and v0.6.2
extensions. Record reopening and the current reference profile are separate
model branches with distinct source contexts. The [source manifest](source-manifest.json)
pins ROOT and each theory file in this namespace. The compiler-input seal,
[Validation/V061/kernel-input-seal.json](Validation/V061/kernel-input-seal.json),
records the checked build of the current namespace, including the v0.6.2
targets.

## Extension sessions

The 47 v0.6.1 extension sessions cover state commitment sync, scoped response
codes and the reference `Write` path. The 120 v0.6.2 extension sessions add
comparison models for configured threshold admission, retained outcomes and
selected reference storage boundaries under their stated premises. Both sets
build on the base sessions and keep the assurance scope stated above.

| Group | Sessions | Content |
| --- | --- | --- |
| Wire and authentication | 15 | Negotiation, canonical wire data and threshold signatures |
| State sync and reads | 39 | Commitment sync, queries, cached and historical reads |
| Responses and receipts | 14 | Response codes, signed replies and stored outcomes |
| Authority and asset effects | 61 | Handover, legal controls, locks and reference writes |
| Ordering and settlement | 17 | Scheduling, primary decisions and settlement queues |
| Persistence and recovery | 21 | Source journals, witness checks, publication and reopening |

The groups match the [session overview](../docs/assets/session-architecture.svg).
Exact session names, directories and parents are declared in [ROOT](ROOT).

## Executable interfaces and comparison consumers

The typed transport export exposes
`OIP_Wire_Oracle_V061.sync_v061_nested_transport_flat` and the parameterless
`OIP_Wire_Oracle_V061.sync_v061_typed_model_identity`. The Full response export exposes
the sender, current-client and combined interfaces, including
`OIP_Wire_Response_Boundary.code_response_egress_flat_oracle` and
`OIP_Wire_Response_Boundary.code_response_full_model_identity`. These interface
names date from v0.6.1 and are unchanged in the v0.6.2 binding; each six-field
identity carries the v0.6.2 runtime source fingerprint.

The THRESHOLD export exposes `OIP_Threshold_Raw_ABI.threshold_raw_packet`
and `OIP_Threshold_Raw_ABI.threshold_raw_model_identity`. Its 22 raw Packet
inputs use independent finite Ed25519 key and signature observations as
model premises. Rust and Go run their own configured verifiers on those bytes.
The raw suite compares the signature step and checks the finite transport
attestation and binding effects separately.

Each identity returns six fields: schema, ABI, scope, entrypoint, natural-number
refinement and runtime source fingerprint. Identity is not supplied by the
caller. Generated ML is consumed as unedited export bytes; model content hashes
and operational receipts are not embedded in the model identity.

The typed consumer compares all seven observation fields: input identity,
verdict, retained binding, reencoded Core bytes, signing preimage, transport-key
IR and typed operand IR. Its corpus has 692 fixed/seeded rows.

The Full consumer compares 33 original-operation inputs, 207 typed boundary
inputs and 21 current-client inputs. It resolves the model's exact primitive
requests through the separate provider, compares sender bytes and typed client
results, and passes the model's own sender output to its combined client
interface. A missing primitive record is an execution failure, not a false
cryptographic answer or protocol verdict. ABI/identity loading, these sampled
value comparisons and conditional HOL statements are different evidence scopes.

## Reproduction and downstream linkage

[REPRODUCING.md](REPRODUCING.md) describes exact source identity, session builds,
logical-session extraction, external drivers and the standard consumers.

A downstream consumer link may record the actual public OIP code commit after
the signed root has been observed through the public API. That link is separate
metadata: CodeCommit is not an input to the source fingerprint, model identity,
export, artifact origin or lock. Creating the formal sources and model bytes
does not depend on that later public code link.

The exact public code commit and model content pins are listed in [consumer-binding.json](consumer-binding.json).
They bind the [OIP v0.6.2 release](https://github.com/Oraclizer/oip-spec/releases/tag/v0.6.2)
at commit `ba2a775ef41ab368fc243fc07ab5a8ecdd699263`.
