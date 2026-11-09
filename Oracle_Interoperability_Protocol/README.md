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
  seeded inputs, typed values, response construction and current-client
  admission. Agreement on those inputs is separate from universal refinement.

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

The [ROOT](ROOT) declares the base sessions above and the v0.6.1 extension
sessions. Record reopening and the current reference profile are separate
model branches with distinct source contexts. The [source manifest](source-manifest.json)
pins ROOT and each theory file in this namespace. The compiler-input seal
records the checked build separately.

## Executable interfaces and comparison consumers

The typed transport export exposes
`OIP_Wire_Oracle_V061.sync_v061_nested_transport_flat` and the parameterless
`OIP_Wire_Oracle_V061.sync_v061_typed_model_identity`. The Full response export exposes
the sender, current-client and combined interfaces, including
`OIP_Wire_Response_Boundary.code_response_egress_flat_oracle` and
`OIP_Wire_Response_Boundary.code_response_full_model_identity`.

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
