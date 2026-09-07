<!-- SPDX-License-Identifier: BSD-3-Clause -->
# Evidence Binding Composition

`Evidence_Binding_Composition` formalizes finite funding allocation, the calls
that consume it, and preservation of their responses through historical-state
projection and recovery in Isabelle/HOL. It extends
[Evidence Atomic Binding](../Evidence_Atomic_Binding/README.md).

The statements concern HOL operations, not deployed adapters, contracts,
storage or distributed protocols. [MODEL_BOUNDARY.md](MODEL_BOUNDARY.md)
specifies the assumptions and limits of each connection.

## From allocation to completed calls

A financial root identifies one credited source transfer. Pooled account
balances do not identify which root may fund a later transfer.

For finite selections of credited roots and holders, the allocation theorem
characterizes the target tables reached by supported successful ordinary
transfer words with unchanged final pooled balances and non-lineage
reservation state. The necessary and sufficient arithmetic conditions are:

- each selected root retains its total funding across the selected holders;
- each complete destination account retains its selected funding total.

The assumptions include the parent reservation contract, distinct root keys
and distinct holders. Accounts include destination, asset and holder: equal
holder labels on different accounts are not a shared column. The construction
gathers and redistributes each root's selected funding, supplying current
permissions for its positive transfers. A fixed policy can prevent realization.

[Source_Realization_Link](Source_Realization_Link.thy) connects transfers to
current contexts, confirmed terminal references and primary publication.
[Source_Call_Realization](Source_Call_Realization.thy) translates them into actual sourced calls:

```text
source effect and issued evidence -> terminal record and credit
  -> permitted transfer -> fresh completed call
  -> recovery of the same recorded execution -> projected continuation
```

Each translated client command completes a cache refresh and then the unchanged
command under fresh identifiers. The translation preserves the actual source
state and records rejected replies as well as successful ones. Recovery uses
the same generated call machine, with its existing identifiers, log and results.

## Information depends on the consumer

Historical queries do not read every field stored in a snapshot. The historical
projection normalizes six financial fields while preserving all modeled query
values, readiness decisions and subsequent observed or sourced replies.
The current core, current caches, raw journals and source effects remain intact.
The result extends to every finite word in those client and environment
languages, including completed `Busy`, `Unavailable` and rejected responses.

The counterexamples delimit that result. Full current-snapshot comparisons and
raw history readers distinguish information that historical queries can ignore.
A projected state can preserve replies without being reachable in the original
machine. No globally minimal state representation is claimed.

Two histories generated from the same source genesis illustrate the distinction:

| Before the same one-unit probe | Pooled balances at holders 3 and 4 | Root 17 funding at holder 4 | Completed reply |
|---|---|---|---|
| Before the exchange | `(5, 5)` | `5` | Executed |
| After the exchange | `(5, 5)` | `0` | Rejected |

The probe uses the same root, sender, recipient, amount and current permission.
Both outcomes come from fresh executions. Their completed replies remain
distinct after exact recovery and every finite projected continuation.

A separate regulatory application completes a monetary prefix, a freeze,
ordinary-transfer rejection and authorized enforcement on one observed call
machine. It also supplies a changed historical snapshot and preserves both
completed decisions through recovery. Its regulatory fact is a supplied
attestation input, not a physical regulatory-fact producer.

## Source guide

| Topic | Sources |
|---|---|
| Constructive allocation and its converse | [Funding_Realization](Funding_Realization.thy), [Funding_Characterization](Funding_Characterization.thy) |
| Actual source operations and fresh completed calls | [Source_Realization_Link](Source_Realization_Link.thy), [Source_Call_Realization](Source_Call_Realization.thy) |
| Historical projection and necessary observable distinctions | [Historical_Decision_Projection](Historical_Decision_Projection.thy), [Integration_Boundaries](Integration_Boundaries.thy) |
| Ordered recovery inputs and continuation | [Integration_Transport](Integration_Transport.thy) |
| Generated clock and regulatory applications | [Integration_Examples](Integration_Examples.thy), [Regulatory_Composition_Example](Regulatory_Composition_Example.thy) |
| Reply preservation versus original-state reachability | [Historical_Reachability_Boundary](Historical_Reachability_Boundary.thy) |
| Current permissions and the fixed even-amount policy | [Funding_Guard_Controls](Funding_Guard_Controls.thy), [Even_Amount_Policy_Boundary](Even_Amount_Policy_Boundary.thy) |
| Successful orderings distinguished by raw history | [Funding_Order_Boundary](Funding_Order_Boundary.thy) |
| Equal pooled balances with different completed funding decisions | [Funding_Completion_Separation](Funding_Completion_Separation.thy) |

The parent supplies message authentication, reservation accounting, terminal
consumers, the durable-call kernel and the descendant funding threshold.
The child connects finite allocation, complete call histories, projected behavior
and recovery of those existing machines. No new general transportation or
quotient mathematics is claimed.

## Reproduction

Use **Isabelle2025-2** and the dated [AFP ADS_Functor archive](https://isa-afp.org/release/afp-ADS_Functor-2026-02-06.tar.gz),
SHA-256 `10d6fa8671c461022ae5e71859a07610d616681fed79e2f1c81029a124203c85`.
From the repository root, point `-d` at the extracted directory containing its `ROOT`:

```bash
node Evidence_Binding_Composition/verify-source.mjs
isabelle build -b -j 1 -o threads=1 -o parallel_proofs=0 \
  -d /path/to/ADS_Functor -d . Evidence_Binding_Composition
```

The session uses `document = false`. With `pdflatex` and `bibtex` on `PATH`,
the separate document builder writes into the selected output directory:

```bash
node Evidence_Binding_Composition/build-document.mjs output/Evidence_Binding_Composition
```

Name the session and repository commit when citing a result. See
[CONTRIBUTING](../CONTRIBUTING.md), [CITATION](../CITATION.cff) and [LICENSE](../LICENSE).
