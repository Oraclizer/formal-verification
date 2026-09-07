# Preemptive Lock Correctness

This Isabelle/HOL session connects asset reservations and worker leases to irreversible source obligations, authenticated destination credit, rooted financial effects and complete-journal recovery. It extends the existing Cross-Chain Message Integrity session without changing that parent's definitions or claims.

## Checked results

| Result | Principal source |
|---|---|
| Complete-footprint acquisition, reservation ownership and exclusion | [Reservation_Ownership.thy](Reservation_Ownership.thy) |
| Committed writes, monotonically increasing versions, stale-worker rejection and asset frames | [Reservation_Frame.thy](Reservation_Frame.thy) |
| Acyclic snapshot conflicts and conditional takeover/cleanup paths | [Reservation_Progress.thy](Reservation_Progress.thy) |
| Source non-reuse connected to the actual destination-once receiver and prior source effect | [Reservation_Message_Link.thy](Reservation_Message_Link.thy) |
| Executable reversal evidence and exclusion of conflicting current or later credit | [Reservation_Evidence.thy](Reservation_Evidence.thy) |
| Permanent cancel/fence closure and actual return-journal uniqueness | [Reservation_Return_History.thy](Reservation_Return_History.thy) |
| Unresolved, credited and returned bindings form an exclusive settlement partition | [Reservation_Settlement.thy](Reservation_Settlement.thy) |
| Account-history correspondence, root funding and source-pool allocation conservation | [Reservation_Conservation.thy](Reservation_Conservation.thy) |
| Identical expired pending states do not determine different stable outcomes | [Reservation_Boundaries.thy](Reservation_Boundaries.thy) |
| Pooled balances and credit records do not determine rooted onward spending | [Reservation_Lineage.thy](Reservation_Lineage.thy) |
| Publication-sensitive internal summaries factor the actual message consumer | [Reservation_Information.thy](Reservation_Information.thy) |
| Complete-journal recovery preserves actual continuations after arbitrary cache loss | [Reservation_Recovery.thy](Reservation_Recovery.thy) |
| A proved execution contract for the subsequent protocol layer | [Reservation_Provider.thy](Reservation_Provider.thy) |

For every finite execution and each source allocation pool, the current source balance plus unresolved obligations plus that pool's current destination funding equals the genesis allocation. Funding is indexed by its source key and holder, so lawful onward transfers change its distribution without creating new principal. A completed destination credit awaiting source acknowledgement is counted as credited, not again as unresolved. Return history is connected to permanent returned records and occurs at most once per source key.

The source key is an immutable event identity. New envelope identifiers, worker generations and authority epochs do not reset it. Acquisition checks the whole dependency footprint in one local model step. A worker lease is separate from the resource reservation. Timeout changes neither ownership nor financial authority. The destination receiver does not wait for a local source-pending notification or an unexpired source worker lease.

## Assumptions and exact boundaries

- The inherited source-attestation locale assumes sound cryptographic verification, a trusted finite roster and fault/threshold configuration, honest source checking, and a unique stable non-Observed statement at each source key. A later Finalized-to-Reversed change at the same key is outside that profile. The reversal result is not an independent terminal-consensus proof.
- Caller identity, current authority and policy, regulatory metadata, coherent versions and dependency footprints must come from authoritative runtime providers. The model checks the supplied fields; it does not establish their real-world authenticity or freshness.
- Source accounts are allocation pools indexed by domain and asset. A concrete adapter must relate them to real holders and source events. Token quantities are distinct from regulatory holding support.
- The no-effect fence is an atomic action of the modeled authoritative source endpoint: it checks a persistent debit record and permanently closes the key. Absence of a local observation of an uncontrolled external effect is insufficient.
- Effect, marker and journal updates are atomic durable model steps. Recovery uses a complete authentic locally produced journal and the same genesis allocation. Completed observations are retained separately, and historical policy evidence is not reconstructed in full. A crash between an external effect and its record is outside this model.
- The conflict result concerns completed Busy attempts against one state. There is no worker scheduler or persistent waiter queue. Recovery call bounds apply once their stated current authority, lease, version and evidence conditions hold, and the calls actually execute while those conditions hold. No unconditional external-evidence or wall-clock progress bound is claimed.
- `asset_value` is committed application data. Reservation cancellation does not roll it back as though it were a tentative binding-transaction value.

There is no claim of distributed observational atomicity, realization of every proposed normal form, independent terminal decisions, general composition of recovery representations, or compiled/runtime implementation refinement. The implementation status is **PLANNED**. [refinement-obligations.json](refinement-obligations.json) records the concrete producer and implementation obligations, including missing consumers. General accounting, factorization and guarded-invariant packaging are standard mathematics; they are not counted as new general mathematical results.

## Executed controls and mutations

All controls and mutations are theory inputs registered in `ROOT`. Positive executions include source acquisition/debit/credit, reversal release, authoritative non-effect fencing, worker takeover, current writes and reads, independent-asset progress, two roots sharing an account, onward spending and cache-loss recovery.

Negative inputs cover contention, stale caller/authority/version/generation, invalid zero-value dispatch, wrong ownership, frozen current policy, and conflicting source outcomes. Explicit mutations remove source or destination once checks, local publication origin, reversal evidence, expected-version or policy admission, or restore a cache without once state. Wrong-target writes alter an unrelated asset. The timeout-refund policy and the coupled phase-and-owner closure omission demonstrate duplicated funds. The latter is explicitly a two-field closure-mechanism mutation, not a single-guard minimality claim. The finite source/verifier instances establish satisfiability and actual branch activation, not real cryptography.

## Reproduction

Use **Isabelle2025-2** and the pinned [ADS_Functor archive](https://isa-afp.org/release/afp-ADS_Functor-2026-02-06.tar.gz), SHA-256 `10d6fa8671c461022ae5e71859a07610d616681fed79e2f1c81029a124203c85`. The parent input baseline is repository commit `0de6d7961ff0884e392bc573c0dec602b7bda6c6`.

From the repository root, after verifying and extracting the archive:

```sh
node Preemptive_Lock_Correctness/verify-source.mjs
isabelle build -c -v -j 1 -o threads=1 -o parallel_proofs=0 \
  -d /path/to/afp/ADS_Functor -d . Preemptive_Lock_Correctness
```

The named session includes every formal theory and control. `-c` cleans the selected session; unchanged parents can be reused after checking their source and dependency hashes. To build the technical companion with a TeX installation providing `pdflatex`:

```sh
isabelle build -b -o document=pdf \
  -d /path/to/afp/ADS_Functor -d . Preemptive_Lock_Correctness
isabelle document -O /path/to/document-output \
  -d /path/to/afp/ADS_Functor -d . Preemptive_Lock_Correctness
```

On Windows with TeX Live, Isabelle's user settings may need `ISABELLE_PDFLATEX="pdflatex -interaction=nonstopmode -file-line-error"`; the alternative Windows `-c-style-errors` option is not supported by TeX Live. This is a local toolchain setting, not a change to the proof model.

[claims.json](claims.json) records exact theorem statements and assumption boundaries. [source-manifest.json](source-manifest.json) binds the source, documentation and mapping bytes. The technical companion summarizes the results; all complete definitions, proofs and controls remain in the accompanying theory files. Generated PDFs, caches and temporary audit outputs are not authoritative source.
