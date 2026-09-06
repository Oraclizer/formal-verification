# Cross-Chain Message Integrity

This Isabelle/HOL session connects authenticated source facts to destination-credit execution. A source event may arrive through either route, with a new envelope identifier and at a later authority epoch. The model counts each new credit execution, including executions with identical values.

## Results

| Result | Source and principal theorem |
|---|---|
| Full authenticated payload binding | `Source_Certificates.source_attestation.accepted_payload_is_bound` |
| Honest attestation and stable source facts | `certificate_authenticates_source_fact`, `certificate_authenticates_stable_fact` |
| At most one new destination credit for each source key over arbitrary finite delivery traces | `Message_Execution.source_attestation.family_wide_at_most_once` |
| Exact condition for destination-local markers to give global uniqueness in the declared kernel | `Credit_Once_Kernel.local_markers_give_global_once_iff` |
| Normal and bypass representations preserve rejection, state, replies and finite continuations | `normal_bypass_guarantee_equivalence`, `normal_bypass_finite_continuation_equivalence` |
| Checked internal summaries exactly characterize receiver observations over all declared contexts | `Message_Summary.source_attestation.checked_summary_is_exact_information` |
| Reconstruction of markers from a complete credit history preserves subsequent deliveries in the same current contexts | `recovery_preserves_future_deliveries` |
| Actual regulatory permission and completed state-update consumers | [Message_Consumers.thy](Message_Consumers.thy) |

The kernel characterization concerns state-independent admission and the displayed destination/source-key marker rule. It is not a necessity result for every distributed implementation. The checked summary is computed after intrinsic verification; it is not an untrusted wire certificate, an optimal byte format or a statement about every product-reachable policy. General deterministic factorization and quorum intersection are established mathematical results.

## Assumptions and boundaries

The `source_attestation` locale separates cryptographic verification, actual signing, honest source-fact checks and stable source outcomes. Its trusted epoch configuration supplies a finite roster, a fault bound and a threshold strictly above that bound. A stable source outcome is unique for each source key. These are explicit external assumptions, not implementations proved by this session.

The execution context must contain actual current authority, permissions and version. The caller must come from an authenticated runtime context, not a self-asserted wire field. Every modeled route uses the same receiver. Credit and persistent marker insertion are one atomic local model step. The global history is a proof observation; admission consults the destination-local marker.

The session does not establish source-chain consensus, a source-lock protocol, an independent terminal-decision protocol, network liveness, full financial-journal recovery, distributed atomicity or compiled/runtime refinement. A source reversal does not authorize destination finality. Later lawful transfers are not new destination-credit occurrences.

The regulatory permission consumer uses the actual ordinary/enforcement distinction in Regulatory Action Composition. The completed state-update consumer uses Cross-Domain State Preservation for regulatory metadata. It does not treat regulatory holding support as token supply, and a valid metadata state does not establish current authorization.

## Concrete witnesses and negative tests

All examples and mutations are registered in `ROOT` and checked by the logic kernel. The concrete source/verifier table demonstrates satisfiability and activation; it is a finite model, not real cryptography.

`Message_Mutations` checks removal of each of the eight binding fields, destination conflicts, repeated equal-value credits, missing/erased markers, untrusted thresholds, repeated Byzantine signer identifiers and raw-message compression that launders invalid input. `Message_Boundaries` checks actual two-destination execution in the weakened kernel, distinct valid certificates with identical observations, information loss from a dropped authority epoch, stale FREEZE authorization, historical-record insufficiency for current permissions, invalid signatures, empty/unregistered signers, stale relay/version and changed envelope identifiers.

## Reproduction

Use **Isabelle2025-2** and the dated AFP entry:

- [ADS_Functor archive](https://isa-afp.org/release/afp-ADS_Functor-2026-02-06.tar.gz)
- SHA-256: `10d6fa8671c461022ae5e71859a07610d616681fed79e2f1c81029a124203c85`

From the repository root, after checking and extracting that archive:

```sh
isabelle build -c -v -j 1 -o threads=1 -o parallel_proofs=0 \
  -d /path/to/afp/ADS_Functor -d . Cross_Chain_Message_Integrity
```

`-c` cleans the selected session. Isabelle also builds its required parent sessions. To generate the reading document, use a TeX installation with `pdflatex`:

```sh
isabelle build -b -o document=pdf \
  -d /path/to/afp/ADS_Functor -d . Cross_Chain_Message_Integrity
isabelle document -O /path/to/document-output \
  -d /path/to/afp/ADS_Functor -d . Cross_Chain_Message_Integrity
```

The document is generated from these theories. Generated caches and PDFs are not authoritative source. The repository's `Proofs` workflow checks the same named session with pinned dependency archives. [claims.json](claims.json) maps the claims, assumptions and executable formal consumers; [verify-source.mjs](verify-source.mjs) checks the recorded source bytes and registered theory inventory before reproduction.
