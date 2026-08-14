# Contributing

This repository is the public home of two composable product-model sessions:
the ten-theory `Cross_Domain_State_Preservation` session and the standalone
`Regulatory_Action_Composition` child session. It also contains the independent
`PARTIAL / NO SAME` `Protected_Behavior_Obstructions` research companion, which
has no Oraclizer implementation or product-refinement target. The artifacts are
maintained as single-author scholarly works rather than as a conventional
open-source project that routinely merges external theory contributions.
Please keep this context in mind when engaging with the repository.

The repository is production-maintained as a public research surface. That
means every accepted change must preserve reproducibility, release identity,
public-claim consistency, and reviewability. It does not mean that this
repository contains or certifies a production implementation.

Read the [Code of Conduct](CODE_OF_CONDUCT.md), [Security
policy](SECURITY.md), and [Governance](GOVERNANCE.md) before contributing.

## Choose the right channel

| Contribution | Channel |
| --- | --- |
| Counterexample, proof, locale, or assumption challenge | Proof-review issue form |
| Documentation, link, citation, or rendering defect | Documentation issue form |
| Potentially exploitable or sensitive vulnerability | Private path in `SECURITY.md` |
| Build or usage question | `SUPPORT.md` |
| Material theory or architecture proposal | Issue first, before a Pull Request |

## What is most welcome

The highest-value contribution is scrutiny of the proofs themselves:

- **Counterexamples** to any stated theorem or property.
- **Incorrect or overly strong assumptions** in a locale or instance.
- **Soundness concerns** about the model, the threat model, or the stated scope.
- **Clarity issues** in the documentation, the abstract, or the model-to-implementation mapping.

If you find any of these, please open an issue (see below). Reports that question the validity
or the framing of the formalization are exactly the kind of engagement this entry benefits from.

## On code contributions

Changes to `.thy` sources are issue-first and handled at the affected session's
artifact boundary, not through ad-hoc merges. We do not generally accept pull
requests that add new locales, instances, or theorems. If you believe a proof
change is warranted (a fix for an unsound step, a meaningful simplification,
or a generalization), please open an issue before preparing a patch. This
keeps each public session coherent and auditable.

## Reporting issues

Please open an issue with:

- The exact commit.
- The specific theorem, lemma, or locale affected.
- A minimal reproduction (an Isabelle theory snippet if applicable).
- Your Isabelle version.
- The AFP revision and build command when reproduction depends on AFP.

## Building and checking the proofs

Anyone can independently check the proofs. The CDSP session depends on the AFP
entry `ADS_Functor`, and RAC inherits that session environment through CDSP,
so the AFP must be available to Isabelle: register it once with `isabelle components -u
/path/to/afp/thys`, or pass it via `-d` as shown below. See https://www.isa-afp.org/help/ for
obtaining and using the AFP.

```bash
# Check the two product-model sessions (point -d at both this repo and the AFP)
isabelle build -d . -d /path/to/afp/thys \
  Cross_Domain_State_Preservation Regulatory_Action_Composition

# Check the independent PARTIAL / NO SAME companion (AFP is not required)
isabelle build -c -D Protected_Behavior_Obstructions \
  Protected_Behavior_Obstructions

# Generate one session document into a chosen output directory
isabelle build -d . -d /path/to/afp/thys \
  -o document=pdf -o document_output=/path/to/output \
  Regulatory_Action_Composition
```

Before changing the companion, read its folder-local
[`CROSS_PROVER_MAPPING.md`](Protected_Behavior_Obstructions/CROSS_PROVER_MAPPING.md).
It is not an Oraclizer product-refinement mapping.

- **Isabelle version:** exactly 2025-2 for the audited build.
- All theories build without `sorry` or `oops`; independent confirmation of this is welcome.
- Isabelle may emit `document.pdf` in the build-output directory. A tracked
  reading copy must instead be named
  `<Session>/release/<Session>.pdf`.

Before submitting documentation or repository changes, also run:

```bash
node scripts/verify-repository-health.mjs
```

This lightweight check validates the public repository surface. It does not
replace the Isabelle build.

## Pull Request requirements

A Pull Request should:

- address one reviewable issue;
- explain the affected theorem, assumption, public claim, or document;
- preserve Isabelle `2025-2`, the session graph, and declared dependencies unless the change
  is an intentional migration;
- include the exact proof build result when theories or document sources
  change;
- update `FORMAL_MODEL_MAPPING.md` when an Oraclizer product-model assumption,
  result, or implementation target changes, and update the folder-local
  `Protected_Behavior_Obstructions/CROSS_PROVER_MAPPING.md` when the companion
  correspondence changes;
- preserve the production-maintenance contract across the README, governance,
  security, release manifest, and automated repository-health surfaces;
- contain no generated Isabelle output, credentials, private correspondence,
  machine-local paths, or unrelated artifacts;
- distinguish model-level evidence from implementation or deployment claims.

Maintainers may request a smaller patch or further mechanization and review.
A passing check does not guarantee acceptance or merge.

## Code style (for reference)

These conventions describe the existing sources, for readers studying or independently checking them:

- **Theory headers:** Title, Author, Maintainer, License fields in the header comment.
- **Locale naming:** descriptive `snake_case`.
- **Lemma naming:** `[subject]_[property]` (e.g., `confiscated_terminal`, `sync_isolation`, `starvation_bound`).
- **Comments:** `text \<open>...\<close>` for documentation, `\<comment> \<open>...\<close>` for inline remarks.
- **LaTeX safety:** the AFP document build runs LaTeX over `text` blocks and `\<comment> \<open>...\<close>` inline comments, so a bare underscore in either breaks it (math-mode error). When referring to identifiers with underscores inside a `text` block or a `\<comment>` comment, wrap them with `\<^verbatim>\<open>...\<close>` or `\<^term>\<open>...\<close>`, or word the remark without underscores.
- **Proof style:** structured Isar proofs preferred over `apply` scripts for non-trivial results.
- **Design decisions:** legal or domain-specific justifications documented in `text` blocks.

## License

By submitting a contribution, you represent that you have the right to submit
it, that it does not knowingly contain confidential or incompatibly licensed
material, and that it may be distributed under the BSD 3-Clause License.

Meaningful contributions may be credited through Git history, acknowledgments,
release notes, or a security advisory. State a preferred credit name if it
differs from your GitHub identity. Submission does not create an employment,
agency, support, acceptance, or publication obligation.
