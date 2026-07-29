# Contributing

This repository is the public mirror of an academic verification artifact: a set of
Isabelle/HOL theories prepared as a ten-theory resubmission candidate for the
[Archive of Formal Proofs](https://www.isa-afp.org/). An earlier submission exists, but the
current candidate has not yet been uploaded. It is maintained as a single-author scholarly entry rather
than as a conventional open-source project that merges external pull requests. Please keep this
context in mind when engaging with the repository.

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

Because the theories form an AFP resubmission candidate, changes to the `.thy` sources are
handled through the AFP process and the entry's authorship, not through ad-hoc merges here.
We do not generally accept pull requests that add new locales, instances, or theorems. If you
believe a proof change is warranted (a fix for an unsound step, a meaningful simplification, or
a generalization), please open an issue first to discuss it before preparing any patch. This
keeps the public mirror consistent with the audited candidate.

## Reporting issues

Please open an issue with:

- The exact commit.
- The specific theorem, lemma, or locale affected.
- A minimal reproduction (an Isabelle theory snippet if applicable).
- Your Isabelle version.
- The AFP revision and build command when reproduction depends on AFP.

## Building and checking the proofs

Anyone can independently check the proofs. The entry depends on the AFP entry `ADS_Functor`,
so the AFP must be available to Isabelle: register it once with `isabelle components -u
/path/to/afp/thys`, or pass it via `-d` as shown below. See https://www.isa-afp.org/help/ for
obtaining and using the AFP.

```bash
# Check all proofs (point -d at both this repo and the AFP)
# expects: Finished Cross_Domain_State_Preservation, no errors
isabelle build -d . -d /path/to/afp/thys Cross_Domain_State_Preservation

# Generate the document PDF
isabelle build -d . -d /path/to/afp/thys -o document=pdf Cross_Domain_State_Preservation
```

- **Isabelle version:** exactly 2025-2 for the audited build.
- All theories build without `sorry` or `oops`; independent confirmation of this is welcome.

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
- preserve Isabelle `2025-2` and the declared AFP dependency unless the change
  is an intentional migration;
- include the exact proof build result when theories or document sources
  change;
- update `FORMAL_MODEL_MAPPING.md` when an assumption, result, or
  implementation target changes;
- contain no generated Isabelle output, credentials, private correspondence,
  machine-local paths, or unrelated artifacts;
- distinguish model-level evidence from implementation or deployment claims.

Maintainers may request a smaller patch, further mechanization, or AFP review.
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
