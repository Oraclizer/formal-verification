# Contributing

This repository is the public mirror of an academic verification artifact: a set of
Isabelle/HOL theories submitted to the [Archive of Formal Proofs](https://www.isa-afp.org/)
and currently under editor review. It is maintained as a single-author scholarly entry rather
than as a conventional open-source project that merges external pull requests. Please keep this
context in mind when engaging with the repository.

## What is most welcome

The highest-value contribution is scrutiny of the proofs themselves:

- **Counterexamples** to any stated theorem or property.
- **Incorrect or overly strong assumptions** in a locale or instance.
- **Soundness concerns** about the model, the threat model, or the stated scope.
- **Clarity issues** in the documentation, the abstract, or the model-to-implementation mapping.

If you find any of these, please open an issue (see below). Reports that question the validity
or the framing of the formalization are exactly the kind of engagement this entry benefits from.

## On code contributions

Because the theories are an AFP submission under review, changes to the `.thy` sources are
handled through the AFP process and the entry's authorship, not through ad-hoc merges here.
We do not generally accept pull requests that add new locales, instances, or theorems. If you
believe a proof change is warranted (a fix for an unsound step, a meaningful simplification, or
a generalization), please open an issue first to discuss it before preparing any patch. This
keeps the public mirror consistent with the version under review at the AFP.

## Reporting issues

Please open an issue with:

- The specific theorem, lemma, or locale affected.
- A minimal reproduction (an Isabelle theory snippet if applicable).
- Your Isabelle version.

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

- **Isabelle version:** 2025-2 or later.
- All theories build without `sorry` or `oops`; independent confirmation of this is welcome.

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

By contributing, you agree that your contributions will be licensed under the BSD 3-Clause License.
