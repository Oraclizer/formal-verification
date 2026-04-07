# Contributing to Oraclizer Formal Verification

Thank you for your interest in contributing to the Oraclizer formal verification project.

## Scope

This repository contains Isabelle/HOL theories that formally verify safety and liveness properties of cross-domain state synchronization in Byzantine environments. Contributions may include:

- Bug reports (counterexamples, incorrect assumptions)
- Proof improvements (simplification, generalization)
- New instantiations of the generic locales in `State_Preservation.thy` or `Priority_Resolution.thy`
- Documentation improvements

## Requirements

- **Isabelle version:** 2025-2 or later
- All theories must build without `sorry` or `oops`
- Follow existing code style (see below)

## Building and Testing

```bash
# Check all proofs
isabelle build -d . Cross_Domain_State_Preservation

# Generate documentation
isabelle build -d . -o document=pdf Cross_Domain_State_Preservation
```

All proofs must pass before submitting a pull request.

## Code Style

- **Theory headers:** Include Title, Author, Maintainer, License fields in the header comment
- **Locale naming:** Use descriptive `snake_case` names
- **Lemma naming:** `[subject]_[property]` pattern (e.g., `confiscated_terminal`, `sync_isolation`, `lock_eventually_expires`)
- **Comments:** Use `text \<open>...\<close>` blocks for documentation, `\<comment> \<open>...\<close>` for inline remarks
- **LaTeX safety in comments:** When referring to identifiers containing underscores inside `text` blocks, wrap them with `\<^verbatim>\<open>...\<close>` or `\<^term>\<open>...\<close>` to prevent LaTeX rendering errors
- **Proof style:** Prefer structured Isar proofs over `apply` scripts for non-trivial results
- **Design decisions:** Document legal or domain-specific justifications in `text` blocks

## Pull Request Process

1. Fork the repository
2. Create a feature branch from `main`
3. Ensure `isabelle build` passes with no errors
4. Submit a pull request with a clear description of changes

## Reporting Issues

If you find an error in a proof, an incorrect assumption, or a counterexample to a stated property, please open an issue with:

- The specific theorem or lemma affected
- A minimal reproduction (Isabelle theory snippet if applicable)
- Your Isabelle version

## License

By contributing, you agree that your contributions will be licensed under the BSD 2-Clause License.
