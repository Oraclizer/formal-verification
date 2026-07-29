# Disclaimer

This repository is an academic formalization and proof artifact. It is not a
production implementation, security audit, legal service, compliance
certification, deployment recommendation, or warranty of any system.

## Model boundary

The Isabelle/HOL results apply to the exact definitions, locales, assumptions,
theories, and dependency environment identified by the evaluated commit.
They do not automatically apply to Rust, Solidity, EVM bytecode, a bridge,
network protocol, deployed contract, operator, or modified fork.

The model intentionally abstracts or assumes aspects including atomic
synchronization, finite domains, deterministic fairness, aggregate
pending-count behavior, and existential recovery. The exact dispositions are
documented in `FORMAL_MODEL_MAPPING.md`.

## Risk and use

Machine-checked proofs can coexist with an unsuitable model, missing
assumption, dependency issue, refinement error, implementation defect,
operational failure, key compromise, network failure, or incorrect external
fact. Independent review and implementation-specific evidence remain
necessary.

Nothing here is legal, regulatory, tax, investment, security, or operational
advice.

## License controls

The [BSD 3-Clause License](LICENSE) is controlling and includes warranty and
liability limitations. This plain-language summary does not replace, modify,
or expand the license.
