# Security policy

## Artifact status

This repository is an academic, model-level formal verification artifact. It
does not contain a production bridge, validator, relayer, smart contract,
wallet, key-management system, or deployed service.

| Scope | Status |
| --- | --- |
| Exact tracked CDSP and RAC sessions | Proof and model reports accepted |
| Earlier commits and forks | Best effort only |
| Implementations and deployments | Not covered |

This policy creates no warranty, support agreement, audit representation, or
service-level commitment.

## Report sensitive concerns privately

Use GitHub Private Vulnerability Reporting:

1. Open the repository's **Security** tab.
2. Select **Advisories**.
3. Select **Report a vulnerability**.

If private reporting is unavailable, email `jay@oraclizer.io` with the subject
`FORMAL VERIFICATION SECURITY`. Do not include secrets, personal data,
production credentials, or unrelated confidential information.

Do not publish exploit details in an issue, Pull Request, discussion, social
post, paper review, or standards forum before coordinated disclosure.

## What to report publicly

Ordinary counterexamples, invalid lemmas, overly strong assumptions,
reproduction failures, model-scope concerns, and documentation errors are
valuable and may use the public proof-review issue form when they are not
sensitive or exploitable.

Include the exact commit, theory, theorem or locale, Isabelle version, AFP
revision, build command, minimal reproduction, expected result, and observed
result.

## Handling

The maintainer will assess whether a report affects a tracked session and
may request more information. No response, remediation, disclosure, release,
or publication deadline is guaranteed. There is no bug bounty or financial
reward program.

Credit may be offered in Git history, acknowledgments, release notes, or a
security advisory when requested and appropriate.

## Assurance boundary

A successful Isabelle build shows that the theories satisfy the Isabelle
kernel under their definitions and assumptions. It does not establish
model-to-code refinement, implementation safety, deployment security,
cryptographic correctness, network liveness, or legal compliance.

The BSD 3-Clause License controls and includes warranty and liability
limitations. This policy does not expand the license or certify the artifact.
