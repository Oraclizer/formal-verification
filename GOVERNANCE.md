# Governance

This repository is maintained by Oraclizer as the public home of
single-author scholarly Isabelle/HOL artifacts. It has no elected governance
body, token vote, or delegated release committee.

## Maintainer authority

The maintainer controls repository access, triage, merge decisions, artifact
designations, tags, releases, publication metadata, and scholarly submissions.
Opening an issue or Pull Request creates no obligation to accept, merge,
publish, submit, or respond within a particular period.

## Decision principles

Changes are evaluated for:

1. logical correctness and consistency with the Isabelle sources;
2. precise assumptions and honest model boundaries;
3. reproducibility under the declared Isabelle and AFP versions;
4. consistency between theories, paper, mapping, and public claims;
5. scholarly attribution, licensing, and provenance;
6. maintainability and compatibility across declared Isabelle sessions.

## Merge policy

Theory, document-source, or theorem-claim changes require a clean Isabelle
session build and an updated mapping when assumptions or targets change.
Documentation-only changes must pass repository-health checks. Independent
review may be requested for material proof or security changes.

A green check does not compel a merge. Material theory changes remain
issue-first so that the affected session can be reviewed as one coherent
artifact.

## Publications and releases

A repository branch, badge, PDF, tag, preprint, AFP submission, AFP acceptance,
and production implementation are distinct states. Public materials must not
represent one as another.

Tags and releases must bind an exact commit, proof environment, session set,
status, and change summary. Existing tags must not be moved or reused.

## Amendments

Governance changes are recorded in `CHANGELOG.md`. Community participation
remains subject to the repository license and Code of Conduct.
