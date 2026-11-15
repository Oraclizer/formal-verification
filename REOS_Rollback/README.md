# Authorized Selective Rollback

The Isabelle/HOL model checks scoped rollback against current authority,
policy and journal evidence. A successful operation restores the chosen
cells, preserves the frame and charges the case-local rollback budget.
The connected trace proofs preserve installed terminal records and their
protected ledger values. The replica repair operation installs the
recorded values on the chosen replica.

The release recovery example observes both the alias and manifest. The
legacy adapter connects terminal observations and prior priority selection
to the rollback contracts. Authority and evidence are verified inputs to
the abstract transition system. Implementations supply authentication,
authoritative external-effect receipts and durable state correspondence.

With the repository's Isabelle2025-2 and AFP ADS_Functor prerequisites:

~~~
isabelle build -d . REOS_Rollback_Examples REOS_Rollback_Legacy
~~~
