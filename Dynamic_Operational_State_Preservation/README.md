# Dynamic operational state preservation

The Isabelle/HOL sessions model synchronization degrees, authorized
promotion, metered credit and dynamic replica repair. The degree model
separates hub-only observation from commits initiated by other domains.
The cutover admits promotion after the affected locks have cleared and
charges each admitted binding against the applicable registry ticket.

The integrated example runs two credits for the same asset with distinct
bindings on opposite sides of a promotion. One authority supplies the
settlement clock, issues the publication sequence and records the metered
transition in its journal. It checks the active session identity and retains
the new metering version on an authorized promotion. The replayed publication
then drives installation of the original job at its successor domain after a
membership change.
The example also exercises a stale registry ticket and a modified journal.

The recovery proofs track pending jobs and irreversible facts. With finite
interference and an actual installation selected whenever recovery is pending,
the fixed-primary execution converges and agrees with the selected repair
observation. The replicated catalog instantiates the progress argument with
its own publication, withdrawal, transfer and removal events.

The model takes registry, clock, membership and attestation decisions as
verified inputs. Runtime correspondence requires matching these inputs and the
journal and replica installation effects to the deployed authority and storage
interfaces.

## Routing, settlement and receipt checks

The [model defense session](model-defense/DOSP_Product_Source.thy) connects the routing, billing and
recovery decisions in one product model. It checks an ordered plan of
outstanding routing grants, rejects new grants with retroactive activation
times, and preserves earlier approvals when a proposed plan conflicts.
An exit closes the ordinary route. A previously debited binding can still
settle under its live lock and exact confirmation. A locally rolled-back
attempt leaves that binding pending and records the verified failure charge.

One checked trace starts with a native publication and reports a receipt for
the same asset observed at a replica. Two independently replayed journals
establish that the competing receipt has the same sequence and a different
binding. The report opens a recovery job, and the appointed current receipt
authorizes its installation. The replica stores the projected value and the
job is completed; other pending jobs and irreversible facts are preserved.
The recovery convergence theorem uses verified-ready service on an execution
with finite interference.

## Reproduce

With Isabelle2025-2 and the repository's pinned AFP ADS_Functor dependency,
run from the repository root.

~~~sh
isabelle build -d . -d /path/to/ADS_Functor -j 1 -o threads=1 -o parallel_proofs=0 \
  DOSP_Model_Defense DOSP_Quiet_Run_Comparison DOSP_Rollback_Trade_Recovery \
  DOSP_Terminal_Repair DOSP_Legacy DOSP_OIP_Profile \
  DOSP_Router_Metadata_Projection DOSP_Billing_Epoch_Projection
~~~
