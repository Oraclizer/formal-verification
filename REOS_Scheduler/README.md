# Ordinary Request Service under Regulatory Priority

The open scheduler admits new signed packets, selects eligible regulatory
actions and services ordinary work in FIFO order. A selected governed
rollback calls the authority-checked rollback handler with the exact
selected intent. With finite executed regulatory interference and
recurring honest service opportunities, the admitted ordinary packet is
served with the original packet in its receipt.

The request proof tracks the finite FIFO cohort present at admission and
uses the separately developed finite-interference completion theorem in
`DOSP_Progress.Recovery_Progress`. Strict escalation in a fixed finite
set of bounded cases gives one way to establish finite interference.
The examples include a starvation execution with legal de-escalation
and a deployment catalogue that reads the exact manifest receipt.
These are model-level contracts for supplied authority, ordering and
service evidence.

With the repository's Isabelle2025-2 and AFP ADS_Functor prerequisites:

~~~
isabelle build -d . DOSP_Progress REOS_Scheduler_Controls
~~~
