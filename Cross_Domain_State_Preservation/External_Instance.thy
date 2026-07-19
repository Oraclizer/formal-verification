(*
  Title:      Cross_Domain_State_Preservation/External_Instance.thy
  Author:     Jinwook Kim (Jay) <jay@oraclizer.io>
  Maintainer: Jinwook Kim (Jay) <jay@oraclizer.io>
  License:    BSD

  Cross-Domain State Preservation Functor — An Instance Outside the
  Regulatory Domain

  This theory instantiates the generic locales of State_Preservation.thy on
  a domain with no connection to the regulatory vocabulary: a TCP-inspired
  toy endpoint lifecycle and an abstract tracker record.  The state and event
  names are drawn from RFC 793, but the model is not trace-conformant to that
  specification and is not a model of a concrete conntrack implementation.
  The theory imports only the generic
  locale layer and the generic proof automation; it does not depend on
  Regulatory_Instance.thy, which is itself the evidence that the framework
  carries no hidden regulatory assumptions.

  The instance reuses, outside their original domain, the two structural
  patterns of the regulatory instances:

    * the action-scoping pattern: the tracker observes a strict subset of
      the endpoint's events (the wire-visible handshake and teardown
      packets), so the locale's actions_s parameter is instantiated with
      that subset, exactly as the escalation instance scopes the regulatory
      vocabulary;

    * the layer-crossing pattern: the tracker state is a structured record
      (a phase tag plus peer-endpoint metadata) whose well-formedness
      invariant ties the auxiliary field to the tag, exactly as the DAML
      permission record does.
*)

theory External_Instance
  imports Proof_Automation
begin

section \<open>A TCP-Inspired Endpoint State Machine\<close>

text \<open>
  A toy single-endpoint lifecycle, restricted to six states and five packet
  events and using names inspired by RFC~793.  It is not an RFC~793 subset or
  a trace-conformant TCP model: in particular, \<open>FIN-WAIT\<close> followed by \<open>ACK\<close>
  goes directly to \<open>CLOSED\<close>, deliberately collapsing the peer-FIN and
  TIME-WAIT stages.  The purpose is only to instantiate the generic locales
  outside the regulatory vocabulary.  A \<open>RST\<close> aborts any modeled connection
  in flight.

  Two modelling notes.  First, \<open>CLOSED\<close> is terminal: a re-connection is a
  new connection identity (a new tracker entry), not a transition of the old
  one.  Second, a \<open>RST\<close> in \<^emph>\<open>listen\<close> is ignored by RFC~793; the partial
  transition function returns \<open>None\<close> there, as for every other
  state/event pair the subset does not admit.
\<close>

datatype tcp_state =
  LISTEN | SYN_SENT | SYN_RCVD | ESTABLISHED | FIN_WAIT | CLOSED

datatype tcp_event = EvSyn | EvSynAck | EvAck | EvFin | EvRst

fun tcp_transition :: "tcp_state \<Rightarrow> tcp_event \<Rightarrow> tcp_state option" where
  "tcp_transition LISTEN      EvSyn    = Some SYN_RCVD"
| "tcp_transition SYN_SENT    EvSynAck = Some ESTABLISHED"
| "tcp_transition SYN_RCVD    EvAck    = Some ESTABLISHED"
| "tcp_transition ESTABLISHED EvFin    = Some FIN_WAIT"
| "tcp_transition FIN_WAIT    EvAck    = Some CLOSED"
| "tcp_transition SYN_SENT    EvRst    = Some CLOSED"
| "tcp_transition SYN_RCVD    EvRst    = Some CLOSED"
| "tcp_transition ESTABLISHED EvRst    = Some CLOSED"
| "tcp_transition FIN_WAIT    EvRst    = Some CLOSED"
| "tcp_transition _           _        = None"

definition tcp_states :: "tcp_state set" where
  "tcp_states = {LISTEN, SYN_SENT, SYN_RCVD, ESTABLISHED, FIN_WAIT, CLOSED}"

definition tcp_events :: "tcp_event set" where
  "tcp_events = {EvSyn, EvSynAck, EvAck, EvFin, EvRst}"

definition tcp_terminal :: "tcp_state set" where
  "tcp_terminal = {CLOSED}"

lemma tcp_states_UNIV: "tcp_states = UNIV"
  unfolding tcp_states_def by (auto, case_tac x, auto)

lemma finite_tcp_states: "finite tcp_states"
  unfolding tcp_states_def by simp

lemma finite_tcp_state_UNIV: "finite (UNIV :: tcp_state set)"
  using finite_tcp_states by (simp add: tcp_states_UNIV)

lemma closed_terminal: "tcp_transition CLOSED e = None"
  by (cases e) simp_all

section \<open>The Connection-Tracker Representation\<close>

text \<open>
  The tracker entry is a structured record: a phase tag together with the
  peer-endpoint metadata the tracker keeps for a connection in flight.  The
  well-formedness invariant ties the auxiliary field to the tag --- the peer
  is recorded exactly while a connection attempt or connection exists ---
  mirroring the layer-crossing pattern of the regulatory development.  The
  peer identifier value itself is a representative placeholder, exactly as
  in the DAML permission record; what the invariant tracks is its presence.
  The tracker's state space is the image of the representation map, and its
  transition function is the lift of the endpoint transition through that
  map, guarded by the image domain.
\<close>

datatype ct_phase =
  CtNew | CtSynSent | CtSynRecv | CtEstablished | CtFinWait | CtClosed

record ct_entry =
  ct_state :: ct_phase
  ct_peer  :: "nat option"

definition default_peer :: nat where
  "default_peer = 0"

fun tcp_to_ct :: "tcp_state \<Rightarrow> ct_entry" where
  "tcp_to_ct LISTEN      = \<lparr> ct_state = CtNew,         ct_peer = None \<rparr>"
| "tcp_to_ct SYN_SENT    = \<lparr> ct_state = CtSynSent,     ct_peer = Some default_peer \<rparr>"
| "tcp_to_ct SYN_RCVD    = \<lparr> ct_state = CtSynRecv,     ct_peer = Some default_peer \<rparr>"
| "tcp_to_ct ESTABLISHED = \<lparr> ct_state = CtEstablished, ct_peer = Some default_peer \<rparr>"
| "tcp_to_ct FIN_WAIT    = \<lparr> ct_state = CtFinWait,     ct_peer = Some default_peer \<rparr>"
| "tcp_to_ct CLOSED      = \<lparr> ct_state = CtClosed,      ct_peer = None \<rparr>"

fun ct_to_tcp :: "ct_entry \<Rightarrow> tcp_state" where
  "ct_to_tcp p = (case ct_state p of
                    CtNew         \<Rightarrow> LISTEN
                  | CtSynSent     \<Rightarrow> SYN_SENT
                  | CtSynRecv     \<Rightarrow> SYN_RCVD
                  | CtEstablished \<Rightarrow> ESTABLISHED
                  | CtFinWait     \<Rightarrow> FIN_WAIT
                  | CtClosed      \<Rightarrow> CLOSED)"

definition valid_ct_entry :: "ct_entry \<Rightarrow> bool" where
  "valid_ct_entry p \<longleftrightarrow> (ct_state p \<in> {CtNew, CtClosed}) = (ct_peer p = None)"

lemma tcp_to_ct_valid: "valid_ct_entry (tcp_to_ct s)"
  by (cases s) (auto simp: valid_ct_entry_def)

lemma ct_to_tcp_to_ct_id: "ct_to_tcp (tcp_to_ct s) = s"
  by (cases s) simp_all

definition ct_states :: "ct_entry set" where
  "ct_states = range tcp_to_ct"

definition ct_terminal :: "ct_entry set" where
  "ct_terminal = {tcp_to_ct CLOSED}"

section \<open>The Tracked Event Subset and the Tracker Transition\<close>

text \<open>
  The abstract tracker observes the modeled handshake and teardown events but
  excludes \<open>RST\<close> by design.  This is an action-scoping choice, not a claim
  about a concrete operating-system conntrack implementation.  The source
  action set of the preservation morphism is therefore the strict subset of
  tracked events, and the tracker has its own event alphabet, mapped one-to-one
  from that subset.
\<close>

datatype ct_event = CT_SYN | CT_SYNACK | CT_ACK | CT_FIN

definition tracked_events :: "tcp_event set" where
  "tracked_events = {EvSyn, EvSynAck, EvAck, EvFin}"

definition ct_events :: "ct_event set" where
  "ct_events = {CT_SYN, CT_SYNACK, CT_ACK, CT_FIN}"

fun tcp_to_ct_event :: "tcp_event \<Rightarrow> ct_event" where
  "tcp_to_ct_event EvSyn    = CT_SYN"
| "tcp_to_ct_event EvSynAck = CT_SYNACK"
| "tcp_to_ct_event EvAck    = CT_ACK"
| "tcp_to_ct_event EvFin    = CT_FIN"
| "tcp_to_ct_event EvRst    = CT_SYN"
  \<comment> \<open>The last clause is unused by the morphism, since \<open>actions\<^sub>s\<close> is the
      tracked subset, which excludes \<open>EvRst\<close>; it only makes the function
      total, exactly as in the escalation action map.\<close>

fun ct_event_to_tcp :: "ct_event \<Rightarrow> tcp_event" where
  "ct_event_to_tcp CT_SYN    = EvSyn"
| "ct_event_to_tcp CT_SYNACK = EvSynAck"
| "ct_event_to_tcp CT_ACK    = EvAck"
| "ct_event_to_tcp CT_FIN    = EvFin"

definition ct_transition :: "ct_entry \<Rightarrow> ct_event \<Rightarrow> ct_entry option" where
  "ct_transition p e =
     (if p \<in> ct_states
      then map_option tcp_to_ct (tcp_transition (ct_to_tcp p) (ct_event_to_tcp e))
      else None)"

lemma ct_event_roundtrip:
  "e \<in> tracked_events \<Longrightarrow> ct_event_to_tcp (tcp_to_ct_event e) = e"
  by (auto simp: tracked_events_def)

section \<open>Discharging the Instance with the Generic Methods\<close>

text \<open>
  The helper lemmas mirror, point for point, those of the regulatory
  development: finiteness in the simplifier's normal form, terminal
  absorption, closure, domain, the naturality of the representation map on
  the tracked subset, and the terminal/well-definedness facts of the map.
  They are declared into the discharge collections, after which the machine
  and preservation instances close by one method invocation each.
\<close>

lemma ct_states_finite: "finite ct_states"
  by (auto simp: ct_states_def finite_tcp_state_UNIV intro: finite_imageI)

lemma ct_terminal_subset: "ct_terminal \<subseteq> ct_states"
  unfolding ct_terminal_def ct_states_def by blast

lemma ct_closed_absorbing:
  "\<lbrakk> p \<in> ct_terminal; e \<in> ct_events \<rbrakk> \<Longrightarrow> ct_transition p e = None"
  by (auto simp: ct_terminal_def ct_transition_def ct_to_tcp_to_ct_id closed_terminal)

lemma ct_transition_closed:
  "\<lbrakk> p \<in> ct_states; e \<in> ct_events; ct_transition p e = Some p' \<rbrakk> \<Longrightarrow> p' \<in> ct_states"
  unfolding ct_transition_def ct_states_def
  by (auto split: if_splits option.splits)

lemma ct_transition_outside_states:
  "p \<notin> ct_states \<Longrightarrow> ct_transition p e = None"
  by (simp add: ct_transition_def)

lemma tcp_to_ct_in_states: "tcp_to_ct s \<in> ct_states"
  by (simp add: ct_states_def)

lemma tcp_to_ct_terminal:
  "s \<in> tcp_terminal \<Longrightarrow> tcp_to_ct s \<in> ct_terminal"
  by (auto simp: tcp_terminal_def ct_terminal_def)

lemma tcp_to_ct_naturality_some:
  "\<lbrakk> s \<in> tcp_states; e \<in> tracked_events; tcp_transition s e = Some s' \<rbrakk>
   \<Longrightarrow> ct_transition (tcp_to_ct s) (tcp_to_ct_event e) = Some (tcp_to_ct s')"
  by (simp add: ct_transition_def tcp_to_ct_in_states ct_to_tcp_to_ct_id
                ct_event_roundtrip
           del: ct_to_tcp.simps tcp_to_ct.simps)

lemma tcp_to_ct_naturality_none:
  "\<lbrakk> s \<in> tcp_states; e \<in> tracked_events; tcp_transition s e = None \<rbrakk>
   \<Longrightarrow> ct_transition (tcp_to_ct s) (tcp_to_ct_event e) = None"
  by (simp add: ct_transition_def tcp_to_ct_in_states ct_to_tcp_to_ct_id
                ct_event_roundtrip
           del: ct_to_tcp.simps tcp_to_ct.simps)

lemmas [discharge_simps] =
  tcp_states_UNIV finite_tcp_state_UNIV
  tcp_events_def tracked_events_def ct_events_def
  tcp_terminal_def closed_terminal
  ct_states_finite ct_terminal_subset
  ct_closed_absorbing ct_transition_outside_states
  tcp_to_ct_naturality_some tcp_to_ct_naturality_none
  tcp_to_ct_terminal tcp_to_ct_in_states

lemmas [discharge_intros] =
  ct_transition_closed

lemmas [discharge_dels] =
  tcp_to_ct.simps ct_to_tcp.simps

text \<open>The two state machines and the preservation morphism, each discharged
  by the corresponding generic method.  No obligation is weakened: the
  statements are the full locale predicates.\<close>

theorem tcp_state_machine:
  "state_machine tcp_states tcp_events tcp_transition tcp_terminal"
  by discharge_state_machine

theorem conntrack_state_machine:
  "state_machine ct_states ct_events ct_transition ct_terminal"
  by discharge_state_machine

theorem tcp_conntrack_preservation:
  "state_preservation tcp_states tracked_events tcp_transition tcp_terminal
                      ct_states ct_events ct_transition ct_terminal
                      tcp_to_ct tcp_to_ct_event"
  by discharge_preservation

text \<open>Registered form of the morphism, giving access to the locale's
  sequential payload: every tracked packet sequence accepted by the endpoint
  is mirrored, packet for packet, by the tracker, ending in the
  corresponding tracker entry.\<close>

interpretation tcp_ct:
  state_preservation tcp_states tracked_events tcp_transition tcp_terminal
                     ct_states ct_events ct_transition ct_terminal
                     tcp_to_ct tcp_to_ct_event
  by (rule tcp_conntrack_preservation)

corollary tracked_sequence_mirrored:
  assumes "s \<in> tcp_states"
    and "\<forall>e \<in> set es. e \<in> tracked_events"
    and "tcp_ct.source.apply_actions s es = Some s'"
  shows "tcp_ct.target.apply_actions (tcp_to_ct s) (map tcp_to_ct_event es)
         = Some (tcp_to_ct s')"
  using assms by (rule tcp_ct.sequential_preservation)

text \<open>Non-vacuity witnesses: the three-way handshake is accepted by the
  endpoint machine, and its tracked image steps the tracker entry from the
  fresh entry to the established entry.\<close>

lemma three_way_handshake_endpoint:
  "tcp_transition LISTEN EvSyn = Some SYN_RCVD"
  "tcp_transition SYN_RCVD EvAck = Some ESTABLISHED"
  by simp_all

lemma three_way_handshake_tracked:
  "ct_transition (tcp_to_ct LISTEN) CT_SYN = Some (tcp_to_ct SYN_RCVD)"
  "ct_transition (tcp_to_ct SYN_RCVD) CT_ACK = Some (tcp_to_ct ESTABLISHED)"
  by (simp_all add: ct_transition_def tcp_to_ct_in_states ct_to_tcp_to_ct_id
                del: ct_to_tcp.simps tcp_to_ct.simps)

end
