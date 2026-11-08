theory Wire_Code_Response_Boundary_Input
  imports "OIP_Message_Code.Wire_Code_Oracle_Codegen" "Wire_Response_Fixed_Fields"
begin

definition code_rbound_accepted_reply where
  "code_rbound_accepted_reply oip_binder_tag =
    (let oip_binder_variants = [Code_Source_Rejected_Reply,Code_Source_Busy_Reply,
       Code_Source_Reserved_Reply,Code_Source_Dispatched_Reply,Code_Source_Debited_Reply,
       Code_Source_Closed_Reply,Code_Source_Preempted_Reply,Code_Source_Time_Reply,
       Code_Source_Recorded_Reply,Code_Source_Credited_Reply,Code_Source_Reconciled_Reply,
       Code_Source_Refunded_Reply,Code_Source_Data_Reply,Code_Source_Evidence_Reply,
       Code_Source_Published_Reply]
     in if oip_binder_tag < length oip_binder_variants then Some (oip_binder_variants ! oip_binder_tag) else None)"

definition code_rbound_position :: "nat \<Rightarrow> nat \<Rightarrow> nat option option" where
  "code_rbound_position oip_binder_present oip_binder_position =
    (if oip_binder_present = 0 then (if oip_binder_position = 0 then Some None else None)
     else if oip_binder_present = 1 then Some (Some oip_binder_position) else None)"

definition code_rbound_outcome :: "nat list \<Rightarrow> code_source_outcome option" where
  "code_rbound_outcome oip_binder_values =
    (case oip_binder_values of [oip_binder_tag,oip_binder_first,oip_binder_present,oip_binder_position] \<Rightarrow>
       Option.bind (code_rbound_position oip_binder_present oip_binder_position) (\<lambda>oip_binder_commit.
         if oip_binder_tag = 0 then map_option (\<lambda>oip_binder_reply.
           \<lparr>source_outcome_reply = Code_Source_Accepted oip_binder_reply,source_outcome_commit = oip_binder_commit\<rparr>)
           (code_rbound_accepted_reply oip_binder_first)
         else if oip_binder_tag = 2 \<and> oip_binder_first \<in> {1,2} then Some
           \<lparr>source_outcome_reply = (if oip_binder_first = 1 then Code_Source_Duplicate_Confirmed
             else Code_Source_Duplicate_Reversed),source_outcome_commit = oip_binder_commit\<rparr>
         else None)
     | [oip_binder_tag,oip_binder_present,oip_binder_position] \<Rightarrow>
       Option.bind (code_rbound_position oip_binder_present oip_binder_position) (\<lambda>oip_binder_commit.
         map_option (\<lambda>oip_binder_reply. \<lparr>source_outcome_reply = oip_binder_reply,source_outcome_commit = oip_binder_commit\<rparr>)
           (if oip_binder_tag = 1 then Some Code_Source_Duplicate_Decision
            else if oip_binder_tag = 3 then Some Code_Source_Outcome_Rejected
            else if oip_binder_tag = 4 then Some Code_Source_Outcome_Busy
            else if oip_binder_tag = 5 then Some Code_Source_Outcome_Unavailable else None))
     | _ \<Rightarrow> None)"

definition code_rbound_collection :: "nat list \<Rightarrow> code_source_collection option" where
  "code_rbound_collection oip_binder_values =
    (case oip_binder_values of [] \<Rightarrow> None | oip_binder_tag # oip_binder_rest \<Rightarrow>
       if oip_binder_tag = 0 then map_option Code_Source_Collected (code_rbound_outcome oip_binder_rest)
       else if oip_binder_rest \<noteq> [] then None
       else if oip_binder_tag = 1 then Some Code_Source_Collection_Waiting
       else if oip_binder_tag = 2 then Some Code_Source_Collection_Rejected else None)"

definition code_rbound_legal :: "nat list \<Rightarrow> code_source_legal_reply option" where
  "code_rbound_legal oip_binder_values =
    (case oip_binder_values of [oip_binder_tag,oip_binder_value] \<Rightarrow>
       if oip_binder_tag = 0 then Some (Code_Source_Legal_Emitted oip_binder_value)
       else if oip_binder_tag = 1 then Some (Code_Source_Legal_Applied oip_binder_value)
       else if oip_binder_tag = 2 then
         (let oip_binder_refusals = [Invalid_Legal_Authority,Invalid_Legal_State,Invalid_Legal_Binding,
            Missing_Prior_Freeze,Missing_Prior_Seizure,Appeal_Still_Open,
            Appeal_Deadline_Mismatch,Missing_Confiscation_Destination,Conflicting_Legal_Order]
          in if oip_binder_value < length oip_binder_refusals then Some (Code_Source_Legal_Blocked (oip_binder_refusals ! oip_binder_value))
             else if oip_binder_value = 9 then Some Code_Source_Legal_Busy
             else if oip_binder_value = 10 then Some Code_Source_Legal_Unavailable else None)
       else None
     | _ \<Rightarrow> None)"

definition code_rbound_spend ::
  "nat list \<Rightarrow> (source_key option \<times> code_source_spend_reply) option" where
  "code_rbound_spend oip_binder_values =
    (case oip_binder_values of [oip_binder_tag,oip_binder_domain,oip_binder_event,oip_binder_position] \<Rightarrow>
       if oip_binder_tag = 0 then Some (Some (oip_binder_domain,oip_binder_event),Code_Source_Spend_Executed oip_binder_position) else None
     | [oip_binder_tag] \<Rightarrow>
       if oip_binder_tag = 1 then Some (None,Code_Source_Spend_Rejected)
       else if oip_binder_tag = 2 then Some (None,Code_Source_Spend_Busy)
       else if oip_binder_tag = 3 then Some (None,Code_Source_Spend_Unavailable) else None
     | _ \<Rightarrow> None)"

definition code_rbound_action ::
  "nat list \<Rightarrow> (source_key option \<times> code_source_action_reply) option" where
  "code_rbound_action oip_binder_values =
    (case oip_binder_values of [] \<Rightarrow> None | oip_binder_tag # oip_binder_rest \<Rightarrow>
       if oip_binder_tag = 0 then
         (case oip_binder_rest of [] \<Rightarrow> None | oip_binder_checked # oip_binder_tail \<Rightarrow>
           if oip_binder_checked = 0 then map_option (\<lambda>oip_binder_collection. (None,
               case oip_binder_collection of Code_Source_Collected oip_binder_outcome \<Rightarrow> Code_Source_Ordinary_Collected oip_binder_outcome
                | Code_Source_Collection_Waiting \<Rightarrow> Code_Source_Ordinary_Waiting
                | Code_Source_Collection_Rejected \<Rightarrow> Code_Source_Ordinary_Rejected))
             (code_rbound_collection oip_binder_tail)
           else if oip_binder_tail \<noteq> [] then None
           else if oip_binder_checked = 1 then Some (None,Code_Source_Ordinary_Busy)
           else if oip_binder_checked = 2 then Some (None,Code_Source_Ordinary_Unavailable)
           else if oip_binder_checked = 3 then Some (None,Code_Source_Ordinary_Rejected) else None)
       else if oip_binder_tag = 1 then map_option (\<lambda>oip_binder_reply. (None,Code_Source_Legal_Action oip_binder_reply)) (code_rbound_legal oip_binder_rest)
       else if oip_binder_tag = 2 then map_option (\<lambda>(oip_binder_root,oip_binder_reply). (oip_binder_root,Code_Source_Spend_Action oip_binder_reply)) (code_rbound_spend oip_binder_rest)
       else if oip_binder_tag = 3 \<and> oip_binder_rest = [] then Some (None,Code_Source_Other_Action) else None)"

definition code_rbound_receipt ::
  "nat list \<Rightarrow> (source_key option \<times> code_source_receipt) option" where
  "code_rbound_receipt oip_binder_values =
    (case oip_binder_values of [] \<Rightarrow> None | oip_binder_tag # oip_binder_rest \<Rightarrow>
       if oip_binder_tag = 0 then map_option (\<lambda>oip_binder_reply. (None,Code_Source_Ordinary_Receipt oip_binder_reply)) (code_rbound_collection oip_binder_rest)
       else if oip_binder_tag = 1 then map_option (\<lambda>oip_binder_reply. (None,Code_Source_Legal_Receipt oip_binder_reply)) (code_rbound_legal oip_binder_rest)
       else if oip_binder_tag = 2 then map_option (\<lambda>(oip_binder_root,oip_binder_reply). (oip_binder_root,Code_Source_Spend_Receipt oip_binder_reply)) (code_rbound_spend oip_binder_rest)
       else None)"

definition code_rbound_resolution :: "nat list \<Rightarrow> code_source_resolution option" where
  "code_rbound_resolution oip_binder_values =
    (case oip_binder_values of [] \<Rightarrow> None | oip_binder_tag # oip_binder_rest \<Rightarrow>
       if oip_binder_tag = 0 \<and> oip_binder_rest = [] then Some Code_Source_Resolution_Rejected
       else if oip_binder_tag = 2 \<and> oip_binder_rest = [] then Some Code_Source_Resolution_Unresolved
       else if oip_binder_tag = 1 then map_option (\<lambda>(oip_binder_root,oip_binder_receipt). Code_Source_Resolution_Published oip_binder_receipt)
         (code_rbound_receipt oip_binder_rest) else None)"

definition code_rbound_error :: "nat list \<Rightarrow> code_source_wire_error option" where
  "code_rbound_error oip_binder_values =
    (case oip_binder_values of [oip_binder_tag] \<Rightarrow>
       (let oip_binder_variants = [Code_Source_Wire_Validation Invalid_Wire_Format,
          Code_Source_Wire_Validation Unsupported_Wire_Version,
          Code_Source_Wire_Validation Invalid_Wire_Source,
          Code_Source_Wire_Validation Invalid_Wire_Signature,
          Code_Source_Wire_Validation Invalid_Wire_Threshold,
          Code_Source_Wire_Validation Wire_TTL_Expired,
          Code_Source_Wire_Validation Wire_TTL_Invalid,
          Code_Source_Wire_Validation Conflicting_Wire_Replay,
          Code_Source_Wire_Product_Rejected,Code_Source_Wire_Cancelled,
          Code_Source_Wire_Deadline,Code_Source_Wire_Response_Lost,Code_Source_Wire_Unresolved,
          Code_Source_Wire_Recovery Code_Source_Recovery_Endpoint_Rejected,
          Code_Source_Wire_Recovery Code_Source_Recovery_Endpoint_Unavailable,
          Code_Source_Wire_Recovery Code_Source_Recovery_Hold]
        in if oip_binder_tag < length oip_binder_variants then Some (oip_binder_variants ! oip_binder_tag) else None)
     | _ \<Rightarrow> None)"

end
