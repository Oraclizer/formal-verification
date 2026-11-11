theory Pending_Lock_Inputs
  imports Pending_Lock_Seeds
begin

definition pl_case_pending_timeout :: "pl_case" where
  "pl_case_pending_timeout = \<lparr>plcase_id = 0,plcase_binding = \<lparr>pl_origin = (0,17),pl_asset = 17,pl_owner = 7,pl_destination = 2,pl_recipient = 3,pl_amount = 5\<rparr>,plcase_initial = 10,plcase_epoch = 9,plcase_lease = 5,
    plcase_setup = [],plcase_command = PL_Time 10,plcase_actor = 7,plcase_session = 1,plcase_credential = None\<rparr>"

definition pl_case_pending_cancel :: "pl_case" where
  "pl_case_pending_cancel = \<lparr>plcase_id = 1,plcase_binding = \<lparr>pl_origin = (0,17),pl_asset = 17,pl_owner = 7,pl_destination = 2,pl_recipient = 3,pl_amount = 5\<rparr>,plcase_initial = 10,plcase_epoch = 9,plcase_lease = 5,
    plcase_setup = [],plcase_command = PL_Cancel 0,plcase_actor = 7,plcase_session = 1,plcase_credential = Some (pl_seed_credential (\<lparr>pl_origin = (0,17),pl_asset = 17,pl_owner = 7,pl_destination = 2,pl_recipient = 3,pl_amount = 5\<rparr>) 7 0 9)\<rparr>"

definition pl_case_pending_fence :: "pl_case" where
  "pl_case_pending_fence = \<lparr>plcase_id = 2,plcase_binding = \<lparr>pl_origin = (0,17),pl_asset = 17,pl_owner = 7,pl_destination = 2,pl_recipient = 3,pl_amount = 5\<rparr>,plcase_initial = 10,plcase_epoch = 9,plcase_lease = 5,
    plcase_setup = [],plcase_command = PL_Fence 0,plcase_actor = 7,plcase_session = 1,plcase_credential = Some (pl_seed_credential (\<lparr>pl_origin = (0,17),pl_asset = 17,pl_owner = 7,pl_destination = 2,pl_recipient = 3,pl_amount = 5\<rparr>) 7 0 9)\<rparr>"

definition pl_case_pending_preempt :: "pl_case" where
  "pl_case_pending_preempt = \<lparr>plcase_id = 3,plcase_binding = \<lparr>pl_origin = (0,17),pl_asset = 17,pl_owner = 7,pl_destination = 2,pl_recipient = 3,pl_amount = 5\<rparr>,plcase_initial = 10,plcase_epoch = 9,plcase_lease = 5,
    plcase_setup = [PL_Setup_Time 10],plcase_command = PL_Preempt 5,plcase_actor = 7,plcase_session = 1,plcase_credential = None\<rparr>"

definition pl_case_reconcile_confirmed_not_credited :: "pl_case" where
  "pl_case_reconcile_confirmed_not_credited = \<lparr>plcase_id = 4,plcase_binding = \<lparr>pl_origin = (0,17),pl_asset = 17,pl_owner = 7,pl_destination = 2,pl_recipient = 3,pl_amount = 5\<rparr>,plcase_initial = 10,plcase_epoch = 9,plcase_lease = 5,
    plcase_setup = [PL_Setup_Record 0 PL_Confirmed],plcase_command = PL_Reconcile 0 0,plcase_actor = 7,plcase_session = 1,plcase_credential = Some (pl_seed_credential (\<lparr>pl_origin = (0,17),pl_asset = 17,pl_owner = 7,pl_destination = 2,pl_recipient = 3,pl_amount = 5\<rparr>) 7 0 9)\<rparr>"

definition pl_case_reconcile_exact_credit :: "pl_case" where
  "pl_case_reconcile_exact_credit = \<lparr>plcase_id = 5,plcase_binding = \<lparr>pl_origin = (0,17),pl_asset = 17,pl_owner = 7,pl_destination = 2,pl_recipient = 3,pl_amount = 5\<rparr>,plcase_initial = 10,plcase_epoch = 9,plcase_lease = 5,
    plcase_setup = [PL_Setup_Record 0 PL_Confirmed,PL_Setup_Credit 0],plcase_command = PL_Reconcile 0 0,plcase_actor = 7,plcase_session = 1,plcase_credential = Some (pl_seed_credential (\<lparr>pl_origin = (0,17),pl_asset = 17,pl_owner = 7,pl_destination = 2,pl_recipient = 3,pl_amount = 5\<rparr>) 7 0 9)\<rparr>"

definition pl_case_reconcile_unrecorded_reference :: "pl_case" where
  "pl_case_reconcile_unrecorded_reference = \<lparr>plcase_id = 6,plcase_binding = \<lparr>pl_origin = (0,17),pl_asset = 17,pl_owner = 7,pl_destination = 2,pl_recipient = 3,pl_amount = 5\<rparr>,plcase_initial = 10,plcase_epoch = 9,plcase_lease = 5,
    plcase_setup = [PL_Setup_Record 0 PL_Confirmed,PL_Setup_Credit 0],plcase_command = PL_Reconcile 0 1,plcase_actor = 7,plcase_session = 1,plcase_credential = Some (pl_seed_credential (\<lparr>pl_origin = (0,17),pl_asset = 17,pl_owner = 7,pl_destination = 2,pl_recipient = 3,pl_amount = 5\<rparr>) 7 0 9)\<rparr>"

definition pl_case_reconcile_refreshed_exact_reference :: "pl_case" where
  "pl_case_reconcile_refreshed_exact_reference = \<lparr>plcase_id = 7,plcase_binding = \<lparr>pl_origin = (0,17),pl_asset = 17,pl_owner = 7,pl_destination = 2,pl_recipient = 3,pl_amount = 5\<rparr>,plcase_initial = 10,plcase_epoch = 9,plcase_lease = 5,
    plcase_setup = [PL_Setup_Record 0 PL_Confirmed,PL_Setup_Credit 0,PL_Setup_Record 1 PL_Confirmed],plcase_command = PL_Reconcile 0 1,plcase_actor = 7,plcase_session = 1,plcase_credential = Some (pl_seed_credential (\<lparr>pl_origin = (0,17),pl_asset = 17,pl_owner = 7,pl_destination = 2,pl_recipient = 3,pl_amount = 5\<rparr>) 7 0 9)\<rparr>"

definition pl_case_reconcile_expired_credit :: "pl_case" where
  "pl_case_reconcile_expired_credit = \<lparr>plcase_id = 8,plcase_binding = \<lparr>pl_origin = (0,17),pl_asset = 17,pl_owner = 7,pl_destination = 2,pl_recipient = 3,pl_amount = 5\<rparr>,plcase_initial = 10,plcase_epoch = 9,plcase_lease = 5,
    plcase_setup = [PL_Setup_Record 0 PL_Confirmed,PL_Setup_Credit 0,PL_Setup_Time 10],plcase_command = PL_Reconcile 0 0,plcase_actor = 7,plcase_session = 1,plcase_credential = Some (pl_seed_credential (\<lparr>pl_origin = (0,17),pl_asset = 17,pl_owner = 7,pl_destination = 2,pl_recipient = 3,pl_amount = 5\<rparr>) 7 0 9)\<rparr>"

definition pl_case_reconcile_after_reassignment :: "pl_case" where
  "pl_case_reconcile_after_reassignment = \<lparr>plcase_id = 9,plcase_binding = \<lparr>pl_origin = (0,17),pl_asset = 17,pl_owner = 7,pl_destination = 2,pl_recipient = 3,pl_amount = 5\<rparr>,plcase_initial = 10,plcase_epoch = 9,plcase_lease = 5,
    plcase_setup = [PL_Setup_Record 0 PL_Confirmed,PL_Setup_Credit 0,PL_Setup_Time 10,PL_Setup_Preempt 8 2 5],plcase_command = PL_Reconcile 1 0,plcase_actor = 8,plcase_session = 2,plcase_credential = Some (pl_seed_credential (\<lparr>pl_origin = (0,17),pl_asset = 17,pl_owner = 7,pl_destination = 2,pl_recipient = 3,pl_amount = 5\<rparr>) 8 1 9)\<rparr>"

definition pl_case_reconcile_wrong_holder :: "pl_case" where
  "pl_case_reconcile_wrong_holder = \<lparr>plcase_id = 10,plcase_binding = \<lparr>pl_origin = (0,17),pl_asset = 17,pl_owner = 7,pl_destination = 2,pl_recipient = 3,pl_amount = 5\<rparr>,plcase_initial = 10,plcase_epoch = 9,plcase_lease = 5,
    plcase_setup = [PL_Setup_Record 0 PL_Confirmed,PL_Setup_Credit 0],plcase_command = PL_Reconcile 0 0,plcase_actor = 7,plcase_session = 1,plcase_credential = Some (pl_seed_credential (\<lparr>pl_origin = (0,17),pl_asset = 17,pl_owner = 7,pl_destination = 2,pl_recipient = 3,pl_amount = 5\<rparr>) 3 0 9)\<rparr>"

definition pl_case_reconcile_wrong_generation :: "pl_case" where
  "pl_case_reconcile_wrong_generation = \<lparr>plcase_id = 11,plcase_binding = \<lparr>pl_origin = (0,17),pl_asset = 17,pl_owner = 7,pl_destination = 2,pl_recipient = 3,pl_amount = 5\<rparr>,plcase_initial = 10,plcase_epoch = 9,plcase_lease = 5,
    plcase_setup = [PL_Setup_Record 0 PL_Confirmed,PL_Setup_Credit 0],plcase_command = PL_Reconcile 0 0,plcase_actor = 7,plcase_session = 1,plcase_credential = Some (pl_seed_credential (\<lparr>pl_origin = (0,17),pl_asset = 17,pl_owner = 7,pl_destination = 2,pl_recipient = 3,pl_amount = 5\<rparr>) 7 1 9)\<rparr>"

definition pl_case_reconcile_old_epoch :: "pl_case" where
  "pl_case_reconcile_old_epoch = \<lparr>plcase_id = 12,plcase_binding = \<lparr>pl_origin = (0,17),pl_asset = 17,pl_owner = 7,pl_destination = 2,pl_recipient = 3,pl_amount = 5\<rparr>,plcase_initial = 10,plcase_epoch = 9,plcase_lease = 5,
    plcase_setup = [PL_Setup_Record 0 PL_Confirmed,PL_Setup_Credit 0],plcase_command = PL_Reconcile 0 0,plcase_actor = 7,plcase_session = 1,plcase_credential = Some (pl_seed_credential (\<lparr>pl_origin = (0,17),pl_asset = 17,pl_owner = 7,pl_destination = 2,pl_recipient = 3,pl_amount = 5\<rparr>) 7 0 8)\<rparr>"

definition pl_cases :: "pl_case list" where
  "pl_cases = [pl_case_pending_timeout,
    pl_case_pending_cancel,
    pl_case_pending_fence,
    pl_case_pending_preempt,
    pl_case_reconcile_confirmed_not_credited,
    pl_case_reconcile_exact_credit,
    pl_case_reconcile_unrecorded_reference,
    pl_case_reconcile_refreshed_exact_reference,
    pl_case_reconcile_expired_credit,
    pl_case_reconcile_after_reassignment,
    pl_case_reconcile_wrong_holder,
    pl_case_reconcile_wrong_generation,
    pl_case_reconcile_old_epoch]"

end
