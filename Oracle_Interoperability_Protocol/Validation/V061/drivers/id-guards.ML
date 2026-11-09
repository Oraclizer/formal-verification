val _ = use (valOf (OS.Process.getEnv "OIP_SYNC_ID_GUARD_MODEL"));
val _ = use (valOf (OS.Process.getEnv "OIP_SYNC_ID_GUARD_INPUTS"));
structure Model = OIP_Sync_ID_Guard_ABI;

fun observe (name, metadata, flags) =
  case Model.sync_id_guard_after_admission id_guard_packet id_guard_original_core metadata flags of
    SOME (fields as [_,_,_,_,_,_]) =>
      print (String.concatWith "\t" (name :: map IntInf.toString fields) ^ "\n")
  | _ => raise Fail ("Unusable ID guard input: " ^ name);

val _ = List.app observe id_guard_cases;
