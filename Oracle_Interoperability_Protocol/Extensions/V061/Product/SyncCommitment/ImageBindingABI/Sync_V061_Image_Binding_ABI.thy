theory Sync_V061_Image_Binding_ABI
  imports "OIP_Sync_V061_Image_Link.Sync_V061_Image_Link"
    "OIP_Message_Code.Wire_Code_Oracle_Codegen"
begin

type_synonym sync_binding_map = "(authenticated_message_id \<times> wire_bytes) list"
type_synonym sync_binding_observation = "nat list \<times> wire_bytes list"

definition sync_drop_exact_binding :: "authenticated_message_id \<Rightarrow> sync_binding_map \<Rightarrow> sync_binding_map" where
  "sync_drop_exact_binding removed_key bindings = filter (\<lambda>binding. fst binding \<noteq> removed_key) bindings"

lemma sync_drop_exact_binding_lookup_none:
  "map_of (sync_drop_exact_binding removed_key bindings) removed_key = None"
  by (induction bindings) (auto simp: sync_drop_exact_binding_def split: prod.splits if_splits)

lemma sync_drop_exact_binding_other_lookup:
  assumes "other_key \<noteq> removed_key"
  shows "map_of (sync_drop_exact_binding removed_key bindings) other_key = map_of bindings other_key"
  using assms by (induction bindings) (auto simp: sync_drop_exact_binding_def split: prod.splits if_splits)

lemma sync_drop_exact_binding_invalidates_retained_image:
  assumes stored: "(chosen_call,raw,outcome) \<in> set (sync_image_calls img_view)"
    and decoded: "sync_decode_core raw = Some core"
  shows "\<not> sync_image_valid (img_view\<lparr>sync_image_bindings :=
     sync_drop_exact_binding (code_transport_key core) (sync_image_bindings img_view)\<rparr>)"
proof (rule sync_image_lost_transport_invalidates_the_image[where core=core and img_call_key=chosen_call and raw=raw and outcome=outcome])
  show "(chosen_call,raw,outcome) \<in> set (sync_image_calls (img_view\<lparr>sync_image_bindings :=
     sync_drop_exact_binding (code_transport_key core) (sync_image_bindings img_view)\<rparr>))" using stored by simp
  show "sync_decode_core raw = Some core" by (rule decoded)
  show "map_of (sync_image_bindings (img_view\<lparr>sync_image_bindings :=
      sync_drop_exact_binding (code_transport_key core) (sync_image_bindings img_view)\<rparr>))
        (code_transport_key core) \<noteq> Some raw"
    by (simp add: sync_drop_exact_binding_lookup_none)
qed

definition sync_binding_number_fields where
  "sync_binding_number_fields transport_key =
    (case transport_key of (key_deployment,key_source,key_principal,_) \<Rightarrow> [key_deployment,key_source,key_principal])"

definition sync_binding_observe :: "client_call_id \<Rightarrow> wire_core \<Rightarrow> wire_bytes \<Rightarrow> sync_binding_map
    \<Rightarrow> sync_binding_observation" where
  "sync_binding_observe chosen_call core raw bindings =
    (let transport_key = code_transport_key core;
         exact_matches = (map_of bindings transport_key = Some raw)
     in ([if exact_matches then 1 else 0,length bindings,fst chosen_call,snd chosen_call] @
         sync_binding_number_fields transport_key @ concat (map (\<lambda>binding. sync_binding_number_fields (fst binding)) bindings),
         [wire_uuid core,encode_wire_core core] @ concat (map (\<lambda>((_,_,_,uuid),exact). [uuid,exact]) bindings)))"

definition sync_binding_compare where
  "sync_binding_compare chosen_call stored_cores bindings =
    Option.bind (map_of stored_cores chosen_call) (\<lambda>raw.
      Option.bind (sync_decode_core raw) (\<lambda>core.
        Option.bind (sync_read_operands core) (\<lambda>request.
          if sync_call request = chosen_call then
            Some (sync_binding_observe chosen_call core raw bindings,
              sync_binding_observe chosen_call core raw (sync_drop_exact_binding (code_transport_key core) bindings))
          else None)))"

definition sync_binding_integer_compare where
  "sync_binding_integer_compare input_id input_rows input_bindings =
    (let n = nat_of_integer; ns = map n; call_key = (\<lambda>(namespace,sequence). (n namespace,n sequence));
         rows = map (\<lambda>(stored_id,raw). (call_key stored_id,ns raw)) input_rows;
         bindings = map (\<lambda>((key_deployment,key_source,key_principal,key_uuid),raw).
           ((n key_deployment,n key_source,n key_principal,ns key_uuid),ns raw)) input_bindings;
         output = (\<lambda>(words,blobs). (map integer_of_nat words,map (map integer_of_nat) blobs))
     in map_option (\<lambda>(prior_image,removed_image). (output prior_image,output removed_image))
       (sync_binding_compare (call_key input_id) rows bindings))"

ML_val \<open>
  if null (Thm_Deps.all_oracles @{thms sync_drop_exact_binding_lookup_none
    sync_drop_exact_binding_other_lookup sync_drop_exact_binding_invalidates_retained_image})
  then () else error "Unexpected oracle in the exact transport binding removal ABI"
\<close>

export_code sync_binding_integer_compare
  in SML module_name OIP_Sync_Image_Binding_ABI file_prefix "oip_sync_image_binding_abi"

end
