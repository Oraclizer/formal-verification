val _ = use (case OS.Process.getEnv "OIP_WIRE_MODEL" of
  SOME path => path | NONE => raise Fail "OIP_WIRE_MODEL must name the pinned model");
fun mirror_integer text = case IntInf.fromString text of SOME value => value | NONE => raise Fail "Invalid wire input integer";
fun mirror_integers "" = []
  | mirror_integers text = map mirror_integer (String.fields (fn c => c = #",") text);
fun mirror_bool "0" = false | mirror_bool "1" = true | mirror_bool _ = raise Fail "Invalid wire input boolean";
fun mirror_clean line = String.implode (List.filter (fn c => c <> #"\r" andalso c <> #"\n") (String.explode line));
fun mirror_csv values = String.concatWith "," (map IntInf.toString values);
fun mirror_one line = case String.fields (fn c => c = #"\t") (mirror_clean line) of
  [ident,packet,boundary,version,families,atomicities,schemes,critical,signature_valid,attestation,prior_present,prior] =>
    let val (status,(present,(binding,(summary_present,(typed,(core,(preimage,key))))))) =
          OIP_Wire_Oracle_V061.sync_v061_nested_transport_flat
            (mirror_integers packet) (mirror_integers boundary) (mirror_integer version)
            (mirror_integers families) (mirror_integers atomicities) (mirror_integers schemes)
            (mirror_bool critical) (mirror_bool signature_valid) (mirror_bool attestation)
            (mirror_bool prior_present) (mirror_integers prior);
        val fields = ["OIP-MIRROR",ident,IntInf.toString status,if present then "1" else "0",mirror_csv binding,
                      if summary_present then "1" else "0",mirror_csv typed,mirror_csv core,mirror_csv preimage,mirror_csv key];
    in TextIO.output (TextIO.stdOut,String.concatWith "\t" fields ^ "\n");TextIO.flushOut TextIO.stdOut end
| _ => raise Fail "Wrong typed wire input field count";
fun mirror_loop () = case TextIO.inputLine TextIO.stdIn of NONE => () | SOME line => (mirror_one line;mirror_loop ());
fun mirror_identity_text bytes = String.implode (map (fn byte =>
  if byte < 0 orelse byte > 127 then raise Fail "Non-ASCII typed model identity" else Char.chr (IntInf.toInt byte)) bytes);
val _ = let val fields = map mirror_identity_text (OIP_Wire_Oracle_V061.sync_v061_typed_model_identity ());
            val _ = if List.length fields = 6 then () else raise Fail "Wrong typed model identity shape";
        in TextIO.output (TextIO.stdOut,String.concatWith "\t" ("OIP-MODEL"::fields) ^ "\n");
           TextIO.flushOut TextIO.stdOut;mirror_loop () end;
