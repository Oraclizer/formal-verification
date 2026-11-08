val _ = use (case OS.Process.getEnv "OIP_WIRE_RESPONSE_MODEL" of SOME path => path | NONE => raise Fail "Pinned full model path required");
fun full_int text = case IntInf.fromString text of SOME value => value | NONE => raise Fail "Invalid full ABI integer";
fun full_ints "" = [] | full_ints text = map full_int (String.fields (fn c => c = #",") text);
fun full_size value = if value < 0 orelse value > 1000000 then raise Fail "Invalid full ABI length" else IntInf.toInt value;
fun full_take 0 values = ([],values)
  | full_take count (value::values) = let val (taken,rest)=full_take (count-1) values in (value::taken,rest) end
  | full_take _ [] = raise Fail "Truncated full ABI field";
fun full_rows text = let
  fun rows 0 values = ([],values)
    | rows count (size::values) = let val (row,rest)=full_take (full_size size) values;
                                     val (tail,final)=rows (count-1) rest in (row::tail,final) end
    | rows _ [] = raise Fail "Truncated full ABI matrix";
  val values=full_ints text;
  val (result,rest)=case values of count::tail => rows (full_size count) tail | [] => raise Fail "Missing matrix count";
in if null rest then result else raise Fail "Trailing matrix tokens" end;
fun full_bool "0" = false | full_bool "1" = true | full_bool _ = raise Fail "Invalid full ABI bool";
fun full_clean text = String.implode (List.filter (fn c => c <> #"\r" andalso c <> #"\n") (String.explode text));
fun full_matrix rows = String.concatWith "," (map IntInf.toString
  (IntInf.fromInt (List.length rows)::List.concat (map (fn row => IntInf.fromInt (List.length row)::row) rows)));
fun full_emit id command status rows =
  (TextIO.output (TextIO.stdOut,String.concatWith "\t" ["OIP-FULL",id,command,IntInf.toString status,full_matrix rows]^"\n");TextIO.flushOut TextIO.stdOut);
fun full_sender command context mode reply present retained original hashes signs verifies =
  let val apply = case command of
      "Q"=>OIP_Wire_Response_Boundary.code_response_egress_queries_flat
    | "q"=>OIP_Wire_Response_Boundary.code_response_encode_boundary_queries_flat
    | "S"=>OIP_Wire_Response_Boundary.code_response_egress_flat_oracle
    | "B"=>OIP_Wire_Response_Boundary.code_response_encode_boundary_flat_oracle
    | "P"=>OIP_Wire_Response_Boundary.code_response_egress_prefix_flat
    | "p"=>OIP_Wire_Response_Boundary.code_response_encode_boundary_prefix_flat
    | _=>raise Fail "Unknown full sender command"
  in apply (full_rows context) (full_int mode) (full_ints reply) (full_bool present) (full_ints retained)
      (full_ints original) (full_rows hashes) (full_rows signs) (full_rows verifies) end;
fun full_one line = case String.fields (fn c => c = #"\t") (full_clean line) of
  [command,id,context,mode,reply,present,retained,original,hashes,signs,verifies] =>
    let val (status,rows)=full_sender command context mode reply present retained original hashes signs verifies
    in full_emit id command status rows end
| ["V",id,context,expected,network,verifies] =>
    let val (status,rows)=OIP_Wire_Response_Boundary.code_response_admit_queries_flat
          (full_rows context) (full_ints expected) (full_ints network) (full_rows verifies)
    in full_emit id "V" status rows end
| ["C",id,context,expected,network,verifies] =>
    let val (status,result)=OIP_Wire_Response_Boundary.code_response_admit_flat_oracle
          (full_rows context) (full_ints expected) (full_ints network) (full_rows verifies)
    in full_emit id "C" status [result] end
| ["A",id,context,mode,reply,present,retained,original,hashes,signs,verifies,client,clientverifies] =>
    let val (status,(rows,(clientstatus,result)))=OIP_Wire_Response_Boundary.code_response_egress_and_admit_flat_oracle
          (full_rows context) (full_int mode) (full_ints reply) (full_bool present) (full_ints retained)
          (full_ints original) (full_rows hashes) (full_rows signs) (full_rows verifies) (full_rows client) (full_rows clientverifies)
    in full_emit id "A" status ([clientstatus]::result::rows) end
| _=>raise Fail "Wrong full ABI command field count";
fun full_loop () = case TextIO.inputLine TextIO.stdIn of NONE=>() | SOME line=>(full_one line;full_loop ());
fun full_identity_text bytes = String.implode (map (fn value =>
  if value < 0 orelse value > 127 then raise Fail "Non-ASCII full identity" else Char.chr (IntInf.toInt value)) bytes);
val _ = let val identity=map full_identity_text (OIP_Wire_Response_Boundary.code_response_full_model_identity ());
            val _ = if List.length identity=6 then () else raise Fail "Full model identity must have6fields";
        in TextIO.output (TextIO.stdOut,String.concatWith "\t" ("OIP-RESPONSE-FULL-MODEL"::identity)^"\n");
           TextIO.flushOut TextIO.stdOut;full_loop () end;
