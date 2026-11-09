val _ = use (valOf (OS.Process.getEnv "OIP_SYNC_SUPPLIER_MODEL"));
val _ = use (valOf (OS.Process.getEnv "OIP_SYNC_SUPPLIER_INPUTS"));
structure Model = OIP_Sync_Supplier_ABI;

fun hex_byte byte =
  let
    val n = IntInf.toInt byte;
    val digits = "0123456789abcdef";
  in
    if n < 0 orelse n >= 256 then raise Fail "Model emitted a non-octet"
    else String.implode [String.sub (digits, n div 16), String.sub (digits, n mod 16)]
  end;

fun line fields = print (String.concatWith "\t" fields ^ "\n");

fun assembly (name, token, votes) =
  case Model.supplier_abi_aggregate token votes of
    NONE => raise Fail ("Invalid assembly input: " ^ name)
  | SOME NONE => line ["assemble", name, "reject", "-"]
  | SOME (SOME proof) => line ["assemble", name, "assembled", String.concat (map hex_byte proof)];

fun old_append (name, token, prefix, candidate) =
  case Model.supplier_abi_old_append token prefix candidate of
    SOME 0 => line ["old-append", name, "append", "-"]
  | SOME 1 => line ["old-append", name, "same-current", "-"]
  | SOME 2 => line ["old-append", name, "reject", "-"]
  | _ => raise Fail ("Invalid admitted-prefix input or result: " ^ name);

val _ = List.app assembly supplier_assembly_cases;
val _ = List.app old_append supplier_append_cases;
