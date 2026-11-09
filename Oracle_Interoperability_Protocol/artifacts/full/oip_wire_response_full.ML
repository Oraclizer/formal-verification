structure OIP_Wire_Response_Boundary : sig
  type nat
  type num
  type wire_refusal
  type 'a wire_packet_ext
  type reference_response_kind
  type code_response_status
  type char
  type ('a, 'b) sum
  type response_v061_sender_stage
  type response_fixed_observation
  type response_v061_observation
  type 'a response_fixed_channel_ext
  type 'a response_fixed_client_boundary_ext
  val code_response_admit_flat_oracle :
    (IntInf.int list) list ->
      IntInf.int list ->
        IntInf.int list ->
          (IntInf.int list) list -> IntInf.int * IntInf.int list
  val code_response_full_model_identity : unit -> (IntInf.int list) list
  val code_response_admit_queries_flat :
    (IntInf.int list) list ->
      IntInf.int list ->
        IntInf.int list ->
          (IntInf.int list) list -> IntInf.int * (IntInf.int list) list
  val code_response_egress_flat_oracle :
    (IntInf.int list) list ->
      IntInf.int ->
        IntInf.int list ->
          bool ->
            IntInf.int list ->
              IntInf.int list ->
                (IntInf.int list) list ->
                  (IntInf.int list) list ->
                    (IntInf.int list) list ->
                      IntInf.int * (IntInf.int list) list
  val code_response_egress_prefix_flat :
    (IntInf.int list) list ->
      IntInf.int ->
        IntInf.int list ->
          bool ->
            IntInf.int list ->
              IntInf.int list ->
                (IntInf.int list) list ->
                  (IntInf.int list) list ->
                    (IntInf.int list) list ->
                      IntInf.int * (IntInf.int list) list
  val code_response_result_flat_oracle :
    IntInf.int ->
      IntInf.int list ->
        bool -> IntInf.int list -> bool * (IntInf.int * (bool * IntInf.int))
  val code_response_egress_queries_flat :
    (IntInf.int list) list ->
      IntInf.int ->
        IntInf.int list ->
          bool ->
            IntInf.int list ->
              IntInf.int list ->
                (IntInf.int list) list ->
                  (IntInf.int list) list ->
                    (IntInf.int list) list ->
                      IntInf.int * (IntInf.int list) list
  val code_response_encode_boundary_flat_oracle :
    (IntInf.int list) list ->
      IntInf.int ->
        IntInf.int list ->
          bool ->
            IntInf.int list ->
              IntInf.int list ->
                (IntInf.int list) list ->
                  (IntInf.int list) list ->
                    (IntInf.int list) list ->
                      IntInf.int * (IntInf.int list) list
  val code_response_encode_boundary_prefix_flat :
    (IntInf.int list) list ->
      IntInf.int ->
        IntInf.int list ->
          bool ->
            IntInf.int list ->
              IntInf.int list ->
                (IntInf.int list) list ->
                  (IntInf.int list) list ->
                    (IntInf.int list) list ->
                      IntInf.int * (IntInf.int list) list
  val code_response_egress_and_admit_flat_oracle :
    (IntInf.int list) list ->
      IntInf.int ->
        IntInf.int list ->
          bool ->
            IntInf.int list ->
              IntInf.int list ->
                (IntInf.int list) list ->
                  (IntInf.int list) list ->
                    (IntInf.int list) list ->
                      (IntInf.int list) list ->
                        (IntInf.int list) list ->
                          IntInf.int *
                            ((IntInf.int list) list *
                              (IntInf.int * IntInf.int list))
  val code_response_encode_boundary_queries_flat :
    (IntInf.int list) list ->
      IntInf.int ->
        IntInf.int list ->
          bool ->
            IntInf.int list ->
              IntInf.int list ->
                (IntInf.int list) list ->
                  (IntInf.int list) list ->
                    (IntInf.int list) list ->
                      IntInf.int * (IntInf.int list) list
  val code_response_binding_flat_oracle :
    IntInf.int ->
      IntInf.int list ->
        bool ->
          IntInf.int list ->
            IntInf.int list ->
              IntInf.int list ->
                bool *
                  (IntInf.int *
                    (IntInf.int *
                      (bool *
                        (IntInf.int *
                          (IntInf.int *
                            (IntInf.int list *
                              (IntInf.int list * IntInf.int list)))))))
  val code_response_uuid_preimage_flat_oracle :
    IntInf.int list -> IntInf.int list -> IntInf.int -> bool * IntInf.int list
end = struct

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_nat = {equal = equal_nata} : nat equal;

fun times_nata m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a dvd = {times_dvd : 'a times};
val times_dvd = #times_dvd : 'a dvd -> 'a times;

val times_nat = {times = times_nata} : nat times;

val dvd_nat = {times_dvd = times_nat} : nat dvd;

datatype num = One | Bit0 of num | Bit1 of num;

val one_nata : nat = Nat (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_nat = {one = one_nata} : nat one;

fun plus_nata m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_nat = {plus = plus_nata} : nat plus;

val zero_nata : nat = Nat (0 : IntInf.int);

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_nat = {zero = zero_nata} : nat zero;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a numeral =
  {one_numeral : 'a one, semigroup_add_numeral : 'a semigroup_add};
val one_numeral = #one_numeral : 'a numeral -> 'a one;
val semigroup_add_numeral = #semigroup_add_numeral :
  'a numeral -> 'a semigroup_add;

val semigroup_add_nat = {plus_semigroup_add = plus_nat} : nat semigroup_add;

val numeral_nat =
  {one_numeral = one_nat, semigroup_add_numeral = semigroup_add_nat} :
  nat numeral;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

val power_nat = {one_power = one_nat, times_power = times_nat} : nat power;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun max A_ a b = (if less_eq A_ a b then b else a);

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun minus_nata m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

type 'a minus = {minus : 'a -> 'a -> 'a};
val minus = #minus : 'a minus -> 'a -> 'a -> 'a;

val minus_nat = {minus = minus_nata} : nat minus;

fun apsnd f (x, y) = (x, f y);

fun divmod_integer k l =
  (if ((k : IntInf.int) = (0 : IntInf.int))
    then ((0 : IntInf.int), (0 : IntInf.int))
    else (if IntInf.< ((0 : IntInf.int), l)
           then (if IntInf.< ((0 : IntInf.int), k)
                  then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                  else let
                         val (r, s) =
                           IntInf.divMod (IntInf.abs k, IntInf.abs l);
                       in
                         (if ((s : IntInf.int) = (0 : IntInf.int))
                           then (IntInf.~ r, (0 : IntInf.int))
                           else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                  IntInf.- (l, s)))
                       end)
           else (if ((l : IntInf.int) = (0 : IntInf.int))
                  then ((0 : IntInf.int), k)
                  else apsnd IntInf.~
                         (if IntInf.< (k, (0 : IntInf.int))
                           then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                           else let
                                  val (r, s) =
                                    IntInf.divMod (IntInf.abs k, IntInf.abs l);
                                in
                                  (if ((s : IntInf.int) = (0 : IntInf.int))
                                    then (IntInf.~ r, (0 : IntInf.int))
                                    else (IntInf.- (IntInf.~
              r, (1 : IntInf.int)),
   IntInf.- (IntInf.~ l, s)))
                                end))));

fun fst (x1, x2) = x1;

fun divide_integer k l = fst (divmod_integer k l);

fun divide_nata m n =
  Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

type 'a divide = {divide : 'a -> 'a -> 'a};
val divide = #divide : 'a divide -> 'a -> 'a -> 'a;

val divide_nat = {divide = divide_nata} : nat divide;

fun snd (x1, x2) = x2;

fun modulo_integer k l = snd (divmod_integer k l);

fun modulo_nata m n =
  Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

type 'a modulo =
  {divide_modulo : 'a divide, dvd_modulo : 'a dvd, modulo : 'a -> 'a -> 'a};
val divide_modulo = #divide_modulo : 'a modulo -> 'a divide;
val dvd_modulo = #dvd_modulo : 'a modulo -> 'a dvd;
val modulo = #modulo : 'a modulo -> 'a -> 'a -> 'a;

val modulo_nat =
  {divide_modulo = divide_nat, dvd_modulo = dvd_nat, modulo = modulo_nata} :
  nat modulo;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};
val semigroup_add_cancel_semigroup_add = #semigroup_add_cancel_semigroup_add :
  'a cancel_semigroup_add -> 'a semigroup_add;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};
val semigroup_add_ab_semigroup_add = #semigroup_add_ab_semigroup_add :
  'a ab_semigroup_add -> 'a semigroup_add;

type 'a cancel_ab_semigroup_add =
  {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add,
    cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add,
    minus_cancel_ab_semigroup_add : 'a minus};
val ab_semigroup_add_cancel_ab_semigroup_add =
  #ab_semigroup_add_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a ab_semigroup_add;
val cancel_semigroup_add_cancel_ab_semigroup_add =
  #cancel_semigroup_add_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a cancel_semigroup_add;
val minus_cancel_ab_semigroup_add = #minus_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a minus;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add :
  'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add,
    monoid_add_comm_monoid_add : 'a monoid_add};
val ab_semigroup_add_comm_monoid_add = #ab_semigroup_add_comm_monoid_add :
  'a comm_monoid_add -> 'a ab_semigroup_add;
val monoid_add_comm_monoid_add = #monoid_add_comm_monoid_add :
  'a comm_monoid_add -> 'a monoid_add;

type 'a cancel_comm_monoid_add =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_ab_semigroup_add,
    comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add};
val cancel_ab_semigroup_add_cancel_comm_monoid_add =
  #cancel_ab_semigroup_add_cancel_comm_monoid_add :
  'a cancel_comm_monoid_add -> 'a cancel_ab_semigroup_add;
val comm_monoid_add_cancel_comm_monoid_add =
  #comm_monoid_add_cancel_comm_monoid_add :
  'a cancel_comm_monoid_add -> 'a comm_monoid_add;

type 'a mult_zero = {times_mult_zero : 'a times, zero_mult_zero : 'a zero};
val times_mult_zero = #times_mult_zero : 'a mult_zero -> 'a times;
val zero_mult_zero = #zero_mult_zero : 'a mult_zero -> 'a zero;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};
val times_semigroup_mult = #times_semigroup_mult :
  'a semigroup_mult -> 'a times;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add,
    semigroup_mult_semiring : 'a semigroup_mult};
val ab_semigroup_add_semiring = #ab_semigroup_add_semiring :
  'a semiring -> 'a ab_semigroup_add;
val semigroup_mult_semiring = #semigroup_mult_semiring :
  'a semiring -> 'a semigroup_mult;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add,
    mult_zero_semiring_0 : 'a mult_zero, semiring_semiring_0 : 'a semiring};
val comm_monoid_add_semiring_0 = #comm_monoid_add_semiring_0 :
  'a semiring_0 -> 'a comm_monoid_add;
val mult_zero_semiring_0 = #mult_zero_semiring_0 :
  'a semiring_0 -> 'a mult_zero;
val semiring_semiring_0 = #semiring_semiring_0 : 'a semiring_0 -> 'a semiring;

type 'a semiring_0_cancel =
  {cancel_comm_monoid_add_semiring_0_cancel : 'a cancel_comm_monoid_add,
    semiring_0_semiring_0_cancel : 'a semiring_0};
val cancel_comm_monoid_add_semiring_0_cancel =
  #cancel_comm_monoid_add_semiring_0_cancel :
  'a semiring_0_cancel -> 'a cancel_comm_monoid_add;
val semiring_0_semiring_0_cancel = #semiring_0_semiring_0_cancel :
  'a semiring_0_cancel -> 'a semiring_0;

type 'a ab_semigroup_mult =
  {semigroup_mult_ab_semigroup_mult : 'a semigroup_mult};
val semigroup_mult_ab_semigroup_mult = #semigroup_mult_ab_semigroup_mult :
  'a ab_semigroup_mult -> 'a semigroup_mult;

type 'a comm_semiring =
  {ab_semigroup_mult_comm_semiring : 'a ab_semigroup_mult,
    semiring_comm_semiring : 'a semiring};
val ab_semigroup_mult_comm_semiring = #ab_semigroup_mult_comm_semiring :
  'a comm_semiring -> 'a ab_semigroup_mult;
val semiring_comm_semiring = #semiring_comm_semiring :
  'a comm_semiring -> 'a semiring;

type 'a comm_semiring_0 =
  {comm_semiring_comm_semiring_0 : 'a comm_semiring,
    semiring_0_comm_semiring_0 : 'a semiring_0};
val comm_semiring_comm_semiring_0 = #comm_semiring_comm_semiring_0 :
  'a comm_semiring_0 -> 'a comm_semiring;
val semiring_0_comm_semiring_0 = #semiring_0_comm_semiring_0 :
  'a comm_semiring_0 -> 'a semiring_0;

type 'a comm_semiring_0_cancel =
  {comm_semiring_0_comm_semiring_0_cancel : 'a comm_semiring_0,
    semiring_0_cancel_comm_semiring_0_cancel : 'a semiring_0_cancel};
val comm_semiring_0_comm_semiring_0_cancel =
  #comm_semiring_0_comm_semiring_0_cancel :
  'a comm_semiring_0_cancel -> 'a comm_semiring_0;
val semiring_0_cancel_comm_semiring_0_cancel =
  #semiring_0_cancel_comm_semiring_0_cancel :
  'a comm_semiring_0_cancel -> 'a semiring_0_cancel;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult,
    power_monoid_mult : 'a power};
val semigroup_mult_monoid_mult = #semigroup_mult_monoid_mult :
  'a monoid_mult -> 'a semigroup_mult;
val power_monoid_mult = #power_monoid_mult : 'a monoid_mult -> 'a power;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult,
    numeral_semiring_numeral : 'a numeral,
    semiring_semiring_numeral : 'a semiring};
val monoid_mult_semiring_numeral = #monoid_mult_semiring_numeral :
  'a semiring_numeral -> 'a monoid_mult;
val numeral_semiring_numeral = #numeral_semiring_numeral :
  'a semiring_numeral -> 'a numeral;
val semiring_semiring_numeral = #semiring_semiring_numeral :
  'a semiring_numeral -> 'a semiring;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral,
    semiring_0_semiring_1 : 'a semiring_0,
    zero_neq_one_semiring_1 : 'a zero_neq_one};
val semiring_numeral_semiring_1 = #semiring_numeral_semiring_1 :
  'a semiring_1 -> 'a semiring_numeral;
val semiring_0_semiring_1 = #semiring_0_semiring_1 :
  'a semiring_1 -> 'a semiring_0;
val zero_neq_one_semiring_1 = #zero_neq_one_semiring_1 :
  'a semiring_1 -> 'a zero_neq_one;

type 'a semiring_1_cancel =
  {semiring_0_cancel_semiring_1_cancel : 'a semiring_0_cancel,
    semiring_1_semiring_1_cancel : 'a semiring_1};
val semiring_0_cancel_semiring_1_cancel = #semiring_0_cancel_semiring_1_cancel :
  'a semiring_1_cancel -> 'a semiring_0_cancel;
val semiring_1_semiring_1_cancel = #semiring_1_semiring_1_cancel :
  'a semiring_1_cancel -> 'a semiring_1;

type 'a comm_monoid_mult =
  {ab_semigroup_mult_comm_monoid_mult : 'a ab_semigroup_mult,
    monoid_mult_comm_monoid_mult : 'a monoid_mult,
    dvd_comm_monoid_mult : 'a dvd};
val ab_semigroup_mult_comm_monoid_mult = #ab_semigroup_mult_comm_monoid_mult :
  'a comm_monoid_mult -> 'a ab_semigroup_mult;
val monoid_mult_comm_monoid_mult = #monoid_mult_comm_monoid_mult :
  'a comm_monoid_mult -> 'a monoid_mult;
val dvd_comm_monoid_mult = #dvd_comm_monoid_mult :
  'a comm_monoid_mult -> 'a dvd;

type 'a comm_semiring_1 =
  {comm_monoid_mult_comm_semiring_1 : 'a comm_monoid_mult,
    comm_semiring_0_comm_semiring_1 : 'a comm_semiring_0,
    semiring_1_comm_semiring_1 : 'a semiring_1};
val comm_monoid_mult_comm_semiring_1 = #comm_monoid_mult_comm_semiring_1 :
  'a comm_semiring_1 -> 'a comm_monoid_mult;
val comm_semiring_0_comm_semiring_1 = #comm_semiring_0_comm_semiring_1 :
  'a comm_semiring_1 -> 'a comm_semiring_0;
val semiring_1_comm_semiring_1 = #semiring_1_comm_semiring_1 :
  'a comm_semiring_1 -> 'a semiring_1;

type 'a comm_semiring_1_cancel =
  {comm_semiring_0_cancel_comm_semiring_1_cancel : 'a comm_semiring_0_cancel,
    comm_semiring_1_comm_semiring_1_cancel : 'a comm_semiring_1,
    semiring_1_cancel_comm_semiring_1_cancel : 'a semiring_1_cancel};
val comm_semiring_0_cancel_comm_semiring_1_cancel =
  #comm_semiring_0_cancel_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a comm_semiring_0_cancel;
val comm_semiring_1_comm_semiring_1_cancel =
  #comm_semiring_1_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a comm_semiring_1;
val semiring_1_cancel_comm_semiring_1_cancel =
  #semiring_1_cancel_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a semiring_1_cancel;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

type 'a interval =
  {linorder_interval : 'a linorder,
    comm_semiring_1_cancel_interval : 'a comm_semiring_1_cancel};
val linorder_interval = #linorder_interval : 'a interval -> 'a linorder;
val comm_semiring_1_cancel_interval = #comm_semiring_1_cancel_interval :
  'a interval -> 'a comm_semiring_1_cancel;

val cancel_semigroup_add_nat =
  {semigroup_add_cancel_semigroup_add = semigroup_add_nat} :
  nat cancel_semigroup_add;

val ab_semigroup_add_nat = {semigroup_add_ab_semigroup_add = semigroup_add_nat}
  : nat ab_semigroup_add;

val cancel_ab_semigroup_add_nat =
  {ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_nat,
    cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_nat,
    minus_cancel_ab_semigroup_add = minus_nat}
  : nat cancel_ab_semigroup_add;

val monoid_add_nat =
  {semigroup_add_monoid_add = semigroup_add_nat, zero_monoid_add = zero_nat} :
  nat monoid_add;

val comm_monoid_add_nat =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_nat,
    monoid_add_comm_monoid_add = monoid_add_nat}
  : nat comm_monoid_add;

val cancel_comm_monoid_add_nat =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add = cancel_ab_semigroup_add_nat,
    comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_nat}
  : nat cancel_comm_monoid_add;

val mult_zero_nat = {times_mult_zero = times_nat, zero_mult_zero = zero_nat} :
  nat mult_zero;

val semigroup_mult_nat = {times_semigroup_mult = times_nat} :
  nat semigroup_mult;

val semiring_nat =
  {ab_semigroup_add_semiring = ab_semigroup_add_nat,
    semigroup_mult_semiring = semigroup_mult_nat}
  : nat semiring;

val semiring_0_nat =
  {comm_monoid_add_semiring_0 = comm_monoid_add_nat,
    mult_zero_semiring_0 = mult_zero_nat, semiring_semiring_0 = semiring_nat}
  : nat semiring_0;

val semiring_0_cancel_nat =
  {cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_nat,
    semiring_0_semiring_0_cancel = semiring_0_nat}
  : nat semiring_0_cancel;

val ab_semigroup_mult_nat =
  {semigroup_mult_ab_semigroup_mult = semigroup_mult_nat} :
  nat ab_semigroup_mult;

val comm_semiring_nat =
  {ab_semigroup_mult_comm_semiring = ab_semigroup_mult_nat,
    semiring_comm_semiring = semiring_nat}
  : nat comm_semiring;

val comm_semiring_0_nat =
  {comm_semiring_comm_semiring_0 = comm_semiring_nat,
    semiring_0_comm_semiring_0 = semiring_0_nat}
  : nat comm_semiring_0;

val comm_semiring_0_cancel_nat =
  {comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_nat,
    semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_nat}
  : nat comm_semiring_0_cancel;

val monoid_mult_nat =
  {semigroup_mult_monoid_mult = semigroup_mult_nat,
    power_monoid_mult = power_nat}
  : nat monoid_mult;

val semiring_numeral_nat =
  {monoid_mult_semiring_numeral = monoid_mult_nat,
    numeral_semiring_numeral = numeral_nat,
    semiring_semiring_numeral = semiring_nat}
  : nat semiring_numeral;

val zero_neq_one_nat =
  {one_zero_neq_one = one_nat, zero_zero_neq_one = zero_nat} : nat zero_neq_one;

val semiring_1_nat =
  {semiring_numeral_semiring_1 = semiring_numeral_nat,
    semiring_0_semiring_1 = semiring_0_nat,
    zero_neq_one_semiring_1 = zero_neq_one_nat}
  : nat semiring_1;

val semiring_1_cancel_nat =
  {semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_nat,
    semiring_1_semiring_1_cancel = semiring_1_nat}
  : nat semiring_1_cancel;

val comm_monoid_mult_nat =
  {ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_nat,
    monoid_mult_comm_monoid_mult = monoid_mult_nat,
    dvd_comm_monoid_mult = dvd_nat}
  : nat comm_monoid_mult;

val comm_semiring_1_nat =
  {comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_nat,
    comm_semiring_0_comm_semiring_1 = comm_semiring_0_nat,
    semiring_1_comm_semiring_1 = semiring_1_nat}
  : nat comm_semiring_1;

val comm_semiring_1_cancel_nat =
  {comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_nat,
    comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_nat,
    semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_nat}
  : nat comm_semiring_1_cancel;

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

val preorder_nat = {ord_preorder = ord_nat} : nat preorder;

val order_nat = {preorder_order = preorder_nat} : nat order;

val linorder_nat = {order_linorder = order_nat} : nat linorder;

val interval_nat =
  {linorder_interval = linorder_nat,
    comm_semiring_1_cancel_interval = comm_semiring_1_cancel_nat}
  : nat interval;

fun eq A_ a b = equal A_ a b;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

fun equal_optiona A_ NONE (SOME x2) = false
  | equal_optiona A_ (SOME x2) NONE = false
  | equal_optiona A_ (SOME x2) (SOME y2) = eq A_ x2 y2
  | equal_optiona A_ NONE NONE = true;

fun equal_option A_ = {equal = equal_optiona A_} : ('a option) equal;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

fun equal_unita u v = true;

val equal_unit = {equal = equal_unita} : unit equal;

val equal_integer = {equal = (fn a => fn b => ((a : IntInf.int) = b))} :
  IntInf.int equal;

val one_integera : IntInf.int = (1 : IntInf.int);

val one_integer = {one = one_integera} : IntInf.int one;

val zero_integer = {zero = (0 : IntInf.int)} : IntInf.int zero;

val times_integer = {times = (fn a => fn b => IntInf.* (a, b))} :
  IntInf.int times;

val power_integer = {one_power = one_integer, times_power = times_integer} :
  IntInf.int power;

val zero_neq_one_integer =
  {one_zero_neq_one = one_integer, zero_zero_neq_one = zero_integer} :
  IntInf.int zero_neq_one;

datatype wire_family = Wire_State_Sync | Wire_Regulatory | Wire_Lock |
  Wire_Query | Wire_Ack | Wire_Heartbeat | Wire_Governance;

fun equal_wire_familya Wire_Heartbeat Wire_Governance = false
  | equal_wire_familya Wire_Governance Wire_Heartbeat = false
  | equal_wire_familya Wire_Ack Wire_Governance = false
  | equal_wire_familya Wire_Governance Wire_Ack = false
  | equal_wire_familya Wire_Ack Wire_Heartbeat = false
  | equal_wire_familya Wire_Heartbeat Wire_Ack = false
  | equal_wire_familya Wire_Query Wire_Governance = false
  | equal_wire_familya Wire_Governance Wire_Query = false
  | equal_wire_familya Wire_Query Wire_Heartbeat = false
  | equal_wire_familya Wire_Heartbeat Wire_Query = false
  | equal_wire_familya Wire_Query Wire_Ack = false
  | equal_wire_familya Wire_Ack Wire_Query = false
  | equal_wire_familya Wire_Lock Wire_Governance = false
  | equal_wire_familya Wire_Governance Wire_Lock = false
  | equal_wire_familya Wire_Lock Wire_Heartbeat = false
  | equal_wire_familya Wire_Heartbeat Wire_Lock = false
  | equal_wire_familya Wire_Lock Wire_Ack = false
  | equal_wire_familya Wire_Ack Wire_Lock = false
  | equal_wire_familya Wire_Lock Wire_Query = false
  | equal_wire_familya Wire_Query Wire_Lock = false
  | equal_wire_familya Wire_Regulatory Wire_Governance = false
  | equal_wire_familya Wire_Governance Wire_Regulatory = false
  | equal_wire_familya Wire_Regulatory Wire_Heartbeat = false
  | equal_wire_familya Wire_Heartbeat Wire_Regulatory = false
  | equal_wire_familya Wire_Regulatory Wire_Ack = false
  | equal_wire_familya Wire_Ack Wire_Regulatory = false
  | equal_wire_familya Wire_Regulatory Wire_Query = false
  | equal_wire_familya Wire_Query Wire_Regulatory = false
  | equal_wire_familya Wire_Regulatory Wire_Lock = false
  | equal_wire_familya Wire_Lock Wire_Regulatory = false
  | equal_wire_familya Wire_State_Sync Wire_Governance = false
  | equal_wire_familya Wire_Governance Wire_State_Sync = false
  | equal_wire_familya Wire_State_Sync Wire_Heartbeat = false
  | equal_wire_familya Wire_Heartbeat Wire_State_Sync = false
  | equal_wire_familya Wire_State_Sync Wire_Ack = false
  | equal_wire_familya Wire_Ack Wire_State_Sync = false
  | equal_wire_familya Wire_State_Sync Wire_Query = false
  | equal_wire_familya Wire_Query Wire_State_Sync = false
  | equal_wire_familya Wire_State_Sync Wire_Lock = false
  | equal_wire_familya Wire_Lock Wire_State_Sync = false
  | equal_wire_familya Wire_State_Sync Wire_Regulatory = false
  | equal_wire_familya Wire_Regulatory Wire_State_Sync = false
  | equal_wire_familya Wire_Governance Wire_Governance = true
  | equal_wire_familya Wire_Heartbeat Wire_Heartbeat = true
  | equal_wire_familya Wire_Ack Wire_Ack = true
  | equal_wire_familya Wire_Query Wire_Query = true
  | equal_wire_familya Wire_Lock Wire_Lock = true
  | equal_wire_familya Wire_Regulatory Wire_Regulatory = true
  | equal_wire_familya Wire_State_Sync Wire_State_Sync = true;

val equal_wire_family = {equal = equal_wire_familya} : wire_family equal;

datatype wire_refusal = Invalid_Wire_Format | Unsupported_Wire_Version |
  Invalid_Wire_Source | Invalid_Wire_Signature | Invalid_Wire_Threshold |
  Wire_TTL_Expired | Wire_TTL_Invalid | Conflicting_Wire_Replay;

fun equal_wire_refusala Wire_TTL_Invalid Conflicting_Wire_Replay = false
  | equal_wire_refusala Conflicting_Wire_Replay Wire_TTL_Invalid = false
  | equal_wire_refusala Wire_TTL_Expired Conflicting_Wire_Replay = false
  | equal_wire_refusala Conflicting_Wire_Replay Wire_TTL_Expired = false
  | equal_wire_refusala Wire_TTL_Expired Wire_TTL_Invalid = false
  | equal_wire_refusala Wire_TTL_Invalid Wire_TTL_Expired = false
  | equal_wire_refusala Invalid_Wire_Threshold Conflicting_Wire_Replay = false
  | equal_wire_refusala Conflicting_Wire_Replay Invalid_Wire_Threshold = false
  | equal_wire_refusala Invalid_Wire_Threshold Wire_TTL_Invalid = false
  | equal_wire_refusala Wire_TTL_Invalid Invalid_Wire_Threshold = false
  | equal_wire_refusala Invalid_Wire_Threshold Wire_TTL_Expired = false
  | equal_wire_refusala Wire_TTL_Expired Invalid_Wire_Threshold = false
  | equal_wire_refusala Invalid_Wire_Signature Conflicting_Wire_Replay = false
  | equal_wire_refusala Conflicting_Wire_Replay Invalid_Wire_Signature = false
  | equal_wire_refusala Invalid_Wire_Signature Wire_TTL_Invalid = false
  | equal_wire_refusala Wire_TTL_Invalid Invalid_Wire_Signature = false
  | equal_wire_refusala Invalid_Wire_Signature Wire_TTL_Expired = false
  | equal_wire_refusala Wire_TTL_Expired Invalid_Wire_Signature = false
  | equal_wire_refusala Invalid_Wire_Signature Invalid_Wire_Threshold = false
  | equal_wire_refusala Invalid_Wire_Threshold Invalid_Wire_Signature = false
  | equal_wire_refusala Invalid_Wire_Source Conflicting_Wire_Replay = false
  | equal_wire_refusala Conflicting_Wire_Replay Invalid_Wire_Source = false
  | equal_wire_refusala Invalid_Wire_Source Wire_TTL_Invalid = false
  | equal_wire_refusala Wire_TTL_Invalid Invalid_Wire_Source = false
  | equal_wire_refusala Invalid_Wire_Source Wire_TTL_Expired = false
  | equal_wire_refusala Wire_TTL_Expired Invalid_Wire_Source = false
  | equal_wire_refusala Invalid_Wire_Source Invalid_Wire_Threshold = false
  | equal_wire_refusala Invalid_Wire_Threshold Invalid_Wire_Source = false
  | equal_wire_refusala Invalid_Wire_Source Invalid_Wire_Signature = false
  | equal_wire_refusala Invalid_Wire_Signature Invalid_Wire_Source = false
  | equal_wire_refusala Unsupported_Wire_Version Conflicting_Wire_Replay = false
  | equal_wire_refusala Conflicting_Wire_Replay Unsupported_Wire_Version = false
  | equal_wire_refusala Unsupported_Wire_Version Wire_TTL_Invalid = false
  | equal_wire_refusala Wire_TTL_Invalid Unsupported_Wire_Version = false
  | equal_wire_refusala Unsupported_Wire_Version Wire_TTL_Expired = false
  | equal_wire_refusala Wire_TTL_Expired Unsupported_Wire_Version = false
  | equal_wire_refusala Unsupported_Wire_Version Invalid_Wire_Threshold = false
  | equal_wire_refusala Invalid_Wire_Threshold Unsupported_Wire_Version = false
  | equal_wire_refusala Unsupported_Wire_Version Invalid_Wire_Signature = false
  | equal_wire_refusala Invalid_Wire_Signature Unsupported_Wire_Version = false
  | equal_wire_refusala Unsupported_Wire_Version Invalid_Wire_Source = false
  | equal_wire_refusala Invalid_Wire_Source Unsupported_Wire_Version = false
  | equal_wire_refusala Invalid_Wire_Format Conflicting_Wire_Replay = false
  | equal_wire_refusala Conflicting_Wire_Replay Invalid_Wire_Format = false
  | equal_wire_refusala Invalid_Wire_Format Wire_TTL_Invalid = false
  | equal_wire_refusala Wire_TTL_Invalid Invalid_Wire_Format = false
  | equal_wire_refusala Invalid_Wire_Format Wire_TTL_Expired = false
  | equal_wire_refusala Wire_TTL_Expired Invalid_Wire_Format = false
  | equal_wire_refusala Invalid_Wire_Format Invalid_Wire_Threshold = false
  | equal_wire_refusala Invalid_Wire_Threshold Invalid_Wire_Format = false
  | equal_wire_refusala Invalid_Wire_Format Invalid_Wire_Signature = false
  | equal_wire_refusala Invalid_Wire_Signature Invalid_Wire_Format = false
  | equal_wire_refusala Invalid_Wire_Format Invalid_Wire_Source = false
  | equal_wire_refusala Invalid_Wire_Source Invalid_Wire_Format = false
  | equal_wire_refusala Invalid_Wire_Format Unsupported_Wire_Version = false
  | equal_wire_refusala Unsupported_Wire_Version Invalid_Wire_Format = false
  | equal_wire_refusala Conflicting_Wire_Replay Conflicting_Wire_Replay = true
  | equal_wire_refusala Wire_TTL_Invalid Wire_TTL_Invalid = true
  | equal_wire_refusala Wire_TTL_Expired Wire_TTL_Expired = true
  | equal_wire_refusala Invalid_Wire_Threshold Invalid_Wire_Threshold = true
  | equal_wire_refusala Invalid_Wire_Signature Invalid_Wire_Signature = true
  | equal_wire_refusala Invalid_Wire_Source Invalid_Wire_Source = true
  | equal_wire_refusala Unsupported_Wire_Version Unsupported_Wire_Version = true
  | equal_wire_refusala Invalid_Wire_Format Invalid_Wire_Format = true;

val equal_wire_refusal = {equal = equal_wire_refusala} : wire_refusal equal;

datatype sync_failure = Sync_Busy | Sync_Unavailable | Sync_Proof_Rejected |
  Sync_Mismatch | Sync_Stale;

fun equal_sync_failure Sync_Mismatch Sync_Stale = false
  | equal_sync_failure Sync_Stale Sync_Mismatch = false
  | equal_sync_failure Sync_Proof_Rejected Sync_Stale = false
  | equal_sync_failure Sync_Stale Sync_Proof_Rejected = false
  | equal_sync_failure Sync_Proof_Rejected Sync_Mismatch = false
  | equal_sync_failure Sync_Mismatch Sync_Proof_Rejected = false
  | equal_sync_failure Sync_Unavailable Sync_Stale = false
  | equal_sync_failure Sync_Stale Sync_Unavailable = false
  | equal_sync_failure Sync_Unavailable Sync_Mismatch = false
  | equal_sync_failure Sync_Mismatch Sync_Unavailable = false
  | equal_sync_failure Sync_Unavailable Sync_Proof_Rejected = false
  | equal_sync_failure Sync_Proof_Rejected Sync_Unavailable = false
  | equal_sync_failure Sync_Busy Sync_Stale = false
  | equal_sync_failure Sync_Stale Sync_Busy = false
  | equal_sync_failure Sync_Busy Sync_Mismatch = false
  | equal_sync_failure Sync_Mismatch Sync_Busy = false
  | equal_sync_failure Sync_Busy Sync_Proof_Rejected = false
  | equal_sync_failure Sync_Proof_Rejected Sync_Busy = false
  | equal_sync_failure Sync_Busy Sync_Unavailable = false
  | equal_sync_failure Sync_Unavailable Sync_Busy = false
  | equal_sync_failure Sync_Stale Sync_Stale = true
  | equal_sync_failure Sync_Mismatch Sync_Mismatch = true
  | equal_sync_failure Sync_Proof_Rejected Sync_Proof_Rejected = true
  | equal_sync_failure Sync_Unavailable Sync_Unavailable = true
  | equal_sync_failure Sync_Busy Sync_Busy = true;

datatype sync_outcome = Sync_Uncommitted of sync_failure |
  Sync_Committed of nat;

fun equal_sync_outcomea (Sync_Uncommitted x1) (Sync_Committed x2) = false
  | equal_sync_outcomea (Sync_Committed x2) (Sync_Uncommitted x1) = false
  | equal_sync_outcomea (Sync_Committed x2) (Sync_Committed y2) =
    equal_nata x2 y2
  | equal_sync_outcomea (Sync_Uncommitted x1) (Sync_Uncommitted y1) =
    equal_sync_failure x1 y1;

val equal_sync_outcome = {equal = equal_sync_outcomea} : sync_outcome equal;

datatype wire_deadline = Deadline_Absent | Deadline_Indefinite |
  Deadline_At of nat;

fun equal_wire_deadline Deadline_Indefinite (Deadline_At x3) = false
  | equal_wire_deadline (Deadline_At x3) Deadline_Indefinite = false
  | equal_wire_deadline Deadline_Absent (Deadline_At x3) = false
  | equal_wire_deadline (Deadline_At x3) Deadline_Absent = false
  | equal_wire_deadline Deadline_Absent Deadline_Indefinite = false
  | equal_wire_deadline Deadline_Indefinite Deadline_Absent = false
  | equal_wire_deadline (Deadline_At x3) (Deadline_At y3) = equal_nata x3 y3
  | equal_wire_deadline Deadline_Indefinite Deadline_Indefinite = true
  | equal_wire_deadline Deadline_Absent Deadline_Absent = true;

datatype 'a wire_body_ext =
  Wire_body_ext of nat * nat list * (nat list) list * wire_deadline * 'a;

fun equal_wire_body_ext A_
  (Wire_body_ext
    (wire_opcodea, wire_wordsa, wire_blobsa, wire_deadlinea, morea))
  (Wire_body_ext (wire_opcode, wire_words, wire_blobs, wire_deadline, more)) =
  equal_nata wire_opcodea wire_opcode andalso
    (equal_lista equal_nat wire_wordsa wire_words andalso
      (equal_lista (equal_list equal_nat) wire_blobsa wire_blobs andalso
        (equal_wire_deadline wire_deadlinea wire_deadline andalso
          eq A_ morea more)));

datatype 'a wire_core_ext =
  Wire_core_ext of
    nat * nat * nat * nat * nat * nat * nat * nat * nat * nat * nat list *
      wire_family * nat * nat option * nat * unit wire_body_ext * nat * nat *
      nat * 'a;

fun equal_wire_core_ext A_
  (Wire_core_ext
    (wire_versiona, wire_purposea, wire_deploymenta, wire_source_domaina,
      wire_target_domaina, wire_principala, wire_key_numbera,
      wire_authority_epocha, wire_sent_secondsa, wire_ttl_secondsa, wire_uuida,
      wire_message_familya, wire_primary_codea, wire_secondary_codea,
      wire_signature_schemea, wire_operation_bodya, wire_atomicitya,
      wire_prioritya, wire_route_scopea, morea))
  (Wire_core_ext
    (wire_version, wire_purpose, wire_deployment, wire_source_domain,
      wire_target_domain, wire_principal, wire_key_number, wire_authority_epoch,
      wire_sent_seconds, wire_ttl_seconds, wire_uuid, wire_message_family,
      wire_primary_code, wire_secondary_code, wire_signature_scheme,
      wire_operation_body, wire_atomicity, wire_priority, wire_route_scope,
      more))
  = equal_nata wire_versiona wire_version andalso
      (equal_nata wire_purposea wire_purpose andalso
        (equal_nata wire_deploymenta wire_deployment andalso
          (equal_nata wire_source_domaina wire_source_domain andalso
            (equal_nata wire_target_domaina wire_target_domain andalso
              (equal_nata wire_principala wire_principal andalso
                (equal_nata wire_key_numbera wire_key_number andalso
                  (equal_nata wire_authority_epocha wire_authority_epoch andalso
                    (equal_nata wire_sent_secondsa wire_sent_seconds andalso
                      (equal_nata wire_ttl_secondsa wire_ttl_seconds andalso
                        (equal_lista equal_nat wire_uuida wire_uuid andalso
                          (equal_wire_familya wire_message_familya
                             wire_message_family andalso
                            (equal_nata wire_primary_codea
                               wire_primary_code andalso
                              (equal_optiona equal_nat wire_secondary_codea
                                 wire_secondary_code andalso
                                (equal_nata wire_signature_schemea
                                   wire_signature_scheme andalso
                                  (equal_wire_body_ext equal_unit
                                     wire_operation_bodya
                                     wire_operation_body andalso
                                    (equal_nata wire_atomicitya
                                       wire_atomicity andalso
                                      (equal_nata wire_prioritya
 wire_priority andalso
(equal_nata wire_route_scopea wire_route_scope andalso
  eq A_ morea more))))))))))))))))));

datatype 'a wire_packet_ext =
  Wire_packet_ext of unit wire_core_ext * nat list * 'a;

fun equal_wire_packet_exta A_
  (Wire_packet_ext (packet_corea, packet_signaturea, morea))
  (Wire_packet_ext (packet_core, packet_signature, more)) =
  equal_wire_core_ext equal_unit packet_corea packet_core andalso
    (equal_lista equal_nat packet_signaturea packet_signature andalso
      eq A_ morea more);

fun equal_wire_packet_ext A_ = {equal = equal_wire_packet_exta A_} :
  'a wire_packet_ext equal;

datatype reference_response_kind = Recorded_Result | Delivery_Refusal |
  Validation_Refusal;

fun equal_reference_response_kinda Delivery_Refusal Validation_Refusal = false
  | equal_reference_response_kinda Validation_Refusal Delivery_Refusal = false
  | equal_reference_response_kinda Recorded_Result Validation_Refusal = false
  | equal_reference_response_kinda Validation_Refusal Recorded_Result = false
  | equal_reference_response_kinda Recorded_Result Delivery_Refusal = false
  | equal_reference_response_kinda Delivery_Refusal Recorded_Result = false
  | equal_reference_response_kinda Validation_Refusal Validation_Refusal = true
  | equal_reference_response_kinda Delivery_Refusal Delivery_Refusal = true
  | equal_reference_response_kinda Recorded_Result Recorded_Result = true;

datatype code_response_status =
  Code_Known_Response of reference_response_kind * nat |
  Code_Unknown_Response of reference_response_kind * nat;

fun equal_code_response_statusa (Code_Known_Response (x11, x12))
  (Code_Unknown_Response (x21, x22)) = false
  | equal_code_response_statusa (Code_Unknown_Response (x21, x22))
    (Code_Known_Response (x11, x12)) = false
  | equal_code_response_statusa (Code_Unknown_Response (x21, x22))
    (Code_Unknown_Response (y21, y22)) =
    equal_reference_response_kinda x21 y21 andalso equal_nata x22 y22
  | equal_code_response_statusa (Code_Known_Response (x11, x12))
    (Code_Known_Response (y11, y12)) =
    equal_reference_response_kinda x11 y11 andalso equal_nata x12 y12;

val equal_code_response_status = {equal = equal_code_response_statusa} :
  code_response_status equal;

val equal_reference_response_kind = {equal = equal_reference_response_kinda} :
  reference_response_kind equal;

datatype 'a sync_entry_ext = Sync_entry_ext of nat list * nat * nat * nat * 'a;

fun equal_sync_entry_ext A_
  (Sync_entry_ext
    (sync_commitmenta, sync_positiona, sync_origin_epocha, sync_eventa, morea))
  (Sync_entry_ext
    (sync_commitment, sync_position, sync_origin_epoch, sync_event, more))
  = equal_lista equal_nat sync_commitmenta sync_commitment andalso
      (equal_nata sync_positiona sync_position andalso
        (equal_nata sync_origin_epocha sync_origin_epoch andalso
          (equal_nata sync_eventa sync_event andalso eq A_ morea more)));

datatype 'a product_cut_ext = Product_cut_ext of nat * nat * 'a;

fun equal_product_cut_ext A_
  (Product_cut_ext (cut_authority_epocha, cut_revisiona, morea))
  (Product_cut_ext (cut_authority_epoch, cut_revision, more)) =
  equal_nata cut_authority_epocha cut_authority_epoch andalso
    (equal_nata cut_revisiona cut_revision andalso eq A_ morea more);

datatype sync_mode = Sync_Initial | Sync_Incremental | Sync_Full;

fun equal_sync_mode Sync_Incremental Sync_Full = false
  | equal_sync_mode Sync_Full Sync_Incremental = false
  | equal_sync_mode Sync_Initial Sync_Full = false
  | equal_sync_mode Sync_Full Sync_Initial = false
  | equal_sync_mode Sync_Initial Sync_Incremental = false
  | equal_sync_mode Sync_Incremental Sync_Initial = false
  | equal_sync_mode Sync_Full Sync_Full = true
  | equal_sync_mode Sync_Incremental Sync_Incremental = true
  | equal_sync_mode Sync_Initial Sync_Initial = true;

datatype 'a sync_request_ext =
  Sync_request_ext of
    (nat * nat) * nat * nat * unit product_cut_ext * (nat * nat) *
      unit sync_entry_ext * sync_mode * (nat list) option * nat list * 'a;

fun equal_sync_request_ext A_
  (Sync_request_ext
    (sync_calla, sync_messagea, sync_sessiona, sync_signed_cuta, sync_keya,
      sync_requesteda, sync_modea, sync_claimed_priora, sync_attestationa,
      morea))
  (Sync_request_ext
    (sync_call, sync_message, sync_session, sync_signed_cut, sync_key,
      sync_requested, sync_mode, sync_claimed_prior, sync_attestation, more))
  = equal_proda equal_nat equal_nat sync_calla sync_call andalso
      (equal_nata sync_messagea sync_message andalso
        (equal_nata sync_sessiona sync_session andalso
          (equal_product_cut_ext equal_unit sync_signed_cuta
             sync_signed_cut andalso
            (equal_proda equal_nat equal_nat sync_keya sync_key andalso
              (equal_sync_entry_ext equal_unit sync_requesteda
                 sync_requested andalso
                (equal_sync_mode sync_modea sync_mode andalso
                  (equal_optiona (equal_list equal_nat) sync_claimed_priora
                     sync_claimed_prior andalso
                    (equal_lista equal_nat sync_attestationa
                       sync_attestation andalso
                      eq A_ morea more))))))));

datatype 'a wire_native_call_ext =
  Wire_native_call_ext of
    nat * (nat * nat) * nat * unit product_cut_ext * nat * (nat * nat) * nat *
      nat * nat * nat * nat * nat list * (nat list) list * 'a;

fun equal_wire_native_call_ext A_
  (Wire_native_call_ext
    (native_referencea, native_ida, native_sessiona, native_cuta,
      native_origin_epocha, native_origina, native_asseta,
      native_funding_ownera, native_destinationa, native_recipienta,
      native_amounta, native_tail_wordsa, native_proof_bytesa, morea))
  (Wire_native_call_ext
    (native_reference, native_id, native_session, native_cut,
      native_origin_epoch, native_origin, native_asset, native_funding_owner,
      native_destination, native_recipient, native_amount, native_tail_words,
      native_proof_bytes, more))
  = equal_nata native_referencea native_reference andalso
      (equal_proda equal_nat equal_nat native_ida native_id andalso
        (equal_nata native_sessiona native_session andalso
          (equal_product_cut_ext equal_unit native_cuta native_cut andalso
            (equal_nata native_origin_epocha native_origin_epoch andalso
              (equal_proda equal_nat equal_nat native_origina
                 native_origin andalso
                (equal_nata native_asseta native_asset andalso
                  (equal_nata native_funding_ownera native_funding_owner andalso
                    (equal_nata native_destinationa native_destination andalso
                      (equal_nata native_recipienta native_recipient andalso
                        (equal_nata native_amounta native_amount andalso
                          (equal_lista equal_nat native_tail_wordsa
                             native_tail_words andalso
                            (equal_lista (equal_list equal_nat)
                               native_proof_bytesa native_proof_bytes andalso
                              eq A_ morea more))))))))))));

datatype ordinary_wire_command = Wire_Reserve of nat | Wire_Dispatch of nat |
  Wire_Debit of nat | Wire_Cancel of nat | Wire_Fence of nat |
  Wire_Preempt of nat | Wire_Timeout of nat | Wire_Record_Terminal of nat * nat
  | Wire_Deliver of nat | Wire_Refund of nat * nat | Wire_Reconcile of nat * nat
  | Wire_Write of nat * nat | Wire_Publish;

fun equal_ordinary_wire_command (Wire_Write (x121, x122)) Wire_Publish = false
  | equal_ordinary_wire_command Wire_Publish (Wire_Write (x121, x122)) = false
  | equal_ordinary_wire_command (Wire_Reconcile (x111, x112)) Wire_Publish =
    false
  | equal_ordinary_wire_command Wire_Publish (Wire_Reconcile (x111, x112)) =
    false
  | equal_ordinary_wire_command (Wire_Reconcile (x111, x112))
    (Wire_Write (x121, x122)) = false
  | equal_ordinary_wire_command (Wire_Write (x121, x122))
    (Wire_Reconcile (x111, x112)) = false
  | equal_ordinary_wire_command (Wire_Refund (x101, x102)) Wire_Publish = false
  | equal_ordinary_wire_command Wire_Publish (Wire_Refund (x101, x102)) = false
  | equal_ordinary_wire_command (Wire_Refund (x101, x102))
    (Wire_Write (x121, x122)) = false
  | equal_ordinary_wire_command (Wire_Write (x121, x122))
    (Wire_Refund (x101, x102)) = false
  | equal_ordinary_wire_command (Wire_Refund (x101, x102))
    (Wire_Reconcile (x111, x112)) = false
  | equal_ordinary_wire_command (Wire_Reconcile (x111, x112))
    (Wire_Refund (x101, x102)) = false
  | equal_ordinary_wire_command (Wire_Deliver x9) Wire_Publish = false
  | equal_ordinary_wire_command Wire_Publish (Wire_Deliver x9) = false
  | equal_ordinary_wire_command (Wire_Deliver x9) (Wire_Write (x121, x122)) =
    false
  | equal_ordinary_wire_command (Wire_Write (x121, x122)) (Wire_Deliver x9) =
    false
  | equal_ordinary_wire_command (Wire_Deliver x9) (Wire_Reconcile (x111, x112))
    = false
  | equal_ordinary_wire_command (Wire_Reconcile (x111, x112)) (Wire_Deliver x9)
    = false
  | equal_ordinary_wire_command (Wire_Deliver x9) (Wire_Refund (x101, x102)) =
    false
  | equal_ordinary_wire_command (Wire_Refund (x101, x102)) (Wire_Deliver x9) =
    false
  | equal_ordinary_wire_command (Wire_Record_Terminal (x81, x82)) Wire_Publish =
    false
  | equal_ordinary_wire_command Wire_Publish (Wire_Record_Terminal (x81, x82)) =
    false
  | equal_ordinary_wire_command (Wire_Record_Terminal (x81, x82))
    (Wire_Write (x121, x122)) = false
  | equal_ordinary_wire_command (Wire_Write (x121, x122))
    (Wire_Record_Terminal (x81, x82)) = false
  | equal_ordinary_wire_command (Wire_Record_Terminal (x81, x82))
    (Wire_Reconcile (x111, x112)) = false
  | equal_ordinary_wire_command (Wire_Reconcile (x111, x112))
    (Wire_Record_Terminal (x81, x82)) = false
  | equal_ordinary_wire_command (Wire_Record_Terminal (x81, x82))
    (Wire_Refund (x101, x102)) = false
  | equal_ordinary_wire_command (Wire_Refund (x101, x102))
    (Wire_Record_Terminal (x81, x82)) = false
  | equal_ordinary_wire_command (Wire_Record_Terminal (x81, x82))
    (Wire_Deliver x9) = false
  | equal_ordinary_wire_command (Wire_Deliver x9)
    (Wire_Record_Terminal (x81, x82)) = false
  | equal_ordinary_wire_command (Wire_Timeout x7) Wire_Publish = false
  | equal_ordinary_wire_command Wire_Publish (Wire_Timeout x7) = false
  | equal_ordinary_wire_command (Wire_Timeout x7) (Wire_Write (x121, x122)) =
    false
  | equal_ordinary_wire_command (Wire_Write (x121, x122)) (Wire_Timeout x7) =
    false
  | equal_ordinary_wire_command (Wire_Timeout x7) (Wire_Reconcile (x111, x112))
    = false
  | equal_ordinary_wire_command (Wire_Reconcile (x111, x112)) (Wire_Timeout x7)
    = false
  | equal_ordinary_wire_command (Wire_Timeout x7) (Wire_Refund (x101, x102)) =
    false
  | equal_ordinary_wire_command (Wire_Refund (x101, x102)) (Wire_Timeout x7) =
    false
  | equal_ordinary_wire_command (Wire_Timeout x7) (Wire_Deliver x9) = false
  | equal_ordinary_wire_command (Wire_Deliver x9) (Wire_Timeout x7) = false
  | equal_ordinary_wire_command (Wire_Timeout x7)
    (Wire_Record_Terminal (x81, x82)) = false
  | equal_ordinary_wire_command (Wire_Record_Terminal (x81, x82))
    (Wire_Timeout x7) = false
  | equal_ordinary_wire_command (Wire_Preempt x6) Wire_Publish = false
  | equal_ordinary_wire_command Wire_Publish (Wire_Preempt x6) = false
  | equal_ordinary_wire_command (Wire_Preempt x6) (Wire_Write (x121, x122)) =
    false
  | equal_ordinary_wire_command (Wire_Write (x121, x122)) (Wire_Preempt x6) =
    false
  | equal_ordinary_wire_command (Wire_Preempt x6) (Wire_Reconcile (x111, x112))
    = false
  | equal_ordinary_wire_command (Wire_Reconcile (x111, x112)) (Wire_Preempt x6)
    = false
  | equal_ordinary_wire_command (Wire_Preempt x6) (Wire_Refund (x101, x102)) =
    false
  | equal_ordinary_wire_command (Wire_Refund (x101, x102)) (Wire_Preempt x6) =
    false
  | equal_ordinary_wire_command (Wire_Preempt x6) (Wire_Deliver x9) = false
  | equal_ordinary_wire_command (Wire_Deliver x9) (Wire_Preempt x6) = false
  | equal_ordinary_wire_command (Wire_Preempt x6)
    (Wire_Record_Terminal (x81, x82)) = false
  | equal_ordinary_wire_command (Wire_Record_Terminal (x81, x82))
    (Wire_Preempt x6) = false
  | equal_ordinary_wire_command (Wire_Preempt x6) (Wire_Timeout x7) = false
  | equal_ordinary_wire_command (Wire_Timeout x7) (Wire_Preempt x6) = false
  | equal_ordinary_wire_command (Wire_Fence x5) Wire_Publish = false
  | equal_ordinary_wire_command Wire_Publish (Wire_Fence x5) = false
  | equal_ordinary_wire_command (Wire_Fence x5) (Wire_Write (x121, x122)) =
    false
  | equal_ordinary_wire_command (Wire_Write (x121, x122)) (Wire_Fence x5) =
    false
  | equal_ordinary_wire_command (Wire_Fence x5) (Wire_Reconcile (x111, x112)) =
    false
  | equal_ordinary_wire_command (Wire_Reconcile (x111, x112)) (Wire_Fence x5) =
    false
  | equal_ordinary_wire_command (Wire_Fence x5) (Wire_Refund (x101, x102)) =
    false
  | equal_ordinary_wire_command (Wire_Refund (x101, x102)) (Wire_Fence x5) =
    false
  | equal_ordinary_wire_command (Wire_Fence x5) (Wire_Deliver x9) = false
  | equal_ordinary_wire_command (Wire_Deliver x9) (Wire_Fence x5) = false
  | equal_ordinary_wire_command (Wire_Fence x5)
    (Wire_Record_Terminal (x81, x82)) = false
  | equal_ordinary_wire_command (Wire_Record_Terminal (x81, x82))
    (Wire_Fence x5) = false
  | equal_ordinary_wire_command (Wire_Fence x5) (Wire_Timeout x7) = false
  | equal_ordinary_wire_command (Wire_Timeout x7) (Wire_Fence x5) = false
  | equal_ordinary_wire_command (Wire_Fence x5) (Wire_Preempt x6) = false
  | equal_ordinary_wire_command (Wire_Preempt x6) (Wire_Fence x5) = false
  | equal_ordinary_wire_command (Wire_Cancel x4) Wire_Publish = false
  | equal_ordinary_wire_command Wire_Publish (Wire_Cancel x4) = false
  | equal_ordinary_wire_command (Wire_Cancel x4) (Wire_Write (x121, x122)) =
    false
  | equal_ordinary_wire_command (Wire_Write (x121, x122)) (Wire_Cancel x4) =
    false
  | equal_ordinary_wire_command (Wire_Cancel x4) (Wire_Reconcile (x111, x112)) =
    false
  | equal_ordinary_wire_command (Wire_Reconcile (x111, x112)) (Wire_Cancel x4) =
    false
  | equal_ordinary_wire_command (Wire_Cancel x4) (Wire_Refund (x101, x102)) =
    false
  | equal_ordinary_wire_command (Wire_Refund (x101, x102)) (Wire_Cancel x4) =
    false
  | equal_ordinary_wire_command (Wire_Cancel x4) (Wire_Deliver x9) = false
  | equal_ordinary_wire_command (Wire_Deliver x9) (Wire_Cancel x4) = false
  | equal_ordinary_wire_command (Wire_Cancel x4)
    (Wire_Record_Terminal (x81, x82)) = false
  | equal_ordinary_wire_command (Wire_Record_Terminal (x81, x82))
    (Wire_Cancel x4) = false
  | equal_ordinary_wire_command (Wire_Cancel x4) (Wire_Timeout x7) = false
  | equal_ordinary_wire_command (Wire_Timeout x7) (Wire_Cancel x4) = false
  | equal_ordinary_wire_command (Wire_Cancel x4) (Wire_Preempt x6) = false
  | equal_ordinary_wire_command (Wire_Preempt x6) (Wire_Cancel x4) = false
  | equal_ordinary_wire_command (Wire_Cancel x4) (Wire_Fence x5) = false
  | equal_ordinary_wire_command (Wire_Fence x5) (Wire_Cancel x4) = false
  | equal_ordinary_wire_command (Wire_Debit x3) Wire_Publish = false
  | equal_ordinary_wire_command Wire_Publish (Wire_Debit x3) = false
  | equal_ordinary_wire_command (Wire_Debit x3) (Wire_Write (x121, x122)) =
    false
  | equal_ordinary_wire_command (Wire_Write (x121, x122)) (Wire_Debit x3) =
    false
  | equal_ordinary_wire_command (Wire_Debit x3) (Wire_Reconcile (x111, x112)) =
    false
  | equal_ordinary_wire_command (Wire_Reconcile (x111, x112)) (Wire_Debit x3) =
    false
  | equal_ordinary_wire_command (Wire_Debit x3) (Wire_Refund (x101, x102)) =
    false
  | equal_ordinary_wire_command (Wire_Refund (x101, x102)) (Wire_Debit x3) =
    false
  | equal_ordinary_wire_command (Wire_Debit x3) (Wire_Deliver x9) = false
  | equal_ordinary_wire_command (Wire_Deliver x9) (Wire_Debit x3) = false
  | equal_ordinary_wire_command (Wire_Debit x3)
    (Wire_Record_Terminal (x81, x82)) = false
  | equal_ordinary_wire_command (Wire_Record_Terminal (x81, x82))
    (Wire_Debit x3) = false
  | equal_ordinary_wire_command (Wire_Debit x3) (Wire_Timeout x7) = false
  | equal_ordinary_wire_command (Wire_Timeout x7) (Wire_Debit x3) = false
  | equal_ordinary_wire_command (Wire_Debit x3) (Wire_Preempt x6) = false
  | equal_ordinary_wire_command (Wire_Preempt x6) (Wire_Debit x3) = false
  | equal_ordinary_wire_command (Wire_Debit x3) (Wire_Fence x5) = false
  | equal_ordinary_wire_command (Wire_Fence x5) (Wire_Debit x3) = false
  | equal_ordinary_wire_command (Wire_Debit x3) (Wire_Cancel x4) = false
  | equal_ordinary_wire_command (Wire_Cancel x4) (Wire_Debit x3) = false
  | equal_ordinary_wire_command (Wire_Dispatch x2) Wire_Publish = false
  | equal_ordinary_wire_command Wire_Publish (Wire_Dispatch x2) = false
  | equal_ordinary_wire_command (Wire_Dispatch x2) (Wire_Write (x121, x122)) =
    false
  | equal_ordinary_wire_command (Wire_Write (x121, x122)) (Wire_Dispatch x2) =
    false
  | equal_ordinary_wire_command (Wire_Dispatch x2) (Wire_Reconcile (x111, x112))
    = false
  | equal_ordinary_wire_command (Wire_Reconcile (x111, x112)) (Wire_Dispatch x2)
    = false
  | equal_ordinary_wire_command (Wire_Dispatch x2) (Wire_Refund (x101, x102)) =
    false
  | equal_ordinary_wire_command (Wire_Refund (x101, x102)) (Wire_Dispatch x2) =
    false
  | equal_ordinary_wire_command (Wire_Dispatch x2) (Wire_Deliver x9) = false
  | equal_ordinary_wire_command (Wire_Deliver x9) (Wire_Dispatch x2) = false
  | equal_ordinary_wire_command (Wire_Dispatch x2)
    (Wire_Record_Terminal (x81, x82)) = false
  | equal_ordinary_wire_command (Wire_Record_Terminal (x81, x82))
    (Wire_Dispatch x2) = false
  | equal_ordinary_wire_command (Wire_Dispatch x2) (Wire_Timeout x7) = false
  | equal_ordinary_wire_command (Wire_Timeout x7) (Wire_Dispatch x2) = false
  | equal_ordinary_wire_command (Wire_Dispatch x2) (Wire_Preempt x6) = false
  | equal_ordinary_wire_command (Wire_Preempt x6) (Wire_Dispatch x2) = false
  | equal_ordinary_wire_command (Wire_Dispatch x2) (Wire_Fence x5) = false
  | equal_ordinary_wire_command (Wire_Fence x5) (Wire_Dispatch x2) = false
  | equal_ordinary_wire_command (Wire_Dispatch x2) (Wire_Cancel x4) = false
  | equal_ordinary_wire_command (Wire_Cancel x4) (Wire_Dispatch x2) = false
  | equal_ordinary_wire_command (Wire_Dispatch x2) (Wire_Debit x3) = false
  | equal_ordinary_wire_command (Wire_Debit x3) (Wire_Dispatch x2) = false
  | equal_ordinary_wire_command (Wire_Reserve x1) Wire_Publish = false
  | equal_ordinary_wire_command Wire_Publish (Wire_Reserve x1) = false
  | equal_ordinary_wire_command (Wire_Reserve x1) (Wire_Write (x121, x122)) =
    false
  | equal_ordinary_wire_command (Wire_Write (x121, x122)) (Wire_Reserve x1) =
    false
  | equal_ordinary_wire_command (Wire_Reserve x1) (Wire_Reconcile (x111, x112))
    = false
  | equal_ordinary_wire_command (Wire_Reconcile (x111, x112)) (Wire_Reserve x1)
    = false
  | equal_ordinary_wire_command (Wire_Reserve x1) (Wire_Refund (x101, x102)) =
    false
  | equal_ordinary_wire_command (Wire_Refund (x101, x102)) (Wire_Reserve x1) =
    false
  | equal_ordinary_wire_command (Wire_Reserve x1) (Wire_Deliver x9) = false
  | equal_ordinary_wire_command (Wire_Deliver x9) (Wire_Reserve x1) = false
  | equal_ordinary_wire_command (Wire_Reserve x1)
    (Wire_Record_Terminal (x81, x82)) = false
  | equal_ordinary_wire_command (Wire_Record_Terminal (x81, x82))
    (Wire_Reserve x1) = false
  | equal_ordinary_wire_command (Wire_Reserve x1) (Wire_Timeout x7) = false
  | equal_ordinary_wire_command (Wire_Timeout x7) (Wire_Reserve x1) = false
  | equal_ordinary_wire_command (Wire_Reserve x1) (Wire_Preempt x6) = false
  | equal_ordinary_wire_command (Wire_Preempt x6) (Wire_Reserve x1) = false
  | equal_ordinary_wire_command (Wire_Reserve x1) (Wire_Fence x5) = false
  | equal_ordinary_wire_command (Wire_Fence x5) (Wire_Reserve x1) = false
  | equal_ordinary_wire_command (Wire_Reserve x1) (Wire_Cancel x4) = false
  | equal_ordinary_wire_command (Wire_Cancel x4) (Wire_Reserve x1) = false
  | equal_ordinary_wire_command (Wire_Reserve x1) (Wire_Debit x3) = false
  | equal_ordinary_wire_command (Wire_Debit x3) (Wire_Reserve x1) = false
  | equal_ordinary_wire_command (Wire_Reserve x1) (Wire_Dispatch x2) = false
  | equal_ordinary_wire_command (Wire_Dispatch x2) (Wire_Reserve x1) = false
  | equal_ordinary_wire_command (Wire_Write (x121, x122))
    (Wire_Write (y121, y122)) =
    equal_nata x121 y121 andalso equal_nata x122 y122
  | equal_ordinary_wire_command (Wire_Reconcile (x111, x112))
    (Wire_Reconcile (y111, y112)) =
    equal_nata x111 y111 andalso equal_nata x112 y112
  | equal_ordinary_wire_command (Wire_Refund (x101, x102))
    (Wire_Refund (y101, y102)) =
    equal_nata x101 y101 andalso equal_nata x102 y102
  | equal_ordinary_wire_command (Wire_Deliver x9) (Wire_Deliver y9) =
    equal_nata x9 y9
  | equal_ordinary_wire_command (Wire_Record_Terminal (x81, x82))
    (Wire_Record_Terminal (y81, y82)) =
    equal_nata x81 y81 andalso equal_nata x82 y82
  | equal_ordinary_wire_command (Wire_Timeout x7) (Wire_Timeout y7) =
    equal_nata x7 y7
  | equal_ordinary_wire_command (Wire_Preempt x6) (Wire_Preempt y6) =
    equal_nata x6 y6
  | equal_ordinary_wire_command (Wire_Fence x5) (Wire_Fence y5) =
    equal_nata x5 y5
  | equal_ordinary_wire_command (Wire_Cancel x4) (Wire_Cancel y4) =
    equal_nata x4 y4
  | equal_ordinary_wire_command (Wire_Debit x3) (Wire_Debit y3) =
    equal_nata x3 y3
  | equal_ordinary_wire_command (Wire_Dispatch x2) (Wire_Dispatch y2) =
    equal_nata x2 y2
  | equal_ordinary_wire_command (Wire_Reserve x1) (Wire_Reserve y1) =
    equal_nata x1 y1
  | equal_ordinary_wire_command Wire_Publish Wire_Publish = true;

datatype code_nested_operand =
  Code_Nested_Ordinary of unit wire_native_call_ext * ordinary_wire_command |
  Code_Nested_Legal of (nat * nat) | Code_Nested_Spend of (nat * nat) |
  Code_Nested_Receipt of unit wire_core_ext | Code_Nested_Response |
  Code_Nested_Other;

fun equal_code_nested_operand Code_Nested_Response Code_Nested_Other = false
  | equal_code_nested_operand Code_Nested_Other Code_Nested_Response = false
  | equal_code_nested_operand (Code_Nested_Receipt x4) Code_Nested_Other = false
  | equal_code_nested_operand Code_Nested_Other (Code_Nested_Receipt x4) = false
  | equal_code_nested_operand (Code_Nested_Receipt x4) Code_Nested_Response =
    false
  | equal_code_nested_operand Code_Nested_Response (Code_Nested_Receipt x4) =
    false
  | equal_code_nested_operand (Code_Nested_Spend x3) Code_Nested_Other = false
  | equal_code_nested_operand Code_Nested_Other (Code_Nested_Spend x3) = false
  | equal_code_nested_operand (Code_Nested_Spend x3) Code_Nested_Response =
    false
  | equal_code_nested_operand Code_Nested_Response (Code_Nested_Spend x3) =
    false
  | equal_code_nested_operand (Code_Nested_Spend x3) (Code_Nested_Receipt x4) =
    false
  | equal_code_nested_operand (Code_Nested_Receipt x4) (Code_Nested_Spend x3) =
    false
  | equal_code_nested_operand (Code_Nested_Legal x2) Code_Nested_Other = false
  | equal_code_nested_operand Code_Nested_Other (Code_Nested_Legal x2) = false
  | equal_code_nested_operand (Code_Nested_Legal x2) Code_Nested_Response =
    false
  | equal_code_nested_operand Code_Nested_Response (Code_Nested_Legal x2) =
    false
  | equal_code_nested_operand (Code_Nested_Legal x2) (Code_Nested_Receipt x4) =
    false
  | equal_code_nested_operand (Code_Nested_Receipt x4) (Code_Nested_Legal x2) =
    false
  | equal_code_nested_operand (Code_Nested_Legal x2) (Code_Nested_Spend x3) =
    false
  | equal_code_nested_operand (Code_Nested_Spend x3) (Code_Nested_Legal x2) =
    false
  | equal_code_nested_operand (Code_Nested_Ordinary (x11, x12))
    Code_Nested_Other = false
  | equal_code_nested_operand Code_Nested_Other
    (Code_Nested_Ordinary (x11, x12)) = false
  | equal_code_nested_operand (Code_Nested_Ordinary (x11, x12))
    Code_Nested_Response = false
  | equal_code_nested_operand Code_Nested_Response
    (Code_Nested_Ordinary (x11, x12)) = false
  | equal_code_nested_operand (Code_Nested_Ordinary (x11, x12))
    (Code_Nested_Receipt x4) = false
  | equal_code_nested_operand (Code_Nested_Receipt x4)
    (Code_Nested_Ordinary (x11, x12)) = false
  | equal_code_nested_operand (Code_Nested_Ordinary (x11, x12))
    (Code_Nested_Spend x3) = false
  | equal_code_nested_operand (Code_Nested_Spend x3)
    (Code_Nested_Ordinary (x11, x12)) = false
  | equal_code_nested_operand (Code_Nested_Ordinary (x11, x12))
    (Code_Nested_Legal x2) = false
  | equal_code_nested_operand (Code_Nested_Legal x2)
    (Code_Nested_Ordinary (x11, x12)) = false
  | equal_code_nested_operand (Code_Nested_Receipt x4) (Code_Nested_Receipt y4)
    = equal_wire_core_ext equal_unit x4 y4
  | equal_code_nested_operand (Code_Nested_Spend x3) (Code_Nested_Spend y3) =
    equal_proda equal_nat equal_nat x3 y3
  | equal_code_nested_operand (Code_Nested_Legal x2) (Code_Nested_Legal y2) =
    equal_proda equal_nat equal_nat x2 y2
  | equal_code_nested_operand (Code_Nested_Ordinary (x11, x12))
    (Code_Nested_Ordinary (y11, y12)) =
    equal_wire_native_call_ext equal_unit x11 y11 andalso
      equal_ordinary_wire_command x12 y12
  | equal_code_nested_operand Code_Nested_Other Code_Nested_Other = true
  | equal_code_nested_operand Code_Nested_Response Code_Nested_Response = true;

datatype response_v061_nested =
  Response_V061_Legacy_Operand of code_nested_operand |
  Response_V061_Sync_Operand of unit sync_request_ext |
  Response_V061_Receipt of unit wire_core_ext | Response_V061_Current;

fun equal_response_v061_nesteda (Response_V061_Receipt x3) Response_V061_Current
  = false
  | equal_response_v061_nesteda Response_V061_Current (Response_V061_Receipt x3)
    = false
  | equal_response_v061_nesteda (Response_V061_Sync_Operand x2)
    Response_V061_Current = false
  | equal_response_v061_nesteda Response_V061_Current
    (Response_V061_Sync_Operand x2) = false
  | equal_response_v061_nesteda (Response_V061_Sync_Operand x2)
    (Response_V061_Receipt x3) = false
  | equal_response_v061_nesteda (Response_V061_Receipt x3)
    (Response_V061_Sync_Operand x2) = false
  | equal_response_v061_nesteda (Response_V061_Legacy_Operand x1)
    Response_V061_Current = false
  | equal_response_v061_nesteda Response_V061_Current
    (Response_V061_Legacy_Operand x1) = false
  | equal_response_v061_nesteda (Response_V061_Legacy_Operand x1)
    (Response_V061_Receipt x3) = false
  | equal_response_v061_nesteda (Response_V061_Receipt x3)
    (Response_V061_Legacy_Operand x1) = false
  | equal_response_v061_nesteda (Response_V061_Legacy_Operand x1)
    (Response_V061_Sync_Operand x2) = false
  | equal_response_v061_nesteda (Response_V061_Sync_Operand x2)
    (Response_V061_Legacy_Operand x1) = false
  | equal_response_v061_nesteda (Response_V061_Receipt x3)
    (Response_V061_Receipt y3) = equal_wire_core_ext equal_unit x3 y3
  | equal_response_v061_nesteda (Response_V061_Sync_Operand x2)
    (Response_V061_Sync_Operand y2) = equal_sync_request_ext equal_unit x2 y2
  | equal_response_v061_nesteda (Response_V061_Legacy_Operand x1)
    (Response_V061_Legacy_Operand y1) = equal_code_nested_operand x1 y1
  | equal_response_v061_nesteda Response_V061_Current Response_V061_Current =
    true;

val equal_response_v061_nested = {equal = equal_response_v061_nesteda} :
  response_v061_nested equal;

datatype 'a set = Set of 'a list | Coset of 'a list;

datatype char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;

datatype ('a, 'b) sum = Inl of 'a | Inr of 'b;

datatype proto_field = Proto_Varint of nat * nat | Proto_Fixed64 of nat * nat |
  Proto_Bytes of nat * nat list;

datatype terminal_kind = Confirmed_Decision | Reversed_Decision;

datatype legal_refusal = Invalid_Legal_Authority | Invalid_Legal_State |
  Missing_Prior_Freeze | Missing_Prior_Seizure | Appeal_Deadline_Mismatch |
  Appeal_Still_Open | Missing_Confiscation_Destination | Conflicting_Legal_Order
  | Invalid_Legal_Binding;

datatype 'a session_proof_ext = Session_proof_ext of nat * nat * 'a;

datatype application_query = Source_Balance of (nat * nat) |
  Destination_Balance of (nat * (nat * nat)) |
  Root_Balance of (nat * nat) * (nat * (nat * nat)) | Application_Value of nat |
  Regulatory_State of nat * nat | Terminal_Receipt of (nat * nat);

datatype identity_read_request =
  Current_Data of application_query * unit product_cut_ext |
  Historical_Data of application_query * nat | Raw_Data of application_query |
  Operation_Status of (nat * nat) | Authority_Journal | Owner_Data of nat;

datatype parsed_wire_query =
  Wire_Read_Request of unit session_proof_ext * identity_read_request |
  Wire_Cache_Request of unit session_proof_ext * application_query;

datatype 'a sync_query_ext =
  Sync_query_ext of nat * unit product_cut_ext * (nat * nat) * 'a;

datatype code_legal_stage = Code_Source_Emission | Code_Receiving_Commit;

datatype 'a negotiated_wire_profile_ext =
  Negotiated_wire_profile_ext of nat * wire_family set * nat set * nat set * 'a;

datatype 'a wire_boundary_ext =
  Wire_boundary_ext of
    unit negotiated_wire_profile_ext * nat * nat * nat * nat * nat * nat * nat *
      nat * nat * nat * nat * nat * bool * bool * 'a;

datatype 'a product_lock_token_ext =
  Product_lock_token_ext of nat * nat * nat * 'a;

datatype 'a product_lock_credential_ext =
  Product_lock_credential_ext of
    unit product_lock_token_ext * nat * (nat * nat) * 'a;

datatype code_ordinary_result = Code_Ordinary_Refused of wire_refusal |
  Code_Ordinary_Ready of
    unit wire_native_call_ext * unit product_lock_credential_ext option *
      (nat * nat) list * ordinary_wire_command;

datatype 'a code_legal_fields_ext =
  Code_legal_fields_ext of
    nat * nat * nat * nat * nat * nat set * (nat * nat) option * nat option *
      nat option * 'a;

datatype code_legal_result = Code_Legal_Refused of wire_refusal |
  Code_Legal_Ready of
    unit wire_native_call_ext * code_legal_stage * unit code_legal_fields_ext *
      nat list;

datatype 'a code_enforcement_fields_ext =
  Code_enforcement_fields_ext of
    nat * nat * nat * nat set * (nat * nat) option * nat option * 'a;

datatype 'a code_spend_fields_ext =
  Code_spend_fields_ext of
    nat * nat * nat * nat * nat * unit code_enforcement_fields_ext option *
      (nat list) option * 'a;

datatype code_spend_result = Code_Spend_Refused of wire_refusal |
  Code_Spend_Ready of unit wire_native_call_ext * unit code_spend_fields_ext;

datatype code_source_spend_reply = Code_Source_Spend_Executed of nat |
  Code_Source_Spend_Rejected | Code_Source_Spend_Busy |
  Code_Source_Spend_Unavailable;

datatype code_source_legal_reply = Code_Source_Legal_Emitted of nat |
  Code_Source_Legal_Applied of nat | Code_Source_Legal_Blocked of legal_refusal
  | Code_Source_Legal_Busy | Code_Source_Legal_Unavailable;

datatype code_source_accepted_reply = Code_Source_Rejected_Reply |
  Code_Source_Busy_Reply | Code_Source_Reserved_Reply |
  Code_Source_Dispatched_Reply | Code_Source_Debited_Reply |
  Code_Source_Closed_Reply | Code_Source_Preempted_Reply |
  Code_Source_Time_Reply | Code_Source_Recorded_Reply |
  Code_Source_Credited_Reply | Code_Source_Reconciled_Reply |
  Code_Source_Refunded_Reply | Code_Source_Data_Reply |
  Code_Source_Evidence_Reply | Code_Source_Published_Reply;

datatype code_source_outcome_reply =
  Code_Source_Accepted of code_source_accepted_reply |
  Code_Source_Duplicate_Decision | Code_Source_Duplicate_Confirmed |
  Code_Source_Duplicate_Reversed | Code_Source_Outcome_Rejected |
  Code_Source_Outcome_Busy | Code_Source_Outcome_Unavailable;

datatype 'a code_source_outcome_ext =
  Code_source_outcome_ext of code_source_outcome_reply * nat option * 'a;

datatype code_source_collection =
  Code_Source_Collected of unit code_source_outcome_ext |
  Code_Source_Collection_Waiting | Code_Source_Collection_Rejected;

datatype code_source_receipt =
  Code_Source_Ordinary_Receipt of code_source_collection |
  Code_Source_Legal_Receipt of code_source_legal_reply |
  Code_Source_Spend_Receipt of code_source_spend_reply;

datatype code_operand_tree_result = Code_Tree_Refused of wire_refusal |
  Code_Tree_Ready of code_nested_operand | Code_Tree_Pending;

datatype code_heartbeat_fields =
  Code_Capabilities of nat * nat * nat set * nat set * nat set * nat set |
  Code_Liveness of nat * nat;

datatype code_source_resolution = Code_Source_Resolution_Rejected |
  Code_Source_Resolution_Published of code_source_receipt |
  Code_Source_Resolution_Unresolved;

datatype code_source_recovery_error = Code_Source_Publication_Unsupported |
  Code_Source_Publication_Deadline | Code_Source_Publication_TTL |
  Code_Source_Publication_Cancelled | Code_Source_Recovery_Endpoint_Rejected |
  Code_Source_Recovery_Endpoint_Unavailable | Code_Source_Recovery_Hold |
  Code_Source_Recovery_Other of nat;

datatype code_source_wire_error = Code_Source_Wire_Validation of wire_refusal |
  Code_Source_Wire_Product_Rejected | Code_Source_Wire_Cancelled |
  Code_Source_Wire_Deadline | Code_Source_Wire_Response_Lost |
  Code_Source_Wire_Unresolved |
  Code_Source_Wire_Recovery of code_source_recovery_error;

datatype response_v061_sender_stage = Response_V061_Plan | Response_V061_Prefix
  | Response_V061_Emit;

datatype code_source_action_reply =
  Code_Source_Ordinary_Collected of unit code_source_outcome_ext |
  Code_Source_Ordinary_Waiting | Code_Source_Ordinary_Busy |
  Code_Source_Ordinary_Unavailable | Code_Source_Ordinary_Rejected |
  Code_Source_Legal_Action of code_source_legal_reply |
  Code_Source_Spend_Action of code_source_spend_reply |
  Code_Source_Other_Action;

datatype 'a code_json_endpoint_context_ext =
  Code_json_endpoint_context_ext of
    nat * nat * (nat * (nat * nat)) list * (nat * nat list) list *
      (nat * (nat * nat)) list * 'a;

datatype 'a code_json_session_binding_ext =
  Code_json_session_binding_ext of nat * nat * 'a;

datatype code_governance_fields =
  Code_Governance_Handover of
    nat * unit product_cut_ext * nat * nat * nat * nat * nat * nat *
      unit code_json_endpoint_context_ext list * nat list * nat list
  | Code_Governance_Install of
      nat * unit product_cut_ext * nat *
        unit code_json_endpoint_context_ext list *
        (nat * unit code_json_session_binding_ext) list * nat list;

datatype response_fixed_observation =
  Response_Fixed_Received of
    code_source_action_reply * code_source_receipt option
  | Response_Fixed_Resolved of code_source_resolution |
  Response_Fixed_Error of code_source_wire_error;

datatype response_v061_observation =
  Response_V061_Legacy of response_fixed_observation |
  Response_V061_Sync of sync_outcome * sync_outcome option;

datatype response_fixed_encoding_error =
  Response_Fixed_Encoding_Refused of wire_refusal |
  Response_Fixed_Signature_Unavailable;

datatype 'a response_fixed_site_ext =
  Response_fixed_site_ext of
    (nat * (nat * nat)) * unit option * (nat * (nat * nat)) option * 'a;

datatype 'a native_scheduled_ack_ext =
  Native_scheduled_ack_ext of
    ((nat * nat) * nat) * nat * nat * nat * nat * nat * nat * nat *
      terminal_kind * 'a;

datatype 'a response_fixed_channel_ext =
  Response_fixed_channel_ext of
    unit negotiated_wire_profile_ext * nat * nat * nat * nat * nat list *
      nat list * 'a;

datatype 'a response_fixed_config_ext =
  Response_fixed_config_ext of
    nat * nat set * (nat * nat list) set * nat * nat * nat * nat * nat * nat *
      nat list * nat list * 'a;

datatype 'a response_fixed_decoded_ext =
  Response_fixed_decoded_ext of
    (nat * nat) * reference_response_kind * nat * nat option * nat list *
      unit wire_core_ext * 'a;

datatype 'a response_fixed_parameters_ext =
  Response_fixed_parameters_ext of
    nat * nat * nat * nat * nat * nat list * nat * 'a;

datatype 'a response_fixed_emission_ext =
  Response_fixed_emission_ext of
    nat list * unit wire_packet_ext * unit wire_core_ext *
      ((nat * nat) * (reference_response_kind * (nat * nat option))) *
      ((nat * nat) * (reference_response_kind * (nat * nat option))) *
      unit response_fixed_parameters_ext * nat list * nat list * 'a;

datatype 'a code_response_full_context_ext =
  Code_response_full_context_ext of
    unit response_fixed_config_ext * unit response_fixed_channel_ext *
      unit response_fixed_site_ext * nat option * nat option * nat * 'a;

datatype 'a response_fixed_client_boundary_ext =
  Response_fixed_client_boundary_ext of
    unit wire_boundary_ext * nat list * nat * 'a;

fun id x = (fn xa => xa) x;

fun suc n = plus_nata n one_nata;

fun nth (x :: xs) n =
  (if equal_nata n zero_nata then x else nth xs (minus_nata n one_nata));

fun fold f [] s = s
  | fold f (x :: xs) s = fold f xs (f x s);

fun rev xs = fold (fn a => fn b => a :: b) xs [];

fun zip [] ys = []
  | zip xs [] = []
  | zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys;

fun drop n [] = []
  | drop n (x :: xs) =
    (if equal_nata n zero_nata then x :: xs
      else drop (minus_nata n one_nata) xs);

fun find uu [] = NONE
  | find p (x :: xs) = (if p x then SOME x else find p xs);

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun null [] = true
  | null (x :: xs) = false;

fun take n [] = []
  | take n (x :: xs) =
    (if equal_nata n zero_nata then []
      else x :: take (minus_nata n one_nata) xs);

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun image f (Set xs) = Set (map f xs);

fun foldr f [] = id
  | foldr f (x :: xs) = f x o foldr f xs;

fun map_of A_ [] k = NONE
  | map_of A_ ((l, v) :: ps) k = (if eq A_ l k then SOME v else map_of A_ ps k);

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun inserta A_ x xs = (if membera A_ xs x then xs else x :: xs);

fun insert A_ x (Set xs) = Set (inserta A_ x xs)
  | insert A_ x (Coset xs) = Coset (removeAll A_ x xs);

fun member A_ x (Set xs) = membera A_ xs x
  | member A_ x (Coset xs) = not (membera A_ xs x);

fun concat xss = foldr (fn a => fn b => a @ b) xss [];

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun bind NONE f = NONE
  | bind (SOME x) f = f x;

fun hd (x21 :: x22) = x21;

fun tl [] = []
  | tl (x21 :: x22) = x22;

fun distinct A_ [] = true
  | distinct A_ (x :: xs) = not (membera A_ xs x) andalso distinct A_ xs;

fun replicate n x =
  (if equal_nata n zero_nata then []
    else x :: replicate (minus_nata n one_nata) x);

fun is_none NONE = true
  | is_none (SOME x) = false;

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

fun sorted_wrt p [] = true
  | sorted_wrt p (x :: ys) = list_all (p x) ys andalso sorted_wrt p ys;

fun list_update [] i y = []
  | list_update (x :: xs) i y =
    (if equal_nata i zero_nata then y :: xs
      else x :: list_update xs (minus_nata i one_nata) y);

fun map_sum f1 f2 (Inl a) = Inl (f1 a)
  | map_sum f1 f2 (Inr a) = Inr (f2 a);

fun length_tailrec [] n = n
  | length_tailrec (x :: xs) n = length_tailrec xs (suc n);

fun abort_empty_set _ = raise Fail "List.abort_empty_set";

fun wire_deadline
  (Wire_body_ext (wire_opcode, wire_words, wire_blobs, wire_deadline, more)) =
  wire_deadline;

fun wire_opcode
  (Wire_body_ext (wire_opcode, wire_words, wire_blobs, wire_deadline, more)) =
  wire_opcode;

fun wire_words
  (Wire_body_ext (wire_opcode, wire_words, wire_blobs, wire_deadline, more)) =
  wire_words;

fun wire_blobs
  (Wire_body_ext (wire_opcode, wire_words, wire_blobs, wire_deadline, more)) =
  wire_blobs;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun deadline_fields Deadline_Absent = []
  | deadline_fields Deadline_Indefinite =
    [Proto_Varint (nat_of_integer (4 : IntInf.int), one_nata)]
  | deadline_fields (Deadline_At seconds) =
    [Proto_Fixed64 (nat_of_integer (5 : IntInf.int), seconds)];

fun body_fields body =
  Proto_Varint (one_nata, wire_opcode body) ::
    map (fn a => Proto_Fixed64 (nat_of_integer (2 : IntInf.int), a))
      (wire_words body) @
      map (fn a => Proto_Bytes (nat_of_integer (3 : IntInf.int), a))
        (wire_blobs body) @
        deadline_fields (wire_deadline body);

fun wire_signature_scheme
  (Wire_core_ext
    (wire_version, wire_purpose, wire_deployment, wire_source_domain,
      wire_target_domain, wire_principal, wire_key_number, wire_authority_epoch,
      wire_sent_seconds, wire_ttl_seconds, wire_uuid, wire_message_family,
      wire_primary_code, wire_secondary_code, wire_signature_scheme,
      wire_operation_body, wire_atomicity, wire_priority, wire_route_scope,
      more))
  = wire_signature_scheme;

fun wire_authority_epoch
  (Wire_core_ext
    (wire_version, wire_purpose, wire_deployment, wire_source_domain,
      wire_target_domain, wire_principal, wire_key_number, wire_authority_epoch,
      wire_sent_seconds, wire_ttl_seconds, wire_uuid, wire_message_family,
      wire_primary_code, wire_secondary_code, wire_signature_scheme,
      wire_operation_body, wire_atomicity, wire_priority, wire_route_scope,
      more))
  = wire_authority_epoch;

fun wire_secondary_code
  (Wire_core_ext
    (wire_version, wire_purpose, wire_deployment, wire_source_domain,
      wire_target_domain, wire_principal, wire_key_number, wire_authority_epoch,
      wire_sent_seconds, wire_ttl_seconds, wire_uuid, wire_message_family,
      wire_primary_code, wire_secondary_code, wire_signature_scheme,
      wire_operation_body, wire_atomicity, wire_priority, wire_route_scope,
      more))
  = wire_secondary_code;

fun wire_operation_body
  (Wire_core_ext
    (wire_version, wire_purpose, wire_deployment, wire_source_domain,
      wire_target_domain, wire_principal, wire_key_number, wire_authority_epoch,
      wire_sent_seconds, wire_ttl_seconds, wire_uuid, wire_message_family,
      wire_primary_code, wire_secondary_code, wire_signature_scheme,
      wire_operation_body, wire_atomicity, wire_priority, wire_route_scope,
      more))
  = wire_operation_body;

fun wire_message_family
  (Wire_core_ext
    (wire_version, wire_purpose, wire_deployment, wire_source_domain,
      wire_target_domain, wire_principal, wire_key_number, wire_authority_epoch,
      wire_sent_seconds, wire_ttl_seconds, wire_uuid, wire_message_family,
      wire_primary_code, wire_secondary_code, wire_signature_scheme,
      wire_operation_body, wire_atomicity, wire_priority, wire_route_scope,
      more))
  = wire_message_family;

fun wire_target_domain
  (Wire_core_ext
    (wire_version, wire_purpose, wire_deployment, wire_source_domain,
      wire_target_domain, wire_principal, wire_key_number, wire_authority_epoch,
      wire_sent_seconds, wire_ttl_seconds, wire_uuid, wire_message_family,
      wire_primary_code, wire_secondary_code, wire_signature_scheme,
      wire_operation_body, wire_atomicity, wire_priority, wire_route_scope,
      more))
  = wire_target_domain;

fun wire_source_domain
  (Wire_core_ext
    (wire_version, wire_purpose, wire_deployment, wire_source_domain,
      wire_target_domain, wire_principal, wire_key_number, wire_authority_epoch,
      wire_sent_seconds, wire_ttl_seconds, wire_uuid, wire_message_family,
      wire_primary_code, wire_secondary_code, wire_signature_scheme,
      wire_operation_body, wire_atomicity, wire_priority, wire_route_scope,
      more))
  = wire_source_domain;

fun wire_sent_seconds
  (Wire_core_ext
    (wire_version, wire_purpose, wire_deployment, wire_source_domain,
      wire_target_domain, wire_principal, wire_key_number, wire_authority_epoch,
      wire_sent_seconds, wire_ttl_seconds, wire_uuid, wire_message_family,
      wire_primary_code, wire_secondary_code, wire_signature_scheme,
      wire_operation_body, wire_atomicity, wire_priority, wire_route_scope,
      more))
  = wire_sent_seconds;

fun wire_primary_code
  (Wire_core_ext
    (wire_version, wire_purpose, wire_deployment, wire_source_domain,
      wire_target_domain, wire_principal, wire_key_number, wire_authority_epoch,
      wire_sent_seconds, wire_ttl_seconds, wire_uuid, wire_message_family,
      wire_primary_code, wire_secondary_code, wire_signature_scheme,
      wire_operation_body, wire_atomicity, wire_priority, wire_route_scope,
      more))
  = wire_primary_code;

fun wire_ttl_seconds
  (Wire_core_ext
    (wire_version, wire_purpose, wire_deployment, wire_source_domain,
      wire_target_domain, wire_principal, wire_key_number, wire_authority_epoch,
      wire_sent_seconds, wire_ttl_seconds, wire_uuid, wire_message_family,
      wire_primary_code, wire_secondary_code, wire_signature_scheme,
      wire_operation_body, wire_atomicity, wire_priority, wire_route_scope,
      more))
  = wire_ttl_seconds;

fun wire_route_scope
  (Wire_core_ext
    (wire_version, wire_purpose, wire_deployment, wire_source_domain,
      wire_target_domain, wire_principal, wire_key_number, wire_authority_epoch,
      wire_sent_seconds, wire_ttl_seconds, wire_uuid, wire_message_family,
      wire_primary_code, wire_secondary_code, wire_signature_scheme,
      wire_operation_body, wire_atomicity, wire_priority, wire_route_scope,
      more))
  = wire_route_scope;

fun wire_key_number
  (Wire_core_ext
    (wire_version, wire_purpose, wire_deployment, wire_source_domain,
      wire_target_domain, wire_principal, wire_key_number, wire_authority_epoch,
      wire_sent_seconds, wire_ttl_seconds, wire_uuid, wire_message_family,
      wire_primary_code, wire_secondary_code, wire_signature_scheme,
      wire_operation_body, wire_atomicity, wire_priority, wire_route_scope,
      more))
  = wire_key_number;

fun wire_deployment
  (Wire_core_ext
    (wire_version, wire_purpose, wire_deployment, wire_source_domain,
      wire_target_domain, wire_principal, wire_key_number, wire_authority_epoch,
      wire_sent_seconds, wire_ttl_seconds, wire_uuid, wire_message_family,
      wire_primary_code, wire_secondary_code, wire_signature_scheme,
      wire_operation_body, wire_atomicity, wire_priority, wire_route_scope,
      more))
  = wire_deployment;

fun wire_principal
  (Wire_core_ext
    (wire_version, wire_purpose, wire_deployment, wire_source_domain,
      wire_target_domain, wire_principal, wire_key_number, wire_authority_epoch,
      wire_sent_seconds, wire_ttl_seconds, wire_uuid, wire_message_family,
      wire_primary_code, wire_secondary_code, wire_signature_scheme,
      wire_operation_body, wire_atomicity, wire_priority, wire_route_scope,
      more))
  = wire_principal;

fun wire_atomicity
  (Wire_core_ext
    (wire_version, wire_purpose, wire_deployment, wire_source_domain,
      wire_target_domain, wire_principal, wire_key_number, wire_authority_epoch,
      wire_sent_seconds, wire_ttl_seconds, wire_uuid, wire_message_family,
      wire_primary_code, wire_secondary_code, wire_signature_scheme,
      wire_operation_body, wire_atomicity, wire_priority, wire_route_scope,
      more))
  = wire_atomicity;

fun wire_priority
  (Wire_core_ext
    (wire_version, wire_purpose, wire_deployment, wire_source_domain,
      wire_target_domain, wire_principal, wire_key_number, wire_authority_epoch,
      wire_sent_seconds, wire_ttl_seconds, wire_uuid, wire_message_family,
      wire_primary_code, wire_secondary_code, wire_signature_scheme,
      wire_operation_body, wire_atomicity, wire_priority, wire_route_scope,
      more))
  = wire_priority;

fun wire_version
  (Wire_core_ext
    (wire_version, wire_purpose, wire_deployment, wire_source_domain,
      wire_target_domain, wire_principal, wire_key_number, wire_authority_epoch,
      wire_sent_seconds, wire_ttl_seconds, wire_uuid, wire_message_family,
      wire_primary_code, wire_secondary_code, wire_signature_scheme,
      wire_operation_body, wire_atomicity, wire_priority, wire_route_scope,
      more))
  = wire_version;

fun wire_purpose
  (Wire_core_ext
    (wire_version, wire_purpose, wire_deployment, wire_source_domain,
      wire_target_domain, wire_principal, wire_key_number, wire_authority_epoch,
      wire_sent_seconds, wire_ttl_seconds, wire_uuid, wire_message_family,
      wire_primary_code, wire_secondary_code, wire_signature_scheme,
      wire_operation_body, wire_atomicity, wire_priority, wire_route_scope,
      more))
  = wire_purpose;

fun wire_uuid
  (Wire_core_ext
    (wire_version, wire_purpose, wire_deployment, wire_source_domain,
      wire_target_domain, wire_principal, wire_key_number, wire_authority_epoch,
      wire_sent_seconds, wire_ttl_seconds, wire_uuid, wire_message_family,
      wire_primary_code, wire_secondary_code, wire_signature_scheme,
      wire_operation_body, wire_atomicity, wire_priority, wire_route_scope,
      more))
  = wire_uuid;

fun put_wire_varint n =
  (if less_nat n (nat_of_integer (128 : IntInf.int)) then [n]
    else plus_nata (nat_of_integer (128 : IntInf.int))
           (modulo_nata n (nat_of_integer (128 : IntInf.int))) ::
           put_wire_varint (divide_nata n (nat_of_integer (128 : IntInf.int))));

fun size_list xs = length_tailrec xs zero_nata;

fun put_le_octets width number =
  (if equal_nata width zero_nata then []
    else modulo_nata number (nat_of_integer (256 : IntInf.int)) ::
           put_le_octets (minus_nata width one_nata)
             (divide_nata number (nat_of_integer (256 : IntInf.int))));

fun make_proto_tag number kind =
  plus_nata kind (times_nata number (nat_of_integer (8 : IntInf.int)));

fun put_proto_field (Proto_Varint (number, value)) =
  put_wire_varint (make_proto_tag number zero_nata) @ put_wire_varint value
  | put_proto_field (Proto_Fixed64 (number, value)) =
    put_wire_varint (make_proto_tag number one_nata) @
      put_le_octets (nat_of_integer (8 : IntInf.int)) value
  | put_proto_field (Proto_Bytes (number, bytes)) =
    put_wire_varint (make_proto_tag number (nat_of_integer (2 : IntInf.int))) @
      put_wire_varint (size_list bytes) @ bytes;

fun put_proto_fields fields = maps put_proto_field fields;

fun encode_wire_body body = put_proto_fields (body_fields body);

fun secondary_field value =
  (case value of NONE => []
    | SOME code => [Proto_Varint (nat_of_integer (14 : IntInf.int), code)]);

fun family_number Wire_State_Sync = one_nata
  | family_number Wire_Regulatory = nat_of_integer (2 : IntInf.int)
  | family_number Wire_Lock = nat_of_integer (3 : IntInf.int)
  | family_number Wire_Query = nat_of_integer (4 : IntInf.int)
  | family_number Wire_Ack = nat_of_integer (5 : IntInf.int)
  | family_number Wire_Heartbeat = nat_of_integer (6 : IntInf.int)
  | family_number Wire_Governance = nat_of_integer (7 : IntInf.int);

fun core_fields core =
  [Proto_Varint (one_nata, wire_version core),
    Proto_Varint (nat_of_integer (2 : IntInf.int), wire_purpose core),
    Proto_Fixed64 (nat_of_integer (3 : IntInf.int), wire_deployment core),
    Proto_Fixed64 (nat_of_integer (4 : IntInf.int), wire_source_domain core),
    Proto_Fixed64 (nat_of_integer (5 : IntInf.int), wire_target_domain core),
    Proto_Fixed64 (nat_of_integer (6 : IntInf.int), wire_principal core),
    Proto_Fixed64 (nat_of_integer (7 : IntInf.int), wire_key_number core),
    Proto_Fixed64 (nat_of_integer (8 : IntInf.int), wire_authority_epoch core),
    Proto_Fixed64 (nat_of_integer (9 : IntInf.int), wire_sent_seconds core),
    Proto_Fixed64 (nat_of_integer (10 : IntInf.int), wire_ttl_seconds core),
    Proto_Bytes (nat_of_integer (11 : IntInf.int), wire_uuid core),
    Proto_Varint
      (nat_of_integer (12 : IntInf.int),
        family_number (wire_message_family core)),
    Proto_Varint (nat_of_integer (13 : IntInf.int), wire_primary_code core)] @
    secondary_field (wire_secondary_code core) @
      [Proto_Varint
         (nat_of_integer (15 : IntInf.int), wire_signature_scheme core),
        Proto_Bytes
          (plus_nata (nat_of_integer (15 : IntInf.int))
             (family_number (wire_message_family core)),
            encode_wire_body (wire_operation_body core)),
        Proto_Varint (nat_of_integer (23 : IntInf.int), wire_atomicity core),
        Proto_Varint (nat_of_integer (24 : IntInf.int), wire_priority core),
        Proto_Fixed64
          (nat_of_integer (25 : IntInf.int), wire_route_scope core)];

fun of_bool A_ false = zero (zero_zero_neq_one A_)
  | of_bool A_ true = one (one_zero_neq_one A_);

fun integer_of_char (Chara (b0, b1, b2, b3, b4, b5, b6, b7)) =
  IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (IntInf.+ (IntInf.* (of_bool
                        zero_neq_one_integer
                        b7, (2 : IntInf.int)), of_bool zero_neq_one_integer
         b6), (2 : IntInf.int)), of_bool zero_neq_one_integer
                                   b5), (2 : IntInf.int)), of_bool
                     zero_neq_one_integer
                     b4), (2 : IntInf.int)), of_bool zero_neq_one_integer
       b3), (2 : IntInf.int)), of_bool zero_neq_one_integer
                                 b2), (2 : IntInf.int)), of_bool
                   zero_neq_one_integer
                   b1), (2 : IntInf.int)), of_bool zero_neq_one_integer b0);

fun min A_ a b = (if less_eq A_ a b then a else b);

fun power A_ a n =
  (if equal_nata n zero_nata then one (one_power A_)
    else times (times_power A_) a (power A_ a (minus_nata n one_nata)));

fun map_option f NONE = NONE
  | map_option f (SOME x2) = SOME (f x2);

val bot_set : 'a set = Set [];

fun sup_set A_ (Set xs) a = fold (insert A_) xs a
  | sup_set A_ (Coset xs) a = Coset (filter (fn x => not (member A_ x a)) xs);

fun numeral A_ One = one (one_numeral A_)
  | numeral A_ (Bit0 n) =
    let
      val m = numeral A_ n;
    in
      plus ((plus_semigroup_add o semigroup_add_numeral) A_) m m
    end
  | numeral A_ (Bit1 n) =
    let
      val m = numeral A_ n;
    in
      plus ((plus_semigroup_add o semigroup_add_numeral) A_)
        (plus ((plus_semigroup_add o semigroup_add_numeral) A_) m m)
        (one (one_numeral A_))
    end;

fun wire_octets (A1_, A2_) bytes =
  list_all
    (fn b =>
      less A2_ b
        (numeral A1_
          (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))))
    bytes;

fun packet_signature (Wire_packet_ext (packet_core, packet_signature, more)) =
  packet_signature;

fun packet_core (Wire_packet_ext (packet_core, packet_signature, more)) =
  packet_core;

fun encode_wire_core core = put_proto_fields (core_fields core);

fun packet_fields packet =
  [Proto_Bytes (one_nata, encode_wire_core (packet_core packet)),
    Proto_Bytes (nat_of_integer (2 : IntInf.int), packet_signature packet)];

fun take_wire_varint [] = NONE
  | take_wire_varint (byte :: tail) =
    (if less_nat byte (nat_of_integer (128 : IntInf.int)) then SOME (byte, tail)
      else (if less_nat byte (nat_of_integer (256 : IntInf.int))
             then map_option
                    (fn (n, a) =>
                      (plus_nata
                         (minus_nata byte (nat_of_integer (128 : IntInf.int)))
                         (times_nata (nat_of_integer (128 : IntInf.int)) n),
                        a))
                    (take_wire_varint tail)
             else NONE));

fun get_le_octets [] = zero_nata
  | get_le_octets (byte :: tail) =
    plus_nata byte
      (times_nata (nat_of_integer (256 : IntInf.int)) (get_le_octets tail));

fun take_proto_field bytes =
  (case take_wire_varint bytes of NONE => NONE
    | SOME (tag, tail) =>
      let
        val number = divide_nata tag (nat_of_integer (8 : IntInf.int));
        val kind = modulo_nata tag (nat_of_integer (8 : IntInf.int));
      in
        (if equal_nata number zero_nata orelse
              less_eq_nat
                (power power_nat (nat_of_integer (2 : IntInf.int))
                  (nat_of_integer (29 : IntInf.int)))
                number
          then NONE
          else (if equal_nata kind zero_nata
                 then (case take_wire_varint tail of NONE => NONE
                        | SOME (value, rest) =>
                          (if less_nat value
                                (power power_nat
                                  (nat_of_integer (2 : IntInf.int))
                                  (nat_of_integer (64 : IntInf.int)))
                            then SOME (Proto_Varint (number, value), rest)
                            else NONE))
                 else (if equal_nata kind one_nata
                        then (if less_eq_nat (nat_of_integer (8 : IntInf.int))
                                   (size_list tail) andalso
                                   wire_octets (numeral_nat, ord_nat)
                                     (take (nat_of_integer (8 : IntInf.int))
                                       tail)
                               then SOME (Proto_Fixed64
    (number, get_le_octets (take (nat_of_integer (8 : IntInf.int)) tail)),
   drop (nat_of_integer (8 : IntInf.int)) tail)
                               else NONE)
                        else (if equal_nata kind
                                   (nat_of_integer (2 : IntInf.int))
                               then (case take_wire_varint tail of NONE => NONE
                                      | SOME (count, rest) =>
(if less_eq_nat count (size_list rest) andalso
      wire_octets (numeral_nat, ord_nat) (take count rest)
  then SOME (Proto_Bytes (number, take count rest), drop count rest) else NONE))
                               else NONE))))
      end);

fun take_proto_fields fuel bytes =
  (if null bytes then SOME []
    else (if equal_nata fuel zero_nata then NONE
           else (case take_proto_field bytes of NONE => NONE
                  | SOME (field, rest) =>
                    map_option (fn a => field :: a)
                      (take_proto_fields (minus_nata fuel one_nata) rest))));

fun read_canonical_proto_fields bytes =
  (case take_proto_fields (size_list bytes) bytes of NONE => NONE
    | SOME fields =>
      (if equal_lista equal_nat (put_proto_fields fields) bytes then SOME fields
        else NONE));

fun parse_deadline_fields [] = SOME Deadline_Absent
  | parse_deadline_fields [Proto_Varint (tag, value)] =
    (if equal_nata tag (nat_of_integer (4 : IntInf.int)) andalso
          equal_nata value one_nata
      then SOME Deadline_Indefinite else NONE)
  | parse_deadline_fields [Proto_Fixed64 (tag, seconds)] =
    (if equal_nata tag (nat_of_integer (5 : IntInf.int))
      then SOME (Deadline_At seconds) else NONE)
  | parse_deadline_fields (Proto_Fixed64 (vb, vc) :: v :: vd) = NONE
  | parse_deadline_fields (Proto_Bytes (vb, vc) :: va) = NONE
  | parse_deadline_fields (v :: vb :: vc) = NONE;

fun consume_body_words (Proto_Fixed64 (tag, value) :: rest) =
  (if equal_nata tag (nat_of_integer (2 : IntInf.int))
    then let
           val (values, a) = consume_body_words rest;
         in
           (value :: values, a)
         end
    else ([], Proto_Fixed64 (tag, value) :: rest))
  | consume_body_words [] = ([], [])
  | consume_body_words (Proto_Varint (vb, vc) :: va) =
    ([], Proto_Varint (vb, vc) :: va)
  | consume_body_words (Proto_Bytes (vb, vc) :: va) =
    ([], Proto_Bytes (vb, vc) :: va);

fun consume_body_blobs (Proto_Bytes (tag, bytes) :: rest) =
  (if equal_nata tag (nat_of_integer (3 : IntInf.int))
    then let
           val (values, a) = consume_body_blobs rest;
         in
           (bytes :: values, a)
         end
    else ([], Proto_Bytes (tag, bytes) :: rest))
  | consume_body_blobs [] = ([], [])
  | consume_body_blobs (Proto_Varint (vb, vc) :: va) =
    ([], Proto_Varint (vb, vc) :: va)
  | consume_body_blobs (Proto_Fixed64 (vb, vc) :: va) =
    ([], Proto_Fixed64 (vb, vc) :: va);

fun parse_body_fields (Proto_Varint (tag, operation) :: tail) =
  (if equal_nata tag one_nata
    then let
           val (words, remainder) = consume_body_words tail;
           val (blobs, ending) = consume_body_blobs remainder;
         in
           map_option
             (fn deadline =>
               Wire_body_ext (operation, words, blobs, deadline, ()))
             (parse_deadline_fields ending)
         end
    else NONE)
  | parse_body_fields [] = NONE
  | parse_body_fields (Proto_Fixed64 (vb, vc) :: va) = NONE
  | parse_body_fields (Proto_Bytes (vb, vc) :: va) = NONE;

fun decode_wire_body bytes =
  (case read_canonical_proto_fields bytes of NONE => NONE
    | SOME items =>
      (case parse_body_fields items of NONE => NONE
        | SOME body =>
          (if equal_lista equal_nat (encode_wire_body body) bytes then SOME body
            else NONE)));

fun interval (A1_, A2_) a b =
  (if less ((ord_preorder o preorder_order o order_linorder o linorder_interval)
             A2_)
        a b
    then a :: interval (A1_, A2_)
                (plus ((plus_semigroup_add o semigroup_add_numeral o
                         numeral_semiring_numeral o
                         semiring_numeral_semiring_1 o
                         semiring_1_comm_semiring_1 o
                         comm_semiring_1_comm_semiring_1_cancel o
                         comm_semiring_1_cancel_interval)
                        A2_)
                  a (one ((one_numeral o numeral_semiring_numeral o
                            semiring_numeral_semiring_1 o
                            semiring_1_comm_semiring_1 o
                            comm_semiring_1_comm_semiring_1_cancel o
                            comm_semiring_1_cancel_interval)
                           A2_)))
                b
    else (if eq A1_ a b then [a] else []));

fun atLeastAtMost (A1_, A2_) a b = Set (interval (A1_, A2_) a b);

fun wellformed_proto_field (Proto_Varint (number, value)) =
  less_nat zero_nata number andalso
    (less_nat number
       (power power_nat (nat_of_integer (2 : IntInf.int))
         (nat_of_integer (29 : IntInf.int))) andalso
      less_nat value
        (power power_nat (nat_of_integer (2 : IntInf.int))
          (nat_of_integer (64 : IntInf.int))))
  | wellformed_proto_field (Proto_Fixed64 (number, value)) =
    less_nat zero_nata number andalso
      (less_nat number
         (power power_nat (nat_of_integer (2 : IntInf.int))
           (nat_of_integer (29 : IntInf.int))) andalso
        less_nat value
          (power power_nat (nat_of_integer (256 : IntInf.int))
            (nat_of_integer (8 : IntInf.int))))
  | wellformed_proto_field (Proto_Bytes (number, bytes)) =
    less_nat zero_nata number andalso
      (less_nat number
         (power power_nat (nat_of_integer (2 : IntInf.int))
           (nat_of_integer (29 : IntInf.int))) andalso
        wire_octets (numeral_nat, ord_nat) bytes);

fun wire_body_wellformed body =
  list_all wellformed_proto_field (body_fields body);

fun valid_family_opcode Wire_State_Sync operation =
  member equal_nat operation
    (atLeastAtMost (equal_nat, interval_nat) one_nata
      (nat_of_integer (6 : IntInf.int)))
  | valid_family_opcode Wire_Regulatory operation =
    member equal_nat operation
      (atLeastAtMost (equal_nat, interval_nat) one_nata
        (nat_of_integer (3 : IntInf.int)))
  | valid_family_opcode Wire_Lock operation =
    member equal_nat operation
      (atLeastAtMost (equal_nat, interval_nat) one_nata
        (nat_of_integer (8 : IntInf.int)))
  | valid_family_opcode Wire_Query operation =
    member equal_nat operation
      (atLeastAtMost (equal_nat, interval_nat) one_nata
        (nat_of_integer (8 : IntInf.int)))
  | valid_family_opcode Wire_Ack operation =
    member equal_nat operation
      (insert equal_nat one_nata
        (insert equal_nat (nat_of_integer (2 : IntInf.int)) bot_set))
  | valid_family_opcode Wire_Heartbeat operation =
    member equal_nat operation
      (insert equal_nat one_nata
        (insert equal_nat (nat_of_integer (2 : IntInf.int)) bot_set))
  | valid_family_opcode Wire_Governance operation =
    member equal_nat operation
      (insert equal_nat one_nata
        (insert equal_nat (nat_of_integer (2 : IntInf.int)) bot_set));

fun wire_core_wellformed core =
  equal_nata (size_list (wire_uuid core))
    (nat_of_integer (16 : IntInf.int)) andalso
    (equal_nata
       (divide_nata (nth (wire_uuid core) (nat_of_integer (6 : IntInf.int)))
         (nat_of_integer (16 : IntInf.int)))
       (nat_of_integer (4 : IntInf.int)) andalso
      (equal_nata
         (divide_nata (nth (wire_uuid core) (nat_of_integer (8 : IntInf.int)))
           (nat_of_integer (64 : IntInf.int)))
         (nat_of_integer (2 : IntInf.int)) andalso
        (member equal_nat (wire_primary_code core)
           (atLeastAtMost (equal_nat, interval_nat) one_nata
             (nat_of_integer (5 : IntInf.int))) andalso
          (member equal_nat (wire_signature_scheme core)
             (insert equal_nat one_nata
               (insert equal_nat (nat_of_integer (2 : IntInf.int))
                 bot_set)) andalso
            (member equal_nat (wire_atomicity core)
               (atLeastAtMost (equal_nat, interval_nat) one_nata
                 (nat_of_integer (3 : IntInf.int))) andalso
              (less_eq_nat (wire_priority core)
                 (nat_of_integer (4 : IntInf.int)) andalso
                ((if equal_nata (wire_priority core) zero_nata
                   then equal_nata (wire_atomicity core)
                          (nat_of_integer (3 : IntInf.int))
                   else true) andalso
                  (valid_family_opcode (wire_message_family core)
                     (wire_opcode (wire_operation_body core)) andalso
                    (wire_body_wellformed (wire_operation_body core) andalso
                      list_all wellformed_proto_field
                        (core_fields core))))))))));

fun parse_secondary_field (Proto_Varint (tag, code) :: tail) =
  (if equal_nata tag (nat_of_integer (14 : IntInf.int)) then (SOME code, tail)
    else (NONE, Proto_Varint (tag, code) :: tail))
  | parse_secondary_field [] = (NONE, [])
  | parse_secondary_field (Proto_Fixed64 (vb, vc) :: va) =
    (NONE, Proto_Fixed64 (vb, vc) :: va)
  | parse_secondary_field (Proto_Bytes (vb, vc) :: va) =
    (NONE, Proto_Bytes (vb, vc) :: va);

fun family_at_number number =
  find (fn family => equal_nata (family_number family) number)
    [Wire_State_Sync, Wire_Regulatory, Wire_Lock, Wire_Query, Wire_Ack,
      Wire_Heartbeat, Wire_Governance];

fun parse_core_body_tail kind items =
  (case parse_secondary_field items of (_, []) => NONE
    | (_, [Proto_Varint (_, _)]) => NONE
    | (_, Proto_Varint (_, _) :: Proto_Varint (_, _) :: _) => NONE
    | (_, Proto_Varint (_, _) :: Proto_Fixed64 (_, _) :: _) => NONE
    | (_, [Proto_Varint (_, _), Proto_Bytes (_, _)]) => NONE
    | (_, [Proto_Varint (_, _), Proto_Bytes (_, _), Proto_Varint (_, _)]) =>
      NONE
    | (_, [Proto_Varint (_, _), Proto_Bytes (_, _), Proto_Varint (_, _),
            Proto_Varint (_, _)])
      => NONE
    | (_, Proto_Varint (_, _) ::
            Proto_Bytes (_, _) ::
              Proto_Varint (_, _) ::
                Proto_Varint (_, _) :: Proto_Varint (_, _) :: _)
      => NONE
    | (secondary,
        [Proto_Varint (scheme_tag, scheme), Proto_Bytes (body_tag, raw),
          Proto_Varint (atomicity_tag, atomicity),
          Proto_Varint (priority_tag, priority),
          Proto_Fixed64 (scope_tag, scope)])
      => (if equal_nata scheme_tag (nat_of_integer (15 : IntInf.int)) andalso
               (equal_nata body_tag
                  (plus_nata (nat_of_integer (15 : IntInf.int)) kind) andalso
                 (member equal_nat scheme
                    (insert equal_nat one_nata
                      (insert equal_nat (nat_of_integer (2 : IntInf.int))
                        bot_set)) andalso
                   (equal_nata atomicity_tag
                      (nat_of_integer (23 : IntInf.int)) andalso
                     (equal_nata priority_tag
                        (nat_of_integer (24 : IntInf.int)) andalso
                       equal_nata scope_tag
                         (nat_of_integer (25 : IntInf.int))))))
           then (case (family_at_number kind, decode_wire_body raw)
                  of (NONE, _) => NONE | (SOME _, NONE) => NONE
                  | (SOME family, SOME body) =>
                    (if valid_family_opcode family (wire_opcode body)
                      then SOME (secondary,
                                  (scheme,
                                    (family,
                                      (body, (atomicity, (priority, scope))))))
                      else NONE))
           else NONE)
    | (_, Proto_Varint (_, _) ::
            Proto_Bytes (_, _) ::
              Proto_Varint (_, _) ::
                Proto_Varint (_, _) :: Proto_Fixed64 (_, _) :: _ :: _)
      => NONE
    | (_, Proto_Varint (_, _) ::
            Proto_Bytes (_, _) ::
              Proto_Varint (_, _) ::
                Proto_Varint (_, _) :: Proto_Bytes (_, _) :: _)
      => NONE
    | (_, Proto_Varint (_, _) ::
            Proto_Bytes (_, _) ::
              Proto_Varint (_, _) :: Proto_Fixed64 (_, _) :: _)
      => NONE
    | (_, Proto_Varint (_, _) ::
            Proto_Bytes (_, _) ::
              Proto_Varint (_, _) :: Proto_Bytes (_, _) :: _)
      => NONE
    | (_, Proto_Varint (_, _) ::
            Proto_Bytes (_, _) :: Proto_Fixed64 (_, _) :: _)
      => NONE
    | (_, Proto_Varint (_, _) :: Proto_Bytes (_, _) :: Proto_Bytes (_, _) :: _)
      => NONE
    | (_, Proto_Fixed64 (_, _) :: _) => NONE
    | (_, Proto_Bytes (_, _) :: _) => NONE);

fun expect_proto_fixed64 expected (Proto_Fixed64 (tag, value)) =
  (if equal_nata tag expected then SOME value else NONE)
  | expect_proto_fixed64 expected (Proto_Varint (v, va)) = NONE
  | expect_proto_fixed64 expected (Proto_Bytes (v, va)) = NONE;

fun expect_proto_varint expected (Proto_Varint (tag, value)) =
  (if equal_nata tag expected then SOME value else NONE)
  | expect_proto_varint expected (Proto_Fixed64 (v, va)) = NONE
  | expect_proto_varint expected (Proto_Bytes (v, va)) = NONE;

fun expect_proto_bytes expected (Proto_Bytes (tag, value)) =
  (if equal_nata tag expected then SOME value else NONE)
  | expect_proto_bytes expected (Proto_Varint (v, va)) = NONE
  | expect_proto_bytes expected (Proto_Fixed64 (v, va)) = NONE;

fun parse_core_fields items =
  (if less_nat (size_list items) (nat_of_integer (13 : IntInf.int)) then NONE
    else bind (expect_proto_varint one_nata (nth items zero_nata))
           (fn version =>
             bind (expect_proto_varint (nat_of_integer (2 : IntInf.int))
                    (nth items one_nata))
               (fn purpose =>
                 bind (expect_proto_fixed64 (nat_of_integer (3 : IntInf.int))
                        (nth items (nat_of_integer (2 : IntInf.int))))
                   (fn deployment =>
                     bind (expect_proto_fixed64
                            (nat_of_integer (4 : IntInf.int))
                            (nth items (nat_of_integer (3 : IntInf.int))))
                       (fn source =>
                         bind (expect_proto_fixed64
                                (nat_of_integer (5 : IntInf.int))
                                (nth items (nat_of_integer (4 : IntInf.int))))
                           (fn target =>
                             bind (expect_proto_fixed64
                                    (nat_of_integer (6 : IntInf.int))
                                    (nth items
                                      (nat_of_integer (5 : IntInf.int))))
                               (fn who =>
                                 bind (expect_proto_fixed64
(nat_of_integer (7 : IntInf.int)) (nth items (nat_of_integer (6 : IntInf.int))))
                                   (fn key =>
                                     bind (expect_proto_fixed64
    (nat_of_integer (8 : IntInf.int))
    (nth items (nat_of_integer (7 : IntInf.int))))
                                       (fn epoch =>
 bind (expect_proto_fixed64 (nat_of_integer (9 : IntInf.int))
        (nth items (nat_of_integer (8 : IntInf.int))))
   (fn sent =>
     bind (expect_proto_fixed64 (nat_of_integer (10 : IntInf.int))
            (nth items (nat_of_integer (9 : IntInf.int))))
       (fn ttl =>
         bind (expect_proto_bytes (nat_of_integer (11 : IntInf.int))
                (nth items (nat_of_integer (10 : IntInf.int))))
           (fn uuid =>
             bind (expect_proto_varint (nat_of_integer (12 : IntInf.int))
                    (nth items (nat_of_integer (11 : IntInf.int))))
               (fn kind =>
                 bind (expect_proto_varint (nat_of_integer (13 : IntInf.int))
                        (nth items (nat_of_integer (12 : IntInf.int))))
                   (fn primary =>
                     map_option
                       (fn (secondary,
                             (scheme,
                               (family,
                                 (body, (atomicity, (priority, scope))))))
                          =>
                         Wire_core_ext
                           (version, purpose, deployment, source, target, who,
                             key, epoch, sent, ttl, uuid, family, primary,
                             secondary, scheme, body, atomicity, priority,
                             scope, ()))
                       (parse_core_body_tail kind
                         (drop (nat_of_integer (13 : IntInf.int))
                           items))))))))))))))));

fun decode_wire_core bytes =
  (case read_canonical_proto_fields bytes of NONE => NONE
    | SOME items =>
      (case parse_core_fields items of NONE => NONE
        | SOME core =>
          (if wire_core_wellformed core andalso
                equal_lista equal_nat (encode_wire_core core) bytes
            then SOME core else NONE)));

fun nat_of_char c = Nat (integer_of_char c);

fun sync_operation core =
  (wire_message_family core, wire_opcode (wire_operation_body core));

fun wire_packet_wellformed packet =
  wire_core_wellformed (packet_core packet) andalso
    (wire_octets (numeral_nat, ord_nat) (packet_signature packet) andalso
      (less_nat (size_list (encode_wire_core (packet_core packet)))
         (power power_nat (nat_of_integer (256 : IntInf.int))
           (nat_of_integer (4 : IntInf.int))) andalso
        (if equal_nata (wire_signature_scheme (packet_core packet)) one_nata
          then equal_nata (size_list (packet_signature packet))
                 (nat_of_integer (64 : IntInf.int))
          else not (null (packet_signature packet)))));

fun encode_wire_packet packet = put_proto_fields (packet_fields packet);

fun decode_wire_packet bytes =
  (case read_canonical_proto_fields bytes of NONE => NONE | SOME [] => NONE
    | SOME (Proto_Varint (_, _) :: _) => NONE
    | SOME (Proto_Fixed64 (_, _) :: _) => NONE
    | SOME [Proto_Bytes (_, _)] => NONE
    | SOME (Proto_Bytes (_, _) :: Proto_Varint (_, _) :: _) => NONE
    | SOME (Proto_Bytes (_, _) :: Proto_Fixed64 (_, _) :: _) => NONE
    | SOME [Proto_Bytes (core_tag, body),
             Proto_Bytes (signature_tag, signaturea)]
      => (if equal_nata core_tag one_nata andalso
               equal_nata signature_tag (nat_of_integer (2 : IntInf.int))
           then (case decode_wire_core body of NONE => NONE
                  | SOME core =>
                    let
                      val packet = Wire_packet_ext (core, signaturea, ());
                    in
                      (if wire_packet_wellformed packet andalso
                            equal_lista equal_nat (encode_wire_packet packet)
                              bytes
                        then SOME packet else NONE)
                    end)
           else NONE)
    | SOME (Proto_Bytes (_, _) :: Proto_Bytes (_, _) :: _ :: _) => NONE);

fun mina A_ (Set []) = abort_empty_set (mina A_)
  | mina A_ (Set (x :: xs)) =
    fold (min ((ord_preorder o preorder_order o order_linorder) A_)) xs x;

fun equal_proto_field (Proto_Fixed64 (x21, x22)) (Proto_Bytes (x31, x32)) =
  false
  | equal_proto_field (Proto_Bytes (x31, x32)) (Proto_Fixed64 (x21, x22)) =
    false
  | equal_proto_field (Proto_Varint (x11, x12)) (Proto_Bytes (x31, x32)) = false
  | equal_proto_field (Proto_Bytes (x31, x32)) (Proto_Varint (x11, x12)) = false
  | equal_proto_field (Proto_Varint (x11, x12)) (Proto_Fixed64 (x21, x22)) =
    false
  | equal_proto_field (Proto_Fixed64 (x21, x22)) (Proto_Varint (x11, x12)) =
    false
  | equal_proto_field (Proto_Bytes (x31, x32)) (Proto_Bytes (y31, y32)) =
    equal_nata x31 y31 andalso equal_lista equal_nat x32 y32
  | equal_proto_field (Proto_Fixed64 (x21, x22)) (Proto_Fixed64 (y21, y22)) =
    equal_nata x21 y21 andalso equal_nata x22 y22
  | equal_proto_field (Proto_Varint (x11, x12)) (Proto_Varint (y11, y12)) =
    equal_nata x11 y11 andalso equal_nata x12 y12;

fun wire_operation_body_update wire_operation_bodya
  (Wire_core_ext
    (wire_version, wire_purpose, wire_deployment, wire_source_domain,
      wire_target_domain, wire_principal, wire_key_number, wire_authority_epoch,
      wire_sent_seconds, wire_ttl_seconds, wire_uuid, wire_message_family,
      wire_primary_code, wire_secondary_code, wire_signature_scheme,
      wire_operation_body, wire_atomicity, wire_priority, wire_route_scope,
      more))
  = Wire_core_ext
      (wire_version, wire_purpose, wire_deployment, wire_source_domain,
        wire_target_domain, wire_principal, wire_key_number,
        wire_authority_epoch, wire_sent_seconds, wire_ttl_seconds, wire_uuid,
        wire_message_family, wire_primary_code, wire_secondary_code,
        wire_signature_scheme, wire_operation_bodya wire_operation_body,
        wire_atomicity, wire_priority, wire_route_scope, more);

fun wire_opcode_update wire_opcodea
  (Wire_body_ext (wire_opcode, wire_words, wire_blobs, wire_deadline, more)) =
  Wire_body_ext
    (wire_opcodea wire_opcode, wire_words, wire_blobs, wire_deadline, more);

fun sync_added_operation core =
  member (equal_prod equal_wire_family equal_nat) (sync_operation core)
    (insert (equal_prod equal_wire_family equal_nat)
      (Wire_State_Sync, nat_of_integer (7 : IntInf.int))
      (insert (equal_prod equal_wire_family equal_nat)
        (Wire_Query, nat_of_integer (9 : IntInf.int)) bot_set));

fun sync_new_body_field (Proto_Bytes (tag, raw)) =
  (if member equal_nat tag
        (insert equal_nat (nat_of_integer (16 : IntInf.int))
          (insert equal_nat (nat_of_integer (19 : IntInf.int)) bot_set))
    then bind (decode_wire_body raw)
           (fn body =>
             (if member (equal_prod equal_nat equal_nat) (tag, wire_opcode body)
                   (insert (equal_prod equal_nat equal_nat)
                     (nat_of_integer (16 : IntInf.int),
                       nat_of_integer (7 : IntInf.int))
                     (insert (equal_prod equal_nat equal_nat)
                       (nat_of_integer (19 : IntInf.int),
                         nat_of_integer (9 : IntInf.int))
                       bot_set))
               then SOME (tag, body) else NONE))
    else NONE)
  | sync_new_body_field (Proto_Varint (v, va)) = NONE
  | sync_new_body_field (Proto_Fixed64 (v, va)) = NONE;

fun sync_parse_new_core wire_items =
  bind (find (fn field => not (is_none (sync_new_body_field field))) wire_items)
    (fn candidate =>
      bind (sync_new_body_field candidate)
        (fn (tag, body) =>
          let
            val alias =
              Proto_Bytes
                (tag, encode_wire_body
                        (wire_opcode_update (fn _ => one_nata) body));
          in
            bind (parse_core_fields
                   (map (fn field =>
                          (if equal_proto_field field candidate then alias
                            else field))
                     wire_items))
              (fn legacy =>
                let
                  val original =
                    wire_operation_body_update (fn _ => body) legacy;
                in
                  (if wire_core_wellformed legacy andalso
                        sync_added_operation original
                    then SOME original else NONE)
                end)
          end));

fun sync_decode_core raw =
  (case decode_wire_core raw
    of NONE =>
      bind (read_canonical_proto_fields raw)
        (fn wire_items =>
          bind (sync_parse_new_core wire_items)
            (fn core =>
              (if equal_lista equal_nat (encode_wire_core core) raw
                then SOME core else NONE)))
    | SOME a => SOME a);

fun equal_sum A_ B_ (Inl x1) (Inr x2) = false
  | equal_sum A_ B_ (Inr x2) (Inl x1) = false
  | equal_sum A_ B_ (Inr x2) (Inr y2) = eq B_ x2 y2
  | equal_sum A_ B_ (Inl x1) (Inl y1) = eq A_ x1 y1;

fun sync_read_query core =
  let
    val body = wire_operation_body core;
  in
    (if not (equal_proda equal_wire_family equal_nat (sync_operation core)
              (Wire_Query, nat_of_integer (9 : IntInf.int))) orelse
          (not (equal_wire_deadline (wire_deadline body) Deadline_Absent) orelse
            not (null (wire_blobs body)))
      then NONE
      else (case wire_words body of [] => NONE | [_] => NONE | [_, _] => NONE
             | [_, _, _] => NONE
             | [session, revision_word, asset, origin] =>
               SOME (Sync_query_ext
                      (session,
                        Product_cut_ext
                          (wire_authority_epoch core, revision_word, ()),
                        (asset, origin), ()))
             | _ :: _ :: _ :: _ :: _ :: _ => NONE))
  end;

fun sync_decode_packet raw =
  (case decode_wire_packet raw
    of NONE =>
      (case read_canonical_proto_fields raw of NONE => NONE | SOME [] => NONE
        | SOME (Proto_Varint (_, _) :: _) => NONE
        | SOME (Proto_Fixed64 (_, _) :: _) => NONE
        | SOME [Proto_Bytes (_, _)] => NONE
        | SOME (Proto_Bytes (_, _) :: Proto_Varint (_, _) :: _) => NONE
        | SOME (Proto_Bytes (_, _) :: Proto_Fixed64 (_, _) :: _) => NONE
        | SOME [Proto_Bytes (core_tag, original),
                 Proto_Bytes (signature_tag, signaturea)]
          => (if equal_nata core_tag one_nata andalso
                   equal_nata signature_tag (nat_of_integer (2 : IntInf.int))
               then bind (sync_decode_core original)
                      (fn core =>
                        let
                          val packet = Wire_packet_ext (core, signaturea, ());
                        in
                          (if sync_added_operation core andalso
                                (less_nat (size_list original)
                                   (power power_nat
                                     (nat_of_integer (256 : IntInf.int))
                                     (nat_of_integer (4 : IntInf.int))) andalso
                                  (wire_octets (numeral_nat, ord_nat)
                                     signaturea andalso
                                    ((if equal_nata (wire_signature_scheme core)
   one_nata
                                       then equal_nata (size_list signaturea)
      (nat_of_integer (64 : IntInf.int))
                                       else not (null signaturea)) andalso
                                      equal_lista equal_nat
(encode_wire_packet packet) raw)))
                            then SOME packet else NONE)
                        end)
               else NONE)
        | SOME (Proto_Bytes (_, _) :: Proto_Bytes (_, _) :: _ :: _) => NONE)
    | SOME a => SOME a);

fun boundary_critical_allowed
  (Wire_boundary_ext
    (boundary_profile, boundary_deployment, boundary_source, boundary_target,
      boundary_principal, boundary_key, boundary_epoch, boundary_route_scope,
      boundary_now, boundary_asset_ttl_floor, boundary_future_skew,
      boundary_max_frame, boundary_version_floor, boundary_critical_allowed,
      boundary_threshold_supported, more))
  = boundary_critical_allowed;

fun boundary_route_scope
  (Wire_boundary_ext
    (boundary_profile, boundary_deployment, boundary_source, boundary_target,
      boundary_principal, boundary_key, boundary_epoch, boundary_route_scope,
      boundary_now, boundary_asset_ttl_floor, boundary_future_skew,
      boundary_max_frame, boundary_version_floor, boundary_critical_allowed,
      boundary_threshold_supported, more))
  = boundary_route_scope;

fun boundary_deployment
  (Wire_boundary_ext
    (boundary_profile, boundary_deployment, boundary_source, boundary_target,
      boundary_principal, boundary_key, boundary_epoch, boundary_route_scope,
      boundary_now, boundary_asset_ttl_floor, boundary_future_skew,
      boundary_max_frame, boundary_version_floor, boundary_critical_allowed,
      boundary_threshold_supported, more))
  = boundary_deployment;

fun boundary_principal
  (Wire_boundary_ext
    (boundary_profile, boundary_deployment, boundary_source, boundary_target,
      boundary_principal, boundary_key, boundary_epoch, boundary_route_scope,
      boundary_now, boundary_asset_ttl_floor, boundary_future_skew,
      boundary_max_frame, boundary_version_floor, boundary_critical_allowed,
      boundary_threshold_supported, more))
  = boundary_principal;

fun boundary_target
  (Wire_boundary_ext
    (boundary_profile, boundary_deployment, boundary_source, boundary_target,
      boundary_principal, boundary_key, boundary_epoch, boundary_route_scope,
      boundary_now, boundary_asset_ttl_floor, boundary_future_skew,
      boundary_max_frame, boundary_version_floor, boundary_critical_allowed,
      boundary_threshold_supported, more))
  = boundary_target;

fun boundary_source
  (Wire_boundary_ext
    (boundary_profile, boundary_deployment, boundary_source, boundary_target,
      boundary_principal, boundary_key, boundary_epoch, boundary_route_scope,
      boundary_now, boundary_asset_ttl_floor, boundary_future_skew,
      boundary_max_frame, boundary_version_floor, boundary_critical_allowed,
      boundary_threshold_supported, more))
  = boundary_source;

fun boundary_epoch
  (Wire_boundary_ext
    (boundary_profile, boundary_deployment, boundary_source, boundary_target,
      boundary_principal, boundary_key, boundary_epoch, boundary_route_scope,
      boundary_now, boundary_asset_ttl_floor, boundary_future_skew,
      boundary_max_frame, boundary_version_floor, boundary_critical_allowed,
      boundary_threshold_supported, more))
  = boundary_epoch;

fun boundary_key
  (Wire_boundary_ext
    (boundary_profile, boundary_deployment, boundary_source, boundary_target,
      boundary_principal, boundary_key, boundary_epoch, boundary_route_scope,
      boundary_now, boundary_asset_ttl_floor, boundary_future_skew,
      boundary_max_frame, boundary_version_floor, boundary_critical_allowed,
      boundary_threshold_supported, more))
  = boundary_key;

fun current_wire_scope authority core =
  equal_nata (wire_deployment core) (boundary_deployment authority) andalso
    (equal_nata (wire_source_domain core) (boundary_source authority) andalso
      (equal_nata (wire_target_domain core) (boundary_target authority) andalso
        (equal_nata (wire_principal core) (boundary_principal authority) andalso
          (equal_nata (wire_key_number core) (boundary_key authority) andalso
            (equal_nata (wire_authority_epoch core)
               (boundary_epoch authority) andalso
              (equal_nata (wire_route_scope core)
                 (boundary_route_scope authority) andalso
                (equal_nata (wire_purpose core) one_nata andalso
                  (if equal_nata (wire_priority core) zero_nata
                    then boundary_critical_allowed authority else true))))))));

fun code_varint_loop number out =
  (if less_nat number (nat_of_integer (128 : IntInf.int)) then out @ [number]
    else code_varint_loop
           (divide_nata number (nat_of_integer (128 : IntInf.int)))
           (out @
             [plus_nata (nat_of_integer (128 : IntInf.int))
                (modulo_nata number (nat_of_integer (128 : IntInf.int)))]));

fun code_field_fixed64 tag value =
  code_varint_loop
    (plus_nata (times_nata (nat_of_integer (8 : IntInf.int)) tag) one_nata) [] @
    put_le_octets (nat_of_integer (8 : IntInf.int)) value;

fun code_field_varint tag value =
  code_varint_loop (times_nata (nat_of_integer (8 : IntInf.int)) tag) [] @
    code_varint_loop value [];

fun code_deadline_bytes Deadline_Absent = []
  | code_deadline_bytes Deadline_Indefinite =
    code_field_varint (nat_of_integer (4 : IntInf.int)) one_nata
  | code_deadline_bytes (Deadline_At seconds) =
    code_field_fixed64 (nat_of_integer (5 : IntInf.int)) seconds;

fun code_field_bytes tag bytes =
  code_varint_loop
    (plus_nata (times_nata (nat_of_integer (8 : IntInf.int)) tag)
      (nat_of_integer (2 : IntInf.int)))
    [] @
    code_varint_loop (size_list bytes) [] @ bytes;

fun code_body_bytes body =
  code_field_varint one_nata (wire_opcode body) @
    maps (code_field_fixed64 (nat_of_integer (2 : IntInf.int)))
      (wire_words body) @
      maps (code_field_bytes (nat_of_integer (3 : IntInf.int)))
        (wire_blobs body) @
        code_deadline_bytes (wire_deadline body);

fun code_core_bytes core =
  code_field_varint one_nata (wire_version core) @
    code_field_varint (nat_of_integer (2 : IntInf.int)) (wire_purpose core) @
      maps (fn (a, b) => code_field_fixed64 a b)
        [(nat_of_integer (3 : IntInf.int), wire_deployment core),
          (nat_of_integer (4 : IntInf.int), wire_source_domain core),
          (nat_of_integer (5 : IntInf.int), wire_target_domain core),
          (nat_of_integer (6 : IntInf.int), wire_principal core),
          (nat_of_integer (7 : IntInf.int), wire_key_number core),
          (nat_of_integer (8 : IntInf.int), wire_authority_epoch core),
          (nat_of_integer (9 : IntInf.int), wire_sent_seconds core),
          (nat_of_integer (10 : IntInf.int), wire_ttl_seconds core)] @
        code_field_bytes (nat_of_integer (11 : IntInf.int)) (wire_uuid core) @
          code_field_varint (nat_of_integer (12 : IntInf.int))
            (family_number (wire_message_family core)) @
            code_field_varint (nat_of_integer (13 : IntInf.int))
              (wire_primary_code core) @
              (case wire_secondary_code core of NONE => []
                | SOME a =>
                  code_field_varint (nat_of_integer (14 : IntInf.int)) a) @
                code_field_varint (nat_of_integer (15 : IntInf.int))
                  (wire_signature_scheme core) @
                  code_field_bytes
                    (plus_nata (nat_of_integer (15 : IntInf.int))
                      (family_number (wire_message_family core)))
                    (code_body_bytes (wire_operation_body core)) @
                    code_field_varint (nat_of_integer (23 : IntInf.int))
                      (wire_atomicity core) @
                      code_field_varint (nat_of_integer (24 : IntInf.int))
                        (wire_priority core) @
                        code_field_fixed64 (nat_of_integer (25 : IntInf.int))
                          (wire_route_scope core);

fun code_core_shape_allowed core =
  equal_nata (size_list (wire_uuid core))
    (nat_of_integer (16 : IntInf.int)) andalso
    (equal_nata
       (divide_nata (nth (wire_uuid core) (nat_of_integer (6 : IntInf.int)))
         (nat_of_integer (16 : IntInf.int)))
       (nat_of_integer (4 : IntInf.int)) andalso
      (equal_nata
         (divide_nata (nth (wire_uuid core) (nat_of_integer (8 : IntInf.int)))
           (nat_of_integer (64 : IntInf.int)))
         (nat_of_integer (2 : IntInf.int)) andalso
        (member equal_nat (wire_primary_code core)
           (atLeastAtMost (equal_nat, interval_nat) one_nata
             (nat_of_integer (5 : IntInf.int))) andalso
          (member equal_nat (wire_signature_scheme core)
             (insert equal_nat one_nata
               (insert equal_nat (nat_of_integer (2 : IntInf.int))
                 bot_set)) andalso
            (member equal_nat (wire_atomicity core)
               (atLeastAtMost (equal_nat, interval_nat) one_nata
                 (nat_of_integer (3 : IntInf.int))) andalso
              (less_eq_nat (wire_priority core)
                 (nat_of_integer (4 : IntInf.int)) andalso
                ((if equal_nata (wire_priority core) zero_nata
                   then equal_nata (wire_atomicity core)
                          (nat_of_integer (3 : IntInf.int))
                   else true) andalso
                  valid_family_opcode (wire_message_family core)
                    (wire_opcode (wire_operation_body core)))))))));

fun code_encode_core core =
  (if code_core_shape_allowed core then SOME (code_core_bytes core) else NONE);

fun envelope_signing_bytes core =
  let
    val encoded = encode_wire_core core;
  in
    [nat_of_integer (79 : IntInf.int), nat_of_integer (73 : IntInf.int),
      nat_of_integer (80 : IntInf.int), zero_nata,
      nat_of_integer (69 : IntInf.int), nat_of_integer (78 : IntInf.int),
      nat_of_integer (86 : IntInf.int), nat_of_integer (69 : IntInf.int),
      nat_of_integer (76 : IntInf.int), nat_of_integer (79 : IntInf.int),
      nat_of_integer (80 : IntInf.int), nat_of_integer (69 : IntInf.int),
      zero_nata] @
      rev (put_le_octets (nat_of_integer (4 : IntInf.int))
            (size_list encoded)) @
        encoded
  end;

fun code_packet_bytes packet =
  code_field_bytes one_nata (code_core_bytes (packet_core packet)) @
    code_field_bytes (nat_of_integer (2 : IntInf.int))
      (packet_signature packet);

fun boundary_asset_ttl_floor
  (Wire_boundary_ext
    (boundary_profile, boundary_deployment, boundary_source, boundary_target,
      boundary_principal, boundary_key, boundary_epoch, boundary_route_scope,
      boundary_now, boundary_asset_ttl_floor, boundary_future_skew,
      boundary_max_frame, boundary_version_floor, boundary_critical_allowed,
      boundary_threshold_supported, more))
  = boundary_asset_ttl_floor;

fun code_wire_expiry core authority =
  let
    val expiry =
      plus_nata (wire_sent_seconds core)
        (max ord_nat (wire_ttl_seconds core)
          (boundary_asset_ttl_floor authority));
  in
    (if less_nat expiry
          (power power_nat (nat_of_integer (2 : IntInf.int))
            (nat_of_integer (64 : IntInf.int)))
      then SOME expiry else NONE)
  end;

fun code_core_machine_domain core =
  wire_body_wellformed (wire_operation_body core) andalso
    list_all wellformed_proto_field (core_fields core);

fun code_typed_encode_core core =
  (if code_core_machine_domain core then code_encode_core core else NONE);

fun code_encode_packet packet =
  (if equal_nata (wire_signature_scheme (packet_core packet)) one_nata andalso
        not (equal_nata (size_list (packet_signature packet))
              (nat_of_integer (64 : IntInf.int))) orelse
        equal_nata (wire_signature_scheme (packet_core packet))
          (nat_of_integer (2 : IntInf.int)) andalso
          null (packet_signature packet)
    then NONE
    else (case code_typed_encode_core (packet_core packet) of NONE => NONE
           | SOME core_bytes =>
             (if less_eq_nat
                   (power power_nat (nat_of_integer (2 : IntInf.int))
                     (nat_of_integer (32 : IntInf.int)))
                   (size_list core_bytes) orelse
                   not (wire_octets (numeral_nat, ord_nat)
                         (packet_signature packet))
               then NONE else SOME (code_packet_bytes packet))));

fun sync_added_status (A1_, A2_) number =
  member A1_ number
    (insert A1_ (numeral A2_ (Bit1 (Bit0 (Bit1 (Bit1 One)))))
      (insert A1_ (numeral A2_ (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One))))))
        (insert A1_ (numeral A2_ (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One))))))
          (insert A1_ (numeral A2_ (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 One))))))
            bot_set))));

fun negotiated_schemes
  (Negotiated_wire_profile_ext
    (negotiated_version, negotiated_families, negotiated_atomicities,
      negotiated_schemes, more))
  = negotiated_schemes;

fun negotiated_atomicities
  (Negotiated_wire_profile_ext
    (negotiated_version, negotiated_families, negotiated_atomicities,
      negotiated_schemes, more))
  = negotiated_atomicities;

fun negotiated_version
  (Negotiated_wire_profile_ext
    (negotiated_version, negotiated_families, negotiated_atomicities,
      negotiated_schemes, more))
  = negotiated_version;

fun boundary_version_floor
  (Wire_boundary_ext
    (boundary_profile, boundary_deployment, boundary_source, boundary_target,
      boundary_principal, boundary_key, boundary_epoch, boundary_route_scope,
      boundary_now, boundary_asset_ttl_floor, boundary_future_skew,
      boundary_max_frame, boundary_version_floor, boundary_critical_allowed,
      boundary_threshold_supported, more))
  = boundary_version_floor;

fun boundary_future_skew
  (Wire_boundary_ext
    (boundary_profile, boundary_deployment, boundary_source, boundary_target,
      boundary_principal, boundary_key, boundary_epoch, boundary_route_scope,
      boundary_now, boundary_asset_ttl_floor, boundary_future_skew,
      boundary_max_frame, boundary_version_floor, boundary_critical_allowed,
      boundary_threshold_supported, more))
  = boundary_future_skew;

fun boundary_profile
  (Wire_boundary_ext
    (boundary_profile, boundary_deployment, boundary_source, boundary_target,
      boundary_principal, boundary_key, boundary_epoch, boundary_route_scope,
      boundary_now, boundary_asset_ttl_floor, boundary_future_skew,
      boundary_max_frame, boundary_version_floor, boundary_critical_allowed,
      boundary_threshold_supported, more))
  = boundary_profile;

fun boundary_now
  (Wire_boundary_ext
    (boundary_profile, boundary_deployment, boundary_source, boundary_target,
      boundary_principal, boundary_key, boundary_epoch, boundary_route_scope,
      boundary_now, boundary_asset_ttl_floor, boundary_future_skew,
      boundary_max_frame, boundary_version_floor, boundary_critical_allowed,
      boundary_threshold_supported, more))
  = boundary_now;

fun negotiated_families
  (Negotiated_wire_profile_ext
    (negotiated_version, negotiated_families, negotiated_atomicities,
      negotiated_schemes, more))
  = negotiated_families;

fun code_profile_allows profile family operation =
  member equal_wire_family family (negotiated_families profile) andalso
    (not (equal_nata (negotiated_version profile)
           (nat_of_integer (5 : IntInf.int))) orelse
      member equal_wire_family family
        (insert equal_wire_family Wire_Query
          (insert equal_wire_family Wire_Heartbeat bot_set)) andalso
        member equal_nat operation
          (insert equal_nat one_nata
            (insert equal_nat (nat_of_integer (2 : IntInf.int)) bot_set)));

fun code_check_versioned_scope core authority version =
  let
    val profile = boundary_profile authority;
  in
    (if not (equal_nata (negotiated_version profile) version) orelse
          (not (equal_nata (wire_version core) version) orelse
            (less_nat version (boundary_version_floor authority) orelse
              (not (code_profile_allows profile (wire_message_family core)
                     (wire_opcode (wire_operation_body core))) orelse
                not (member equal_nat (wire_atomicity core)
                      (negotiated_atomicities profile)))))
      then SOME Unsupported_Wire_Version
      else (if not (current_wire_scope authority core)
             then SOME Invalid_Wire_Source
             else (case code_wire_expiry core authority
                    of NONE => SOME Wire_TTL_Invalid
                    | SOME expiry =>
                      (if less_eq_nat
                            (power power_nat (nat_of_integer (2 : IntInf.int))
                              (nat_of_integer (64 : IntInf.int)))
                            (plus_nata (boundary_now authority)
                              (boundary_future_skew authority)) orelse
                            less_nat
                              (plus_nata (boundary_now authority)
                                (boundary_future_skew authority))
                              (wire_sent_seconds core)
                        then SOME Wire_TTL_Invalid
                        else (if less_nat expiry (boundary_now authority)
                               then SOME Wire_TTL_Expired else NONE)))))
  end;

fun code_admit_packet verify packet authority =
  (case code_check_versioned_scope (packet_core packet) authority
          (nat_of_integer (6 : IntInf.int))
    of NONE =>
      let
        val core = packet_core packet;
      in
        (if equal_nata (wire_signature_scheme core)
              (nat_of_integer (2 : IntInf.int))
          then SOME Invalid_Wire_Threshold
          else (if not (member equal_nat (wire_signature_scheme core)
                         (negotiated_schemes
                           (boundary_profile authority))) orelse
                     not (verify core (envelope_signing_bytes core)
                           (packet_signature packet))
                 then SOME Invalid_Wire_Signature else NONE))
      end
    | SOME a => SOME a);

fun code_product_amount bytes =
  (if not (equal_nata (size_list bytes)
            (nat_of_integer (32 : IntInf.int))) orelse
        (not (wire_octets (numeral_nat, ord_nat) bytes) orelse
          not (equal_lista equal_nat
                (take (nat_of_integer (24 : IntInf.int)) bytes)
                (replicate (nat_of_integer (24 : IntInf.int)) zero_nata)))
    then NONE
    else SOME (get_le_octets
                (rev (drop (nat_of_integer (24 : IntInf.int)) bytes))));

fun cut_revision (Product_cut_ext (cut_authority_epoch, cut_revision, more)) =
  cut_revision;

fun native_id
  (Wire_native_call_ext
    (native_reference, native_id, native_session, native_cut,
      native_origin_epoch, native_origin, native_asset, native_funding_owner,
      native_destination, native_recipient, native_amount, native_tail_words,
      native_proof_bytes, more))
  = native_id;

fun legal_issuance_epoch
  (Code_legal_fields_ext
    (legal_action_number, legal_officer, legal_jurisdiction, legal_basis,
      legal_issuance_epoch, legal_scope, legal_predecessor, legal_destination,
      legal_appeal_deadline, more))
  = legal_issuance_epoch;

fun native_origin_epoch
  (Wire_native_call_ext
    (native_reference, native_id, native_session, native_cut,
      native_origin_epoch, native_origin, native_asset, native_funding_owner,
      native_destination, native_recipient, native_amount, native_tail_words,
      native_proof_bytes, more))
  = native_origin_epoch;

fun native_proof_bytes
  (Wire_native_call_ext
    (native_reference, native_id, native_session, native_cut,
      native_origin_epoch, native_origin, native_asset, native_funding_owner,
      native_destination, native_recipient, native_amount, native_tail_words,
      native_proof_bytes, more))
  = native_proof_bytes;

fun native_destination
  (Wire_native_call_ext
    (native_reference, native_id, native_session, native_cut,
      native_origin_epoch, native_origin, native_asset, native_funding_owner,
      native_destination, native_recipient, native_amount, native_tail_words,
      native_proof_bytes, more))
  = native_destination;

fun native_tail_words
  (Wire_native_call_ext
    (native_reference, native_id, native_session, native_cut,
      native_origin_epoch, native_origin, native_asset, native_funding_owner,
      native_destination, native_recipient, native_amount, native_tail_words,
      native_proof_bytes, more))
  = native_tail_words;

fun native_origin
  (Wire_native_call_ext
    (native_reference, native_id, native_session, native_cut,
      native_origin_epoch, native_origin, native_asset, native_funding_owner,
      native_destination, native_recipient, native_amount, native_tail_words,
      native_proof_bytes, more))
  = native_origin;

fun code_optional_origin (A1_, A2_, A3_) words =
  (case words of [] => NONE
    | present :: tail =>
      (if eq A3_ present (zero A2_) then SOME (NONE, tail)
        else (if eq A3_ present (one A1_)
               then (case tail of [] => NONE | [_] => NONE
                      | domain :: event :: rest =>
                        SOME (SOME (domain, event), rest))
               else NONE)));

fun code_take_ordered_set words =
  (case words of [] => NONE
    | count :: tail =>
      (if less_nat (size_list tail) count then NONE
        else let
               val items = take count tail;
             in
               (if sorted_wrt less_nat items
                 then SOME (Set items, drop count tail) else NONE)
             end));

fun code_optional_word (A1_, A2_, A3_) words =
  (case words of [] => NONE
    | present :: tail =>
      (if eq A3_ present (zero A2_) then SOME (NONE, tail)
        else (if eq A3_ present (one A1_)
               then (case tail of [] => NONE
                      | value :: rest => SOME (SOME value, rest))
               else NONE)));

fun code_product_deadline Deadline_Absent = NONE
  | code_product_deadline Deadline_Indefinite = NONE
  | code_product_deadline (Deadline_At seconds) = SOME seconds;

fun code_parse_legal_fields deadline words =
  (case words of [] => NONE | [_] => NONE | [_, _] => NONE | [_, _, _] => NONE
    | [_, _, _, _] => NONE
    | action :: officer :: jurisdiction :: basis :: epoch :: tail =>
      (if not (member equal_nat action
                (atLeastAtMost (equal_nat, interval_nat) one_nata
                  (nat_of_integer (7 : IntInf.int))))
        then NONE
        else bind (code_take_ordered_set tail)
               (fn (scope, first) =>
                 bind (code_optional_origin (one_nat, zero_nat, equal_nat)
                        first)
                   (fn (predecessor, second) =>
                     bind (code_optional_word (one_nat, zero_nat, equal_nat)
                            second)
                       (fn (destination, last) =>
                         (if not (null last) then NONE
                           else SOME (Code_legal_fields_ext
                                       (action, officer, jurisdiction, basis,
 epoch, scope, predecessor, destination, code_product_deadline deadline,
 ()))))))));

fun code_native_call_prefix core =
  let
    val body = wire_operation_body core;
    val words = wire_words body;
  in
    (if less_nat (size_list words) (nat_of_integer (11 : IntInf.int)) then NONE
      else (case wire_blobs body of [] => NONE
             | amount :: proofs =>
               map_option
                 (fn value =>
                   Wire_native_call_ext
                     (nth words zero_nata,
                       (wire_principal core, nth words one_nata),
                       nth words (nat_of_integer (2 : IntInf.int)),
                       Product_cut_ext
                         (wire_authority_epoch core,
                           nth words (nat_of_integer (3 : IntInf.int)), ()),
                       nth words (nat_of_integer (4 : IntInf.int)),
                       (nth words (nat_of_integer (5 : IntInf.int)),
                         nth words (nat_of_integer (6 : IntInf.int))),
                       nth words (nat_of_integer (7 : IntInf.int)),
                       nth words (nat_of_integer (8 : IntInf.int)),
                       nth words (nat_of_integer (9 : IntInf.int)),
                       nth words (nat_of_integer (10 : IntInf.int)), value,
                       drop (nat_of_integer (11 : IntInf.int)) words, proofs,
                       ()))
                 (code_product_amount amount)))
  end;

fun code_decode_legal core =
  (case code_native_call_prefix core
    of NONE => Code_Legal_Refused Invalid_Wire_Format
    | SOME native =>
      (case native_proof_bytes native
        of [] => Code_Legal_Refused Invalid_Wire_Format
        | [proof] =>
          (if null proof then Code_Legal_Refused Invalid_Wire_Format
            else let
                   val operation = wire_opcode (wire_operation_body core);
                 in
                   (if not (member equal_nat operation
                             (insert equal_nat one_nata
                               (insert equal_nat
                                 (nat_of_integer (2 : IntInf.int)) bot_set)))
                     then Code_Legal_Refused Invalid_Wire_Format
                     else (case code_parse_legal_fields
                                  (wire_deadline (wire_operation_body core))
                                  (native_tail_words native)
                            of NONE => Code_Legal_Refused Invalid_Wire_Format
                            | SOME parsed_fields =>
                              let
                                val stage =
                                  (if equal_nata operation one_nata
                                    then Code_Source_Emission
                                    else Code_Receiving_Commit);
                                val target =
                                  (if equal_nata operation one_nata
                                    then fst (native_origin native)
                                    else native_destination native);
                              in
                                (if not (equal_nata (wire_target_domain core)
  target) orelse
                                      not
(equal_nata (legal_issuance_epoch parsed_fields) (native_origin_epoch native))
                                  then Code_Legal_Refused Invalid_Wire_Source
                                  else Code_Legal_Ready
 (native, stage, parsed_fields, proof))
                              end))
                 end)
        | _ :: _ :: _ => Code_Legal_Refused Invalid_Wire_Format));

fun code_legal_tree core =
  (case code_decode_legal core of Code_Legal_Refused a => Code_Tree_Refused a
    | Code_Legal_Ready (native, _, _, _) =>
      Code_Tree_Ready (Code_Nested_Legal (native_id native)));

fun spend_enforcement_update spend_enforcementa
  (Code_spend_fields_ext
    (spend_reference, spend_sender, spend_recipient, spend_kind_number,
      spend_amount, spend_enforcement, spend_proof, more))
  = Code_spend_fields_ext
      (spend_reference, spend_sender, spend_recipient, spend_kind_number,
        spend_amount, spend_enforcementa spend_enforcement, spend_proof, more);

fun spend_proof_update spend_proofa
  (Code_spend_fields_ext
    (spend_reference, spend_sender, spend_recipient, spend_kind_number,
      spend_amount, spend_enforcement, spend_proof, more))
  = Code_spend_fields_ext
      (spend_reference, spend_sender, spend_recipient, spend_kind_number,
        spend_amount, spend_enforcement, spend_proofa spend_proof, more);

fun code_parse_enforcement_fields deadline words =
  (case words of [] => NONE | [_] => NONE | [_, _] => NONE
    | officer :: jurisdiction :: basis :: tail =>
      bind (code_take_ordered_set tail)
        (fn (assets, first) =>
          bind (code_optional_origin (one_nat, zero_nat, equal_nat) first)
            (fn (prior, last) =>
              (if not (null last) then NONE
                else SOME (Code_enforcement_fields_ext
                            (officer, jurisdiction, basis, assets, prior,
                              code_product_deadline deadline, ()))))));

fun code_parse_spend_fields family deadline native =
  (case native_tail_words native of [] => NONE | [_] => NONE | [_, _] => NONE
    | [_, _, _] => NONE
    | reference :: sender :: recipient :: kind :: tail =>
      (if not (equal_wire_familya family Wire_State_Sync andalso
                 equal_nata kind zero_nata orelse
                equal_wire_familya family Wire_Regulatory andalso
                  member equal_nat kind
                    (atLeastAtMost (equal_nat, interval_nat) one_nata
                      (nat_of_integer (4 : IntInf.int))))
        then NONE
        else (case native_proof_bytes native of [] => NONE
               | amount :: proofs =>
                 bind (code_product_amount amount)
                   (fn value =>
                     let
                       val base =
                         Code_spend_fields_ext
                           (reference, sender, recipient, kind, value, NONE,
                             NONE, ());
                     in
                       (if equal_wire_familya family Wire_Regulatory
                         then (case proofs of [] => NONE
                                | [proof] =>
                                  (if null proof then NONE
                                    else map_option
   (fn parsed_fields =>
     spend_proof_update (fn _ => SOME proof)
       (spend_enforcement_update (fn _ => SOME parsed_fields) base))
   (code_parse_enforcement_fields deadline tail))
                                | _ :: _ :: _ => NONE)
                         else (if not (null proofs) orelse
                                    (not (equal_wire_deadline deadline
   Deadline_Absent) orelse
                                      not (null tail))
                                then NONE else SOME base))
                     end))));

fun code_decode_spend core =
  (case code_native_call_prefix core
    of NONE => Code_Spend_Refused Invalid_Wire_Format
    | SOME native =>
      (case code_parse_spend_fields (wire_message_family core)
              (wire_deadline (wire_operation_body core)) native
        of NONE => Code_Spend_Refused Invalid_Wire_Format
        | SOME parsed_fields =>
          (if not (equal_nata (wire_target_domain core)
                    (native_destination native))
            then Code_Spend_Refused Invalid_Wire_Source
            else Code_Spend_Ready (native, parsed_fields))));

fun code_spend_tree core =
  (case code_decode_spend core of Code_Spend_Refused a => Code_Tree_Refused a
    | Code_Spend_Ready (native, _) =>
      Code_Tree_Ready (Code_Nested_Spend (native_id native)));

fun code_take_varint_from fuel index input =
  (if equal_nata fuel zero_nata then NONE
    else (case input of [] => NONE
           | byte :: tail =>
             (if less_eq_nat (nat_of_integer (256 : IntInf.int)) byte orelse
                   equal_nata index (nat_of_integer (9 : IntInf.int)) andalso
                     less_nat one_nata byte
               then NONE
               else (if less_nat byte (nat_of_integer (128 : IntInf.int))
                      then (if less_nat zero_nata index andalso
                                 equal_nata byte zero_nata
                             then NONE else SOME (byte, tail))
                      else map_option
                             (fn (number, a) =>
                               (plus_nata
                                  (minus_nata byte
                                    (nat_of_integer (128 : IntInf.int)))
                                  (times_nata
                                    (nat_of_integer (128 : IntInf.int)) number),
                                 a))
                             (code_take_varint_from (minus_nata fuel one_nata)
                               (plus_nata index one_nata) tail)))));

fun code_take_varint bytes =
  code_take_varint_from (nat_of_integer (10 : IntInf.int)) zero_nata bytes;

fun equal_bool false p = not p
  | equal_bool true p = p
  | equal_bool p false = not p
  | equal_bool p true = p;

val code_json_permissions : (char list) list =
  [[Chara (false, true, false, false, true, false, true, false),
     Chara (true, false, true, false, false, true, true, false),
     Chara (true, true, false, false, true, true, true, false),
     Chara (true, false, true, false, false, true, true, false),
     Chara (false, true, false, false, true, true, true, false),
     Chara (false, true, true, false, true, true, true, false),
     Chara (true, false, true, false, false, true, true, false)],
    [Chara (false, false, true, false, false, false, true, false),
      Chara (true, false, false, true, false, true, true, false),
      Chara (true, true, false, false, true, true, true, false),
      Chara (false, false, false, false, true, true, true, false),
      Chara (true, false, false, false, false, true, true, false),
      Chara (false, false, true, false, true, true, true, false),
      Chara (true, true, false, false, false, true, true, false),
      Chara (false, false, false, true, false, true, true, false)],
    [Chara (false, false, true, false, false, false, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, true, false, false, false, true, true, false),
      Chara (true, false, false, true, false, true, true, false),
      Chara (false, false, true, false, true, true, true, false)],
    [Chara (true, true, false, false, false, false, true, false),
      Chara (true, false, false, false, false, true, true, false),
      Chara (false, true, true, true, false, true, true, false),
      Chara (true, true, false, false, false, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, false, true, true, false, true, true, false)],
    [Chara (false, true, true, false, false, false, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, true, true, true, false, true, true, false),
      Chara (true, true, false, false, false, true, true, false),
      Chara (true, false, true, false, false, true, true, false)],
    [Chara (false, false, false, false, true, false, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (true, false, true, true, false, true, true, false),
      Chara (false, false, false, false, true, true, true, false),
      Chara (false, false, true, false, true, true, true, false)],
    [Chara (true, true, true, true, false, false, true, false),
      Chara (false, true, false, false, false, true, true, false),
      Chara (true, true, false, false, true, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (false, true, true, false, true, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, false, true, false, true, false, true, false),
      Chara (true, false, false, true, false, true, true, false),
      Chara (true, false, true, true, false, true, true, false),
      Chara (true, false, true, false, false, true, true, false)],
    [Chara (true, false, false, false, false, false, true, false),
      Chara (false, false, true, false, true, true, true, false),
      Chara (false, false, true, false, true, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (true, true, false, false, true, true, true, false),
      Chara (false, false, true, false, true, true, true, false)],
    [Chara (true, true, false, false, false, false, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, false, true, false, false, true, true, false),
      Chara (true, false, false, true, false, true, true, false),
      Chara (false, false, true, false, true, true, true, false)],
    [Chara (false, true, false, false, true, false, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, true, true, false, false, true, true, false),
      Chara (true, false, true, false, true, true, true, false),
      Chara (false, true, true, true, false, true, true, false),
      Chara (false, false, true, false, false, true, true, false)],
    [Chara (false, true, false, false, true, false, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (true, true, false, false, false, true, true, false),
      Chara (true, true, true, true, false, true, true, false),
      Chara (false, true, true, true, false, true, true, false),
      Chara (true, true, false, false, false, true, true, false),
      Chara (true, false, false, true, false, true, true, false),
      Chara (false, false, true, true, false, true, true, false),
      Chara (true, false, true, false, false, true, true, false)],
    [Chara (true, true, true, false, true, false, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (true, false, false, true, false, true, true, false),
      Chara (false, false, true, false, true, true, true, false),
      Chara (true, false, true, false, false, true, true, false)],
    [Chara (false, false, false, false, true, false, true, false),
      Chara (true, false, true, false, true, true, true, false),
      Chara (false, true, false, false, false, true, true, false),
      Chara (false, false, true, true, false, true, true, false),
      Chara (true, false, false, true, false, true, true, false),
      Chara (true, true, false, false, true, true, true, false),
      Chara (false, false, false, true, false, true, true, false),
      Chara (false, false, false, false, true, false, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (true, false, false, true, false, true, true, false),
      Chara (true, false, true, true, false, true, true, false),
      Chara (true, false, false, false, false, true, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (true, false, false, true, true, true, true, false)]];

fun code_json_expect token bytes =
  (if equal_lista equal_nat (take (size_list token) bytes) token
    then SOME (drop (size_list token) bytes) else NONE);

fun code_json_triple first second third bytes =
  bind (code_json_expect [nat_of_integer (91 : IntInf.int)] bytes)
    (fn r0 =>
      bind (first r0)
        (fn (a, r1) =>
          bind (code_json_expect [nat_of_integer (44 : IntInf.int)] r1)
            (fn r2 =>
              bind (second r2)
                (fn (b, r3) =>
                  bind (code_json_expect [nat_of_integer (44 : IntInf.int)] r3)
                    (fn r4 =>
                      bind (third r4)
                        (fn (c, r5) =>
                          map_option (fn d => ((a, (b, c)), d))
                            (code_json_expect [nat_of_integer (93 : IntInf.int)]
                              r5)))))));

fun code_json_ascii text = map nat_of_char text;

fun code_json_enum_from index [] bytes = NONE
  | code_json_enum_from index (name :: names) bytes =
    (case code_json_expect
            ([nat_of_integer (34 : IntInf.int)] @
              code_json_ascii name @ [nat_of_integer (34 : IntInf.int)])
            bytes
      of NONE => code_json_enum_from (suc index) names bytes
      | SOME rest => SOME (index, rest));

fun code_json_enum names bytes = code_json_enum_from zero_nata names bytes;

val code_json_routes : (char list) list =
  [[Chara (false, true, true, true, false, false, true, false),
     Chara (true, true, true, true, false, true, true, false),
     Chara (false, true, false, false, true, true, true, false),
     Chara (true, false, true, true, false, true, true, false),
     Chara (true, false, false, false, false, true, true, false),
     Chara (false, false, true, true, false, true, true, false)],
    [Chara (true, false, false, false, false, false, true, false),
      Chara (false, false, true, false, false, true, true, false),
      Chara (true, false, true, true, false, true, true, false),
      Chara (true, false, false, true, false, true, true, false),
      Chara (false, true, true, true, false, true, true, false),
      Chara (true, false, false, true, false, true, true, false),
      Chara (true, true, false, false, true, true, true, false),
      Chara (false, false, true, false, true, true, true, false),
      Chara (false, true, false, false, true, true, true, false),
      Chara (true, false, false, false, false, true, true, false),
      Chara (false, false, true, false, true, true, true, false),
      Chara (true, false, false, true, false, true, true, false),
      Chara (false, true, true, false, true, true, true, false),
      Chara (true, false, true, false, false, true, true, false)],
    [Chara (true, false, false, false, false, false, true, false),
      Chara (false, false, true, false, false, true, true, false),
      Chara (true, false, false, false, false, true, true, false),
      Chara (false, false, false, false, true, true, true, false),
      Chara (false, false, true, false, true, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (false, true, false, false, true, true, true, false)]];

fun code_json_digits value [] = SOME (value, [])
  | code_json_digits value (byte :: tail) =
    (if less_eq_nat (nat_of_integer (48 : IntInf.int)) byte andalso
          less_eq_nat byte (nat_of_integer (57 : IntInf.int))
      then let
             val next =
               plus_nata (times_nata (nat_of_integer (10 : IntInf.int)) value)
                 (minus_nata byte (nat_of_integer (48 : IntInf.int)));
           in
             (if less_nat next
                   (power power_nat (nat_of_integer (2 : IntInf.int))
                     (nat_of_integer (64 : IntInf.int)))
               then code_json_digits next tail else NONE)
           end
      else SOME (value, byte :: tail));

fun code_json_u64 bytes =
  (case bytes of [] => NONE
    | byte :: tail =>
      (if equal_nata byte (nat_of_integer (48 : IntInf.int))
        then SOME (zero_nata, tail)
        else (if less_eq_nat (nat_of_integer (49 : IntInf.int)) byte andalso
                   less_eq_nat byte (nat_of_integer (57 : IntInf.int))
               then code_json_digits
                      (minus_nata byte (nat_of_integer (48 : IntInf.int))) tail
               else NONE)));

fun code_json_grant x =
  code_json_triple code_json_u64 (code_json_enum code_json_routes)
    (code_json_enum code_json_permissions) x;

fun sync_mode_at tag =
  (if equal_nata tag one_nata then SOME Sync_Initial
    else (if equal_nata tag (nat_of_integer (2 : IntInf.int))
           then SOME Sync_Incremental
           else (if equal_nata tag (nat_of_integer (3 : IntInf.int))
                  then SOME Sync_Full else NONE)));

fun code_json_lex3 first second =
  let
    val ((a, (b, c)), (x, (y, z))) = (first, second);
  in
    less_nat a x orelse
      equal_nata a x andalso
        (less_nat b y orelse equal_nata b y andalso less_nat c z)
  end;

fun code_json_pair left right bytes =
  bind (code_json_expect [nat_of_integer (91 : IntInf.int)] bytes)
    (fn first =>
      bind (left first)
        (fn (a, second) =>
          bind (code_json_expect [nat_of_integer (44 : IntInf.int)] second)
            (fn third =>
              bind (right third)
                (fn (b, fourth) =>
                  map_option (fn c => ((a, b), c))
                    (code_json_expect [nat_of_integer (93 : IntInf.int)]
                      fourth)))));

fun code_check_operation accepts core =
  (if accepts (wire_message_family core)
        (wire_opcode (wire_operation_body core))
    then NONE else SOME Unsupported_Wire_Version);

fun parse_wire_application_query args =
  (case args of [] => NONE | [_] => NONE
    | [tag, asset] =>
      (if equal_nata tag one_nata then SOME (Application_Value asset) else NONE)
    | [tag, asset, item] =>
      (if equal_nata tag (nat_of_integer (2 : IntInf.int))
        then SOME (Source_Balance (asset, item))
        else (if equal_nata tag (nat_of_integer (5 : IntInf.int))
               then SOME (Regulatory_State (asset, item))
               else (if equal_nata tag (nat_of_integer (6 : IntInf.int))
                      then SOME (Terminal_Receipt (asset, item)) else NONE)))
    | [tag, asset, item, holder] =>
      (if equal_nata tag (nat_of_integer (3 : IntInf.int))
        then SOME (Destination_Balance (asset, (item, holder))) else NONE)
    | [_, _, _, _, _] => NONE
    | [tag, asset, item, holder, asseta, holdera] =>
      (if equal_nata tag (nat_of_integer (4 : IntInf.int))
        then SOME (Root_Balance ((asset, item), (holder, (asseta, holdera))))
        else NONE)
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => NONE);

fun decode_wire_query_body core =
  let
    val body = wire_operation_body core;
    val opa = wire_opcode body;
    val expected_epoch = wire_authority_epoch core;
  in
    (if not (equal_wire_familya (wire_message_family core) Wire_Query) orelse
          not (null (wire_blobs body))
      then NONE
      else (case wire_words body of [] => NONE
             | session :: args =>
               let
                 val proof = Session_proof_ext (session, expected_epoch, ());
               in
                 (if member equal_nat opa
                       (insert equal_nat one_nata
                         (insert equal_nat (nat_of_integer (2 : IntInf.int))
                           bot_set))
                   then (case args of [] => NONE
                          | revision :: query =>
                            map_option
                              (fn q =>
                                Wire_Read_Request
                                  (proof,
                                    (if equal_nata opa one_nata
                                      then Current_Data
     (q, Product_cut_ext (expected_epoch, revision, ()))
                                      else Historical_Data (q, revision))))
                              (parse_wire_application_query query))
                   else (if equal_nata opa (nat_of_integer (3 : IntInf.int))
                          then map_option
                                 (fn q => Wire_Read_Request (proof, Raw_Data q))
                                 (parse_wire_application_query args)
                          else (if equal_nata opa
                                     (nat_of_integer (4 : IntInf.int))
                                 then (case args of [] => NONE | [_] => NONE
| [domain, event] =>
  SOME (Wire_Read_Request (proof, Operation_Status (domain, event)))
| _ :: _ :: _ :: _ => NONE)
                                 else (if equal_nata opa
    (nat_of_integer (5 : IntInf.int))
then (if null args then SOME (Wire_Read_Request (proof, Authority_Journal))
       else NONE)
else (if equal_nata opa (nat_of_integer (6 : IntInf.int))
       then map_option (fn a => Wire_Cache_Request (proof, a))
              (parse_wire_application_query args)
       else (if equal_nata opa (nat_of_integer (7 : IntInf.int))
              then (case args of [] => NONE
                     | [asset] =>
                       SOME (Wire_Read_Request (proof, Owner_Data asset))
                     | _ :: _ :: _ => NONE)
              else NONE))))))
               end))
  end;

fun code_json_write_permission x =
  code_json_triple code_json_u64 code_json_u64 code_json_u64 x;

fun code_json_elements fuel parse bytes =
  (if equal_nata fuel zero_nata then NONE
    else (case parse bytes of NONE => NONE | SOME (_, []) => NONE
           | SOME (parsed_item, separator :: rest) =>
             (if equal_nata separator (nat_of_integer (93 : IntInf.int))
               then SOME ([parsed_item], rest)
               else (if equal_nata separator (nat_of_integer (44 : IntInf.int))
                      then map_option
                             (fn (values, a) => (parsed_item :: values, a))
                             (code_json_elements (minus_nata fuel one_nata)
                               parse rest)
                      else NONE))));

fun code_json_array parse bytes =
  (case bytes of [] => NONE
    | opening :: tail =>
      (if not (equal_nata opening (nat_of_integer (91 : IntInf.int))) then NONE
        else (case tail of [] => code_json_elements (size_list bytes) parse tail
               | first :: rest =>
                 (if equal_nata first (nat_of_integer (93 : IntInf.int))
                   then SOME ([], rest)
                   else code_json_elements (size_list bytes) parse tail))));

fun code_json_strict_list relation parse bytes =
  bind (code_json_array parse bytes)
    (fn (values, rest) =>
      (if sorted_wrt relation values then SOME (values, rest) else NONE));

fun code_json_open_key name =
  [nat_of_integer (123 : IntInf.int), nat_of_integer (34 : IntInf.int)] @
    code_json_ascii name @
      [nat_of_integer (34 : IntInf.int), nat_of_integer (58 : IntInf.int)];

fun code_json_first_field name parse bytes =
  bind (code_json_expect (code_json_open_key name) bytes) parse;

fun code_json_next_key name =
  [nat_of_integer (44 : IntInf.int), nat_of_integer (34 : IntInf.int)] @
    code_json_ascii name @
      [nat_of_integer (34 : IntInf.int), nat_of_integer (58 : IntInf.int)];

fun code_json_next_field name parse bytes =
  bind (code_json_expect (code_json_next_key name) bytes) parse;

fun code_json_dependency x =
  code_json_pair code_json_u64 (code_json_strict_list less_nat code_json_u64) x;

fun code_json_context bytes =
  bind (code_json_first_field
         [Chara (true, false, true, false, false, true, true, false),
           Chara (false, true, true, true, false, true, true, false),
           Chara (false, false, true, false, false, true, true, false),
           Chara (false, false, false, false, true, true, true, false),
           Chara (true, true, true, true, false, true, true, false),
           Chara (true, false, false, true, false, true, true, false),
           Chara (false, true, true, true, false, true, true, false),
           Chara (false, false, true, false, true, true, true, false)]
         code_json_u64 bytes)
    (fn (endpoint, r0) =>
      bind (code_json_next_field
             [Chara (true, false, true, false, false, true, true, false),
               Chara (false, false, false, false, true, true, true, false),
               Chara (true, true, true, true, false, true, true, false),
               Chara (true, true, false, false, false, true, true, false),
               Chara (false, false, false, true, false, true, true, false)]
             code_json_u64 r0)
        (fn (epoch, r1) =>
          bind (code_json_next_field
                 [Chara (true, true, true, false, false, true, true, false),
                   Chara (false, true, false, false, true, true, true, false),
                   Chara (true, false, false, false, false, true, true, false),
                   Chara (false, true, true, true, false, true, true, false),
                   Chara (false, false, true, false, true, true, true, false),
                   Chara (true, true, false, false, true, true, true, false)]
                 (code_json_strict_list code_json_lex3 code_json_grant) r1)
            (fn (grants, r2) =>
              bind (code_json_next_field
                     [Chara (false, false, true, false, false, true, true,
                              false),
                       Chara (true, false, true, false, false, true, true,
                               false),
                       Chara (false, false, false, false, true, true, true,
                               false),
                       Chara (true, false, true, false, false, true, true,
                               false),
                       Chara (false, true, true, true, false, true, true,
                               false),
                       Chara (false, false, true, false, false, true, true,
                               false),
                       Chara (true, false, true, false, false, true, true,
                               false),
                       Chara (false, true, true, true, false, true, true,
                               false),
                       Chara (true, true, false, false, false, true, true,
                               false),
                       Chara (true, false, false, true, false, true, true,
                               false),
                       Chara (true, false, true, false, false, true, true,
                               false),
                       Chara (true, true, false, false, true, true, true,
                               false)]
                     (code_json_strict_list
                       (fn first => fn second =>
                         less_nat (fst first) (fst second))
                       code_json_dependency)
                     r2)
                (fn (dependencies, r3) =>
                  bind (code_json_next_field
                         [Chara (true, true, true, false, true, true, true,
                                  false),
                           Chara (false, true, false, false, true, true, true,
                                   false),
                           Chara (true, false, false, true, false, true, true,
                                   false),
                           Chara (false, false, true, false, true, true, true,
                                   false),
                           Chara (true, false, true, false, false, true, true,
                                   false),
                           Chara (true, true, true, true, true, false, true,
                                   false),
                           Chara (false, false, false, false, true, true, true,
                                   false),
                           Chara (true, false, true, false, false, true, true,
                                   false),
                           Chara (false, true, false, false, true, true, true,
                                   false),
                           Chara (true, false, true, true, false, true, true,
                                   false),
                           Chara (true, false, false, true, false, true, true,
                                   false),
                           Chara (true, true, false, false, true, true, true,
                                   false),
                           Chara (true, true, false, false, true, true, true,
                                   false),
                           Chara (true, false, false, true, false, true, true,
                                   false),
                           Chara (true, true, true, true, false, true, true,
                                   false),
                           Chara (false, true, true, true, false, true, true,
                                   false),
                           Chara (true, true, false, false, true, true, true,
                                   false)]
                         (code_json_strict_list code_json_lex3
                           code_json_write_permission)
                         r3)
                    (fn (writes, r4) =>
                      map_option
                        (fn a =>
                          (Code_json_endpoint_context_ext
                             (endpoint, epoch, grants, dependencies, writes,
                               ()),
                            a))
                        (code_json_expect [nat_of_integer (125 : IntInf.int)]
                          r4))))));

fun code_ordinary_proof_count (Wire_Record_Terminal (kind, reference)) =
  one_nata
  | code_ordinary_proof_count (Wire_Refund (generation, reference)) = one_nata
  | code_ordinary_proof_count (Wire_Cancel generation) = one_nata
  | code_ordinary_proof_count (Wire_Fence generation) = one_nata
  | code_ordinary_proof_count (Wire_Reconcile (generation, reference)) =
    one_nata
  | code_ordinary_proof_count (Wire_Preempt duration) = one_nata
  | code_ordinary_proof_count (Wire_Reserve v) = zero_nata
  | code_ordinary_proof_count (Wire_Dispatch v) = zero_nata
  | code_ordinary_proof_count (Wire_Debit v) = zero_nata
  | code_ordinary_proof_count (Wire_Timeout v) = zero_nata
  | code_ordinary_proof_count (Wire_Deliver v) = zero_nata
  | code_ordinary_proof_count (Wire_Write (v, va)) = zero_nata
  | code_ordinary_proof_count Wire_Publish = zero_nata;

fun code_ordinary_proofs_allowed native command =
  equal_nata (size_list (native_proof_bytes native))
    (code_ordinary_proof_count command) andalso
    list_all (fn proof => not (null proof)) (native_proof_bytes native);

fun code_ordinary_endpoint native (Wire_Deliver reference) =
  native_destination native
  | code_ordinary_endpoint native (Wire_Reserve v) = fst (native_origin native)
  | code_ordinary_endpoint native (Wire_Dispatch v) = fst (native_origin native)
  | code_ordinary_endpoint native (Wire_Debit v) = fst (native_origin native)
  | code_ordinary_endpoint native (Wire_Cancel v) = fst (native_origin native)
  | code_ordinary_endpoint native (Wire_Fence v) = fst (native_origin native)
  | code_ordinary_endpoint native (Wire_Preempt v) = fst (native_origin native)
  | code_ordinary_endpoint native (Wire_Timeout v) = fst (native_origin native)
  | code_ordinary_endpoint native (Wire_Record_Terminal (v, va)) =
    fst (native_origin native)
  | code_ordinary_endpoint native (Wire_Refund (v, va)) =
    fst (native_origin native)
  | code_ordinary_endpoint native (Wire_Reconcile (v, va)) =
    fst (native_origin native)
  | code_ordinary_endpoint native (Wire_Write (v, va)) =
    fst (native_origin native)
  | code_ordinary_endpoint native Wire_Publish = fst (native_origin native);

fun decode_wire_credential_prefix args =
  (case args of [] => NONE
    | presence :: tail =>
      (if equal_nata presence zero_nata then SOME (NONE, tail)
        else (if equal_nata presence one_nata andalso
                   less_eq_nat (nat_of_integer (6 : IntInf.int))
                     (size_list tail)
               then SOME (SOME (Product_lock_credential_ext
                                 (Product_lock_token_ext
                                    (nth tail zero_nata,
                                      nth tail
(nat_of_integer (3 : IntInf.int)),
                                      nth tail
(nat_of_integer (4 : IntInf.int)),
                                      ()),
                                   nth tail (nat_of_integer (5 : IntInf.int)),
                                   (nth tail one_nata,
                                     nth tail
                                       (nat_of_integer (2 : IntInf.int))),
                                   ())),
                           drop (nat_of_integer (6 : IntInf.int)) tail)
               else NONE)));

fun decode_ordinary_tail family operation args =
  (case family
    of Wire_State_Sync =>
      (case args
        of [] =>
          (if equal_nata operation (nat_of_integer (5 : IntInf.int))
            then SOME Wire_Publish else NONE)
        | [arg] =>
          (if equal_nata operation one_nata then SOME (Wire_Debit arg)
            else (if equal_nata operation (nat_of_integer (3 : IntInf.int))
                   then SOME (Wire_Deliver arg) else NONE))
        | [arg, second] =>
          (if equal_nata operation (nat_of_integer (2 : IntInf.int)) andalso
                member equal_nat arg
                  (insert equal_nat one_nata
                    (insert equal_nat (nat_of_integer (2 : IntInf.int))
                      bot_set))
            then SOME (Wire_Record_Terminal (arg, second))
            else (if equal_nata operation (nat_of_integer (4 : IntInf.int))
                   then SOME (Wire_Refund (arg, second)) else NONE))
        | _ :: _ :: _ :: _ => NONE)
    | Wire_Regulatory => NONE
    | Wire_Lock =>
      (case args of [] => NONE
        | [arg] =>
          (if equal_nata operation one_nata then SOME (Wire_Reserve arg)
            else (if equal_nata operation (nat_of_integer (2 : IntInf.int))
                   then SOME (Wire_Dispatch arg)
                   else (if equal_nata operation
                              (nat_of_integer (3 : IntInf.int))
                          then SOME (Wire_Cancel arg)
                          else (if equal_nata operation
                                     (nat_of_integer (4 : IntInf.int))
                                 then SOME (Wire_Fence arg)
                                 else (if equal_nata operation
    (nat_of_integer (5 : IntInf.int))
then SOME (Wire_Preempt arg)
else (if equal_nata operation (nat_of_integer (8 : IntInf.int))
       then SOME (Wire_Timeout arg) else NONE))))))
        | [arg, second] =>
          (if equal_nata operation (nat_of_integer (6 : IntInf.int))
            then SOME (Wire_Reconcile (arg, second))
            else (if equal_nata operation (nat_of_integer (7 : IntInf.int))
                   then SOME (Wire_Write (arg, second)) else NONE))
        | _ :: _ :: _ :: _ => NONE)
    | Wire_Query => NONE | Wire_Ack => NONE | Wire_Heartbeat => NONE
    | Wire_Governance => NONE);

fun read_wire_versions count args =
  (if equal_nata count zero_nata then SOME ([], args)
    else (case args of [] => NONE | [_] => NONE
           | asset :: version :: remaining =>
             map_option (fn (versions, a) => ((asset, version) :: versions, a))
               (read_wire_versions (minus_nata count one_nata) remaining)));

fun decode_ordinary_operands core native =
  (case decode_wire_credential_prefix (native_tail_words native) of NONE => NONE
    | SOME (_, []) => NONE
    | SOME (credential, count :: tail) =>
      (case read_wire_versions count tail of NONE => NONE
        | SOME (versions, args) =>
          (if sorted_wrt less_nat (map fst versions)
            then map_option (fn command => (credential, (versions, command)))
                   (decode_ordinary_tail (wire_message_family core)
                     (wire_opcode (wire_operation_body core)) args)
            else NONE)));

fun code_decode_ordinary core =
  (if not (equal_wire_deadline (wire_deadline (wire_operation_body core))
            Deadline_Absent)
    then Code_Ordinary_Refused Invalid_Wire_Format
    else (case code_native_call_prefix core
           of NONE => Code_Ordinary_Refused Invalid_Wire_Format
           | SOME native =>
             (case decode_ordinary_operands core native
               of NONE => Code_Ordinary_Refused Invalid_Wire_Format
               | SOME (credential, (versions, command)) =>
                 (if not (equal_nata (wire_target_domain core)
                           (code_ordinary_endpoint native command))
                   then Code_Ordinary_Refused Invalid_Wire_Source
                   else (if not (code_ordinary_proofs_allowed native command)
                          then Code_Ordinary_Refused Invalid_Wire_Format
                          else Code_Ordinary_Ready
                                 (native, credential, versions, command))))));

fun code_ordinary_tree core =
  (case code_decode_ordinary core
    of Code_Ordinary_Refused a => Code_Tree_Refused a
    | Code_Ordinary_Ready (native, _, _, command) =>
      Code_Tree_Ready (Code_Nested_Ordinary (native, command)));

fun code_declared_version bytes =
  bind (code_take_varint bytes)
    (fn (packet_tag, packet_tail) =>
      (if not (equal_nata packet_tag (nat_of_integer (10 : IntInf.int)))
        then NONE
        else bind (code_take_varint packet_tail)
               (fn (declared_length, packet_body) =>
                 (if less_nat (size_list packet_body) declared_length then NONE
                   else bind (code_take_varint
                               (take declared_length packet_body))
                          (fn (core_tag, version_tail) =>
                            (if not (equal_nata core_tag
                                      (nat_of_integer (8 : IntInf.int)))
                              then NONE
                              else map_option fst
                                     (code_take_varint version_tail)))))));

fun json_context_endpoint
  (Code_json_endpoint_context_ext
    (json_context_endpoint, json_context_epoch, json_context_grants,
      json_context_dependencies, json_context_write_permissions, more))
  = json_context_endpoint;

fun code_json_complete parse bytes =
  (case parse bytes of NONE => NONE | SOME (value, []) => SOME value
    | SOME (_, _ :: _) => NONE);

fun code_json_contexts bytes =
  bind (code_json_complete
         (code_json_strict_list
           (fn first => fn second =>
             less_nat (json_context_endpoint first)
               (json_context_endpoint second))
           code_json_context)
         bytes)
    (fn values => (if null values then NONE else SOME values));

fun code_reference_accepts Wire_State_Sync operation =
  member equal_nat operation
    (atLeastAtMost (equal_nat, interval_nat) one_nata
      (nat_of_integer (6 : IntInf.int)))
  | code_reference_accepts Wire_Regulatory operation =
    member equal_nat operation
      (atLeastAtMost (equal_nat, interval_nat) one_nata
        (nat_of_integer (3 : IntInf.int)))
  | code_reference_accepts Wire_Lock operation =
    member equal_nat operation
      (atLeastAtMost (equal_nat, interval_nat) one_nata
        (nat_of_integer (6 : IntInf.int)))
  | code_reference_accepts Wire_Query operation =
    member equal_nat operation
      (atLeastAtMost (equal_nat, interval_nat) one_nata
        (nat_of_integer (8 : IntInf.int)))
  | code_reference_accepts Wire_Ack operation = equal_nata operation one_nata
  | code_reference_accepts Wire_Heartbeat operation = false
  | code_reference_accepts Wire_Governance operation =
    equal_nata operation one_nata;

fun code_same_original core original =
  equal_nata (wire_deployment core) (wire_deployment original) andalso
    (equal_nata (wire_source_domain core) (wire_source_domain original) andalso
      (equal_nata (wire_target_domain core)
         (wire_target_domain original) andalso
        (equal_nata (wire_principal core) (wire_principal original) andalso
          (equal_nata (wire_authority_epoch core)
             (wire_authority_epoch original) andalso
            equal_nata (wire_version original)
              (nat_of_integer (6 : IntInf.int))))));

fun reference_response_kind_number A_ Recorded_Result = one (one_numeral A_)
  | reference_response_kind_number A_ Delivery_Refusal = numeral A_ (Bit0 One)
  | reference_response_kind_number A_ Validation_Refusal =
    numeral A_ (Bit1 One);

fun reference_result_codes (A1_, A2_) kind committed =
  (case kind
    of Recorded_Result =>
      (if committed
        then atLeastAtMost (A1_, A2_)
               (numeral
                 ((numeral_semiring_numeral o semiring_numeral_semiring_1 o
                    semiring_1_comm_semiring_1 o
                    comm_semiring_1_comm_semiring_1_cancel o
                    comm_semiring_1_cancel_interval)
                   A2_)
                 (Bit0 (Bit1 (Bit0 One))))
               (numeral
                 ((numeral_semiring_numeral o semiring_numeral_semiring_1 o
                    semiring_1_comm_semiring_1 o
                    comm_semiring_1_comm_semiring_1_cancel o
                    comm_semiring_1_cancel_interval)
                   A2_)
                 (Bit0 (Bit0 (Bit1 (Bit1 One)))))
        else sup_set A1_
               (atLeastAtMost (A1_, A2_)
                 (one ((one_numeral o numeral_semiring_numeral o
                         semiring_numeral_semiring_1 o
                         semiring_1_comm_semiring_1 o
                         comm_semiring_1_comm_semiring_1_cancel o
                         comm_semiring_1_cancel_interval)
                        A2_))
                 (numeral
                   ((numeral_semiring_numeral o semiring_numeral_semiring_1 o
                      semiring_1_comm_semiring_1 o
                      comm_semiring_1_comm_semiring_1_cancel o
                      comm_semiring_1_cancel_interval)
                     A2_)
                   (Bit0 (Bit0 One))))
               (atLeastAtMost (A1_, A2_)
                 (numeral
                   ((numeral_semiring_numeral o semiring_numeral_semiring_1 o
                      semiring_1_comm_semiring_1 o
                      comm_semiring_1_comm_semiring_1_cancel o
                      comm_semiring_1_cancel_interval)
                     A2_)
                   (Bit0 (Bit1 (Bit1 (Bit1 One)))))
                 (numeral
                   ((numeral_semiring_numeral o semiring_numeral_semiring_1 o
                      semiring_1_comm_semiring_1 o
                      comm_semiring_1_comm_semiring_1_cancel o
                      comm_semiring_1_cancel_interval)
                     A2_)
                   (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 One))))))))
    | Delivery_Refusal =>
      (if committed then bot_set
        else atLeastAtMost (A1_, A2_)
               (numeral
                 ((numeral_semiring_numeral o semiring_numeral_semiring_1 o
                    semiring_1_comm_semiring_1 o
                    comm_semiring_1_comm_semiring_1_cancel o
                    comm_semiring_1_cancel_interval)
                   A2_)
                 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 One))))))
               (numeral
                 ((numeral_semiring_numeral o semiring_numeral_semiring_1 o
                    semiring_1_comm_semiring_1 o
                    comm_semiring_1_comm_semiring_1_cancel o
                    comm_semiring_1_cancel_interval)
                   A2_)
                 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 One)))))))
    | Validation_Refusal =>
      (if committed then bot_set
        else atLeastAtMost (A1_, A2_)
               (numeral
                 ((numeral_semiring_numeral o semiring_numeral_semiring_1 o
                    semiring_1_comm_semiring_1 o
                    comm_semiring_1_comm_semiring_1_cancel o
                    comm_semiring_1_cancel_interval)
                   A2_)
                 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 One)))))))
               (numeral
                 ((numeral_semiring_numeral o semiring_numeral_semiring_1 o
                    semiring_1_comm_semiring_1 o
                    comm_semiring_1_comm_semiring_1_cancel o
                    comm_semiring_1_cancel_interval)
                   A2_)
                 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 One)))))))));

fun code_response_words (A1_, A2_) call_id kind number position =
  (if member A1_ number
        (reference_result_codes (A1_, A2_) kind (not (is_none position)))
    then SOME ([fst call_id, snd call_id,
                 reference_response_kind_number
                   ((numeral_semiring_numeral o semiring_numeral_semiring_1 o
                      semiring_1_comm_semiring_1 o
                      comm_semiring_1_comm_semiring_1_cancel o
                      comm_semiring_1_cancel_interval)
                     A2_)
                   kind,
                 number] @
                (case position
                  of NONE =>
                    [zero ((zero_mult_zero o mult_zero_semiring_0 o
                             semiring_0_semiring_1 o
                             semiring_1_comm_semiring_1 o
                             comm_semiring_1_comm_semiring_1_cancel o
                             comm_semiring_1_cancel_interval)
                            A2_)]
                  | SOME revision =>
                    [one ((one_numeral o numeral_semiring_numeral o
                            semiring_numeral_semiring_1 o
                            semiring_1_comm_semiring_1 o
                            comm_semiring_1_comm_semiring_1_cancel o
                            comm_semiring_1_cancel_interval)
                           A2_),
                      revision]))
    else NONE);

fun sync_read_operands core =
  let
    val body = wire_operation_body core;
  in
    (if not (equal_wire_familya (wire_message_family core)
              Wire_State_Sync) orelse
          (not (equal_nata (wire_opcode body)
                 (nat_of_integer (7 : IntInf.int))) orelse
            not (equal_wire_deadline (wire_deadline body) Deadline_Absent))
      then NONE
      else (case (wire_words body, wire_blobs body) of ([], _) => NONE
             | ([_], _) => NONE | ([_, _], _) => NONE | ([_, _, _], _) => NONE
             | ([_, _, _, _], _) => NONE | ([_, _, _, _, _], _) => NONE
             | ([_, _, _, _, _, _], _) => NONE
             | ([_, _, _, _, _, _, _], _) => NONE
             | ([_, _, _, _, _, _, _, _], _) => NONE
             | ([_, _, _, _, _, _, _, _, _], _) => NONE
             | ([_, _, _, _, _, _, _, _, _, _], []) => NONE
             | ([_, _, _, _, _, _, _, _, _, _], [_]) => NONE
             | ([_, _, _, _, _, _, _, _, _, _], [_, _]) => NONE
             | ([message, call_sequence, session, revision_word, epoch, origin,
                  event, asset, pos, mode],
                 [commitment, prior, proof])
               => bind (sync_mode_at mode)
                    (fn m =>
                      (if equal_nata (size_list commitment)
                            (nat_of_integer (32 : IntInf.int)) andalso
                            equal_nata (size_list prior)
                              (if equal_sync_mode m Sync_Incremental
                                then nat_of_integer (32 : IntInf.int)
                                else zero_nata)
                        then SOME (Sync_request_ext
                                    ((wire_principal core, call_sequence),
                                      message, session,
                                      Product_cut_ext
(wire_authority_epoch core, revision_word, ()),
                                      (asset, origin),
                                      Sync_entry_ext
(commitment, pos, epoch, event, ()),
                                      m, (if equal_sync_mode m Sync_Incremental
   then SOME prior else NONE),
                                      proof, ()))
                        else NONE))
             | ([_, _, _, _, _, _, _, _, _, _], _ :: _ :: _ :: _ :: _) => NONE
             | (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, _) =>
               NONE))
  end;

fun response_parameter_principal
  (Response_fixed_parameters_ext
    (response_parameter_principal, response_parameter_key,
      response_parameter_epoch, response_parameter_issued,
      response_parameter_ttl, response_parameter_uuid, response_parameter_route,
      more))
  = response_parameter_principal;

fun response_parameter_issued
  (Response_fixed_parameters_ext
    (response_parameter_principal, response_parameter_key,
      response_parameter_epoch, response_parameter_issued,
      response_parameter_ttl, response_parameter_uuid, response_parameter_route,
      more))
  = response_parameter_issued;

fun response_parameter_route
  (Response_fixed_parameters_ext
    (response_parameter_principal, response_parameter_key,
      response_parameter_epoch, response_parameter_issued,
      response_parameter_ttl, response_parameter_uuid, response_parameter_route,
      more))
  = response_parameter_route;

fun response_parameter_epoch
  (Response_fixed_parameters_ext
    (response_parameter_principal, response_parameter_key,
      response_parameter_epoch, response_parameter_issued,
      response_parameter_ttl, response_parameter_uuid, response_parameter_route,
      more))
  = response_parameter_epoch;

fun response_channel_deployment
  (Response_fixed_channel_ext
    (response_channel_profile, response_channel_deployment,
      response_channel_local, response_channel_remote, response_channel_expires,
      response_channel_local_key, response_channel_remote_key, more))
  = response_channel_deployment;

fun response_parameter_uuid
  (Response_fixed_parameters_ext
    (response_parameter_principal, response_parameter_key,
      response_parameter_epoch, response_parameter_issued,
      response_parameter_ttl, response_parameter_uuid, response_parameter_route,
      more))
  = response_parameter_uuid;

fun response_parameter_ttl
  (Response_fixed_parameters_ext
    (response_parameter_principal, response_parameter_key,
      response_parameter_epoch, response_parameter_issued,
      response_parameter_ttl, response_parameter_uuid, response_parameter_route,
      more))
  = response_parameter_ttl;

fun response_parameter_key
  (Response_fixed_parameters_ext
    (response_parameter_principal, response_parameter_key,
      response_parameter_epoch, response_parameter_issued,
      response_parameter_ttl, response_parameter_uuid, response_parameter_route,
      more))
  = response_parameter_key;

fun response_channel_remote
  (Response_fixed_channel_ext
    (response_channel_profile, response_channel_deployment,
      response_channel_local, response_channel_remote, response_channel_expires,
      response_channel_local_key, response_channel_remote_key, more))
  = response_channel_remote;

fun response_channel_local
  (Response_fixed_channel_ext
    (response_channel_profile, response_channel_deployment,
      response_channel_local, response_channel_remote, response_channel_expires,
      response_channel_local_key, response_channel_remote_key, more))
  = response_channel_local;

fun response_fixed_core channel parameters atomicity words original =
  Wire_core_ext
    (nat_of_integer (6 : IntInf.int), one_nata,
      response_channel_deployment channel, response_channel_local channel,
      response_channel_remote channel, response_parameter_principal parameters,
      response_parameter_key parameters, response_parameter_epoch parameters,
      response_parameter_issued parameters, response_parameter_ttl parameters,
      response_parameter_uuid parameters, Wire_Ack, one_nata, NONE, one_nata,
      Wire_body_ext
        (nat_of_integer (2 : IntInf.int), words, [original], Deadline_Absent,
          ()),
      atomicity, nat_of_integer (3 : IntInf.int),
      response_parameter_route parameters, ());

fun response_kind_at number =
  (if equal_nata number one_nata then SOME Recorded_Result
    else (if equal_nata number (nat_of_integer (2 : IntInf.int))
           then SOME Delivery_Refusal
           else (if equal_nata number (nat_of_integer (3 : IntInf.int))
                  then SOME Validation_Refusal else NONE)));

fun reference_accepts_write family opcode =
  code_reference_accepts family opcode orelse
    equal_wire_familya family Wire_Lock andalso
      equal_nata opcode (nat_of_integer (7 : IntInf.int));

val sync_response_operation : wire_family * nat =
  (Wire_State_Sync, nat_of_integer (7 : IntInf.int));

val sync_response_allocations :
  (nat * (reference_response_kind * (bool * (wire_family * nat) list))) list
  = [(nat_of_integer (29 : IntInf.int),
       (Recorded_Result, (true, [sync_response_operation]))),
      (nat_of_integer (39 : IntInf.int),
        (Recorded_Result, (false, [sync_response_operation]))),
      (nat_of_integer (40 : IntInf.int),
        (Recorded_Result, (false, [sync_response_operation]))),
      (nat_of_integer (41 : IntInf.int),
        (Recorded_Result, (false, [sync_response_operation])))];

fun response_fixed_descriptor number =
  (if member equal_nat number
        (sup_set equal_nat
          (insert equal_nat one_nata
            (insert equal_nat (nat_of_integer (2 : IntInf.int))
              (insert equal_nat (nat_of_integer (3 : IntInf.int))
                (insert equal_nat (nat_of_integer (4 : IntInf.int)) bot_set))))
          (atLeastAtMost (equal_nat, interval_nat)
            (nat_of_integer (30 : IntInf.int))
            (nat_of_integer (38 : IntInf.int))))
    then SOME (Recorded_Result, false)
    else (if member equal_nat number
               (atLeastAtMost (equal_nat, interval_nat)
                 (nat_of_integer (10 : IntInf.int))
                 (nat_of_integer (28 : IntInf.int)))
           then SOME (Recorded_Result, true)
           else (if member equal_nat number
                      (atLeastAtMost (equal_nat, interval_nat)
                        (nat_of_integer (50 : IntInf.int))
                        (nat_of_integer (56 : IntInf.int)))
                  then SOME (Delivery_Refusal, false)
                  else (if member equal_nat number
                             (atLeastAtMost (equal_nat, interval_nat)
                               (nat_of_integer (70 : IntInf.int))
                               (nat_of_integer (77 : IntInf.int)))
                         then SOME (Validation_Refusal, false) else NONE))));

fun response_fixed_words call_id result =
  let
    val (number, position) = result;
  in
    (case response_fixed_descriptor number of NONE => NONE
      | SOME (kind, needs_commit) =>
        (if not (equal_bool needs_commit (not (is_none position))) then NONE
          else map_option (fn words => (kind, (number, (position, words))))
                 (code_response_words (equal_nat, interval_nat) call_id kind
                   number position)))
  end;

fun response_v061_words call result =
  let
    val (number, position) = result;
  in
    (case map_of equal_nat sync_response_allocations number
      of NONE => response_fixed_words call result
      | SOME (kind, (needs_commit, _)) =>
        (if not (equal_bool needs_commit (not (is_none position))) then NONE
          else SOME (kind,
                      (number,
                        (position,
                          [fst call, snd call,
                            reference_response_kind_number numeral_nat kind,
                            number] @
                            (case position of NONE => [zero_nata]
                              | SOME revision => [one_nata, revision]))))))
  end;

fun response_client_max_nesting
  (Response_fixed_client_boundary_ext
    (response_client_scope, response_client_public_key,
      response_client_max_nesting, more))
  = response_client_max_nesting;

fun response_client_public_key
  (Response_fixed_client_boundary_ext
    (response_client_scope, response_client_public_key,
      response_client_max_nesting, more))
  = response_client_public_key;

fun response_client_scope
  (Response_fixed_client_boundary_ext
    (response_client_scope, response_client_public_key,
      response_client_max_nesting, more))
  = response_client_scope;

fun response_channel_remote_key
  (Response_fixed_channel_ext
    (response_channel_profile, response_channel_deployment,
      response_channel_local, response_channel_remote, response_channel_expires,
      response_channel_local_key, response_channel_remote_key, more))
  = response_channel_remote_key;

fun response_channel_profile
  (Response_fixed_channel_ext
    (response_channel_profile, response_channel_deployment,
      response_channel_local, response_channel_remote, response_channel_expires,
      response_channel_local_key, response_channel_remote_key, more))
  = response_channel_profile;

fun response_channel_expires
  (Response_fixed_channel_ext
    (response_channel_profile, response_channel_deployment,
      response_channel_local, response_channel_remote, response_channel_expires,
      response_channel_local_key, response_channel_remote_key, more))
  = response_channel_expires;

fun boundary_profile_update boundary_profilea
  (Wire_boundary_ext
    (boundary_profile, boundary_deployment, boundary_source, boundary_target,
      boundary_principal, boundary_key, boundary_epoch, boundary_route_scope,
      boundary_now, boundary_asset_ttl_floor, boundary_future_skew,
      boundary_max_frame, boundary_version_floor, boundary_critical_allowed,
      boundary_threshold_supported, more))
  = Wire_boundary_ext
      (boundary_profilea boundary_profile, boundary_deployment, boundary_source,
        boundary_target, boundary_principal, boundary_key, boundary_epoch,
        boundary_route_scope, boundary_now, boundary_asset_ttl_floor,
        boundary_future_skew, boundary_max_frame, boundary_version_floor,
        boundary_critical_allowed, boundary_threshold_supported, more);

fun response_decoded_original_bytes
  (Response_fixed_decoded_ext
    (response_decoded_id, response_decoded_kind, response_decoded_number,
      response_decoded_position, response_decoded_original_bytes,
      response_decoded_original, more))
  = response_decoded_original_bytes;

fun response_decoded_position
  (Response_fixed_decoded_ext
    (response_decoded_id, response_decoded_kind, response_decoded_number,
      response_decoded_position, response_decoded_original_bytes,
      response_decoded_original, more))
  = response_decoded_position;

fun response_decoded_number
  (Response_fixed_decoded_ext
    (response_decoded_id, response_decoded_kind, response_decoded_number,
      response_decoded_position, response_decoded_original_bytes,
      response_decoded_original, more))
  = response_decoded_number;

fun response_decoded_kind
  (Response_fixed_decoded_ext
    (response_decoded_id, response_decoded_kind, response_decoded_number,
      response_decoded_position, response_decoded_original_bytes,
      response_decoded_original, more))
  = response_decoded_kind;

fun response_decoded_id
  (Response_fixed_decoded_ext
    (response_decoded_id, response_decoded_kind, response_decoded_number,
      response_decoded_position, response_decoded_original_bytes,
      response_decoded_original, more))
  = response_decoded_id;

fun response_v061_result_of_view view =
  (response_decoded_id view,
    (response_decoded_kind view,
      (response_decoded_number view, response_decoded_position view)));

fun code_decode_query_nonreceipt core =
  (if not (equal_wire_deadline (wire_deadline (wire_operation_body core))
            Deadline_Absent)
    then NONE else decode_wire_query_body core);

fun code_response_commit_matches position revision =
  (case position of NONE => true
    | SOME retained => equal_nata retained revision);

fun native_cut
  (Wire_native_call_ext
    (native_reference, native_id, native_session, native_cut,
      native_origin_epoch, native_origin, native_asset, native_funding_owner,
      native_destination, native_recipient, native_amount, native_tail_words,
      native_proof_bytes, more))
  = native_cut;

fun code_check_nested_response nested (Code_Nested_Ordinary (native, command))
  call_id position =
  (if not (equal_proda equal_nat equal_nat (native_id native) call_id) orelse
        (case command of Wire_Reserve _ => false | Wire_Dispatch _ => false
          | Wire_Debit _ => true | Wire_Cancel _ => false
          | Wire_Fence _ => false | Wire_Preempt _ => false
          | Wire_Timeout _ => false | Wire_Record_Terminal (_, _) => false
          | Wire_Deliver _ => false | Wire_Refund (_, _) => false
          | Wire_Reconcile (_, _) => false | Wire_Write (_, _) => false
          | Wire_Publish => false) andalso
          not (code_response_commit_matches position
                (cut_revision (native_cut native)))
    then SOME Invalid_Wire_Format else NONE)
  | code_check_nested_response nested (Code_Nested_Legal nested_id) call_id
    position =
    (if not (equal_proda equal_nat equal_nat nested_id call_id)
      then SOME Invalid_Wire_Format else NONE)
  | code_check_nested_response nested (Code_Nested_Spend nested_id) call_id
    position =
    (if not (equal_proda equal_nat equal_nat nested_id call_id)
      then SOME Invalid_Wire_Format else NONE)
  | code_check_nested_response nested (Code_Nested_Receipt original) call_id
    position =
    (if not (code_same_original nested original) then SOME Invalid_Wire_Source
      else (case code_native_call_prefix original
             of NONE => SOME Invalid_Wire_Format
             | SOME native =>
               (if not (equal_proda equal_nat equal_nat (native_id native)
                         call_id) orelse
                     equal_wire_familya (wire_message_family original)
                       Wire_State_Sync andalso
                       (equal_nata (wire_opcode (wire_operation_body original))
                          one_nata andalso
                         not (code_response_commit_matches position
                               (cut_revision (native_cut native))))
                 then SOME Invalid_Wire_Format else NONE)))
  | code_check_nested_response nested Code_Nested_Response call_id position =
    SOME Invalid_Wire_Format
  | code_check_nested_response nested Code_Nested_Other call_id position = NONE;

fun response_result_words words =
  (case words of [] => NONE | [_] => NONE | [_, _] => NONE | [_, _, _] => NONE
    | [_, _, _, _] => NONE
    | [namespace, sequence, kind, code, present] =>
      (if equal_nata present zero_nata
        then map_option (fn tag => ((namespace, sequence), (tag, (code, NONE))))
               (response_kind_at kind)
        else NONE)
    | [namespace, sequence, kind, code, present, revision] =>
      (if equal_nata present one_nata
        then map_option
               (fn tag => ((namespace, sequence), (tag, (code, SOME revision))))
               (response_kind_at kind)
        else NONE)
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => NONE);

fun code_response_tree_finish core nested decoded =
  (case response_result_words (wire_words (wire_operation_body core))
    of NONE => Code_Tree_Refused Invalid_Wire_Format
    | SOME (call_id, (kind, (_, position))) =>
      (if not (equal_reference_response_kinda kind Recorded_Result) andalso
            not (is_none position)
        then Code_Tree_Refused Invalid_Wire_Format
        else (if not (equal_nata (wire_version nested)
                       (wire_version core)) orelse
                   (not (equal_nata (wire_deployment nested)
                          (wire_deployment core)) orelse
                     (not (equal_nata (wire_principal nested)
                            (fst call_id)) orelse
                       (not (equal_nata (wire_source_domain nested)
                              (wire_target_domain core)) orelse
                         not (equal_nata (wire_target_domain nested)
                               (wire_source_domain core)))))
               then Code_Tree_Refused Invalid_Wire_Source
               else (case code_check_nested_response nested decoded call_id
                            position
                      of NONE => Code_Tree_Ready Code_Nested_Response
                      | SOME a => Code_Tree_Refused a))));

fun code_response_tree_after_nested core nested result =
  (case result of Code_Tree_Refused a => Code_Tree_Refused a
    | Code_Tree_Ready a => code_response_tree_finish core nested a
    | Code_Tree_Pending => Code_Tree_Pending);

fun code_json_session_binding bytes =
  bind (code_json_first_field
         [Chara (false, false, false, false, true, true, true, false),
           Chara (false, true, false, false, true, true, true, false),
           Chara (true, false, false, true, false, true, true, false),
           Chara (false, true, true, true, false, true, true, false),
           Chara (true, true, false, false, false, true, true, false),
           Chara (true, false, false, true, false, true, true, false),
           Chara (false, false, false, false, true, true, true, false),
           Chara (true, false, false, false, false, true, true, false),
           Chara (false, false, true, true, false, true, true, false)]
         code_json_u64 bytes)
    (fn (principal, r0) =>
      bind (code_json_next_field
             [Chara (true, false, false, false, false, true, true, false),
               Chara (true, false, true, false, true, true, true, false),
               Chara (false, false, true, false, true, true, true, false),
               Chara (false, false, false, true, false, true, true, false),
               Chara (true, true, true, true, false, true, true, false),
               Chara (false, true, false, false, true, true, true, false),
               Chara (true, false, false, true, false, true, true, false),
               Chara (false, false, true, false, true, true, true, false),
               Chara (true, false, false, true, true, true, true, false),
               Chara (true, true, true, true, true, false, true, false),
               Chara (true, false, true, false, false, true, true, false),
               Chara (false, false, false, false, true, true, true, false),
               Chara (true, true, true, true, false, true, true, false),
               Chara (true, true, false, false, false, true, true, false),
               Chara (false, false, false, true, false, true, true, false)]
             code_json_u64 r0)
        (fn (epoch, r1) =>
          map_option
            (fn a => (Code_json_session_binding_ext (principal, epoch, ()), a))
            (code_json_expect [nat_of_integer (125 : IntInf.int)] r1)));

fun code_json_session_entry x =
  code_json_pair code_json_u64 code_json_session_binding x;

fun code_json_session_bindings bytes =
  code_json_complete
    (code_json_strict_list
      (fn first => fn second => less_nat (fst first) (fst second))
      code_json_session_entry)
    bytes;

fun code_decode_governance core =
  let
    val body = wire_operation_body core;
  in
    (if not (equal_wire_deadline (wire_deadline body) Deadline_Absent) then NONE
      else (case (wire_words body, wire_blobs body) of ([], _) => NONE
             | ([_], _) => NONE | (_ :: _ :: _, []) => NONE
             | (_ :: _ :: _, [_]) => NONE | (_ :: _ :: _, [_, _]) => NONE
             | (session :: revision :: tail, [batch, first, second]) =>
               (if null first orelse null second then NONE
                 else bind (code_json_contexts batch)
                        (fn contexts =>
                          let
                            val cut =
                              Product_cut_ext
                                (wire_authority_epoch core, revision, ());
                          in
                            (if equal_nata (wire_opcode body) one_nata
                              then (case tail of [] => NONE | [_] => NONE
                                     | [_, _] => NONE | [_, _, _] => NONE
                                     | [_, _, _, _] => NONE
                                     | [_, _, _, _, _] => NONE
                                     | [asset, previous, successor, old_session,
 new_session, epoch]
                                       => SOME
    (Code_Governance_Handover
      (session, cut, asset, previous, successor, old_session, new_session,
        epoch, contexts, first, second))
                                     | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ =>
                                       NONE)
                              else (case tail of [] => NONE
                                     | [epoch] =>
                                       map_option
 (fn sessions =>
   Code_Governance_Install (session, cut, epoch, contexts, sessions, second))
 (code_json_session_bindings first)
                                     | _ :: _ :: _ => NONE))
                          end))
             | (_ :: _ :: _, _ :: _ :: _ :: _ :: _) => NONE))
  end;

fun code_decode_heartbeat core =
  let
    val body = wire_operation_body core;
  in
    (if not (null (wire_blobs body)) orelse
          not (equal_wire_deadline (wire_deadline body) Deadline_Absent)
      then NONE
      else (case wire_words body of [] => NONE | [_] => NONE
             | challenge :: expires :: tail =>
               (if equal_nata (wire_opcode body) one_nata
                 then bind (code_take_ordered_set tail)
                        (fn (versions, first) =>
                          bind (code_take_ordered_set first)
                            (fn (families, second) =>
                              bind (code_take_ordered_set second)
                                (fn (atomicities, third) =>
                                  bind (code_take_ordered_set third)
                                    (fn (schemes, last) =>
                                      (if null last
then SOME (Code_Capabilities
            (challenge, expires, versions, families, atomicities, schemes))
else NONE)))))
                 else (if null tail
                        then SOME (Code_Liveness (challenge, expires))
                        else NONE))))
  end;

fun code_decode_settlement_ack core =
  let
    val body = wire_operation_body core;
  in
    (if not (equal_wire_familya (wire_message_family core) Wire_Ack) orelse
          (not (equal_nata (wire_opcode body) one_nata) orelse
            not (equal_wire_deadline (wire_deadline body) Deadline_Absent))
      then NONE
      else (case (wire_words body, wire_blobs body) of ([], _) => NONE
             | ([_], _) => NONE | ([_, _], _) => NONE | ([_, _, _], _) => NONE
             | ([_, _, _, _], _) => NONE | ([_, _, _, _, _], _) => NONE
             | ([_, _, _, _, _, _], _) => NONE
             | ([_, _, _, _, _, _, _], _) => NONE
             | ([_, _, _, _, _, _, _, _], _) => NONE
             | ([_, _, _, _, _, _, _, _, _], _) => NONE
             | ([_, _, _, _, _, _, _, _, _, _], []) => NONE
             | ([domain, event, position, target, asset, owner, destination,
                  recipient, epoch, kind],
                 [raw])
               => (if not (member equal_nat kind
                            (insert equal_nat one_nata
                              (insert equal_nat
                                (nat_of_integer (2 : IntInf.int)) bot_set)))
                    then NONE
                    else map_option
                           (fn amount =>
                             Native_scheduled_ack_ext
                               (((domain, event), position), target, asset,
                                 owner, destination, recipient, amount, epoch,
                                 (if equal_nata kind one_nata
                                   then Confirmed_Decision
                                   else Reversed_Decision),
                                 ()))
                           (code_product_amount raw))
             | ([_, _, _, _, _, _, _, _, _, _], _ :: _ :: _) => NONE
             | (_ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, _) =>
               NONE))
  end;

fun code_receipt_tree_finish original decoded =
  (case decoded of Code_Tree_Refused a => Code_Tree_Refused a
    | Code_Tree_Ready (Code_Nested_Ordinary (_, _)) =>
      Code_Tree_Ready (Code_Nested_Receipt original)
    | Code_Tree_Ready (Code_Nested_Legal _) =>
      Code_Tree_Ready (Code_Nested_Receipt original)
    | Code_Tree_Ready (Code_Nested_Spend _) =>
      Code_Tree_Ready (Code_Nested_Receipt original)
    | Code_Tree_Ready (Code_Nested_Receipt _) =>
      Code_Tree_Refused Invalid_Wire_Format
    | Code_Tree_Ready Code_Nested_Response =>
      Code_Tree_Refused Invalid_Wire_Format
    | Code_Tree_Ready Code_Nested_Other => Code_Tree_Refused Invalid_Wire_Format
    | Code_Tree_Pending => Code_Tree_Pending);

fun code_decode_operand_tree fuel core =
  (if equal_nata fuel zero_nata then Code_Tree_Refused Invalid_Wire_Format
    else let
           val body = wire_operation_body core;
           val family = wire_message_family core;
           val operation = wire_opcode body;
         in
           (if equal_wire_familya family Wire_State_Sync andalso
                 equal_nata operation (nat_of_integer (6 : IntInf.int)) orelse
                 equal_wire_familya family Wire_Regulatory andalso
                   equal_nata operation (nat_of_integer (3 : IntInf.int))
             then code_spend_tree core
             else (if member equal_wire_family family
                        (insert equal_wire_family Wire_State_Sync
                          (insert equal_wire_family Wire_Lock bot_set))
                    then code_ordinary_tree core
                    else (if equal_wire_familya family Wire_Regulatory
                           then code_legal_tree core
                           else (if equal_wire_familya family Wire_Query
                                  then (if equal_nata operation
     (nat_of_integer (8 : IntInf.int))
 then (case (wire_words body, wire_blobs body)
        of ([], _) => Code_Tree_Refused Invalid_Wire_Format
        | ([_], []) => Code_Tree_Refused Invalid_Wire_Format
        | ([_], [original_bytes]) =>
          (if not (equal_wire_deadline (wire_deadline body)
                    Deadline_Absent) orelse
                equal_nata (minus_nata fuel one_nata) zero_nata
            then Code_Tree_Refused Invalid_Wire_Format
            else (case decode_wire_core original_bytes
                   of NONE => Code_Tree_Refused Invalid_Wire_Format
                   | SOME original =>
                     code_receipt_tree_finish original
                       (code_decode_operand_tree (minus_nata fuel one_nata)
                         original)))
        | ([_], _ :: _ :: _) => Code_Tree_Refused Invalid_Wire_Format
        | (_ :: _ :: _, _) => Code_Tree_Refused Invalid_Wire_Format)
 else (case code_decode_query_nonreceipt core
        of NONE => Code_Tree_Refused Invalid_Wire_Format
        | SOME _ => Code_Tree_Ready Code_Nested_Other))
                                  else (if equal_wire_familya family Wire_Ack
 then (if equal_nata operation (nat_of_integer (2 : IntInf.int))
        then (if not (equal_wire_deadline (wire_deadline body) Deadline_Absent)
               then Code_Tree_Refused Invalid_Wire_Format
               else (case wire_blobs body
                      of [] => Code_Tree_Refused Invalid_Wire_Format
                      | [original_bytes] =>
                        (case decode_wire_core original_bytes
                          of NONE => Code_Tree_Refused Invalid_Wire_Format
                          | SOME original =>
                            code_response_tree_after_nested core original
                              (code_decode_operand_tree
                                (minus_nata fuel one_nata) original))
                      | _ :: _ :: _ => Code_Tree_Refused Invalid_Wire_Format))
        else (case code_decode_settlement_ack core
               of NONE => Code_Tree_Refused Invalid_Wire_Format
               | SOME _ => Code_Tree_Ready Code_Nested_Other))
 else (if equal_wire_familya family Wire_Heartbeat
        then (case code_decode_heartbeat core
               of NONE => Code_Tree_Refused Invalid_Wire_Format
               | SOME _ => Code_Tree_Ready Code_Nested_Other)
        else (if equal_wire_familya family Wire_Governance
               then (case code_decode_governance core
                      of NONE => Code_Tree_Refused Invalid_Wire_Format
                      | SOME _ => Code_Tree_Ready Code_Nested_Other)
               else Code_Tree_Refused Invalid_Wire_Format)))))))
         end);

fun response_fixed_expected_decode core =
  (case code_decode_operand_tree one_nata core of Code_Tree_Refused a => Inl a
    | Code_Tree_Ready a => Inr a
    | Code_Tree_Pending => Inl Invalid_Wire_Format);

fun sync_call
  (Sync_request_ext
    (sync_call, sync_message, sync_session, sync_signed_cut, sync_key,
      sync_requested, sync_mode, sync_claimed_prior, sync_attestation, more))
  = sync_call;

fun code_known_response_number (A1_, A2_) number =
  member A1_ number
    (sup_set A1_
      (sup_set A1_
        (sup_set A1_ (reference_result_codes (A1_, A2_) Recorded_Result true)
          (reference_result_codes (A1_, A2_) Recorded_Result false))
        (reference_result_codes (A1_, A2_) Delivery_Refusal false))
      (reference_result_codes (A1_, A2_) Validation_Refusal false));

fun code_decode_response_status kind number committed =
  (if code_known_response_number (equal_nat, interval_nat) number
    then (if member equal_nat number
               (reference_result_codes (equal_nat, interval_nat) kind committed)
           then SOME (Code_Known_Response (kind, number)) else NONE)
    else (if not (equal_reference_response_kinda kind Recorded_Result) andalso
               committed
           then NONE else SOME (Code_Unknown_Response (kind, number))));

fun reference_result_targets code =
  (if equal_nata code (nat_of_integer (10 : IntInf.int))
    then insert (equal_prod equal_wire_family equal_nat) (Wire_Lock, one_nata)
           bot_set
    else (if equal_nata code (nat_of_integer (11 : IntInf.int))
           then insert (equal_prod equal_wire_family equal_nat)
                  (Wire_Lock, nat_of_integer (2 : IntInf.int)) bot_set
           else (if member equal_nat code
                      (insert equal_nat (nat_of_integer (4 : IntInf.int))
                        (insert equal_nat (nat_of_integer (12 : IntInf.int))
                          bot_set))
                  then insert (equal_prod equal_wire_family equal_nat)
                         (Wire_State_Sync, one_nata) bot_set
                  else (if equal_nata code (nat_of_integer (13 : IntInf.int))
                         then insert (equal_prod equal_wire_family equal_nat)
                                (Wire_Lock, nat_of_integer (3 : IntInf.int))
                                (insert (equal_prod equal_wire_family equal_nat)
                                  (Wire_Lock, nat_of_integer (4 : IntInf.int))
                                  bot_set)
                         else (if equal_nata code
                                    (nat_of_integer (14 : IntInf.int))
                                then insert
                                       (equal_prod equal_wire_family equal_nat)
                                       (Wire_Lock,
 nat_of_integer (5 : IntInf.int))
                                       bot_set
                                else (if equal_nata code
   (nat_of_integer (15 : IntInf.int))
                                       then insert
      (equal_prod equal_wire_family equal_nat)
      (Wire_Lock, nat_of_integer (8 : IntInf.int)) bot_set
                                       else (if member equal_nat code
          (insert equal_nat (nat_of_integer (16 : IntInf.int))
            (insert equal_nat (nat_of_integer (21 : IntInf.int))
              (insert equal_nat (nat_of_integer (23 : IntInf.int)) bot_set)))
      then insert (equal_prod equal_wire_family equal_nat)
             (Wire_State_Sync, nat_of_integer (2 : IntInf.int)) bot_set
      else (if member equal_nat code
                 (insert equal_nat (nat_of_integer (17 : IntInf.int))
                   (insert equal_nat (nat_of_integer (24 : IntInf.int))
                     bot_set))
             then insert (equal_prod equal_wire_family equal_nat)
                    (Wire_State_Sync, nat_of_integer (3 : IntInf.int)) bot_set
             else (if equal_nata code (nat_of_integer (18 : IntInf.int))
                    then insert (equal_prod equal_wire_family equal_nat)
                           (Wire_Lock, nat_of_integer (6 : IntInf.int)) bot_set
                    else (if member equal_nat code
                               (insert equal_nat
                                 (nat_of_integer (19 : IntInf.int))
                                 (insert equal_nat
                                   (nat_of_integer (25 : IntInf.int)) bot_set))
                           then insert (equal_prod equal_wire_family equal_nat)
                                  (Wire_State_Sync,
                                    nat_of_integer (4 : IntInf.int))
                                  bot_set
                           else (if equal_nata code
                                      (nat_of_integer (20 : IntInf.int))
                                  then insert
 (equal_prod equal_wire_family equal_nat)
 (Wire_Lock, nat_of_integer (7 : IntInf.int)) bot_set
                                  else (if equal_nata code
     (nat_of_integer (22 : IntInf.int))
 then insert (equal_prod equal_wire_family equal_nat)
        (Wire_State_Sync, nat_of_integer (5 : IntInf.int)) bot_set
 else (if equal_nata code (nat_of_integer (26 : IntInf.int))
        then insert (equal_prod equal_wire_family equal_nat)
               (Wire_Regulatory, one_nata) bot_set
        else (if equal_nata code (nat_of_integer (27 : IntInf.int))
               then insert (equal_prod equal_wire_family equal_nat)
                      (Wire_Regulatory, nat_of_integer (2 : IntInf.int)) bot_set
               else (if equal_nata code (nat_of_integer (28 : IntInf.int))
                      then insert (equal_prod equal_wire_family equal_nat)
                             (Wire_State_Sync, nat_of_integer (6 : IntInf.int))
                             (insert (equal_prod equal_wire_family equal_nat)
                               (Wire_Regulatory,
                                 nat_of_integer (3 : IntInf.int))
                               bot_set)
                      else (if member equal_nat code
                                 (atLeastAtMost (equal_nat, interval_nat)
                                   (nat_of_integer (30 : IntInf.int))
                                   (nat_of_integer (38 : IntInf.int)))
                             then insert
                                    (equal_prod equal_wire_family equal_nat)
                                    (Wire_Regulatory, one_nata)
                                    (insert
                                      (equal_prod equal_wire_family equal_nat)
                                      (Wire_Regulatory,
nat_of_integer (2 : IntInf.int))
                                      bot_set)
                             else bot_set))))))))))))))));

fun reference_response_compatible family opcode kind code committed =
  member equal_nat code
    (reference_result_codes (equal_nat, interval_nat) kind committed) andalso
    (member (equal_prod equal_wire_family equal_nat) (family, opcode)
       (reference_result_targets code) orelse
      (not (equal_reference_response_kinda kind Recorded_Result) orelse
        member equal_nat code
          (insert equal_nat one_nata
            (insert equal_nat (nat_of_integer (2 : IntInf.int))
              (insert equal_nat (nat_of_integer (3 : IntInf.int))
                bot_set)))) andalso
        (equal_wire_familya family Wire_State_Sync andalso
           member equal_nat opcode
             (atLeastAtMost (equal_nat, interval_nat) one_nata
               (nat_of_integer (6 : IntInf.int))) orelse
          (equal_wire_familya family Wire_Regulatory andalso
             member equal_nat opcode
               (atLeastAtMost (equal_nat, interval_nat) one_nata
                 (nat_of_integer (3 : IntInf.int))) orelse
            equal_wire_familya family Wire_Lock andalso
              member equal_nat opcode
                (atLeastAtMost (equal_nat, interval_nat) one_nata
                  (nat_of_integer (8 : IntInf.int))))));

fun code_response_call_shape (A1_, A2_) family operation =
  equal_wire_familya family Wire_State_Sync andalso
    member A1_ operation
      (atLeastAtMost (A1_, A2_)
        (one ((one_numeral o numeral_semiring_numeral o
                semiring_numeral_semiring_1 o semiring_1_comm_semiring_1 o
                comm_semiring_1_comm_semiring_1_cancel o
                comm_semiring_1_cancel_interval)
               A2_))
        (numeral
          ((numeral_semiring_numeral o semiring_numeral_semiring_1 o
             semiring_1_comm_semiring_1 o
             comm_semiring_1_comm_semiring_1_cancel o
             comm_semiring_1_cancel_interval)
            A2_)
          (Bit0 (Bit1 One)))) orelse
    (equal_wire_familya family Wire_Regulatory andalso
       member A1_ operation
         (atLeastAtMost (A1_, A2_)
           (one ((one_numeral o numeral_semiring_numeral o
                   semiring_numeral_semiring_1 o semiring_1_comm_semiring_1 o
                   comm_semiring_1_comm_semiring_1_cancel o
                   comm_semiring_1_cancel_interval)
                  A2_))
           (numeral
             ((numeral_semiring_numeral o semiring_numeral_semiring_1 o
                semiring_1_comm_semiring_1 o
                comm_semiring_1_comm_semiring_1_cancel o
                comm_semiring_1_cancel_interval)
               A2_)
             (Bit1 One))) orelse
      equal_wire_familya family Wire_Lock andalso
        member A1_ operation
          (atLeastAtMost (A1_, A2_)
            (one ((one_numeral o numeral_semiring_numeral o
                    semiring_numeral_semiring_1 o semiring_1_comm_semiring_1 o
                    comm_semiring_1_comm_semiring_1_cancel o
                    comm_semiring_1_cancel_interval)
                   A2_))
            (numeral
              ((numeral_semiring_numeral o semiring_numeral_semiring_1 o
                 semiring_1_comm_semiring_1 o
                 comm_semiring_1_comm_semiring_1_cancel o
                 comm_semiring_1_cancel_interval)
                A2_)
              (Bit0 (Bit0 (Bit0 One))))));

fun code_response_compatible family operation kind number committed =
  (if code_known_response_number (equal_nat, interval_nat) number
    then reference_response_compatible family operation kind number committed
    else code_response_call_shape (equal_nat, interval_nat) family
           operation andalso
           (equal_reference_response_kinda kind Recorded_Result orelse
             not committed));

fun response_extended_compatible allocations added_calls family operation kind
  number committed =
  (case map_of equal_nat allocations number
    of NONE =>
      code_response_compatible family operation kind number committed orelse
        not (code_response_call_shape (equal_nat, interval_nat) family
              operation) andalso
          (membera (equal_prod equal_wire_family equal_nat) added_calls
             (family, operation) andalso
            (not (is_none
                   (code_decode_response_status kind number committed)) andalso
              (not (code_known_response_number (equal_nat, interval_nat)
                     number) orelse
                (not (equal_reference_response_kinda kind
                       Recorded_Result) orelse
                  member equal_nat number
                    (insert equal_nat one_nata
                      (insert equal_nat (nat_of_integer (2 : IntInf.int))
                        (insert equal_nat (nat_of_integer (3 : IntInf.int))
                          bot_set)))))))
    | SOME (assigned_kind, (assigned_commit, targets)) =>
      equal_reference_response_kinda kind assigned_kind andalso
        (equal_bool committed assigned_commit andalso
          membera (equal_prod equal_wire_family equal_nat) targets
            (family, operation)));

fun response_extended_status allocations kind number committed =
  (case map_of equal_nat allocations number
    of NONE => code_decode_response_status kind number committed
    | SOME (assigned_kind, (assigned_commit, _)) =>
      (if equal_reference_response_kinda kind assigned_kind andalso
            equal_bool committed assigned_commit
        then SOME (Code_Known_Response (kind, number)) else NONE));

fun response_v061_status original kind number position =
  let
    val committed = not (is_none position);
  in
    (case response_extended_status sync_response_allocations kind number
            committed
      of NONE => NONE
      | SOME (Code_Known_Response (category, known)) =>
        (if response_extended_compatible sync_response_allocations
              [sync_response_operation] (wire_message_family original)
              (wire_opcode (wire_operation_body original)) kind number committed
          then SOME (Code_Known_Response (category, known)) else NONE)
      | SOME (Code_Unknown_Response (category, raw)) =>
        SOME (Code_Unknown_Response (category, raw)))
  end;

fun response_v061_check_enclosed check_status original decoded v061_caller kind
  number position =
  (case decoded
    of Response_V061_Legacy_Operand legacy =>
      (case code_check_nested_response original legacy v061_caller position
        of NONE =>
          (if check_status andalso
                sync_added_status (equal_nat, numeral_nat) number
            then SOME Invalid_Wire_Format else NONE)
        | SOME a => SOME a)
    | Response_V061_Sync_Operand request =>
      (if not (equal_proda equal_nat equal_nat v061_caller
                (sync_call request)) orelse
            check_status andalso
              is_none (response_v061_status original kind number position)
        then SOME Invalid_Wire_Format else NONE)
    | Response_V061_Receipt _ => SOME Invalid_Wire_Format
    | Response_V061_Current => SOME Invalid_Wire_Format);

fun sync_link_response_header outer enclosed caller =
  equal_nata (wire_version outer) (wire_version enclosed) andalso
    (equal_nata (wire_deployment outer) (wire_deployment enclosed) andalso
      (equal_nata (wire_principal enclosed) (fst caller) andalso
        (equal_nata (wire_source_domain outer)
           (wire_target_domain enclosed) andalso
          equal_nata (wire_target_domain outer)
            (wire_source_domain enclosed))));

fun response_v061_finish_parse check_status descend outer exact nested decoded =
  (case response_result_words (wire_words (wire_operation_body outer))
    of NONE => Inl Invalid_Wire_Format
    | SOME (v061_caller, (kind, (number, position))) =>
      (if not (equal_reference_response_kinda kind Recorded_Result) andalso
            not (is_none position) orelse
            check_status andalso
              (sync_added_status (equal_nat, numeral_nat) number andalso
                (not (equal_reference_response_kinda kind
                       Recorded_Result) orelse
                  not (equal_bool (not (is_none position))
                        (equal_nata number
                          (nat_of_integer (29 : IntInf.int))))))
        then Inl Invalid_Wire_Format
        else (if not (sync_link_response_header outer nested v061_caller)
               then Inl Invalid_Wire_Source
               else let
                      val v061_check =
                        (fn original => fn operand =>
                          response_v061_check_enclosed check_status original
                            operand v061_caller kind number position);
                    in
                      (case (case decoded
                              of Response_V061_Legacy_Operand _ =>
                                v061_check nested decoded
                              | Response_V061_Sync_Operand _ =>
                                v061_check nested decoded
                              | Response_V061_Receipt original =>
                                (if not (code_same_original nested original)
                                  then SOME Invalid_Wire_Source
                                  else (case descend original of Inl a => SOME a
 | Inr a => v061_check original a))
                              | Response_V061_Current =>
                                v061_check nested decoded)
                        of NONE =>
                          Inr (Response_fixed_decoded_ext
                                (v061_caller, kind, number, position, exact,
                                  nested, ()))
                        | SOME a => Inl a)
                    end)));

fun response_v061_parse_layer check_status descend outer =
  let
    val v061_body = wire_operation_body outer;
  in
    (if not (equal_proda equal_wire_family equal_nat (sync_operation outer)
              (Wire_Ack, nat_of_integer (2 : IntInf.int))) orelse
          not (equal_wire_deadline (wire_deadline v061_body) Deadline_Absent)
      then Inl Invalid_Wire_Format
      else (case wire_blobs v061_body of [] => Inl Invalid_Wire_Format
             | [exact] =>
               (case sync_decode_core exact of NONE => Inl Invalid_Wire_Format
                 | SOME nested =>
                   (case descend nested of Inl a => Inl a
                     | Inr a =>
                       response_v061_finish_parse check_status descend outer
                         exact nested a))
             | _ :: _ :: _ => Inl Invalid_Wire_Format))
  end;

fun response_fixed_caller_from_decoded (Code_Nested_Ordinary (native, command))
  = Inr (native_id native)
  | response_fixed_caller_from_decoded (Code_Nested_Legal call_id) = Inr call_id
  | response_fixed_caller_from_decoded (Code_Nested_Spend call_id) = Inr call_id
  | response_fixed_caller_from_decoded (Code_Nested_Receipt v) =
    Inl Invalid_Wire_Format
  | response_fixed_caller_from_decoded Code_Nested_Response =
    Inl Invalid_Wire_Format
  | response_fixed_caller_from_decoded Code_Nested_Other =
    Inl Invalid_Wire_Format;

fun response_v061_is_call operand =
  (case operand
    of Response_V061_Legacy_Operand decoded =>
      (case response_fixed_caller_from_decoded decoded of Inl _ => false
        | Inr _ => true)
    | Response_V061_Sync_Operand _ => true | Response_V061_Receipt _ => false
    | Response_V061_Current => false);

fun response_v061_operand fuel core =
  (if equal_nata fuel zero_nata then Inl Invalid_Wire_Format
    else let
           val v061_body = wire_operation_body core;
           val operation = sync_operation core;
         in
           (if equal_proda equal_wire_family equal_nat operation
                 (Wire_State_Sync, nat_of_integer (7 : IntInf.int))
             then (case sync_read_operands core
                    of NONE => Inl Invalid_Wire_Format
                    | SOME request => Inr (Response_V061_Sync_Operand request))
             else (if equal_proda equal_wire_family equal_nat operation
                        (Wire_Query, nat_of_integer (9 : IntInf.int))
                    then (case sync_read_query core
                           of NONE => Inl Invalid_Wire_Format
                           | SOME _ => Inr Response_V061_Current)
                    else (if equal_proda equal_wire_family equal_nat operation
                               (Wire_Query, nat_of_integer (8 : IntInf.int))
                           then (if not (equal_wire_deadline
  (wire_deadline v061_body) Deadline_Absent) orelse
                                      equal_nata (minus_nata fuel one_nata)
zero_nata
                                  then Inl Invalid_Wire_Format
                                  else (case
 (wire_words v061_body, wire_blobs v061_body)
 of ([], _) => Inl Invalid_Wire_Format | ([_], []) => Inl Invalid_Wire_Format
 | ([_], [exact]) =>
   (case sync_decode_core exact of NONE => Inl Invalid_Wire_Format
     | SOME nested =>
       (case response_v061_operand (minus_nata fuel one_nata) nested
         of Inl a => Inl a
         | Inr decoded =>
           (if response_v061_is_call decoded
             then Inr (Response_V061_Receipt nested)
             else Inl Invalid_Wire_Format)))
 | ([_], _ :: _ :: _) => Inl Invalid_Wire_Format
 | (_ :: _ :: _, _) => Inl Invalid_Wire_Format))
                           else (if equal_proda equal_wire_family equal_nat
                                      operation
                                      (Wire_Ack,
nat_of_integer (2 : IntInf.int))
                                  then (case
 response_v061_parse_layer true
   (response_v061_operand (minus_nata fuel one_nata)) core
 of Inl a => Inl a
 | Inr _ => Inr (Response_V061_Legacy_Operand Code_Nested_Response))
                                  else map_sum id Response_V061_Legacy_Operand
 (response_fixed_expected_decode core)))))
         end);

fun response_v061_caller (Response_V061_Sync_Operand request) =
  Inr (sync_call request)
  | response_v061_caller (Response_V061_Legacy_Operand decoded) =
    response_fixed_caller_from_decoded decoded
  | response_v061_caller (Response_V061_Receipt original) =
    Inl Invalid_Wire_Format
  | response_v061_caller Response_V061_Current = Inl Invalid_Wire_Format;

fun response_v061_parse check_status v061_depth core =
  (if equal_nata v061_depth zero_nata then Inl Invalid_Wire_Format
    else response_v061_parse_layer check_status
           (response_v061_operand (minus_nata v061_depth one_nata)) core);

fun response_v061_validate v061_depth expected packet =
  (case response_v061_parse false v061_depth (packet_core packet)
    of Inl a => Inl a
    | Inr view =>
      (case response_v061_operand one_nata expected of Inl a => Inl a
        | Inr decoded =>
          (if not (equal_lista equal_nat (response_decoded_original_bytes view)
                    (encode_wire_core expected))
            then Inl Conflicting_Wire_Replay
            else (case response_v061_caller decoded of Inl a => Inl a
                   | Inr original_id =>
                     (if not (equal_proda equal_nat equal_nat
                               (response_decoded_id view) original_id)
                       then Inl Conflicting_Wire_Replay
                       else (case response_v061_status expected
                                    (response_decoded_kind view)
                                    (response_decoded_number view)
                                    (response_decoded_position view)
                              of NONE => Inl Invalid_Wire_Format
                              | SOME status =>
                                Inr (response_v061_result_of_view view,
                                      SOME status)))))));

fun code_check_declared_version bytes max_frame =
  (if less_nat max_frame (size_list bytes) then SOME Invalid_Wire_Format
    else (case code_declared_version bytes of NONE => NONE
           | SOME version =>
             (if not (equal_nata version (nat_of_integer (6 : IntInf.int)))
               then SOME Unsupported_Wire_Version else NONE)));

fun boundary_max_frame
  (Wire_boundary_ext
    (boundary_profile, boundary_deployment, boundary_source, boundary_target,
      boundary_principal, boundary_key, boundary_epoch, boundary_route_scope,
      boundary_now, boundary_asset_ttl_floor, boundary_future_skew,
      boundary_max_frame, boundary_version_floor, boundary_critical_allowed,
      boundary_threshold_supported, more))
  = boundary_max_frame;

fun response_v061_admit curve_verify channel current expected bytes =
  let
    val scope = response_client_scope current;
  in
    (if not (equal_nata (response_channel_local channel)
              (boundary_target scope)) orelse
          (not (equal_nata (response_channel_remote channel)
                 (boundary_source scope)) orelse
            (not (equal_nata (response_channel_deployment channel)
                   (boundary_deployment scope)) orelse
              (less_nat (response_channel_expires channel)
                 (boundary_now scope) orelse
                not (equal_lista equal_nat (response_client_public_key current)
                      (response_channel_remote_key channel)))))
      then Inl Invalid_Wire_Source
      else (case code_check_declared_version bytes (boundary_max_frame scope)
             of NONE =>
               (case sync_decode_packet bytes of NONE => Inl Invalid_Wire_Format
                 | SOME packet =>
                   (case code_admit_packet
                           (fn _ =>
                             curve_verify (response_client_public_key current))
                           packet
                           (boundary_profile_update
                             (fn _ => response_channel_profile channel) scope)
                     of NONE =>
                       response_v061_validate
                         (response_client_max_nesting current)
                         (packet_core expected) packet
                     | SOME a => Inl a))
             | SOME a => Inl a))
  end;

fun response_v061_pack_rows rows =
  ((0 : IntInf.int), map (map integer_of_nat) rows);

fun response_v061_sync_result (Sync_Committed position) =
  (nat_of_integer (29 : IntInf.int), SOME position)
  | response_v061_sync_result (Sync_Uncommitted Sync_Busy) =
    (nat_of_integer (2 : IntInf.int), NONE)
  | response_v061_sync_result (Sync_Uncommitted Sync_Unavailable) =
    (nat_of_integer (3 : IntInf.int), NONE)
  | response_v061_sync_result (Sync_Uncommitted Sync_Mismatch) =
    (nat_of_integer (39 : IntInf.int), NONE)
  | response_v061_sync_result (Sync_Uncommitted Sync_Stale) =
    (nat_of_integer (40 : IntInf.int), NONE)
  | response_v061_sync_result (Sync_Uncommitted Sync_Proof_Rejected) =
    (nat_of_integer (41 : IntInf.int), NONE);

fun source_outcome_commit
  (Code_source_outcome_ext (source_outcome_reply, source_outcome_commit, more))
  = source_outcome_commit;

fun source_outcome_reply
  (Code_source_outcome_ext (source_outcome_reply, source_outcome_commit, more))
  = source_outcome_reply;

fun code_source_accepted_number Code_Source_Rejected_Reply = one_nata
  | code_source_accepted_number Code_Source_Busy_Reply =
    nat_of_integer (2 : IntInf.int)
  | code_source_accepted_number Code_Source_Reserved_Reply =
    nat_of_integer (10 : IntInf.int)
  | code_source_accepted_number Code_Source_Dispatched_Reply =
    nat_of_integer (11 : IntInf.int)
  | code_source_accepted_number Code_Source_Debited_Reply =
    nat_of_integer (12 : IntInf.int)
  | code_source_accepted_number Code_Source_Closed_Reply =
    nat_of_integer (13 : IntInf.int)
  | code_source_accepted_number Code_Source_Preempted_Reply =
    nat_of_integer (14 : IntInf.int)
  | code_source_accepted_number Code_Source_Time_Reply =
    nat_of_integer (15 : IntInf.int)
  | code_source_accepted_number Code_Source_Recorded_Reply =
    nat_of_integer (16 : IntInf.int)
  | code_source_accepted_number Code_Source_Credited_Reply =
    nat_of_integer (17 : IntInf.int)
  | code_source_accepted_number Code_Source_Reconciled_Reply =
    nat_of_integer (18 : IntInf.int)
  | code_source_accepted_number Code_Source_Refunded_Reply =
    nat_of_integer (19 : IntInf.int)
  | code_source_accepted_number Code_Source_Data_Reply =
    nat_of_integer (20 : IntInf.int)
  | code_source_accepted_number Code_Source_Evidence_Reply =
    nat_of_integer (21 : IntInf.int)
  | code_source_accepted_number Code_Source_Published_Reply =
    nat_of_integer (22 : IntInf.int);

fun code_source_ordinary_number (Code_Source_Accepted reply) =
  code_source_accepted_number reply
  | code_source_ordinary_number Code_Source_Duplicate_Decision =
    nat_of_integer (23 : IntInf.int)
  | code_source_ordinary_number Code_Source_Duplicate_Confirmed =
    nat_of_integer (24 : IntInf.int)
  | code_source_ordinary_number Code_Source_Duplicate_Reversed =
    nat_of_integer (25 : IntInf.int)
  | code_source_ordinary_number Code_Source_Outcome_Rejected = one_nata
  | code_source_ordinary_number Code_Source_Outcome_Busy =
    nat_of_integer (2 : IntInf.int)
  | code_source_ordinary_number Code_Source_Outcome_Unavailable =
    nat_of_integer (3 : IntInf.int);

fun code_source_ordinary_result observed =
  (code_source_ordinary_number (source_outcome_reply observed),
    source_outcome_commit observed);

fun code_source_from_resolution Code_Source_Resolution_Rejected =
  (nat_of_integer (4 : IntInf.int), NONE)
  | code_source_from_resolution
    (Code_Source_Resolution_Published
      (Code_Source_Ordinary_Receipt (Code_Source_Collected observed)))
    = code_source_ordinary_result observed
  | code_source_from_resolution
    (Code_Source_Resolution_Published
      (Code_Source_Ordinary_Receipt Code_Source_Collection_Waiting))
    = (nat_of_integer (50 : IntInf.int), NONE)
  | code_source_from_resolution
    (Code_Source_Resolution_Published
      (Code_Source_Ordinary_Receipt Code_Source_Collection_Rejected))
    = (nat_of_integer (50 : IntInf.int), NONE)
  | code_source_from_resolution
    (Code_Source_Resolution_Published (Code_Source_Legal_Receipt va)) =
    (nat_of_integer (50 : IntInf.int), NONE)
  | code_source_from_resolution
    (Code_Source_Resolution_Published (Code_Source_Spend_Receipt va)) =
    (nat_of_integer (50 : IntInf.int), NONE)
  | code_source_from_resolution Code_Source_Resolution_Unresolved =
    (nat_of_integer (50 : IntInf.int), NONE);

fun equal_code_source_accepted_reply Code_Source_Evidence_Reply
  Code_Source_Published_Reply = false
  | equal_code_source_accepted_reply Code_Source_Published_Reply
    Code_Source_Evidence_Reply = false
  | equal_code_source_accepted_reply Code_Source_Data_Reply
    Code_Source_Published_Reply = false
  | equal_code_source_accepted_reply Code_Source_Published_Reply
    Code_Source_Data_Reply = false
  | equal_code_source_accepted_reply Code_Source_Data_Reply
    Code_Source_Evidence_Reply = false
  | equal_code_source_accepted_reply Code_Source_Evidence_Reply
    Code_Source_Data_Reply = false
  | equal_code_source_accepted_reply Code_Source_Refunded_Reply
    Code_Source_Published_Reply = false
  | equal_code_source_accepted_reply Code_Source_Published_Reply
    Code_Source_Refunded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Refunded_Reply
    Code_Source_Evidence_Reply = false
  | equal_code_source_accepted_reply Code_Source_Evidence_Reply
    Code_Source_Refunded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Refunded_Reply
    Code_Source_Data_Reply = false
  | equal_code_source_accepted_reply Code_Source_Data_Reply
    Code_Source_Refunded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reconciled_Reply
    Code_Source_Published_Reply = false
  | equal_code_source_accepted_reply Code_Source_Published_Reply
    Code_Source_Reconciled_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reconciled_Reply
    Code_Source_Evidence_Reply = false
  | equal_code_source_accepted_reply Code_Source_Evidence_Reply
    Code_Source_Reconciled_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reconciled_Reply
    Code_Source_Data_Reply = false
  | equal_code_source_accepted_reply Code_Source_Data_Reply
    Code_Source_Reconciled_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reconciled_Reply
    Code_Source_Refunded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Refunded_Reply
    Code_Source_Reconciled_Reply = false
  | equal_code_source_accepted_reply Code_Source_Credited_Reply
    Code_Source_Published_Reply = false
  | equal_code_source_accepted_reply Code_Source_Published_Reply
    Code_Source_Credited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Credited_Reply
    Code_Source_Evidence_Reply = false
  | equal_code_source_accepted_reply Code_Source_Evidence_Reply
    Code_Source_Credited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Credited_Reply
    Code_Source_Data_Reply = false
  | equal_code_source_accepted_reply Code_Source_Data_Reply
    Code_Source_Credited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Credited_Reply
    Code_Source_Refunded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Refunded_Reply
    Code_Source_Credited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Credited_Reply
    Code_Source_Reconciled_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reconciled_Reply
    Code_Source_Credited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Recorded_Reply
    Code_Source_Published_Reply = false
  | equal_code_source_accepted_reply Code_Source_Published_Reply
    Code_Source_Recorded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Recorded_Reply
    Code_Source_Evidence_Reply = false
  | equal_code_source_accepted_reply Code_Source_Evidence_Reply
    Code_Source_Recorded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Recorded_Reply
    Code_Source_Data_Reply = false
  | equal_code_source_accepted_reply Code_Source_Data_Reply
    Code_Source_Recorded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Recorded_Reply
    Code_Source_Refunded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Refunded_Reply
    Code_Source_Recorded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Recorded_Reply
    Code_Source_Reconciled_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reconciled_Reply
    Code_Source_Recorded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Recorded_Reply
    Code_Source_Credited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Credited_Reply
    Code_Source_Recorded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Time_Reply
    Code_Source_Published_Reply = false
  | equal_code_source_accepted_reply Code_Source_Published_Reply
    Code_Source_Time_Reply = false
  | equal_code_source_accepted_reply Code_Source_Time_Reply
    Code_Source_Evidence_Reply = false
  | equal_code_source_accepted_reply Code_Source_Evidence_Reply
    Code_Source_Time_Reply = false
  | equal_code_source_accepted_reply Code_Source_Time_Reply
    Code_Source_Data_Reply = false
  | equal_code_source_accepted_reply Code_Source_Data_Reply
    Code_Source_Time_Reply = false
  | equal_code_source_accepted_reply Code_Source_Time_Reply
    Code_Source_Refunded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Refunded_Reply
    Code_Source_Time_Reply = false
  | equal_code_source_accepted_reply Code_Source_Time_Reply
    Code_Source_Reconciled_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reconciled_Reply
    Code_Source_Time_Reply = false
  | equal_code_source_accepted_reply Code_Source_Time_Reply
    Code_Source_Credited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Credited_Reply
    Code_Source_Time_Reply = false
  | equal_code_source_accepted_reply Code_Source_Time_Reply
    Code_Source_Recorded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Recorded_Reply
    Code_Source_Time_Reply = false
  | equal_code_source_accepted_reply Code_Source_Preempted_Reply
    Code_Source_Published_Reply = false
  | equal_code_source_accepted_reply Code_Source_Published_Reply
    Code_Source_Preempted_Reply = false
  | equal_code_source_accepted_reply Code_Source_Preempted_Reply
    Code_Source_Evidence_Reply = false
  | equal_code_source_accepted_reply Code_Source_Evidence_Reply
    Code_Source_Preempted_Reply = false
  | equal_code_source_accepted_reply Code_Source_Preempted_Reply
    Code_Source_Data_Reply = false
  | equal_code_source_accepted_reply Code_Source_Data_Reply
    Code_Source_Preempted_Reply = false
  | equal_code_source_accepted_reply Code_Source_Preempted_Reply
    Code_Source_Refunded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Refunded_Reply
    Code_Source_Preempted_Reply = false
  | equal_code_source_accepted_reply Code_Source_Preempted_Reply
    Code_Source_Reconciled_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reconciled_Reply
    Code_Source_Preempted_Reply = false
  | equal_code_source_accepted_reply Code_Source_Preempted_Reply
    Code_Source_Credited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Credited_Reply
    Code_Source_Preempted_Reply = false
  | equal_code_source_accepted_reply Code_Source_Preempted_Reply
    Code_Source_Recorded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Recorded_Reply
    Code_Source_Preempted_Reply = false
  | equal_code_source_accepted_reply Code_Source_Preempted_Reply
    Code_Source_Time_Reply = false
  | equal_code_source_accepted_reply Code_Source_Time_Reply
    Code_Source_Preempted_Reply = false
  | equal_code_source_accepted_reply Code_Source_Closed_Reply
    Code_Source_Published_Reply = false
  | equal_code_source_accepted_reply Code_Source_Published_Reply
    Code_Source_Closed_Reply = false
  | equal_code_source_accepted_reply Code_Source_Closed_Reply
    Code_Source_Evidence_Reply = false
  | equal_code_source_accepted_reply Code_Source_Evidence_Reply
    Code_Source_Closed_Reply = false
  | equal_code_source_accepted_reply Code_Source_Closed_Reply
    Code_Source_Data_Reply = false
  | equal_code_source_accepted_reply Code_Source_Data_Reply
    Code_Source_Closed_Reply = false
  | equal_code_source_accepted_reply Code_Source_Closed_Reply
    Code_Source_Refunded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Refunded_Reply
    Code_Source_Closed_Reply = false
  | equal_code_source_accepted_reply Code_Source_Closed_Reply
    Code_Source_Reconciled_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reconciled_Reply
    Code_Source_Closed_Reply = false
  | equal_code_source_accepted_reply Code_Source_Closed_Reply
    Code_Source_Credited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Credited_Reply
    Code_Source_Closed_Reply = false
  | equal_code_source_accepted_reply Code_Source_Closed_Reply
    Code_Source_Recorded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Recorded_Reply
    Code_Source_Closed_Reply = false
  | equal_code_source_accepted_reply Code_Source_Closed_Reply
    Code_Source_Time_Reply = false
  | equal_code_source_accepted_reply Code_Source_Time_Reply
    Code_Source_Closed_Reply = false
  | equal_code_source_accepted_reply Code_Source_Closed_Reply
    Code_Source_Preempted_Reply = false
  | equal_code_source_accepted_reply Code_Source_Preempted_Reply
    Code_Source_Closed_Reply = false
  | equal_code_source_accepted_reply Code_Source_Debited_Reply
    Code_Source_Published_Reply = false
  | equal_code_source_accepted_reply Code_Source_Published_Reply
    Code_Source_Debited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Debited_Reply
    Code_Source_Evidence_Reply = false
  | equal_code_source_accepted_reply Code_Source_Evidence_Reply
    Code_Source_Debited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Debited_Reply
    Code_Source_Data_Reply = false
  | equal_code_source_accepted_reply Code_Source_Data_Reply
    Code_Source_Debited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Debited_Reply
    Code_Source_Refunded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Refunded_Reply
    Code_Source_Debited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Debited_Reply
    Code_Source_Reconciled_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reconciled_Reply
    Code_Source_Debited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Debited_Reply
    Code_Source_Credited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Credited_Reply
    Code_Source_Debited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Debited_Reply
    Code_Source_Recorded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Recorded_Reply
    Code_Source_Debited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Debited_Reply
    Code_Source_Time_Reply = false
  | equal_code_source_accepted_reply Code_Source_Time_Reply
    Code_Source_Debited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Debited_Reply
    Code_Source_Preempted_Reply = false
  | equal_code_source_accepted_reply Code_Source_Preempted_Reply
    Code_Source_Debited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Debited_Reply
    Code_Source_Closed_Reply = false
  | equal_code_source_accepted_reply Code_Source_Closed_Reply
    Code_Source_Debited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Dispatched_Reply
    Code_Source_Published_Reply = false
  | equal_code_source_accepted_reply Code_Source_Published_Reply
    Code_Source_Dispatched_Reply = false
  | equal_code_source_accepted_reply Code_Source_Dispatched_Reply
    Code_Source_Evidence_Reply = false
  | equal_code_source_accepted_reply Code_Source_Evidence_Reply
    Code_Source_Dispatched_Reply = false
  | equal_code_source_accepted_reply Code_Source_Dispatched_Reply
    Code_Source_Data_Reply = false
  | equal_code_source_accepted_reply Code_Source_Data_Reply
    Code_Source_Dispatched_Reply = false
  | equal_code_source_accepted_reply Code_Source_Dispatched_Reply
    Code_Source_Refunded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Refunded_Reply
    Code_Source_Dispatched_Reply = false
  | equal_code_source_accepted_reply Code_Source_Dispatched_Reply
    Code_Source_Reconciled_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reconciled_Reply
    Code_Source_Dispatched_Reply = false
  | equal_code_source_accepted_reply Code_Source_Dispatched_Reply
    Code_Source_Credited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Credited_Reply
    Code_Source_Dispatched_Reply = false
  | equal_code_source_accepted_reply Code_Source_Dispatched_Reply
    Code_Source_Recorded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Recorded_Reply
    Code_Source_Dispatched_Reply = false
  | equal_code_source_accepted_reply Code_Source_Dispatched_Reply
    Code_Source_Time_Reply = false
  | equal_code_source_accepted_reply Code_Source_Time_Reply
    Code_Source_Dispatched_Reply = false
  | equal_code_source_accepted_reply Code_Source_Dispatched_Reply
    Code_Source_Preempted_Reply = false
  | equal_code_source_accepted_reply Code_Source_Preempted_Reply
    Code_Source_Dispatched_Reply = false
  | equal_code_source_accepted_reply Code_Source_Dispatched_Reply
    Code_Source_Closed_Reply = false
  | equal_code_source_accepted_reply Code_Source_Closed_Reply
    Code_Source_Dispatched_Reply = false
  | equal_code_source_accepted_reply Code_Source_Dispatched_Reply
    Code_Source_Debited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Debited_Reply
    Code_Source_Dispatched_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reserved_Reply
    Code_Source_Published_Reply = false
  | equal_code_source_accepted_reply Code_Source_Published_Reply
    Code_Source_Reserved_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reserved_Reply
    Code_Source_Evidence_Reply = false
  | equal_code_source_accepted_reply Code_Source_Evidence_Reply
    Code_Source_Reserved_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reserved_Reply
    Code_Source_Data_Reply = false
  | equal_code_source_accepted_reply Code_Source_Data_Reply
    Code_Source_Reserved_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reserved_Reply
    Code_Source_Refunded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Refunded_Reply
    Code_Source_Reserved_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reserved_Reply
    Code_Source_Reconciled_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reconciled_Reply
    Code_Source_Reserved_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reserved_Reply
    Code_Source_Credited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Credited_Reply
    Code_Source_Reserved_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reserved_Reply
    Code_Source_Recorded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Recorded_Reply
    Code_Source_Reserved_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reserved_Reply
    Code_Source_Time_Reply = false
  | equal_code_source_accepted_reply Code_Source_Time_Reply
    Code_Source_Reserved_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reserved_Reply
    Code_Source_Preempted_Reply = false
  | equal_code_source_accepted_reply Code_Source_Preempted_Reply
    Code_Source_Reserved_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reserved_Reply
    Code_Source_Closed_Reply = false
  | equal_code_source_accepted_reply Code_Source_Closed_Reply
    Code_Source_Reserved_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reserved_Reply
    Code_Source_Debited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Debited_Reply
    Code_Source_Reserved_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reserved_Reply
    Code_Source_Dispatched_Reply = false
  | equal_code_source_accepted_reply Code_Source_Dispatched_Reply
    Code_Source_Reserved_Reply = false
  | equal_code_source_accepted_reply Code_Source_Busy_Reply
    Code_Source_Published_Reply = false
  | equal_code_source_accepted_reply Code_Source_Published_Reply
    Code_Source_Busy_Reply = false
  | equal_code_source_accepted_reply Code_Source_Busy_Reply
    Code_Source_Evidence_Reply = false
  | equal_code_source_accepted_reply Code_Source_Evidence_Reply
    Code_Source_Busy_Reply = false
  | equal_code_source_accepted_reply Code_Source_Busy_Reply
    Code_Source_Data_Reply = false
  | equal_code_source_accepted_reply Code_Source_Data_Reply
    Code_Source_Busy_Reply = false
  | equal_code_source_accepted_reply Code_Source_Busy_Reply
    Code_Source_Refunded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Refunded_Reply
    Code_Source_Busy_Reply = false
  | equal_code_source_accepted_reply Code_Source_Busy_Reply
    Code_Source_Reconciled_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reconciled_Reply
    Code_Source_Busy_Reply = false
  | equal_code_source_accepted_reply Code_Source_Busy_Reply
    Code_Source_Credited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Credited_Reply
    Code_Source_Busy_Reply = false
  | equal_code_source_accepted_reply Code_Source_Busy_Reply
    Code_Source_Recorded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Recorded_Reply
    Code_Source_Busy_Reply = false
  | equal_code_source_accepted_reply Code_Source_Busy_Reply
    Code_Source_Time_Reply = false
  | equal_code_source_accepted_reply Code_Source_Time_Reply
    Code_Source_Busy_Reply = false
  | equal_code_source_accepted_reply Code_Source_Busy_Reply
    Code_Source_Preempted_Reply = false
  | equal_code_source_accepted_reply Code_Source_Preempted_Reply
    Code_Source_Busy_Reply = false
  | equal_code_source_accepted_reply Code_Source_Busy_Reply
    Code_Source_Closed_Reply = false
  | equal_code_source_accepted_reply Code_Source_Closed_Reply
    Code_Source_Busy_Reply = false
  | equal_code_source_accepted_reply Code_Source_Busy_Reply
    Code_Source_Debited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Debited_Reply
    Code_Source_Busy_Reply = false
  | equal_code_source_accepted_reply Code_Source_Busy_Reply
    Code_Source_Dispatched_Reply = false
  | equal_code_source_accepted_reply Code_Source_Dispatched_Reply
    Code_Source_Busy_Reply = false
  | equal_code_source_accepted_reply Code_Source_Busy_Reply
    Code_Source_Reserved_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reserved_Reply
    Code_Source_Busy_Reply = false
  | equal_code_source_accepted_reply Code_Source_Rejected_Reply
    Code_Source_Published_Reply = false
  | equal_code_source_accepted_reply Code_Source_Published_Reply
    Code_Source_Rejected_Reply = false
  | equal_code_source_accepted_reply Code_Source_Rejected_Reply
    Code_Source_Evidence_Reply = false
  | equal_code_source_accepted_reply Code_Source_Evidence_Reply
    Code_Source_Rejected_Reply = false
  | equal_code_source_accepted_reply Code_Source_Rejected_Reply
    Code_Source_Data_Reply = false
  | equal_code_source_accepted_reply Code_Source_Data_Reply
    Code_Source_Rejected_Reply = false
  | equal_code_source_accepted_reply Code_Source_Rejected_Reply
    Code_Source_Refunded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Refunded_Reply
    Code_Source_Rejected_Reply = false
  | equal_code_source_accepted_reply Code_Source_Rejected_Reply
    Code_Source_Reconciled_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reconciled_Reply
    Code_Source_Rejected_Reply = false
  | equal_code_source_accepted_reply Code_Source_Rejected_Reply
    Code_Source_Credited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Credited_Reply
    Code_Source_Rejected_Reply = false
  | equal_code_source_accepted_reply Code_Source_Rejected_Reply
    Code_Source_Recorded_Reply = false
  | equal_code_source_accepted_reply Code_Source_Recorded_Reply
    Code_Source_Rejected_Reply = false
  | equal_code_source_accepted_reply Code_Source_Rejected_Reply
    Code_Source_Time_Reply = false
  | equal_code_source_accepted_reply Code_Source_Time_Reply
    Code_Source_Rejected_Reply = false
  | equal_code_source_accepted_reply Code_Source_Rejected_Reply
    Code_Source_Preempted_Reply = false
  | equal_code_source_accepted_reply Code_Source_Preempted_Reply
    Code_Source_Rejected_Reply = false
  | equal_code_source_accepted_reply Code_Source_Rejected_Reply
    Code_Source_Closed_Reply = false
  | equal_code_source_accepted_reply Code_Source_Closed_Reply
    Code_Source_Rejected_Reply = false
  | equal_code_source_accepted_reply Code_Source_Rejected_Reply
    Code_Source_Debited_Reply = false
  | equal_code_source_accepted_reply Code_Source_Debited_Reply
    Code_Source_Rejected_Reply = false
  | equal_code_source_accepted_reply Code_Source_Rejected_Reply
    Code_Source_Dispatched_Reply = false
  | equal_code_source_accepted_reply Code_Source_Dispatched_Reply
    Code_Source_Rejected_Reply = false
  | equal_code_source_accepted_reply Code_Source_Rejected_Reply
    Code_Source_Reserved_Reply = false
  | equal_code_source_accepted_reply Code_Source_Reserved_Reply
    Code_Source_Rejected_Reply = false
  | equal_code_source_accepted_reply Code_Source_Rejected_Reply
    Code_Source_Busy_Reply = false
  | equal_code_source_accepted_reply Code_Source_Busy_Reply
    Code_Source_Rejected_Reply = false
  | equal_code_source_accepted_reply Code_Source_Published_Reply
    Code_Source_Published_Reply = true
  | equal_code_source_accepted_reply Code_Source_Evidence_Reply
    Code_Source_Evidence_Reply = true
  | equal_code_source_accepted_reply Code_Source_Data_Reply
    Code_Source_Data_Reply = true
  | equal_code_source_accepted_reply Code_Source_Refunded_Reply
    Code_Source_Refunded_Reply = true
  | equal_code_source_accepted_reply Code_Source_Reconciled_Reply
    Code_Source_Reconciled_Reply = true
  | equal_code_source_accepted_reply Code_Source_Credited_Reply
    Code_Source_Credited_Reply = true
  | equal_code_source_accepted_reply Code_Source_Recorded_Reply
    Code_Source_Recorded_Reply = true
  | equal_code_source_accepted_reply Code_Source_Time_Reply
    Code_Source_Time_Reply = true
  | equal_code_source_accepted_reply Code_Source_Preempted_Reply
    Code_Source_Preempted_Reply = true
  | equal_code_source_accepted_reply Code_Source_Closed_Reply
    Code_Source_Closed_Reply = true
  | equal_code_source_accepted_reply Code_Source_Debited_Reply
    Code_Source_Debited_Reply = true
  | equal_code_source_accepted_reply Code_Source_Dispatched_Reply
    Code_Source_Dispatched_Reply = true
  | equal_code_source_accepted_reply Code_Source_Reserved_Reply
    Code_Source_Reserved_Reply = true
  | equal_code_source_accepted_reply Code_Source_Busy_Reply
    Code_Source_Busy_Reply = true
  | equal_code_source_accepted_reply Code_Source_Rejected_Reply
    Code_Source_Rejected_Reply = true;

fun equal_code_source_outcome_reply Code_Source_Outcome_Busy
  Code_Source_Outcome_Unavailable = false
  | equal_code_source_outcome_reply Code_Source_Outcome_Unavailable
    Code_Source_Outcome_Busy = false
  | equal_code_source_outcome_reply Code_Source_Outcome_Rejected
    Code_Source_Outcome_Unavailable = false
  | equal_code_source_outcome_reply Code_Source_Outcome_Unavailable
    Code_Source_Outcome_Rejected = false
  | equal_code_source_outcome_reply Code_Source_Outcome_Rejected
    Code_Source_Outcome_Busy = false
  | equal_code_source_outcome_reply Code_Source_Outcome_Busy
    Code_Source_Outcome_Rejected = false
  | equal_code_source_outcome_reply Code_Source_Duplicate_Reversed
    Code_Source_Outcome_Unavailable = false
  | equal_code_source_outcome_reply Code_Source_Outcome_Unavailable
    Code_Source_Duplicate_Reversed = false
  | equal_code_source_outcome_reply Code_Source_Duplicate_Reversed
    Code_Source_Outcome_Busy = false
  | equal_code_source_outcome_reply Code_Source_Outcome_Busy
    Code_Source_Duplicate_Reversed = false
  | equal_code_source_outcome_reply Code_Source_Duplicate_Reversed
    Code_Source_Outcome_Rejected = false
  | equal_code_source_outcome_reply Code_Source_Outcome_Rejected
    Code_Source_Duplicate_Reversed = false
  | equal_code_source_outcome_reply Code_Source_Duplicate_Confirmed
    Code_Source_Outcome_Unavailable = false
  | equal_code_source_outcome_reply Code_Source_Outcome_Unavailable
    Code_Source_Duplicate_Confirmed = false
  | equal_code_source_outcome_reply Code_Source_Duplicate_Confirmed
    Code_Source_Outcome_Busy = false
  | equal_code_source_outcome_reply Code_Source_Outcome_Busy
    Code_Source_Duplicate_Confirmed = false
  | equal_code_source_outcome_reply Code_Source_Duplicate_Confirmed
    Code_Source_Outcome_Rejected = false
  | equal_code_source_outcome_reply Code_Source_Outcome_Rejected
    Code_Source_Duplicate_Confirmed = false
  | equal_code_source_outcome_reply Code_Source_Duplicate_Confirmed
    Code_Source_Duplicate_Reversed = false
  | equal_code_source_outcome_reply Code_Source_Duplicate_Reversed
    Code_Source_Duplicate_Confirmed = false
  | equal_code_source_outcome_reply Code_Source_Duplicate_Decision
    Code_Source_Outcome_Unavailable = false
  | equal_code_source_outcome_reply Code_Source_Outcome_Unavailable
    Code_Source_Duplicate_Decision = false
  | equal_code_source_outcome_reply Code_Source_Duplicate_Decision
    Code_Source_Outcome_Busy = false
  | equal_code_source_outcome_reply Code_Source_Outcome_Busy
    Code_Source_Duplicate_Decision = false
  | equal_code_source_outcome_reply Code_Source_Duplicate_Decision
    Code_Source_Outcome_Rejected = false
  | equal_code_source_outcome_reply Code_Source_Outcome_Rejected
    Code_Source_Duplicate_Decision = false
  | equal_code_source_outcome_reply Code_Source_Duplicate_Decision
    Code_Source_Duplicate_Reversed = false
  | equal_code_source_outcome_reply Code_Source_Duplicate_Reversed
    Code_Source_Duplicate_Decision = false
  | equal_code_source_outcome_reply Code_Source_Duplicate_Decision
    Code_Source_Duplicate_Confirmed = false
  | equal_code_source_outcome_reply Code_Source_Duplicate_Confirmed
    Code_Source_Duplicate_Decision = false
  | equal_code_source_outcome_reply (Code_Source_Accepted x1)
    Code_Source_Outcome_Unavailable = false
  | equal_code_source_outcome_reply Code_Source_Outcome_Unavailable
    (Code_Source_Accepted x1) = false
  | equal_code_source_outcome_reply (Code_Source_Accepted x1)
    Code_Source_Outcome_Busy = false
  | equal_code_source_outcome_reply Code_Source_Outcome_Busy
    (Code_Source_Accepted x1) = false
  | equal_code_source_outcome_reply (Code_Source_Accepted x1)
    Code_Source_Outcome_Rejected = false
  | equal_code_source_outcome_reply Code_Source_Outcome_Rejected
    (Code_Source_Accepted x1) = false
  | equal_code_source_outcome_reply (Code_Source_Accepted x1)
    Code_Source_Duplicate_Reversed = false
  | equal_code_source_outcome_reply Code_Source_Duplicate_Reversed
    (Code_Source_Accepted x1) = false
  | equal_code_source_outcome_reply (Code_Source_Accepted x1)
    Code_Source_Duplicate_Confirmed = false
  | equal_code_source_outcome_reply Code_Source_Duplicate_Confirmed
    (Code_Source_Accepted x1) = false
  | equal_code_source_outcome_reply (Code_Source_Accepted x1)
    Code_Source_Duplicate_Decision = false
  | equal_code_source_outcome_reply Code_Source_Duplicate_Decision
    (Code_Source_Accepted x1) = false
  | equal_code_source_outcome_reply (Code_Source_Accepted x1)
    (Code_Source_Accepted y1) = equal_code_source_accepted_reply x1 y1
  | equal_code_source_outcome_reply Code_Source_Outcome_Unavailable
    Code_Source_Outcome_Unavailable = true
  | equal_code_source_outcome_reply Code_Source_Outcome_Busy
    Code_Source_Outcome_Busy = true
  | equal_code_source_outcome_reply Code_Source_Outcome_Rejected
    Code_Source_Outcome_Rejected = true
  | equal_code_source_outcome_reply Code_Source_Duplicate_Reversed
    Code_Source_Duplicate_Reversed = true
  | equal_code_source_outcome_reply Code_Source_Duplicate_Confirmed
    Code_Source_Duplicate_Confirmed = true
  | equal_code_source_outcome_reply Code_Source_Duplicate_Decision
    Code_Source_Duplicate_Decision = true;

fun equal_code_source_outcome_ext A_
  (Code_source_outcome_ext
    (source_outcome_replya, source_outcome_commita, morea))
  (Code_source_outcome_ext (source_outcome_reply, source_outcome_commit, more))
  = equal_code_source_outcome_reply source_outcome_replya
      source_outcome_reply andalso
      (equal_optiona equal_nat source_outcome_commita
         source_outcome_commit andalso
        eq A_ morea more);

fun equal_code_source_spend_reply Code_Source_Spend_Busy
  Code_Source_Spend_Unavailable = false
  | equal_code_source_spend_reply Code_Source_Spend_Unavailable
    Code_Source_Spend_Busy = false
  | equal_code_source_spend_reply Code_Source_Spend_Rejected
    Code_Source_Spend_Unavailable = false
  | equal_code_source_spend_reply Code_Source_Spend_Unavailable
    Code_Source_Spend_Rejected = false
  | equal_code_source_spend_reply Code_Source_Spend_Rejected
    Code_Source_Spend_Busy = false
  | equal_code_source_spend_reply Code_Source_Spend_Busy
    Code_Source_Spend_Rejected = false
  | equal_code_source_spend_reply (Code_Source_Spend_Executed x1)
    Code_Source_Spend_Unavailable = false
  | equal_code_source_spend_reply Code_Source_Spend_Unavailable
    (Code_Source_Spend_Executed x1) = false
  | equal_code_source_spend_reply (Code_Source_Spend_Executed x1)
    Code_Source_Spend_Busy = false
  | equal_code_source_spend_reply Code_Source_Spend_Busy
    (Code_Source_Spend_Executed x1) = false
  | equal_code_source_spend_reply (Code_Source_Spend_Executed x1)
    Code_Source_Spend_Rejected = false
  | equal_code_source_spend_reply Code_Source_Spend_Rejected
    (Code_Source_Spend_Executed x1) = false
  | equal_code_source_spend_reply (Code_Source_Spend_Executed x1)
    (Code_Source_Spend_Executed y1) = equal_nata x1 y1
  | equal_code_source_spend_reply Code_Source_Spend_Unavailable
    Code_Source_Spend_Unavailable = true
  | equal_code_source_spend_reply Code_Source_Spend_Busy Code_Source_Spend_Busy
    = true
  | equal_code_source_spend_reply Code_Source_Spend_Rejected
    Code_Source_Spend_Rejected = true;

fun equal_legal_refusal Conflicting_Legal_Order Invalid_Legal_Binding = false
  | equal_legal_refusal Invalid_Legal_Binding Conflicting_Legal_Order = false
  | equal_legal_refusal Missing_Confiscation_Destination Invalid_Legal_Binding =
    false
  | equal_legal_refusal Invalid_Legal_Binding Missing_Confiscation_Destination =
    false
  | equal_legal_refusal Missing_Confiscation_Destination Conflicting_Legal_Order
    = false
  | equal_legal_refusal Conflicting_Legal_Order Missing_Confiscation_Destination
    = false
  | equal_legal_refusal Appeal_Still_Open Invalid_Legal_Binding = false
  | equal_legal_refusal Invalid_Legal_Binding Appeal_Still_Open = false
  | equal_legal_refusal Appeal_Still_Open Conflicting_Legal_Order = false
  | equal_legal_refusal Conflicting_Legal_Order Appeal_Still_Open = false
  | equal_legal_refusal Appeal_Still_Open Missing_Confiscation_Destination =
    false
  | equal_legal_refusal Missing_Confiscation_Destination Appeal_Still_Open =
    false
  | equal_legal_refusal Appeal_Deadline_Mismatch Invalid_Legal_Binding = false
  | equal_legal_refusal Invalid_Legal_Binding Appeal_Deadline_Mismatch = false
  | equal_legal_refusal Appeal_Deadline_Mismatch Conflicting_Legal_Order = false
  | equal_legal_refusal Conflicting_Legal_Order Appeal_Deadline_Mismatch = false
  | equal_legal_refusal Appeal_Deadline_Mismatch
    Missing_Confiscation_Destination = false
  | equal_legal_refusal Missing_Confiscation_Destination
    Appeal_Deadline_Mismatch = false
  | equal_legal_refusal Appeal_Deadline_Mismatch Appeal_Still_Open = false
  | equal_legal_refusal Appeal_Still_Open Appeal_Deadline_Mismatch = false
  | equal_legal_refusal Missing_Prior_Seizure Invalid_Legal_Binding = false
  | equal_legal_refusal Invalid_Legal_Binding Missing_Prior_Seizure = false
  | equal_legal_refusal Missing_Prior_Seizure Conflicting_Legal_Order = false
  | equal_legal_refusal Conflicting_Legal_Order Missing_Prior_Seizure = false
  | equal_legal_refusal Missing_Prior_Seizure Missing_Confiscation_Destination =
    false
  | equal_legal_refusal Missing_Confiscation_Destination Missing_Prior_Seizure =
    false
  | equal_legal_refusal Missing_Prior_Seizure Appeal_Still_Open = false
  | equal_legal_refusal Appeal_Still_Open Missing_Prior_Seizure = false
  | equal_legal_refusal Missing_Prior_Seizure Appeal_Deadline_Mismatch = false
  | equal_legal_refusal Appeal_Deadline_Mismatch Missing_Prior_Seizure = false
  | equal_legal_refusal Missing_Prior_Freeze Invalid_Legal_Binding = false
  | equal_legal_refusal Invalid_Legal_Binding Missing_Prior_Freeze = false
  | equal_legal_refusal Missing_Prior_Freeze Conflicting_Legal_Order = false
  | equal_legal_refusal Conflicting_Legal_Order Missing_Prior_Freeze = false
  | equal_legal_refusal Missing_Prior_Freeze Missing_Confiscation_Destination =
    false
  | equal_legal_refusal Missing_Confiscation_Destination Missing_Prior_Freeze =
    false
  | equal_legal_refusal Missing_Prior_Freeze Appeal_Still_Open = false
  | equal_legal_refusal Appeal_Still_Open Missing_Prior_Freeze = false
  | equal_legal_refusal Missing_Prior_Freeze Appeal_Deadline_Mismatch = false
  | equal_legal_refusal Appeal_Deadline_Mismatch Missing_Prior_Freeze = false
  | equal_legal_refusal Missing_Prior_Freeze Missing_Prior_Seizure = false
  | equal_legal_refusal Missing_Prior_Seizure Missing_Prior_Freeze = false
  | equal_legal_refusal Invalid_Legal_State Invalid_Legal_Binding = false
  | equal_legal_refusal Invalid_Legal_Binding Invalid_Legal_State = false
  | equal_legal_refusal Invalid_Legal_State Conflicting_Legal_Order = false
  | equal_legal_refusal Conflicting_Legal_Order Invalid_Legal_State = false
  | equal_legal_refusal Invalid_Legal_State Missing_Confiscation_Destination =
    false
  | equal_legal_refusal Missing_Confiscation_Destination Invalid_Legal_State =
    false
  | equal_legal_refusal Invalid_Legal_State Appeal_Still_Open = false
  | equal_legal_refusal Appeal_Still_Open Invalid_Legal_State = false
  | equal_legal_refusal Invalid_Legal_State Appeal_Deadline_Mismatch = false
  | equal_legal_refusal Appeal_Deadline_Mismatch Invalid_Legal_State = false
  | equal_legal_refusal Invalid_Legal_State Missing_Prior_Seizure = false
  | equal_legal_refusal Missing_Prior_Seizure Invalid_Legal_State = false
  | equal_legal_refusal Invalid_Legal_State Missing_Prior_Freeze = false
  | equal_legal_refusal Missing_Prior_Freeze Invalid_Legal_State = false
  | equal_legal_refusal Invalid_Legal_Authority Invalid_Legal_Binding = false
  | equal_legal_refusal Invalid_Legal_Binding Invalid_Legal_Authority = false
  | equal_legal_refusal Invalid_Legal_Authority Conflicting_Legal_Order = false
  | equal_legal_refusal Conflicting_Legal_Order Invalid_Legal_Authority = false
  | equal_legal_refusal Invalid_Legal_Authority Missing_Confiscation_Destination
    = false
  | equal_legal_refusal Missing_Confiscation_Destination Invalid_Legal_Authority
    = false
  | equal_legal_refusal Invalid_Legal_Authority Appeal_Still_Open = false
  | equal_legal_refusal Appeal_Still_Open Invalid_Legal_Authority = false
  | equal_legal_refusal Invalid_Legal_Authority Appeal_Deadline_Mismatch = false
  | equal_legal_refusal Appeal_Deadline_Mismatch Invalid_Legal_Authority = false
  | equal_legal_refusal Invalid_Legal_Authority Missing_Prior_Seizure = false
  | equal_legal_refusal Missing_Prior_Seizure Invalid_Legal_Authority = false
  | equal_legal_refusal Invalid_Legal_Authority Missing_Prior_Freeze = false
  | equal_legal_refusal Missing_Prior_Freeze Invalid_Legal_Authority = false
  | equal_legal_refusal Invalid_Legal_Authority Invalid_Legal_State = false
  | equal_legal_refusal Invalid_Legal_State Invalid_Legal_Authority = false
  | equal_legal_refusal Invalid_Legal_Binding Invalid_Legal_Binding = true
  | equal_legal_refusal Conflicting_Legal_Order Conflicting_Legal_Order = true
  | equal_legal_refusal Missing_Confiscation_Destination
    Missing_Confiscation_Destination = true
  | equal_legal_refusal Appeal_Still_Open Appeal_Still_Open = true
  | equal_legal_refusal Appeal_Deadline_Mismatch Appeal_Deadline_Mismatch = true
  | equal_legal_refusal Missing_Prior_Seizure Missing_Prior_Seizure = true
  | equal_legal_refusal Missing_Prior_Freeze Missing_Prior_Freeze = true
  | equal_legal_refusal Invalid_Legal_State Invalid_Legal_State = true
  | equal_legal_refusal Invalid_Legal_Authority Invalid_Legal_Authority = true;

fun equal_code_source_legal_reply Code_Source_Legal_Busy
  Code_Source_Legal_Unavailable = false
  | equal_code_source_legal_reply Code_Source_Legal_Unavailable
    Code_Source_Legal_Busy = false
  | equal_code_source_legal_reply (Code_Source_Legal_Blocked x3)
    Code_Source_Legal_Unavailable = false
  | equal_code_source_legal_reply Code_Source_Legal_Unavailable
    (Code_Source_Legal_Blocked x3) = false
  | equal_code_source_legal_reply (Code_Source_Legal_Blocked x3)
    Code_Source_Legal_Busy = false
  | equal_code_source_legal_reply Code_Source_Legal_Busy
    (Code_Source_Legal_Blocked x3) = false
  | equal_code_source_legal_reply (Code_Source_Legal_Applied x2)
    Code_Source_Legal_Unavailable = false
  | equal_code_source_legal_reply Code_Source_Legal_Unavailable
    (Code_Source_Legal_Applied x2) = false
  | equal_code_source_legal_reply (Code_Source_Legal_Applied x2)
    Code_Source_Legal_Busy = false
  | equal_code_source_legal_reply Code_Source_Legal_Busy
    (Code_Source_Legal_Applied x2) = false
  | equal_code_source_legal_reply (Code_Source_Legal_Applied x2)
    (Code_Source_Legal_Blocked x3) = false
  | equal_code_source_legal_reply (Code_Source_Legal_Blocked x3)
    (Code_Source_Legal_Applied x2) = false
  | equal_code_source_legal_reply (Code_Source_Legal_Emitted x1)
    Code_Source_Legal_Unavailable = false
  | equal_code_source_legal_reply Code_Source_Legal_Unavailable
    (Code_Source_Legal_Emitted x1) = false
  | equal_code_source_legal_reply (Code_Source_Legal_Emitted x1)
    Code_Source_Legal_Busy = false
  | equal_code_source_legal_reply Code_Source_Legal_Busy
    (Code_Source_Legal_Emitted x1) = false
  | equal_code_source_legal_reply (Code_Source_Legal_Emitted x1)
    (Code_Source_Legal_Blocked x3) = false
  | equal_code_source_legal_reply (Code_Source_Legal_Blocked x3)
    (Code_Source_Legal_Emitted x1) = false
  | equal_code_source_legal_reply (Code_Source_Legal_Emitted x1)
    (Code_Source_Legal_Applied x2) = false
  | equal_code_source_legal_reply (Code_Source_Legal_Applied x2)
    (Code_Source_Legal_Emitted x1) = false
  | equal_code_source_legal_reply (Code_Source_Legal_Blocked x3)
    (Code_Source_Legal_Blocked y3) = equal_legal_refusal x3 y3
  | equal_code_source_legal_reply (Code_Source_Legal_Applied x2)
    (Code_Source_Legal_Applied y2) = equal_nata x2 y2
  | equal_code_source_legal_reply (Code_Source_Legal_Emitted x1)
    (Code_Source_Legal_Emitted y1) = equal_nata x1 y1
  | equal_code_source_legal_reply Code_Source_Legal_Unavailable
    Code_Source_Legal_Unavailable = true
  | equal_code_source_legal_reply Code_Source_Legal_Busy Code_Source_Legal_Busy
    = true;

fun code_source_without_matching_receipt Code_Source_Ordinary_Busy =
  (nat_of_integer (55 : IntInf.int), NONE)
  | code_source_without_matching_receipt Code_Source_Ordinary_Unavailable =
    (nat_of_integer (56 : IntInf.int), NONE)
  | code_source_without_matching_receipt
    (Code_Source_Legal_Action Code_Source_Legal_Busy) =
    (nat_of_integer (55 : IntInf.int), NONE)
  | code_source_without_matching_receipt
    (Code_Source_Legal_Action Code_Source_Legal_Unavailable) =
    (nat_of_integer (56 : IntInf.int), NONE)
  | code_source_without_matching_receipt
    (Code_Source_Spend_Action Code_Source_Spend_Busy) =
    (nat_of_integer (55 : IntInf.int), NONE)
  | code_source_without_matching_receipt
    (Code_Source_Spend_Action Code_Source_Spend_Unavailable) =
    (nat_of_integer (56 : IntInf.int), NONE)
  | code_source_without_matching_receipt
    (Code_Source_Legal_Action (Code_Source_Legal_Emitted position)) =
    (nat_of_integer (50 : IntInf.int), NONE)
  | code_source_without_matching_receipt
    (Code_Source_Legal_Action (Code_Source_Legal_Applied position)) =
    (nat_of_integer (50 : IntInf.int), NONE)
  | code_source_without_matching_receipt
    (Code_Source_Spend_Action (Code_Source_Spend_Executed position)) =
    (nat_of_integer (50 : IntInf.int), NONE)
  | code_source_without_matching_receipt
    (Code_Source_Ordinary_Collected observed) =
    (nat_of_integer (50 : IntInf.int), NONE)
  | code_source_without_matching_receipt Code_Source_Ordinary_Waiting =
    (nat_of_integer (50 : IntInf.int), NONE)
  | code_source_without_matching_receipt Code_Source_Ordinary_Rejected =
    (nat_of_integer (77 : IntInf.int), NONE)
  | code_source_without_matching_receipt
    (Code_Source_Legal_Action (Code_Source_Legal_Blocked va)) =
    (nat_of_integer (77 : IntInf.int), NONE)
  | code_source_without_matching_receipt
    (Code_Source_Spend_Action Code_Source_Spend_Rejected) =
    (nat_of_integer (77 : IntInf.int), NONE)
  | code_source_without_matching_receipt Code_Source_Other_Action =
    (nat_of_integer (77 : IntInf.int), NONE);

fun code_source_spend_result (Code_Source_Spend_Executed position) =
  (nat_of_integer (28 : IntInf.int), SOME position)
  | code_source_spend_result Code_Source_Spend_Rejected = (one_nata, NONE)
  | code_source_spend_result Code_Source_Spend_Busy =
    (nat_of_integer (2 : IntInf.int), NONE)
  | code_source_spend_result Code_Source_Spend_Unavailable =
    (nat_of_integer (3 : IntInf.int), NONE);

fun code_source_legal_refusal_number Invalid_Legal_Authority =
  nat_of_integer (30 : IntInf.int)
  | code_source_legal_refusal_number Invalid_Legal_State =
    nat_of_integer (31 : IntInf.int)
  | code_source_legal_refusal_number Invalid_Legal_Binding =
    nat_of_integer (32 : IntInf.int)
  | code_source_legal_refusal_number Missing_Prior_Freeze =
    nat_of_integer (33 : IntInf.int)
  | code_source_legal_refusal_number Missing_Prior_Seizure =
    nat_of_integer (34 : IntInf.int)
  | code_source_legal_refusal_number Appeal_Still_Open =
    nat_of_integer (35 : IntInf.int)
  | code_source_legal_refusal_number Appeal_Deadline_Mismatch =
    nat_of_integer (36 : IntInf.int)
  | code_source_legal_refusal_number Missing_Confiscation_Destination =
    nat_of_integer (37 : IntInf.int)
  | code_source_legal_refusal_number Conflicting_Legal_Order =
    nat_of_integer (38 : IntInf.int);

fun code_source_legal_result (Code_Source_Legal_Emitted position) =
  (nat_of_integer (26 : IntInf.int), SOME position)
  | code_source_legal_result (Code_Source_Legal_Applied position) =
    (nat_of_integer (27 : IntInf.int), SOME position)
  | code_source_legal_result (Code_Source_Legal_Blocked reason) =
    (code_source_legal_refusal_number reason, NONE)
  | code_source_legal_result Code_Source_Legal_Busy =
    (nat_of_integer (2 : IntInf.int), NONE)
  | code_source_legal_result Code_Source_Legal_Unavailable =
    (nat_of_integer (3 : IntInf.int), NONE);

fun code_source_from_received (Code_Source_Ordinary_Collected reply)
  (SOME (Code_Source_Ordinary_Receipt (Code_Source_Collected stored))) =
  (if equal_code_source_outcome_ext equal_unit reply stored
    then code_source_ordinary_result stored
    else code_source_without_matching_receipt
           (Code_Source_Ordinary_Collected reply))
  | code_source_from_received (Code_Source_Legal_Action reply)
    (SOME (Code_Source_Legal_Receipt stored)) =
    (if equal_code_source_legal_reply reply stored
      then code_source_legal_result stored
      else code_source_without_matching_receipt
             (Code_Source_Legal_Action reply))
  | code_source_from_received (Code_Source_Spend_Action reply)
    (SOME (Code_Source_Spend_Receipt stored)) =
    (if equal_code_source_spend_reply reply stored
      then code_source_spend_result stored
      else code_source_without_matching_receipt
             (Code_Source_Spend_Action reply))
  | code_source_from_received Code_Source_Ordinary_Waiting retained =
    code_source_without_matching_receipt Code_Source_Ordinary_Waiting
  | code_source_from_received Code_Source_Ordinary_Busy retained =
    code_source_without_matching_receipt Code_Source_Ordinary_Busy
  | code_source_from_received Code_Source_Ordinary_Unavailable retained =
    code_source_without_matching_receipt Code_Source_Ordinary_Unavailable
  | code_source_from_received Code_Source_Ordinary_Rejected retained =
    code_source_without_matching_receipt Code_Source_Ordinary_Rejected
  | code_source_from_received (Code_Source_Legal_Action v) NONE =
    code_source_without_matching_receipt (Code_Source_Legal_Action v)
  | code_source_from_received (Code_Source_Legal_Action v)
    (SOME (Code_Source_Ordinary_Receipt vb)) =
    code_source_without_matching_receipt (Code_Source_Legal_Action v)
  | code_source_from_received (Code_Source_Legal_Action v)
    (SOME (Code_Source_Spend_Receipt vb)) =
    code_source_without_matching_receipt (Code_Source_Legal_Action v)
  | code_source_from_received (Code_Source_Spend_Action v) NONE =
    code_source_without_matching_receipt (Code_Source_Spend_Action v)
  | code_source_from_received (Code_Source_Spend_Action v)
    (SOME (Code_Source_Ordinary_Receipt vb)) =
    code_source_without_matching_receipt (Code_Source_Spend_Action v)
  | code_source_from_received (Code_Source_Spend_Action v)
    (SOME (Code_Source_Legal_Receipt vb)) =
    code_source_without_matching_receipt (Code_Source_Spend_Action v)
  | code_source_from_received Code_Source_Other_Action retained =
    code_source_without_matching_receipt Code_Source_Other_Action
  | code_source_from_received reply NONE =
    code_source_without_matching_receipt reply
  | code_source_from_received reply
    (SOME (Code_Source_Ordinary_Receipt Code_Source_Collection_Waiting)) =
    code_source_without_matching_receipt reply
  | code_source_from_received reply
    (SOME (Code_Source_Ordinary_Receipt Code_Source_Collection_Rejected)) =
    code_source_without_matching_receipt reply
  | code_source_from_received (Code_Source_Ordinary_Collected v)
    (SOME (Code_Source_Legal_Receipt va)) =
    code_source_without_matching_receipt (Code_Source_Ordinary_Collected v)
  | code_source_from_received (Code_Source_Ordinary_Collected v)
    (SOME (Code_Source_Spend_Receipt va)) =
    code_source_without_matching_receipt (Code_Source_Ordinary_Collected v);

fun code_transport_refusal_number Invalid_Wire_Format =
  nat_of_integer (70 : IntInf.int)
  | code_transport_refusal_number Unsupported_Wire_Version =
    nat_of_integer (71 : IntInf.int)
  | code_transport_refusal_number Invalid_Wire_Source =
    nat_of_integer (72 : IntInf.int)
  | code_transport_refusal_number Invalid_Wire_Signature =
    nat_of_integer (73 : IntInf.int)
  | code_transport_refusal_number Invalid_Wire_Threshold =
    nat_of_integer (74 : IntInf.int)
  | code_transport_refusal_number Wire_TTL_Expired =
    nat_of_integer (54 : IntInf.int)
  | code_transport_refusal_number Wire_TTL_Invalid =
    nat_of_integer (75 : IntInf.int)
  | code_transport_refusal_number Conflicting_Wire_Replay =
    nat_of_integer (76 : IntInf.int);

fun code_source_error_number (Code_Source_Wire_Validation reason) =
  code_transport_refusal_number reason
  | code_source_error_number Code_Source_Wire_Product_Rejected =
    nat_of_integer (77 : IntInf.int)
  | code_source_error_number Code_Source_Wire_Cancelled =
    nat_of_integer (53 : IntInf.int)
  | code_source_error_number Code_Source_Wire_Deadline =
    nat_of_integer (52 : IntInf.int)
  | code_source_error_number Code_Source_Wire_Response_Lost =
    nat_of_integer (51 : IntInf.int)
  | code_source_error_number Code_Source_Wire_Unresolved =
    nat_of_integer (50 : IntInf.int)
  | code_source_error_number
    (Code_Source_Wire_Recovery Code_Source_Recovery_Endpoint_Rejected) =
    nat_of_integer (77 : IntInf.int)
  | code_source_error_number
    (Code_Source_Wire_Recovery Code_Source_Recovery_Endpoint_Unavailable) =
    nat_of_integer (56 : IntInf.int)
  | code_source_error_number
    (Code_Source_Wire_Recovery Code_Source_Publication_Unsupported) =
    nat_of_integer (50 : IntInf.int)
  | code_source_error_number
    (Code_Source_Wire_Recovery Code_Source_Publication_Deadline) =
    nat_of_integer (50 : IntInf.int)
  | code_source_error_number
    (Code_Source_Wire_Recovery Code_Source_Publication_TTL) =
    nat_of_integer (50 : IntInf.int)
  | code_source_error_number
    (Code_Source_Wire_Recovery Code_Source_Publication_Cancelled) =
    nat_of_integer (50 : IntInf.int)
  | code_source_error_number
    (Code_Source_Wire_Recovery Code_Source_Recovery_Hold) =
    nat_of_integer (50 : IntInf.int)
  | code_source_error_number
    (Code_Source_Wire_Recovery (Code_Source_Recovery_Other v)) =
    nat_of_integer (50 : IntInf.int);

fun code_source_error_result error = (code_source_error_number error, NONE);

fun response_fixed_result (Response_Fixed_Received (reply, retained)) =
  code_source_from_received reply retained
  | response_fixed_result (Response_Fixed_Resolved result) =
    code_source_from_resolution result
  | response_fixed_result (Response_Fixed_Error error) =
    code_source_error_result error;

fun response_v061_result (Response_V061_Legacy prior) =
  response_fixed_result prior
  | response_v061_result (Response_V061_Sync (observed, retained)) =
    (if equal_optiona equal_sync_outcome retained (SOME observed)
      then response_v061_sync_result observed
      else (nat_of_integer (50 : IntInf.int), NONE));

fun full_response_frame_limit
  (Code_response_full_context_ext
    (full_response_config, full_response_channel, full_response_site,
      full_parameters_clock, full_signing_clock, full_response_frame_limit,
      more))
  = full_response_frame_limit;

fun full_response_channel
  (Code_response_full_context_ext
    (full_response_config, full_response_channel, full_response_site,
      full_parameters_clock, full_signing_clock, full_response_frame_limit,
      more))
  = full_response_channel;

fun full_parameters_clock
  (Code_response_full_context_ext
    (full_response_config, full_response_channel, full_response_site,
      full_parameters_clock, full_signing_clock, full_response_frame_limit,
      more))
  = full_parameters_clock;

fun full_response_config
  (Code_response_full_context_ext
    (full_response_config, full_response_channel, full_response_site,
      full_parameters_clock, full_signing_clock, full_response_frame_limit,
      more))
  = full_response_config;

fun response_channel_local_key
  (Response_fixed_channel_ext
    (response_channel_profile, response_channel_deployment,
      response_channel_local, response_channel_remote, response_channel_expires,
      response_channel_local_key, response_channel_remote_key, more))
  = response_channel_local_key;

fun response_fixed_be64 number =
  rev (put_le_octets (nat_of_integer (8 : IntInf.int)) number);

fun response_fixed_binding_preimage original atomicity words =
  [nat_of_integer (111 : IntInf.int), nat_of_integer (105 : IntInf.int),
    nat_of_integer (112 : IntInf.int), nat_of_integer (47 : IntInf.int),
    nat_of_integer (114 : IntInf.int), nat_of_integer (101 : IntInf.int),
    nat_of_integer (102 : IntInf.int), nat_of_integer (101 : IntInf.int),
    nat_of_integer (114 : IntInf.int), nat_of_integer (101 : IntInf.int),
    nat_of_integer (110 : IntInf.int), nat_of_integer (99 : IntInf.int),
    nat_of_integer (101 : IntInf.int), nat_of_integer (45 : IntInf.int),
    nat_of_integer (114 : IntInf.int), nat_of_integer (101 : IntInf.int),
    nat_of_integer (115 : IntInf.int), nat_of_integer (112 : IntInf.int),
    nat_of_integer (111 : IntInf.int), nat_of_integer (110 : IntInf.int),
    nat_of_integer (115 : IntInf.int), nat_of_integer (101 : IntInf.int),
    nat_of_integer (45 : IntInf.int), nat_of_integer (98 : IntInf.int),
    nat_of_integer (105 : IntInf.int), nat_of_integer (110 : IntInf.int),
    nat_of_integer (100 : IntInf.int), nat_of_integer (105 : IntInf.int),
    nat_of_integer (110 : IntInf.int), nat_of_integer (103 : IntInf.int),
    nat_of_integer (47 : IntInf.int), nat_of_integer (118 : IntInf.int),
    nat_of_integer (49 : IntInf.int), zero_nata] @
    response_fixed_be64 (size_list original) @
      original @
        response_fixed_be64 atomicity @
          response_fixed_be64 (size_list words) @
            maps response_fixed_be64 words;

fun response_fixed_post_boundary channel parameters frame_limit =
  Wire_boundary_ext
    (response_channel_profile channel, response_channel_deployment channel,
      response_channel_local channel, response_channel_remote channel,
      response_parameter_principal parameters,
      response_parameter_key parameters, response_parameter_epoch parameters,
      response_parameter_route parameters, response_parameter_issued parameters,
      zero_nata, zero_nata, frame_limit, nat_of_integer (6 : IntInf.int), false,
      false, ());

fun response_config_principal
  (Response_fixed_config_ext
    (response_config_deployment, response_config_local_endpoints,
      response_config_peers, response_config_principal, response_config_key,
      response_config_epoch, response_config_route, response_config_ttl,
      response_config_max_nesting, response_config_public_key,
      response_config_policy_binding, more))
  = response_config_principal;

fun response_config_route
  (Response_fixed_config_ext
    (response_config_deployment, response_config_local_endpoints,
      response_config_peers, response_config_principal, response_config_key,
      response_config_epoch, response_config_route, response_config_ttl,
      response_config_max_nesting, response_config_public_key,
      response_config_policy_binding, more))
  = response_config_route;

fun response_config_epoch
  (Response_fixed_config_ext
    (response_config_deployment, response_config_local_endpoints,
      response_config_peers, response_config_principal, response_config_key,
      response_config_epoch, response_config_route, response_config_ttl,
      response_config_max_nesting, response_config_public_key,
      response_config_policy_binding, more))
  = response_config_epoch;

fun response_config_ttl
  (Response_fixed_config_ext
    (response_config_deployment, response_config_local_endpoints,
      response_config_peers, response_config_principal, response_config_key,
      response_config_epoch, response_config_route, response_config_ttl,
      response_config_max_nesting, response_config_public_key,
      response_config_policy_binding, more))
  = response_config_ttl;

fun response_config_key
  (Response_fixed_config_ext
    (response_config_deployment, response_config_local_endpoints,
      response_config_peers, response_config_principal, response_config_key,
      response_config_epoch, response_config_route, response_config_ttl,
      response_config_max_nesting, response_config_public_key,
      response_config_policy_binding, more))
  = response_config_key;

fun response_config_local_endpoints
  (Response_fixed_config_ext
    (response_config_deployment, response_config_local_endpoints,
      response_config_peers, response_config_principal, response_config_key,
      response_config_epoch, response_config_route, response_config_ttl,
      response_config_max_nesting, response_config_public_key,
      response_config_policy_binding, more))
  = response_config_local_endpoints;

fun response_config_public_key
  (Response_fixed_config_ext
    (response_config_deployment, response_config_local_endpoints,
      response_config_peers, response_config_principal, response_config_key,
      response_config_epoch, response_config_route, response_config_ttl,
      response_config_max_nesting, response_config_public_key,
      response_config_policy_binding, more))
  = response_config_public_key;

fun response_config_deployment
  (Response_fixed_config_ext
    (response_config_deployment, response_config_local_endpoints,
      response_config_peers, response_config_principal, response_config_key,
      response_config_epoch, response_config_route, response_config_ttl,
      response_config_max_nesting, response_config_public_key,
      response_config_policy_binding, more))
  = response_config_deployment;

fun response_config_peers
  (Response_fixed_config_ext
    (response_config_deployment, response_config_local_endpoints,
      response_config_peers, response_config_principal, response_config_key,
      response_config_epoch, response_config_route, response_config_ttl,
      response_config_max_nesting, response_config_public_key,
      response_config_policy_binding, more))
  = response_config_peers;

fun response_fixed_channel_current config channel =
  equal_nata (negotiated_version (response_channel_profile channel))
    (nat_of_integer (6 : IntInf.int)) andalso
    (equal_nata (response_channel_deployment channel)
       (response_config_deployment config) andalso
      (member equal_nat (response_channel_local channel)
         (response_config_local_endpoints config) andalso
        (equal_lista equal_nat (response_channel_local_key channel)
           (response_config_public_key config) andalso
          member (equal_prod equal_nat (equal_list equal_nat))
            (response_channel_remote channel,
              response_channel_remote_key channel)
            (response_config_peers config))));

fun response_config_policy_binding
  (Response_fixed_config_ext
    (response_config_deployment, response_config_local_endpoints,
      response_config_peers, response_config_principal, response_config_key,
      response_config_epoch, response_config_route, response_config_ttl,
      response_config_max_nesting, response_config_public_key,
      response_config_policy_binding, more))
  = response_config_policy_binding;

fun response_fixed_uuid_preimage config response_binding issued =
  [nat_of_integer (111 : IntInf.int), nat_of_integer (105 : IntInf.int),
    nat_of_integer (112 : IntInf.int), nat_of_integer (47 : IntInf.int),
    nat_of_integer (114 : IntInf.int), nat_of_integer (101 : IntInf.int),
    nat_of_integer (102 : IntInf.int), nat_of_integer (101 : IntInf.int),
    nat_of_integer (114 : IntInf.int), nat_of_integer (101 : IntInf.int),
    nat_of_integer (110 : IntInf.int), nat_of_integer (99 : IntInf.int),
    nat_of_integer (101 : IntInf.int), nat_of_integer (45 : IntInf.int),
    nat_of_integer (114 : IntInf.int), nat_of_integer (101 : IntInf.int),
    nat_of_integer (115 : IntInf.int), nat_of_integer (112 : IntInf.int),
    nat_of_integer (111 : IntInf.int), nat_of_integer (110 : IntInf.int),
    nat_of_integer (115 : IntInf.int), nat_of_integer (101 : IntInf.int),
    nat_of_integer (45 : IntInf.int), nat_of_integer (117 : IntInf.int),
    nat_of_integer (117 : IntInf.int), nat_of_integer (105 : IntInf.int),
    nat_of_integer (100 : IntInf.int), nat_of_integer (47 : IntInf.int),
    nat_of_integer (118 : IntInf.int), nat_of_integer (49 : IntInf.int),
    zero_nata] @
    response_config_policy_binding config @
      response_binding @ response_fixed_be64 issued;

fun response_fixed_uuid (A1_, A2_) digest =
  list_update
    (list_update (take (nat_of_integer (16 : IntInf.int)) digest)
      (nat_of_integer (6 : IntInf.int))
      (plus ((plus_semigroup_add o semigroup_add_numeral) A1_)
        (modulo A2_ (nth digest (nat_of_integer (6 : IntInf.int)))
          (numeral A1_ (Bit0 (Bit0 (Bit0 (Bit0 One))))))
        (numeral A1_ (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))))
    (nat_of_integer (8 : IntInf.int))
    (plus ((plus_semigroup_add o semigroup_add_numeral) A1_)
      (modulo A2_ (nth digest (nat_of_integer (8 : IntInf.int)))
        (numeral A1_ (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))))
      (numeral A1_ (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))));

fun response_fixed_parameters_from hash config channel clock response_binding =
  (if not (response_fixed_channel_current config channel) then NONE
    else map_option
           (fn issued =>
             Response_fixed_parameters_ext
               (response_config_principal config, response_config_key config,
                 response_config_epoch config, issued,
                 response_config_ttl config,
                 response_fixed_uuid (numeral_nat, modulo_nat)
                   (hash (response_fixed_uuid_preimage config response_binding
                           issued)),
                 response_config_route config, ()))
           clock);

fun response_v061_encoding_refused reason =
  Inl (Response_Fixed_Encoding_Refused reason);

fun full_signing_clock
  (Code_response_full_context_ext
    (full_response_config, full_response_channel, full_response_site,
      full_parameters_clock, full_signing_clock, full_response_frame_limit,
      more))
  = full_signing_clock;

fun response_fixed_unframe preimage =
  (if less_nat (size_list preimage) (nat_of_integer (17 : IntInf.int)) orelse
        not (equal_lista equal_nat
              (take (nat_of_integer (13 : IntInf.int)) preimage)
              [nat_of_integer (79 : IntInf.int),
                nat_of_integer (73 : IntInf.int),
                nat_of_integer (80 : IntInf.int), zero_nata,
                nat_of_integer (69 : IntInf.int),
                nat_of_integer (78 : IntInf.int),
                nat_of_integer (86 : IntInf.int),
                nat_of_integer (69 : IntInf.int),
                nat_of_integer (76 : IntInf.int),
                nat_of_integer (79 : IntInf.int),
                nat_of_integer (80 : IntInf.int),
                nat_of_integer (69 : IntInf.int), zero_nata])
    then NONE
    else let
           val framed = drop (nat_of_integer (13 : IntInf.int)) preimage;
           val bytes = drop (nat_of_integer (4 : IntInf.int)) framed;
           val declared =
             get_le_octets
               (rev (take (nat_of_integer (4 : IntInf.int)) framed));
         in
           (if not (equal_nata declared (size_list bytes)) then NONE
             else decode_wire_core bytes)
         end);

fun response_config_max_nesting
  (Response_fixed_config_ext
    (response_config_deployment, response_config_local_endpoints,
      response_config_peers, response_config_principal, response_config_key,
      response_config_epoch, response_config_route, response_config_ttl,
      response_config_max_nesting, response_config_public_key,
      response_config_policy_binding, more))
  = response_config_max_nesting;

fun response_v061_signable config v061_now core =
  less_eq_nat (wire_sent_seconds core) v061_now andalso
    (less_nat (plus_nata (wire_sent_seconds core) (response_config_ttl config))
       (power power_nat (nat_of_integer (2 : IntInf.int))
         (nat_of_integer (64 : IntInf.int))) andalso
      (less_eq_nat v061_now
         (plus_nata (wire_sent_seconds core)
           (response_config_ttl config)) andalso
        (equal_nata (wire_version core)
           (nat_of_integer (6 : IntInf.int)) andalso
          (equal_nata (wire_purpose core) one_nata andalso
            (equal_nata (wire_deployment core)
               (response_config_deployment config) andalso
              (member equal_nat (wire_source_domain core)
                 (response_config_local_endpoints config) andalso
                (member equal_nat (wire_target_domain core)
                   (image fst (response_config_peers config)) andalso
                  (equal_nata (wire_principal core)
                     (response_config_principal config) andalso
                    (equal_nata (wire_key_number core)
                       (response_config_key config) andalso
                      (equal_nata (wire_authority_epoch core)
                         (response_config_epoch config) andalso
                        (equal_nata (wire_route_scope core)
                           (response_config_route config) andalso
                          (equal_nata (wire_ttl_seconds core)
                             (response_config_ttl config) andalso
                            (equal_nata (wire_signature_scheme core)
                               one_nata andalso
                              equal_sum equal_wire_refusal
                                equal_response_v061_nested
                                (response_v061_operand
                                  (response_config_max_nesting config) core)
                                (Inr (Response_V061_Legacy_Operand
                                       Code_Nested_Response)))))))))))))));

fun response_v061_sign_guard context preimage =
  (case response_fixed_unframe preimage of NONE => false
    | SOME core =>
      (case full_signing_clock context of NONE => false
        | SOME v061_now =>
          response_v061_signable (full_response_config context) v061_now core));

fun response_v061_encode hash curve_sign curve_verify context selected_mode
  original call result =
  let
    val channel = full_response_channel context;
    val config = full_response_config context;
    val frame_limit = full_response_frame_limit context;
    val exact = encode_wire_core original;
  in
    (case response_v061_words call result
      of NONE => response_v061_encoding_refused Invalid_Wire_Format
      | SOME (kind, (number, (position, words))) =>
        (case selected_mode
          of NONE => response_v061_encoding_refused Unsupported_Wire_Version
          | SOME atomicity =>
            let
              val binding_message =
                response_fixed_binding_preimage exact atomicity words;
            in
              (case response_fixed_parameters_from hash config channel
                      (full_parameters_clock context) (hash binding_message)
                of NONE => response_v061_encoding_refused Invalid_Wire_Source
                | SOME parameters =>
                  (if less_nat (response_channel_expires channel)
                        (response_parameter_issued parameters)
                    then response_v061_encoding_refused Invalid_Wire_Source
                    else let
                           val core =
                             response_fixed_core channel parameters atomicity
                               words exact;
                         in
                           (case code_typed_encode_core core
                             of NONE =>
                               response_v061_encoding_refused
                                 Invalid_Wire_Format
                             | SOME core_bytes =>
                               (if less_eq_nat
                                     (power power_nat
                                       (nat_of_integer (2 : IntInf.int))
                                       (nat_of_integer (32 : IntInf.int)))
                                     (size_list core_bytes)
                                 then response_v061_encoding_refused
Invalid_Wire_Format
                                 else let
val preimage = envelope_signing_bytes core;
                                      in
(if not (response_v061_sign_guard context preimage)
  then Inl Response_Fixed_Signature_Unavailable
  else let
         val packet =
           Wire_packet_ext
             (core, curve_sign (response_channel_local_key channel) preimage,
               ());
       in
         (case code_encode_packet packet
           of NONE => response_v061_encoding_refused Invalid_Wire_Format
           | SOME encoded =>
             (if less_nat frame_limit (size_list encoded)
               then response_v061_encoding_refused Invalid_Wire_Format
               else (case sync_decode_packet encoded
                      of NONE =>
                        response_v061_encoding_refused Invalid_Wire_Format
                      | SOME parsed =>
                        (case code_admit_packet
                                (fn _ =>
                                  curve_verify
                                    (response_channel_local_key channel))
                                parsed
                                (response_fixed_post_boundary channel parameters
                                  frame_limit)
                          of NONE =>
                            (case response_v061_validate
                                    (nat_of_integer (2 : IntInf.int)) original
                                    parsed
                              of Inl a => response_v061_encoding_refused a
                              | Inr (verified, _) =>
                                Inr (Response_fixed_emission_ext
                                      (encoded, parsed, original,
(call, (kind, (number, position))), verified, parameters, binding_message,
preimage, ())))
                          | SOME a => response_v061_encoding_refused a))))
       end)
                                      end))
                         end))
            end))
  end;

fun code_numeric_family_set numbers =
  Set (maps (fn number =>
              (case family_at_number number of NONE => []
                | SOME family => [family]))
        numbers);

fun code_contract_boundary values version families atomicities schemes critical
  = Wire_boundary_ext
      (Negotiated_wire_profile_ext
         (version, code_numeric_family_set families, Set atomicities,
           Set schemes, ()),
        nth values zero_nata, nth values one_nata,
        nth values (nat_of_integer (2 : IntInf.int)),
        nth values (nat_of_integer (3 : IntInf.int)),
        nth values (nat_of_integer (4 : IntInf.int)),
        nth values (nat_of_integer (5 : IntInf.int)),
        nth values (nat_of_integer (6 : IntInf.int)),
        nth values (nat_of_integer (7 : IntInf.int)),
        nth values (nat_of_integer (8 : IntInf.int)),
        nth values (nat_of_integer (9 : IntInf.int)),
        nth values (nat_of_integer (10 : IntInf.int)),
        nth values (nat_of_integer (11 : IntInf.int)), critical, false, ());

fun response_v061_accepts accept_sync accept_current family operation =
  reference_accepts_write family operation orelse
    (accept_sync andalso
       equal_proda equal_wire_family equal_nat (family, operation)
         (Wire_State_Sync, nat_of_integer (7 : IntInf.int)) orelse
      accept_current andalso
        equal_proda equal_wire_family equal_nat (family, operation)
          (Wire_Query, nat_of_integer (9 : IntInf.int)));

fun code_integer_u64_values values =
  list_all
    (fn value =>
      IntInf.<= ((0 : IntInf.int), value) andalso
        IntInf.< (value, power power_integer (2 : IntInf.int)
                           (nat_of_integer (64 : IntInf.int))))
    values;

fun code_full_profile x =
  (fn oip_full_rows =>
    Negotiated_wire_profile_ext
      (nth (nth oip_full_rows zero_nata) zero_nata,
        code_numeric_family_set (nth oip_full_rows one_nata),
        Set (nth oip_full_rows (nat_of_integer (2 : IntInf.int))),
        Set (nth oip_full_rows (nat_of_integer (3 : IntInf.int))), ()))
    x;

fun code_full_channel x =
  (fn oip_full_rows =>
    Response_fixed_channel_ext
      (code_full_profile oip_full_rows,
        nth (nth oip_full_rows zero_nata) one_nata,
        nth (nth oip_full_rows zero_nata) (nat_of_integer (2 : IntInf.int)),
        nth (nth oip_full_rows zero_nata) (nat_of_integer (3 : IntInf.int)),
        nth (nth oip_full_rows zero_nata) (nat_of_integer (4 : IntInf.int)),
        nth oip_full_rows (nat_of_integer (4 : IntInf.int)),
        nth oip_full_rows (nat_of_integer (5 : IntInf.int)), ()))
    x;

fun code_full_lookup_hash x =
  (fn oip_full_table => fn oip_full_message =>
    map_option snd
      (find (fn oip_full_item =>
              equal_lista equal_nat (fst oip_full_item) oip_full_message)
        oip_full_table))
    x;

fun code_full_hash x =
  (fn oip_full_table => fn oip_full_message =>
    (case code_full_lookup_hash oip_full_table oip_full_message
      of NONE => (raise Fail "OIP_PRIMITIVE_MISSING_SHA256") (fn _ => [])
      | SOME oip_full_digest => oip_full_digest))
    x;

fun code_full_lookup_sign x =
  (fn oip_full_table => fn oip_full_key => fn oip_full_message =>
    map_option (fn (_, (_, oip_full_signature)) => oip_full_signature)
      (find (fn (oip_full_record_key, (oip_full_record_message, _)) =>
              equal_lista equal_nat oip_full_record_key oip_full_key andalso
                equal_lista equal_nat oip_full_record_message oip_full_message)
        oip_full_table))
    x;

fun code_full_sign x =
  (fn oip_full_table => fn oip_full_key => fn _ => fn oip_full_message =>
    (case code_full_lookup_sign oip_full_table oip_full_key oip_full_message
      of NONE => (raise Fail "OIP_PRIMITIVE_MISSING_ED25519_SIGN") (fn _ => [])
      | SOME oip_full_signature => oip_full_signature))
    x;

fun code_response_caller core =
  (case code_decode_operand_tree one_nata core of Code_Tree_Refused a => Inl a
    | Code_Tree_Ready (Code_Nested_Ordinary (native, _)) =>
      Inr (native_id native)
    | Code_Tree_Ready (Code_Nested_Legal a) => Inr a
    | Code_Tree_Ready (Code_Nested_Spend a) => Inr a
    | Code_Tree_Ready (Code_Nested_Receipt _) => Inl Invalid_Wire_Format
    | Code_Tree_Ready Code_Nested_Response => Inl Invalid_Wire_Format
    | Code_Tree_Ready Code_Nested_Other => Inl Invalid_Wire_Format
    | Code_Tree_Pending => Inl Invalid_Wire_Format);

fun code_response_body_length count original_length =
  plus_nata
    (plus_nata
      (plus_nata (nat_of_integer (3 : IntInf.int))
        (times_nata (nat_of_integer (9 : IntInf.int)) count))
      (size_list (put_wire_varint original_length)))
    original_length;

fun code_response_core_length count original_length =
  let
    val body = code_response_body_length count original_length;
  in
    plus_nata
      (plus_nata (nat_of_integer (118 : IntInf.int))
        (size_list (put_wire_varint body)))
      body
  end;

fun code_full_clock_row x =
  (fn oip_full_context =>
    (case full_parameters_clock oip_full_context
      of NONE => [zero_nata, zero_nata]
      | SOME oip_full_now => [one_nata, oip_full_now]) @
      (case full_signing_clock oip_full_context
        of NONE => [zero_nata, zero_nata]
        | SOME oip_full_now => [one_nata, oip_full_now]))
    x;

fun code_full_parse_verify_rows [] = SOME []
  | code_full_parse_verify_rows
    (oip_full_key ::
      oip_full_message ::
        oip_full_signature :: oip_full_answer :: oip_full_rest)
    = (if not (equal_nata (size_list oip_full_key)
                (nat_of_integer (32 : IntInf.int))) orelse
            (not (list_all (wire_octets (numeral_nat, ord_nat))
                   [oip_full_key, oip_full_message, oip_full_signature]) orelse
              not (equal_lista equal_nat oip_full_answer [zero_nata]) andalso
                not (equal_lista equal_nat oip_full_answer [one_nata]))
        then NONE
        else map_option
               (fn a =>
                 (oip_full_key,
                   (oip_full_message,
                     (oip_full_signature,
                       equal_lista equal_nat oip_full_answer [one_nata]))) ::
                   a)
               (code_full_parse_verify_rows oip_full_rest))
  | code_full_parse_verify_rows [uu] = NONE
  | code_full_parse_verify_rows [uv, uw] = NONE
  | code_full_parse_verify_rows [ux, uy, uz] = NONE;

fun code_full_parse_sign_rows [] = SOME []
  | code_full_parse_sign_rows
    (oip_full_key :: oip_full_message :: oip_full_signature :: oip_full_rest) =
    (if not (equal_nata (size_list oip_full_key)
              (nat_of_integer (32 : IntInf.int))) orelse
          (not (equal_nata (size_list oip_full_signature)
                 (nat_of_integer (64 : IntInf.int))) orelse
            not (list_all (wire_octets (numeral_nat, ord_nat))
                  [oip_full_key, oip_full_message, oip_full_signature]))
      then NONE
      else map_option
             (fn a =>
               (oip_full_key, (oip_full_message, oip_full_signature)) :: a)
             (code_full_parse_sign_rows oip_full_rest))
  | code_full_parse_sign_rows [uu] = NONE
  | code_full_parse_sign_rows [uv, uw] = NONE;

fun code_full_parse_hash_rows [] = SOME []
  | code_full_parse_hash_rows
    (oip_full_message :: oip_full_digest :: oip_full_rest) =
    (if not (equal_nata (size_list oip_full_digest)
              (nat_of_integer (32 : IntInf.int))) orelse
          not (list_all (wire_octets (numeral_nat, ord_nat))
                [oip_full_message, oip_full_digest])
      then NONE
      else map_option (fn a => (oip_full_message, oip_full_digest) :: a)
             (code_full_parse_hash_rows oip_full_rest))
  | code_full_parse_hash_rows [uu] = NONE;

fun code_integer_octet_values values =
  list_all
    (fn value =>
      IntInf.<= ((0 : IntInf.int), value) andalso
        IntInf.< (value, (256 : IntInf.int)))
    values;

fun code_full_tables_from_integer x =
  (fn oip_full_hash_rows => fn oip_full_sign_rows => fn oip_full_verify_rows =>
    (if not (code_integer_octet_values
              (concat
                (oip_full_hash_rows @
                  oip_full_sign_rows @ oip_full_verify_rows)))
      then NONE
      else bind (code_full_parse_hash_rows
                  (map (map nat_of_integer) oip_full_hash_rows))
             (fn oip_full_hashes =>
               bind (code_full_parse_sign_rows
                      (map (map nat_of_integer) oip_full_sign_rows))
                 (fn oip_full_signatures =>
                   bind (code_full_parse_verify_rows
                          (map (map nat_of_integer) oip_full_verify_rows))
                     (fn oip_full_verifications =>
                       (if distinct (equal_list equal_nat)
                             (map fst oip_full_hashes) andalso
                             (distinct
                                (equal_prod (equal_list equal_nat)
                                  (equal_list equal_nat))
                                (map (fn (oip_full_key, (oip_full_message, _))
=>
                                       (oip_full_key, oip_full_message))
                                  oip_full_signatures) andalso
                               distinct
                                 (equal_prod (equal_list equal_nat)
                                   (equal_prod (equal_list equal_nat)
                                     (equal_list equal_nat)))
                                 (map (fn
 (oip_full_key, (oip_full_message, (oip_full_signature, _))) =>
(oip_full_key, (oip_full_message, oip_full_signature)))
                                   oip_full_verifications))
                         then SOME (oip_full_hashes,
                                     (oip_full_signatures,
                                       oip_full_verifications))
                         else NONE))))))
    x;

fun code_full_build_client x =
  (fn oip_full_rows =>
    (code_full_channel oip_full_rows,
      Response_fixed_client_boundary_ext
        (code_contract_boundary
           (nth oip_full_rows (nat_of_integer (6 : IntInf.int)))
           (nth (nth oip_full_rows zero_nata) zero_nata)
           (nth oip_full_rows one_nata)
           (nth oip_full_rows (nat_of_integer (2 : IntInf.int)))
           (nth oip_full_rows (nat_of_integer (3 : IntInf.int)))
           (equal_nata
             (nth (nth oip_full_rows (nat_of_integer (7 : IntInf.int)))
               zero_nata)
             one_nata),
          nth oip_full_rows (nat_of_integer (8 : IntInf.int)),
          nth (nth oip_full_rows (nat_of_integer (6 : IntInf.int)))
            (nat_of_integer (12 : IntInf.int)),
          ())))
    x;

fun code_full_client_from_integer x =
  (fn oip_full_rows =>
    (if not (equal_nata (size_list oip_full_rows)
              (nat_of_integer (9 : IntInf.int))) orelse
          not (code_integer_u64_values (concat oip_full_rows))
      then NONE
      else let
             val oip_full_natural = map (map nat_of_integer) oip_full_rows;
           in
             (if not (equal_nata (size_list (nth oip_full_natural zero_nata))
                       (nat_of_integer (5 : IntInf.int))) orelse
                   (not (equal_nata
                          (size_list
                            (nth oip_full_natural
                              (nat_of_integer (6 : IntInf.int))))
                          (nat_of_integer (13 : IntInf.int))) orelse
                     not (equal_nata
                           (size_list
                             (nth oip_full_natural
                               (nat_of_integer (7 : IntInf.int))))
                           one_nata))
               then NONE
               else (if not (member equal_nat
                              (nth (nth oip_full_natural
                                     (nat_of_integer (7 : IntInf.int)))
                                zero_nata)
                              (insert equal_nat zero_nata
                                (insert equal_nat one_nata bot_set))) orelse
                          not (list_all
                                (fn oip_full_key =>
                                  equal_nata (size_list oip_full_key)
                                    (nat_of_integer (32 : IntInf.int)) andalso
                                    wire_octets (numeral_nat, ord_nat)
                                      oip_full_key)
                                [nth oip_full_natural
                                   (nat_of_integer (4 : IntInf.int)),
                                  nth oip_full_natural
                                    (nat_of_integer (5 : IntInf.int)),
                                  nth oip_full_natural
                                    (nat_of_integer (8 : IntInf.int))])
                      then NONE
                      else SOME (code_full_build_client oip_full_natural)))
           end))
    x;

fun response_v061_client_input rows expected received verify_rows =
  (if not (code_integer_octet_values (expected @ received)) then NONE
    else bind (code_full_client_from_integer rows)
           (fn (channel, current) =>
             bind (sync_decode_packet (map nat_of_integer expected))
               (fn original =>
                 map_option
                   (fn (_, (_, verifications)) =>
                     (channel,
                       (current,
                         (original,
                           (map nat_of_integer received, verifications)))))
                   (code_full_tables_from_integer [] [] verify_rows))));

fun code_response_list_atomicity x =
  (fn a =>
    (case a of [] => NONE
      | oip_exec_first :: oip_exec_rest =>
        SOME (fold (min ord_nat) oip_exec_rest oip_exec_first)))
    x;

fun code_full_build_context x =
  (fn oip_full_rows => fn oip_full_parameters_time =>
    fn oip_full_signing_time =>
    Code_response_full_context_ext
      (Response_fixed_config_ext
         (nth (nth oip_full_rows (nat_of_integer (6 : IntInf.int))) zero_nata,
           Set (nth oip_full_rows (nat_of_integer (7 : IntInf.int))),
           Set (zip (nth oip_full_rows (nat_of_integer (8 : IntInf.int)))
                 (drop (nat_of_integer (14 : IntInf.int)) oip_full_rows)),
           nth (nth oip_full_rows (nat_of_integer (6 : IntInf.int))) one_nata,
           nth (nth oip_full_rows (nat_of_integer (6 : IntInf.int)))
             (nat_of_integer (2 : IntInf.int)),
           nth (nth oip_full_rows (nat_of_integer (6 : IntInf.int)))
             (nat_of_integer (3 : IntInf.int)),
           nth (nth oip_full_rows (nat_of_integer (6 : IntInf.int)))
             (nat_of_integer (4 : IntInf.int)),
           nth (nth oip_full_rows (nat_of_integer (6 : IntInf.int)))
             (nat_of_integer (5 : IntInf.int)),
           nth (nth oip_full_rows (nat_of_integer (6 : IntInf.int)))
             (nat_of_integer (6 : IntInf.int)),
           nth oip_full_rows (nat_of_integer (9 : IntInf.int)),
           nth oip_full_rows (nat_of_integer (10 : IntInf.int)), ()),
        code_full_channel oip_full_rows,
        Response_fixed_site_ext
          ((nth (nth oip_full_rows (nat_of_integer (11 : IntInf.int)))
              zero_nata,
             (nth (nth oip_full_rows (nat_of_integer (11 : IntInf.int)))
                one_nata,
               nth (nth oip_full_rows (nat_of_integer (11 : IntInf.int)))
                 (nat_of_integer (2 : IntInf.int)))),
            (if equal_nata
                  (nth (nth oip_full_rows (nat_of_integer (11 : IntInf.int)))
                    (nat_of_integer (3 : IntInf.int)))
                  one_nata
              then SOME () else NONE),
            (if equal_nata
                  (nth (nth oip_full_rows (nat_of_integer (11 : IntInf.int)))
                    (nat_of_integer (4 : IntInf.int)))
                  one_nata
              then SOME (nth (nth oip_full_rows
                               (nat_of_integer (11 : IntInf.int)))
                           (nat_of_integer (5 : IntInf.int)),
                          (nth (nth oip_full_rows
                                 (nat_of_integer (11 : IntInf.int)))
                             (nat_of_integer (6 : IntInf.int)),
                            nth (nth oip_full_rows
                                  (nat_of_integer (11 : IntInf.int)))
                              (nat_of_integer (7 : IntInf.int))))
              else NONE),
            ()),
        oip_full_parameters_time, oip_full_signing_time,
        nth (nth oip_full_rows (nat_of_integer (13 : IntInf.int))) zero_nata,
        ()))
    x;

fun code_rbound_position oip_binder_present oip_binder_position =
  (if equal_nata oip_binder_present zero_nata
    then (if equal_nata oip_binder_position zero_nata then SOME NONE else NONE)
    else (if equal_nata oip_binder_present one_nata
           then SOME (SOME oip_binder_position) else NONE));

fun code_full_parse_context x =
  (fn oip_full_rows =>
    (if less_nat (size_list oip_full_rows) (nat_of_integer (14 : IntInf.int))
      then NONE
      else (if not (equal_nata (size_list (nth oip_full_rows zero_nata))
                     (nat_of_integer (5 : IntInf.int))) orelse
                 (not (equal_nata
                        (size_list
                          (nth oip_full_rows (nat_of_integer (6 : IntInf.int))))
                        (nat_of_integer (7 : IntInf.int))) orelse
                   (not (equal_nata
                          (size_list
                            (nth oip_full_rows
                              (nat_of_integer (11 : IntInf.int))))
                          (nat_of_integer (8 : IntInf.int))) orelse
                     (not (equal_nata
                            (size_list
                              (nth oip_full_rows
                                (nat_of_integer (12 : IntInf.int))))
                            (nat_of_integer (4 : IntInf.int))) orelse
                       (not (equal_nata
                              (size_list
                                (nth oip_full_rows
                                  (nat_of_integer (13 : IntInf.int))))
                              one_nata) orelse
                         (not (equal_nata
                                (size_list
                                  (nth oip_full_rows
                                    (nat_of_integer (8 : IntInf.int))))
                                (size_list
                                  (drop (nat_of_integer (14 : IntInf.int))
                                    oip_full_rows))) orelse
                           (not (list_all
                                  (fn oip_full_key =>
                                    equal_nata (size_list oip_full_key)
                                      (nat_of_integer (32 : IntInf.int)))
                                  ([nth oip_full_rows
                                      (nat_of_integer (4 : IntInf.int)),
                                     nth oip_full_rows
                                       (nat_of_integer (5 : IntInf.int)),
                                     nth oip_full_rows
                                       (nat_of_integer (9 : IntInf.int)),
                                     nth oip_full_rows
                                       (nat_of_integer (10 : IntInf.int))] @
                                    drop (nat_of_integer (14 : IntInf.int))
                                      oip_full_rows)) orelse
                             (not (member equal_nat
                                    (nth (nth oip_full_rows
   (nat_of_integer (11 : IntInf.int)))
                                      (nat_of_integer (3 : IntInf.int)))
                                    (insert equal_nat zero_nata
                                      (insert equal_nat one_nata
bot_set))) orelse
                               (not (member equal_nat
                                      (nth
(nth oip_full_rows (nat_of_integer (11 : IntInf.int)))
(nat_of_integer (4 : IntInf.int)))
                                      (insert equal_nat zero_nata
(insert equal_nat one_nata bot_set))) orelse
                                 not (list_all
                                       (wire_octets (numeral_nat, ord_nat))
                                       ([nth oip_full_rows
   (nat_of_integer (4 : IntInf.int)),
  nth oip_full_rows (nat_of_integer (5 : IntInf.int)),
  nth oip_full_rows (nat_of_integer (9 : IntInf.int)),
  nth oip_full_rows (nat_of_integer (10 : IntInf.int))] @
 drop (nat_of_integer (14 : IntInf.int)) oip_full_rows))))))))))
             then NONE
             else bind (code_rbound_position
                         (nth (nth oip_full_rows
                                (nat_of_integer (12 : IntInf.int)))
                           zero_nata)
                         (nth (nth oip_full_rows
                                (nat_of_integer (12 : IntInf.int)))
                           one_nata))
                    (fn oip_full_parameters_time =>
                      map_option
                        (code_full_build_context oip_full_rows
                          oip_full_parameters_time)
                        (code_rbound_position
                          (nth (nth oip_full_rows
                                 (nat_of_integer (12 : IntInf.int)))
                            (nat_of_integer (2 : IntInf.int)))
                          (nth (nth oip_full_rows
                                 (nat_of_integer (12 : IntInf.int)))
                            (nat_of_integer (3 : IntInf.int))))))))
    x;

fun code_full_context_from_integer x =
  (fn oip_full_rows =>
    (if not (code_integer_u64_values (concat oip_full_rows)) then NONE
      else code_full_parse_context (map (map nat_of_integer) oip_full_rows)))
    x;

fun code_rbound_accepted_reply oip_binder_tag =
  let
    val oip_binder_variants =
      [Code_Source_Rejected_Reply, Code_Source_Busy_Reply,
        Code_Source_Reserved_Reply, Code_Source_Dispatched_Reply,
        Code_Source_Debited_Reply, Code_Source_Closed_Reply,
        Code_Source_Preempted_Reply, Code_Source_Time_Reply,
        Code_Source_Recorded_Reply, Code_Source_Credited_Reply,
        Code_Source_Reconciled_Reply, Code_Source_Refunded_Reply,
        Code_Source_Data_Reply, Code_Source_Evidence_Reply,
        Code_Source_Published_Reply];
  in
    (if less_nat oip_binder_tag (size_list oip_binder_variants)
      then SOME (nth oip_binder_variants oip_binder_tag) else NONE)
  end;

fun code_rbound_outcome oip_binder_values =
  (case oip_binder_values of [] => NONE | [_] => NONE | [_, _] => NONE
    | [oip_binder_tag, oip_binder_first, oip_binder_present] =>
      bind (code_rbound_position oip_binder_first oip_binder_present)
        (fn oip_binder_commit =>
          map_option
            (fn oip_binder_reply =>
              Code_source_outcome_ext (oip_binder_reply, oip_binder_commit, ()))
            (if equal_nata oip_binder_tag one_nata
              then SOME Code_Source_Duplicate_Decision
              else (if equal_nata oip_binder_tag
                         (nat_of_integer (3 : IntInf.int))
                     then SOME Code_Source_Outcome_Rejected
                     else (if equal_nata oip_binder_tag
                                (nat_of_integer (4 : IntInf.int))
                            then SOME Code_Source_Outcome_Busy
                            else (if equal_nata oip_binder_tag
                                       (nat_of_integer (5 : IntInf.int))
                                   then SOME Code_Source_Outcome_Unavailable
                                   else NONE)))))
    | [oip_binder_tag, oip_binder_first, oip_binder_present,
        oip_binder_position]
      => bind (code_rbound_position oip_binder_present oip_binder_position)
           (fn oip_binder_commit =>
             (if equal_nata oip_binder_tag zero_nata
               then map_option
                      (fn oip_binder_reply =>
                        Code_source_outcome_ext
                          (Code_Source_Accepted oip_binder_reply,
                            oip_binder_commit, ()))
                      (code_rbound_accepted_reply oip_binder_first)
               else (if equal_nata oip_binder_tag
                          (nat_of_integer (2 : IntInf.int)) andalso
                          member equal_nat oip_binder_first
                            (insert equal_nat one_nata
                              (insert equal_nat
                                (nat_of_integer (2 : IntInf.int)) bot_set))
                      then SOME (Code_source_outcome_ext
                                  ((if equal_nata oip_binder_first one_nata
                                     then Code_Source_Duplicate_Confirmed
                                     else Code_Source_Duplicate_Reversed),
                                    oip_binder_commit, ()))
                      else NONE)))
    | _ :: _ :: _ :: _ :: _ :: _ => NONE);

fun code_rbound_collection oip_binder_values =
  (case oip_binder_values of [] => NONE
    | oip_binder_tag :: oip_binder_rest =>
      (if equal_nata oip_binder_tag zero_nata
        then map_option Code_Source_Collected
               (code_rbound_outcome oip_binder_rest)
        else (if not (null oip_binder_rest) then NONE
               else (if equal_nata oip_binder_tag one_nata
                      then SOME Code_Source_Collection_Waiting
                      else (if equal_nata oip_binder_tag
                                 (nat_of_integer (2 : IntInf.int))
                             then SOME Code_Source_Collection_Rejected
                             else NONE)))));

fun code_rbound_spend oip_binder_values =
  (case oip_binder_values of [] => NONE
    | [oip_binder_tag] =>
      (if equal_nata oip_binder_tag one_nata
        then SOME (NONE, Code_Source_Spend_Rejected)
        else (if equal_nata oip_binder_tag (nat_of_integer (2 : IntInf.int))
               then SOME (NONE, Code_Source_Spend_Busy)
               else (if equal_nata oip_binder_tag
                          (nat_of_integer (3 : IntInf.int))
                      then SOME (NONE, Code_Source_Spend_Unavailable)
                      else NONE)))
    | [_, _] => NONE | [_, _, _] => NONE
    | [oip_binder_tag, oip_binder_domain, oip_binder_event, oip_binder_position]
      => (if equal_nata oip_binder_tag zero_nata
           then SOME (SOME (oip_binder_domain, oip_binder_event),
                       Code_Source_Spend_Executed oip_binder_position)
           else NONE)
    | _ :: _ :: _ :: _ :: _ :: _ => NONE);

fun code_rbound_legal oip_binder_values =
  (case oip_binder_values of [] => NONE | [_] => NONE
    | [oip_binder_tag, oip_binder_value] =>
      (if equal_nata oip_binder_tag zero_nata
        then SOME (Code_Source_Legal_Emitted oip_binder_value)
        else (if equal_nata oip_binder_tag one_nata
               then SOME (Code_Source_Legal_Applied oip_binder_value)
               else (if equal_nata oip_binder_tag
                          (nat_of_integer (2 : IntInf.int))
                      then let
                             val oip_binder_refusals =
                               [Invalid_Legal_Authority, Invalid_Legal_State,
                                 Invalid_Legal_Binding, Missing_Prior_Freeze,
                                 Missing_Prior_Seizure, Appeal_Still_Open,
                                 Appeal_Deadline_Mismatch,
                                 Missing_Confiscation_Destination,
                                 Conflicting_Legal_Order];
                           in
                             (if less_nat oip_binder_value
                                   (size_list oip_binder_refusals)
                               then SOME (Code_Source_Legal_Blocked
   (nth oip_binder_refusals oip_binder_value))
                               else (if equal_nata oip_binder_value
  (nat_of_integer (9 : IntInf.int))
                                      then SOME Code_Source_Legal_Busy
                                      else (if equal_nata oip_binder_value
         (nat_of_integer (10 : IntInf.int))
     then SOME Code_Source_Legal_Unavailable else NONE)))
                           end
                      else NONE)))
    | _ :: _ :: _ :: _ => NONE);

fun code_rbound_receipt oip_binder_values =
  (case oip_binder_values of [] => NONE
    | oip_binder_tag :: oip_binder_rest =>
      (if equal_nata oip_binder_tag zero_nata
        then map_option
               (fn oip_binder_reply =>
                 (NONE, Code_Source_Ordinary_Receipt oip_binder_reply))
               (code_rbound_collection oip_binder_rest)
        else (if equal_nata oip_binder_tag one_nata
               then map_option
                      (fn oip_binder_reply =>
                        (NONE, Code_Source_Legal_Receipt oip_binder_reply))
                      (code_rbound_legal oip_binder_rest)
               else (if equal_nata oip_binder_tag
                          (nat_of_integer (2 : IntInf.int))
                      then map_option
                             (fn (oip_binder_root, oip_binder_reply) =>
                               (oip_binder_root,
                                 Code_Source_Spend_Receipt oip_binder_reply))
                             (code_rbound_spend oip_binder_rest)
                      else NONE))));

fun code_rbound_resolution oip_binder_values =
  (case oip_binder_values of [] => NONE
    | oip_binder_tag :: oip_binder_rest =>
      (if equal_nata oip_binder_tag zero_nata andalso null oip_binder_rest
        then SOME Code_Source_Resolution_Rejected
        else (if equal_nata oip_binder_tag
                   (nat_of_integer (2 : IntInf.int)) andalso
                   null oip_binder_rest
               then SOME Code_Source_Resolution_Unresolved
               else (if equal_nata oip_binder_tag one_nata
                      then map_option
                             (fn (_, a) => Code_Source_Resolution_Published a)
                             (code_rbound_receipt oip_binder_rest)
                      else NONE))));

fun code_rbound_action oip_binder_values =
  (case oip_binder_values of [] => NONE
    | oip_binder_tag :: oip_binder_rest =>
      (if equal_nata oip_binder_tag zero_nata
        then (case oip_binder_rest of [] => NONE
               | oip_binder_checked :: oip_binder_tail =>
                 (if equal_nata oip_binder_checked zero_nata
                   then map_option
                          (fn oip_binder_collection =>
                            (NONE,
                              (case oip_binder_collection
                                of Code_Source_Collected a =>
                                  Code_Source_Ordinary_Collected a
                                | Code_Source_Collection_Waiting =>
                                  Code_Source_Ordinary_Waiting
                                | Code_Source_Collection_Rejected =>
                                  Code_Source_Ordinary_Rejected)))
                          (code_rbound_collection oip_binder_tail)
                   else (if not (null oip_binder_tail) then NONE
                          else (if equal_nata oip_binder_checked one_nata
                                 then SOME (NONE, Code_Source_Ordinary_Busy)
                                 else (if equal_nata oip_binder_checked
    (nat_of_integer (2 : IntInf.int))
then SOME (NONE, Code_Source_Ordinary_Unavailable)
else (if equal_nata oip_binder_checked (nat_of_integer (3 : IntInf.int))
       then SOME (NONE, Code_Source_Ordinary_Rejected) else NONE))))))
        else (if equal_nata oip_binder_tag one_nata
               then map_option
                      (fn oip_binder_reply =>
                        (NONE, Code_Source_Legal_Action oip_binder_reply))
                      (code_rbound_legal oip_binder_rest)
               else (if equal_nata oip_binder_tag
                          (nat_of_integer (2 : IntInf.int))
                      then map_option
                             (fn (oip_binder_root, oip_binder_reply) =>
                               (oip_binder_root,
                                 Code_Source_Spend_Action oip_binder_reply))
                             (code_rbound_spend oip_binder_rest)
                      else (if equal_nata oip_binder_tag
                                 (nat_of_integer (3 : IntInf.int)) andalso
                                 null oip_binder_rest
                             then SOME (NONE, Code_Source_Other_Action)
                             else NONE)))));

fun code_rbound_error oip_binder_values =
  (case oip_binder_values of [] => NONE
    | [oip_binder_tag] =>
      let
        val oip_binder_variants =
          [Code_Source_Wire_Validation Invalid_Wire_Format,
            Code_Source_Wire_Validation Unsupported_Wire_Version,
            Code_Source_Wire_Validation Invalid_Wire_Source,
            Code_Source_Wire_Validation Invalid_Wire_Signature,
            Code_Source_Wire_Validation Invalid_Wire_Threshold,
            Code_Source_Wire_Validation Wire_TTL_Expired,
            Code_Source_Wire_Validation Wire_TTL_Invalid,
            Code_Source_Wire_Validation Conflicting_Wire_Replay,
            Code_Source_Wire_Product_Rejected, Code_Source_Wire_Cancelled,
            Code_Source_Wire_Deadline, Code_Source_Wire_Response_Lost,
            Code_Source_Wire_Unresolved,
            Code_Source_Wire_Recovery Code_Source_Recovery_Endpoint_Rejected,
            Code_Source_Wire_Recovery Code_Source_Recovery_Endpoint_Unavailable,
            Code_Source_Wire_Recovery Code_Source_Recovery_Hold];
      in
        (if less_nat oip_binder_tag (size_list oip_binder_variants)
          then SOME (nth oip_binder_variants oip_binder_tag) else NONE)
      end
    | _ :: _ :: _ => NONE);

fun code_rbound_observation oip_binder_mode oip_binder_values
  oip_binder_retained_present oip_binder_retained =
  (if equal_nata oip_binder_mode zero_nata
    then bind (code_rbound_action oip_binder_values)
           (fn (oip_binder_root, oip_binder_reply) =>
             (if not oip_binder_retained_present
               then (if null oip_binder_retained
                      then SOME (Response_Fixed_Received
                                  (oip_binder_reply, NONE))
                      else NONE)
               else bind (code_rbound_receipt oip_binder_retained)
                      (fn (oip_binder_stored_root, oip_binder_receipt) =>
                        let
                          val oip_binder_full_root_matches =
                            (case oip_binder_reply
                              of Code_Source_Ordinary_Collected _ => true
                              | Code_Source_Ordinary_Waiting => true
                              | Code_Source_Ordinary_Busy => true
                              | Code_Source_Ordinary_Unavailable => true
                              | Code_Source_Ordinary_Rejected => true
                              | Code_Source_Legal_Action _ => true
                              | Code_Source_Spend_Action
                                  (Code_Source_Spend_Executed _)
                                => equal_optiona
                                     (equal_prod equal_nat equal_nat)
                                     oip_binder_root oip_binder_stored_root
                              | Code_Source_Spend_Action
                                  Code_Source_Spend_Rejected
                                => true
                              | Code_Source_Spend_Action Code_Source_Spend_Busy
                                => true
                              | Code_Source_Spend_Action
                                  Code_Source_Spend_Unavailable
                                => true
                              | Code_Source_Other_Action => true);
                        in
                          SOME (Response_Fixed_Received
                                 (oip_binder_reply,
                                   (if oip_binder_full_root_matches
                                     then SOME oip_binder_receipt else NONE)))
                        end)))
    else (if oip_binder_retained_present orelse not (null oip_binder_retained)
           then NONE
           else (if equal_nata oip_binder_mode one_nata
                  then map_option Response_Fixed_Resolved
                         (code_rbound_resolution oip_binder_values)
                  else (if equal_nata oip_binder_mode
                             (nat_of_integer (2 : IntInf.int))
                         then map_option Response_Fixed_Error
                                (code_rbound_error oip_binder_values)
                         else NONE))));

fun response_v061_decode_sync row =
  (case row of [] => NONE | [_] => NONE
    | [tag, branch] =>
      (if not (equal_nata tag (nat_of_integer (3 : IntInf.int))) then NONE
        else (if equal_nata branch one_nata
               then SOME (Sync_Uncommitted Sync_Busy)
               else (if equal_nata branch (nat_of_integer (2 : IntInf.int))
                      then SOME (Sync_Uncommitted Sync_Unavailable)
                      else (if equal_nata branch
                                 (nat_of_integer (3 : IntInf.int))
                             then SOME (Sync_Uncommitted Sync_Mismatch)
                             else (if equal_nata branch
(nat_of_integer (4 : IntInf.int))
                                    then SOME (Sync_Uncommitted Sync_Stale)
                                    else (if equal_nata branch
       (nat_of_integer (5 : IntInf.int))
   then SOME (Sync_Uncommitted Sync_Proof_Rejected) else NONE))))))
    | [tag, branch, position] =>
      (if equal_nata tag (nat_of_integer (3 : IntInf.int)) andalso
            equal_nata branch zero_nata
        then SOME (Sync_Committed position) else NONE)
    | _ :: _ :: _ :: _ :: _ => NONE);

fun response_v061_decode_observation mode reply v061_present retained =
  (if equal_nata mode zero_nata andalso
        (not (null reply) andalso
          (equal_nata (hd reply) (nat_of_integer (3 : IntInf.int)) andalso
            not (equal_lista equal_nat reply
                  [nat_of_integer (3 : IntInf.int)])))
    then bind (response_v061_decode_sync reply)
           (fn observed =>
             (if not v061_present
               then (if null retained
                      then SOME (Response_V061_Sync (observed, NONE)) else NONE)
               else (case response_v061_decode_sync retained
                      of NONE =>
                        map_option (fn _ => Response_V061_Sync (observed, NONE))
                          (code_rbound_receipt retained)
                      | SOME saved =>
                        SOME (Response_V061_Sync (observed, SOME saved)))))
    else (if equal_nata mode zero_nata andalso
               (v061_present andalso
                 (not (null retained) andalso
                   equal_nata (hd retained) (nat_of_integer (3 : IntInf.int))))
           then bind (response_v061_decode_sync retained)
                  (fn _ =>
                    map_option Response_V061_Legacy
                      (code_rbound_observation mode reply false []))
           else (if equal_nata mode one_nata andalso
                      (equal_lista equal_nat
                         (take (nat_of_integer (2 : IntInf.int)) reply)
                         [one_nata, nat_of_integer (3 : IntInf.int)] andalso
                        (not v061_present andalso null retained))
                  then map_option
                         (fn _ =>
                           Response_V061_Legacy
                             (Response_Fixed_Resolved
                               Code_Source_Resolution_Unresolved))
                         (response_v061_decode_sync (tl reply))
                  else map_option Response_V061_Legacy
                         (code_rbound_observation mode reply v061_present
                           retained))));

fun response_v061_sender_input rows mode reply v061_present retained raw
  hash_rows sign_rows verify_rows =
  (if less_nat (size_list rows) (nat_of_integer (14 : IntInf.int)) orelse
        (not (equal_nata
               (size_list (nth rows (nat_of_integer (6 : IntInf.int))))
               (nat_of_integer (9 : IntInf.int))) orelse
          (not (member equal_integer
                 (nth (nth rows (nat_of_integer (6 : IntInf.int)))
                   (nat_of_integer (7 : IntInf.int)))
                 (insert equal_integer (0 : IntInf.int)
                   (insert equal_integer (1 : IntInf.int) bot_set))) orelse
            (not (member equal_integer
                   (nth (nth rows (nat_of_integer (6 : IntInf.int)))
                     (nat_of_integer (8 : IntInf.int)))
                   (insert equal_integer (0 : IntInf.int)
                     (insert equal_integer (1 : IntInf.int) bot_set))) orelse
              (not (code_integer_u64_values (mode :: reply @ retained)) orelse
                not (code_integer_octet_values raw)))))
    then NONE
    else bind (code_full_context_from_integer
                (list_update rows (nat_of_integer (6 : IntInf.int))
                  (take (nat_of_integer (7 : IntInf.int))
                    (nth rows (nat_of_integer (6 : IntInf.int))))))
           (fn context =>
             bind (if ((mode : IntInf.int) = (3 : IntInf.int))
                    then (if null reply andalso
                               (not v061_present andalso null retained)
                           then SOME NONE else NONE)
                    else map_option SOME
                           (response_v061_decode_observation
                             (nat_of_integer mode) (map nat_of_integer reply)
                             v061_present (map nat_of_integer retained)))
               (fn observed =>
                 map_option
                   (fn (hashes, (signatures, verifications)) =>
                     (context,
                       ((((nth (nth rows (nat_of_integer (6 : IntInf.int)))
                            (nat_of_integer
                              (7 : IntInf.int))) : IntInf.int) = (1 : IntInf.int)),
                         ((((nth (nth rows (nat_of_integer (6 : IntInf.int)))
                              (nat_of_integer
                                (8 : IntInf.int))) : IntInf.int) = (1 : IntInf.int)),
                           (code_response_list_atomicity
                              (map nat_of_integer
                                (nth rows (nat_of_integer (2 : IntInf.int)))),
                             (observed,
                               (map nat_of_integer raw,
                                 (hashes, (signatures, verifications)))))))))
                   (code_full_tables_from_integer hash_rows sign_rows
                     verify_rows))));

fun code_full_lookup_verify x =
  (fn oip_full_table => fn oip_full_key => fn oip_full_message =>
    fn oip_full_signature =>
    map_option (fn (_, (_, (_, oip_full_answer))) => oip_full_answer)
      (find (fn (oip_full_record_key,
                  (oip_full_record_message, (oip_full_record_signature, _)))
               =>
              equal_lista equal_nat oip_full_record_key oip_full_key andalso
                (equal_lista equal_nat oip_full_record_message
                   oip_full_message andalso
                  equal_lista equal_nat oip_full_record_signature
                    oip_full_signature))
        oip_full_table))
    x;

fun code_full_verify x =
  (fn oip_full_table => fn oip_full_key => fn oip_full_message =>
    fn oip_full_signature =>
    (case code_full_lookup_verify oip_full_table oip_full_key oip_full_message
            oip_full_signature
      of NONE =>
        (raise Fail "OIP_PRIMITIVE_MISSING_ED25519_VERIFY") (fn _ => false)
      | SOME oip_full_answer => oip_full_answer))
    x;

fun code_full_kind_number x =
  (fn a =>
    (case a of Recorded_Result => one_nata
      | Delivery_Refusal => nat_of_integer (2 : IntInf.int)
      | Validation_Refusal => nat_of_integer (3 : IntInf.int)))
    x;

fun code_full_result_row x =
  (fn (oip_full_call, (oip_full_kind, (oip_full_number, oip_full_position))) =>
    [fst oip_full_call, snd oip_full_call, code_full_kind_number oip_full_kind,
      oip_full_number,
      (if is_none oip_full_position then zero_nata else one_nata),
      (case oip_full_position of NONE => zero_nata
        | SOME oip_full_optional_position => oip_full_optional_position)])
    x;

fun code_response_packet_length count original_length =
  let
    val core = code_response_core_length count original_length;
  in
    plus_nata
      (plus_nata (nat_of_integer (67 : IntInf.int))
        (size_list (put_wire_varint core)))
      core
  end;

fun code_full_query_blob x =
  (fn oip_full_bytes => size_list oip_full_bytes :: oip_full_bytes) x;

fun code_full_verify_query x =
  (fn oip_full_key => fn oip_full_message => fn oip_full_signature =>
    nat_of_integer (2 : IntInf.int) ::
      code_full_query_blob oip_full_key @
        code_full_query_blob oip_full_message @
          code_full_query_blob oip_full_signature)
    x;

fun code_full_need_verify x =
  (fn oip_full_table => fn oip_full_key => fn oip_full_message =>
    fn oip_full_signature =>
    (if is_none
          (code_full_lookup_verify oip_full_table oip_full_key oip_full_message
            oip_full_signature)
      then [code_full_verify_query oip_full_key oip_full_message
              oip_full_signature]
      else []))
    x;

fun response_v061_missing_original_verification context raw verifications =
  (case sync_decode_packet raw of NONE => []
    | SOME packet =>
      let
        val channel = full_response_channel context;
        val core = packet_core packet;
      in
        (if equal_nata (wire_signature_scheme core)
              (nat_of_integer (2 : IntInf.int)) orelse
              not (member equal_nat (wire_signature_scheme core)
                    (negotiated_schemes (response_channel_profile channel)))
          then []
          else code_full_need_verify verifications
                 (response_channel_remote_key channel)
                 (envelope_signing_bytes core) (packet_signature packet))
      end);

fun code_full_probe_verify x =
  (fn oip_full_table => fn oip_full_key => fn oip_full_message =>
    fn oip_full_signature =>
    (case code_full_lookup_verify oip_full_table oip_full_key oip_full_message
            oip_full_signature
      of NONE => false | SOME oip_full_probe_answer => oip_full_probe_answer))
    x;

fun response_site_security_ordered_profile
  (Response_fixed_site_ext
    (response_site_profile, response_site_ordered_control,
      response_site_security_ordered_profile, more))
  = response_site_security_ordered_profile;

fun response_site_ordered_control
  (Response_fixed_site_ext
    (response_site_profile, response_site_ordered_control,
      response_site_security_ordered_profile, more))
  = response_site_ordered_control;

fun full_response_site
  (Code_response_full_context_ext
    (full_response_config, full_response_channel, full_response_site,
      full_parameters_clock, full_signing_clock, full_response_frame_limit,
      more))
  = full_response_site;

fun response_site_profile
  (Response_fixed_site_ext
    (response_site_profile, response_site_ordered_control,
      response_site_security_ordered_profile, more))
  = response_site_profile;

fun code_original_signature_refusal profile verify_peer packet =
  let
    val core = packet_core packet;
  in
    (if equal_nata (wire_signature_scheme core)
          (nat_of_integer (2 : IntInf.int))
      then SOME Invalid_Wire_Threshold
      else (if not (member equal_nat (wire_signature_scheme core)
                     (negotiated_schemes profile)) orelse
                 not (verify_peer core (envelope_signing_bytes core)
                       (packet_signature packet))
             then SOME Invalid_Wire_Signature else NONE))
  end;

fun response_fixed_original_signature curve_verify channel original =
  code_original_signature_refusal (response_channel_profile channel)
    (fn _ => curve_verify (response_channel_remote_key channel)) original;

fun response_v061_original_caller core =
  (case response_v061_operand one_nata core of Inl a => Inl a
    | Inr a => response_v061_caller a);

fun code_response_measurement selected_atomicity original_length =
  (case selected_atomicity of NONE => Inl Unsupported_Wire_Version
    | SOME mode =>
      (if not (member equal_nat mode
                (atLeastAtMost (equal_nat, interval_nat) one_nata
                  (nat_of_integer (3 : IntInf.int)))) orelse
            less_eq_nat
              (power power_nat (nat_of_integer (2 : IntInf.int))
                (nat_of_integer (32 : IntInf.int)))
              (code_response_core_length (nat_of_integer (6 : IntInf.int))
                original_length)
        then Inl Invalid_Wire_Format
        else Inr (code_response_packet_length (nat_of_integer (6 : IntInf.int))
                   original_length)));

fun response_v061_original_preflight context accept_sync accept_current
  selected_mode verify raw =
  let
    val channel = full_response_channel context;
    val profile = response_channel_profile channel;
    val config = full_response_config context;
    val site = full_response_site context;
    val frame_limit = full_response_frame_limit context;
  in
    (if not (equal_nata (negotiated_version profile)
              (nat_of_integer (6 : IntInf.int))) orelse
          not (code_profile_allows profile Wire_Ack
                (nat_of_integer (2 : IntInf.int)))
      then Inl Unsupported_Wire_Version
      else (if is_none (response_site_ordered_control site) orelse
                 (not (equal_optiona
                        (equal_prod equal_nat (equal_prod equal_nat equal_nat))
                        (response_site_security_ordered_profile site)
                        (SOME (response_site_profile site))) orelse
                   (not (response_fixed_channel_current config channel) orelse
                     not (equal_nata (response_channel_deployment channel)
                           (fst (response_site_profile site)))))
             then Inl Invalid_Wire_Source
             else (case code_check_declared_version raw frame_limit
                    of NONE =>
                      (case sync_decode_packet raw
                        of NONE => Inl Invalid_Wire_Format
                        | SOME packet =>
                          let
                            val core = packet_core packet;
                          in
                            (if not (is_none
                                      (code_check_operation
(response_v061_accepts accept_sync accept_current) core))
                              then Inl Unsupported_Wire_Version
                              else (if not
 (equal_nata (wire_version core) (negotiated_version profile)) orelse
 (not (equal_nata (wire_deployment core)
        (response_channel_deployment channel)) orelse
   (not (equal_nata (wire_source_domain core)
          (response_channel_remote channel)) orelse
     not (equal_nata (wire_target_domain core)
           (response_channel_local channel))))
                                     then Inl Invalid_Wire_Source
                                     else (case
    response_v061_original_caller core of Inl a => Inl a
    | Inr call =>
      (case code_response_measurement selected_mode
              (size_list (encode_wire_core core))
        of Inl a => Inl a
        | Inr measured =>
          (if less_nat frame_limit measured then Inl Invalid_Wire_Format
            else (case response_fixed_original_signature verify channel packet
                   of NONE => Inr (packet, call) | SOME a => Inl a))))))
                          end)
                    | SOME a => Inl a)))
  end;

fun response_v061_packet_caller raw =
  (case sync_decode_packet raw of NONE => Inl Invalid_Wire_Format
    | SOME packet =>
      map_sum id (fn a => (packet, a))
        (response_v061_original_caller (packet_core packet)));

fun response_v061_selected_original include_original context accept_sync
  accept_current selected_mode verify raw =
  (if include_original
    then response_v061_original_preflight context accept_sync accept_current
           selected_mode verify raw
    else response_v061_packet_caller raw);

fun response_v061_original_plan include_original context accept_sync
  accept_current selected_mode raw verifications =
  let
    val selected =
      response_v061_selected_original include_original context accept_sync
        accept_current selected_mode (code_full_probe_verify verifications) raw;
  in
    (selected,
      (if include_original andalso
            equal_sum equal_wire_refusal
              (equal_prod (equal_wire_packet_ext equal_unit)
                (equal_prod equal_nat equal_nat))
              selected (Inl Invalid_Wire_Signature)
        then response_v061_missing_original_verification context raw
               verifications
        else []))
  end;

fun code_full_hash_query x =
  (fn oip_full_message => zero_nata :: code_full_query_blob oip_full_message) x;

fun code_full_sign_query x =
  (fn oip_full_key => fn oip_full_message =>
    one_nata ::
      code_full_query_blob oip_full_key @ code_full_query_blob oip_full_message)
    x;

fun response_v061_plan_after_uuid context original atomicity words binding
  hashes signatures verifications rows =
  let
    val config = full_response_config context;
    val channel = full_response_channel context;
  in
    (case response_fixed_parameters_from (code_full_hash hashes) config channel
            (full_parameters_clock context) binding
      of NONE => ([], rows)
      | SOME parameters =>
        let
          val with_parameters =
            list_update
              (list_update rows (nat_of_integer (8 : IntInf.int))
                (response_parameter_uuid parameters))
              (nat_of_integer (9 : IntInf.int))
              [response_parameter_principal parameters,
                response_parameter_key parameters,
                response_parameter_epoch parameters,
                response_parameter_issued parameters,
                response_parameter_ttl parameters,
                response_parameter_route parameters];
          val core =
            response_fixed_core channel parameters atomicity words original;
        in
          (if less_nat (response_channel_expires channel)
                (response_parameter_issued parameters)
            then ([], with_parameters)
            else (case code_typed_encode_core core
                   of NONE => ([], with_parameters)
                   | SOME core_bytes =>
                     (if less_eq_nat
                           (power power_nat (nat_of_integer (2 : IntInf.int))
                             (nat_of_integer (32 : IntInf.int)))
                           (size_list core_bytes)
                       then ([], with_parameters)
                       else let
                              val preimage = envelope_signing_bytes core;
                              val allowed =
                                response_v061_sign_guard context preimage;
                              val attempted =
                                list_update
                                  (list_update
                                    (list_update with_parameters
                                      (nat_of_integer (10 : IntInf.int))
                                      core_bytes)
                                    (nat_of_integer (11 : IntInf.int)) preimage)
                                  (nat_of_integer (12 : IntInf.int))
                                  [(if allowed then one_nata else zero_nata)];
                              val v061_key = response_channel_local_key channel;
                            in
                              (if not allowed then ([], attempted)
                                else (case code_full_lookup_sign signatures
     v061_key preimage
                                       of NONE =>
 ([code_full_sign_query v061_key preimage], attempted)
                                       | SOME signaturea =>
 (code_full_need_verify verifications v061_key preimage signaturea,
   list_update attempted (nat_of_integer (13 : IntInf.int)) signaturea)))
                            end)))
        end)
  end;

fun response_v061_plan_after_binding context original atomicity words binding
  hashes signatures verifications rows =
  let
    val config = full_response_config context;
    val channel = full_response_channel context;
  in
    (if not (response_fixed_channel_current config channel) then ([], rows)
      else (case full_parameters_clock context of NONE => ([], rows)
             | SOME issued =>
               let
                 val uuid_message =
                   response_fixed_uuid_preimage config binding issued;
                 val with_uuid_message =
                   list_update rows (nat_of_integer (6 : IntInf.int))
                     uuid_message;
               in
                 (case code_full_lookup_hash hashes uuid_message
                   of NONE =>
                     ([code_full_hash_query uuid_message], with_uuid_message)
                   | SOME digest =>
                     response_v061_plan_after_uuid context original atomicity
                       words binding hashes signatures verifications
                       (list_update with_uuid_message
                         (nat_of_integer (7 : IntInf.int)) digest))
               end))
  end;

fun response_v061_plan_selected context selected_mode packet call result hashes
  signatures verifications =
  let
    val exact = encode_wire_core (packet_core packet);
    val (number, position) = result;
    val offset =
      (case position of NONE => zero_nata | SOME revision => revision);
    val base =
      list_update
        (list_update (replicate (nat_of_integer (14 : IntInf.int)) []) zero_nata
          [number, (if is_none position then zero_nata else one_nata), offset])
        (nat_of_integer (3 : IntInf.int)) exact;
  in
    (case response_v061_words call result of NONE => ([], base)
      | SOME (_, (_, (_, words))) =>
        let
          val with_words = list_update base one_nata words;
        in
          (case selected_mode of NONE => ([], with_words)
            | SOME atomicity =>
              let
                val binding_message =
                  response_fixed_binding_preimage exact atomicity words;
                val with_binding =
                  list_update
                    (list_update with_words (nat_of_integer (2 : IntInf.int))
                      [atomicity])
                    (nat_of_integer (4 : IntInf.int)) binding_message;
              in
                (case code_full_lookup_hash hashes binding_message
                  of NONE =>
                    ([code_full_hash_query binding_message], with_binding)
                  | SOME binding =>
                    response_v061_plan_after_binding context exact atomicity
                      words binding hashes signatures verifications
                      (list_update with_binding
                        (nat_of_integer (5 : IntInf.int)) binding))
              end)
        end)
  end;

fun code_full_pack_client x =
  (fn a =>
    (case a
      of Inl oip_full_reason =>
        (integer_of_nat (code_transport_refusal_number oip_full_reason), [])
      | Inr (_, NONE) => ((~1 : IntInf.int), [])
      | Inr (oip_full_selected,
              SOME (Code_Known_Response (oip_full_kind, oip_full_number)))
        => ((0 : IntInf.int),
             map integer_of_nat
               (code_full_result_row oip_full_selected @
                 [one_nata, code_full_kind_number oip_full_kind,
                   oip_full_number]))
      | Inr (oip_full_selected,
              SOME (Code_Unknown_Response (oip_full_kind, oip_full_number)))
        => ((0 : IntInf.int),
             map integer_of_nat
               (code_full_result_row oip_full_selected @
                 [zero_nata, code_full_kind_number oip_full_kind,
                   oip_full_number]))))
    x;

fun response_emission_signing_preimage
  (Response_fixed_emission_ext
    (response_emission_bytes, response_emission_packet,
      response_emission_original, response_emission_converted,
      response_emission_verified, response_emission_parameters,
      response_emission_binding_preimage, response_emission_signing_preimage,
      more))
  = response_emission_signing_preimage;

fun response_emission_binding_preimage
  (Response_fixed_emission_ext
    (response_emission_bytes, response_emission_packet,
      response_emission_original, response_emission_converted,
      response_emission_verified, response_emission_parameters,
      response_emission_binding_preimage, response_emission_signing_preimage,
      more))
  = response_emission_binding_preimage;

fun response_emission_parameters
  (Response_fixed_emission_ext
    (response_emission_bytes, response_emission_packet,
      response_emission_original, response_emission_converted,
      response_emission_verified, response_emission_parameters,
      response_emission_binding_preimage, response_emission_signing_preimage,
      more))
  = response_emission_parameters;

fun response_emission_converted
  (Response_fixed_emission_ext
    (response_emission_bytes, response_emission_packet,
      response_emission_original, response_emission_converted,
      response_emission_verified, response_emission_parameters,
      response_emission_binding_preimage, response_emission_signing_preimage,
      more))
  = response_emission_converted;

fun response_emission_verified
  (Response_fixed_emission_ext
    (response_emission_bytes, response_emission_packet,
      response_emission_original, response_emission_converted,
      response_emission_verified, response_emission_parameters,
      response_emission_binding_preimage, response_emission_signing_preimage,
      more))
  = response_emission_verified;

fun response_emission_original
  (Response_fixed_emission_ext
    (response_emission_bytes, response_emission_packet,
      response_emission_original, response_emission_converted,
      response_emission_verified, response_emission_parameters,
      response_emission_binding_preimage, response_emission_signing_preimage,
      more))
  = response_emission_original;

fun response_emission_packet
  (Response_fixed_emission_ext
    (response_emission_bytes, response_emission_packet,
      response_emission_original, response_emission_converted,
      response_emission_verified, response_emission_parameters,
      response_emission_binding_preimage, response_emission_signing_preimage,
      more))
  = response_emission_packet;

fun response_emission_bytes
  (Response_fixed_emission_ext
    (response_emission_bytes, response_emission_packet,
      response_emission_original, response_emission_converted,
      response_emission_verified, response_emission_parameters,
      response_emission_binding_preimage, response_emission_signing_preimage,
      more))
  = response_emission_bytes;

fun code_full_emission_rows x =
  (fn oip_full_context => fn oip_full_hashes => fn oip_full_emission =>
    let
      val oip_full_parameters = response_emission_parameters oip_full_emission;
      val oip_full_packet = response_emission_packet oip_full_emission;
      val oip_full_binding_message =
        response_emission_binding_preimage oip_full_emission;
      val oip_full_binding =
        code_full_hash oip_full_hashes oip_full_binding_message;
      val oip_full_uuid_message =
        response_fixed_uuid_preimage (full_response_config oip_full_context)
          oip_full_binding (response_parameter_issued oip_full_parameters);
    in
      [code_full_result_row (response_emission_converted oip_full_emission),
        code_full_result_row (response_emission_verified oip_full_emission),
        wire_words (wire_operation_body (packet_core oip_full_packet)),
        encode_wire_core (response_emission_original oip_full_emission),
        oip_full_binding_message, oip_full_binding, oip_full_uuid_message,
        code_full_hash oip_full_hashes oip_full_uuid_message,
        response_parameter_uuid oip_full_parameters,
        encode_wire_core (packet_core oip_full_packet),
        response_emission_signing_preimage oip_full_emission,
        packet_signature oip_full_packet,
        response_emission_bytes oip_full_emission,
        [response_parameter_principal oip_full_parameters,
          response_parameter_key oip_full_parameters,
          response_parameter_epoch oip_full_parameters,
          response_parameter_issued oip_full_parameters,
          response_parameter_ttl oip_full_parameters,
          response_parameter_route oip_full_parameters],
        code_full_clock_row oip_full_context]
    end)
    x;

fun code_full_pack_sender x =
  (fn oip_full_context => fn oip_full_hashes => fn a =>
    (case a
      of Inl (Response_Fixed_Encoding_Refused oip_full_reason) =>
        (integer_of_nat (code_transport_refusal_number oip_full_reason), [])
      | Inl Response_Fixed_Signature_Unavailable => ((51 : IntInf.int), [])
      | Inr oip_full_emission =>
        ((0 : IntInf.int),
          map (map integer_of_nat)
            (code_full_emission_rows oip_full_context oip_full_hashes
              oip_full_emission))))
    x;

fun response_v061_client_queries channel current expected raw verifications =
  (if not (equal_sum equal_wire_refusal
            (equal_prod
              (equal_prod (equal_prod equal_nat equal_nat)
                (equal_prod equal_reference_response_kind
                  (equal_prod equal_nat (equal_option equal_nat))))
              (equal_option equal_code_response_status))
            (response_v061_admit (code_full_probe_verify verifications) channel
              current expected raw)
            (Inl Invalid_Wire_Signature))
    then []
    else (case sync_decode_packet raw of NONE => []
           | SOME packet =>
             let
               val core = packet_core packet;
             in
               (if equal_nata (wire_signature_scheme core)
                     (nat_of_integer (2 : IntInf.int)) orelse
                     not (member equal_nat (wire_signature_scheme core)
                           (negotiated_schemes
                             (response_channel_profile channel)))
                 then []
                 else code_full_need_verify verifications
                        (response_client_public_key current)
                        (envelope_signing_bytes core) (packet_signature packet))
             end));

fun response_v061_execute_sender v061_stage include_original context accept_sync
  accept_current selected_mode observed raw hashes signatures verifications =
  (if is_none observed andalso not include_original then ((~1 : IntInf.int), [])
    else (case response_v061_original_plan include_original context accept_sync
                 accept_current selected_mode raw verifications
           of (Inl _, original_queries) =>
             (case v061_stage
               of Response_V061_Plan => response_v061_pack_rows original_queries
               | Response_V061_Prefix =>
                 (if null original_queries then ((0 : IntInf.int), [])
                   else ((~2 : IntInf.int), []))
               | Response_V061_Emit =>
                 (if not (null original_queries) then ((~2 : IntInf.int), [])
                   else (case response_v061_selected_original include_original
                                context accept_sync accept_current selected_mode
                                (code_full_verify verifications) raw
                          of Inl strict_reason =>
                            (integer_of_nat
                               (code_transport_refusal_number strict_reason),
                              [])
                          | Inr _ => ((~1 : IntInf.int), []))))
           | (Inr (packet, call), _) =>
             (case observed of NONE => ((~1 : IntInf.int), [])
               | SOME observation =>
                 let
                   val result = response_v061_result observation;
                   val (queries, prefix) =
                     response_v061_plan_selected context selected_mode packet
                       call result hashes signatures verifications;
                 in
                   (case v061_stage
                     of Response_V061_Plan => response_v061_pack_rows queries
                     | Response_V061_Prefix =>
                       (if null queries then response_v061_pack_rows prefix
                         else ((~2 : IntInf.int), []))
                     | Response_V061_Emit =>
                       (if not (null queries) then ((~2 : IntInf.int), [])
                         else (case response_v061_selected_original
                                      include_original context accept_sync
                                      accept_current selected_mode
                                      (code_full_verify verifications) raw
                                of Inl reason =>
                                  (integer_of_nat
                                     (code_transport_refusal_number reason),
                                    [])
                                | Inr (actual, actual_call) =>
                                  code_full_pack_sender context hashes
                                    (response_v061_encode
                                      (code_full_hash hashes)
                                      (fn v061_key =>
code_full_sign signatures v061_key ())
                                      (code_full_verify verifications) context
                                      selected_mode (packet_core actual)
                                      actual_call result))))
                 end)));

fun response_v061_sender_integer v061_stage include_original rows mode reply
  v061_present retained raw hash_rows sign_rows verify_rows =
  (case response_v061_sender_input rows mode reply v061_present retained raw
          hash_rows sign_rows verify_rows
    of NONE => ((~1 : IntInf.int), [])
    | SOME (context,
             (accept_sync,
               (accept_current,
                 (selected_mode, (observed, (original, (hashes, (a, b))))))))
      => response_v061_execute_sender v061_stage include_original context
           accept_sync accept_current selected_mode observed original hashes a
           b);

fun response_v061_identity_fields fingerprint =
  map (map integer_of_nat o code_json_ascii)
    [[Chara (true, false, false, false, true, true, false, false)],
      [Chara (true, false, false, true, false, true, true, false),
        Chara (false, true, true, true, false, true, true, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (true, false, false, true, false, true, true, false),
        Chara (false, true, true, true, false, true, true, false),
        Chara (false, true, true, false, false, true, true, false),
        Chara (true, false, true, true, false, true, false, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, true, false, false, true, true, true, false),
        Chara (false, false, false, false, true, true, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (false, true, true, true, false, true, true, false),
        Chara (true, true, false, false, true, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, false, true, true, false, true, false, false),
        Chara (false, true, true, false, false, true, true, false),
        Chara (true, false, true, false, true, true, true, false),
        Chara (false, false, true, true, false, true, true, false),
        Chara (false, false, true, true, false, true, true, false),
        Chara (true, false, true, true, false, true, false, false),
        Chara (false, true, true, false, true, true, true, false),
        Chara (false, true, false, false, true, true, false, false)],
      [Chara (true, true, true, false, true, true, true, false),
        Chara (true, false, false, true, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, false, true, true, false, true, false, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, true, false, false, true, true, true, false),
        Chara (false, false, false, false, true, true, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (false, true, true, true, false, true, true, false),
        Chara (true, true, false, false, true, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, false, true, true, false, true, false, false),
        Chara (true, true, false, false, true, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, true, true, true, false, true, true, false),
        Chara (false, false, true, false, false, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, true, true, false, true, false, false),
        Chara (true, true, false, false, false, true, true, false),
        Chara (false, false, true, true, false, true, true, false),
        Chara (true, false, false, true, false, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, true, true, true, false, true, true, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (true, false, true, true, false, true, false, false),
        Chara (false, true, true, false, true, true, true, false),
        Chara (false, true, false, false, true, true, false, false)],
      [Chara (true, true, true, true, false, false, true, false),
        Chara (true, false, false, true, false, false, true, false),
        Chara (false, false, false, false, true, false, true, false),
        Chara (true, true, true, true, true, false, true, false),
        Chara (true, true, true, false, true, false, true, false),
        Chara (true, false, false, true, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, true, true, true, true, false, true, false),
        Chara (false, true, false, false, true, false, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, true, false, false, true, true, true, false),
        Chara (false, false, false, false, true, true, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (false, true, true, true, false, true, true, false),
        Chara (true, true, false, false, true, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, true, true, true, true, false, true, false),
        Chara (false, true, false, false, false, false, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (true, false, true, false, true, true, true, false),
        Chara (false, true, true, true, false, true, true, false),
        Chara (false, false, true, false, false, true, true, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, false, true, true, true, true, false),
        Chara (false, true, true, true, false, true, false, false),
        Chara (true, true, false, false, false, true, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (false, false, true, false, false, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, true, true, true, true, false, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, true, false, false, true, true, true, false),
        Chara (false, false, false, false, true, true, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (false, true, true, true, false, true, true, false),
        Chara (true, true, false, false, true, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, true, true, true, true, false, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, true, true, false, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, true, false, false, true, true, true, false),
        Chara (true, true, false, false, true, true, true, false),
        Chara (true, true, true, true, true, false, true, false),
        Chara (false, true, true, false, false, true, true, false),
        Chara (false, false, true, true, false, true, true, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (true, true, true, true, true, false, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (true, true, false, false, false, true, true, false),
        Chara (false, false, true, true, false, true, true, false),
        Chara (true, false, true, false, false, true, true, false)],
      [Chara (false, false, false, true, false, false, true, false),
        Chara (true, true, true, true, false, false, true, false),
        Chara (false, false, true, true, false, false, true, false),
        Chara (true, false, true, true, false, true, false, false),
        Chara (false, false, true, true, false, false, true, false),
        Chara (true, false, false, true, false, true, true, false),
        Chara (false, true, false, false, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, false, true, true, true, true, false),
        Chara (false, true, true, true, false, true, false, false),
        Chara (true, true, false, false, false, false, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (false, false, true, false, false, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, true, true, true, true, false, true, false),
        Chara (false, false, true, false, true, false, true, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, true, true, false, false, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (true, true, true, true, true, false, true, false),
        Chara (false, true, true, true, false, false, true, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (false, false, true, false, true, true, true, false)],
      fingerprint];

fun code_response_admit_flat_oracle rows expected received verify_rows =
  (case response_v061_client_input rows expected received verify_rows
    of NONE => ((~1 : IntInf.int), [])
    | SOME (channel, (current, (original, (raw, verifications)))) =>
      (if not (null (response_v061_client_queries channel current original raw
                      verifications))
        then ((~2 : IntInf.int), [])
        else code_full_pack_client
               (response_v061_admit (code_full_verify verifications) channel
                 current original raw)));

fun code_response_full_model_identity ignored =
  response_v061_identity_fields
    [Chara (true, false, false, true, true, true, false, false),
      Chara (false, true, true, false, false, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (true, true, true, false, true, true, false, false),
      Chara (false, true, true, false, true, true, false, false),
      Chara (false, true, false, false, true, true, false, false),
      Chara (true, false, false, false, true, true, false, false),
      Chara (true, true, false, false, false, true, true, false),
      Chara (true, false, false, true, true, true, false, false),
      Chara (true, false, false, false, false, true, true, false),
      Chara (true, false, false, false, false, true, true, false),
      Chara (false, false, false, false, true, true, false, false),
      Chara (true, false, false, false, true, true, false, false),
      Chara (true, false, false, false, false, true, true, false),
      Chara (false, false, true, false, true, true, false, false),
      Chara (false, false, false, true, true, true, false, false),
      Chara (true, true, false, false, false, true, true, false),
      Chara (true, false, false, true, true, true, false, false),
      Chara (false, false, false, false, true, true, false, false),
      Chara (true, true, false, false, false, true, true, false),
      Chara (true, false, true, false, false, true, true, false),
      Chara (true, true, false, false, false, true, true, false),
      Chara (false, true, true, false, false, true, true, false),
      Chara (true, false, false, true, true, true, false, false),
      Chara (true, false, false, false, true, true, false, false),
      Chara (false, false, false, true, true, true, false, false),
      Chara (false, true, false, false, true, true, false, false),
      Chara (true, false, false, true, true, true, false, false),
      Chara (false, true, false, false, true, true, false, false),
      Chara (true, false, false, true, true, true, false, false),
      Chara (false, false, false, false, true, true, false, false),
      Chara (false, true, true, false, true, true, false, false),
      Chara (false, false, false, true, true, true, false, false),
      Chara (false, true, false, false, true, true, false, false),
      Chara (false, false, true, false, false, true, true, false),
      Chara (true, true, false, false, false, true, true, false),
      Chara (false, true, true, false, true, true, false, false),
      Chara (true, true, false, false, true, true, false, false),
      Chara (false, false, true, false, false, true, true, false),
      Chara (false, true, false, false, true, true, false, false),
      Chara (false, false, true, false, false, true, true, false),
      Chara (true, true, true, false, true, true, false, false),
      Chara (true, true, true, false, true, true, false, false),
      Chara (true, true, false, false, true, true, false, false),
      Chara (false, false, false, true, true, true, false, false),
      Chara (true, false, true, false, true, true, false, false),
      Chara (true, true, true, false, true, true, false, false),
      Chara (true, false, false, false, true, true, false, false),
      Chara (false, true, false, false, false, true, true, false),
      Chara (false, false, false, true, true, true, false, false),
      Chara (true, true, true, false, true, true, false, false),
      Chara (false, true, false, false, true, true, false, false),
      Chara (true, false, false, false, true, true, false, false),
      Chara (false, false, false, true, true, true, false, false),
      Chara (false, true, true, false, true, true, false, false),
      Chara (false, true, true, false, false, true, true, false),
      Chara (true, true, false, false, true, true, false, false),
      Chara (false, false, false, false, true, true, false, false),
      Chara (true, false, false, false, false, true, true, false),
      Chara (true, false, false, true, true, true, false, false),
      Chara (false, false, false, true, true, true, false, false),
      Chara (true, true, false, false, false, true, true, false),
      Chara (true, false, true, false, true, true, false, false),
      Chara (true, true, false, false, false, true, true, false)];

fun code_response_admit_queries_flat rows expected received verify_rows =
  (case response_v061_client_input rows expected received verify_rows
    of NONE => ((~1 : IntInf.int), [])
    | SOME (channel, (current, (original, (raw, verifications)))) =>
      response_v061_pack_rows
        (response_v061_client_queries channel current original raw
          verifications));

fun code_response_egress_flat_oracle x =
  response_v061_sender_integer Response_V061_Emit true x;

fun code_response_egress_prefix_flat x =
  response_v061_sender_integer Response_V061_Prefix true x;

fun code_response_result_flat_oracle mode reply v061_present retained =
  (if not (code_integer_u64_values (mode :: reply @ retained))
    then (false, ((~1 : IntInf.int), (false, (0 : IntInf.int))))
    else (case response_v061_decode_observation (nat_of_integer mode)
                 (map nat_of_integer reply) v061_present
                 (map nat_of_integer retained)
           of NONE => (false, ((~1 : IntInf.int), (false, (0 : IntInf.int))))
           | SOME observation =>
             let
               val (number, position) = response_v061_result observation;
             in
               (true,
                 (integer_of_nat number,
                   (not (is_none position),
                     integer_of_nat
                       (case position of NONE => zero_nata
                         | SOME revision => revision))))
             end));

fun code_rbound_atomicity oip_binder_numbers =
  (if null oip_binder_numbers then NONE
    else SOME (mina linorder_nat (Set oip_binder_numbers)));

fun code_response_egress_queries_flat x =
  response_v061_sender_integer Response_V061_Plan true x;

fun code_rbound_binding_stage oip_binder_observation oip_binder_original
  oip_binder_numbers =
  (case code_response_caller (packet_core oip_binder_original) of Inl a => Inl a
    | Inr oip_binder_call_id =>
      (case response_fixed_words oip_binder_call_id
              (response_fixed_result oip_binder_observation)
        of NONE => Inl Invalid_Wire_Format
        | SOME (_, (oip_binder_number, (oip_binder_position, oip_binder_words)))
          => (case code_rbound_atomicity oip_binder_numbers
               of NONE => Inl Unsupported_Wire_Version
               | SOME oip_binder_atomicity =>
                 let
                   val oip_binder_core =
                     encode_wire_core (packet_core oip_binder_original);
                 in
                   Inr (oip_binder_number,
                         (oip_binder_position,
                           (oip_binder_atomicity,
                             (oip_binder_words,
                               (oip_binder_core,
                                 response_fixed_binding_preimage oip_binder_core
                                   oip_binder_atomicity oip_binder_words)))))
                 end)));

fun code_rbound_uuid_preimage oip_binder_policy_binding
  oip_binder_response_binding oip_binder_issued =
  [nat_of_integer (111 : IntInf.int), nat_of_integer (105 : IntInf.int),
    nat_of_integer (112 : IntInf.int), nat_of_integer (47 : IntInf.int),
    nat_of_integer (114 : IntInf.int), nat_of_integer (101 : IntInf.int),
    nat_of_integer (102 : IntInf.int), nat_of_integer (101 : IntInf.int),
    nat_of_integer (114 : IntInf.int), nat_of_integer (101 : IntInf.int),
    nat_of_integer (110 : IntInf.int), nat_of_integer (99 : IntInf.int),
    nat_of_integer (101 : IntInf.int), nat_of_integer (45 : IntInf.int),
    nat_of_integer (114 : IntInf.int), nat_of_integer (101 : IntInf.int),
    nat_of_integer (115 : IntInf.int), nat_of_integer (112 : IntInf.int),
    nat_of_integer (111 : IntInf.int), nat_of_integer (110 : IntInf.int),
    nat_of_integer (115 : IntInf.int), nat_of_integer (101 : IntInf.int),
    nat_of_integer (45 : IntInf.int), nat_of_integer (117 : IntInf.int),
    nat_of_integer (117 : IntInf.int), nat_of_integer (105 : IntInf.int),
    nat_of_integer (100 : IntInf.int), nat_of_integer (47 : IntInf.int),
    nat_of_integer (118 : IntInf.int), nat_of_integer (49 : IntInf.int),
    zero_nata] @
    oip_binder_policy_binding @
      oip_binder_response_binding @ response_fixed_be64 oip_binder_issued;

fun code_response_encode_boundary_flat_oracle x =
  response_v061_sender_integer Response_V061_Emit false x;

fun code_response_encode_boundary_prefix_flat x =
  response_v061_sender_integer Response_V061_Prefix false x;

fun code_response_egress_and_admit_flat_oracle rows mode reply v061_present
  retained original hash_rows sign_rows verify_rows client_rows
  client_verify_rows =
  let
    val (status, output) =
      code_response_egress_flat_oracle rows mode reply v061_present retained
        original hash_rows sign_rows verify_rows;
  in
    (if not ((status : IntInf.int) = (0 : IntInf.int))
      then (status, (output, ((~3 : IntInf.int), [])))
      else let
             val (client_status, client_output) =
               code_response_admit_flat_oracle client_rows original
                 (nth output (nat_of_integer (12 : IntInf.int)))
                 client_verify_rows;
           in
             (status, (output, (client_status, client_output)))
           end)
  end;

fun code_response_encode_boundary_queries_flat x =
  response_v061_sender_integer Response_V061_Plan false x;

fun code_response_binding_flat_oracle oip_binder_mode oip_binder_values
  oip_binder_retained_present oip_binder_retained oip_binder_original_bytes
  oip_binder_atomicities =
  (if not (code_integer_u64_values
            (oip_binder_mode ::
              oip_binder_values @
                oip_binder_retained @ oip_binder_atomicities)) orelse
        not (code_integer_octet_values oip_binder_original_bytes)
    then (false,
           ((~1 : IntInf.int),
             ((0 : IntInf.int),
               (false,
                 ((0 : IntInf.int), ((0 : IntInf.int), ([], ([], []))))))))
    else (case code_rbound_observation (nat_of_integer oip_binder_mode)
                 (map nat_of_integer oip_binder_values)
                 oip_binder_retained_present
                 (map nat_of_integer oip_binder_retained)
           of NONE =>
             (false,
               ((~1 : IntInf.int),
                 ((0 : IntInf.int),
                   (false,
                     ((0 : IntInf.int), ((0 : IntInf.int), ([], ([], []))))))))
           | SOME oip_binder_observation =>
             (case decode_wire_packet
                     (map nat_of_integer oip_binder_original_bytes)
               of NONE =>
                 (true,
                   ((70 : IntInf.int),
                     ((0 : IntInf.int),
                       (false,
                         ((0 : IntInf.int),
                           ((0 : IntInf.int), ([], ([], []))))))))
               | SOME oip_binder_original =>
                 (case code_rbound_binding_stage oip_binder_observation
                         oip_binder_original
                         (map nat_of_integer oip_binder_atomicities)
                   of Inl oip_binder_reason =>
                     (true,
                       (integer_of_nat
                          (code_transport_refusal_number oip_binder_reason),
                         ((0 : IntInf.int),
                           (false,
                             ((0 : IntInf.int),
                               ((0 : IntInf.int), ([], ([], []))))))))
                   | Inr (oip_binder_number,
                           (oip_binder_position,
                             (oip_binder_atomicity,
                               (oip_binder_words,
                                 (oip_binder_core, oip_binder_preimage)))))
                     => (true,
                          ((0 : IntInf.int),
                            (integer_of_nat oip_binder_number,
                              (not (is_none oip_binder_position),
                                (integer_of_nat
                                   (case oip_binder_position
                                     of NONE => zero_nata
                                     | SOME oip_option_value =>
                                       oip_option_value),
                                  (integer_of_nat oip_binder_atomicity,
                                    (map integer_of_nat oip_binder_words,
                                      (map integer_of_nat oip_binder_core,
map integer_of_nat oip_binder_preimage))))))))))));

fun code_response_uuid_preimage_flat_oracle oip_binder_policy_binding
  oip_binder_response_binding oip_binder_issued =
  (if not (code_integer_octet_values
            (oip_binder_policy_binding @ oip_binder_response_binding)) orelse
        (not (equal_nata (size_list oip_binder_response_binding)
               (nat_of_integer (32 : IntInf.int))) orelse
          not (code_integer_u64_values [oip_binder_issued]))
    then (false, [])
    else (true,
           map integer_of_nat
             (code_rbound_uuid_preimage
               (map nat_of_integer oip_binder_policy_binding)
               (map nat_of_integer oip_binder_response_binding)
               (nat_of_integer oip_binder_issued))));

end; (*struct OIP_Wire_Response_Boundary*)
