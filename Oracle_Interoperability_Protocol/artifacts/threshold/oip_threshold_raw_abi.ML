structure OIP_Threshold_Raw_ABI : sig
  type nat
  type char
  val threshold_raw_packet :
    IntInf.int ->
      IntInf.int list ->
        IntInf.int list ->
          IntInf.int list ->
            (IntInf.int * IntInf.int list) list ->
              (IntInf.int list * bool) list ->
                (IntInf.int list *
                  (IntInf.int list * (IntInf.int list * bool))) list ->
                  IntInf.int list ->
                    (IntInf.int list * (IntInf.int list) list) option
  val threshold_raw_model_identity : unit -> (IntInf.int list) list
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

fun equal_boola false p = not p
  | equal_boola true p = p
  | equal_boola p false = not p
  | equal_boola p true = p;

val equal_bool = {equal = equal_boola} : bool equal;

fun eq A_ a b = equal A_ a b;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

val one_integera : IntInf.int = (1 : IntInf.int);

val one_integer = {one = one_integera} : IntInf.int one;

val zero_integer = {zero = (0 : IntInf.int)} : IntInf.int zero;

val zero_neq_one_integer =
  {one_zero_neq_one = one_integer, zero_zero_neq_one = zero_integer} :
  IntInf.int zero_neq_one;

datatype 'a set = Set of 'a list | Coset of 'a list;

datatype char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;

datatype wire_family = Wire_State_Sync | Wire_Regulatory | Wire_Lock |
  Wire_Query | Wire_Ack | Wire_Heartbeat | Wire_Governance;

datatype wire_deadline = Deadline_Absent | Deadline_Indefinite |
  Deadline_At of nat;

datatype proto_field = Proto_Varint of nat * nat | Proto_Fixed64 of nat * nat |
  Proto_Bytes of nat * nat list;

datatype wire_refusal = Invalid_Wire_Format | Unsupported_Wire_Version |
  Invalid_Wire_Source | Invalid_Wire_Signature | Invalid_Wire_Threshold |
  Wire_TTL_Expired | Wire_TTL_Invalid | Conflicting_Wire_Replay;

datatype 'a wire_body_ext =
  Wire_body_ext of nat * nat list * (nat list) list * wire_deadline * 'a;

datatype 'a wire_core_ext =
  Wire_core_ext of
    nat * nat * nat * nat * nat * nat * nat * nat * nat * nat * nat list *
      wire_family * nat * nat option * nat * unit wire_body_ext * nat * nat *
      nat * 'a;

datatype 'a wire_packet_ext =
  Wire_packet_ext of unit wire_core_ext * nat list * 'a;

datatype 'a p19_roster_ext =
  P19_roster_ext of
    nat * nat * nat * nat * nat * nat * (nat * nat list) list * 'a;

datatype 'a p19_registry_ext =
  P19_registry_ext of
    (nat * (nat * (nat * nat)) -> nat option) *
      ((nat * (nat * (nat * nat))) * nat -> unit p19_roster_ext option) * 'a;

fun suc n = plus_nata n one_nata;

fun nth (x :: xs) n =
  (if equal_nata n zero_nata then x else nth xs (minus_nata n one_nata));

fun fold f [] s = s
  | fold f (x :: xs) s = fold f xs (f x s);

fun rev xs = fold (fn a => fn b => a :: b) xs [];

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

fun bind NONE f = NONE
  | bind (SOME x) f = f x;

fun distinct A_ [] = true
  | distinct A_ (x :: xs) = not (membera A_ xs x) andalso distinct A_ xs;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun list_all p [] = true
  | list_all p (x :: xs) = p x andalso list_all p xs;

fun sorted_wrt p [] = true
  | sorted_wrt p (x :: ys) = list_all (p x) ys andalso sorted_wrt p ys;

fun apsnd f (x, y) = (x, f y);

fun length_tailrec [] n = n
  | length_tailrec (x :: xs) n = length_tailrec xs (suc n);

fun fst (x1, x2) = x1;

fun snd (x1, x2) = x2;

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

fun modulo_integer k l = snd (divmod_integer k l);

fun modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

fun divide_integer k l = fst (divmod_integer k l);

fun divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

fun put_wire_varint n =
  (if less_nat n (nat_of_integer (128 : IntInf.int)) then [n]
    else plus_nata (nat_of_integer (128 : IntInf.int))
           (modulo_nat n (nat_of_integer (128 : IntInf.int))) ::
           put_wire_varint (divide_nat n (nat_of_integer (128 : IntInf.int))));

fun size_list xs = length_tailrec xs zero_nata;

fun put_le_octets width number =
  (if equal_nata width zero_nata then []
    else modulo_nat number (nat_of_integer (256 : IntInf.int)) ::
           put_le_octets (minus_nata width one_nata)
             (divide_nat number (nat_of_integer (256 : IntInf.int))));

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

fun power A_ a n =
  (if equal_nata n zero_nata then one (one_power A_)
    else times (times_power A_) a (power A_ a (minus_nata n one_nata)));

fun map_option f NONE = NONE
  | map_option f (SOME x2) = SOME (f x2);

val bot_set : 'a set = Set [];

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
        val number = divide_nat tag (nat_of_integer (8 : IntInf.int));
        val kind = modulo_nat tag (nat_of_integer (8 : IntInf.int));
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
       (divide_nat (nth (wire_uuid core) (nat_of_integer (6 : IntInf.int)))
         (nat_of_integer (16 : IntInf.int)))
       (nat_of_integer (4 : IntInf.int)) andalso
      (equal_nata
         (divide_nat (nth (wire_uuid core) (nat_of_integer (8 : IntInf.int)))
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

fun p19_current_epoch
  (P19_registry_ext (p19_current_epoch, p19_catalogue, more)) =
  p19_current_epoch;

fun p19_catalogue (P19_registry_ext (p19_current_epoch, p19_catalogue, more)) =
  p19_catalogue;

fun equal_option A_ NONE (SOME x2) = false
  | equal_option A_ (SOME x2) NONE = false
  | equal_option A_ (SOME x2) (SOME y2) = eq A_ x2 y2
  | equal_option A_ NONE NONE = true;

fun p19_deployment
  (P19_roster_ext
    (p19_deployment, p19_source, p19_principal, p19_group_key, p19_epoch,
      p19_quorum, p19_members, more))
  = p19_deployment;

fun p19_principal
  (P19_roster_ext
    (p19_deployment, p19_source, p19_principal, p19_group_key, p19_epoch,
      p19_quorum, p19_members, more))
  = p19_principal;

fun p19_group_key
  (P19_roster_ext
    (p19_deployment, p19_source, p19_principal, p19_group_key, p19_epoch,
      p19_quorum, p19_members, more))
  = p19_group_key;

fun p19_source
  (P19_roster_ext
    (p19_deployment, p19_source, p19_principal, p19_group_key, p19_epoch,
      p19_quorum, p19_members, more))
  = p19_source;

fun p19_epoch
  (P19_roster_ext
    (p19_deployment, p19_source, p19_principal, p19_group_key, p19_epoch,
      p19_quorum, p19_members, more))
  = p19_epoch;

fun p19_matches_core r c =
  equal_nata (p19_deployment r) (wire_deployment c) andalso
    (equal_nata (p19_source r) (wire_source_domain c) andalso
      (equal_nata (p19_principal r) (wire_principal c) andalso
        (equal_nata (p19_group_key r) (wire_key_number c) andalso
          equal_nata (p19_epoch r) (wire_authority_epoch c))));

fun p19_core_slot c =
  (wire_deployment c,
    (wire_source_domain c, (wire_principal c, wire_key_number c)));

fun p19_select registry c =
  (if equal_option equal_nat (p19_current_epoch registry (p19_core_slot c))
        (SOME (wire_authority_epoch c))
    then (case p19_catalogue registry (p19_core_slot c, wire_authority_epoch c)
           of NONE => NONE
           | SOME r => (if p19_matches_core r c then SOME r else NONE))
    else NONE);

fun p19_members
  (P19_roster_ext
    (p19_deployment, p19_source, p19_principal, p19_group_key, p19_epoch,
      p19_quorum, p19_members, more))
  = p19_members;

fun p19_quorum
  (P19_roster_ext
    (p19_deployment, p19_source, p19_principal, p19_group_key, p19_epoch,
      p19_quorum, p19_members, more))
  = p19_quorum;

fun p19_votes_ok (B1_, B2_) strict r message votes =
  less_eq_nat (p19_quorum r) (size_list votes) andalso
    (sorted_wrt less_nat (map fst votes) andalso
      list_all
        (fn (i, s) =>
          equal_nata (size_list s) (nat_of_integer (64 : IntInf.int)) andalso
            (wire_octets (B1_, B2_) s andalso
              (case map_of equal_nat (p19_members r) i of NONE => false
                | SOME p19_member_key => strict p19_member_key message s)))
        votes);

fun p19_roster_shape key_ok r =
  less_nat zero_nata (p19_quorum r) andalso
    (less_eq_nat (p19_quorum r) (size_list (p19_members r)) andalso
      (distinct equal_nat (map fst (p19_members r)) andalso
        list_all
          (fn (i, k) =>
            less_nat i
              (power power_nat (nat_of_integer (2 : IntInf.int))
                (nat_of_integer (64 : IntInf.int))) andalso
              (equal_nata (size_list k)
                 (nat_of_integer (32 : IntInf.int)) andalso
                (wire_octets (numeral_nat, ord_nat) k andalso key_ok k)))
          (p19_members r)));

fun p19_no_key_alias r =
  distinct (equal_list equal_nat) (map snd (p19_members r));

fun p19_roster_ok key_ok r =
  p19_roster_shape key_ok r andalso p19_no_key_alias r;

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

fun p19_key_status checks k =
  (if membera (equal_prod (equal_list equal_nat) equal_bool) checks (k, true)
    then (if membera (equal_prod (equal_list equal_nat) equal_bool) checks
               (k, false)
           then nat_of_integer (3 : IntInf.int) else zero_nata)
    else (if membera (equal_prod (equal_list equal_nat) equal_bool) checks
               (k, false)
           then one_nata else nat_of_integer (2 : IntInf.int)));

fun p19_scan_keys checks [] = zero_nata
  | p19_scan_keys checks (k :: rest) =
    let
      val status = p19_key_status checks k;
    in
      (if equal_nata status zero_nata then p19_scan_keys checks rest
        else status)
    end;

fun p19_parse_records n raw =
  (if equal_nata n zero_nata then []
    else (get_le_octets (rev (take (nat_of_integer (8 : IntInf.int)) raw)),
           take (nat_of_integer (64 : IntInf.int))
             (drop (nat_of_integer (8 : IntInf.int)) raw)) ::
           p19_parse_records (minus_nata n one_nata)
             (drop (nat_of_integer (72 : IntInf.int)) raw));

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

fun p19_strict_status checks k m s =
  (if membera
        (equal_prod (equal_list equal_nat)
          (equal_prod (equal_list equal_nat)
            (equal_prod (equal_list equal_nat) equal_bool)))
        checks (k, (m, (s, true)))
    then (if membera
               (equal_prod (equal_list equal_nat)
                 (equal_prod (equal_list equal_nat)
                   (equal_prod (equal_list equal_nat) equal_bool)))
               checks (k, (m, (s, false)))
           then nat_of_integer (3 : IntInf.int) else zero_nata)
    else (if membera
               (equal_prod (equal_list equal_nat)
                 (equal_prod (equal_list equal_nat)
                   (equal_prod (equal_list equal_nat) equal_bool)))
               checks (k, (m, (s, false)))
           then one_nata else nat_of_integer (2 : IntInf.int)));

fun p19_scan_votes checks members m [] = zero_nata
  | p19_scan_votes checks members m ((i, s) :: rest) =
    (case map_of equal_nat members i of NONE => nat_of_integer (4 : IntInf.int)
      | SOME k =>
        let
          val status = p19_strict_status checks k m s;
        in
          (if equal_nata status zero_nata
            then p19_scan_votes checks members m rest else status)
        end);

fun p19_decode_payload max_signature roster_size raw =
  (if not (wire_octets (numeral_nat, ord_nat) raw) orelse
        (less_nat (size_list raw) (nat_of_integer (8 : IntInf.int)) orelse
          less_nat max_signature (size_list raw))
    then NONE
    else let
           val n =
             get_le_octets (rev (take (nat_of_integer (8 : IntInf.int)) raw));
         in
           (if less_eq_nat
                 (power power_nat (nat_of_integer (2 : IntInf.int))
                   (nat_of_integer (64 : IntInf.int)))
                 n orelse
                 (less_nat roster_size n orelse
                   (less_nat
                      (divide_nat
                        (minus_nata (size_list raw)
                          (nat_of_integer (8 : IntInf.int)))
                        (nat_of_integer (72 : IntInf.int)))
                      n orelse
                     not (equal_nata (size_list raw)
                           (plus_nata (nat_of_integer (8 : IntInf.int))
                             (times_nata (nat_of_integer (72 : IntInf.int))
                               n)))))
             then NONE
             else SOME (p19_parse_records n
                         (drop (nat_of_integer (8 : IntInf.int)) raw)))
         end);

fun p19_export_metadata stage cause =
  ([nat_of_integer (3 : IntInf.int), stage, cause], []);

fun p19_export_refusal reason = ([zero_nata, reason], []);

fun p19_export_accept r votes packet =
  ([one_nata, p19_deployment r, p19_source r, p19_principal r, p19_group_key r,
     p19_epoch r, p19_quorum r, size_list votes] @
     map fst votes,
    [encode_wire_core (packet_core packet),
      envelope_signing_bytes (packet_core packet), packet_signature packet]);

fun p19_export_step max_frame schemes registry key_checks strict_checks packet =
  let
    val c = packet_core packet;
  in
    (if not (wire_packet_wellformed packet) orelse
          less_nat max_frame (size_list (encode_wire_packet packet))
      then p19_export_refusal (nat_of_integer (70 : IntInf.int))
      else (if equal_nata (wire_signature_scheme c) one_nata
             then ([nat_of_integer (2 : IntInf.int)], [])
             else (if not (equal_nata (wire_signature_scheme c)
                            (nat_of_integer (2 : IntInf.int)))
                    then p19_export_refusal (nat_of_integer (70 : IntInf.int))
                    else (if not (membera equal_nat schemes
                                   (nat_of_integer (2 : IntInf.int)))
                           then p19_export_refusal
                                  (nat_of_integer (74 : IntInf.int))
                           else (case p19_select registry c
                                  of NONE =>
                                    p19_export_refusal
                                      (nat_of_integer (74 : IntInf.int))
                                  | SOME r =>
                                    (if not (p19_roster_ok (fn _ => true) r)
                                      then p19_export_refusal
     (nat_of_integer (74 : IntInf.int))
                                      else (case
     p19_decode_payload max_frame (size_list (p19_members r))
       (packet_signature packet)
     of NONE => p19_export_refusal (nat_of_integer (74 : IntInf.int))
     | SOME votes =>
       (if not (p19_votes_ok (numeral_nat, ord_nat)
                 (fn _ => fn _ => fn _ => true) r (envelope_signing_bytes c)
                 votes)
         then p19_export_refusal (nat_of_integer (74 : IntInf.int))
         else let
                val key_status =
                  p19_scan_keys key_checks (map snd (p19_members r));
              in
                (if equal_nata key_status one_nata
                  then p19_export_refusal (nat_of_integer (74 : IntInf.int))
                  else (if not (equal_nata key_status zero_nata)
                         then p19_export_metadata one_nata key_status
                         else let
                                val strict_status =
                                  p19_scan_votes strict_checks (p19_members r)
                                    (envelope_signing_bytes c) votes;
                              in
                                (if equal_nata strict_status one_nata
                                  then p19_export_refusal
 (nat_of_integer (74 : IntInf.int))
                                  else (if not
     (equal_nata strict_status zero_nata)
 then p19_export_metadata (nat_of_integer (2 : IntInf.int)) strict_status
 else p19_export_accept r votes packet))
                              end))
              end))))))))
  end;

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

fun code_check_declared_version bytes max_frame =
  (if less_nat max_frame (size_list bytes) then SOME Invalid_Wire_Format
    else (case code_declared_version bytes of NONE => NONE
           | SOME version =>
             (if not (equal_nata version (nat_of_integer (6 : IntInf.int)))
               then SOME Unsupported_Wire_Version else NONE)));

fun p19_export_packet max_frame schemes registry key_checks strict_checks bytes
  = (case code_check_declared_version bytes max_frame
      of NONE =>
        (case decode_wire_packet bytes
          of NONE => p19_export_refusal (nat_of_integer (70 : IntInf.int))
          | SOME a =>
            p19_export_step max_frame schemes registry key_checks strict_checks
              a)
      | SOME reason =>
        p19_export_refusal (code_transport_refusal_number reason));

fun p19_export_roster header members =
  (case header of [] => NONE | [_] => NONE | [_, _] => NONE | [_, _, _] => NONE
    | [_, _, _, _] => NONE | [_, _, _, _, _] => NONE
    | [p19_cfg_deployment, p19_cfg_source, p19_cfg_principal, p19_cfg_group,
        p19_cfg_epoch, p19_cfg_quorum]
      => SOME (P19_roster_ext
                (p19_cfg_deployment, p19_cfg_source, p19_cfg_principal,
                  p19_cfg_group, p19_cfg_epoch, p19_cfg_quorum, members, ()))
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => NONE);

fun p19_integer_octets xs =
  list_all
    (fn x =>
      IntInf.<= ((0 : IntInf.int), x) andalso IntInf.< (x, (256 : IntInf.int)))
    xs;

fun p19_export_registry current header members =
  (case current of [] => P19_registry_ext ((fn _ => NONE), (fn _ => NONE), ())
    | [_] => P19_registry_ext ((fn _ => NONE), (fn _ => NONE), ())
    | [_, _] => P19_registry_ext ((fn _ => NONE), (fn _ => NONE), ())
    | [_, _, _] => P19_registry_ext ((fn _ => NONE), (fn _ => NONE), ())
    | [_, _, _, _] => P19_registry_ext ((fn _ => NONE), (fn _ => NONE), ())
    | [p19_cfg_deployment, p19_cfg_source, p19_cfg_principal, p19_cfg_group,
        p19_cfg_epoch]
      => P19_registry_ext
           ((fn slot =>
              (if equal_proda equal_nat
                    (equal_prod equal_nat (equal_prod equal_nat equal_nat)) slot
                    (p19_cfg_deployment,
                      (p19_cfg_source, (p19_cfg_principal, p19_cfg_group)))
                then SOME p19_cfg_epoch else NONE)),
             (fn slot =>
               (if equal_proda
                     (equal_prod equal_nat
                       (equal_prod equal_nat (equal_prod equal_nat equal_nat)))
                     equal_nat slot
                     ((p19_cfg_deployment,
                        (p19_cfg_source, (p19_cfg_principal, p19_cfg_group))),
                       p19_cfg_epoch)
                 then p19_export_roster header members else NONE)),
             ())
    | _ :: _ :: _ :: _ :: _ :: _ :: _ =>
      P19_registry_ext ((fn _ => NONE), (fn _ => NONE), ()));

fun code_json_ascii text = map nat_of_char text;

fun p19_integer_nonnegative xs =
  list_all (fn a => IntInf.<= ((0 : IntInf.int), a)) xs;

fun p19_export_integer_metadata_ok (A1_, A2_) max_frame schemes current header
  members key_checks strict_checks =
  IntInf.<= ((0 : IntInf.int), max_frame) andalso
    (p19_integer_nonnegative schemes andalso
      ((equal_nata (size_list current) zero_nata orelse
         equal_nata (size_list current)
           (nat_of_integer (5 : IntInf.int))) andalso
        (p19_integer_nonnegative current andalso
          ((equal_nata (size_list header) zero_nata orelse
             equal_nata (size_list header)
               (nat_of_integer (6 : IntInf.int))) andalso
            (p19_integer_nonnegative header andalso
              ((if null header then null members else true) andalso
                (list_all
                   (fn (i, k) =>
                     less_eq A2_ (zero A1_) i andalso p19_integer_octets k)
                   members andalso
                  (list_all (fn (k, _) => p19_integer_octets k)
                     key_checks andalso
                    list_all
                      (fn (k, (m, (s, _))) =>
                        p19_integer_octets k andalso
                          (p19_integer_octets m andalso p19_integer_octets s))
                      strict_checks))))))));

fun p19_export_integer_run run max_frame schemes current header members
  key_checks strict_checks =
  (if not (p19_export_integer_metadata_ok (zero_integer, ord_integer) max_frame
            schemes current header members key_checks strict_checks)
    then NONE
    else let
           val ns = map nat_of_integer;
           val registry =
             p19_export_registry (ns current) (ns header)
               (map (fn (i, k) => (nat_of_integer i, ns k)) members);
           val keys = map (fn (k, a) => (ns k, a)) key_checks;
           val facts =
             map (fn (k, (m, (s, b))) => (ns k, (ns m, (ns s, b))))
               strict_checks;
           val (words, blobs) =
             run (nat_of_integer max_frame) (ns schemes) registry keys facts;
         in
           SOME (map integer_of_nat words, map (map integer_of_nat) blobs)
         end);

fun p19_export_integer_packet max_frame schemes current header members
  key_checks strict_checks raw =
  (if not (p19_integer_octets raw) then NONE
    else p19_export_integer_run
           (fn frame => fn selected => fn registry => fn keys => fn facts =>
             p19_export_packet frame selected registry keys facts
               (map nat_of_integer raw))
           max_frame schemes current header members key_checks strict_checks);

fun threshold_raw_packet x = p19_export_integer_packet x;

fun threshold_raw_model_identity ignored =
  map (map integer_of_nat o code_json_ascii)
    [[Chara (true, false, false, false, true, true, false, false)],
      [Chara (true, false, false, true, false, true, true, false),
        Chara (false, true, true, true, false, true, true, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (true, false, false, true, false, true, true, false),
        Chara (false, true, true, true, false, true, true, false),
        Chara (false, true, true, false, false, true, true, false),
        Chara (true, false, true, true, false, true, false, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (false, false, false, true, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, true, false, false, true, true, true, false),
        Chara (false, false, false, true, false, true, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (false, false, true, true, false, true, true, false),
        Chara (false, false, true, false, false, true, true, false),
        Chara (true, false, true, true, false, true, false, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (true, true, true, false, true, true, true, false),
        Chara (true, false, true, true, false, true, false, false),
        Chara (false, true, true, false, true, true, true, false),
        Chara (true, false, false, false, true, true, false, false)],
      [Chara (true, true, true, false, true, true, true, false),
        Chara (true, false, false, true, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, false, true, true, false, true, false, false),
        Chara (false, true, true, false, true, true, true, false),
        Chara (false, true, true, false, true, true, false, false),
        Chara (true, false, true, true, false, true, false, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (false, false, false, true, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, true, false, false, true, true, true, false),
        Chara (false, false, false, true, false, true, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (false, false, true, true, false, true, true, false),
        Chara (false, false, true, false, false, true, true, false),
        Chara (true, false, true, true, false, true, false, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (true, true, true, false, true, true, true, false),
        Chara (true, false, true, true, false, true, false, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (false, true, false, false, false, true, true, false),
        Chara (true, true, false, false, true, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (false, true, true, false, true, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, false, true, false, false, true, true, false),
        Chara (true, false, true, true, false, true, false, false),
        Chara (false, false, false, false, true, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, false, true, false, true, true, false),
        Chara (true, false, true, true, false, true, true, false),
        Chara (true, false, false, true, false, true, true, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (true, false, false, true, false, true, true, false),
        Chara (false, true, true, false, true, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, true, false, false, true, true, true, false)],
      [Chara (true, true, true, true, false, false, true, false),
        Chara (true, false, false, true, false, false, true, false),
        Chara (false, false, false, false, true, false, true, false),
        Chara (true, true, true, true, true, false, true, false),
        Chara (false, false, true, false, true, false, true, false),
        Chara (false, false, false, true, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, true, false, false, true, true, true, false),
        Chara (false, false, false, true, false, true, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (false, false, true, true, false, true, true, false),
        Chara (false, false, true, false, false, true, true, false),
        Chara (true, true, true, true, true, false, true, false),
        Chara (false, true, false, false, true, false, true, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (true, true, true, false, true, true, true, false),
        Chara (true, true, true, true, true, false, true, false),
        Chara (true, false, false, false, false, false, true, false),
        Chara (false, true, false, false, false, false, true, false),
        Chara (true, false, false, true, false, false, true, false),
        Chara (false, true, true, true, false, true, false, false),
        Chara (false, false, true, false, true, true, true, false),
        Chara (false, false, false, true, false, true, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, true, false, false, true, true, true, false),
        Chara (false, false, false, true, false, true, true, false),
        Chara (true, true, true, true, false, true, true, false),
        Chara (false, false, true, true, false, true, true, false),
        Chara (false, false, true, false, false, true, true, false),
        Chara (true, true, true, true, true, false, true, false),
        Chara (false, true, false, false, true, true, true, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (true, true, true, false, true, true, true, false),
        Chara (true, true, true, true, true, false, true, false),
        Chara (false, false, false, false, true, true, true, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (true, true, false, false, false, true, true, false),
        Chara (true, true, false, true, false, true, true, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, false, true, false, true, true, true, false)],
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
      [Chara (true, true, true, false, true, true, false, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, false, true, false, false, true, true, false),
        Chara (true, true, false, false, false, true, true, false),
        Chara (true, true, false, false, true, true, false, false),
        Chara (false, true, false, false, false, true, true, false),
        Chara (true, false, false, false, true, true, false, false),
        Chara (false, false, true, false, false, true, true, false),
        Chara (false, false, true, false, false, true, true, false),
        Chara (true, false, false, false, true, true, false, false),
        Chara (false, true, false, false, true, true, false, false),
        Chara (true, true, true, false, true, true, false, false),
        Chara (false, false, true, false, false, true, true, false),
        Chara (true, false, false, true, true, true, false, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (false, false, true, false, false, true, true, false),
        Chara (false, false, false, false, true, true, false, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, true, false, false, true, true, false, false),
        Chara (false, false, false, false, true, true, false, false),
        Chara (false, true, true, false, false, true, true, false),
        Chara (false, true, true, false, false, true, true, false),
        Chara (false, true, true, false, true, true, false, false),
        Chara (false, true, true, false, false, true, true, false),
        Chara (false, true, false, false, true, true, false, false),
        Chara (false, false, true, false, false, true, true, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (false, true, false, false, false, true, true, false),
        Chara (true, false, true, false, true, true, false, false),
        Chara (true, true, true, false, true, true, false, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (false, true, false, false, false, true, true, false),
        Chara (true, true, false, false, true, true, false, false),
        Chara (false, true, false, false, false, true, true, false),
        Chara (false, true, true, false, false, true, true, false),
        Chara (false, true, true, false, true, true, false, false),
        Chara (false, true, false, false, true, true, false, false),
        Chara (false, false, true, false, true, true, false, false),
        Chara (true, false, true, false, false, true, true, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (false, true, true, false, true, true, false, false),
        Chara (false, false, false, false, true, true, false, false),
        Chara (false, true, false, false, false, true, true, false),
        Chara (false, true, true, false, true, true, false, false),
        Chara (false, true, false, false, false, true, true, false),
        Chara (true, false, true, false, true, true, false, false),
        Chara (false, false, false, true, true, true, false, false),
        Chara (false, false, false, true, true, true, false, false),
        Chara (false, false, true, false, true, true, false, false),
        Chara (true, false, false, false, true, true, false, false),
        Chara (true, true, false, false, true, true, false, false),
        Chara (true, false, true, false, true, true, false, false),
        Chara (true, true, false, false, true, true, false, false),
        Chara (false, false, true, false, true, true, false, false),
        Chara (false, true, true, false, false, true, true, false),
        Chara (false, false, true, false, false, true, true, false),
        Chara (true, false, false, false, true, true, false, false),
        Chara (false, false, true, false, true, true, false, false),
        Chara (false, false, false, true, true, true, false, false),
        Chara (false, false, true, false, false, true, true, false),
        Chara (true, true, false, false, true, true, false, false),
        Chara (true, true, false, false, true, true, false, false),
        Chara (true, false, false, false, false, true, true, false),
        Chara (false, false, false, true, true, true, false, false)]];

end; (*struct OIP_Threshold_Raw_ABI*)
