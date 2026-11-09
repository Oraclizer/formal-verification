structure OIP_Wire_Oracle_V061 : sig
  type nat
  type char
  type 'a wire_core_ext
  type code_operand_verdict
  val sync_v061_nested_transport_flat :
    IntInf.int list ->
      IntInf.int list ->
        IntInf.int ->
          IntInf.int list ->
            IntInf.int list ->
              IntInf.int list ->
                bool ->
                  bool ->
                    bool ->
                      bool ->
                        IntInf.int list ->
                          IntInf.int *
                            (bool *
                              (IntInf.int list *
                                (bool *
                                  (IntInf.int list *
                                    (IntInf.int list *
                                      (IntInf.int list * IntInf.int list))))))
  val sync_v061_typed_model_identity : unit -> (IntInf.int list) list
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

fun eq A_ a b = equal A_ a b;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

fun equal_proda A_ B_ (x1, x2) (y1, y2) = eq A_ x1 y1 andalso eq B_ x2 y2;

fun equal_prod A_ B_ = {equal = equal_proda A_ B_} : ('a * 'b) equal;

fun equal_unita u v = true;

val equal_unit = {equal = equal_unita} : unit equal;

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

datatype 'a set = Set of 'a list | Coset of 'a list;

datatype char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;

datatype ('a, 'b) sum = Inl of 'a | Inr of 'b;

datatype wire_deadline = Deadline_Absent | Deadline_Indefinite |
  Deadline_At of nat;

datatype proto_field = Proto_Varint of nat * nat | Proto_Fixed64 of nat * nat |
  Proto_Bytes of nat * nat list;

datatype wire_refusal = Invalid_Wire_Format | Unsupported_Wire_Version |
  Invalid_Wire_Source | Invalid_Wire_Signature | Invalid_Wire_Threshold |
  Wire_TTL_Expired | Wire_TTL_Invalid | Conflicting_Wire_Replay;

datatype terminal_kind = Confirmed_Decision | Reversed_Decision;

datatype code_arrival = Code_First | Code_Identical | Code_Replay_Conflict;

datatype 'a wire_body_ext =
  Wire_body_ext of nat * nat list * (nat list) list * wire_deadline * 'a;

datatype 'a wire_core_ext =
  Wire_core_ext of
    nat * nat * nat * nat * nat * nat * nat * nat * nat * nat * nat list *
      wire_family * nat * nat option * nat * unit wire_body_ext * nat * nat *
      nat * 'a;

datatype 'a session_proof_ext = Session_proof_ext of nat * nat * 'a;

datatype application_query = Source_Balance of (nat * nat) |
  Destination_Balance of (nat * (nat * nat)) |
  Root_Balance of (nat * nat) * (nat * (nat * nat)) | Application_Value of nat |
  Regulatory_State of nat * nat | Terminal_Receipt of (nat * nat);

datatype 'a product_cut_ext = Product_cut_ext of nat * nat * 'a;

datatype identity_read_request =
  Current_Data of application_query * unit product_cut_ext |
  Historical_Data of application_query * nat | Raw_Data of application_query |
  Operation_Status of (nat * nat) | Authority_Journal | Owner_Data of nat;

datatype parsed_wire_query =
  Wire_Read_Request of unit session_proof_ext * identity_read_request |
  Wire_Cache_Request of unit session_proof_ext * application_query;

datatype sync_mode = Sync_Initial | Sync_Incremental | Sync_Full;

datatype 'a wire_packet_ext =
  Wire_packet_ext of unit wire_core_ext * nat list * 'a;

datatype 'a sync_query_ext =
  Sync_query_ext of nat * unit product_cut_ext * (nat * nat) * 'a;

datatype ordinary_wire_command = Wire_Reserve of nat | Wire_Dispatch of nat |
  Wire_Debit of nat | Wire_Cancel of nat | Wire_Fence of nat |
  Wire_Preempt of nat | Wire_Timeout of nat | Wire_Record_Terminal of nat * nat
  | Wire_Deliver of nat | Wire_Refund of nat * nat | Wire_Reconcile of nat * nat
  | Wire_Write of nat * nat | Wire_Publish;

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

datatype 'a wire_native_call_ext =
  Wire_native_call_ext of
    nat * (nat * nat) * nat * unit product_cut_ext * nat * (nat * nat) * nat *
      nat * nat * nat * nat * nat list * (nat list) list * 'a;

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

datatype code_nested_operand =
  Code_Nested_Ordinary of unit wire_native_call_ext * ordinary_wire_command |
  Code_Nested_Legal of (nat * nat) | Code_Nested_Spend of (nat * nat) |
  Code_Nested_Receipt of unit wire_core_ext | Code_Nested_Response |
  Code_Nested_Other;

datatype reference_response_kind = Recorded_Result | Delivery_Refusal |
  Validation_Refusal;

datatype code_response_status =
  Code_Known_Response of reference_response_kind * nat |
  Code_Unknown_Response of reference_response_kind * nat;

datatype code_operand_tree_result = Code_Tree_Refused of wire_refusal |
  Code_Tree_Ready of code_nested_operand | Code_Tree_Pending;

datatype code_operand_verdict = Code_Operand_Accept |
  Code_Operand_Refuse of wire_refusal | Code_Operand_Pending;

datatype code_heartbeat_fields =
  Code_Capabilities of nat * nat * nat set * nat set * nat set * nat set |
  Code_Liveness of nat * nat;

datatype code_transport_verdict = Code_Transport_First |
  Code_Transport_Identical | Code_Transport_Refusal of nat |
  Code_Transport_Pending;

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

datatype 'a sync_entry_ext = Sync_entry_ext of nat list * nat * nat * nat * 'a;

datatype 'a sync_request_ext =
  Sync_request_ext of
    (nat * nat) * nat * nat * unit product_cut_ext * (nat * nat) *
      unit sync_entry_ext * sync_mode * (nat list) option * nat list * 'a;

datatype 'a sync_link_original_ext =
  Sync_link_original_ext of
    unit wire_core_ext * unit wire_core_ext * unit sync_request_ext * 'a;

datatype 'a sync_link_ack_ext =
  Sync_link_ack_ext of
    nat list * unit sync_link_original_ext * (nat * nat) *
      reference_response_kind * nat * nat option * 'a;

datatype 'a sync_receipt_original_ext =
  Sync_receipt_original_ext of
    nat * nat list * unit wire_core_ext * unit sync_request_ext * 'a;

datatype 'a code_source_binding_ext =
  Code_source_binding_ext of (nat * nat) * nat * nat * nat * nat * nat * 'a;

datatype 'a native_scheduled_ack_ext =
  Native_scheduled_ack_ext of
    ((nat * nat) * nat) * nat * nat * nat * nat * nat * nat * nat *
      terminal_kind * 'a;

datatype 'a code_source_call_payload_ext =
  Code_source_call_payload_ext of
    nat * nat * nat * nat * nat * unit product_cut_ext *
      unit code_source_binding_ext * unit product_lock_credential_ext option *
      (nat * nat) list * ordinary_wire_command * 'a;

datatype 'a code_raw_capability_offer_ext =
  Code_raw_capability_offer_ext of
    nat * nat * nat * nat * nat * nat set * nat set * nat set * nat set * 'a;

fun id x = (fn xa => xa) x;

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

fun foldr f [] = id
  | foldr f (x :: xs) = f x o foldr f xs;

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

fun remdups A_ [] = []
  | remdups A_ (x :: xs) =
    (if membera A_ xs x then remdups A_ xs else x :: remdups A_ xs);

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun replicate n x =
  (if equal_nata n zero_nata then []
    else x :: replicate (minus_nata n one_nata) x);

fun is_none NONE = true
  | is_none (SOME x) = false;

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

fun insort_key B_ f x [] = [x]
  | insort_key B_ f x (y :: ys) =
    (if less_eq ((ord_preorder o preorder_order o order_linorder) B_) (f x)
          (f y)
      then x :: y :: ys else y :: insort_key B_ f x ys);

fun sort_key B_ f xs = foldr (insort_key B_ f) xs [];

fun sync_operation core =
  (wire_message_family core, wire_opcode (wire_operation_body core));

fun cut_authority_epoch
  (Product_cut_ext (cut_authority_epoch, cut_revision, more)) =
  cut_authority_epoch;

fun cut_revision (Product_cut_ext (cut_authority_epoch, cut_revision, more)) =
  cut_revision;

fun code_ir_scalar oip_binder_value = [zero_nata, oip_binder_value];

fun code_ir_node x =
  (fn oip_binder_tag => fn oip_binder_field_chunks =>
    [oip_binder_tag, size_list oip_binder_field_chunks] @
      concat oip_binder_field_chunks)
    x;

fun code_ir_pair oip_binder_pair =
  code_ir_node (nat_of_integer (90 : IntInf.int))
    [code_ir_scalar (fst oip_binder_pair),
      code_ir_scalar (snd oip_binder_pair)];

fun code_ir_cut x =
  (fn oip_binder_selected_cut =>
    code_ir_pair
      (cut_authority_epoch oip_binder_selected_cut,
        cut_revision oip_binder_selected_cut))
    x;

fun sorted_list_of_set (A1_, A2_) (Set xs) =
  sort_key A2_ (fn x => x) (remdups A1_ xs);

fun code_ir_list oip_binder_render oip_binder_values =
  [nat_of_integer (2 : IntInf.int), size_list oip_binder_values] @
    maps oip_binder_render oip_binder_values;

fun code_ir_set oip_binder_values =
  code_ir_list code_ir_scalar
    (sorted_list_of_set (equal_nat, linorder_nat) oip_binder_values);

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

fun code_ir_bytes oip_binder_bytes =
  [one_nata, size_list oip_binder_bytes] @ oip_binder_bytes;

fun equal_wire_deadline Deadline_Indefinite (Deadline_At x3) = false
  | equal_wire_deadline (Deadline_At x3) Deadline_Indefinite = false
  | equal_wire_deadline Deadline_Absent (Deadline_At x3) = false
  | equal_wire_deadline (Deadline_At x3) Deadline_Absent = false
  | equal_wire_deadline Deadline_Absent Deadline_Indefinite = false
  | equal_wire_deadline Deadline_Indefinite Deadline_Absent = false
  | equal_wire_deadline (Deadline_At x3) (Deadline_At y3) = equal_nata x3 y3
  | equal_wire_deadline Deadline_Indefinite Deadline_Indefinite = true
  | equal_wire_deadline Deadline_Absent Deadline_Absent = true;

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

fun code_ir_option oip_binder_render NONE = [nat_of_integer (3 : IntInf.int)]
  | code_ir_option oip_binder_render (SOME oip_binder_value) =
    nat_of_integer (4 : IntInf.int) :: oip_binder_render oip_binder_value;

fun code_ir_triple oip_binder_triple =
  let
    val (oip_binder_first, (oip_binder_second, oip_binder_third)) =
      oip_binder_triple;
  in
    code_ir_node (nat_of_integer (91 : IntInf.int))
      [code_ir_scalar oip_binder_first, code_ir_scalar oip_binder_second,
        code_ir_scalar oip_binder_third]
  end;

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

fun sync_mode_number Sync_Initial = one_nata
  | sync_mode_number Sync_Incremental = nat_of_integer (2 : IntInf.int)
  | sync_mode_number Sync_Full = nat_of_integer (3 : IntInf.int);

fun response_kind_at number =
  (if equal_nata number one_nata then SOME Recorded_Result
    else (if equal_nata number (nat_of_integer (2 : IntInf.int))
           then SOME Delivery_Refusal
           else (if equal_nata number (nat_of_integer (3 : IntInf.int))
                  then SOME Validation_Refusal else NONE)));

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

fun equal_reference_response_kind Delivery_Refusal Validation_Refusal = false
  | equal_reference_response_kind Validation_Refusal Delivery_Refusal = false
  | equal_reference_response_kind Recorded_Result Validation_Refusal = false
  | equal_reference_response_kind Validation_Refusal Recorded_Result = false
  | equal_reference_response_kind Recorded_Result Delivery_Refusal = false
  | equal_reference_response_kind Delivery_Refusal Recorded_Result = false
  | equal_reference_response_kind Validation_Refusal Validation_Refusal = true
  | equal_reference_response_kind Delivery_Refusal Delivery_Refusal = true
  | equal_reference_response_kind Recorded_Result Recorded_Result = true;

fun equal_wire_body_ext A_
  (Wire_body_ext
    (wire_opcodea, wire_wordsa, wire_blobsa, wire_deadlinea, morea))
  (Wire_body_ext (wire_opcode, wire_words, wire_blobs, wire_deadline, more)) =
  equal_nata wire_opcodea wire_opcode andalso
    (equal_lista equal_nat wire_wordsa wire_words andalso
      (equal_lista (equal_list equal_nat) wire_blobsa wire_blobs andalso
        (equal_wire_deadline wire_deadlinea wire_deadline andalso
          eq A_ morea more)));

fun equal_option A_ NONE (SOME x2) = false
  | equal_option A_ (SOME x2) NONE = false
  | equal_option A_ (SOME x2) (SOME y2) = eq A_ x2 y2
  | equal_option A_ NONE NONE = true;

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
                              (equal_option equal_nat wire_secondary_codea
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

fun sync_link_call_core
  (Sync_link_original_ext
    (sync_link_enclosed, sync_link_call_core, sync_link_request, more))
  = sync_link_call_core;

fun sync_link_enclosed
  (Sync_link_original_ext
    (sync_link_enclosed, sync_link_call_core, sync_link_request, more))
  = sync_link_enclosed;

fun sync_link_request
  (Sync_link_original_ext
    (sync_link_enclosed, sync_link_call_core, sync_link_request, more))
  = sync_link_request;

fun sync_call
  (Sync_request_ext
    (sync_call, sync_message, sync_session, sync_signed_cut, sync_key,
      sync_requested, sync_mode, sync_claimed_prior, sync_attestation, more))
  = sync_call;

fun sync_link_original_view
  (Sync_link_ack_ext
    (sync_link_exact_original, sync_link_original_view, sync_link_id,
      sync_link_kind, sync_link_code, sync_link_commit, more))
  = sync_link_original_view;

fun sync_link_commit
  (Sync_link_ack_ext
    (sync_link_exact_original, sync_link_original_view, sync_link_id,
      sync_link_kind, sync_link_code, sync_link_commit, more))
  = sync_link_commit;

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
    else (if not (equal_reference_response_kind kind Recorded_Result) andalso
               committed
           then NONE else SOME (Code_Unknown_Response (kind, number))));

fun sync_link_kind
  (Sync_link_ack_ext
    (sync_link_exact_original, sync_link_original_view, sync_link_id,
      sync_link_kind, sync_link_code, sync_link_commit, more))
  = sync_link_kind;

fun sync_link_code
  (Sync_link_ack_ext
    (sync_link_exact_original, sync_link_original_view, sync_link_id,
      sync_link_kind, sync_link_code, sync_link_commit, more))
  = sync_link_code;

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
      (not (equal_reference_response_kind kind Recorded_Result) orelse
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
           (equal_reference_response_kind kind Recorded_Result orelse
             not committed));

fun equal_bool false p = not p
  | equal_bool true p = p
  | equal_bool p false = not p
  | equal_bool p true = p;

fun sync_added_status (A1_, A2_) number =
  member A1_ number
    (insert A1_ (numeral A2_ (Bit1 (Bit0 (Bit1 (Bit1 One)))))
      (insert A1_ (numeral A2_ (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One))))))
        (insert A1_ (numeral A2_ (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One))))))
          (insert A1_ (numeral A2_ (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 One))))))
            bot_set))));

fun sync_known_response_compatible original kind number committed =
  (if sync_added_status (equal_nat, numeral_nat) number
    then equal_proda equal_wire_family equal_nat (sync_operation original)
           (Wire_State_Sync, nat_of_integer (7 : IntInf.int)) andalso
           (equal_reference_response_kind kind Recorded_Result andalso
             equal_bool committed
               (equal_nata number (nat_of_integer (29 : IntInf.int))))
    else (if equal_proda equal_wire_family equal_nat (sync_operation original)
               (Wire_State_Sync, nat_of_integer (7 : IntInf.int))
           then (if code_known_response_number (equal_nat, interval_nat) number
                  then member equal_nat number
                         (reference_result_codes (equal_nat, interval_nat) kind
                           committed) andalso
                         (not (equal_reference_response_kind kind
                                Recorded_Result) orelse
                           member equal_nat number
                             (insert equal_nat one_nata
                               (insert equal_nat
                                 (nat_of_integer (2 : IntInf.int))
                                 (insert equal_nat
                                   (nat_of_integer (3 : IntInf.int)) bot_set))))
                  else equal_reference_response_kind kind Recorded_Result orelse
                         not committed)
           else code_response_compatible (wire_message_family original)
                  (wire_opcode (wire_operation_body original)) kind number
                  committed));

fun sync_link_response_status view =
  let
    val kind = sync_link_kind view;
    val code = sync_link_code view;
    val committed = not (is_none (sync_link_commit view));
  in
    (if not (sync_known_response_compatible
              (sync_link_call_core (sync_link_original_view view)) kind code
              committed)
      then NONE
      else (if sync_added_status (equal_nat, numeral_nat) code
             then SOME (Code_Known_Response (kind, code))
             else code_decode_response_status kind code committed))
  end;

fun sync_link_response_header outer enclosed caller =
  equal_nata (wire_version outer) (wire_version enclosed) andalso
    (equal_nata (wire_deployment outer) (wire_deployment enclosed) andalso
      (equal_nata (wire_principal enclosed) (fst caller) andalso
        (equal_nata (wire_source_domain outer)
           (wire_target_domain enclosed) andalso
          equal_nata (wire_target_domain outer)
            (wire_source_domain enclosed))));

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

fun sync_link_finish_parse raw_status outer raw original caller kind code commit
  = let
      val enclosed = sync_link_enclosed original;
      val inner = sync_link_call_core original;
      val committed = not (is_none commit);
      val view =
        Sync_link_ack_ext (raw, original, caller, kind, code, commit, ());
    in
      (if not (equal_reference_response_kind kind Recorded_Result) andalso
            committed orelse
            raw_status andalso
              (sync_added_status (equal_nat, numeral_nat) code andalso
                (not (equal_reference_response_kind kind Recorded_Result) orelse
                  not (equal_bool committed
                        (equal_nata code (nat_of_integer (29 : IntInf.int))))))
        then Inl Invalid_Wire_Format
        else (if not (sync_link_response_header outer enclosed caller)
               then Inl Invalid_Wire_Source
               else (if not (equal_wire_core_ext equal_unit enclosed
                              inner) andalso
                          not (code_same_original enclosed inner)
                      then Inl Invalid_Wire_Source
                      else (if not (equal_proda equal_nat equal_nat caller
                                     (sync_call (sync_link_request original)))
                             then Inl Invalid_Wire_Format
                             else (if raw_status andalso
is_none (sync_link_response_status view)
                                    then Inl Invalid_Wire_Format
                                    else Inr view)))))
    end;

fun sync_receipt_request
  (Sync_receipt_original_ext
    (sync_receipt_session, sync_receipt_exact_core, sync_receipt_inner,
      sync_receipt_request, more))
  = sync_receipt_request;

fun sync_receipt_inner
  (Sync_receipt_original_ext
    (sync_receipt_session, sync_receipt_exact_core, sync_receipt_inner,
      sync_receipt_request, more))
  = sync_receipt_inner;

fun equal_sync_mode Sync_Incremental Sync_Full = false
  | equal_sync_mode Sync_Full Sync_Incremental = false
  | equal_sync_mode Sync_Initial Sync_Full = false
  | equal_sync_mode Sync_Full Sync_Initial = false
  | equal_sync_mode Sync_Initial Sync_Incremental = false
  | equal_sync_mode Sync_Incremental Sync_Initial = false
  | equal_sync_mode Sync_Full Sync_Full = true
  | equal_sync_mode Sync_Incremental Sync_Incremental = true
  | equal_sync_mode Sync_Initial Sync_Initial = true;

fun sync_mode_at tag =
  (if equal_nata tag one_nata then SOME Sync_Initial
    else (if equal_nata tag (nat_of_integer (2 : IntInf.int))
           then SOME Sync_Incremental
           else (if equal_nata tag (nat_of_integer (3 : IntInf.int))
                  then SOME Sync_Full else NONE)));

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

fun sync_parse_query_eight fuel outer =
  let
    val body = wire_operation_body outer;
  in
    (if less_nat fuel (nat_of_integer (2 : IntInf.int)) orelse
          (not (equal_proda equal_wire_family equal_nat (sync_operation outer)
                 (Wire_Query, nat_of_integer (8 : IntInf.int))) orelse
            not (equal_wire_deadline (wire_deadline body) Deadline_Absent))
      then NONE
      else (case (wire_words body, wire_blobs body) of ([], _) => NONE
             | ([_], []) => NONE
             | ([session], [raw]) =>
               bind (sync_decode_core raw)
                 (fn original =>
                   map_option
                     (fn request =>
                       Sync_receipt_original_ext
                         (session, raw, original, request, ()))
                     (sync_read_operands original))
             | ([_], _ :: _ :: _) => NONE | (_ :: _ :: _, _) => NONE))
  end;

fun sync_link_original_at fuel enclosed =
  (if less_nat fuel (nat_of_integer (2 : IntInf.int)) then NONE
    else (case sync_read_operands enclosed
           of NONE =>
             map_option
               (fn receipt =>
                 Sync_link_original_ext
                   (enclosed, sync_receipt_inner receipt,
                     sync_receipt_request receipt, ()))
               (sync_parse_query_eight (minus_nata fuel one_nata) enclosed)
           | SOME request =>
             SOME (Sync_link_original_ext (enclosed, enclosed, request, ()))));

fun sync_link_parse_ack raw_status fuel outer =
  let
    val body = wire_operation_body outer;
  in
    (if not (equal_proda equal_wire_family equal_nat (sync_operation outer)
              (Wire_Ack, nat_of_integer (2 : IntInf.int))) orelse
          not (equal_wire_deadline (wire_deadline body) Deadline_Absent)
      then Inl Invalid_Wire_Format
      else (case wire_blobs body of [] => Inl Invalid_Wire_Format
             | [raw] =>
               (case sync_decode_core raw of NONE => Inl Invalid_Wire_Format
                 | SOME enclosed =>
                   (case sync_link_original_at fuel enclosed
                     of NONE => Inl Invalid_Wire_Format
                     | SOME original =>
                       (case response_result_words (wire_words body)
                         of NONE => Inl Invalid_Wire_Format
                         | SOME (caller, (kind, (a, b))) =>
                           sync_link_finish_parse raw_status outer raw original
                             caller kind a b)))
             | _ :: _ :: _ => Inl Invalid_Wire_Format))
  end;

fun sync_link_exact_original
  (Sync_link_ack_ext
    (sync_link_exact_original, sync_link_original_view, sync_link_id,
      sync_link_kind, sync_link_code, sync_link_commit, more))
  = sync_link_exact_original;

fun sync_link_id
  (Sync_link_ack_ext
    (sync_link_exact_original, sync_link_original_view, sync_link_id,
      sync_link_kind, sync_link_code, sync_link_commit, more))
  = sync_link_id;

fun sync_response_kind_number A_ Recorded_Result = one (one_numeral A_)
  | sync_response_kind_number A_ Delivery_Refusal = numeral A_ (Bit0 One)
  | sync_response_kind_number A_ Validation_Refusal = numeral A_ (Bit1 One);

fun sync_claimed_prior
  (Sync_request_ext
    (sync_call, sync_message, sync_session, sync_signed_cut, sync_key,
      sync_requested, sync_mode, sync_claimed_prior, sync_attestation, more))
  = sync_claimed_prior;

fun sync_attestation
  (Sync_request_ext
    (sync_call, sync_message, sync_session, sync_signed_cut, sync_key,
      sync_requested, sync_mode, sync_claimed_prior, sync_attestation, more))
  = sync_attestation;

fun sync_signed_cut
  (Sync_request_ext
    (sync_call, sync_message, sync_session, sync_signed_cut, sync_key,
      sync_requested, sync_mode, sync_claimed_prior, sync_attestation, more))
  = sync_signed_cut;

fun sync_origin_epoch
  (Sync_entry_ext
    (sync_commitment, sync_position, sync_origin_epoch, sync_event, more))
  = sync_origin_epoch;

fun sync_requested
  (Sync_request_ext
    (sync_call, sync_message, sync_session, sync_signed_cut, sync_key,
      sync_requested, sync_mode, sync_claimed_prior, sync_attestation, more))
  = sync_requested;

fun sync_commitment
  (Sync_entry_ext
    (sync_commitment, sync_position, sync_origin_epoch, sync_event, more))
  = sync_commitment;

fun sync_session
  (Sync_request_ext
    (sync_call, sync_message, sync_session, sync_signed_cut, sync_key,
      sync_requested, sync_mode, sync_claimed_prior, sync_attestation, more))
  = sync_session;

fun sync_message
  (Sync_request_ext
    (sync_call, sync_message, sync_session, sync_signed_cut, sync_key,
      sync_requested, sync_mode, sync_claimed_prior, sync_attestation, more))
  = sync_message;

fun sync_position
  (Sync_entry_ext
    (sync_commitment, sync_position, sync_origin_epoch, sync_event, more))
  = sync_position;

fun sync_mode
  (Sync_request_ext
    (sync_call, sync_message, sync_session, sync_signed_cut, sync_key,
      sync_requested, sync_mode, sync_claimed_prior, sync_attestation, more))
  = sync_mode;

fun sync_key
  (Sync_request_ext
    (sync_call, sync_message, sync_session, sync_signed_cut, sync_key,
      sync_requested, sync_mode, sync_claimed_prior, sync_attestation, more))
  = sync_key;

fun sync_event
  (Sync_entry_ext
    (sync_commitment, sync_position, sync_origin_epoch, sync_event, more))
  = sync_event;

fun sync_call_operand_ir request =
  let
    val item = sync_requested request;
    val stream = sync_key request;
  in
    code_ir_node (nat_of_integer (22 : IntInf.int))
      [code_ir_scalar (sync_message request), code_ir_pair (sync_call request),
        code_ir_scalar (sync_session request),
        code_ir_cut (sync_signed_cut request),
        code_ir_scalar (sync_origin_epoch item),
        code_ir_pair (snd stream, sync_event item), code_ir_scalar (fst stream),
        code_ir_scalar (sync_position item),
        code_ir_scalar (sync_mode_number (sync_mode request)),
        code_ir_bytes (sync_commitment item),
        code_ir_option code_ir_bytes (sync_claimed_prior request),
        code_ir_bytes (sync_attestation request)]
  end;

fun sync_receipt_operand_ir session original request =
  code_ir_node (nat_of_integer (15 : IntInf.int))
    [code_ir_scalar session, code_ir_bytes (encode_wire_core original),
      sync_call_operand_ir request];

fun sync_enclosed_operand_ir original =
  let
    val enclosed = sync_link_enclosed original;
    val effective = sync_link_call_core original;
    val request = sync_link_request original;
  in
    (if equal_wire_core_ext equal_unit enclosed effective
      then sync_call_operand_ir request
      else sync_receipt_operand_ir
             (hd (wire_words (wire_operation_body enclosed))) effective request)
  end;

fun sync_ack_operand_ir view =
  code_ir_node (nat_of_integer (16 : IntInf.int))
    [code_ir_pair (sync_link_id view),
      code_ir_scalar
        (sync_response_kind_number numeral_nat (sync_link_kind view)),
      code_ir_scalar (sync_link_code view),
      code_ir_option code_ir_scalar (sync_link_commit view),
      code_ir_bytes (sync_link_exact_original view),
      sync_enclosed_operand_ir (sync_link_original_view view)];

fun sync_ack_wire_ir depth core =
  (case sync_link_parse_ack true depth core of Inl a => Inl a
    | Inr view => Inr (sync_ack_operand_ir view));

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

fun code_transport_key core =
  (wire_deployment core,
    (wire_source_domain core, (wire_principal core, wire_uuid core)));

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

fun sync_single_original core =
  (case wire_blobs (wire_operation_body core) of [] => NONE
    | [raw] => sync_decode_core raw | _ :: _ :: _ => NONE);

fun code_compare_binding A_ retained exact =
  (case retained of NONE => Code_First
    | SOME bytes =>
      (if eq A_ bytes exact then Code_Identical else Code_Replay_Conflict));

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

fun sync_query_session
  (Sync_query_ext (sync_query_session, sync_query_cut, sync_query_key, more)) =
  sync_query_session;

fun sync_query_key
  (Sync_query_ext (sync_query_session, sync_query_cut, sync_query_key, more)) =
  sync_query_key;

fun sync_query_cut
  (Sync_query_ext (sync_query_session, sync_query_cut, sync_query_key, more)) =
  sync_query_cut;

fun sync_query_operand_ir request =
  let
    val cut = sync_query_cut request;
    val stream = sync_query_key request;
  in
    code_ir_node (nat_of_integer (13 : IntInf.int))
      [code_ir_node (nat_of_integer (104 : IntInf.int))
         [code_ir_scalar (sync_query_session request),
           code_ir_scalar (cut_authority_epoch cut)],
        code_ir_node (nat_of_integer (156 : IntInf.int))
          [code_ir_cut cut, code_ir_scalar (fst stream),
            code_ir_scalar (snd stream)]]
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

fun sync_direct_operand_ir depth core =
  (if equal_nata depth zero_nata then NONE
    else (if equal_proda equal_wire_family equal_nat (sync_operation core)
               (Wire_State_Sync, nat_of_integer (7 : IntInf.int))
           then map_option sync_call_operand_ir (sync_read_operands core)
           else map_option sync_query_operand_ir (sync_read_query core)));

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

fun source_payload_origin_epoch
  (Code_source_call_payload_ext
    (source_payload_message, source_payload_origin_epoch,
      source_payload_endpoint, source_payload_caller, source_payload_session,
      source_payload_cut, source_payload_binding, source_payload_credential,
      source_payload_versions, source_payload_command, more))
  = source_payload_origin_epoch;

fun source_payload_endpoint
  (Code_source_call_payload_ext
    (source_payload_message, source_payload_origin_epoch,
      source_payload_endpoint, source_payload_caller, source_payload_session,
      source_payload_cut, source_payload_binding, source_payload_credential,
      source_payload_versions, source_payload_command, more))
  = source_payload_endpoint;

fun source_payload_session
  (Code_source_call_payload_ext
    (source_payload_message, source_payload_origin_epoch,
      source_payload_endpoint, source_payload_caller, source_payload_session,
      source_payload_cut, source_payload_binding, source_payload_credential,
      source_payload_versions, source_payload_command, more))
  = source_payload_session;

fun source_payload_message
  (Code_source_call_payload_ext
    (source_payload_message, source_payload_origin_epoch,
      source_payload_endpoint, source_payload_caller, source_payload_session,
      source_payload_cut, source_payload_binding, source_payload_credential,
      source_payload_versions, source_payload_command, more))
  = source_payload_message;

fun source_payload_binding
  (Code_source_call_payload_ext
    (source_payload_message, source_payload_origin_epoch,
      source_payload_endpoint, source_payload_caller, source_payload_session,
      source_payload_cut, source_payload_binding, source_payload_credential,
      source_payload_versions, source_payload_command, more))
  = source_payload_binding;

fun source_payload_caller
  (Code_source_call_payload_ext
    (source_payload_message, source_payload_origin_epoch,
      source_payload_endpoint, source_payload_caller, source_payload_session,
      source_payload_cut, source_payload_binding, source_payload_credential,
      source_payload_versions, source_payload_command, more))
  = source_payload_caller;

fun source_binding_destination
  (Code_source_binding_ext
    (source_binding_origin, source_binding_asset, source_binding_owner,
      source_binding_destination, source_binding_recipient,
      source_binding_amount, more))
  = source_binding_destination;

fun source_binding_recipient
  (Code_source_binding_ext
    (source_binding_origin, source_binding_asset, source_binding_owner,
      source_binding_destination, source_binding_recipient,
      source_binding_amount, more))
  = source_binding_recipient;

fun source_payload_cut
  (Code_source_call_payload_ext
    (source_payload_message, source_payload_origin_epoch,
      source_payload_endpoint, source_payload_caller, source_payload_session,
      source_payload_cut, source_payload_binding, source_payload_credential,
      source_payload_versions, source_payload_command, more))
  = source_payload_cut;

fun source_binding_origin
  (Code_source_binding_ext
    (source_binding_origin, source_binding_asset, source_binding_owner,
      source_binding_destination, source_binding_recipient,
      source_binding_amount, more))
  = source_binding_origin;

fun source_binding_amount
  (Code_source_binding_ext
    (source_binding_origin, source_binding_asset, source_binding_owner,
      source_binding_destination, source_binding_recipient,
      source_binding_amount, more))
  = source_binding_amount;

fun source_binding_owner
  (Code_source_binding_ext
    (source_binding_origin, source_binding_asset, source_binding_owner,
      source_binding_destination, source_binding_recipient,
      source_binding_amount, more))
  = source_binding_owner;

fun source_binding_asset
  (Code_source_binding_ext
    (source_binding_origin, source_binding_asset, source_binding_owner,
      source_binding_destination, source_binding_recipient,
      source_binding_amount, more))
  = source_binding_asset;

fun native_funding_owner
  (Wire_native_call_ext
    (native_reference, native_id, native_session, native_cut,
      native_origin_epoch, native_origin, native_asset, native_funding_owner,
      native_destination, native_recipient, native_amount, native_tail_words,
      native_proof_bytes, more))
  = native_funding_owner;

fun native_recipient
  (Wire_native_call_ext
    (native_reference, native_id, native_session, native_cut,
      native_origin_epoch, native_origin, native_asset, native_funding_owner,
      native_destination, native_recipient, native_amount, native_tail_words,
      native_proof_bytes, more))
  = native_recipient;

fun native_amount
  (Wire_native_call_ext
    (native_reference, native_id, native_session, native_cut,
      native_origin_epoch, native_origin, native_asset, native_funding_owner,
      native_destination, native_recipient, native_amount, native_tail_words,
      native_proof_bytes, more))
  = native_amount;

fun native_asset
  (Wire_native_call_ext
    (native_reference, native_id, native_session, native_cut,
      native_origin_epoch, native_origin, native_asset, native_funding_owner,
      native_destination, native_recipient, native_amount, native_tail_words,
      native_proof_bytes, more))
  = native_asset;

fun code_source_binding_from_native native =
  Code_source_binding_ext
    (native_origin native, native_asset native, native_funding_owner native,
      native_destination native, native_recipient native, native_amount native,
      ());

fun native_reference
  (Wire_native_call_ext
    (native_reference, native_id, native_session, native_cut,
      native_origin_epoch, native_origin, native_asset, native_funding_owner,
      native_destination, native_recipient, native_amount, native_tail_words,
      native_proof_bytes, more))
  = native_reference;

fun native_session
  (Wire_native_call_ext
    (native_reference, native_id, native_session, native_cut,
      native_origin_epoch, native_origin, native_asset, native_funding_owner,
      native_destination, native_recipient, native_amount, native_tail_words,
      native_proof_bytes, more))
  = native_session;

fun native_cut
  (Wire_native_call_ext
    (native_reference, native_id, native_session, native_cut,
      native_origin_epoch, native_origin, native_asset, native_funding_owner,
      native_destination, native_recipient, native_amount, native_tail_words,
      native_proof_bytes, more))
  = native_cut;

fun code_source_payload_from_native core native credential versions command =
  Code_source_call_payload_ext
    (native_reference native, native_origin_epoch native,
      wire_target_domain core, fst (native_id native), native_session native,
      native_cut native, code_source_binding_from_native native, credential,
      versions, command, ());

fun code_ir_native oip_binder_core oip_binder_native =
  let
    val oip_binder_payload =
      code_source_payload_from_native oip_binder_core oip_binder_native NONE []
        Wire_Publish;
    val oip_binder_binding = source_payload_binding oip_binder_payload;
  in
    code_ir_node (nat_of_integer (100 : IntInf.int))
      [code_ir_scalar (source_payload_message oip_binder_payload),
        code_ir_pair (native_id oip_binder_native),
        code_ir_scalar (source_payload_session oip_binder_payload),
        code_ir_cut (source_payload_cut oip_binder_payload),
        code_ir_scalar (source_payload_origin_epoch oip_binder_payload),
        code_ir_pair (source_binding_origin oip_binder_binding),
        code_ir_scalar (source_binding_asset oip_binder_binding),
        code_ir_scalar (source_binding_owner oip_binder_binding),
        code_ir_scalar (source_binding_destination oip_binder_binding),
        code_ir_scalar (source_binding_recipient oip_binder_binding),
        code_ir_scalar (source_binding_amount oip_binder_binding),
        code_ir_scalar (source_payload_endpoint oip_binder_payload),
        code_ir_scalar (source_payload_caller oip_binder_payload)]
  end;

fun proof_epoch (Session_proof_ext (proof_session, proof_epoch, more)) =
  proof_epoch;

fun sync_direct_added_original core =
  (case sync_single_original core of NONE => false
    | SOME a => sync_added_operation a);

fun sync_ack_has_added_original core =
  (case sync_single_original core of NONE => false
    | SOME original =>
      sync_added_operation original orelse
        equal_proda equal_wire_family equal_nat (sync_operation original)
          (Wire_Query, nat_of_integer (8 : IntInf.int)) andalso
          sync_direct_added_original original);

fun sync_receipt_session
  (Sync_receipt_original_ext
    (sync_receipt_session, sync_receipt_exact_core, sync_receipt_inner,
      sync_receipt_request, more))
  = sync_receipt_session;

fun sync_query_eight_wire_ir depth core =
  (case sync_parse_query_eight depth core of NONE => Inl Invalid_Wire_Format
    | SOME receipt =>
      Inr (sync_receipt_operand_ir (sync_receipt_session receipt)
            (sync_receipt_inner receipt) (sync_receipt_request receipt)));

fun sync_selected_nested_ir depth core =
  (if equal_proda equal_wire_family equal_nat (sync_operation core)
        (Wire_Query, nat_of_integer (8 : IntInf.int)) andalso
        sync_direct_added_original core
    then SOME (sync_query_eight_wire_ir depth core)
    else (if equal_proda equal_wire_family equal_nat (sync_operation core)
               (Wire_Ack, nat_of_integer (2 : IntInf.int)) andalso
               sync_ack_has_added_original core
           then SOME (sync_ack_wire_ir depth core) else NONE));

fun code_decode_query_nonreceipt core =
  (if not (equal_wire_deadline (wire_deadline (wire_operation_body core))
            Deadline_Absent)
    then NONE else decode_wire_query_body core);

fun proof_session (Session_proof_ext (proof_session, proof_epoch, more)) =
  proof_session;

fun code_ir_session_proof oip_binder_proof =
  code_ir_node (nat_of_integer (104 : IntInf.int))
    [code_ir_scalar (proof_session oip_binder_proof),
      code_ir_scalar (proof_epoch oip_binder_proof)];

fun code_ir_query (Application_Value oip_binder_asset) =
  code_ir_node (nat_of_integer (160 : IntInf.int))
    [code_ir_scalar oip_binder_asset]
  | code_ir_query (Source_Balance oip_binder_account) =
    code_ir_node (nat_of_integer (161 : IntInf.int))
      [code_ir_pair oip_binder_account]
  | code_ir_query (Destination_Balance oip_binder_account) =
    code_ir_node (nat_of_integer (162 : IntInf.int))
      [code_ir_triple oip_binder_account]
  | code_ir_query (Root_Balance (oip_binder_origin, oip_binder_account)) =
    code_ir_node (nat_of_integer (163 : IntInf.int))
      [code_ir_pair oip_binder_origin, code_ir_triple oip_binder_account]
  | code_ir_query (Regulatory_State (oip_binder_domain, oip_binder_asset)) =
    code_ir_node (nat_of_integer (164 : IntInf.int))
      [code_ir_scalar oip_binder_domain, code_ir_scalar oip_binder_asset]
  | code_ir_query (Terminal_Receipt oip_binder_origin) =
    code_ir_node (nat_of_integer (165 : IntInf.int))
      [code_ir_pair oip_binder_origin];

fun code_ir_read_request (Current_Data (oip_binder_query, oip_binder_expected))
  = code_ir_node (nat_of_integer (150 : IntInf.int))
      [code_ir_query oip_binder_query, code_ir_cut oip_binder_expected]
  | code_ir_read_request
    (Historical_Data (oip_binder_query, oip_binder_revision)) =
    code_ir_node (nat_of_integer (151 : IntInf.int))
      [code_ir_query oip_binder_query, code_ir_scalar oip_binder_revision]
  | code_ir_read_request (Raw_Data oip_binder_query) =
    code_ir_node (nat_of_integer (152 : IntInf.int))
      [code_ir_query oip_binder_query]
  | code_ir_read_request (Operation_Status oip_binder_origin) =
    code_ir_node (nat_of_integer (153 : IntInf.int))
      [code_ir_pair oip_binder_origin]
  | code_ir_read_request Authority_Journal =
    code_ir_node (nat_of_integer (154 : IntInf.int)) []
  | code_ir_read_request (Owner_Data oip_binder_asset) =
    code_ir_node (nat_of_integer (155 : IntInf.int))
      [code_ir_scalar oip_binder_asset];

fun code_ir_parsed_query
  (Wire_Read_Request (oip_binder_proof, oip_binder_request)) =
  code_ir_node (nat_of_integer (13 : IntInf.int))
    [code_ir_session_proof oip_binder_proof,
      code_ir_read_request oip_binder_request]
  | code_ir_parsed_query
    (Wire_Cache_Request (oip_binder_proof, oip_binder_query)) =
    code_ir_node (nat_of_integer (14 : IntInf.int))
      [code_ir_session_proof oip_binder_proof, code_ir_query oip_binder_query];

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

fun json_session_principal
  (Code_json_session_binding_ext
    (json_session_principal, json_session_epoch, more))
  = json_session_principal;

fun json_session_epoch
  (Code_json_session_binding_ext
    (json_session_principal, json_session_epoch, more))
  = json_session_epoch;

fun code_ir_session_binding oip_binder_entry =
  code_ir_node (nat_of_integer (107 : IntInf.int))
    [code_ir_scalar (fst oip_binder_entry),
      code_ir_scalar (json_session_principal (snd oip_binder_entry)),
      code_ir_scalar (json_session_epoch (snd oip_binder_entry))];

fun json_context_write_permissions
  (Code_json_endpoint_context_ext
    (json_context_endpoint, json_context_epoch, json_context_grants,
      json_context_dependencies, json_context_write_permissions, more))
  = json_context_write_permissions;

fun json_context_dependencies
  (Code_json_endpoint_context_ext
    (json_context_endpoint, json_context_epoch, json_context_grants,
      json_context_dependencies, json_context_write_permissions, more))
  = json_context_dependencies;

fun json_context_grants
  (Code_json_endpoint_context_ext
    (json_context_endpoint, json_context_epoch, json_context_grants,
      json_context_dependencies, json_context_write_permissions, more))
  = json_context_grants;

fun json_context_epoch
  (Code_json_endpoint_context_ext
    (json_context_endpoint, json_context_epoch, json_context_grants,
      json_context_dependencies, json_context_write_permissions, more))
  = json_context_epoch;

fun code_ir_dependency oip_binder_dependency =
  code_ir_node (nat_of_integer (109 : IntInf.int))
    [code_ir_scalar (fst oip_binder_dependency),
      code_ir_list code_ir_scalar (snd oip_binder_dependency)];

fun code_ir_context oip_binder_context =
  code_ir_node (nat_of_integer (106 : IntInf.int))
    [code_ir_scalar (json_context_endpoint oip_binder_context),
      code_ir_scalar (json_context_epoch oip_binder_context),
      code_ir_list code_ir_triple (json_context_grants oip_binder_context),
      code_ir_list code_ir_dependency
        (json_context_dependencies oip_binder_context),
      code_ir_list code_ir_triple
        (json_context_write_permissions oip_binder_context)];

fun code_ir_governance
  (Code_Governance_Handover
    (oip_binder_session, oip_binder_selected_cut, oip_binder_asset,
      oip_binder_previous, oip_binder_successor, oip_binder_old_session,
      oip_binder_new_session, oip_binder_epoch, oip_binder_contexts,
      oip_binder_first, oip_binder_second))
  = code_ir_node (nat_of_integer (20 : IntInf.int))
      [code_ir_scalar oip_binder_session, code_ir_cut oip_binder_selected_cut,
        code_ir_scalar oip_binder_asset, code_ir_scalar oip_binder_previous,
        code_ir_scalar oip_binder_successor,
        code_ir_scalar oip_binder_old_session,
        code_ir_scalar oip_binder_new_session, code_ir_scalar oip_binder_epoch,
        code_ir_list code_ir_context oip_binder_contexts,
        code_ir_bytes oip_binder_first, code_ir_bytes oip_binder_second]
  | code_ir_governance
    (Code_Governance_Install
      (oip_binder_session, oip_binder_selected_cut, oip_binder_epoch,
        oip_binder_contexts, oip_binder_sessions, oip_binder_proof))
    = code_ir_node (nat_of_integer (21 : IntInf.int))
        [code_ir_scalar oip_binder_session, code_ir_cut oip_binder_selected_cut,
          code_ir_scalar oip_binder_epoch,
          code_ir_list code_ir_context oip_binder_contexts,
          code_ir_list code_ir_session_binding oip_binder_sessions,
          code_ir_bytes oip_binder_proof];

fun credential_origin
  (Product_lock_credential_ext
    (credential_token, credential_epoch, credential_origin, more))
  = credential_origin;

fun credential_token
  (Product_lock_credential_ext
    (credential_token, credential_epoch, credential_origin, more))
  = credential_token;

fun credential_epoch
  (Product_lock_credential_ext
    (credential_token, credential_epoch, credential_origin, more))
  = credential_epoch;

fun token_generation
  (Product_lock_token_ext (token_asset, token_owner, token_generation, more)) =
  token_generation;

fun token_owner
  (Product_lock_token_ext (token_asset, token_owner, token_generation, more)) =
  token_owner;

fun token_asset
  (Product_lock_token_ext (token_asset, token_owner, token_generation, more)) =
  token_asset;

fun code_ir_credential oip_binder_credential =
  let
    val oip_binder_token = credential_token oip_binder_credential;
  in
    code_ir_node (nat_of_integer (101 : IntInf.int))
      [code_ir_scalar (token_asset oip_binder_token),
        code_ir_scalar (token_owner oip_binder_token),
        code_ir_scalar (token_generation oip_binder_token),
        code_ir_scalar (credential_epoch oip_binder_credential),
        code_ir_pair (credential_origin oip_binder_credential)]
  end;

fun code_ir_command (Wire_Reserve oip_binder_value) =
  code_ir_node (nat_of_integer (110 : IntInf.int))
    [code_ir_scalar oip_binder_value]
  | code_ir_command (Wire_Dispatch oip_binder_value) =
    code_ir_node (nat_of_integer (111 : IntInf.int))
      [code_ir_scalar oip_binder_value]
  | code_ir_command (Wire_Debit oip_binder_value) =
    code_ir_node (nat_of_integer (112 : IntInf.int))
      [code_ir_scalar oip_binder_value]
  | code_ir_command (Wire_Cancel oip_binder_value) =
    code_ir_node (nat_of_integer (113 : IntInf.int))
      [code_ir_scalar oip_binder_value]
  | code_ir_command (Wire_Fence oip_binder_value) =
    code_ir_node (nat_of_integer (114 : IntInf.int))
      [code_ir_scalar oip_binder_value]
  | code_ir_command (Wire_Preempt oip_binder_value) =
    code_ir_node (nat_of_integer (115 : IntInf.int))
      [code_ir_scalar oip_binder_value]
  | code_ir_command (Wire_Timeout oip_binder_value) =
    code_ir_node (nat_of_integer (116 : IntInf.int))
      [code_ir_scalar oip_binder_value]
  | code_ir_command
    (Wire_Record_Terminal (oip_binder_kind, oip_binder_reference)) =
    code_ir_node (nat_of_integer (117 : IntInf.int))
      [code_ir_scalar oip_binder_kind, code_ir_scalar oip_binder_reference]
  | code_ir_command (Wire_Deliver oip_binder_reference) =
    code_ir_node (nat_of_integer (118 : IntInf.int))
      [code_ir_scalar oip_binder_reference]
  | code_ir_command (Wire_Refund (oip_binder_generation, oip_binder_reference))
    = code_ir_node (nat_of_integer (119 : IntInf.int))
        [code_ir_scalar oip_binder_generation,
          code_ir_scalar oip_binder_reference]
  | code_ir_command
    (Wire_Reconcile (oip_binder_generation, oip_binder_reference)) =
    code_ir_node (nat_of_integer (120 : IntInf.int))
      [code_ir_scalar oip_binder_generation,
        code_ir_scalar oip_binder_reference]
  | code_ir_command (Wire_Write (oip_binder_generation, oip_binder_value)) =
    code_ir_node (nat_of_integer (121 : IntInf.int))
      [code_ir_scalar oip_binder_generation, code_ir_scalar oip_binder_value]
  | code_ir_command Wire_Publish =
    code_ir_node (nat_of_integer (122 : IntInf.int)) [];

fun code_typed_ordinary_ir oip_binder_core =
  (case code_decode_ordinary oip_binder_core of Code_Ordinary_Refused _ => NONE
    | Code_Ordinary_Ready
        (oip_binder_native, oip_binder_credential, oip_binder_versions,
          oip_binder_command)
      => SOME (code_ir_node (nat_of_integer (10 : IntInf.int))
                [code_ir_native oip_binder_core oip_binder_native,
                  code_ir_option code_ir_credential oip_binder_credential,
                  code_ir_list code_ir_pair oip_binder_versions,
                  code_ir_command oip_binder_command,
                  code_ir_list code_ir_bytes
                    (native_proof_bytes oip_binder_native)]));

fun capability_atomicities
  (Code_raw_capability_offer_ext
    (capability_deployment, capability_sender, capability_receiver,
      capability_challenge, capability_expires, capability_versions,
      capability_families, capability_atomicities, capability_schemes, more))
  = capability_atomicities;

fun capability_deployment
  (Code_raw_capability_offer_ext
    (capability_deployment, capability_sender, capability_receiver,
      capability_challenge, capability_expires, capability_versions,
      capability_families, capability_atomicities, capability_schemes, more))
  = capability_deployment;

fun capability_challenge
  (Code_raw_capability_offer_ext
    (capability_deployment, capability_sender, capability_receiver,
      capability_challenge, capability_expires, capability_versions,
      capability_families, capability_atomicities, capability_schemes, more))
  = capability_challenge;

fun capability_versions
  (Code_raw_capability_offer_ext
    (capability_deployment, capability_sender, capability_receiver,
      capability_challenge, capability_expires, capability_versions,
      capability_families, capability_atomicities, capability_schemes, more))
  = capability_versions;

fun capability_receiver
  (Code_raw_capability_offer_ext
    (capability_deployment, capability_sender, capability_receiver,
      capability_challenge, capability_expires, capability_versions,
      capability_families, capability_atomicities, capability_schemes, more))
  = capability_receiver;

fun capability_families
  (Code_raw_capability_offer_ext
    (capability_deployment, capability_sender, capability_receiver,
      capability_challenge, capability_expires, capability_versions,
      capability_families, capability_atomicities, capability_schemes, more))
  = capability_families;

fun capability_schemes
  (Code_raw_capability_offer_ext
    (capability_deployment, capability_sender, capability_receiver,
      capability_challenge, capability_expires, capability_versions,
      capability_families, capability_atomicities, capability_schemes, more))
  = capability_schemes;

fun capability_expires
  (Code_raw_capability_offer_ext
    (capability_deployment, capability_sender, capability_receiver,
      capability_challenge, capability_expires, capability_versions,
      capability_families, capability_atomicities, capability_schemes, more))
  = capability_expires;

fun capability_sender
  (Code_raw_capability_offer_ext
    (capability_deployment, capability_sender, capability_receiver,
      capability_challenge, capability_expires, capability_versions,
      capability_families, capability_atomicities, capability_schemes, more))
  = capability_sender;

fun code_ir_capability oip_binder_offer =
  code_ir_node (nat_of_integer (18 : IntInf.int))
    [code_ir_scalar (capability_deployment oip_binder_offer),
      code_ir_scalar (capability_sender oip_binder_offer),
      code_ir_scalar (capability_receiver oip_binder_offer),
      code_ir_scalar (capability_challenge oip_binder_offer),
      code_ir_scalar (capability_expires oip_binder_offer),
      code_ir_set (capability_versions oip_binder_offer),
      code_ir_set (capability_families oip_binder_offer),
      code_ir_set (capability_atomicities oip_binder_offer),
      code_ir_set (capability_schemes oip_binder_offer)];

fun code_capability_offer core parsed_fields =
  (case parsed_fields
    of Code_Capabilities
         (challenge, expires, versions, families, atomicities, schemes)
      => SOME (Code_raw_capability_offer_ext
                (wire_deployment core, wire_source_domain core,
                  wire_target_domain core, challenge, expires, versions,
                  families, atomicities, schemes, ()))
    | Code_Liveness (_, _) => NONE);

fun code_ir_heartbeat oip_binder_core
  (Code_Capabilities
    (oip_binder_challenge, oip_binder_expires, oip_binder_versions,
      oip_binder_families, oip_binder_atomicities, oip_binder_schemes))
  = map_option code_ir_capability
      (code_capability_offer oip_binder_core
        (Code_Capabilities
          (oip_binder_challenge, oip_binder_expires, oip_binder_versions,
            oip_binder_families, oip_binder_atomicities, oip_binder_schemes)))
  | code_ir_heartbeat oip_binder_core
    (Code_Liveness (oip_binder_challenge, oip_binder_expires)) =
    SOME (code_ir_node (nat_of_integer (19 : IntInf.int))
           [code_ir_scalar oip_binder_challenge,
             code_ir_scalar oip_binder_expires]);

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

fun spend_kind_number
  (Code_spend_fields_ext
    (spend_reference, spend_sender, spend_recipient, spend_kind_number,
      spend_amount, spend_enforcement, spend_proof, more))
  = spend_kind_number;

fun spend_enforcement
  (Code_spend_fields_ext
    (spend_reference, spend_sender, spend_recipient, spend_kind_number,
      spend_amount, spend_enforcement, spend_proof, more))
  = spend_enforcement;

fun spend_reference
  (Code_spend_fields_ext
    (spend_reference, spend_sender, spend_recipient, spend_kind_number,
      spend_amount, spend_enforcement, spend_proof, more))
  = spend_reference;

fun spend_recipient
  (Code_spend_fields_ext
    (spend_reference, spend_sender, spend_recipient, spend_kind_number,
      spend_amount, spend_enforcement, spend_proof, more))
  = spend_recipient;

fun spend_sender
  (Code_spend_fields_ext
    (spend_reference, spend_sender, spend_recipient, spend_kind_number,
      spend_amount, spend_enforcement, spend_proof, more))
  = spend_sender;

fun spend_amount
  (Code_spend_fields_ext
    (spend_reference, spend_sender, spend_recipient, spend_kind_number,
      spend_amount, spend_enforcement, spend_proof, more))
  = spend_amount;

fun spend_proof
  (Code_spend_fields_ext
    (spend_reference, spend_sender, spend_recipient, spend_kind_number,
      spend_amount, spend_enforcement, spend_proof, more))
  = spend_proof;

fun enforcement_appeal_deadline
  (Code_enforcement_fields_ext
    (enforcement_officer, enforcement_jurisdiction, enforcement_basis,
      enforcement_assets, enforcement_prior_seizure,
      enforcement_appeal_deadline, more))
  = enforcement_appeal_deadline;

fun enforcement_prior_seizure
  (Code_enforcement_fields_ext
    (enforcement_officer, enforcement_jurisdiction, enforcement_basis,
      enforcement_assets, enforcement_prior_seizure,
      enforcement_appeal_deadline, more))
  = enforcement_prior_seizure;

fun enforcement_jurisdiction
  (Code_enforcement_fields_ext
    (enforcement_officer, enforcement_jurisdiction, enforcement_basis,
      enforcement_assets, enforcement_prior_seizure,
      enforcement_appeal_deadline, more))
  = enforcement_jurisdiction;

fun enforcement_officer
  (Code_enforcement_fields_ext
    (enforcement_officer, enforcement_jurisdiction, enforcement_basis,
      enforcement_assets, enforcement_prior_seizure,
      enforcement_appeal_deadline, more))
  = enforcement_officer;

fun enforcement_assets
  (Code_enforcement_fields_ext
    (enforcement_officer, enforcement_jurisdiction, enforcement_basis,
      enforcement_assets, enforcement_prior_seizure,
      enforcement_appeal_deadline, more))
  = enforcement_assets;

fun enforcement_basis
  (Code_enforcement_fields_ext
    (enforcement_officer, enforcement_jurisdiction, enforcement_basis,
      enforcement_assets, enforcement_prior_seizure,
      enforcement_appeal_deadline, more))
  = enforcement_basis;

fun code_ir_enforcement oip_binder_order =
  code_ir_node (nat_of_integer (108 : IntInf.int))
    [code_ir_scalar (enforcement_officer oip_binder_order),
      code_ir_scalar (enforcement_jurisdiction oip_binder_order),
      code_ir_scalar (enforcement_basis oip_binder_order),
      code_ir_set (enforcement_assets oip_binder_order),
      code_ir_option code_ir_pair (enforcement_prior_seizure oip_binder_order),
      code_ir_option code_ir_scalar
        (enforcement_appeal_deadline oip_binder_order)];

fun code_ir_spend_fields oip_binder_spend =
  code_ir_node (nat_of_integer (103 : IntInf.int))
    [code_ir_scalar (spend_reference oip_binder_spend),
      code_ir_scalar (spend_sender oip_binder_spend),
      code_ir_scalar (spend_recipient oip_binder_spend),
      code_ir_scalar (spend_kind_number oip_binder_spend),
      code_ir_scalar (spend_amount oip_binder_spend),
      code_ir_option code_ir_enforcement (spend_enforcement oip_binder_spend),
      code_ir_option code_ir_bytes (spend_proof oip_binder_spend)];

fun code_typed_spend_ir oip_binder_core =
  (case code_decode_spend oip_binder_core of Code_Spend_Refused _ => NONE
    | Code_Spend_Ready (oip_binder_native, oip_binder_spend) =>
      SOME (code_ir_node (nat_of_integer (12 : IntInf.int))
             [code_ir_native oip_binder_core oip_binder_native,
               code_ir_spend_fields oip_binder_spend]));

fun legal_appeal_deadline
  (Code_legal_fields_ext
    (legal_action_number, legal_officer, legal_jurisdiction, legal_basis,
      legal_issuance_epoch, legal_scope, legal_predecessor, legal_destination,
      legal_appeal_deadline, more))
  = legal_appeal_deadline;

fun legal_action_number
  (Code_legal_fields_ext
    (legal_action_number, legal_officer, legal_jurisdiction, legal_basis,
      legal_issuance_epoch, legal_scope, legal_predecessor, legal_destination,
      legal_appeal_deadline, more))
  = legal_action_number;

fun legal_jurisdiction
  (Code_legal_fields_ext
    (legal_action_number, legal_officer, legal_jurisdiction, legal_basis,
      legal_issuance_epoch, legal_scope, legal_predecessor, legal_destination,
      legal_appeal_deadline, more))
  = legal_jurisdiction;

fun legal_predecessor
  (Code_legal_fields_ext
    (legal_action_number, legal_officer, legal_jurisdiction, legal_basis,
      legal_issuance_epoch, legal_scope, legal_predecessor, legal_destination,
      legal_appeal_deadline, more))
  = legal_predecessor;

fun legal_destination
  (Code_legal_fields_ext
    (legal_action_number, legal_officer, legal_jurisdiction, legal_basis,
      legal_issuance_epoch, legal_scope, legal_predecessor, legal_destination,
      legal_appeal_deadline, more))
  = legal_destination;

fun legal_officer
  (Code_legal_fields_ext
    (legal_action_number, legal_officer, legal_jurisdiction, legal_basis,
      legal_issuance_epoch, legal_scope, legal_predecessor, legal_destination,
      legal_appeal_deadline, more))
  = legal_officer;

fun legal_scope
  (Code_legal_fields_ext
    (legal_action_number, legal_officer, legal_jurisdiction, legal_basis,
      legal_issuance_epoch, legal_scope, legal_predecessor, legal_destination,
      legal_appeal_deadline, more))
  = legal_scope;

fun legal_basis
  (Code_legal_fields_ext
    (legal_action_number, legal_officer, legal_jurisdiction, legal_basis,
      legal_issuance_epoch, legal_scope, legal_predecessor, legal_destination,
      legal_appeal_deadline, more))
  = legal_basis;

fun code_ir_legal_fields oip_binder_order =
  code_ir_node (nat_of_integer (102 : IntInf.int))
    [code_ir_scalar (legal_action_number oip_binder_order),
      code_ir_scalar (legal_officer oip_binder_order),
      code_ir_scalar (legal_jurisdiction oip_binder_order),
      code_ir_scalar (legal_basis oip_binder_order),
      code_ir_scalar (legal_issuance_epoch oip_binder_order),
      code_ir_set (legal_scope oip_binder_order),
      code_ir_option code_ir_pair (legal_predecessor oip_binder_order),
      code_ir_option code_ir_scalar (legal_destination oip_binder_order),
      code_ir_option code_ir_scalar (legal_appeal_deadline oip_binder_order)];

fun code_typed_legal_ir oip_binder_core =
  (case code_decode_legal oip_binder_core of Code_Legal_Refused _ => NONE
    | Code_Legal_Ready
        (oip_binder_native, oip_binder_stage, oip_binder_order,
          oip_binder_proof)
      => SOME (code_ir_node (nat_of_integer (11 : IntInf.int))
                [code_ir_native oip_binder_core oip_binder_native,
                  code_ir_scalar
                    (case oip_binder_stage of Code_Source_Emission => zero_nata
                      | Code_Receiving_Commit => one_nata),
                  code_ir_legal_fields oip_binder_order,
                  code_ir_bytes oip_binder_proof]));

fun code_response_commit_matches position revision =
  (case position of NONE => true
    | SOME retained => equal_nata retained revision);

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

fun code_response_tree_finish core nested decoded =
  (case response_result_words (wire_words (wire_operation_body core))
    of NONE => Code_Tree_Refused Invalid_Wire_Format
    | SOME (call_id, (kind, (_, position))) =>
      (if not (equal_reference_response_kind kind Recorded_Result) andalso
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

fun scheduled_ack_destination
  (Native_scheduled_ack_ext
    (scheduled_ack_key, scheduled_ack_target, scheduled_ack_asset,
      scheduled_ack_owner, scheduled_ack_destination, scheduled_ack_recipient,
      scheduled_ack_amount, scheduled_ack_epoch, scheduled_ack_kind, more))
  = scheduled_ack_destination;

fun scheduled_ack_recipient
  (Native_scheduled_ack_ext
    (scheduled_ack_key, scheduled_ack_target, scheduled_ack_asset,
      scheduled_ack_owner, scheduled_ack_destination, scheduled_ack_recipient,
      scheduled_ack_amount, scheduled_ack_epoch, scheduled_ack_kind, more))
  = scheduled_ack_recipient;

fun scheduled_ack_target
  (Native_scheduled_ack_ext
    (scheduled_ack_key, scheduled_ack_target, scheduled_ack_asset,
      scheduled_ack_owner, scheduled_ack_destination, scheduled_ack_recipient,
      scheduled_ack_amount, scheduled_ack_epoch, scheduled_ack_kind, more))
  = scheduled_ack_target;

fun scheduled_ack_amount
  (Native_scheduled_ack_ext
    (scheduled_ack_key, scheduled_ack_target, scheduled_ack_asset,
      scheduled_ack_owner, scheduled_ack_destination, scheduled_ack_recipient,
      scheduled_ack_amount, scheduled_ack_epoch, scheduled_ack_kind, more))
  = scheduled_ack_amount;

fun scheduled_ack_owner
  (Native_scheduled_ack_ext
    (scheduled_ack_key, scheduled_ack_target, scheduled_ack_asset,
      scheduled_ack_owner, scheduled_ack_destination, scheduled_ack_recipient,
      scheduled_ack_amount, scheduled_ack_epoch, scheduled_ack_kind, more))
  = scheduled_ack_owner;

fun scheduled_ack_epoch
  (Native_scheduled_ack_ext
    (scheduled_ack_key, scheduled_ack_target, scheduled_ack_asset,
      scheduled_ack_owner, scheduled_ack_destination, scheduled_ack_recipient,
      scheduled_ack_amount, scheduled_ack_epoch, scheduled_ack_kind, more))
  = scheduled_ack_epoch;

fun scheduled_ack_asset
  (Native_scheduled_ack_ext
    (scheduled_ack_key, scheduled_ack_target, scheduled_ack_asset,
      scheduled_ack_owner, scheduled_ack_destination, scheduled_ack_recipient,
      scheduled_ack_amount, scheduled_ack_epoch, scheduled_ack_kind, more))
  = scheduled_ack_asset;

fun scheduled_ack_kind
  (Native_scheduled_ack_ext
    (scheduled_ack_key, scheduled_ack_target, scheduled_ack_asset,
      scheduled_ack_owner, scheduled_ack_destination, scheduled_ack_recipient,
      scheduled_ack_amount, scheduled_ack_epoch, scheduled_ack_kind, more))
  = scheduled_ack_kind;

fun scheduled_ack_key
  (Native_scheduled_ack_ext
    (scheduled_ack_key, scheduled_ack_target, scheduled_ack_asset,
      scheduled_ack_owner, scheduled_ack_destination, scheduled_ack_recipient,
      scheduled_ack_amount, scheduled_ack_epoch, scheduled_ack_kind, more))
  = scheduled_ack_key;

fun code_ir_ack oip_binder_ack =
  code_ir_node (nat_of_integer (17 : IntInf.int))
    [code_ir_node (nat_of_integer (105 : IntInf.int))
       [code_ir_pair (fst (scheduled_ack_key oip_binder_ack)),
         code_ir_scalar (snd (scheduled_ack_key oip_binder_ack)),
         code_ir_scalar (scheduled_ack_target oip_binder_ack),
         code_ir_scalar (scheduled_ack_asset oip_binder_ack),
         code_ir_scalar (scheduled_ack_owner oip_binder_ack),
         code_ir_scalar (scheduled_ack_destination oip_binder_ack),
         code_ir_scalar (scheduled_ack_recipient oip_binder_ack),
         code_ir_scalar (scheduled_ack_amount oip_binder_ack),
         code_ir_scalar (scheduled_ack_epoch oip_binder_ack),
         code_ir_scalar
           (case scheduled_ack_kind oip_binder_ack
             of Confirmed_Decision => one_nata
             | Reversed_Decision => nat_of_integer (2 : IntInf.int))]];

fun code_typed_operand_ir oip_binder_depth oip_binder_core =
  (if equal_nata oip_binder_depth zero_nata then NONE
    else (case code_decode_operand_tree oip_binder_depth oip_binder_core
           of Code_Tree_Refused _ => NONE
           | Code_Tree_Ready _ =>
             let
               val oip_binder_body = wire_operation_body oip_binder_core;
               val oip_binder_family = wire_message_family oip_binder_core;
               val oip_binder_operation = wire_opcode oip_binder_body;
             in
               (if equal_wire_familya oip_binder_family Wire_State_Sync andalso
                     equal_nata oip_binder_operation
                       (nat_of_integer (6 : IntInf.int)) orelse
                     equal_wire_familya oip_binder_family
                       Wire_Regulatory andalso
                       equal_nata oip_binder_operation
                         (nat_of_integer (3 : IntInf.int))
                 then code_typed_spend_ir oip_binder_core
                 else (if member equal_wire_family oip_binder_family
                            (insert equal_wire_family Wire_State_Sync
                              (insert equal_wire_family Wire_Lock bot_set))
                        then code_typed_ordinary_ir oip_binder_core
                        else (if equal_wire_familya oip_binder_family
                                   Wire_Regulatory
                               then code_typed_legal_ir oip_binder_core
                               else (if equal_wire_familya oip_binder_family
  Wire_Query
                                      then (if equal_nata oip_binder_operation
         (nat_of_integer (8 : IntInf.int))
     then (case (wire_words oip_binder_body, wire_blobs oip_binder_body)
            of ([], _) => NONE | ([_], []) => NONE
            | ([oip_binder_session], [oip_binder_raw]) =>
              bind (decode_wire_core oip_binder_raw)
                (fn oip_binder_original =>
                  map_option
                    (fn oip_binder_typed =>
                      code_ir_node (nat_of_integer (15 : IntInf.int))
                        [code_ir_scalar oip_binder_session,
                          code_ir_bytes (encode_wire_core oip_binder_original),
                          oip_binder_typed])
                    (code_typed_operand_ir
                      (minus_nata oip_binder_depth one_nata)
                      oip_binder_original))
            | ([_], _ :: _ :: _) => NONE | (_ :: _ :: _, _) => NONE)
     else map_option code_ir_parsed_query
            (code_decode_query_nonreceipt oip_binder_core))
                                      else (if equal_wire_familya
         oip_binder_family Wire_Ack
     then (if equal_nata oip_binder_operation (nat_of_integer (2 : IntInf.int))
            then (case wire_blobs oip_binder_body of [] => NONE
                   | [oip_binder_raw] =>
                     bind (decode_wire_core oip_binder_raw)
                       (fn oip_binder_original =>
                         bind (code_typed_operand_ir
                                (minus_nata oip_binder_depth one_nata)
                                oip_binder_original)
                           (fn oip_binder_typed =>
                             map_option
                               (fn (oip_binder_call_id,
                                     (oip_binder_kind,
                                       (oip_binder_number,
 oip_binder_position)))
                                  =>
                                 code_ir_node (nat_of_integer (16 : IntInf.int))
                                   [code_ir_pair oip_binder_call_id,
                                     code_ir_scalar
                                       (case oip_binder_kind
 of Recorded_Result => one_nata
 | Delivery_Refusal => nat_of_integer (2 : IntInf.int)
 | Validation_Refusal => nat_of_integer (3 : IntInf.int)),
                                     code_ir_scalar oip_binder_number,
                                     code_ir_option code_ir_scalar
                                       oip_binder_position,
                                     code_ir_bytes
                                       (encode_wire_core oip_binder_original),
                                     oip_binder_typed])
                               (response_result_words
                                 (wire_words oip_binder_body))))
                   | _ :: _ :: _ => NONE)
            else map_option code_ir_ack
                   (code_decode_settlement_ack oip_binder_core))
     else (if equal_wire_familya oip_binder_family Wire_Heartbeat
            then bind (code_decode_heartbeat oip_binder_core)
                   (code_ir_heartbeat oip_binder_core)
            else (if equal_wire_familya oip_binder_family Wire_Governance
                   then map_option code_ir_governance
                          (code_decode_governance oip_binder_core)
                   else NONE)))))))
             end
           | Code_Tree_Pending => NONE));

fun sync_v061_operand_ir depth core =
  (if sync_added_operation core then sync_direct_operand_ir depth core
    else code_typed_operand_ir depth core);

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

fun code_transport_refusal prior reason =
  (Code_Transport_Refusal (code_transport_refusal_number reason), prior);

fun code_transport_after_operands operand_check packet max_nesting prior =
  (case operand_check (packet_core packet) max_nesting
    of Code_Operand_Accept =>
      let
        val exact = encode_wire_core (packet_core packet);
      in
        (case code_compare_binding (equal_list equal_nat) prior exact
          of Code_First => (Code_Transport_First, SOME exact)
          | Code_Identical => (Code_Transport_Identical, prior)
          | Code_Replay_Conflict =>
            code_transport_refusal prior Conflicting_Wire_Replay)
      end
    | Code_Operand_Refuse a => code_transport_refusal prior a
    | Code_Operand_Pending => (Code_Transport_Pending, prior));

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

fun sync_transport_oracle operand_check raw authority depth signature_valid
  attestation_valid prior =
  (if not (equal_nata (negotiated_version (boundary_profile authority))
            (nat_of_integer (6 : IntInf.int)))
    then code_transport_refusal prior Unsupported_Wire_Version
    else (case code_check_declared_version raw (boundary_max_frame authority)
           of NONE =>
             (case sync_decode_packet raw
               of NONE => code_transport_refusal prior Invalid_Wire_Format
               | SOME packet =>
                 (case code_admit_packet
                         (fn _ => fn _ => fn _ => signature_valid) packet
                         authority
                   of NONE =>
                     (if not attestation_valid
                       then code_transport_refusal prior Invalid_Wire_Source
                       else code_transport_after_operands operand_check packet
                              depth prior)
                   | SOME a => code_transport_refusal prior a))
           | SOME a => code_transport_refusal prior a));

fun code_integer_reply (Code_Transport_First, binding) =
  ((0 : IntInf.int), map_option (map integer_of_nat) binding)
  | code_integer_reply (Code_Transport_Identical, binding) =
    ((1 : IntInf.int), map_option (map integer_of_nat) binding)
  | code_integer_reply (Code_Transport_Refusal number, binding) =
    (integer_of_nat number, map_option (map integer_of_nat) binding)
  | code_integer_reply (Code_Transport_Pending, binding) =
    ((~1 : IntInf.int), map_option (map integer_of_nat) binding);

fun sync_ack_uses_added_number core =
  (case response_result_words (wire_words (wire_operation_body core))
    of NONE => false
    | SOME (_, (_, (code, _))) =>
      sync_added_status (equal_nat, numeral_nat) code);

fun sync_v061_full_operand_ir depth core =
  (case sync_selected_nested_ir depth core
    of NONE =>
      (if equal_proda equal_wire_family equal_nat (sync_operation core)
            (Wire_Ack, nat_of_integer (2 : IntInf.int)) andalso
            sync_ack_uses_added_number core
        then NONE else sync_v061_operand_ir depth core)
    | SOME (Inl _) => NONE | SOME (Inr a) => SOME a);

fun sync_legacy_ack_new_number depth core =
  (if less_eq_nat depth one_nata orelse
        not (equal_wire_deadline (wire_deadline (wire_operation_body core))
              Deadline_Absent)
    then Code_Operand_Refuse Invalid_Wire_Format
    else (case sync_single_original core
           of NONE => Code_Operand_Refuse Invalid_Wire_Format
           | SOME original =>
             (case code_decode_operand_tree (minus_nata depth one_nata) original
               of Code_Tree_Refused a => Code_Operand_Refuse a
               | Code_Tree_Ready decoded =>
                 (case response_result_words
                         (wire_words (wire_operation_body core))
                   of NONE => Code_Operand_Refuse Invalid_Wire_Format
                   | SOME (_, (kind, (code, position))) =>
                     (if not (equal_reference_response_kind kind
                               Recorded_Result) orelse
                           not (equal_bool (not (is_none position))
                                 (equal_nata code
                                   (nat_of_integer (29 : IntInf.int))))
                       then Code_Operand_Refuse Invalid_Wire_Format
                       else (case code_response_tree_finish core original
                                    decoded
                              of Code_Tree_Refused a => Code_Operand_Refuse a
                              | Code_Tree_Ready _ =>
                                Code_Operand_Refuse Invalid_Wire_Format
                              | Code_Tree_Pending => Code_Operand_Pending)))
               | Code_Tree_Pending => Code_Operand_Pending)));

fun code_transport_operand_verdict core max_nesting =
  (case code_decode_operand_tree max_nesting core
    of Code_Tree_Refused a => Code_Operand_Refuse a
    | Code_Tree_Ready _ => Code_Operand_Accept
    | Code_Tree_Pending => Code_Operand_Pending);

fun sync_v061_operand_verdict core depth =
  (if sync_added_operation core
    then (if is_none (sync_direct_operand_ir depth core)
           then Code_Operand_Refuse Invalid_Wire_Format
           else Code_Operand_Accept)
    else code_transport_operand_verdict core depth);

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

fun code_integer_common_host_values values =
  not (equal_nata (size_list values) (nat_of_integer (13 : IntInf.int))) orelse
    IntInf.< (nth values
                (nat_of_integer
                  (10 : IntInf.int)), power power_integer (2 : IntInf.int)
(nat_of_integer (63 : IntInf.int))) andalso
      IntInf.< (nth values
                  (nat_of_integer
                    (12 : IntInf.int)), power power_integer (2 : IntInf.int)
  (nat_of_integer (63 : IntInf.int)));

fun code_integer_octet_values values =
  list_all
    (fn value =>
      IntInf.<= ((0 : IntInf.int), value) andalso
        IntInf.< (value, (256 : IntInf.int)))
    values;

fun code_ir_transport_key oip_binder_core =
  let
    val (oip_binder_deployment,
          (oip_binder_source, (oip_binder_principal, oip_binder_uuid)))
      = code_transport_key oip_binder_core;
  in
    code_ir_node (nat_of_integer (200 : IntInf.int))
      [code_ir_scalar oip_binder_deployment, code_ir_scalar oip_binder_source,
        code_ir_scalar oip_binder_principal, code_ir_bytes oip_binder_uuid]
  end;

fun sync_typed_value_observation typed_check raw depth =
  bind (sync_decode_packet raw)
    (fn packet =>
      let
        val core = packet_core packet;
      in
        map_option
          (fn typed =>
            (typed,
              (encode_wire_core core,
                (envelope_signing_bytes core, code_ir_transport_key core))))
          (typed_check depth core)
      end);

fun code_integer_u64_values values =
  list_all
    (fn value =>
      IntInf.<= ((0 : IntInf.int), value) andalso
        IntInf.< (value, power power_integer (2 : IntInf.int)
                           (nat_of_integer (64 : IntInf.int))))
    values;

fun sync_transport_flat_values operand_check typed_check bytes values version
  families atomicities schemes critical signature_valid attestation_valid
  prior_present prior =
  (if not (code_integer_octet_values bytes) orelse
        (not (equal_nata (size_list values)
               (nat_of_integer (13 : IntInf.int))) orelse
          (not (code_integer_u64_values
                 (values @ [version] @ families @ atomicities @ schemes)) orelse
            (not (code_integer_common_host_values values) orelse
              prior_present andalso not (code_integer_octet_values prior))))
    then ((~1 : IntInf.int), (false, ([], (false, ([], ([], ([], [])))))))
    else let
           val raw = map nat_of_integer bytes;
           val fields = map nat_of_integer values;
           val depth = nth fields (nat_of_integer (12 : IntInf.int));
           val scope =
             code_contract_boundary fields (nat_of_integer version)
               (map nat_of_integer families) (map nat_of_integer atomicities)
               (map nat_of_integer schemes) critical;
           val saved =
             (if prior_present then SOME (map nat_of_integer prior) else NONE);
           val (number, binding) =
             code_integer_reply
               (sync_transport_oracle operand_check raw scope depth
                 signature_valid attestation_valid saved);
           val present = not (is_none binding);
           val exact = (case binding of NONE => [] | SOME bound => bound);
         in
           (if not ((number : IntInf.int) = (0 : IntInf.int)) andalso
                 not ((number : IntInf.int) = (1 : IntInf.int))
             then (number, (present, (exact, (false, ([], ([], ([], [])))))))
             else (case sync_typed_value_observation typed_check raw depth
                    of NONE =>
                      (number,
                        (present, (exact, (false, ([], ([], ([], [])))))))
                    | SOME (typed, (canonical, (preimage, key))) =>
                      (number,
                        (present,
                          (exact,
                            (true,
                              (map integer_of_nat typed,
                                (map integer_of_nat canonical,
                                  (map integer_of_nat preimage,
                                    map integer_of_nat key)))))))))
         end);

fun sync_v061_full_operand_verdict core depth =
  (case sync_selected_nested_ir depth core
    of NONE =>
      (if equal_proda equal_wire_family equal_nat (sync_operation core)
            (Wire_Ack, nat_of_integer (2 : IntInf.int)) andalso
            sync_ack_uses_added_number core
        then sync_legacy_ack_new_number depth core
        else sync_v061_operand_verdict core depth)
    | SOME (Inl a) => Code_Operand_Refuse a
    | SOME (Inr _) => Code_Operand_Accept);

fun sync_v061_nested_transport_flat x =
  sync_transport_flat_values sync_v061_full_operand_verdict
    sync_v061_full_operand_ir x;

fun sync_v061_typed_model_identity x =
  (fn _ =>
    map (map integer_of_nat o code_json_ascii)
      [[Chara (true, false, false, false, true, true, false, false)],
        [Chara (true, false, false, true, false, true, true, false),
          Chara (false, true, true, true, false, true, true, false),
          Chara (false, false, true, false, true, true, true, false),
          Chara (true, false, false, true, false, true, true, false),
          Chara (false, true, true, true, false, true, true, false),
          Chara (false, true, true, false, false, true, true, false),
          Chara (true, false, true, true, false, true, false, false),
          Chara (true, true, true, false, true, true, true, false),
          Chara (true, false, false, true, false, true, true, false),
          Chara (false, true, false, false, true, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (true, false, true, true, false, true, false, false),
          Chara (false, true, true, false, true, true, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (false, false, true, true, false, true, true, false),
          Chara (true, false, true, false, true, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (true, true, false, false, true, true, true, false),
          Chara (true, false, true, true, false, true, false, false),
          Chara (false, true, true, false, true, true, true, false),
          Chara (false, true, false, false, true, true, false, false)],
        [Chara (true, true, true, false, true, true, true, false),
          Chara (true, false, false, true, false, true, true, false),
          Chara (false, true, false, false, true, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (true, false, true, true, false, true, false, false),
          Chara (false, true, true, false, true, true, true, false),
          Chara (false, true, true, false, true, true, false, false),
          Chara (true, false, true, true, false, true, false, false),
          Chara (true, true, true, false, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (false, true, true, true, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (false, true, false, false, true, true, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (false, false, true, true, false, true, true, false),
          Chara (true, false, true, true, false, true, false, false),
          Chara (true, true, false, false, true, true, false, false),
          Chara (true, true, false, false, true, true, false, false),
          Chara (true, false, true, true, false, true, false, false),
          Chara (false, true, true, false, true, true, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (false, false, true, true, false, true, true, false),
          Chara (true, false, true, false, true, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (true, true, false, false, true, true, true, false)],
        [Chara (true, true, true, true, false, false, true, false),
          Chara (true, false, false, true, false, false, true, false),
          Chara (false, false, false, false, true, false, true, false),
          Chara (true, true, true, true, true, false, true, false),
          Chara (true, true, true, false, true, false, true, false),
          Chara (true, false, false, true, false, true, true, false),
          Chara (false, true, false, false, true, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (true, true, true, true, true, false, true, false),
          Chara (true, true, true, true, false, false, true, false),
          Chara (false, true, false, false, true, true, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (true, true, false, false, false, true, true, false),
          Chara (false, false, true, true, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (true, true, true, true, true, false, true, false),
          Chara (false, true, true, false, true, false, true, false),
          Chara (false, false, false, false, true, true, false, false),
          Chara (false, true, true, false, true, true, false, false),
          Chara (true, false, false, false, true, true, false, false),
          Chara (false, true, true, true, false, true, false, false),
          Chara (true, true, false, false, true, true, true, false),
          Chara (true, false, false, true, true, true, true, false),
          Chara (false, true, true, true, false, true, true, false),
          Chara (true, true, false, false, false, true, true, false),
          Chara (true, true, true, true, true, false, true, false),
          Chara (false, true, true, false, true, true, true, false),
          Chara (false, false, false, false, true, true, false, false),
          Chara (false, true, true, false, true, true, false, false),
          Chara (true, false, false, false, true, true, false, false),
          Chara (true, true, true, true, true, false, true, false),
          Chara (false, true, true, true, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (true, true, false, false, true, true, true, false),
          Chara (false, false, true, false, true, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (true, true, true, true, true, false, true, false),
          Chara (false, false, true, false, true, true, true, false),
          Chara (false, true, false, false, true, true, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (false, true, true, true, false, true, true, false),
          Chara (true, true, false, false, true, true, true, false),
          Chara (false, false, false, false, true, true, true, false),
          Chara (true, true, true, true, false, true, true, false),
          Chara (false, true, false, false, true, true, true, false),
          Chara (false, false, true, false, true, true, true, false),
          Chara (true, true, true, true, true, false, true, false),
          Chara (false, true, true, false, false, true, true, false),
          Chara (false, false, true, true, false, true, true, false),
          Chara (true, false, false, false, false, true, true, false),
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
        [Chara (true, false, true, false, false, true, true, false),
          Chara (true, false, true, false, true, true, false, false),
          Chara (true, true, true, false, true, true, false, false),
          Chara (false, true, false, false, true, true, false, false),
          Chara (false, true, true, false, true, true, false, false),
          Chara (false, false, true, false, true, true, false, false),
          Chara (false, true, true, false, false, true, true, false),
          Chara (false, true, false, false, false, true, true, false),
          Chara (false, false, true, false, true, true, false, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (true, false, false, true, true, true, false, false),
          Chara (false, true, false, false, false, true, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (true, true, false, false, true, true, false, false),
          Chara (false, false, false, false, true, true, false, false),
          Chara (false, true, false, false, true, true, false, false),
          Chara (false, true, true, false, false, true, true, false),
          Chara (false, true, true, false, true, true, false, false),
          Chara (true, true, false, false, false, true, true, false),
          Chara (true, true, false, false, false, true, true, false),
          Chara (false, true, true, false, false, true, true, false),
          Chara (false, false, true, false, true, true, false, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (true, false, false, true, true, true, false, false),
          Chara (true, false, false, false, true, true, false, false),
          Chara (true, true, false, false, true, true, false, false),
          Chara (false, true, true, false, true, true, false, false),
          Chara (false, false, true, false, true, true, false, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (true, true, false, false, true, true, false, false),
          Chara (false, true, false, false, true, true, false, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (true, true, false, false, false, true, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (false, false, true, false, true, true, false, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (true, true, false, false, false, true, true, false),
          Chara (true, false, false, true, true, true, false, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (true, false, false, false, true, true, false, false),
          Chara (false, false, false, false, true, true, false, false),
          Chara (true, false, false, false, false, true, true, false),
          Chara (false, true, true, false, false, true, true, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (false, true, true, false, false, true, true, false),
          Chara (false, false, false, false, true, true, false, false),
          Chara (false, true, false, false, false, true, true, false),
          Chara (false, false, true, false, false, true, true, false),
          Chara (true, false, false, true, true, true, false, false),
          Chara (true, false, true, false, true, true, false, false),
          Chara (false, false, true, false, true, true, false, false),
          Chara (true, false, false, true, true, true, false, false),
          Chara (true, false, true, false, false, true, true, false),
          Chara (false, true, true, false, false, true, true, false),
          Chara (true, true, true, false, true, true, false, false),
          Chara (false, true, false, false, true, true, false, false),
          Chara (true, false, false, true, true, true, false, false),
          Chara (false, true, true, false, false, true, true, false),
          Chara (false, true, true, false, false, true, true, false),
          Chara (false, true, true, false, false, true, true, false),
          Chara (true, false, false, false, true, true, false, false)]])
    x;

end; (*struct OIP_Wire_Oracle_V061*)
