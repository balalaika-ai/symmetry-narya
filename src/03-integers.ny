export "02-sets"

{` Chapter 3, section 'The integers': canonical signed representation,
   one of the alternatives in footnote ft:many-integers. neg n = -(n+1).
   The dependent two-zero gluing universal property is proved in module 51.
   The literal HIT's judgmental negative-zero computation is not reproduced. `}
def Int : Type ≔ data [ pos. (_ : Nat) | neg. (_ : Nat) ]
def int_zero : Int ≔ pos. zero.
def int_of_nat (n : Nat) : Int ≔ pos. n

def int_succ : Int → Int ≔ [
  | pos. n ↦ pos. (suc. n)
  | neg. zero. ↦ pos. zero.
  | neg. (suc. n) ↦ neg. n ]

def int_pred : Int → Int ≔ [
  | pos. zero. ↦ neg. zero.
  | pos. (suc. n) ↦ pos. n
  | neg. n ↦ neg. (suc. n) ]

def int_neg : Int → Int ≔ [
  | pos. zero. ↦ pos. zero.
  | pos. (suc. n) ↦ neg. n
  | neg. n ↦ pos. (suc. n) ]

def int_pred_succ (z : Int) : Id Int (int_pred (int_succ z)) z
  ≔ match z [
  | pos. n ↦ refl (pos. n : Int)
  | neg. zero. ↦ refl (neg. zero. : Int)
  | neg. (suc. n) ↦ refl (neg. (suc. n) : Int) ]

def int_succ_pred (z : Int) : Id Int (int_succ (int_pred z)) z
  ≔ match z [
  | pos. zero. ↦ refl (pos. zero. : Int)
  | pos. (suc. n) ↦ refl (pos. (suc. n) : Int)
  | neg. n ↦ refl (neg. n : Int) ]

def int_neg_neg (z : Int) : Id Int (int_neg (int_neg z)) z
  ≔ match z [
  | pos. zero. ↦ refl (pos. zero. : Int)
  | pos. (suc. n) ↦ refl (pos. (suc. n) : Int)
  | neg. n ↦ refl (neg. n : Int) ]

def IntCode (x y : Int) : Type ≔ match x, y [
  | pos. m, pos. n ↦ NatCode m n
  | pos. m, neg. n ↦ Empty
  | neg. m, pos. n ↦ Empty
  | neg. m, neg. n ↦ NatCode m n ]

def int_encode (x y : Int) (p : Id Int x y) : IntCode x y
  ≔ match p [ pos. p ⤇ nat_encode p.0 p.1 p.2 | neg. p ⤇ nat_encode p.0 p.1 p.2 ]

def int_decode (x y : Int) (c : IntCode x y) : Id Int x y
  ≔ match x, y [
  | pos. m, pos. n ↦ pos. (nat_decode m n c)
  | pos. m, neg. n ↦ match c []
  | neg. m, pos. n ↦ match c []
  | neg. m, neg. n ↦ neg. (nat_decode m n c) ]

def int_decode_encode (x y : Int) (p : Id Int x y)
  : Id (Id Int x y) (int_decode x y (int_encode x y p)) p
  ≔ match p [
  | pos. p ⤇ pos. (nat_decode_encode p.0 p.1 p.2)
  | neg. p ⤇ neg. (nat_decode_encode p.0 p.1 p.2) ]

def int_code_prop (x y : Int) : isProp (IntCode x y)
  ≔ match x, y [
  | pos. m, pos. n ↦ nat_code_prop m n
  | pos. m, neg. n ↦ empty_prop
  | neg. m, pos. n ↦ empty_prop
  | neg. m, neg. n ↦ nat_code_prop m n ]

def int_set (x y : Int) : isProp (Id Int x y)
  ≔ retract_prop (IntCode x y) (Id Int x y) (int_code_prop x y)
      (int_decode x y) (int_encode x y) (int_decode_encode x y)

def int_succ_equiv : Equiv Int Int
  ≔ set_iso_equiv Int Int int_set int_succ int_pred int_pred_succ int_succ_pred

def int_neg_equiv : Equiv Int Int
  ≔ set_iso_equiv Int Int int_set int_neg int_neg int_neg_neg int_neg_neg

{` Monodromy of the future universal cover. Transport computes as successor. `}
def int_universe_loop : Id Type Int Int ≔ ua Int Int int_succ_equiv

def int_universe_loop_transport (z : Int)
  : Id Int (int_universe_loop .trr z) (int_succ z)
  ≔ ua_transport Int Int int_succ_equiv z

def int_iterate (A : Type) (f g : A → A) (z : Int) (a : A) : A
  ≔ match z [ pos. n ↦ iterate A f n a | neg. n ↦ iterate A g (suc. n) a ]

def int_add (x y : Int) : Int ≔ int_iterate Int int_succ int_pred y x
