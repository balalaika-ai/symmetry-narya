export "03-integers"
export "04-path-algebra"

{` Negative information is obtained by encoding native identity paths. `}
def nat_zero_ne_suc (n : Nat) (p : Id Nat zero. (suc. n)) : Empty
  ≔ nat_encode zero. (suc. n) p

def nat_pred : Nat → Nat ≔ [ zero. ↦ zero. | suc. n ↦ n ]

def nat_dec_eq (m n : Nat) : Decidable (Id Nat m n)
  ≔ match m, n [
  | zero., zero. ↦ inl. (refl (zero. : Nat))
  | zero., suc. n ↦ inr. (nat_zero_ne_suc n)
  | suc. m, zero. ↦ inr. (p ↦ nat_encode (suc. m) zero. p)
  | suc. m, suc. n ↦ match nat_dec_eq m n [
    | inl. p ↦ inl. (suc. p)
    | inr. no ↦ inr. (p ↦ no (refl nat_pred p)) ] ]

def int_magnitude : Int → Nat ≔ [ pos. n ↦ n | neg. n ↦ n ]

def int_dec_eq (x y : Int) : Decidable (Id Int x y)
  ≔ match x, y [
  | pos. m, pos. n ↦ match nat_dec_eq m n [
    | inl. p ↦ inl. (pos. p)
    | inr. no ↦ inr. (p ↦ no (refl int_magnitude p)) ]
  | pos. m, neg. n ↦ inr. (p ↦ int_encode (pos. m) (neg. n) p)
  | neg. m, pos. n ↦ inr. (p ↦ int_encode (neg. m) (pos. n) p)
  | neg. m, neg. n ↦ match nat_dec_eq m n [
    | inl. p ↦ inl. (neg. p)
    | inr. no ↦ inr. (p ↦ no (refl int_magnitude p)) ] ]

def Le (m n : Nat) : Type ≔ match m, n [
  | zero., n ↦ Unit
  | suc. m, zero. ↦ Empty
  | suc. m, suc. n ↦ Le m n ]

def le_refl (n : Nat) : Le n n
  ≔ match n [ zero. ↦ star. | suc. n ↦ le_refl n ]

def le_prop (m n : Nat) : isProp (Le m n)
  ≔ match m, n [
  | zero., n ↦ unit_prop
  | suc. m, zero. ↦ empty_prop
  | suc. m, suc. n ↦ le_prop m n ]

def le_decidable (m n : Nat) : Decidable (Le m n)
  ≔ match m, n [
  | zero., n ↦ inl. star.
  | suc. m, zero. ↦ inr. (x ↦ x)
  | suc. m, suc. n ↦ le_decidable m n ]

def le_trans (a b c : Nat) (p : Le a b) (q : Le b c) : Le a c
  ≔ match a, b, c [
  | zero., b, c ↦ star.
  | suc. a, zero., c ↦ match p []
  | suc. a, suc. b, zero. ↦ match q []
  | suc. a, suc. b, suc. c ↦ le_trans a b c p q ]

def le_antisym (m n : Nat) (p : Le m n) (q : Le n m) : Id Nat m n
  ≔ match m, n [
  | zero., zero. ↦ refl (zero. : Nat)
  | zero., suc. n ↦ match q []
  | suc. m, zero. ↦ match p []
  | suc. m, suc. n ↦ suc. (le_antisym m n p q) ]

def le_total (m n : Nat) : Sum (Le m n) (Le n m)
  ≔ match m, n [
  | zero., n ↦ inl. star.
  | suc. m, zero. ↦ inr. star.
  | suc. m, suc. n ↦ le_total m n ]

{` Genuine nontriviality of the univalence loop, observed at zero.
   This also checks that the integer family cannot be replaced by a
   constant family while preserving the supplied monodromy. `}
def int_universe_loop_nontrivial
  (p : Id (Id Type Int Int) int_universe_loop (refl Int)) : Empty
  ≔ int_encode (pos. (suc. zero.)) int_zero
      (concat Int (pos. (suc. zero.)) (refl Int .trr int_zero) int_zero
        (refl ((q ↦ q .trr int_zero) : Id Type Int Int → Int) p)
        (transport_refl Type (X ↦ X) Int int_zero))
