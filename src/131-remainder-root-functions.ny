export "130-cycle-generating-loops"

{` con:root, initially in the bounded-natural-number presentation of
   Fin(suc n). The literal Fin presentation is transferred below. `}
def root_remainder_decision (n : Nat) (X : Type) (t : X → X) (r : Nat)
  (v : Sum (Lt r n) (Id Nat r n)) (x : X) : Product (Remainder (suc. n)) X
  ≔ match v [
  | inl. small ↦ (remainder_at n (suc. r) small, x)
  | inr. last ↦ (remainder_at n zero. star., t x) ]

def root_remainder (n : Nat) (X : Type) (t : X → X)
  (u : Product (Remainder (suc. n)) X) : Product (Remainder (suc. n)) X
  ≔ root_remainder_decision n X t (u .fst .fst)
      (le_split (u .fst .fst) n (lt_from_book (u .fst .fst) (suc. n) (u .fst .snd))) (u .snd)

def root_remainder_decision_small (n : Nat) (X : Type) (t : X → X) (r : Nat)
  (small : Lt r n) (v : Sum (Lt r n) (Id Nat r n)) (x : X)
  : Id (Product (Remainder (suc. n)) X)
      (root_remainder_decision n X t r v x) (remainder_at n (suc. r) small, x)
  ≔ match v [
  | inl. s ↦ (remainder_equal (suc. n) (remainder_at n (suc. r) s) (remainder_at n (suc. r) small)
      (refl (suc. r)), refl x)
  | inr. p ↦ absurd (Id (Product (Remainder (suc. n)) X)
      (remainder_at n zero. star., t x) (remainder_at n (suc. r) small, x)) (lt_not_equal r n small p) ]

def root_remainder_small (n : Nat) (X : Type) (t : X → X) (r : Remainder (suc. n))
  (small : Lt (r .fst) n) (x : X)
  : Id (Product (Remainder (suc. n)) X)
      (root_remainder n X t (r, x)) (remainder_at n (suc. (r .fst)) small, x)
  ≔ root_remainder_decision_small n X t (r .fst) small
      (le_split (r .fst) n (lt_from_book (r .fst) (suc. n) (r .snd))) x

def root_remainder_decision_last (n : Nat) (X : Type) (t : X → X)
  (v : Sum (Lt n n) (Id Nat n n)) (x : X)
  : Id (Product (Remainder (suc. n)) X)
      (root_remainder_decision n X t n v x) (remainder_at n zero. star., t x)
  ≔ match v [
  | inl. s ↦ absurd (Id (Product (Remainder (suc. n)) X)
      (remainder_at n (suc. n) s, x) (remainder_at n zero. star., t x)) (lt_irrefl n s)
  | inr. p ↦ refl (remainder_at n zero. star., t x) ]

def root_remainder_last (n : Nat) (X : Type) (t : X → X) (x : X)
  : Id (Product (Remainder (suc. n)) X)
      (root_remainder n X t (remainder_at n n (le_refl n), x)) (remainder_at n zero. star., t x)
  ≔ root_remainder_decision_last n X t
      (le_split n n (lt_from_book n (suc. n) (lt_to_book n (suc. n) (le_refl n)))) x

def root_remainder_last_at (n : Nat) (X : Type) (t : X → X) (r : Remainder (suc. n))
  (last : Id Nat (r .fst) n) (x : X)
  : Id (Product (Remainder (suc. n)) X)
      (root_remainder n X t (r, x)) (remainder_at n zero. star., t x)
  ≔ concat (Product (Remainder (suc. n)) X) (root_remainder n X t (r, x))
      (root_remainder n X t (remainder_at n n (le_refl n), x)) (remainder_at n zero. star., t x)
      (map_path (Product (Remainder (suc. n)) X) (Product (Remainder (suc. n)) X)
        (root_remainder n X t) (r, x) (remainder_at n n (le_refl n), x)
        (remainder_equal (suc. n) r (remainder_at n n (le_refl n)) last, refl x))
      (root_remainder_last n X t x)
