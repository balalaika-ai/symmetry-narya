export "132-root-equivalences"

def iterate_commute (A : Type) (f : A → A) (m n : Nat) (x : A)
  : Id A (iterate A f m (iterate A f n x)) (iterate A f n (iterate A f m x))
  ≔ calc
      iterate A f m (iterate A f n x) = iterate A f (add n m) x by iterate_add A f n m x
      = iterate A f (add m n) x by refl ((k ↦ iterate A f k x) : Nat → A) (add_comm n m)
      = iterate A f n (iterate A f m x) by iterate_add A f m n x ∎

def root_remainder_iterate_small (n r : Nat) (h : Le r n) (X : Type) (t : X → X) (x : X)
  : Id (Product (Remainder (suc. n)) X)
      (iterate (Product (Remainder (suc. n)) X) (root_remainder n X t) r (remainder_at n zero. star., x))
      (remainder_at n r h, x)
  ≔ match r [
  | zero. ↦ (remainder_equal (suc. n) (remainder_at n zero. star.) (remainder_at n zero. h) (refl zero.), refl x)
  | suc. r ↦ calc
      iterate (Product (Remainder (suc. n)) X) (root_remainder n X t) (suc. r) (remainder_at n zero. star., x)
      = root_remainder n X t (remainder_at n r (lt_le r n h), x)
        by refl (root_remainder n X t) (root_remainder_iterate_small n r (lt_le r n h) X t x)
      = (remainder_at n (suc. r) h, x)
        by root_remainder_small n X t (remainder_at n r (lt_le r n h)) h x ∎ ]

def root_remainder_turn_zero (n : Nat) (X : Type) (t : X → X) (x : X)
  : Id (Product (Remainder (suc. n)) X)
      (iterate (Product (Remainder (suc. n)) X) (root_remainder n X t) (suc. n) (remainder_at n zero. star., x))
      (remainder_at n zero. star., t x)
  ≔ calc
      iterate (Product (Remainder (suc. n)) X) (root_remainder n X t) (suc. n) (remainder_at n zero. star., x)
      = root_remainder n X t (remainder_at n n (le_refl n), x)
        by refl (root_remainder n X t) (root_remainder_iterate_small n n (le_refl n) X t x)
      = (remainder_at n zero. star., t x) by root_remainder_last n X t x ∎

{` The unnumbered assertion after con:root: its m-th iterate applies t
   in every copy, for an arbitrary function on an arbitrary type. `}
def root_remainder_full_turn (n : Nat) (X : Type) (t : X → X) (u : Product (Remainder (suc. n)) X)
  : Id (Product (Remainder (suc. n)) X)
      (iterate (Product (Remainder (suc. n)) X) (root_remainder n X t) (suc. n) u) (u .fst, t (u .snd))
  ≔ let R ≔ Product (Remainder (suc. n)) X in let f ≔ root_remainder n X t in
    let r ≔ u .fst .fst in let h ≔ lt_from_book r (suc. n) (u .fst .snd) in
    let at ≔ remainder_at n r h in
    calc
      iterate R f (suc. n) u = iterate R f (suc. n) (at, u .snd)
        by map_path R R (iterate R f (suc. n)) u (at, u .snd)
          (remainder_equal (suc. n) (u .fst) at (refl r), refl (u .snd))
      = iterate R f (suc. n) (iterate R f r (remainder_at n zero. star., u .snd))
        by refl (iterate R f (suc. n)) (root_remainder_iterate_small n r h X t (u .snd))
      = iterate R f r (iterate R f (suc. n) (remainder_at n zero. star., u .snd))
        by iterate_commute R f (suc. n) r (remainder_at n zero. star., u .snd)
      = iterate R f r (remainder_at n zero. star., t (u .snd))
        by refl (iterate R f r) (root_remainder_turn_zero n X t (u .snd))
      = (at, t (u .snd)) by root_remainder_iterate_small n r h X t (t (u .snd))
      = (u .fst, t (u .snd)) by (remainder_equal (suc. n) at (u .fst) (refl r), refl (t (u .snd))) ∎

def root_remainder_multiple_turns (n q : Nat) (X : Type) (t : X → X) (u : Product (Remainder (suc. n)) X)
  : Id (Product (Remainder (suc. n)) X)
      (iterate (Product (Remainder (suc. n)) X) (root_remainder n X t) (mul (suc. n) q) u)
      (u .fst, iterate X t q (u .snd))
  ≔ match q [
  | zero. ↦ refl u
  | suc. q ↦ let R ≔ Product (Remainder (suc. n)) X in let f ≔ root_remainder n X t in
    calc
      iterate R f (mul (suc. n) (suc. q)) u = iterate R f (suc. n) (iterate R f (mul (suc. n) q) u)
        by iterate_add R f (mul (suc. n) q) (suc. n) u
      = iterate R f (suc. n) (u .fst, iterate X t q (u .snd))
        by refl (iterate R f (suc. n)) (root_remainder_multiple_turns n q X t u)
      = (u .fst, iterate X t (suc. q) (u .snd))
        by root_remainder_full_turn n X t (u .fst, iterate X t q (u .snd)) ∎ ]
