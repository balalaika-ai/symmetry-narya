export "131-remainder-root-functions"

def root_remainder_inverse_at (n : Nat) (X : Type) (e : Equiv X X) (r : Nat) (h : Le r n) (x : X)
  : Product (Remainder (suc. n)) X
  ≔ match r [
  | zero. ↦ (remainder_at n n (le_refl n), equiv_inverse_map X X e x)
  | suc. r ↦ (remainder_at n r (lt_le r n h), x) ]

def root_remainder_inverse (n : Nat) (X : Type) (e : Equiv X X)
  (u : Product (Remainder (suc. n)) X) : Product (Remainder (suc. n)) X
  ≔ root_remainder_inverse_at n X e (u .fst .fst)
      (lt_from_book (u .fst .fst) (suc. n) (u .fst .snd)) (u .snd)

def root_remainder_retraction (n : Nat) (X : Type) (e : Equiv X X)
  (u : Product (Remainder (suc. n)) X)
  : Id (Product (Remainder (suc. n)) X)
      (root_remainder_inverse n X e (root_remainder n X (e .map) u)) u
  ≔ match le_split (u .fst .fst) n (lt_from_book (u .fst .fst) (suc. n) (u .fst .snd)) [
  | inl. small ↦ calc
      root_remainder_inverse n X e (root_remainder n X (e .map) u)
      = root_remainder_inverse n X e (remainder_at n (suc. (u .fst .fst)) small, u .snd)
        by refl (root_remainder_inverse n X e) (root_remainder_small n X (e .map) (u .fst) small (u .snd))
      = u by (remainder_equal (suc. n)
        (root_remainder_inverse n X e (remainder_at n (suc. (u .fst .fst)) small, u .snd) .fst)
        (u .fst) (refl (u .fst .fst)), refl (u .snd)) ∎
  | inr. last ↦ calc
      root_remainder_inverse n X e (root_remainder n X (e .map) u)
      = root_remainder_inverse n X e (remainder_at n zero. star., e .map (u .snd))
        by refl (root_remainder_inverse n X e) (root_remainder_last_at n X (e .map) (u .fst) last (u .snd))
      = u by (remainder_equal (suc. n) (remainder_at n n (le_refl n)) (u .fst)
        (inverse Nat (u .fst .fst) n last), equiv_retraction X X e (u .snd)) ∎ ]

def root_remainder_section_at (n : Nat) (X : Type) (e : Equiv X X) (r : Nat) (h : Le r n) (x : X)
  : Id (Product (Remainder (suc. n)) X)
      (root_remainder n X (e .map) (root_remainder_inverse_at n X e r h x)) (remainder_at n r h, x)
  ≔ match r [
  | zero. ↦ calc
      root_remainder n X (e .map) (remainder_at n n (le_refl n), equiv_inverse_map X X e x)
      = (remainder_at n zero. star., e .map (equiv_inverse_map X X e x))
        by root_remainder_last n X (e .map) (equiv_inverse_map X X e x)
      = (remainder_at n zero. h, x)
        by (remainder_equal (suc. n) (remainder_at n zero. star.) (remainder_at n zero. h) (refl zero.),
          equiv_counit X X e x) ∎
  | suc. r ↦ calc
      root_remainder n X (e .map) (remainder_at n r (lt_le r n h), x)
      = (remainder_at n (suc. r) h, x) by root_remainder_small n X (e .map) (remainder_at n r (lt_le r n h)) h x ∎ ]

def root_remainder_section (n : Nat) (X : Type) (e : Equiv X X)
  (u : Product (Remainder (suc. n)) X)
  : Id (Product (Remainder (suc. n)) X)
      (root_remainder n X (e .map) (root_remainder_inverse n X e u)) u
  ≔ concat (Product (Remainder (suc. n)) X)
      (root_remainder n X (e .map) (root_remainder_inverse n X e u))
      (remainder_at n (u .fst .fst) (lt_from_book (u .fst .fst) (suc. n) (u .fst .snd)), u .snd) u
      (root_remainder_section_at n X e (u .fst .fst)
        (lt_from_book (u .fst .fst) (suc. n) (u .fst .snd)) (u .snd))
      (remainder_equal (suc. n)
        (remainder_at n (u .fst .fst) (lt_from_book (u .fst .fst) (suc. n) (u .fst .snd))) (u .fst)
        (refl (u .fst .fst)), refl (u .snd))

{` lem:root-pres-equiv, without a set restriction on X. `}
def root_remainder_equiv (n : Nat) (X : Type) (e : Equiv X X)
  : Equiv (Product (Remainder (suc. n)) X) (Product (Remainder (suc. n)) X)
  ≔ quasi_inverse_equiv (Product (Remainder (suc. n)) X) (Product (Remainder (suc. n)) X)
      (root_remainder n X (e .map)) (root_remainder_inverse n X e)
      (root_remainder_retraction n X e) (root_remainder_section n X e)
