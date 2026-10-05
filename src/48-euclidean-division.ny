export "47-least-number"

def add_cancel_left (k x y : Nat) (p : Id Nat (add k x) (add k y)) : Id Nat x y
  ≔ add_cancel_right k x y
      (concat Nat (add x k) (add k x) (add y k) (add_comm x k)
        (concat Nat (add k x) (add k y) (add y k) p (add_comm k y)))

def le_add_base (a b : Nat) : Le a (add a b) ≔ le_add_left a zero. b star.

def DivisionSpec (n m : Nat) (p : Product Nat Nat) : Type
  ≔ Product (BookLt (p .snd) m) (Id Nat n (add (mul (p .fst) m) (p .snd)))

def DivisionResult (n m : Nat) : Type ≔ Σ (Product Nat Nat) (DivisionSpec n m)

def division_spec_prop (n m : Nat) (p : Product Nat Nat) : isProp (DivisionSpec n m p)
  ≔ product_prop (BookLt (p .snd) m) (Id Nat n (add (mul (p .fst) m) (p .snd)))
      (book_lt_prop (p .snd) m) (nat_set n (add (mul (p .fst) m) (p .snd)))

def division_value_lt (q q' r r' m : Nat) (hq : Lt q q') (hr : Lt r m)
  : Lt (add (mul q m) r) (add (mul q' m) r')
  ≔ lt_le_trans (add (mul q m) r) (add (mul q m) m) (add (mul q' m) r')
      (lt_add_left (mul q m) r m hr)
      (transport Nat (k ↦ Le k (add (mul q' m) r')) (mul (suc. q) m) (add (mul q m) m)
        (mul_suc_left q m)
        (le_trans (mul (suc. q) m) (mul q' m) (add (mul q' m) r')
          (le_mul_right (suc. q) q' m hq) (le_add_base (mul q' m) r')))

def division_quotients_le_equal (n m : Nat) (u v : DivisionResult n m)
  (h : Le (u .fst .fst) (v .fst .fst)) : Id Nat (u .fst .fst) (v .fst .fst)
  ≔ match le_split (u .fst .fst) (v .fst .fst) h [
  | inr. p ↦ p
  | inl. p ↦ absurd (Id Nat (u .fst .fst) (v .fst .fst))
      (lt_not_equal (add (mul (u .fst .fst) m) (u .fst .snd)) (add (mul (v .fst .fst) m) (v .fst .snd))
        (division_value_lt (u .fst .fst) (v .fst .fst) (u .fst .snd) (v .fst .snd) m p
          (lt_from_book (u .fst .snd) m (u .snd .fst)))
        (concat Nat (add (mul (u .fst .fst) m) (u .fst .snd)) n (add (mul (v .fst .fst) m) (v .fst .snd))
          (inverse Nat n (add (mul (u .fst .fst) m) (u .fst .snd)) (u .snd .snd)) (v .snd .snd))) ]

def division_quotients_equal (n m : Nat) (u v : DivisionResult n m) : Id Nat (u .fst .fst) (v .fst .fst)
  ≔ match le_total (u .fst .fst) (v .fst .fst) [
  | inl. h ↦ division_quotients_le_equal n m u v h
  | inr. h ↦ inverse Nat (v .fst .fst) (u .fst .fst) (division_quotients_le_equal n m v u h) ]

def division_remainders_equal (n m : Nat) (u v : DivisionResult n m) : Id Nat (u .fst .snd) (v .fst .snd)
  ≔ add_cancel_left (mul (u .fst .fst) m) (u .fst .snd) (v .fst .snd)
      (calc
        add (mul (u .fst .fst) m) (u .fst .snd) = n by u .snd .snd
        = add (mul (v .fst .fst) m) (v .fst .snd) by v .snd .snd
        = add (mul (u .fst .fst) m) (v .fst .snd)
          by refl ((q ↦ add (mul q m) (v .fst .snd)) : Nat → Nat) (division_quotients_equal n m u v) ∎)

def division_result_prop (n m : Nat) : isProp (DivisionResult n m)
  ≔ u v ↦ subtype_equal (Product Nat Nat) (DivisionSpec n m) (division_spec_prop n m) u v
      (division_quotients_equal n m u v, division_remainders_equal n m u v)

{` A structurally recursive division algorithm; there is no unbounded subtraction loop. `}
def division_step (n m : Nat) (positive : BookLt zero. m) (u : DivisionResult n m)
  (test : Decidable (Id Nat (suc. (u .fst .snd)) m)) : DivisionResult (suc. n) m
  ≔ let q ≔ u .fst .fst in let r ≔ u .fst .snd in
    match test [
    | inl. p ↦ ((suc. q, zero.), (positive,
        calc
          (suc. n : Nat) = suc. (add (mul q m) r) by suc. (u .snd .snd)
          = add (mul q m) m by refl (add (mul q m)) p
          = mul (suc. q) m by mul_suc_left q m ∎))
    | inr. no ↦ ((q, suc. r),
        (lt_to_book (suc. r) m (le_not_equal_lt (suc. r) m (lt_from_book r m (u .snd .fst)) no),
          suc. (u .snd .snd))) ]

def euclidean_division (n m : Nat) (positive : BookLt zero. m) : DivisionResult n m
  ≔ match n [
  | zero. ↦ ((zero., zero.), (positive, inverse Nat (mul zero. m) zero. (mul_zero_left m)))
  | suc. n ↦ let u ≔ euclidean_division n m positive in
      division_step n m positive u (nat_dec_eq (suc. (u .fst .snd)) m) ]

{` lem:euclid-div, including uniqueness of the whole witness with its proofs. `}
def euclidean_division_unique (n m : Nat) (positive : BookLt zero. m) : BookIsContr (DivisionResult n m)
  ≔ (euclidean_division n m positive, division_result_prop n m (euclidean_division n m positive))

def nat_quotient (n m : Nat) (positive : BookLt zero. m) : Nat ≔ euclidean_division n m positive .fst .fst
def nat_remainder (n m : Nat) (positive : BookLt zero. m) : Nat ≔ euclidean_division n m positive .fst .snd
