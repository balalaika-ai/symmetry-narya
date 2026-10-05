export "74-finite-period-cycles"

def remainder_set (m : Nat) : isSet (Remainder m)
  ≔ sigma_set Nat (r ↦ BookLt r m) nat_set (r ↦ prop_is_set (BookLt r m) (book_lt_prop r m))

def remainder_at (n r : Nat) (h : Le r n) : Remainder (suc. n)
  ≔ (r, lt_to_book r (suc. n) h)

def remainder_equal (m : Nat) (r s : Remainder m) (p : Id Nat (r .fst) (s .fst)) : Id (Remainder m) r s
  ≔ subtype_equal Nat (r ↦ BookLt r m) (r ↦ book_lt_prop r m) r s p

def modular_successor (n : Nat) (r : Remainder (suc. n)) : Remainder (suc. n)
  ≔ integer_digits (suc. n) (lt_to_book zero. (suc. n) star.) (pos. (suc. (r .fst))) .fst

def modular_successor_small (n r : Nat) (h : Lt r n) (hr : Le r n)
  : Id (Remainder (suc. n)) (modular_successor n (remainder_at n r hr)) (remainder_at n (suc. r) h)
  ≔ let u ≔ integer_euclidean_division (pos. (suc. r)) (suc. n) (lt_to_book zero. (suc. n) star.) in
    let v : IntegerDivisionResult (pos. (suc. r)) (suc. n) ≔
      ((int_zero, suc. r), (lt_to_book (suc. r) (suc. n) h,
        inverse Int (integer_division_value int_zero (suc. r) (suc. n)) (pos. (suc. r))
          (integer_division_zero_quotient (suc. r) (suc. n)))) in
    remainder_equal (suc. n) (modular_successor n (remainder_at n r hr)) (remainder_at n (suc. r) h)
      (integer_division_result_prop (pos. (suc. r)) (suc. n) u v .fst .snd)

def integer_division_one_zero (m : Nat) : Id Int (integer_division_value (pos. (suc. zero.)) zero. m) (pos. m)
  ≔ calc
      integer_division_value (pos. (suc. zero.)) zero. m = pos. (mul (suc. zero.) m)
        by integer_division_value_pos (suc. zero.) zero. m
      = pos. (add (mul zero. m) m) by map_path Nat Int (q ↦ pos. q) (mul (suc. zero.) m) (add (mul zero. m) m) (mul_suc_left zero. m)
      = pos. (add zero. m) by refl ((q ↦ (pos. (add q m) : Int)) : Nat → Int) (mul_zero_left m)
      = pos. m by map_path Nat Int (q ↦ pos. q) (add zero. m) m (add_zero_left m) ∎

def modular_successor_last (n : Nat)
  : Id (Remainder (suc. n)) (modular_successor n (remainder_at n n (le_refl n))) (remainder_at n zero. star.)
  ≔ let u ≔ integer_euclidean_division (pos. (suc. n)) (suc. n) (lt_to_book zero. (suc. n) star.) in
    let v : IntegerDivisionResult (pos. (suc. n)) (suc. n) ≔
      ((pos. (suc. zero.), zero.), (lt_to_book zero. (suc. n) star.,
        inverse Int (integer_division_value (pos. (suc. zero.)) zero. (suc. n)) (pos. (suc. n))
          (integer_division_one_zero (suc. n)))) in
    remainder_equal (suc. n) (modular_successor n (remainder_at n n (le_refl n))) (remainder_at n zero. star.)
      (integer_division_result_prop (pos. (suc. n)) (suc. n) u v .fst .snd)

def modular_predecessor_at (n r : Nat) (h : Le r n) : Remainder (suc. n)
  ≔ match r [
  | zero. ↦ remainder_at n n (le_refl n)
  | suc. r ↦ remainder_at n r (lt_le r n h) ]

def modular_predecessor (n : Nat) (r : Remainder (suc. n)) : Remainder (suc. n)
  ≔ modular_predecessor_at n (r .fst) (lt_from_book (r .fst) (suc. n) (r .snd))

def modular_successor_predecessor_at (n r : Nat) (h : Le r n)
  : Id (Remainder (suc. n)) (modular_successor n (modular_predecessor_at n r h)) (remainder_at n r h)
  ≔ match r [
  | zero. ↦ remainder_equal (suc. n) (modular_successor n (remainder_at n n (le_refl n))) (remainder_at n zero. h)
      (modular_successor_last n .fst)
  | suc. r ↦ modular_successor_small n r h (lt_le r n h) ]

def modular_successor_predecessor (n : Nat) (r : Remainder (suc. n))
  : Id (Remainder (suc. n)) (modular_successor n (modular_predecessor n r)) r
  ≔ remainder_equal (suc. n) (modular_successor n (modular_predecessor n r)) r
      (modular_successor_predecessor_at n (r .fst) (lt_from_book (r .fst) (suc. n) (r .snd)) .fst)

def modular_predecessor_successor (n : Nat) (r : Remainder (suc. n))
  : Id (Remainder (suc. n)) (modular_predecessor n (modular_successor n r)) r
  ≔ let h ≔ lt_from_book (r .fst) (suc. n) (r .snd) in
    let at ≔ remainder_at n (r .fst) h in
    let eq ≔ remainder_equal (suc. n) r at (refl (r .fst)) in
    match le_split (r .fst) n h [
    | inl. small ↦ calc
        modular_predecessor n (modular_successor n r) = modular_predecessor n (modular_successor n at)
          by refl ((s ↦ modular_predecessor n (modular_successor n s)) : Remainder (suc. n) → Remainder (suc. n)) eq
        = modular_predecessor n (remainder_at n (suc. (r .fst)) small)
          by refl (modular_predecessor n) (modular_successor_small n (r .fst) small h)
        = r by remainder_equal (suc. n) (modular_predecessor n (remainder_at n (suc. (r .fst)) small)) r (refl (r .fst)) ∎
    | inr. last ↦ calc
        modular_predecessor n (modular_successor n r) = modular_predecessor n (modular_successor n (remainder_at n n (le_refl n)))
          by refl ((s ↦ modular_predecessor n (modular_successor n s)) : Remainder (suc. n) → Remainder (suc. n))
            (remainder_equal (suc. n) r (remainder_at n n (le_refl n)) last)
        = modular_predecessor n (remainder_at n zero. star.) by refl (modular_predecessor n) (modular_successor_last n)
        = r by remainder_equal (suc. n) (modular_predecessor n (remainder_at n zero. star.)) r (inverse Nat (r .fst) n last) ∎ ]

def modular_successor_equiv (n : Nat) : Equiv (Remainder (suc. n)) (Remainder (suc. n))
  ≔ quasi_inverse_equiv (Remainder (suc. n)) (Remainder (suc. n)) (modular_successor n) (modular_predecessor n)
      (modular_predecessor_successor n) (modular_successor_predecessor n)

def modular_successor_iterate (n r : Nat) (h : Le r n)
  : Id (Remainder (suc. n)) (iterate (Remainder (suc. n)) (modular_successor n) r (remainder_at n zero. star.)) (remainder_at n r h)
  ≔ match r [
  | zero. ↦ remainder_equal (suc. n) (remainder_at n zero. star.) (remainder_at n zero. h) (refl zero.)
  | suc. r ↦ concat (Remainder (suc. n))
      (modular_successor n (iterate (Remainder (suc. n)) (modular_successor n) r (remainder_at n zero. star.)))
      (modular_successor n (remainder_at n r (lt_le r n h))) (remainder_at n (suc. r) h)
      (refl (modular_successor n) (modular_successor_iterate n r (lt_le r n h)))
      (modular_successor_small n r h (lt_le r n h)) ]

def modular_successor_cyclic (n : Nat) : Cyclic (Remainder (suc. n)) (modular_successor_equiv n)
  ≔ cyclic_from_orbit_surjective (Remainder (suc. n)) (modular_successor_equiv n) (remainder_at n zero. star.)
      (r ↦ mere (BookFiber Int (Remainder (suc. n))
        (z ↦ permutation_power (Remainder (suc. n)) (modular_successor_equiv n) z (remainder_at n zero. star.)) r)
        (pos. (r .fst), inverse (Remainder (suc. n))
          (permutation_power (Remainder (suc. n)) (modular_successor_equiv n) (pos. (r .fst)) (remainder_at n zero. star.)) r
          (remainder_equal (suc. n)
            (permutation_power (Remainder (suc. n)) (modular_successor_equiv n) (pos. (r .fst)) (remainder_at n zero. star.)) r
            (modular_successor_iterate n (r .fst) (lt_from_book (r .fst) (suc. n) (r .snd)) .fst))))

def finite_standard_cycle (n : Nat) : Cycles
  ≔ (((Remainder (suc. n), remainder_set (suc. n)), modular_successor_equiv n), modular_successor_cyclic n)
