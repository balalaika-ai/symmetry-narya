export "54-integer-order"

def integer_division_value (q : Int) (r m : Nat) : Int
  ≔ int_add (int_mul q (pos. m)) (pos. r)

def IntegerDivisionSpec (z : Int) (m : Nat) (p : Product Int Nat) : Type
  ≔ Product (BookLt (p .snd) m) (Id Int z (integer_division_value (p .fst) (p .snd) m))
def IntegerDivisionResult (z : Int) (m : Nat) : Type
  ≔ Σ (Product Int Nat) (IntegerDivisionSpec z m)

def integer_division_spec_prop (z : Int) (m : Nat) (p : Product Int Nat)
  : isProp (IntegerDivisionSpec z m p)
  ≔ product_prop (BookLt (p .snd) m) (Id Int z (integer_division_value (p .fst) (p .snd) m))
      (book_lt_prop (p .snd) m) (int_set z (integer_division_value (p .fst) (p .snd) m))

def integer_division_value_formula (q : Int) (r m : Nat)
  : Id Int (integer_division_value q r m)
      (int_difference (add (mul (int_balance q .fst) m) r) (mul (int_balance q .snd) m))
  ≔ calc
      integer_division_value q r m
      = iterate Int int_succ r (balance_value (balance_mul (int_balance q) (m, zero.)))
        by refl (iterate Int int_succ r) (int_mul_balance q (pos. m))
      = iterate Int int_succ r (balance_value (balance_scale (int_balance q) m))
        by refl ((p ↦ iterate Int int_succ r (balance_value p)) : Balance → Int)
          (balance_mul_positive (int_balance q) m)
      = int_difference (add (mul (int_balance q .fst) m) r) (mul (int_balance q .snd) m)
        by iterate_succ_difference (mul (int_balance q .fst) m) (mul (int_balance q .snd) m) r ∎

def integer_division_value_pos (q r m : Nat)
  : Id Int (integer_division_value (pos. q) r m) (pos. (add (mul q m) r))
  ≔ calc
      integer_division_value (pos. q) r m = int_difference (add (mul q m) r) (mul zero. m)
        by integer_division_value_formula (pos. q) r m
      = pos. (add (mul q m) r) by refl (int_difference (add (mul q m) r)) (mul_zero_left m) ∎

def integer_division_value_neg (q r m : Nat)
  : Id Int (integer_division_value (neg. q) r m) (int_difference r (mul (suc. q) m))
  ≔ calc
      integer_division_value (neg. q) r m = int_difference (add (mul zero. m) r) (mul (suc. q) m)
        by integer_division_value_formula (neg. q) r m
      = int_difference (add zero. r) (mul (suc. q) m)
        by refl ((w ↦ int_difference (add w r) (mul (suc. q) m)) : Nat → Int) (mul_zero_left m)
      = int_difference r (mul (suc. q) m)
        by refl ((w ↦ int_difference w (mul (suc. q) m)) : Nat → Int) (add_zero_left r) ∎

def negative_division_relation (n q r m k : Nat)
  (hn : Id Nat n (add (mul q m) r)) (hk : Id Nat (add k (suc. r)) m)
  : SameBalance (k, mul (suc. q) m) (zero., suc. n)
  ≔ calc
      add k (suc. n) = add k (add (mul q m) (suc. r))
        by map_path Nat Nat (add k) (suc. n) (suc. (add (mul q m) r)) (suc. hn)
      = add (add k (mul q m)) (suc. r) by add_assoc k (mul q m) (suc. r)
      = add (add (mul q m) k) (suc. r)
        by refl ((w ↦ add w (suc. r)) : Nat → Nat) (add_comm k (mul q m))
      = add (mul q m) (add k (suc. r)) by add_assoc (mul q m) k (suc. r)
      = add (mul q m) m by refl (add (mul q m)) hk
      = mul (suc. q) m by mul_suc_left q m
      = add zero. (mul (suc. q) m) by add_zero_left (mul (suc. q) m) ∎

def negative_division_complement (r m k : Nat) (hk : Id Nat (add k (suc. r)) m) : BookLt k m
  ≔ (suc. r, ((p ↦ nat_encode (suc. r) zero. p),
      concat Nat (add (suc. r) k) (add k (suc. r)) m (add_comm (suc. r) k) hk))

{` Divide the index n of neg n = -(n+1).  If n = qm+r and k+r+1=m,
   then -(n+1) = -(q+1)m+k.  The complement is always a valid remainder. `}
def integer_euclidean_division (z : Int) (m : Nat) (positive : BookLt zero. m)
  : IntegerDivisionResult z m
  ≔ match z [
  | pos. n ↦ let u ≔ euclidean_division n m positive in
      ((pos. (u .fst .fst), u .fst .snd), (u .snd .fst,
        calc
          (pos. n : Int) = pos. (add (mul (u .fst .fst) m) (u .fst .snd)) by pos. (u .snd .snd)
          = integer_division_value (pos. (u .fst .fst)) (u .fst .snd) m
            by integer_division_value_pos (u .fst .fst) (u .fst .snd) m ∎))
  | neg. n ↦ let u ≔ euclidean_division n m positive in
      let q ≔ u .fst .fst in let r ≔ u .fst .snd in
      let c ≔ le_to_book (suc. r) m (lt_from_book r m (u .snd .fst)) in
      ((neg. q, c .fst), (negative_division_complement r m (c .fst) (c .snd),
        calc
          (neg. n : Int) = int_difference (c .fst) (mul (suc. q) m)
            by balance_value_respects (c .fst, mul (suc. q) m) (zero., suc. n)
              (negative_division_relation n q r m (c .fst) (u .snd .snd) (c .snd))
          = integer_division_value (neg. q) (c .fst) m by integer_division_value_neg q (c .fst) m ∎)) ]

def balance_equal_relation (p q : Balance) (e : Id Int (balance_value p) (balance_value q)) : SameBalance p q
  ≔ same_balance_trans p (int_balance (balance_value q)) q
      (transport Balance (SameBalance p) (int_balance (balance_value p)) (int_balance (balance_value q))
        (refl int_balance e) (difference_normalizes (p .fst) (p .snd)))
      (balance_relation .symmetric q (int_balance (balance_value q)) (difference_normalizes (q .fst) (q .snd)))

def difference_negative (w d : Nat) (h : Lt w d) : IntLt (int_difference w d) int_zero
  ≔ match d [
  | zero. ↦ match h []
  | suc. d ↦ match w [ zero. ↦ star. | suc. w ↦ difference_negative w d h ] ]

def positive_multiple_lower (q m : Nat) : Le m (mul (suc. q) m)
  ≔ refl Le (add_zero_left m)
      (inverse Nat (mul (suc. q) m) (add (mul q m) m) (mul_suc_left q m))
      .trr (le_add_right zero. (mul q m) m star.)

def integer_division_mixed_impossible (a b r s m : Nat) (hs : BookLt s m)
  (e : Id Int (integer_division_value (pos. a) r m) (integer_division_value (neg. b) s m)) : Empty
  ≔ let p : Id Int (pos. (add (mul a m) r)) (int_difference s (mul (suc. b) m)) ≔
      calc
        (pos. (add (mul a m) r) : Int) = integer_division_value (pos. a) r m by integer_division_value_pos a r m
        = integer_division_value (neg. b) s m by e
        = int_difference s (mul (suc. b) m) by integer_division_value_neg b s m ∎ in
    refl ((z ↦ IntLt z int_zero) : Int → Type) p .trl
      (difference_negative s (mul (suc. b) m)
        (lt_le_trans s m (mul (suc. b) m) (lt_from_book s m hs) (positive_multiple_lower b m)))

def integer_division_equal_pairs (q q' : Int) (r s m : Nat) (hr : BookLt r m) (hs : BookLt s m)
  (e : Id Int (integer_division_value q r m) (integer_division_value q' s m))
  : Id (Product Int Nat) (q, r) (q', s)
  ≔ match q, q' [
  | pos. a, pos. b ↦
      let p : Id Int (pos. (add (mul a m) r)) (pos. (add (mul b m) s)) ≔ calc
        (pos. (add (mul a m) r) : Int) = integer_division_value (pos. a) r m by integer_division_value_pos a r m
        = integer_division_value (pos. b) s m by e
        = pos. (add (mul b m) s) by integer_division_value_pos b s m ∎ in
      let u : DivisionResult (add (mul a m) r) m ≔ ((a, r), (hr, refl (add (mul a m) r))) in
      let v : DivisionResult (add (mul a m) r) m ≔ ((b, s), (hs, refl int_magnitude p)) in
      (pos. (division_quotients_equal (add (mul a m) r) m u v),
        division_remainders_equal (add (mul a m) r) m u v)
  | pos. a, neg. b ↦ match integer_division_mixed_impossible a b r s m hs e []
  | neg. a, pos. b ↦ match integer_division_mixed_impossible b a s r m hr
      (inverse Int (integer_division_value (neg. a) r m) (integer_division_value (pos. b) s m) e) []
  | neg. a, neg. b ↦
      let p : Id Int (int_difference r (mul (suc. a) m)) (int_difference s (mul (suc. b) m)) ≔ calc
        int_difference r (mul (suc. a) m) = integer_division_value (neg. a) r m by integer_division_value_neg a r m
        = integer_division_value (neg. b) s m by e
        = int_difference s (mul (suc. b) m) by integer_division_value_neg b s m ∎ in
      let h ≔ balance_equal_relation (r, mul (suc. a) m) (s, mul (suc. b) m) p in
      let k : Id Nat (add (mul (suc. b) m) r) (add (mul (suc. a) m) s) ≔ calc
        add (mul (suc. b) m) r = add r (mul (suc. b) m) by add_comm (mul (suc. b) m) r
        = add s (mul (suc. a) m) by h
        = add (mul (suc. a) m) s by add_comm s (mul (suc. a) m) ∎ in
      let u : DivisionResult (add (mul (suc. b) m) r) m ≔ ((suc. b, r), (hr, refl (add (mul (suc. b) m) r))) in
      let v : DivisionResult (add (mul (suc. b) m) r) m ≔ ((suc. a, s), (hs, k)) in
      (neg. (inverse Nat b a (refl nat_pred (division_quotients_equal (add (mul (suc. b) m) r) m u v))),
        division_remainders_equal (add (mul (suc. b) m) r) m u v) ]

def integer_division_result_prop (z : Int) (m : Nat) : isProp (IntegerDivisionResult z m)
  ≔ u v ↦ subtype_equal (Product Int Nat) (IntegerDivisionSpec z m) (integer_division_spec_prop z m) u v
      (integer_division_equal_pairs (u .fst .fst) (v .fst .fst) (u .fst .snd) (v .fst .snd) m (u .snd .fst) (v .snd .fst)
        (concat Int (integer_division_value (u .fst .fst) (u .fst .snd) m) z (integer_division_value (v .fst .fst) (v .fst .snd) m)
          (inverse Int z (integer_division_value (u .fst .fst) (u .fst .snd) m) (u .snd .snd)) (v .snd .snd)))

def integer_euclidean_division_unique (z : Int) (m : Nat) (positive : BookLt zero. m)
  : BookIsContr (IntegerDivisionResult z m)
  ≔ (integer_euclidean_division z m positive,
      integer_division_result_prop z m (integer_euclidean_division z m positive))

def integer_quotient (z : Int) (m : Nat) (positive : BookLt zero. m) : Int
  ≔ integer_euclidean_division z m positive .fst .fst
def integer_remainder (z : Int) (m : Nat) (positive : BookLt zero. m) : Nat
  ≔ integer_euclidean_division z m positive .fst .snd
