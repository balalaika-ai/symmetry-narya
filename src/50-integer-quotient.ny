export "49-pigeonhole"

def Balance : Type ≔ Product Nat Nat
def SameBalance (p q : Balance) : Type ≔ Id Nat (add (p .fst) (q .snd)) (add (q .fst) (p .snd))

def same_balance_trans (p q r : Balance) (h : SameBalance p q) (k : SameBalance q r) : SameBalance p r
  ≔ add_cancel_right (q .snd) (add (p .fst) (r .snd)) (add (r .fst) (p .snd))
      (calc
        add (add (p .fst) (r .snd)) (q .snd) = add (add (p .fst) (q .snd)) (r .snd)
          by add_swap_tail (p .fst) (r .snd) (q .snd)
        = add (add (q .fst) (p .snd)) (r .snd) by refl ((n ↦ add n (r .snd)) : Nat → Nat) h
        = add (add (q .fst) (r .snd)) (p .snd) by add_swap_tail (q .fst) (p .snd) (r .snd)
        = add (add (r .fst) (q .snd)) (p .snd) by refl ((n ↦ add n (p .snd)) : Nat → Nat) k
        = add (add (r .fst) (p .snd)) (q .snd) by add_swap_tail (r .fst) (q .snd) (p .snd) ∎)

def balance_relation : EquivalenceRelation Balance
  ≔ ((p q ↦ (SameBalance p q, nat_set (add (p .fst) (q .snd)) (add (q .fst) (p .snd)))),
      (p ↦ refl (add (p .fst) (p .snd))),
      (p q ↦ inverse Nat (add (p .fst) (q .snd)) (add (q .fst) (p .snd))), same_balance_trans)

def int_balance : Int → Balance ≔ [ pos. n ↦ (n, zero.) | neg. n ↦ (zero., suc. n) ]

def int_difference (w d : Nat) : Int
  ≔ match d [ zero. ↦ pos. w | suc. d ↦ match w [ zero. ↦ neg. d | suc. w ↦ int_difference w d ] ]

def balance_value (p : Balance) : Int ≔ int_difference (p .fst) (p .snd)

def difference_int_balance (z : Int) : Id Int (balance_value (int_balance z)) z
  ≔ match z [ pos. n ↦ refl (pos. n : Int) | neg. n ↦ refl (neg. n : Int) ]

def difference_normalizes (w d : Nat) : SameBalance (w, d) (int_balance (int_difference w d))
  ≔ match d [
  | zero. ↦ refl w
  | suc. d ↦ match w [
    | zero. ↦ refl (add zero. (suc. d))
    | suc. w ↦ concat Nat
      (add (suc. w) (int_balance (int_difference w d) .snd))
      (suc. (add w (int_balance (int_difference w d) .snd)))
      (suc. (add (int_balance (int_difference w d) .fst) d))
      (add_suc_left w (int_balance (int_difference w d) .snd)) (suc. (difference_normalizes w d)) ] ]

def same_int_balances (x y : Int) (h : SameBalance (int_balance x) (int_balance y)) : Id Int x y
  ≔ match x, y [
  | pos. m, pos. n ↦ pos. h
  | pos. m, neg. n ↦ match nat_encode (suc. (add m n)) zero. h []
  | neg. m, pos. n ↦ match nat_encode zero. (suc. (add n m)) h []
  | neg. m, neg. n ↦ neg. (inverse Nat n m (refl nat_pred (add_cancel_left zero. (suc. n) (suc. m) h))) ]

def balance_value_respects (p q : Balance) (h : SameBalance p q) : Id Int (balance_value p) (balance_value q)
  ≔ same_int_balances (balance_value p) (balance_value q)
      (same_balance_trans (int_balance (balance_value p)) p (int_balance (balance_value q))
        (balance_relation .symmetric p (int_balance (balance_value p)) (difference_normalizes (p .fst) (p .snd)))
        (same_balance_trans p q (int_balance (balance_value q)) h (difference_normalizes (q .fst) (q .snd))))

def IntegerQuotient : Type ≔ Quotient Balance balance_relation
def balance_class : Balance → IntegerQuotient ≔ quotient_class Balance balance_relation

def integer_quotient_value : IntegerQuotient → Int
  ≔ quotient_rec Balance Int balance_relation int_set balance_value balance_value_respects

def int_quotient_class (z : Int) : IntegerQuotient ≔ balance_class (int_balance z)

def integer_quotient_roundtrip
  : Id (IntegerQuotient → IntegerQuotient)
      (compose IntegerQuotient Int IntegerQuotient int_quotient_class integer_quotient_value) (identity IntegerQuotient)
  ≔ surjection_function_ext Balance IntegerQuotient IntegerQuotient balance_class
      (quotient_surjective Balance balance_relation) (quotient_set Balance balance_relation)
      (compose IntegerQuotient Int IntegerQuotient int_quotient_class integer_quotient_value) (identity IntegerQuotient)
      (funext Balance (_ ↦ IntegerQuotient) (p ↦ int_quotient_class (balance_value p)) balance_class
        (p ↦ quotient_encode Balance balance_relation (int_balance (balance_value p)) p
          (balance_relation .symmetric p (int_balance (balance_value p)) (difference_normalizes (p .fst) (p .snd)))))

def integer_quotient_equiv : Equiv IntegerQuotient Int
  ≔ quasi_inverse_equiv IntegerQuotient Int integer_quotient_value int_quotient_class
      (q ↦ integer_quotient_roundtrip (refl q)) difference_int_balance

{` xca:ints-as-quotient uses disjunction (native propositional truncation),
   with the negative branch explicitly excluding a second zero. `}
def ReducedBalance (p : Balance) : Type
  ≔ Mere (Sum (Id Nat (p .snd) zero.)
      (Product (Id Nat (p .fst) zero.) (Id Nat (p .snd) zero. → Empty)))

def reduced_balance_prop (p : Balance) : isProp (ReducedBalance p)
  ≔ mere_isprop (Sum (Id Nat (p .snd) zero.)
      (Product (Id Nat (p .fst) zero.) (Id Nat (p .snd) zero. → Empty)))

def NormalBalances : Type ≔ Σ Balance ReducedBalance

def int_balance_reduced (z : Int) : ReducedBalance (int_balance z)
  ≔ match z [
  | pos. n ↦ mere (Sum (Id Nat zero. zero.) (Product (Id Nat n zero.) (Id Nat zero. zero. → Empty))) (inl. (refl zero.))
  | neg. n ↦ mere (Sum (Id Nat (suc. n) zero.) (Product (Id Nat zero. zero.) (Id Nat (suc. n) zero. → Empty)))
      (inr. (refl zero., p ↦ nat_encode (suc. n) zero. p)) ]

def int_normal_balance (z : Int) : NormalBalances ≔ (int_balance z, int_balance_reduced z)

def reduced_balance_normalizes (w d : Nat) (h : ReducedBalance (w, d))
  : Id Balance (int_balance (int_difference w d)) (w, d)
  ≔ match d [
  | zero. ↦ refl (w, zero.)
  | suc. d ↦ match w [
    | zero. ↦ refl (zero., suc. d)
    | suc. w ↦ absurd (Id Balance (int_balance (int_difference w d)) (suc. w, suc. d))
      (mere_rec (Sum (Id Nat (suc. d) zero.)
        (Product (Id Nat (suc. w) zero.) (Id Nat (suc. d) zero. → Empty))) Empty empty_prop
        [ inl. p ↦ nat_encode (suc. d) zero. p | inr. p ↦ nat_encode (suc. w) zero. (p .fst) ] h) ] ]

def normal_balance_roundtrip (p : NormalBalances)
  : Id NormalBalances (int_normal_balance (balance_value (p .fst))) p
  ≔ subtype_equal Balance ReducedBalance reduced_balance_prop (int_normal_balance (balance_value (p .fst))) p
      (reduced_balance_normalizes (p .fst .fst) (p .fst .snd) (p .snd))

def int_normal_balance_equiv : Equiv Int NormalBalances
  ≔ quasi_inverse_equiv Int NormalBalances int_normal_balance (p ↦ balance_value (p .fst))
      difference_int_balance normal_balance_roundtrip

def integer_quotient_normal_equiv : BookEquiv IntegerQuotient NormalBalances
  ≔ book_equivalence IntegerQuotient NormalBalances
      (compose_equiv IntegerQuotient Int NormalBalances integer_quotient_equiv int_normal_balance_equiv)

def integer_quotient_normal_beta (p : NormalBalances)
  : Id NormalBalances (integer_quotient_normal_equiv .map (balance_class (p .fst))) p
  ≔ normal_balance_roundtrip p
