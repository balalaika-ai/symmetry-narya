export "146-quotient-preimages"

{` Divisibility of natural numbers, d | k iff k = qd for some q. `}
def NatDivides (d k : Nat) : Type ≔ Mere (Σ Nat (q ↦ Id Nat k (mul q d)))
def nat_divides_prop (d k : Nat) : isProp (NatDivides d k) ≔ mere_isprop (Σ Nat (q ↦ Id Nat k (mul q d)))

{` As a subset of Z, a principal order d is dZ (0 is the infinite order). `}
def principal_order_periods (k : Nat) : Id (Subtypes Int) (order_periods (principal_order k)) (Multiples k)
  ≔ match k [
  | zero. ↦ concat (Subtypes Int) (CyclePeriods infinite_cycle) ZeroPeriods (Multiples zero.)
      infinite_cycle_periods
      (inclusion_antisym Int ZeroPeriods (Multiples zero.)
        (z p ↦ mere (MultipleWitness zero. z) (z, p))
        (z s ↦ mere_rec (MultipleWitness zero. z) (Id Int z int_zero) (int_set z int_zero) (w ↦ w .snd) s))
  | suc. n ↦ finite_standard_periods n ]

def self_multiple (k : Nat) : Multiples k (pos. k) .fst
  ≔ mere (MultipleWitness k (pos. k))
      (pos. (suc. zero.), inverse Int (int_mul (pos. (suc. zero.)) (pos. k)) (pos. k) (int_mul_comm (pos. (suc. zero.)) (pos. k)))

def multiple_nat_divides_at (d k : Nat) (q : Int) : Id Int (pos. k) (int_mul q (pos. d)) → NatDivides d k
  ≔ match q [
  | pos. j ↦ p ↦ mere (Σ Nat (q ↦ Id Nat k (mul q d))) (j, refl int_magnitude (concat Int (pos. k) (int_mul (pos. j) (pos. d))
      (pos. (mul j d)) p (inverse Int (pos. (mul j d)) (int_mul (pos. j) (pos. d)) (int_mul_naturals j d))))
  | neg. j ↦ match d [
    | zero. ↦ p ↦ mere (Σ Nat (q ↦ Id Nat k (mul q zero.))) (zero., refl int_magnitude
        (concat Int (pos. k) (int_mul (neg. j) (pos. zero.)) (pos. zero.) p (int_mul_negative_positive j zero.)))
    | suc. e ↦ p ↦ absurd (NatDivides (suc. e) k) (int_encode (pos. k) (int_difference zero. (mul (suc. j) (suc. e)))
        (concat Int (pos. k) (int_mul (neg. j) (pos. (suc. e))) (int_difference zero. (mul (suc. j) (suc. e)))
          p (int_mul_negative_positive j (suc. e)))) ] ]

def multiple_nat_divides (d k : Nat) (w : MultipleWitness d (pos. k)) : NatDivides d k
  ≔ multiple_nat_divides_at d k (w .fst) (w .snd)

{` The divisibility relation on orders extends that on natural numbers. `}
def principal_divides_equiv (d k : Nat)
  : Equiv (OrderDivides (principal_order d) (principal_order k)) (NatDivides d k)
  ≔ let Hd ≔ order_periods (principal_order d) in let Hk ≔ order_periods (principal_order k) in
    iff_equiv (OrderDivides (principal_order d) (principal_order k)) (NatDivides d k)
      (order_divides_prop (principal_order d) (principal_order k)) (nat_divides_prop d k)
      (h ↦ mere_rec (MultipleWitness d (pos. k)) (NatDivides d k) (nat_divides_prop d k) (multiple_nat_divides d k)
        (transport (Subtypes Int) (H ↦ H (pos. k) .fst) Hd (Multiples d) (principal_order_periods d)
          (h (pos. k) (transport (Subtypes Int) (H ↦ H (pos. k) .fst) (Multiples k) Hk
            (inverse (Subtypes Int) Hk (Multiples k) (principal_order_periods k)) (self_multiple k)))))
      (v z p ↦ transport (Subtypes Int) (H ↦ H z .fst) (Multiples d) Hd
        (inverse (Subtypes Int) Hd (Multiples d) (principal_order_periods d))
        (mere_rec (Σ Nat (q ↦ Id Nat k (mul q d))) (Multiples d z .fst) (Multiples d z .snd)
          (u ↦ mere_rec (MultipleWitness k z) (Multiples d z .fst) (Multiples d z .snd)
            (r ↦ mere (MultipleWitness d z) (int_mul (r .fst) (pos. (u .fst)), calc
              z = int_mul (r .fst) (pos. k) by r .snd
              = int_mul (r .fst) (pos. (mul (u .fst) d)) by refl ((y ↦ int_mul (r .fst) (pos. y)) : Nat → Int) (u .snd)
              = int_mul (int_mul (r .fst) (pos. (u .fst))) (pos. d) by int_mul_pos_mul (r .fst) (u .fst) d ∎))
            (transport (Subtypes Int) (H ↦ H z .fst) Hk (Multiples k) (principal_order_periods k) p))
          v))
