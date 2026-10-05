export "124-circle-map-degrees"

def nat_product_one_factor (n m : Nat) (h : Id Nat (mul n m) (suc. zero.))
  : Id Nat n (suc. zero.)
  ≔ match n [
  | zero. ↦ absurd (Id Nat zero. (suc. zero.))
      (nat_zero_ne_suc zero. (calc
        (zero. : Nat) = mul zero. m by mul_zero_left m
        = suc. zero. by h ∎))
  | suc. n ↦ match m [
    | zero. ↦ absurd (Id Nat (suc. n) (suc. zero.)) (nat_zero_ne_suc zero. h)
    | suc. m ↦ let bound : Le (suc. n) (suc. zero.)
        ≔ transport Nat (Le (suc. n)) (mul (suc. m) (suc. n)) (suc. zero.)
          (calc
            mul (suc. m) (suc. n) = mul (suc. n) (suc. m) by mul_comm (suc. m) (suc. n)
            = suc. zero. by h ∎) (positive_multiple_lower m (suc. n)) in
      suc. (le_antisym n zero. bound star.) ] ]

def int_mul_negative_positive (n m : Nat)
  : Id Int (int_mul (neg. n) (pos. m)) (int_difference zero. (mul (suc. n) m))
  ≔ calc
      int_mul (neg. n) (pos. m) = balance_value (balance_scale (zero., suc. n) m)
        by iterate_translation_balance (neg. n) (zero., suc. n) (refl (neg. n : Int)) m
      = int_difference zero. (mul (suc. n) m)
        by refl ((k ↦ int_difference k (mul (suc. n) m)) : Nat → Int) (mul_zero_left m) ∎

def int_mul_positive_negative (n m : Nat)
  : Id Int (int_mul (pos. n) (neg. m)) (int_difference zero. (mul (suc. m) n))
  ≔ concat Int (int_mul (pos. n) (neg. m)) (int_mul (neg. m) (pos. n))
      (int_difference zero. (mul (suc. m) n)) (int_mul_comm (pos. n) (neg. m)) (int_mul_negative_positive m n)

def int_mul_negative_negative (n m : Nat)
  : Id Int (int_mul (neg. n) (neg. m)) (pos. (mul (suc. n) (suc. m)))
  ≔ calc
      int_mul (neg. n) (neg. m) = balance_value (balance_scale (suc. n, zero.) (suc. m))
        by iterate_translation_balance (pos. (suc. n)) (suc. n, zero.) (refl (pos. (suc. n) : Int)) (suc. m)
      = (pos. (mul (suc. n) (suc. m)) : Int)
        by refl (int_difference (mul (suc. n) (suc. m))) (mul_zero_left (suc. m)) ∎

def int_nonpositive_not_one (n : Nat)
  : Id Int (int_difference zero. n) (pos. (suc. zero.)) → Empty
  ≔ match n [
  | zero. ↦ p ↦ int_encode (pos. zero.) (pos. (suc. zero.)) p
  | suc. n ↦ p ↦ int_encode (neg. n) (pos. (suc. zero.)) p ]

def IntegerUnitSign (z : Int) : Type
  ≔ Sum (Id Int z (pos. (suc. zero.))) (Id Int z (neg. zero.))

{` A signed integer with a multiplicative right inverse is 1 or -1.
   Constructive case analysis; no order decision principle is supplied. `}
def integer_unit_sign (x y : Int) (h : Id Int (int_mul x y) (pos. (suc. zero.))) : IntegerUnitSign x
  ≔ match x, y [
  | pos. n, pos. m ↦ inl. (refl int_of_nat
      (nat_product_one_factor n m (refl int_magnitude (calc
        (pos. (mul n m) : Int) = int_mul (pos. n) (pos. m) by int_mul_naturals n m
        = (pos. (suc. zero.) : Int) by h ∎))))
  | pos. n, neg. m ↦ absurd (IntegerUnitSign (pos. n))
      (int_nonpositive_not_one (mul (suc. m) n) (calc
        int_difference zero. (mul (suc. m) n) = int_mul (pos. n) (neg. m) by int_mul_positive_negative n m
        = (pos. (suc. zero.) : Int) by h ∎))
  | neg. n, pos. m ↦ absurd (IntegerUnitSign (neg. n))
      (int_nonpositive_not_one (mul (suc. n) m) (calc
        int_difference zero. (mul (suc. n) m) = int_mul (neg. n) (pos. m) by int_mul_negative_positive n m
        = (pos. (suc. zero.) : Int) by h ∎))
  | neg. n, neg. m ↦ inr. (refl ((k ↦ neg. k) : Nat → Int)
      (refl nat_pred (nat_product_one_factor (suc. n) (suc. m) (refl int_magnitude (calc
        (pos. (mul (suc. n) (suc. m)) : Int) = int_mul (neg. n) (neg. m) by int_mul_negative_negative n m
        = (pos. (suc. zero.) : Int) by h ∎))))) ]

def integer_unit_sign_prop (z : Int) : isProp (IntegerUnitSign z)
  ≔ disjoint_sum_prop (Id Int z (pos. (suc. zero.))) (Id Int z (neg. zero.))
      (int_set z (pos. (suc. zero.))) (int_set z (neg. zero.))
      (p q ↦ int_encode (pos. (suc. zero.)) (neg. zero.) (calc
        (pos. (suc. zero.) : Int) = z by p
        = (neg. zero. : Int) by q ∎))
