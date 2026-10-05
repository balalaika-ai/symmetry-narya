export "55-integer-division"

def Remainder (m : Nat) : Type ≔ Σ Nat (r ↦ BookLt r m)
def IntegerDigits (m : Nat) : Type ≔ Product (Remainder m) Int

def integer_digits_value (m : Nat) (p : IntegerDigits m) : Int
  ≔ integer_division_value (p .snd) (p .fst .fst) m

def division_result_digits (z : Int) (m : Nat) (u : IntegerDivisionResult z m) : IntegerDigits m
  ≔ ((u .fst .snd, u .snd .fst), u .fst .fst)

def integer_digits (m : Nat) (positive : BookLt zero. m) (z : Int) : IntegerDigits m
  ≔ division_result_digits z m (integer_euclidean_division z m positive)

def integer_digits_recompose (m : Nat) (positive : BookLt zero. m) (z : Int)
  : Id Int (integer_digits_value m (integer_digits m positive z)) z
  ≔ inverse Int z (integer_digits_value m (integer_digits m positive z))
      (integer_euclidean_division z m positive .snd .snd)

def integer_digits_recover (m : Nat) (positive : BookLt zero. m) (p : IntegerDigits m)
  : Id (IntegerDigits m) (integer_digits m positive (integer_digits_value m p)) p
  ≔ map_path (IntegerDivisionResult (integer_digits_value m p) m) (IntegerDigits m)
      (division_result_digits (integer_digits_value m p) m)
      (integer_euclidean_division (integer_digits_value m p) m positive)
      (((p .snd), (p .fst .fst)), ((p .fst .snd), refl (integer_digits_value m p)))
      (integer_division_result_prop (integer_digits_value m p) m
        (integer_euclidean_division (integer_digits_value m p) m positive)
        (((p .snd), (p .fst .fst)), ((p .fst .snd), refl (integer_digits_value m p))))

def integer_digits_equiv (m : Nat) (positive : BookLt zero. m) : Equiv (IntegerDigits m) Int
  ≔ quasi_inverse_equiv (IntegerDigits m) Int (integer_digits_value m) (integer_digits m positive)
      (integer_digits_recover m positive) (integer_digits_recompose m positive)

def finite_digits_equiv (m : Nat) : Equiv (Product (Fin m) Int) (IntegerDigits m)
  ≔ product_equiv (Fin m) Int (Remainder m) Int (fin_book_below_equiv m) (identity_equiv Int)

{` The displayed map in lem:deg-m-on-Cyc, with exactly the order k + mn. `}
def integer_radix_value (m : Nat) (p : Product (Fin m) Int) : Int
  ≔ int_add (pos. (fin_book_below_equiv m .map (p .fst) .fst)) (int_mul (pos. m) (p .snd))

def integer_radix_value_compare (m : Nat) (p : Product (Fin m) Int)
  : Id Int (integer_digits_value m (finite_digits_equiv m .map p)) (integer_radix_value m p)
  ≔ calc
      integer_digits_value m (finite_digits_equiv m .map p)
      = int_add (pos. (fin_book_below_equiv m .map (p .fst) .fst)) (int_mul (p .snd) (pos. m))
        by int_add_comm (int_mul (p .snd) (pos. m)) (pos. (fin_book_below_equiv m .map (p .fst) .fst))
      = integer_radix_value m p
        by refl (int_add (pos. (fin_book_below_equiv m .map (p .fst) .fst))) (int_mul_comm (p .snd) (pos. m)) ∎

def integer_radix_digits (m : Nat) (positive : BookLt zero. m) (z : Int) : Product (Fin m) Int
  ≔ equiv_inverse_map (Product (Fin m) Int) (IntegerDigits m) (finite_digits_equiv m) (integer_digits m positive z)

def integer_radix_recover (m : Nat) (positive : BookLt zero. m) (p : Product (Fin m) Int)
  : Id (Product (Fin m) Int) (integer_radix_digits m positive (integer_radix_value m p)) p
  ≔ calc
      integer_radix_digits m positive (integer_radix_value m p)
      = integer_radix_digits m positive (integer_digits_value m (finite_digits_equiv m .map p))
        by refl (integer_radix_digits m positive) (integer_radix_value_compare m p)
      = equiv_inverse_map (Product (Fin m) Int) (IntegerDigits m) (finite_digits_equiv m) (finite_digits_equiv m .map p)
        by refl (equiv_inverse_map (Product (Fin m) Int) (IntegerDigits m) (finite_digits_equiv m))
          (integer_digits_recover m positive (finite_digits_equiv m .map p))
      = p by equiv_unit (Product (Fin m) Int) (IntegerDigits m) (finite_digits_equiv m) p ∎

def integer_radix_recompose (m : Nat) (positive : BookLt zero. m) (z : Int)
  : Id Int (integer_radix_value m (integer_radix_digits m positive z)) z
  ≔ calc
      integer_radix_value m (integer_radix_digits m positive z)
      = integer_digits_value m (finite_digits_equiv m .map (integer_radix_digits m positive z))
        by integer_radix_value_compare m (integer_radix_digits m positive z)
      = integer_digits_value m (integer_digits m positive z)
        by refl (integer_digits_value m)
          (equiv_counit (Product (Fin m) Int) (IntegerDigits m) (finite_digits_equiv m) (integer_digits m positive z))
      = z by integer_digits_recompose m positive z ∎

def integer_radix_equiv (m : Nat) (positive : BookLt zero. m) : BookEquiv (Product (Fin m) Int) Int
  ≔ book_quasi_inverse_equiv (Product (Fin m) Int) Int (integer_radix_value m) (integer_radix_digits m positive)
      (integer_radix_recover m positive) (integer_radix_recompose m positive)

def integer_radix_quotient_beta (m : Nat) (positive : BookLt zero. m) (z : Int)
  : Id Int (integer_radix_digits m positive z .snd) (integer_quotient z m positive)
  ≔ map_path (IntegerDigits m) Int (p ↦ p .snd)
      (finite_digits_equiv m .map (integer_radix_digits m positive z)) (integer_digits m positive z)
      (equiv_counit (Product (Fin m) Int) (IntegerDigits m) (finite_digits_equiv m) (integer_digits m positive z))

def integer_radix_remainder_beta (m : Nat) (positive : BookLt zero. m) (z : Int)
  : Id Nat (fin_book_below_equiv m .map (integer_radix_digits m positive z .fst) .fst) (integer_remainder z m positive)
  ≔ map_path (IntegerDigits m) Nat (p ↦ p .fst .fst)
      (finite_digits_equiv m .map (integer_radix_digits m positive z)) (integer_digits m positive z)
      (equiv_counit (Product (Fin m) Int) (IntegerDigits m) (finite_digits_equiv m) (integer_digits m positive z))
