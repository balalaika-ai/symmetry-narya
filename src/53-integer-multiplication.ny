export "52-integer-addition"

{` Multiplication is signed iteration of translation, as in the book.
   Module 52 proves that translation by -x is an inverse of translation by x. `}
def int_mul (x y : Int) : Int
  ≔ int_iterate Int (int_add x) (int_add (int_neg x)) y int_zero

def balance_scale (p : Balance) (n : Nat) : Balance ≔ (mul (p .fst) n, mul (p .snd) n)

def balance_scale_step (p : Balance) (n : Nat)
  : Id Balance (balance_add p (balance_scale p n)) (balance_scale p (suc. n))
  ≔ (add_comm (p .fst) (mul (p .fst) n), add_comm (p .snd) (mul (p .snd) n))

def iterate_translation_balance (x : Int) (p : Balance) (hx : Id Int x (balance_value p)) (n : Nat)
  : Id Int (iterate Int (int_add x) n int_zero) (balance_value (balance_scale p n))
  ≔ match n [
  | zero. ↦ refl int_zero
  | suc. n ↦ calc
      int_add x (iterate Int (int_add x) n int_zero)
      = int_add (balance_value p) (balance_value (balance_scale p n))
        by refl int_add hx (iterate_translation_balance x p hx n)
      = balance_value (balance_add p (balance_scale p n)) by balance_value_add p (balance_scale p n)
      = balance_value (balance_scale p (suc. n))
        by refl balance_value (balance_scale_step p n) ∎ ]

def int_neg_value (x : Int)
  : Id Int (int_neg x) (balance_value (balance_swap (int_balance x)))
  ≔ calc
      int_neg x = balance_value (int_balance (int_neg x)) by difference_int_balance (int_neg x)
      = balance_value (balance_swap (int_balance x)) by refl balance_value (int_neg_balance x) ∎

def balance_mul (p q : Balance) : Balance
  ≔ (add (mul (p .fst) (q .fst)) (mul (p .snd) (q .snd)),
      add (mul (p .fst) (q .snd)) (mul (p .snd) (q .fst)))

def balance_mul_positive (p : Balance) (n : Nat)
  : Id Balance (balance_mul p (n, zero.)) (balance_scale p n)
  ≔ (refl (mul (p .fst) n), add_zero_left (mul (p .snd) n))

def balance_mul_negative (p : Balance) (n : Nat)
  : Id Balance (balance_mul p (zero., suc. n)) (balance_scale (balance_swap p) (suc. n))
  ≔ (add_zero_left (mul (p .snd) (suc. n)), refl (mul (p .fst) (suc. n)))

def int_mul_balance (x y : Int)
  : Id Int (int_mul x y) (balance_value (balance_mul (int_balance x) (int_balance y)))
  ≔ match y [
  | pos. n ↦ calc
      iterate Int (int_add x) n int_zero = balance_value (balance_scale (int_balance x) n)
        by iterate_translation_balance x (int_balance x)
          (inverse Int (balance_value (int_balance x)) x (difference_int_balance x)) n
      = balance_value (balance_mul (int_balance x) (n, zero.))
        by refl balance_value (balance_mul_positive (int_balance x) n) ∎
  | neg. n ↦ calc
      iterate Int (int_add (int_neg x)) (suc. n) int_zero
      = balance_value (balance_scale (balance_swap (int_balance x)) (suc. n))
        by iterate_translation_balance (int_neg x) (balance_swap (int_balance x)) (int_neg_value x) (suc. n)
      = balance_value (balance_mul (int_balance x) (zero., suc. n))
        by refl balance_value (balance_mul_negative (int_balance x) n) ∎ ]

def balance_mul_comm (p q : Balance) : Id Balance (balance_mul p q) (balance_mul q p)
  ≔ (refl add (mul_comm (p .fst) (q .fst)) (mul_comm (p .snd) (q .snd)),
      calc
        add (mul (p .fst) (q .snd)) (mul (p .snd) (q .fst))
        = add (mul (q .snd) (p .fst)) (mul (q .fst) (p .snd))
          by refl add (mul_comm (p .fst) (q .snd)) (mul_comm (p .snd) (q .fst))
        = add (mul (q .fst) (p .snd)) (mul (q .snd) (p .fst))
          by add_comm (mul (q .snd) (p .fst)) (mul (q .fst) (p .snd)) ∎)

def int_mul_comm (x y : Int) : Id Int (int_mul x y) (int_mul y x)
  ≔ calc
      int_mul x y = balance_value (balance_mul (int_balance x) (int_balance y)) by int_mul_balance x y
      = balance_value (balance_mul (int_balance y) (int_balance x))
        by refl balance_value (balance_mul_comm (int_balance x) (int_balance y))
      = int_mul y x by int_mul_balance y x ∎

def int_mul_naturals (n m : Nat) : Id Int (int_of_nat (mul n m)) (int_mul (int_of_nat n) (int_of_nat m))
  ≔ calc
      (pos. (mul n m) : Int) = balance_value (balance_scale (n, zero.) m)
        by map_path Balance Int balance_value (mul n m, zero.) (balance_scale (n, zero.) m)
          (refl (mul n m), inverse Nat (mul zero. m) zero. (mul_zero_left m))
      = balance_value (balance_mul (n, zero.) (m, zero.))
        by refl balance_value (balance_mul_positive (n, zero.) m)
      = int_mul (pos. n) (pos. m) by int_mul_balance (pos. n) (pos. m) ∎
