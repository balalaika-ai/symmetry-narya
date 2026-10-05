export "51-integer-gluing"

def difference_suc_left (w d : Nat)
  : Id Int (int_difference (suc. w) d) (int_succ (int_difference w d))
  ≔ match d [
  | zero. ↦ refl (pos. (suc. w) : Int)
  | suc. d ↦ match w [
    | zero. ↦ match d [ zero. ↦ refl int_zero | suc. d ↦ refl (neg. d : Int) ]
    | suc. w ↦ difference_suc_left w d ] ]

def difference_suc_right (w d : Nat)
  : Id Int (int_difference w (suc. d)) (int_pred (int_difference w d))
  ≔ match w [
  | zero. ↦ match d [ zero. ↦ refl (neg. zero. : Int) | suc. d ↦ refl (neg. (suc. d) : Int) ]
  | suc. w ↦ match d [ zero. ↦ refl (pos. w : Int) | suc. d ↦ difference_suc_right w d ] ]

def iterate_succ_difference (w d n : Nat)
  : Id Int (iterate Int int_succ n (int_difference w d)) (int_difference (add w n) d)
  ≔ match n [
  | zero. ↦ refl (int_difference w d)
  | suc. n ↦ concat Int (int_succ (iterate Int int_succ n (int_difference w d)))
      (int_succ (int_difference (add w n) d)) (int_difference (suc. (add w n)) d)
      (refl int_succ (iterate_succ_difference w d n))
      (inverse Int (int_difference (suc. (add w n)) d) (int_succ (int_difference (add w n) d))
        (difference_suc_left (add w n) d)) ]

def iterate_pred_difference (w d n : Nat)
  : Id Int (iterate Int int_pred n (int_difference w d)) (int_difference w (add d n))
  ≔ match n [
  | zero. ↦ refl (int_difference w d)
  | suc. n ↦ concat Int (int_pred (iterate Int int_pred n (int_difference w d)))
      (int_pred (int_difference w (add d n))) (int_difference w (suc. (add d n)))
      (refl int_pred (iterate_pred_difference w d n))
      (inverse Int (int_difference w (suc. (add d n))) (int_pred (int_difference w (add d n)))
        (difference_suc_right w (add d n))) ]

def balance_add (p q : Balance) : Balance ≔ (add (p .fst) (q .fst), add (p .snd) (q .snd))

def balance_add_respects (p p' q q' : Balance) (h : SameBalance p p') (k : SameBalance q q')
  : SameBalance (balance_add p q) (balance_add p' q')
  ≔ calc
      add (add (p .fst) (q .fst)) (add (p' .snd) (q' .snd))
      = add (add (p .fst) (p' .snd)) (add (q .fst) (q' .snd))
        by add_interchange (p .fst) (q .fst) (p' .snd) (q' .snd)
      = add (add (p' .fst) (p .snd)) (add (q' .fst) (q .snd)) by refl add h k
      = add (add (p' .fst) (q' .fst)) (add (p .snd) (q .snd))
        by add_interchange (p' .fst) (q' .fst) (p .snd) (q .snd) ∎

{` This is the original int_add, defined by signed iteration in module 03. `}
def int_add_balance (x y : Int)
  : Id Int (int_add x y) (balance_value (balance_add (int_balance x) (int_balance y)))
  ≔ match y [
  | pos. n ↦ concat Int (iterate Int int_succ n x) (iterate Int int_succ n (balance_value (int_balance x)))
      (int_difference (add (int_balance x .fst) n) (int_balance x .snd))
      (refl (iterate Int int_succ n) (inverse Int (balance_value (int_balance x)) x (difference_int_balance x)))
      (iterate_succ_difference (int_balance x .fst) (int_balance x .snd) n)
  | neg. n ↦ concat Int (iterate Int int_pred (suc. n) x) (iterate Int int_pred (suc. n) (balance_value (int_balance x)))
      (int_difference (int_balance x .fst) (add (int_balance x .snd) (suc. n)))
      (refl (iterate Int int_pred (suc. n)) (inverse Int (balance_value (int_balance x)) x (difference_int_balance x)))
      (iterate_pred_difference (int_balance x .fst) (int_balance x .snd) (suc. n)) ]

def balance_value_add (p q : Balance) : Id Int (int_add (balance_value p) (balance_value q)) (balance_value (balance_add p q))
  ≔ concat Int (int_add (balance_value p) (balance_value q))
      (balance_value (balance_add (int_balance (balance_value p)) (int_balance (balance_value q))))
      (balance_value (balance_add p q)) (int_add_balance (balance_value p) (balance_value q))
      (balance_value_respects (balance_add (int_balance (balance_value p)) (int_balance (balance_value q))) (balance_add p q)
        (balance_add_respects (int_balance (balance_value p)) p (int_balance (balance_value q)) q
          (balance_relation .symmetric p (int_balance (balance_value p)) (difference_normalizes (p .fst) (p .snd)))
          (balance_relation .symmetric q (int_balance (balance_value q)) (difference_normalizes (q .fst) (q .snd)))))

def balance_add_comm (p q : Balance) : Id Balance (balance_add p q) (balance_add q p)
  ≔ (add_comm (p .fst) (q .fst), add_comm (p .snd) (q .snd))

def balance_add_assoc (p q r : Balance) : Id Balance (balance_add (balance_add p q) r) (balance_add p (balance_add q r))
  ≔ (add_assoc (p .fst) (q .fst) (r .fst), add_assoc (p .snd) (q .snd) (r .snd))

def int_add_comm (x y : Int) : Id Int (int_add x y) (int_add y x)
  ≔ calc
      int_add x y = balance_value (balance_add (int_balance x) (int_balance y)) by int_add_balance x y
      = balance_value (balance_add (int_balance y) (int_balance x))
        by refl balance_value (balance_add_comm (int_balance x) (int_balance y))
      = int_add y x by int_add_balance y x ∎

def int_add_assoc (x y z : Int) : Id Int (int_add (int_add x y) z) (int_add x (int_add y z))
  ≔ calc
      int_add (int_add x y) z
      = int_add (balance_value (balance_add (int_balance x) (int_balance y))) (balance_value (int_balance z))
        by refl int_add (int_add_balance x y) (inverse Int (balance_value (int_balance z)) z (difference_int_balance z))
      = balance_value (balance_add (balance_add (int_balance x) (int_balance y)) (int_balance z))
        by balance_value_add (balance_add (int_balance x) (int_balance y)) (int_balance z)
      = balance_value (balance_add (int_balance x) (balance_add (int_balance y) (int_balance z)))
        by refl balance_value (balance_add_assoc (int_balance x) (int_balance y) (int_balance z))
      = int_add (balance_value (int_balance x)) (balance_value (balance_add (int_balance y) (int_balance z)))
        by balance_value_add (int_balance x) (balance_add (int_balance y) (int_balance z))
      = int_add x (int_add y z)
        by refl int_add (difference_int_balance x)
          (inverse Int (int_add y z) (balance_value (balance_add (int_balance y) (int_balance z))) (int_add_balance y z)) ∎

def int_add_zero_right (x : Int) : Id Int (int_add x int_zero) x ≔ refl x
def int_add_zero_left (x : Int) : Id Int (int_add int_zero x) x ≔ int_add_comm int_zero x

def balance_swap (p : Balance) : Balance ≔ (p .snd, p .fst)
def int_neg_balance (x : Int) : Id Balance (int_balance (int_neg x)) (balance_swap (int_balance x))
  ≔ match x [ pos. zero. ↦ refl (zero., zero.) | pos. (suc. n) ↦ refl (zero., suc. n) | neg. n ↦ refl (suc. n, zero.) ]

def difference_diagonal (n : Nat) : Id Int (int_difference n n) int_zero
  ≔ match n [ zero. ↦ refl int_zero | suc. n ↦ difference_diagonal n ]

def int_add_neg_right (x : Int) : Id Int (int_add x (int_neg x)) int_zero
  ≔ calc
      int_add x (int_neg x) = balance_value (balance_add (int_balance x) (int_balance (int_neg x)))
        by int_add_balance x (int_neg x)
      = balance_value (balance_add (int_balance x) (balance_swap (int_balance x)))
        by refl ((p ↦ balance_value (balance_add (int_balance x) p)) : Balance → Int) (int_neg_balance x)
      = int_difference (add (int_balance x .fst) (int_balance x .snd)) (add (int_balance x .fst) (int_balance x .snd))
        by refl (int_difference (add (int_balance x .fst) (int_balance x .snd)))
          (add_comm (int_balance x .snd) (int_balance x .fst))
      = int_zero by difference_diagonal (add (int_balance x .fst) (int_balance x .snd)) ∎

def int_add_neg_left (x : Int) : Id Int (int_add (int_neg x) x) int_zero
  ≔ concat Int (int_add (int_neg x) x) (int_add x (int_neg x)) int_zero (int_add_comm (int_neg x) x) (int_add_neg_right x)

def int_translate_inverse (x y : Int) : Id Int (int_add (int_neg x) (int_add x y)) y
  ≔ calc
      int_add (int_neg x) (int_add x y) = int_add (int_add (int_neg x) x) y by int_add_assoc (int_neg x) x y
      = int_add int_zero y by refl ((z ↦ int_add z y) : Int → Int) (int_add_neg_left x)
      = y by int_add_zero_left y ∎

def int_translate_inverse_other (x y : Int) : Id Int (int_add x (int_add (int_neg x) y)) y
  ≔ calc
      int_add x (int_add (int_neg x) y) = int_add (int_add x (int_neg x)) y by int_add_assoc x (int_neg x) y
      = int_add int_zero y by refl ((z ↦ int_add z y) : Int → Int) (int_add_neg_right x)
      = y by int_add_zero_left y ∎

def int_translation_equiv (x : Int) : Equiv Int Int
  ≔ quasi_inverse_equiv Int Int (int_add x) (int_add (int_neg x)) (int_translate_inverse x) (int_translate_inverse_other x)

def int_add_naturals (n m : Nat) : Id Int (int_of_nat (add n m)) (int_add (int_of_nat n) (int_of_nat m))
  ≔ inverse Int (int_add (pos. n) (pos. m)) (pos. (add n m)) (int_add_balance (pos. n) (pos. m))

def int_sub (x y : Int) : Int ≔ int_add x (int_neg y)

def int_add_sub (x y : Int) : Id Int (int_sub (int_add x y) y) x
  ≔ calc
      int_sub (int_add x y) y = int_add x (int_add y (int_neg y)) by int_add_assoc x y (int_neg y)
      = x by refl (int_add x) (int_add_neg_right y) ∎

def int_sub_add (x y : Int) : Id Int (int_add (int_sub x y) y) x
  ≔ calc
      int_add (int_sub x y) y = int_add x (int_add (int_neg y) y) by int_add_assoc x (int_neg y) y
      = x by refl (int_add x) (int_add_neg_left y) ∎
