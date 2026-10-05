export "66-cycle-identity-classification"

def int_add_cancel_right (z x y : Int) (p : Id Int (int_add x z) (int_add y z)) : Id Int x y
  ≔ calc
      x = int_sub (int_add x z) z by int_add_sub x z
      = int_sub (int_add y z) z by refl ((w ↦ int_sub w z) : Int → Int) p
      = y by int_add_sub y z ∎

def int_neg_unique (x y : Int) (p : Id Int (int_add x y) int_zero) : Id Int y (int_neg x)
  ≔ calc
      y = int_add (int_neg x) (int_add x y) by int_translate_inverse x y
      = int_neg x by refl (int_add (int_neg x)) p ∎

def int_sub_self (x : Int) : Id Int (int_sub x x) int_zero ≔ int_add_neg_right x

def int_sub_chain (x y z : Int) : Id Int (int_add (int_sub x y) (int_sub y z)) (int_sub x z)
  ≔ calc
      int_add (int_sub x y) (int_sub y z) = int_add x (int_add (int_neg y) (int_add y (int_neg z)))
        by int_add_assoc x (int_neg y) (int_add y (int_neg z))
      = int_sub x z by refl (int_add x) (int_translate_inverse y (int_neg z)) ∎

def int_neg_sub (x y : Int) : Id Int (int_neg (int_sub x y)) (int_sub y x)
  ≔ inverse Int (int_sub y x) (int_neg (int_sub x y))
      (int_neg_unique (int_sub x y) (int_sub y x)
        (concat Int (int_add (int_sub x y) (int_sub y x)) (int_sub x x) int_zero
          (int_sub_chain x y x) (int_sub_self x)))

def int_sub_translate (x y z : Int)
  : Id Int (int_sub (int_add x z) (int_add y z)) (int_sub x y)
  ≔ int_add_cancel_right (int_add y z) (int_sub (int_add x z) (int_add y z)) (int_sub x y) (calc
      int_add (int_sub (int_add x z) (int_add y z)) (int_add y z) = int_add x z
        by int_sub_add (int_add x z) (int_add y z)
      = int_add (int_add (int_sub x y) y) z by refl ((w ↦ int_add w z) : Int → Int) (int_sub_add x y)
      = int_add (int_sub x y) (int_add y z) by int_add_assoc (int_sub x y) y z ∎)
