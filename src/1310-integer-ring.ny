export "1300-abstract-rings"
export "721-mere-inverses"

{` Chapter 13 (fields.tex), running text of sec:rings (line 25): "the
   standard example of a (commutative) ring is the ring with set of
   integers as underlying set, with addition as group operation and
   multiplication as monoid operation". Multiplication of module 53 is
   signed iteration of translation (int_mul x y = y-fold x + -), so
   x · (succ w) = x + x · w and x · (pred w) = -x + x · w; the left
   distributive law follows by induction on the second summand,
   associativity by induction on the third factor (the negative case is
   reduced to the positive one by x · (neg n) ≡ (-x) · (n+1)), and the
   right distributive law and the left unit law by commutativity
   (int_mul_comm, module 53). The additive group is int_add_abstract_group
   of module 721. `}

def int_one : Int ≔ pos. (suc. zero.)

def int_add_left_swap (a b c : Int) : Id Int (int_add a (int_add b c)) (int_add b (int_add a c))
  ≔ calc
      int_add a (int_add b c) = int_add (int_add a b) c
        by inverse Int (int_add (int_add a b) c) (int_add a (int_add b c)) (int_add_assoc a b c)
      = int_add (int_add b a) c by refl ((v ↦ int_add v c) : Int → Int) (int_add_comm a b)
      = int_add b (int_add a c) by int_add_assoc b a c ∎

def int_mul_succ_right (x w : Int) : Id Int (int_mul x (int_succ w)) (int_add x (int_mul x w))
  ≔ match w [
  | pos. n ↦ refl (int_add x (int_mul x (pos. n)))
  | neg. zero. ↦ inverse Int (int_add x (int_neg x)) int_zero (int_add_neg_right x)
  | neg. (suc. n) ↦ inverse Int (int_add x (int_add (int_neg x) (int_mul x (neg. n)))) (int_mul x (neg. n))
      (int_translate_inverse_other x (int_mul x (neg. n))) ]

def int_mul_pred_right (x w : Int) : Id Int (int_mul x (int_pred w)) (int_add (int_neg x) (int_mul x w))
  ≔ match w [
  | pos. zero. ↦ refl (int_neg x)
  | pos. (suc. n) ↦ inverse Int (int_add (int_neg x) (int_add x (int_mul x (pos. n)))) (int_mul x (pos. n))
      (int_translate_inverse x (int_mul x (pos. n)))
  | neg. n ↦ refl (int_add (int_neg x) (int_mul x (neg. n))) ]

def int_mul_add_pos (x y : Int) (n : Nat)
  : Id Int (int_mul x (int_add y (pos. n))) (int_add (int_mul x y) (int_mul x (pos. n)))
  ≔ match n [
  | zero. ↦ refl (int_mul x y)
  | suc. n ↦ calc
      int_mul x (int_succ (int_add y (pos. n))) = int_add x (int_mul x (int_add y (pos. n)))
        by int_mul_succ_right x (int_add y (pos. n))
      = int_add x (int_add (int_mul x y) (int_mul x (pos. n))) by refl (int_add x) (int_mul_add_pos x y n)
      = int_add (int_mul x y) (int_add x (int_mul x (pos. n)))
        by int_add_left_swap x (int_mul x y) (int_mul x (pos. n)) ∎ ]

def int_mul_add_neg (x y : Int) (n : Nat)
  : Id Int (int_mul x (int_add y (neg. n))) (int_add (int_mul x y) (int_mul x (neg. n)))
  ≔ match n [
  | zero. ↦ calc
      int_mul x (int_pred y) = int_add (int_neg x) (int_mul x y) by int_mul_pred_right x y
      = int_add (int_mul x y) (int_neg x) by int_add_comm (int_neg x) (int_mul x y) ∎
  | suc. n ↦ calc
      int_mul x (int_pred (int_add y (neg. n))) = int_add (int_neg x) (int_mul x (int_add y (neg. n)))
        by int_mul_pred_right x (int_add y (neg. n))
      = int_add (int_neg x) (int_add (int_mul x y) (int_mul x (neg. n)))
        by refl (int_add (int_neg x)) (int_mul_add_neg x y n)
      = int_add (int_mul x y) (int_add (int_neg x) (int_mul x (neg. n)))
        by int_add_left_swap (int_neg x) (int_mul x y) (int_mul x (neg. n)) ∎ ]

{` The left distributive law a · (b + c) = a · b + a · c. `}
def int_mul_ldistr (x y z : Int) : Id Int (int_mul x (int_add y z)) (int_add (int_mul x y) (int_mul x z))
  ≔ match z [ pos. n ↦ int_mul_add_pos x y n | neg. n ↦ int_mul_add_neg x y n ]

{` The right distributive law (a + b) · c = a · c + b · c. `}
def int_mul_rdistr (x y z : Int) : Id Int (int_mul (int_add x y) z) (int_add (int_mul x z) (int_mul y z))
  ≔ calc
      int_mul (int_add x y) z = int_mul z (int_add x y) by int_mul_comm (int_add x y) z
      = int_add (int_mul z x) (int_mul z y) by int_mul_ldistr z x y
      = int_add (int_mul x z) (int_mul y z) by refl int_add (int_mul_comm z x) (int_mul_comm z y) ∎

def int_mul_neg_right (x y : Int) : Id Int (int_mul x (int_neg y)) (int_neg (int_mul x y))
  ≔ match y [
  | pos. zero. ↦ refl int_zero
  | pos. (suc. n) ↦ int_mul_neg_left_pos x (suc. n)
  | neg. n ↦ calc
      int_mul x (pos. (suc. n)) = int_neg (int_neg (int_mul x (pos. (suc. n))))
        by inverse Int (int_neg (int_neg (int_mul x (pos. (suc. n))))) (int_mul x (pos. (suc. n)))
          (int_neg_neg (int_mul x (pos. (suc. n))))
      = int_neg (int_mul (int_neg x) (pos. (suc. n)))
        by refl int_neg (inverse Int (int_mul (int_neg x) (pos. (suc. n))) (int_neg (int_mul x (pos. (suc. n))))
          (int_mul_neg_left_pos x (suc. n))) ∎ ]

def int_mul_assoc_pos (x y : Int) (n : Nat)
  : Id Int (int_mul x (int_mul y (pos. n))) (int_mul (int_mul x y) (pos. n))
  ≔ match n [
  | zero. ↦ refl int_zero
  | suc. n ↦ calc
      int_mul x (int_add y (int_mul y (pos. n))) = int_add (int_mul x y) (int_mul x (int_mul y (pos. n)))
        by int_mul_ldistr x y (int_mul y (pos. n))
      = int_add (int_mul x y) (int_mul (int_mul x y) (pos. n))
        by refl (int_add (int_mul x y)) (int_mul_assoc_pos x y n) ∎ ]

{` Associativity in the orientation of AssocLaw: a · (b · c) = (a · b) · c.
   For c = neg n both sides unfold to multiplication by n+1 of -b resp.
   -(a · b). `}
def int_mul_assoc (x y z : Int) : Id Int (int_mul x (int_mul y z)) (int_mul (int_mul x y) z)
  ≔ match z [
  | pos. n ↦ int_mul_assoc_pos x y n
  | neg. n ↦ calc
      int_mul x (int_mul (int_neg y) (pos. (suc. n))) = int_mul (int_mul x (int_neg y)) (pos. (suc. n))
        by int_mul_assoc_pos x (int_neg y) (suc. n)
      = int_mul (int_neg (int_mul x y)) (pos. (suc. n))
        by refl ((v ↦ int_mul v (pos. (suc. n))) : Int → Int) (int_mul_neg_right x y) ∎ ]

def int_mul_one_right (x : Int) : Id Int (int_mul x int_one) x ≔ refl x

def int_mul_one_left (x : Int) : Id Int (int_mul int_one x) x ≔ int_mul_comm int_one x

def int_mul_monoid_laws : MonoidLaws Int int_one int_mul
  ≔ (int_set, (x ↦ (int_mul_one_right x, int_mul_one_left x), int_mul_assoc))

{` The ring of integers (Int, 0, +, -, 1, ·). `}
def integer_ring : AbstractRing
  ≔ (Int, int_zero, int_add, int_neg, int_add_abstract_group_laws, int_one, int_mul, int_mul_monoid_laws,
     (int_mul_ldistr, int_mul_rdistr))

def integer_ring_commutative : IsCommutativeRing integer_ring ≔ int_mul_comm

def integer_ring_non_trivial : IsNonTrivialRing integer_ring ≔ p ↦ int_encode int_zero int_one p

def integer_commutative_ring : CommutativeRing ≔ (integer_ring, integer_ring_commutative)

{` Litmus: 2 · 3 = 6, (-2) · 3 = -6, (-2) · (-3) = 6 and 2 · (3 + (-5)) = -4,
   all by computation. `}
def integer_ring_litmus_mul
  : Id Int (integer_ring .mul (pos. 2) (pos. 3)) (pos. 6) ≔ refl (pos. 6 : Int)

def integer_ring_litmus_neg_mul
  : Id Int (integer_ring .mul (integer_ring .neg (pos. 2)) (pos. 3)) (integer_ring .neg (pos. 6))
  ≔ refl (neg. 5 : Int)

def integer_ring_litmus_neg_neg
  : Id Int (integer_ring .mul (neg. 1) (neg. 2)) (pos. 6) ≔ refl (pos. 6 : Int)

def integer_ring_litmus_distr
  : Id Int (integer_ring .mul (pos. 2) (integer_ring .add (pos. 3) (neg. 4))) (neg. 3) ≔ refl (neg. 3 : Int)
