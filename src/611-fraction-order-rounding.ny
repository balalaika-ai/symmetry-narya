export "610-preorder-functors-and-adjoints"
export "148-order-gcd-lcm"

{` Chapter 6 (cats.tex), rem:adj-in-posets, the example ℤ ⊂ ℚ with
   ⌈-⌉ ⊣ ι ⊣ ⌊-⌋. The repository has no rational numbers. This module
   works with the preorder of fractions a/(k+1) (numerator a : ℤ,
   denominator k+1 > 0) ordered by cross multiplication,
   a/(k+1) ≤ b/(l+1) iff a(l+1) ≤ b(k+1). This preorder is not a poset
   (1/1 ≅ 2/2); its posetal reflection is ℚ with its usual order, which is
   built in module 612, where the adjunctions are transferred. Floor is
   the Euclidean quotient of module 55, and ⌈x⌉ = -⌊-x⌋. `}

{` Integer order lemmas used below (multiplication by positive naturals). `}
def frac_int_lt_le_trans (x y z : Int) (h : IntLt x y) (k : IntLe y z) : IntLt x z
  ≔ match int_le_split y z k [
    | inl. l ↦ int_lt_trans x y z h l
    | inr. p ↦ transport Int (w ↦ IntLt x w) y z p h ]

def frac_int_le_lt_trans (x y z : Int) (h : IntLe x y) (k : IntLt y z) : IntLt x z
  ≔ match int_le_split x y h [
    | inl. l ↦ int_lt_trans x y z l k
    | inr. p ↦ transport Int (w ↦ IntLt w z) y x (inverse Int x y p) k ]

def frac_int_le_rewrite (x x' y y' : Int) (p : Id Int x x') (q : Id Int y y') (h : IntLe x y) : IntLe x' y'
  ≔ transport Int (w ↦ IntLe x' w) y y' q (transport Int (w ↦ IntLe w y) x x' p h)

def frac_int_scale_le (x y : Int) (n : Nat) (h : IntLe x y)
  : IntLe (int_mul x (pos. n)) (int_mul y (pos. n))
  ≔ match n [
    | zero. ↦ int_le_refl int_zero
    | suc. n ↦ int_le_trans (int_add x (int_mul x (pos. n))) (int_add y (int_mul x (pos. n)))
        (int_add y (int_mul y (pos. n)))
        (int_le_add_right x y (int_mul x (pos. n)) h)
        (int_le_add_left y (int_mul x (pos. n)) (int_mul y (pos. n)) (frac_int_scale_le x y n h)) ]

def frac_int_scale_lt (x y : Int) (n : Nat) (h : IntLt x y)
  : IntLt (int_mul x (pos. (suc. n))) (int_mul y (pos. (suc. n)))
  ≔ frac_int_lt_le_trans (int_add x (int_mul x (pos. n))) (int_add y (int_mul x (pos. n)))
      (int_add y (int_mul y (pos. n)))
      (int_lt_add_right x y (int_mul x (pos. n)) h)
      (int_le_add_left y (int_mul x (pos. n)) (int_mul y (pos. n)) (frac_int_scale_le x y n (int_lt_le x y h)))

def frac_int_scale_cancel (x y : Int) (n : Nat)
  (h : IntLe (int_mul x (pos. (suc. n))) (int_mul y (pos. (suc. n)))) : IntLe x y
  ≔ match int_le_total x y [
    | inl. l ↦ l
    | inr. l ↦ match int_le_split y x l [
      | inl. s ↦ absurd (IntLe x y) (int_lt_irrefl (int_mul y (pos. (suc. n)))
          (frac_int_lt_le_trans (int_mul y (pos. (suc. n))) (int_mul x (pos. (suc. n))) (int_mul y (pos. (suc. n)))
            (frac_int_scale_lt y x n s) h))
      | inr. p ↦ int_le_from_equal x y (inverse Int y x p) ] ]

def frac_int_scale_swap (x : Int) (a b : Nat)
  : Id Int (int_mul (int_mul x (pos. a)) (pos. b)) (int_mul (int_mul x (pos. b)) (pos. a))
  ≔ concat Int (int_mul (int_mul x (pos. a)) (pos. b)) (int_mul x (pos. (mul a b)))
      (int_mul (int_mul x (pos. b)) (pos. a))
      (inverse Int (int_mul x (pos. (mul a b))) (int_mul (int_mul x (pos. a)) (pos. b)) (int_mul_pos_mul x a b))
      (concat Int (int_mul x (pos. (mul a b))) (int_mul x (pos. (mul b a))) (int_mul (int_mul x (pos. b)) (pos. a))
        (refl ((m ↦ int_mul x (pos. m)) : Nat → Int) (mul_comm a b))
        (int_mul_pos_mul x b a))

def frac_int_lt_succ_le (x y : Int) : IntLt x y → IntLe (int_succ x) y
  ≔ match x, y [
    | pos. m, pos. n ↦ h ↦ h
    | pos. m, neg. n ↦ h ↦ match h []
    | neg. m, pos. n ↦ h ↦ match m [ zero. ↦ star. | suc. m ↦ star. ]
    | neg. m, neg. n ↦ match m [ zero. ↦ h ↦ match h [] | suc. m ↦ h ↦ h ] ]

def frac_int_le_neg (x y : Int) (h : IntLe x y) : IntLe (int_neg y) (int_neg x)
  ≔ let z ≔ int_add (int_neg x) (int_neg y) in
    frac_int_le_rewrite (int_add x z) (int_neg y) (int_add y z) (int_neg x)
      (int_translate_inverse_other x (int_neg y))
      (concat Int (int_add y z) (int_add y (int_add (int_neg y) (int_neg x))) (int_neg x)
        (refl (int_add y) (int_add_comm (int_neg x) (int_neg y)))
        (int_translate_inverse_other y (int_neg x)))
      (int_le_add_right x y z h)

{` Fractions a/(k+1) and the cross-multiplication preorder. `}
def Frac : Type ≔ Product Int Nat

def FracLe (x y : Frac) : Type
  ≔ IntLe (int_mul (x .fst) (pos. (suc. (y .snd)))) (int_mul (y .fst) (pos. (suc. (x .snd))))

def frac_le_trans (x y z : Frac) (h : FracLe x y) (k : FracLe y z) : FracLe x z
  ≔ let a ≔ x .fst in let b ≔ y .fst in let c ≔ z .fst in
    let K : Nat ≔ suc. (x .snd) in let L : Nat ≔ suc. (y .snd) in let M : Nat ≔ suc. (z .snd) in
    let aL ≔ int_mul a (pos. L) in let bK ≔ int_mul b (pos. K) in
    let bM ≔ int_mul b (pos. M) in let cL ≔ int_mul c (pos. L) in
    let s1 ≔ frac_int_scale_le aL bK M h in
    let s2 ≔ frac_int_scale_le bM cL K k in
    let s2' ≔ frac_int_le_rewrite (int_mul bM (pos. K)) (int_mul bK (pos. M)) (int_mul cL (pos. K)) (int_mul cL (pos. K))
      (frac_int_scale_swap b M K) (refl (int_mul cL (pos. K))) s2 in
    let s3 ≔ int_le_trans (int_mul aL (pos. M)) (int_mul bK (pos. M)) (int_mul cL (pos. K)) s1 s2' in
    let s4 ≔ frac_int_le_rewrite (int_mul aL (pos. M)) (int_mul (int_mul a (pos. M)) (pos. L))
      (int_mul cL (pos. K)) (int_mul (int_mul c (pos. K)) (pos. L))
      (frac_int_scale_swap a L M) (frac_int_scale_swap c L K) s3 in
    frac_int_scale_cancel (int_mul a (pos. M)) (int_mul c (pos. K)) (y .snd) s4

def FracPreorder : Preorder
  ≔ preorder_of_relation (Frac,
      x y ↦ (FracLe x y, int_le_prop (int_mul (x .fst) (pos. (suc. (y .snd)))) (int_mul (y .fst) (pos. (suc. (x .snd))))),
      x ↦ int_le_refl (int_mul (x .fst) (pos. (suc. (x .snd)))),
      frac_le_trans)

{` The inclusion ι : ℤ → ℚ, n ↦ n/1. On these fractions the order is
   judgmentally the order of ℤ. `}
def frac_of_int (n : Int) : Frac ≔ (n, zero.)

def frac_of_int_order (m n : Int) : Id Type (FracLe (frac_of_int m) (frac_of_int n)) (IntLe m n)
  ≔ refl (IntLe m n)

def frac_inclusion_functor : WildFunctor (IntLeqPreorder .wild) (FracPreorder .wild)
  ≔ preorder_functor_of_monotone IntLeqPreorder FracPreorder (frac_of_int, m n h ↦ h)

{` Rounding down: ⌊a/(k+1)⌋ is the Euclidean quotient q with
   a = q(k+1) + r, 0 ≤ r < k+1. `}
def frac_positive (k : Nat) : BookLt zero. (suc. k) ≔ lt_to_book zero. (suc. k) star.

def frac_floor (x : Frac) : Int ≔ integer_quotient (x .fst) (suc. (x .snd)) (frac_positive (x .snd))

def frac_floor_remainder (x : Frac) : Nat ≔ integer_remainder (x .fst) (suc. (x .snd)) (frac_positive (x .snd))

def frac_floor_spec (x : Frac)
  : Product (BookLt (frac_floor_remainder x) (suc. (x .snd)))
      (Id Int (x .fst) (int_add (int_mul (frac_floor x) (pos. (suc. (x .snd)))) (pos. (frac_floor_remainder x))))
  ≔ integer_euclidean_division (x .fst) (suc. (x .snd)) (frac_positive (x .snd)) .snd

def frac_succ_scale (q : Int) (K : Nat)
  : Id Int (int_mul (int_succ q) (pos. K)) (int_add (int_mul q (pos. K)) (pos. K))
  ≔ concat Int (int_mul (int_succ q) (pos. K)) (int_add (int_mul q (pos. K)) (int_mul (pos. 1) (pos. K)))
      (int_add (int_mul q (pos. K)) (pos. K))
      (int_mul_add_left_pos q (pos. 1) K)
      (refl (int_add (int_mul q (pos. K))) (int_mul_comm (pos. 1) (pos. K)))

{` ι ⊣ ⌊-⌋: n/1 ≤ x iff n ≤ ⌊x⌋. `}
def frac_floor_iff (n : Int) (x : Frac)
  : Product (FracLe (frac_of_int n) x → IntLe n (frac_floor x)) (IntLe n (frac_floor x) → FracLe (frac_of_int n) x)
  ≔ let a ≔ x .fst in
    let K : Nat ≔ suc. (x .snd) in
    let q ≔ frac_floor x in
    let r ≔ frac_floor_remainder x in
    let qK ≔ int_mul q (pos. K) in
    let spec ≔ frac_floor_spec x in
    (h ↦ match int_le_total n q [
       | inl. l ↦ l
       | inr. l ↦ match int_le_split q n l [
         | inr. p ↦ int_le_from_equal n q (inverse Int q n p)
         | inl. s ↦
           let u2 : IntLe (int_mul (int_succ q) (pos. K)) a
             ≔ int_le_trans (int_mul (int_succ q) (pos. K)) (int_mul n (pos. K)) a
                 (frac_int_scale_le (int_succ q) n K (frac_int_lt_succ_le q n s)) h in
           let u3 : IntLt (int_add qK (pos. r)) (int_add qK (pos. K))
             ≔ int_lt_add_left qK (pos. r) (pos. K)
                 (equiv_inverse_map (IntLt (pos. r) (pos. K)) (BookLt r K) (int_lt_naturals r K) (spec .fst)) in
           let u3' : IntLt a (int_mul (int_succ q) (pos. K))
             ≔ transport Int (w ↦ IntLt a w) (int_add qK (pos. K)) (int_mul (int_succ q) (pos. K))
                 (inverse Int (int_mul (int_succ q) (pos. K)) (int_add qK (pos. K)) (frac_succ_scale q K))
                 (transport Int (w ↦ IntLt w (int_add qK (pos. K))) (int_add qK (pos. r)) a
                   (inverse Int a (int_add qK (pos. r)) (spec .snd)) u3) in
           absurd (IntLe n q) (int_lt_irrefl (int_mul (int_succ q) (pos. K))
             (frac_int_le_lt_trans (int_mul (int_succ q) (pos. K)) a (int_mul (int_succ q) (pos. K)) u2 u3')) ] ],
     h ↦ frac_int_le_rewrite (int_mul n (pos. K)) (int_mul n (pos. K)) (int_add qK (pos. r)) a
       (refl (int_mul n (pos. K))) (inverse Int a (int_add qK (pos. r)) (spec .snd))
       (int_le_trans (int_mul n (pos. K)) qK (int_add qK (pos. r))
         (frac_int_scale_le n q K h)
         (int_le_add_left qK int_zero (pos. r) star.)))

{` Rounding up: ⌈x⌉ = -⌊-x⌋, and ⌈-⌉ ⊣ ι: ⌈x⌉ ≤ n iff x ≤ n/1. `}
def frac_ceiling (x : Frac) : Int ≔ int_neg (frac_floor (int_neg (x .fst), x .snd))

def frac_ceiling_iff (x : Frac) (n : Int)
  : Product (IntLe (frac_ceiling x) n → FracLe x (frac_of_int n)) (FracLe x (frac_of_int n) → IntLe (frac_ceiling x) n)
  ≔ let a ≔ x .fst in
    let K : Nat ≔ suc. (x .snd) in
    let x' : Frac ≔ (int_neg a, x .snd) in
    let q' ≔ frac_floor x' in
    let nK ≔ int_mul n (pos. K) in
    (h ↦
       let v2 : IntLe (int_neg n) q'
         ≔ frac_int_le_rewrite (int_neg n) (int_neg n) (int_neg (int_neg q')) q' (refl (int_neg n)) (int_neg_neg q')
             (frac_int_le_neg (int_neg q') n h) in
       let v3 : IntLe (int_mul (int_neg n) (pos. K)) (int_neg a) ≔ frac_floor_iff (int_neg n) x' .snd v2 in
       let v4 : IntLe (int_neg nK) (int_neg a)
         ≔ frac_int_le_rewrite (int_mul (int_neg n) (pos. K)) (int_neg nK) (int_neg a) (int_neg a)
             (int_mul_neg_left_pos n K) (refl (int_neg a)) v3 in
       frac_int_le_rewrite (int_neg (int_neg a)) a (int_neg (int_neg nK)) nK (int_neg_neg a) (int_neg_neg nK)
         (frac_int_le_neg (int_neg nK) (int_neg a) v4),
     h ↦
       let w2 : IntLe (int_mul (int_neg n) (pos. K)) (int_neg a)
         ≔ frac_int_le_rewrite (int_neg nK) (int_mul (int_neg n) (pos. K)) (int_neg a) (int_neg a)
             (inverse Int (int_mul (int_neg n) (pos. K)) (int_neg nK) (int_mul_neg_left_pos n K)) (refl (int_neg a))
             (frac_int_le_neg a nK h) in
       let w3 : IntLe (int_neg n) q' ≔ frac_floor_iff (int_neg n) x' .fst w2 in
       frac_int_le_rewrite (int_neg q') (int_neg q') (int_neg (int_neg n)) n (refl (int_neg q')) (int_neg_neg n)
         (frac_int_le_neg (int_neg n) q' w3))

{` The two adjunctions ⌈-⌉ ⊣ ι ⊣ ⌊-⌋ (on the preorder of fractions). The
   floor and ceiling functors are the monotone maps given by the
   biimplications (module 610). `}
def frac_floor_right_adjoint : RightAdjointData (IntLeqPreorder .wild) (FracPreorder .wild) frac_inclusion_functor
  ≔ preorder_adjunction_from_right_map IntLeqPreorder FracPreorder frac_inclusion_functor frac_floor frac_floor_iff

def frac_ceiling_adjunction : WildAdjunction (FracPreorder .wild) (IntLeqPreorder .wild)
  ≔ preorder_adjunction_from_left_map FracPreorder IntLeqPreorder frac_inclusion_functor frac_ceiling frac_ceiling_iff

def frac_ceiling_adjunction_right
  : Id (WildFunctor (IntLeqPreorder .wild) (FracPreorder .wild)) (frac_ceiling_adjunction .right_adjoint .right)
      frac_inclusion_functor
  ≔ refl frac_inclusion_functor

def frac_floor_adjunction_right_obj
  : Id (Frac → Int) (frac_floor_right_adjoint .right .obj) frac_floor
  ≔ refl frac_floor

{` Litmus checks: ⌊7/2⌋ = 3, ⌈7/2⌉ = 4, ⌊-7/2⌋ = -4, ⌈-7/2⌉ = -3, and
   ⌊-6/3⌋ = ⌈-6/3⌉ = -2 (recall neg. n = -(n+1)). The fractions 1/1 and
   2/2 are isomorphic but different, so this preorder is not univalent. `}
def frac_floor_seven_halves : Id Int (frac_floor (pos. 7, 1)) (pos. 3) ≔ refl (pos. 3 : Int)
def frac_ceiling_seven_halves : Id Int (frac_ceiling (pos. 7, 1)) (pos. 4) ≔ refl (pos. 4 : Int)
def frac_floor_minus_seven_halves : Id Int (frac_floor (neg. 6, 1)) (neg. 3) ≔ refl (neg. 3 : Int)
def frac_ceiling_minus_seven_halves : Id Int (frac_ceiling (neg. 6, 1)) (neg. 2) ≔ refl (neg. 2 : Int)
def frac_floor_minus_two : Id Int (frac_floor (neg. 5, 2)) (neg. 1) ≔ refl (neg. 1 : Int)
def frac_ceiling_minus_two : Id Int (frac_ceiling (neg. 5, 2)) (neg. 1) ≔ refl (neg. 1 : Int)

def frac_one_two_halves_iso : CatIso (FracPreorder .wild) (pos. 1, zero.) (pos. 2, 1)
  ≔ preorder_iso_of_arrows FracPreorder (pos. 1, zero.) (pos. 2, 1) star. star.

def frac_preorder_not_univalent (u : IsUnivalentCat (FracPreorder .wild)) : Empty
  ≔ nat_encode zero. 1 (preorder_univalent_antisymmetric FracPreorder u (pos. 1, zero.) (pos. 2, 1) star. star. .snd)
