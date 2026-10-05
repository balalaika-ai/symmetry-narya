export "53-integer-multiplication"

{` The two negative constructors encode -(m+1) and -(n+1),
   so comparing them reverses the natural-number order. `}
def IntLe (x y : Int) : Type ≔ match x, y [
  | pos. m, pos. n ↦ Le m n
  | pos. m, neg. n ↦ Empty
  | neg. m, pos. n ↦ Unit
  | neg. m, neg. n ↦ Le n m ]

def IntLt (x y : Int) : Type ≔ match x, y [
  | pos. m, pos. n ↦ Lt m n
  | pos. m, neg. n ↦ Empty
  | neg. m, pos. n ↦ Unit
  | neg. m, neg. n ↦ Lt n m ]

def int_le_prop (x y : Int) : isProp (IntLe x y) ≔ match x, y [
  | pos. m, pos. n ↦ le_prop m n
  | pos. m, neg. n ↦ empty_prop
  | neg. m, pos. n ↦ unit_prop
  | neg. m, neg. n ↦ le_prop n m ]

def int_lt_prop (x y : Int) : isProp (IntLt x y) ≔ match x, y [
  | pos. m, pos. n ↦ le_prop (suc. m) n
  | pos. m, neg. n ↦ empty_prop
  | neg. m, pos. n ↦ unit_prop
  | neg. m, neg. n ↦ le_prop (suc. n) m ]

def int_le_decidable (x y : Int) : Decidable (IntLe x y) ≔ match x, y [
  | pos. m, pos. n ↦ le_decidable m n
  | pos. m, neg. n ↦ inr. (h ↦ h)
  | neg. m, pos. n ↦ inl. star.
  | neg. m, neg. n ↦ le_decidable n m ]

def int_lt_decidable (x y : Int) : Decidable (IntLt x y) ≔ match x, y [
  | pos. m, pos. n ↦ lt_decidable m n
  | pos. m, neg. n ↦ inr. (h ↦ h)
  | neg. m, pos. n ↦ inl. star.
  | neg. m, neg. n ↦ lt_decidable n m ]

def int_le_naturals (m n : Nat) : Equiv (IntLe (int_of_nat m) (int_of_nat n)) (BookLe m n)
  ≔ le_book_equiv m n
def int_lt_naturals (m n : Nat) : Equiv (IntLt (int_of_nat m) (int_of_nat n)) (BookLt m n)
  ≔ lt_book_equiv m n

def int_le_refl (x : Int) : IntLe x x ≔ match x [ pos. n ↦ le_refl n | neg. n ↦ le_refl n ]

def int_le_trans (x y z : Int) (h : IntLe x y) (k : IntLe y z) : IntLe x z
  ≔ match x, y, z [
  | pos. a, pos. b, pos. c ↦ le_trans a b c h k
  | pos. a, pos. b, neg. c ↦ match k []
  | pos. a, neg. b, pos. c ↦ match h []
  | pos. a, neg. b, neg. c ↦ match h []
  | neg. a, pos. b, pos. c ↦ star.
  | neg. a, pos. b, neg. c ↦ match k []
  | neg. a, neg. b, pos. c ↦ star.
  | neg. a, neg. b, neg. c ↦ le_trans c b a k h ]

def int_le_antisym (x y : Int) (h : IntLe x y) (k : IntLe y x) : Id Int x y
  ≔ match x, y [
  | pos. m, pos. n ↦ pos. (le_antisym m n h k)
  | pos. m, neg. n ↦ match h []
  | neg. m, pos. n ↦ match k []
  | neg. m, neg. n ↦ neg. (le_antisym m n k h) ]

def int_le_total (x y : Int) : Sum (IntLe x y) (IntLe y x)
  ≔ match x, y [
  | pos. m, pos. n ↦ le_total m n
  | pos. m, neg. n ↦ inr. star.
  | neg. m, pos. n ↦ inl. star.
  | neg. m, neg. n ↦ le_total n m ]

def int_lt_irrefl (x : Int) : IntLt x x → Empty
  ≔ match x [ pos. n ↦ lt_irrefl n | neg. n ↦ lt_irrefl n ]

def int_lt_trans (x y z : Int) (h : IntLt x y) (k : IntLt y z) : IntLt x z
  ≔ match x, y, z [
  | pos. a, pos. b, pos. c ↦ lt_trans a b c h k
  | pos. a, pos. b, neg. c ↦ match k []
  | pos. a, neg. b, pos. c ↦ match h []
  | pos. a, neg. b, neg. c ↦ match h []
  | neg. a, pos. b, pos. c ↦ star.
  | neg. a, pos. b, neg. c ↦ match k []
  | neg. a, neg. b, pos. c ↦ star.
  | neg. a, neg. b, neg. c ↦ lt_trans c b a k h ]

def int_lt_le (x y : Int) (h : IntLt x y) : IntLe x y
  ≔ match x, y [
  | pos. m, pos. n ↦ lt_le m n h
  | pos. m, neg. n ↦ match h []
  | neg. m, pos. n ↦ star.
  | neg. m, neg. n ↦ lt_le n m h ]

def int_le_split (x y : Int) (h : IntLe x y) : Sum (IntLt x y) (Id Int x y)
  ≔ match x, y [
  | pos. m, pos. n ↦ match le_split m n h [ inl. p ↦ inl. p | inr. p ↦ inr. (pos. p) ]
  | pos. m, neg. n ↦ match h []
  | neg. m, pos. n ↦ inl. star.
  | neg. m, neg. n ↦ match le_split n m h [ inl. p ↦ inl. p | inr. p ↦ inr. (neg. (inverse Nat n m p)) ] ]

def int_lt_not_equal (x y : Int) (h : IntLt x y) (p : Id Int x y) : Empty
  ≔ int_lt_irrefl x (transport Int (IntLt x) y x (inverse Int x y p) h)

def int_le_from_equal (x y : Int) (p : Id Int x y) : IntLe x y
  ≔ transport Int (IntLe x) x y p (int_le_refl x)

def int_le_split_equiv (x y : Int) : Equiv (IntLe x y) (Sum (IntLt x y) (Id Int x y))
  ≔ iff_equiv (IntLe x y) (Sum (IntLt x y) (Id Int x y)) (int_le_prop x y)
      (disjoint_sum_prop (IntLt x y) (Id Int x y) (int_lt_prop x y) (int_set x y) (int_lt_not_equal x y))
      (int_le_split x y) [ inl. h ↦ int_lt_le x y h | inr. p ↦ int_le_from_equal x y p ]

def int_trichotomy (x y : Int) : Sum (IntLt x y) (Sum (Id Int x y) (IntLt y x))
  ≔ match int_le_total x y [
  | inl. h ↦ match int_le_split x y h [ inl. p ↦ inl. p | inr. p ↦ inr. (inl. p) ]
  | inr. h ↦ match int_le_split y x h [ inl. p ↦ inr. (inr. p) | inr. p ↦ inr. (inl. (inverse Int y x p)) ] ]

def int_le_succ_type (x y : Int) : Id Type (IntLe (int_succ x) (int_succ y)) (IntLe x y)
  ≔ match x, y [
  | pos. m, pos. n ↦ refl (Le m n)
  | pos. m, neg. zero. ↦ refl Empty
  | pos. m, neg. (suc. n) ↦ refl Empty
  | neg. zero., pos. n ↦ refl Unit
  | neg. (suc. m), pos. n ↦ refl Unit
  | neg. zero., neg. zero. ↦ refl Unit
  | neg. zero., neg. (suc. n) ↦ refl Empty
  | neg. (suc. m), neg. zero. ↦ refl Unit
  | neg. (suc. m), neg. (suc. n) ↦ refl (Le n m) ]

def int_lt_succ_type (x y : Int) : Id Type (IntLt (int_succ x) (int_succ y)) (IntLt x y)
  ≔ match x, y [
  | pos. m, pos. n ↦ refl (Lt m n)
  | pos. m, neg. zero. ↦ refl Empty
  | pos. m, neg. (suc. n) ↦ refl Empty
  | neg. zero., pos. n ↦ refl Unit
  | neg. (suc. m), pos. n ↦ refl Unit
  | neg. zero., neg. zero. ↦ refl Empty
  | neg. zero., neg. (suc. n) ↦ refl Empty
  | neg. (suc. m), neg. zero. ↦ refl Unit
  | neg. (suc. m), neg. (suc. n) ↦ refl (Lt n m) ]

def relation_iterate_invariance (R : Int → Int → Type) (f : Int → Int)
  (step : (x y : Int) → Id Type (R (f x) (f y)) (R x y)) (n : Nat) (x y : Int)
  : Id Type (R (iterate Int f n x) (iterate Int f n y)) (R x y)
  ≔ match n [
  | zero. ↦ refl (R x y)
  | suc. n ↦ concat Type
      (R (f (iterate Int f n x)) (f (iterate Int f n y)))
      (R (iterate Int f n x) (iterate Int f n y)) (R x y)
      (step (iterate Int f n x) (iterate Int f n y)) (relation_iterate_invariance R f step n x y) ]

def relation_pred_invariance (R : Int → Int → Type)
  (step : (x y : Int) → Id Type (R (int_succ x) (int_succ y)) (R x y)) (x y : Int)
  : Id Type (R (int_pred x) (int_pred y)) (R x y)
  ≔ calc
      R (int_pred x) (int_pred y) = R (int_succ (int_pred x)) (int_succ (int_pred y))
        by step (int_pred x) (int_pred y)
      = R x y by refl R (int_succ_pred x) (int_succ_pred y) ∎

def relation_translation_invariance (R : Int → Int → Type)
  (step : (x y : Int) → Id Type (R (int_succ x) (int_succ y)) (R x y)) (x y z : Int)
  : Id Type (R (int_add x z) (int_add y z)) (R x y)
  ≔ match z [
  | pos. n ↦ relation_iterate_invariance R int_succ step n x y
  | neg. n ↦ relation_iterate_invariance R int_pred (relation_pred_invariance R step) (suc. n) x y ]

def int_le_translation_equiv (x y z : Int) : Equiv (IntLe (int_add x z) (int_add y z)) (IntLe x y)
  ≔ id_to_equiv (IntLe (int_add x z) (int_add y z)) (IntLe x y)
      (relation_translation_invariance IntLe int_le_succ_type x y z)
def int_lt_translation_equiv (x y z : Int) : Equiv (IntLt (int_add x z) (int_add y z)) (IntLt x y)
  ≔ id_to_equiv (IntLt (int_add x z) (int_add y z)) (IntLt x y)
      (relation_translation_invariance IntLt int_lt_succ_type x y z)

def int_le_add_right (x y z : Int) (h : IntLe x y) : IntLe (int_add x z) (int_add y z)
  ≔ relation_translation_invariance IntLe int_le_succ_type x y z .trl h
def int_lt_add_right (x y z : Int) (h : IntLt x y) : IntLt (int_add x z) (int_add y z)
  ≔ relation_translation_invariance IntLt int_lt_succ_type x y z .trl h
def int_le_add_left (z x y : Int) (h : IntLe x y) : IntLe (int_add z x) (int_add z y)
  ≔ refl IntLe (int_add_comm x z) (int_add_comm y z) .trr (int_le_add_right x y z h)
def int_lt_add_left (z x y : Int) (h : IntLt x y) : IntLt (int_add z x) (int_add z y)
  ≔ refl IntLt (int_add_comm x z) (int_add_comm y z) .trr (int_lt_add_right x y z h)
