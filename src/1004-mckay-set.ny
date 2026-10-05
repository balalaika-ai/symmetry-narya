export "1012-finite-group-orders"
export "1010-usym-powers"
export "1001-divisibility-lemmas"

{` Chapter 10 (fingp.tex 124–202), the combinatorial core of Cauchy's
   theorem (thm:cauchys): McKay's set of p-tuples with product e.

   Indexing. A p-tuple (p = b+1) is a function t : Remainder (b+1) → USym G
   (Z/p of module 56/75); succ = modular_successor b, 0 = mckay_zero b.
   mckay_product G b t s k = t(s)·t(s+1)···t(s+k−1) (head first, the book's
   g_0 g_1 ··· g_{p−1} for s = 0, k = p; g·h = usym_mul G g h).

   McKaySet G b = Σ_t (t(0)···t(b) = e). The book's X(Z/p) asks the product
   to be e along every rotation σ of the indices; McKayConditionRotations
   is that form and mckay_condition_rotations_equiv shows it is equivalent.
   mckay_rotate (t ↦ t ∘ succ) is a permutation of McKaySet whose (b+1)-st
   iterate is the identity (uses "a·B = e ⇒ B·a = e").

   Counting (the book: "the condition says exactly that we can reconstruct
   g_0"): McKaySet ≃ (Remainder b → USym G) by dropping t(0)
   (mckay_set_tail_equiv), so |McKaySet| = |G|^b (mckay_set_card) and p | |G|,
   b ≥ 1 give p | |McKaySet| (mckay_set_card_divisible).

   Fixed points: rotation-fixed tuples are constant, and the product of the
   constant tuple g is g^(b+1), so Σ_x (rotate x = x) ≃ Σ_g (g^(b+1) = e)
   (mckay_fixed_points_equiv). `}

def mckay_zero (b : Nat) : Remainder (suc. b) ≔ remainder_at b zero. star.

def mckay_product (G : Group) (b : Nat) (t : Remainder (suc. b) → USym G) (s : Remainder (suc. b)) (k : Nat) : USym G
  ≔ match k [
  | zero. ↦ usym_unit G
  | suc. k ↦ usym_mul G (t s) (mckay_product G b t (modular_successor b s) k) ]

{` Group-law helpers in path algebra (g·h = concat h g). `}
def mckay_usym_assoc (G : Group) (g1 g2 g3 : USym G)
  : Id (USym G) (usym_mul G g1 (usym_mul G g2 g3)) (usym_mul G (usym_mul G g1 g2) g3)
  ≔ concat_assoc (BG G .carrier) (shape G) (shape G) (shape G) (shape G) g3 g2 g1

def mckay_mul_ap (G : Group) (g g' h h' : USym G) (p : Id (USym G) g g') (q : Id (USym G) h h')
  : Id (USym G) (usym_mul G g h) (usym_mul G g' h')
  ≔ concat (USym G) (usym_mul G g h) (usym_mul G g' h) (usym_mul G g' h')
      (refl ((x ↦ usym_mul G x h) : USym G → USym G) p) (refl (usym_mul G g') q)

def mckay_mul_unit_left_inverse (G : Group) (g h : USym G) (e : Id (USym G) (usym_mul G g h) (usym_unit G))
  : Id (USym G) g (usym_inv G h)
  ≔ let A ≔ BG G .carrier in let a ≔ shape G in
    calc
      g = concat A a a a (inverse A a a h) (concat A a a a h g)
        by inverse (Id A a a) (concat A a a a (inverse A a a h) (concat A a a a h g)) g
          (concat_left_inverse_cancel A a a a h g)
      = concat A a a a (inverse A a a h) (refl a) by refl (concat A a a a (inverse A a a h)) e
      = inverse A a a h by concat_p1 A a a (inverse A a a h) ∎

{` a·B = e ⇒ B·a = e. `}
def mckay_mul_unit_swap (G : Group) (g h : USym G) (e : Id (USym G) (usym_mul G g h) (usym_unit G))
  : Id (USym G) (usym_mul G h g) (usym_unit G)
  ≔ let A ≔ BG G .carrier in let a ≔ shape G in
    concat (Id A a a) (concat A a a a g h) (concat A a a a (inverse A a a h) h) (refl a)
      (refl ((x ↦ concat A a a a x h) : Id A a a → Id A a a) (mckay_mul_unit_left_inverse G g h e))
      (concat_inverse_left A a a h)

{` Shift (rotation of the tuple) and append-at-the-end. `}
def mckay_product_shift (G : Group) (b : Nat) (t : Remainder (suc. b) → USym G) (s : Remainder (suc. b)) (k : Nat)
  : Id (USym G) (mckay_product G b (r ↦ t (modular_successor b r)) s k) (mckay_product G b t (modular_successor b s) k)
  ≔ match k [
  | zero. ↦ refl (usym_unit G)
  | suc. k ↦ refl (usym_mul G (t (modular_successor b s))) (mckay_product_shift G b t (modular_successor b s) k) ]

def mckay_product_snoc (G : Group) (b : Nat) (t : Remainder (suc. b) → USym G) (s : Remainder (suc. b)) (k : Nat)
  : Id (USym G) (mckay_product G b t s (suc. k))
      (usym_mul G (mckay_product G b t s k) (t (iterate (Remainder (suc. b)) (modular_successor b) k s)))
  ≔ match k [
  | zero. ↦ concat (USym G) (usym_mul G (t s) (usym_unit G)) (t s) (usym_mul G (usym_unit G) (t s))
      (concat_1p (BG G .carrier) (shape G) (shape G) (t s))
      (inverse (USym G) (usym_mul G (usym_unit G) (t s)) (t s) (concat_p1 (BG G .carrier) (shape G) (shape G) (t s)))
  | suc. k ↦
    let R ≔ Remainder (suc. b) in let f ≔ modular_successor b in
    calc
      usym_mul G (t s) (mckay_product G b t (f s) (suc. k))
      = usym_mul G (t s) (usym_mul G (mckay_product G b t (f s) k) (t (iterate R f k (f s))))
        by refl (usym_mul G (t s)) (mckay_product_snoc G b t (f s) k)
      = usym_mul G (usym_mul G (t s) (mckay_product G b t (f s) k)) (t (iterate R f k (f s)))
        by mckay_usym_assoc G (t s) (mckay_product G b t (f s) k) (t (iterate R f k (f s)))
      = usym_mul G (mckay_product G b t s (suc. k)) (t (iterate R f (suc. k) s))
        by refl (usym_mul G (mckay_product G b t s (suc. k))) (refl t (iterate_shift R f k s)) ∎ ]

{` The McKay set. `}
def McKayCondition (G : Group) (b : Nat) (t : Remainder (suc. b) → USym G) : Type
  ≔ Id (USym G) (mckay_product G b t (mckay_zero b) (suc. b)) (usym_unit G)

def McKaySet (G : Group) (b : Nat) : Type ≔ Σ (Remainder (suc. b) → USym G) (t ↦ McKayCondition G b t)

def mckay_condition_prop (G : Group) (b : Nat) (t : Remainder (suc. b) → USym G) : isProp (McKayCondition G b t)
  ≔ usym_set G (mckay_product G b t (mckay_zero b) (suc. b)) (usym_unit G)

def mckay_set_is_set (G : Group) (b : Nat) : isSet (McKaySet G b)
  ≔ sigma_set (Remainder (suc. b) → USym G) (McKayCondition G b)
      (pi_set (Remainder (suc. b)) (_ ↦ USym G) (_ ↦ usym_set G))
      (t ↦ prop_is_set (McKayCondition G b t) (mckay_condition_prop G b t))

{` Index facts: r = succ^r(0), and succ^(b+1) = id. `}
def mckay_index_iterate (b : Nat) (r : Remainder (suc. b))
  : Id (Remainder (suc. b)) (iterate (Remainder (suc. b)) (modular_successor b) (r .fst) (mckay_zero b)) r
  ≔ concat (Remainder (suc. b)) (iterate (Remainder (suc. b)) (modular_successor b) (r .fst) (mckay_zero b))
      (remainder_at b (r .fst) (lt_from_book (r .fst) (suc. b) (r .snd))) r
      (modular_successor_iterate b (r .fst) (lt_from_book (r .fst) (suc. b) (r .snd)))
      (remainder_equal (suc. b) (remainder_at b (r .fst) (lt_from_book (r .fst) (suc. b) (r .snd))) r (refl (r .fst)))

def mckay_succ_zero_period (b : Nat)
  : Id (Remainder (suc. b)) (iterate (Remainder (suc. b)) (modular_successor b) (suc. b) (mckay_zero b)) (mckay_zero b)
  ≔ concat (Remainder (suc. b)) (iterate (Remainder (suc. b)) (modular_successor b) (suc. b) (mckay_zero b))
      (modular_successor b (remainder_at b b (le_refl b))) (mckay_zero b)
      (refl (modular_successor b) (modular_successor_iterate b b (le_refl b)))
      (modular_successor_last b)

def mckay_succ_period (b : Nat) (r : Remainder (suc. b))
  : Id (Remainder (suc. b)) (iterate (Remainder (suc. b)) (modular_successor b) (suc. b) r) r
  ≔ let R ≔ Remainder (suc. b) in let f ≔ modular_successor b in let z ≔ mckay_zero b in let k ≔ r .fst in
    calc
      iterate R f (suc. b) r = iterate R f (suc. b) (iterate R f k z)
        by refl (iterate R f (suc. b)) (inverse R (iterate R f k z) r (mckay_index_iterate b r))
      = iterate R f (add k (suc. b)) z
        by inverse R (iterate R f (add k (suc. b)) z) (iterate R f (suc. b) (iterate R f k z)) (iterate_add R f k (suc. b) z)
      = iterate R f (add (suc. b) k) z by refl ((m ↦ iterate R f m z) : Nat → R) (add_comm k (suc. b))
      = iterate R f k (iterate R f (suc. b) z) by iterate_add R f (suc. b) k z
      = iterate R f k z by refl (iterate R f k) (mckay_succ_zero_period b)
      = r by mckay_index_iterate b r ∎

{` If the product starting at s is e, so is the product starting at s+1. `}
def mckay_product_rotate_step (G : Group) (b : Nat) (t : Remainder (suc. b) → USym G) (s : Remainder (suc. b))
  (h : Id (USym G) (mckay_product G b t s (suc. b)) (usym_unit G))
  : Id (USym G) (mckay_product G b t (modular_successor b s) (suc. b)) (usym_unit G)
  ≔ let R ≔ Remainder (suc. b) in let f ≔ modular_successor b in
    calc
      mckay_product G b t (f s) (suc. b)
      = usym_mul G (mckay_product G b t (f s) b) (t (iterate R f b (f s))) by mckay_product_snoc G b t (f s) b
      = usym_mul G (mckay_product G b t (f s) b) (t s)
        by refl (usym_mul G (mckay_product G b t (f s) b))
          (refl t (concat R (iterate R f b (f s)) (iterate R f (suc. b) s) s (iterate_shift R f b s) (mckay_succ_period b s)))
      = usym_unit G by mckay_mul_unit_swap G (t s) (mckay_product G b t (f s) b) h ∎

{` The book's form of the condition: the product is e along every rotation. `}
def McKayConditionRotations (G : Group) (b : Nat) (t : Remainder (suc. b) → USym G) : Type
  ≔ (s : Remainder (suc. b)) → Id (USym G) (mckay_product G b t s (suc. b)) (usym_unit G)

def mckay_condition_iterate (G : Group) (b : Nat) (t : Remainder (suc. b) → USym G) (h : McKayCondition G b t) (k : Nat)
  : Id (USym G) (mckay_product G b t (iterate (Remainder (suc. b)) (modular_successor b) k (mckay_zero b)) (suc. b)) (usym_unit G)
  ≔ match k [
  | zero. ↦ h
  | suc. k ↦ mckay_product_rotate_step G b t (iterate (Remainder (suc. b)) (modular_successor b) k (mckay_zero b))
      (mckay_condition_iterate G b t h k) ]

def mckay_condition_rotations_equiv (G : Group) (b : Nat) (t : Remainder (suc. b) → USym G)
  : Equiv (McKayCondition G b t) (McKayConditionRotations G b t)
  ≔ let R ≔ Remainder (suc. b) in
    let P : R → Type ≔ s ↦ Id (USym G) (mckay_product G b t s (suc. b)) (usym_unit G) in
    iff_equiv (McKayCondition G b t) (McKayConditionRotations G b t) (mckay_condition_prop G b t)
      (pi_prop R P (s ↦ usym_set G (mckay_product G b t s (suc. b)) (usym_unit G)))
      (h s ↦ transport R P (iterate R (modular_successor b) (s .fst) (mckay_zero b)) s (mckay_index_iterate b s)
        (mckay_condition_iterate G b t h (s .fst)))
      (h ↦ h (mckay_zero b))

{` The rotation t ↦ t ∘ succ, its iterates, and (b+1)-periodicity. `}
def mckay_rotate (G : Group) (b : Nat) (x : McKaySet G b) : McKaySet G b
  ≔ (r ↦ x .fst (modular_successor b r),
     concat (USym G) (mckay_product G b (r ↦ x .fst (modular_successor b r)) (mckay_zero b) (suc. b))
       (mckay_product G b (x .fst) (modular_successor b (mckay_zero b)) (suc. b)) (usym_unit G)
       (mckay_product_shift G b (x .fst) (mckay_zero b) (suc. b))
       (mckay_product_rotate_step G b (x .fst) (mckay_zero b) (x .snd)))

def mckay_rotate_iterate_entry (G : Group) (b : Nat) (x : McKaySet G b) (k : Nat) (r : Remainder (suc. b))
  : Id (USym G) (iterate (McKaySet G b) (mckay_rotate G b) k x .fst r)
      (x .fst (iterate (Remainder (suc. b)) (modular_successor b) k r))
  ≔ match k [
  | zero. ↦ refl (x .fst r)
  | suc. k ↦ concat (USym G) (iterate (McKaySet G b) (mckay_rotate G b) k x .fst (modular_successor b r))
      (x .fst (iterate (Remainder (suc. b)) (modular_successor b) k (modular_successor b r)))
      (x .fst (iterate (Remainder (suc. b)) (modular_successor b) (suc. k) r))
      (mckay_rotate_iterate_entry G b x k (modular_successor b r))
      (refl (x .fst) (iterate_shift (Remainder (suc. b)) (modular_successor b) k r)) ]

def mckay_rotate_period (G : Group) (b : Nat) (x : McKaySet G b)
  : Id (McKaySet G b) (iterate (McKaySet G b) (mckay_rotate G b) (suc. b) x) x
  ≔ let R ≔ Remainder (suc. b) in let y ≔ iterate (McKaySet G b) (mckay_rotate G b) (suc. b) x in
    subtype_equal (R → USym G) (McKayCondition G b) (mckay_condition_prop G b) y x
      (funext R (_ ↦ USym G) (y .fst) (x .fst)
        (r ↦ concat (USym G) (y .fst r) (x .fst (iterate R (modular_successor b) (suc. b) r)) (x .fst r)
          (mckay_rotate_iterate_entry G b x (suc. b) r) (refl (x .fst) (mckay_succ_period b r))))

def mckay_rotate_equiv (G : Group) (b : Nat) : Equiv (McKaySet G b) (McKaySet G b)
  ≔ let M ≔ McKaySet G b in let rot ≔ mckay_rotate G b in
    quasi_inverse_equiv M M rot (iterate M rot b)
      (x ↦ concat M (iterate M rot b (rot x)) (iterate M rot (suc. b) x) x
        (iterate_shift M rot b x) (mckay_rotate_period G b x))
      (x ↦ mckay_rotate_period G b x)

{` Dropping t(0): tail and its inverse (extend by a value at 0). `}
def mckay_lt_succ (k b : Nat) (h : BookLt k b) : BookLt (suc. k) (suc. b) ≔ lt_to_book (suc. k) (suc. b) (lt_from_book k b h)

def mckay_lt_pred (k b : Nat) (h : BookLt (suc. k) (suc. b)) : BookLt k b ≔ lt_to_book k b (lt_from_book (suc. k) (suc. b) h)

def mckay_tail (G : Group) (b : Nat) (t : Remainder (suc. b) → USym G) (r : Remainder b) : USym G
  ≔ t (suc. (r .fst), mckay_lt_succ (r .fst) b (r .snd))

def mckay_extend_at (G : Group) (b : Nat) (a : USym G) (f : Remainder b → USym G) (k : Nat) : BookLt k (suc. b) → USym G
  ≔ match k [
  | zero. ↦ _ ↦ a
  | suc. k ↦ h ↦ f (k, mckay_lt_pred k b h) ]

def mckay_extend (G : Group) (b : Nat) (a : USym G) (f : Remainder b → USym G) (r : Remainder (suc. b)) : USym G
  ≔ mckay_extend_at G b a f (r .fst) (r .snd)

def mckay_tail_extend (G : Group) (b : Nat) (a : USym G) (f : Remainder b → USym G) (r : Remainder b)
  : Id (USym G) (mckay_tail G b (mckay_extend G b a f) r) (f r)
  ≔ refl f (remainder_equal b (r .fst, mckay_lt_pred (r .fst) b (mckay_lt_succ (r .fst) b (r .snd))) r (refl (r .fst)))

def mckay_extend_eta_at (G : Group) (b : Nat) (t : Remainder (suc. b) → USym G) (a : USym G)
  (ha : Id (USym G) a (t (mckay_zero b))) (k : Nat)
  : (h : BookLt k (suc. b)) → Id (USym G) (mckay_extend_at G b a (mckay_tail G b t) k h) (t (k, h))
  ≔ match k [
  | zero. ↦ h ↦ concat (USym G) a (t (mckay_zero b)) (t (zero., h)) ha
      (refl t (remainder_equal (suc. b) (mckay_zero b) (zero., h) (refl (zero. : Nat))))
  | suc. k ↦ h ↦ refl t (remainder_equal (suc. b) (suc. k, mckay_lt_succ k b (mckay_lt_pred k b h)) (suc. k, h)
      (refl (suc. k : Nat))) ]

{` The product t(1)···t(b) only depends on the tail of t. `}
def mckay_tail_index_path (b i : Nat) (hi : Lt i b)
  : Id (Remainder (suc. b)) (iterate (Remainder (suc. b)) (modular_successor b) i (modular_successor b (mckay_zero b)))
      (suc. i, mckay_lt_succ i b (lt_to_book i b hi))
  ≔ let R ≔ Remainder (suc. b) in let f ≔ modular_successor b in let z ≔ mckay_zero b in
    concat R (iterate R f i (f z)) (iterate R f (suc. i) z) (suc. i, mckay_lt_succ i b (lt_to_book i b hi))
      (iterate_shift R f i z)
      (concat R (iterate R f (suc. i) z) (remainder_at b (suc. i) hi) (suc. i, mckay_lt_succ i b (lt_to_book i b hi))
        (modular_successor_iterate b (suc. i) hi)
        (remainder_equal (suc. b) (remainder_at b (suc. i) hi) (suc. i, mckay_lt_succ i b (lt_to_book i b hi))
          (refl (suc. i : Nat))))

def mckay_product_congr_step (G : Group) (b : Nat) (t t' : Remainder (suc. b) → USym G) (s : Remainder (suc. b)) (i : Nat)
  (h : Id (USym G) (t (iterate (Remainder (suc. b)) (modular_successor b) (suc. i) s))
         (t' (iterate (Remainder (suc. b)) (modular_successor b) (suc. i) s)))
  : Id (USym G) (t (iterate (Remainder (suc. b)) (modular_successor b) i (modular_successor b s)))
      (t' (iterate (Remainder (suc. b)) (modular_successor b) i (modular_successor b s)))
  ≔ let R ≔ Remainder (suc. b) in let f ≔ modular_successor b in
    concat (USym G) (t (iterate R f i (f s))) (t (iterate R f (suc. i) s)) (t' (iterate R f i (f s)))
      (refl t (iterate_shift R f i s))
      (concat (USym G) (t (iterate R f (suc. i) s)) (t' (iterate R f (suc. i) s)) (t' (iterate R f i (f s)))
        h (refl t' (inverse R (iterate R f i (f s)) (iterate R f (suc. i) s) (iterate_shift R f i s))))

def mckay_product_congr (G : Group) (b : Nat) (t t' : Remainder (suc. b) → USym G) (s : Remainder (suc. b)) (k : Nat)
  : ((i : Nat) → Lt i k → Id (USym G) (t (iterate (Remainder (suc. b)) (modular_successor b) i s))
                                    (t' (iterate (Remainder (suc. b)) (modular_successor b) i s)))
    → Id (USym G) (mckay_product G b t s k) (mckay_product G b t' s k)
  ≔ match k [
  | zero. ↦ _ ↦ refl (usym_unit G)
  | suc. k ↦ h ↦ mckay_mul_ap G (t s) (t' s) (mckay_product G b t (modular_successor b s) k)
      (mckay_product G b t' (modular_successor b s) k) (h zero. star.)
      (mckay_product_congr G b t t' (modular_successor b s) k
        (i hi ↦ mckay_product_congr_step G b t t' s i (h (suc. i) hi))) ]

def mckay_product_tail_at (G : Group) (b : Nat) (t t' : Remainder (suc. b) → USym G)
  (h : (r : Remainder b) → Id (USym G) (mckay_tail G b t r) (mckay_tail G b t' r)) (i : Nat) (hi : Lt i b)
  : Id (USym G) (t (iterate (Remainder (suc. b)) (modular_successor b) i (modular_successor b (mckay_zero b))))
      (t' (iterate (Remainder (suc. b)) (modular_successor b) i (modular_successor b (mckay_zero b))))
  ≔ let R ≔ Remainder (suc. b) in
    let x ≔ iterate R (modular_successor b) i (modular_successor b (mckay_zero b)) in
    let y : R ≔ (suc. i, mckay_lt_succ i b (lt_to_book i b hi)) in
    let p ≔ mckay_tail_index_path b i hi in
    concat (USym G) (t x) (t y) (t' x) (refl t p)
      (concat (USym G) (t y) (t' y) (t' x) (h (i, lt_to_book i b hi)) (refl t' (inverse R x y p)))

def mckay_product_tail (G : Group) (b : Nat) (t t' : Remainder (suc. b) → USym G)
  (h : (r : Remainder b) → Id (USym G) (mckay_tail G b t r) (mckay_tail G b t' r))
  : Id (USym G) (mckay_product G b t (modular_successor b (mckay_zero b)) b)
      (mckay_product G b t' (modular_successor b (mckay_zero b)) b)
  ≔ mckay_product_congr G b t t' (modular_successor b (mckay_zero b)) b (i hi ↦ mckay_product_tail_at G b t t' h i hi)

{` McKaySet ≃ (Remainder b → USym G): t(0) is determined by the others. `}
def mckay_tail_product (G : Group) (b : Nat) (f : Remainder b → USym G) : USym G
  ≔ mckay_product G b (mckay_extend G b (usym_unit G) f) (modular_successor b (mckay_zero b)) b

def mckay_extend_tail_product (G : Group) (b : Nat) (a : USym G) (f : Remainder b → USym G)
  : Id (USym G) (mckay_product G b (mckay_extend G b a f) (modular_successor b (mckay_zero b)) b) (mckay_tail_product G b f)
  ≔ mckay_product_tail G b (mckay_extend G b a f) (mckay_extend G b (usym_unit G) f)
      (r ↦ concat (USym G) (mckay_tail G b (mckay_extend G b a f) r) (f r) (mckay_tail G b (mckay_extend G b (usym_unit G) f) r)
        (mckay_tail_extend G b a f r)
        (inverse (USym G) (mckay_tail G b (mckay_extend G b (usym_unit G) f) r) (f r) (mckay_tail_extend G b (usym_unit G) f r)))

def mckay_from_tail_condition (G : Group) (b : Nat) (f : Remainder b → USym G)
  : McKayCondition G b (mckay_extend G b (usym_inv G (mckay_tail_product G b f)) f)
  ≔ let c ≔ mckay_tail_product G b f in let a ≔ usym_inv G c in
    concat (USym G) (usym_mul G a (mckay_product G b (mckay_extend G b a f) (modular_successor b (mckay_zero b)) b))
      (usym_mul G a c) (usym_unit G)
      (refl (usym_mul G a) (mckay_extend_tail_product G b a f))
      (concat_inverse_right (BG G .carrier) (shape G) (shape G) c)

def mckay_from_tail (G : Group) (b : Nat) (f : Remainder b → USym G) : McKaySet G b
  ≔ (mckay_extend G b (usym_inv G (mckay_tail_product G b f)) f, mckay_from_tail_condition G b f)

def mckay_to_tail (G : Group) (b : Nat) (x : McKaySet G b) : Remainder b → USym G ≔ mckay_tail G b (x .fst)

def mckay_from_to_tail (G : Group) (b : Nat) (x : McKaySet G b)
  : Id (McKaySet G b) (mckay_from_tail G b (mckay_to_tail G b x)) x
  ≔ let R ≔ Remainder (suc. b) in let t ≔ x .fst in let z ≔ mckay_zero b in let u ≔ modular_successor b z in
    let f ≔ mckay_tail G b t in
    let a ≔ usym_inv G (mckay_tail_product G b f) in
    let hc : Id (USym G) (mckay_product G b t u b) (mckay_tail_product G b f)
      ≔ mckay_product_tail G b t (mckay_extend G b (usym_unit G) f)
          (r ↦ inverse (USym G) (mckay_tail G b (mckay_extend G b (usym_unit G) f) r) (f r)
            (mckay_tail_extend G b (usym_unit G) f r)) in
    let ha : Id (USym G) a (t z)
      ≔ inverse (USym G) (t z) a
          (concat (USym G) (t z) (usym_inv G (mckay_product G b t u b)) a
            (mckay_mul_unit_left_inverse G (t z) (mckay_product G b t u b) (x .snd))
            (refl (usym_inv G) hc)) in
    subtype_equal (R → USym G) (McKayCondition G b) (mckay_condition_prop G b) (mckay_from_tail G b f) x
      (funext R (_ ↦ USym G) (mckay_extend G b a f) t (r ↦ mckay_extend_eta_at G b t a ha (r .fst) (r .snd)))

def mckay_set_tail_equiv (G : Group) (b : Nat) : Equiv (McKaySet G b) (Remainder b → USym G)
  ≔ quasi_inverse_equiv (McKaySet G b) (Remainder b → USym G) (mckay_to_tail G b) (mckay_from_tail G b)
      (mckay_from_to_tail G b)
      (f ↦ funext (Remainder b) (_ ↦ USym G) (mckay_tail G b (mckay_extend G b (usym_inv G (mckay_tail_product G b f)) f)) f
        (mckay_tail_extend G b (usym_inv G (mckay_tail_product G b f)) f))

{` |McKaySet| = |G|^b. `}
def fingp_precompose_equiv (X Y Z : Type) (e : Equiv X Y) : Equiv (Y → Z) (X → Z)
  ≔ quasi_inverse_equiv (Y → Z) (X → Z) (f x ↦ f (e .map x)) (g y ↦ g (equiv_inverse_map X Y e y))
      (f ↦ funext Y (_ ↦ Z) (y ↦ f (e .map (equiv_inverse_map X Y e y))) f (y ↦ refl f (equiv_counit X Y e y)))
      (g ↦ funext X (_ ↦ Z) (x ↦ g (equiv_inverse_map X Y e (e .map x))) g (x ↦ refl g (equiv_retraction X Y e x)))

def mckay_set_fin_equiv (G : Group) (b : Nat) : Equiv (McKaySet G b) (Fin b → USym G)
  ≔ compose_equiv (McKaySet G b) (Remainder b → USym G) (Fin b → USym G) (mckay_set_tail_equiv G b)
      (fingp_precompose_equiv (Fin b) (Remainder b) (USym G) (fin_book_below_equiv b))

def mckay_set_finite (G : Group) (b : Nat) (hG : IsFiniteGroup G) : IsFinite (McKaySet G b)
  ≔ finite_of_equiv (McKaySet G b) (Fin b → USym G) (mckay_set_fin_equiv G b) (fin_functions_finite b (USym G) hG)

def mckay_set_card (G : Group) (b : Nat) (hG : IsFiniteGroup G) (h : IsFinite (McKaySet G b))
  : Id Nat (cardinality (McKaySet G b) h) (nat_power (group_card G hG) b)
  ≔ concat Nat (cardinality (McKaySet G b) h) (cardinality (Fin b → USym G) (fin_functions_finite b (USym G) hG))
      (nat_power (group_card G hG) b)
      (cardinality_equiv (McKaySet G b) (Fin b → USym G) (mckay_set_fin_equiv G b) h (fin_functions_finite b (USym G) hG))
      (fin_functions_card b (USym G) hG (fin_functions_finite b (USym G) hG))

def mckay_power_divisible (p c : Nat) (hd : NatDivides p c) (b : Nat) : Lt zero. b → NatDivides p (nat_power c b)
  ≔ match b [
  | zero. ↦ hb ↦ match hb []
  | suc. b ↦ _ ↦ nat_divides_mul_left p (nat_power c b) c hd ]

def mckay_set_card_divisible (p : Nat) (G : Group) (b : Nat) (hG : IsFiniteGroup G) (h : IsFinite (McKaySet G b))
  (hb : Lt zero. b) (hd : NatDivides p (group_card G hG))
  : NatDivides p (cardinality (McKaySet G b) h)
  ≔ transport Nat (NatDivides p) (nat_power (group_card G hG) b) (cardinality (McKaySet G b) h)
      (inverse Nat (cardinality (McKaySet G b) h) (nat_power (group_card G hG) b) (mckay_set_card G b hG h))
      (mckay_power_divisible p (group_card G hG) hd b hb)

{` Fixed points of the rotation are the constant tuples (g, …, g) with g^(b+1) = e. `}
def McKayFixedPoints (G : Group) (b : Nat) : Type
  ≔ Σ (McKaySet G b) (x ↦ Id (McKaySet G b) (mckay_rotate G b x) x)

def McKayPeriodElements (G : Group) (b : Nat) : Type
  ≔ Σ (USym G) (g ↦ Id (USym G) (usym_power G g (suc. b)) (usym_unit G))

def mckay_product_const (G : Group) (b : Nat) (g : USym G) (s : Remainder (suc. b)) (k : Nat)
  : Id (USym G) (mckay_product G b (_ ↦ g) s k) (usym_power G g k)
  ≔ match k [
  | zero. ↦ refl (usym_unit G)
  | suc. k ↦ refl (usym_mul G g) (mckay_product_const G b g (modular_successor b s) k) ]

def mckay_constant_of_rotation (G : Group) (b : Nat) (t : Remainder (suc. b) → USym G)
  (c : (r : Remainder (suc. b)) → Id (USym G) (t (modular_successor b r)) (t r)) (k : Nat) (s : Remainder (suc. b))
  : Id (USym G) (t (iterate (Remainder (suc. b)) (modular_successor b) k s)) (t s)
  ≔ match k [
  | zero. ↦ refl (t s)
  | suc. k ↦ concat (USym G) (t (modular_successor b (iterate (Remainder (suc. b)) (modular_successor b) k s)))
      (t (iterate (Remainder (suc. b)) (modular_successor b) k s)) (t s)
      (c (iterate (Remainder (suc. b)) (modular_successor b) k s)) (mckay_constant_of_rotation G b t c k s) ]

def mckay_constant_entries (G : Group) (b : Nat) (t : Remainder (suc. b) → USym G)
  (c : (r : Remainder (suc. b)) → Id (USym G) (t (modular_successor b r)) (t r)) (r : Remainder (suc. b))
  : Id (USym G) (t r) (t (mckay_zero b))
  ≔ let R ≔ Remainder (suc. b) in let w ≔ iterate R (modular_successor b) (r .fst) (mckay_zero b) in
    concat (USym G) (t r) (t w) (t (mckay_zero b))
      (refl t (inverse R w r (mckay_index_iterate b r))) (mckay_constant_of_rotation G b t c (r .fst) (mckay_zero b))

def mckay_fixed_power (G : Group) (b : Nat) (x : McKaySet G b)
  (c : (r : Remainder (suc. b)) → Id (USym G) (x .fst (modular_successor b r)) (x .fst r))
  : Id (USym G) (usym_power G (x .fst (mckay_zero b)) (suc. b)) (usym_unit G)
  ≔ let z ≔ mckay_zero b in let g ≔ x .fst z in
    let q : Id (USym G) (mckay_product G b (x .fst) z (suc. b)) (usym_power G g (suc. b))
      ≔ concat (USym G) (mckay_product G b (x .fst) z (suc. b)) (mckay_product G b (_ ↦ g) z (suc. b))
          (usym_power G g (suc. b))
          (mckay_product_congr G b (x .fst) (_ ↦ g) z (suc. b) (i _ ↦ mckay_constant_of_rotation G b (x .fst) c i z))
          (mckay_product_const G b g z (suc. b)) in
    concat (USym G) (usym_power G g (suc. b)) (mckay_product G b (x .fst) z (suc. b)) (usym_unit G)
      (inverse (USym G) (mckay_product G b (x .fst) z (suc. b)) (usym_power G g (suc. b)) q) (x .snd)

def mckay_rotation_entries (G : Group) (b : Nat) (x : McKaySet G b) (fx : Id (McKaySet G b) (mckay_rotate G b x) x)
  (r : Remainder (suc. b)) : Id (USym G) (x .fst (modular_successor b r)) (x .fst r)
  ≔ happly (Remainder (suc. b)) (_ ↦ USym G) (mckay_rotate G b x .fst) (x .fst)
      (refl ((y ↦ y .fst) : McKaySet G b → (Remainder (suc. b) → USym G)) fx) r

def mckay_fixed_to_period (G : Group) (b : Nat) (y : McKayFixedPoints G b) : McKayPeriodElements G b
  ≔ (y .fst .fst (mckay_zero b), mckay_fixed_power G b (y .fst) (mckay_rotation_entries G b (y .fst) (y .snd)))

def mckay_constant_tuple (G : Group) (b : Nat) (g : McKayPeriodElements G b) : McKaySet G b
  ≔ ((_ ↦ g .fst),
     concat (USym G) (mckay_product G b (_ ↦ g .fst) (mckay_zero b) (suc. b)) (usym_power G (g .fst) (suc. b)) (usym_unit G)
       (mckay_product_const G b (g .fst) (mckay_zero b) (suc. b)) (g .snd))

def mckay_period_to_fixed (G : Group) (b : Nat) (g : McKayPeriodElements G b) : McKayFixedPoints G b
  ≔ (mckay_constant_tuple G b g,
     subtype_equal (Remainder (suc. b) → USym G) (McKayCondition G b) (mckay_condition_prop G b)
       (mckay_rotate G b (mckay_constant_tuple G b g)) (mckay_constant_tuple G b g)
       (refl ((_ ↦ g .fst) : Remainder (suc. b) → USym G)))

def mckay_period_fixed_period (G : Group) (b : Nat) (g : McKayPeriodElements G b)
  : Id (McKayPeriodElements G b) (mckay_fixed_to_period G b (mckay_period_to_fixed G b g)) g
  ≔ subtype_equal (USym G) (g ↦ Id (USym G) (usym_power G g (suc. b)) (usym_unit G))
      (g ↦ usym_set G (usym_power G g (suc. b)) (usym_unit G))
      (mckay_fixed_to_period G b (mckay_period_to_fixed G b g)) g (refl (g .fst))

def mckay_fixed_period_fixed (G : Group) (b : Nat) (y : McKayFixedPoints G b)
  : Id (McKayFixedPoints G b) (mckay_period_to_fixed G b (mckay_fixed_to_period G b y)) y
  ≔ let M ≔ McKaySet G b in let R ≔ Remainder (suc. b) in let t ≔ y .fst .fst in
    let c ≔ mckay_rotation_entries G b (y .fst) (y .snd) in
    subtype_equal M (x ↦ Id M (mckay_rotate G b x) x) (x ↦ mckay_set_is_set G b (mckay_rotate G b x) x)
      (mckay_period_to_fixed G b (mckay_fixed_to_period G b y)) y
      (subtype_equal (R → USym G) (McKayCondition G b) (mckay_condition_prop G b)
        (mckay_constant_tuple G b (mckay_fixed_to_period G b y)) (y .fst)
        (funext R (_ ↦ USym G) (_ ↦ t (mckay_zero b)) t
          (r ↦ inverse (USym G) (t r) (t (mckay_zero b)) (mckay_constant_entries G b t c r))))

def mckay_fixed_points_equiv (G : Group) (b : Nat) : Equiv (McKayFixedPoints G b) (McKayPeriodElements G b)
  ≔ quasi_inverse_equiv (McKayFixedPoints G b) (McKayPeriodElements G b) (mckay_fixed_to_period G b)
      (mckay_period_to_fixed G b) (mckay_fixed_period_fixed G b) (mckay_period_fixed_period G b)

{` e is always a fixed point (the constant tuple (e, …, e)). `}
def mckay_period_unit (G : Group) (b : Nat) : McKayPeriodElements G b
  ≔ (usym_unit G, usym_power_unit G (suc. b))

{` Litmus checks: the product of a constant triple is g^3 by computation;
   the McKay set of C_3 with p = 3 has 3^2 = 9 elements. `}
def mckay_litmus_const_product (G : Group) (g : USym G)
  : Id (USym G) (mckay_product G (suc. (suc. zero.)) (_ ↦ g) (mckay_zero (suc. (suc. zero.))) (suc. (suc. (suc. zero.))))
      (usym_power G g (suc. (suc. (suc. zero.))))
  ≔ refl (usym_power G g (suc. (suc. (suc. zero.))))

def mckay_litmus_card
  : Id Nat (cardinality (McKaySet (cyclic_group (suc. (suc. (suc. zero.)))) (suc. (suc. zero.)))
      (mckay_set_finite (cyclic_group (suc. (suc. (suc. zero.)))) (suc. (suc. zero.)) (cyclic_group_finite (suc. (suc. zero.)))))
      (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))))
  ≔ let C ≔ cyclic_group (suc. (suc. (suc. zero.))) in let hC ≔ cyclic_group_finite (suc. (suc. zero.)) in
    concat Nat (cardinality (McKaySet C (suc. (suc. zero.))) (mckay_set_finite C (suc. (suc. zero.)) hC))
      (nat_power (group_card C hC) (suc. (suc. zero.))) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))))
      (mckay_set_card C (suc. (suc. zero.)) hC (mckay_set_finite C (suc. (suc. zero.)) hC))
      (refl ((n ↦ nat_power n (suc. (suc. zero.))) : Nat → Nat) (cyclic_group_card (suc. (suc. zero.)) hC))
