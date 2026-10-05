export "1315-standard-vector-space"
export "1304-general-linear-group"

{` Chapter 14 (geometry.tex 8-13): "we assume some standard linear algebra
   over real numbers". Narya has no real numbers, so the field ℝ of the
   chapter is an explicit parameter: a EuclideanField is a field (in the
   sense of chapter 13, module 1301) with a predicate "a ≥ 0" and exactly
   the order-theoretic facts about ℝ that chapter 14 uses:
   - a ≥ 0 is a proposition, closed under +, ·, and every square is ≥ 0;
   - antisymmetry: a ≥ 0 and -a ≥ 0 imply a = 0;
   - square roots: every a ≥ 0 has a chosen square root √a ≥ 0;
   - a ≠ 0 implies that a is invertible.
   All of these hold for ℝ classically (the last one constructively needs
   Markov's principle for the Cauchy reals); they are hypotheses, never
   assumed silently. Also basic consequences used throughout the chapter:
   inverses are unique (InverseWitness is a proposition), x·x = 0 implies
   x = 0, a sum of two non-negative elements is 0 only if both are, a
   finite sum of squares is ≥ 0 and is 0 only if all terms are 0. `}

def EuclideanField : Type ≔ sig (
  field : Field,
  nonneg : field .fst .carrier → Type,
  nonneg_prop : (a : field .fst .carrier) → isProp (nonneg a),
  nonneg_add : (a b : field .fst .carrier) → nonneg a → nonneg b → nonneg (field .fst .add a b),
  nonneg_mul : (a b : field .fst .carrier) → nonneg a → nonneg b → nonneg (field .fst .mul a b),
  nonneg_square : (a : field .fst .carrier) → nonneg (field .fst .mul a a),
  nonneg_antisym : (a : field .fst .carrier) → nonneg a → nonneg (field .fst .neg a)
    → Id (field .fst .carrier) a (field .fst .zero),
  nonzero_invertible : (a : field .fst .carrier) → Not (Id (field .fst .carrier) a (field .fst .zero))
    → IsInvertible (field .fst) a,
  sqrt : (a : field .fst .carrier) → nonneg a → field .fst .carrier,
  sqrt_nonneg : (a : field .fst .carrier) (h : nonneg a) → nonneg (sqrt a h),
  sqrt_square : (a : field .fst .carrier) (h : nonneg a) → Id (field .fst .carrier) (field .fst .mul (sqrt a h) (sqrt a h)) a)

def ef_ring (K : EuclideanField) : AbstractRing ≔ K .field .fst

def ef_carrier (K : EuclideanField) : Type ≔ K .field .fst .carrier

def ef_commutative (K : EuclideanField) : IsCommutativeRing (K .field .fst) ≔ K .field .snd .fst .fst

def ef_non_trivial (K : EuclideanField) : IsNonTrivialRing (K .field .fst) ≔ K .field .snd .fst .snd

{` Inverses in a commutative ring are unique, so InverseWitness is a
   proposition and an invertible element has an inverse. `}
def inverse_witness_prop (R : AbstractRing) (e : R .carrier) : isProp (InverseWitness R e)
  ≔ u v ↦
    let S ≔ R .carrier in
    let a ≔ u .fst in let b ≔ v .fst in
    let p : Id S a b
      ≔ calc
          a = R .mul a (R .one) by inverse S (R .mul a (R .one)) a (ring_mul_one_right R a)
          = R .mul a (R .mul e b) by refl (R .mul a) (inverse S (R .mul e b) (R .one) (v .snd .fst))
          = R .mul (R .mul a e) b by ring_mul_assoc R a e b
          = R .mul (R .one) b by refl ((x ↦ R .mul x b) : S → S) (u .snd .snd)
          = b by ring_mul_one_left R b ∎ in
    subtype_equal S (x ↦ Product (Id S (R .mul e x) (R .one)) (Id S (R .mul x e) (R .one)))
      (x ↦ product_prop (Id S (R .mul e x) (R .one)) (Id S (R .mul x e) (R .one))
        (ring_set R (R .mul e x) (R .one)) (ring_set R (R .mul x e) (R .one)))
      u v p

def invertible_witness (R : AbstractRing) (e : R .carrier) (h : IsInvertible R e) : InverseWitness R e
  ≔ mere_rec (InverseWitness R e) (InverseWitness R e) (inverse_witness_prop R e) (w ↦ w) h

{` The inverse of a non-zero element of a Euclidean field. `}
def ef_inv (K : EuclideanField) (a : ef_carrier K) (nz : Not (Id (ef_carrier K) a (K .field .fst .zero)))
  : InverseWitness (K .field .fst) a
  ≔ invertible_witness (K .field .fst) a (K .nonzero_invertible a nz)

def ef_transport_nonneg (K : EuclideanField) (a b : ef_carrier K) (p : Id (ef_carrier K) a b) (h : K .nonneg a)
  : K .nonneg b
  ≔ transport (ef_carrier K) (K .nonneg) a b p h

def ef_zero_nonneg (K : EuclideanField) : K .nonneg (K .field .fst .zero)
  ≔ let R ≔ K .field .fst in
    ef_transport_nonneg K (R .mul (R .zero) (R .zero)) (R .zero) (ring_mul_zero_left R (R .zero))
      (K .nonneg_square (R .zero))

def ef_one_nonneg (K : EuclideanField) : K .nonneg (K .field .fst .one)
  ≔ let R ≔ K .field .fst in
    ef_transport_nonneg K (R .mul (R .one) (R .one)) (R .one) (ring_mul_one_left R (R .one))
      (K .nonneg_square (R .one))

{` x·x = 0 implies x = 0: an invertible x would give x = x·(x·y) =
   (x·x)·y = 0 and then 1 = x·y = 0; a non-invertible element of a field is
   0 (module 1301). `}
def ef_square_zero (K : EuclideanField) (x : ef_carrier K)
  (p : Id (ef_carrier K) (K .field .fst .mul x x) (K .field .fst .zero))
  : Id (ef_carrier K) x (K .field .fst .zero)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in
    field_non_invertible_zero R (K .field .snd) x
      (hinv ↦
        let w ≔ invertible_witness R x hinv in
        let y ≔ w .fst in
        let x0 : Id S x (R .zero)
          ≔ calc
              x = R .mul x (R .one) by inverse S (R .mul x (R .one)) x (ring_mul_one_right R x)
              = R .mul x (R .mul x y) by refl (R .mul x) (inverse S (R .mul x y) (R .one) (w .snd .fst))
              = R .mul (R .mul x x) y by ring_mul_assoc R x x y
              = R .mul (R .zero) y by refl ((t ↦ R .mul t y) : S → S) p
              = R .zero by ring_mul_zero_left R y ∎ in
        ef_non_trivial K
          (calc
             R .zero = R .mul (R .zero) y by inverse S (R .mul (R .zero) y) (R .zero) (ring_mul_zero_left R y)
             = R .mul x y by refl ((t ↦ R .mul t y) : S → S) (inverse S x (R .zero) x0)
             = R .one by w .snd .fst ∎))

{` a ≥ 0, b ≥ 0 and a + b = 0 imply a = 0 (then b = -a ≥ 0). `}
def ef_sum_zero_left (K : EuclideanField) (a b : ef_carrier K) (ha : K .nonneg a) (hb : K .nonneg b)
  (p : Id (ef_carrier K) (K .field .fst .add a b) (K .field .fst .zero))
  : Id (ef_carrier K) a (K .field .fst .zero)
  ≔ let R ≔ K .field .fst in
    K .nonneg_antisym a ha
      (ef_transport_nonneg K b (R .neg a) (ag_inv_unique_right (ring_additive_group R) a b p) hb)

def ef_sum_zero_right (K : EuclideanField) (a b : ef_carrier K) (ha : K .nonneg a) (hb : K .nonneg b)
  (p : Id (ef_carrier K) (K .field .fst .add a b) (K .field .fst .zero))
  : Id (ef_carrier K) b (K .field .fst .zero)
  ≔ let R ≔ K .field .fst in
    ef_sum_zero_left K b a hb ha
      (concat (R .carrier) (R .add b a) (R .add a b) (R .zero) (ring_add_comm R b a) p)

{` Finite sums of squares Σ_i x_i·x_i (sums in K as in module 1315). `}
def ef_sum_squares (K : EuclideanField) (n : Nat) (x : Fin n → ef_carrier K) : ef_carrier K
  ≔ fin_module_sum (K .field .fst) (ring_self_module (K .field .fst)) n (i ↦ K .field .fst .mul (x i) (x i))

def ef_sum_squares_nonneg (K : EuclideanField) (n : Nat) (x : Fin n → ef_carrier K)
  : K .nonneg (ef_sum_squares K n x)
  ≔ match n [
  | zero. ↦ ef_zero_nonneg K
  | suc. n ↦ K .nonneg_add (ef_sum_squares K n (i ↦ x (inl. i))) (K .field .fst .mul (x (inr. star.)) (x (inr. star.)))
      (ef_sum_squares_nonneg K n (i ↦ x (inl. i))) (K .nonneg_square (x (inr. star.))) ]

def ef_sum_squares_zero (K : EuclideanField) (n : Nat) (x : Fin n → ef_carrier K)
  (p : Id (ef_carrier K) (ef_sum_squares K n x) (K .field .fst .zero)) (i : Fin n)
  : Id (ef_carrier K) (x i) (K .field .fst .zero)
  ≔ match n [
  | zero. ↦ match i [ ]
  | suc. n ↦
    let R ≔ K .field .fst in
    let s ≔ ef_sum_squares K n (j ↦ x (inl. j)) in
    let l ≔ x (inr. star.) in
    let hs ≔ ef_sum_squares_nonneg K n (j ↦ x (inl. j)) in
    let hl ≔ K .nonneg_square l in
    match i [
    | inl. i ↦ ef_sum_squares_zero K n (j ↦ x (inl. j)) (ef_sum_zero_left K s (R .mul l l) hs hl p) i
    | inr. star. ↦ ef_square_zero K l (ef_sum_zero_right K s (R .mul l l) hs hl p) ] ]
