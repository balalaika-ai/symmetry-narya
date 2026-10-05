export "../../../src/1315-standard-vector-space"

{` Blind statements, chapter 14 (geometry.tex), section "Inner product spaces".

   The real numbers. Narya has no real numbers, so the book's RR is an
   explicit parameter K : BlindEuclideanField: a field (chapter 13, Field)
   with an ordering given by its cone of non-negative elements (closed
   under + and ·, containing squares, P ∩ -P = {0}, P ∪ -P = K merely),
   square roots of non-negative elements (the Euclidean property, needed for
   Gram–Schmidt normalization and for √5 in the icosahedron), and the
   classical field axiom x ≠ 0 → x invertible. The last axiom is explicit:
   the chapter assumes "standard linear algebra over the real numbers"
   (Gram–Schmidt divides by ⟨w, w⟩ for w ≠ 0), which is classical; it holds
   for the classical reals but not for the constructive Cauchy reals
   without Markov's principle. Every statement below is quantified over K. `}

def BlindEuclideanField : Type ≔ sig (
  field : Field,
  nonneg : field .fst .carrier → Type,
  nonneg_prop : (x : field .fst .carrier) → isProp (nonneg x),
  nonneg_add : (x y : field .fst .carrier) → nonneg x → nonneg y → nonneg (field .fst .add x y),
  nonneg_mul : (x y : field .fst .carrier) → nonneg x → nonneg y → nonneg (field .fst .mul x y),
  nonneg_square : (x : field .fst .carrier) → nonneg (field .fst .mul x x),
  nonneg_antisym : (x : field .fst .carrier) → nonneg x → nonneg (field .fst .neg x)
    → Id (field .fst .carrier) x (field .fst .zero),
  nonneg_total : (x : field .fst .carrier) → Mere (Sum (nonneg x) (nonneg (field .fst .neg x))),
  nonzero_invertible : (x : field .fst .carrier) → Not (Id (field .fst .carrier) x (field .fst .zero))
    → IsInvertible (field .fst) x,
  sqrt : (x : field .fst .carrier) → nonneg x
    → Σ (field .fst .carrier) (y ↦ Product (nonneg y) (Id (field .fst .carrier) (field .fst .mul y y) x)))

{` An inner product H on a K-vector space V: symmetric, linear in the first
   (hence, by symmetry, in each) argument, positive definite
   (H(x,x) ≥ 0, and H(x,x) = 0 only for x = 0). The book's
   H : V × V → RR is curried. `}
def BlindInnerProductLaws (K : BlindEuclideanField) (V : VectorSpace (K .field))
  (H : V .carrier → V .carrier → K .field .fst .carrier) : Type ≔ sig (
  symm : (x y : V .carrier) → Id (K .field .fst .carrier) (H x y) (H y x),
  add_left : (x y z : V .carrier)
    → Id (K .field .fst .carrier) (H (V .add x y) z) (K .field .fst .add (H x z) (H y z)),
  smul_left : (a : K .field .fst .carrier) (x y : V .carrier)
    → Id (K .field .fst .carrier) (H (V .smul a x) y) (K .field .fst .mul a (H x y)),
  pos : (x : V .carrier) → K .nonneg (H x x),
  definite : (x : V .carrier) → Id (K .field .fst .carrier) (H x x) (K .field .fst .zero) → Id (V .carrier) x (V .zero))

{` def:InnerProductSpace. An inner product space: a finite-dimensional real
   vector space with an inner product. OS (the book's type of pairs (V, H))
   is this record type. `}
def BlindInnerProductSpace (K : BlindEuclideanField) : Type ≔ sig (
  space : VectorSpace (K .field),
  finite_dim : IsFiniteDimensional (K .field) space,
  inner : space .carrier → space .carrier → K .field .fst .carrier,
  laws : BlindInnerProductLaws K space inner)

{` OS_n: inner product spaces of dimension n. `}
def BlindInnerProductSpaceDim (K : BlindEuclideanField) (n : Nat) : Type
  ≔ Σ (BlindInnerProductSpace K) (W ↦ HasDimension (K .field) n (W .space))

{` The dot product x · y = Σ_i x_i y_i on RR^n = (Fin n → K). `}
def blind_dot (K : BlindEuclideanField) (n : Nat) (x y : Fin n → K .field .fst .carrier) : K .field .fst .carrier
  ≔ fin_module_sum (K .field .fst) (ring_self_module (K .field .fst)) n (i ↦ K .field .fst .mul (x i) (y i))

{` Helper proofs that the dot product is an inner product (needed to
   construct the standard space V^n). `}
def blind_nonneg_zero (K : BlindEuclideanField) : K .nonneg (K .field .fst .zero)
  ≔ let R ≔ K .field .fst in
    transport (R .carrier) (K .nonneg) (R .mul (R .zero) (R .zero)) (R .zero) (ring_mul_zero_left R (R .zero))
      (K .nonneg_square (R .zero))

def blind_sum_nonneg (K : BlindEuclideanField) (n : Nat) (f : Fin n → K .field .fst .carrier)
  (h : (i : Fin n) → K .nonneg (f i))
  : K .nonneg (fin_module_sum (K .field .fst) (ring_self_module (K .field .fst)) n f)
  ≔ match n [
  | zero. ↦ blind_nonneg_zero K
  | suc. n ↦ K .nonneg_add
      (fin_module_sum (K .field .fst) (ring_self_module (K .field .fst)) n (i ↦ f (inl. i))) (f (inr. star.))
      (blind_sum_nonneg K n (i ↦ f (inl. i)) (i ↦ h (inl. i))) (h (inr. star.)) ]

def blind_nonneg_sum_zero_neg (K : BlindEuclideanField) (a b : K .field .fst .carrier)
  (p : Id (K .field .fst .carrier) (K .field .fst .add a b) (K .field .fst .zero))
  : Id (K .field .fst .carrier) b (K .field .fst .neg a)
  ≔ ag_inv_unique_right (ring_additive_group (K .field .fst)) a b p

def blind_nonneg_sum_zero_left (K : BlindEuclideanField) (a b : K .field .fst .carrier)
  (ha : K .nonneg a) (hb : K .nonneg b)
  (p : Id (K .field .fst .carrier) (K .field .fst .add a b) (K .field .fst .zero))
  : Id (K .field .fst .carrier) a (K .field .fst .zero)
  ≔ let R ≔ K .field .fst in
    K .nonneg_antisym a ha
      (transport (R .carrier) (K .nonneg) b (R .neg a) (blind_nonneg_sum_zero_neg K a b p) hb)

def blind_nonneg_sum_zero_right (K : BlindEuclideanField) (a b : K .field .fst .carrier)
  (ha : K .nonneg a) (hb : K .nonneg b)
  (p : Id (K .field .fst .carrier) (K .field .fst .add a b) (K .field .fst .zero))
  : Id (K .field .fst .carrier) b (K .field .fst .zero)
  ≔ let R ≔ K .field .fst in
    calc
      b = R .neg a by blind_nonneg_sum_zero_neg K a b p
      = R .neg (R .zero) by refl (R .neg) (blind_nonneg_sum_zero_left K a b ha hb p)
      = R .zero by ag_inv_unit (ring_additive_group R) ∎

def blind_sum_nonneg_zero (K : BlindEuclideanField) (n : Nat) (f : Fin n → K .field .fst .carrier)
  (h : (i : Fin n) → K .nonneg (f i))
  (p : Id (K .field .fst .carrier) (fin_module_sum (K .field .fst) (ring_self_module (K .field .fst)) n f)
         (K .field .fst .zero))
  (i : Fin n) : Id (K .field .fst .carrier) (f i) (K .field .fst .zero)
  ≔ match n [
  | zero. ↦ match i [ ]
  | suc. n ↦
    let s ≔ fin_module_sum (K .field .fst) (ring_self_module (K .field .fst)) n (j ↦ f (inl. j)) in
    let hs ≔ blind_sum_nonneg K n (j ↦ f (inl. j)) (j ↦ h (inl. j)) in
    match i [
    | inl. i ↦ blind_sum_nonneg_zero K n (j ↦ f (inl. j)) (j ↦ h (inl. j))
        (blind_nonneg_sum_zero_left K s (f (inr. star.)) hs (h (inr. star.)) p) i
    | inr. star. ↦ blind_nonneg_sum_zero_right K s (f (inr. star.)) hs (h (inr. star.)) p ] ]

def blind_square_zero (K : BlindEuclideanField) (x : K .field .fst .carrier)
  (p : Id (K .field .fst .carrier) (K .field .fst .mul x x) (K .field .fst .zero))
  : Id (K .field .fst .carrier) x (K .field .fst .zero)
  ≔ let R ≔ K .field .fst in
    let S ≔ R .carrier in
    field_non_invertible_zero R (K .field .snd) x
      (t ↦ mere_rec (InverseWitness R x) Empty empty_prop
        (w ↦
          let a ≔ w .fst in
          let x0 : Id S x (R .zero)
            ≔ calc
                x = R .mul x (R .one) by inverse S (R .mul x (R .one)) x (ring_mul_one_right R x)
                = R .mul x (R .mul x a) by refl (R .mul x) (inverse S (R .mul x a) (R .one) (w .snd .fst))
                = R .mul (R .mul x x) a by ring_mul_assoc R x x a
                = R .mul (R .zero) a by refl ((u ↦ R .mul u a) : S → S) p
                = R .zero by ring_mul_zero_left R a ∎ in
          K .field .snd .fst .snd
            (calc
               R .zero = R .mul (R .zero) a by inverse S (R .mul (R .zero) a) (R .zero) (ring_mul_zero_left R a)
               = R .mul x a by refl ((u ↦ R .mul u a) : S → S) (inverse S x (R .zero) x0)
               = R .one by w .snd .fst ∎))
        t)

def blind_dot_laws (K : BlindEuclideanField) (n : Nat)
  : BlindInnerProductLaws K (standard_vector_space (K .field) n) (blind_dot K n)
  ≔ let R ≔ K .field .fst in
    let S ≔ R .carrier in
    let M ≔ ring_self_module R in
    let sum ≔ fin_module_sum R M n in
    (symm ≔ x y ↦
       refl sum (funext (Fin n) (_ ↦ S) (i ↦ R .mul (x i) (y i)) (i ↦ R .mul (y i) (x i))
         (i ↦ K .field .snd .fst .fst (x i) (y i))),
     add_left ≔ x y z ↦ calc
       sum (i ↦ R .mul (R .add (x i) (y i)) (z i))
       = sum (i ↦ R .add (R .mul (x i) (z i)) (R .mul (y i) (z i)))
         by refl sum (funext (Fin n) (_ ↦ S) (i ↦ R .mul (R .add (x i) (y i)) (z i))
           (i ↦ R .add (R .mul (x i) (z i)) (R .mul (y i) (z i))) (i ↦ ring_rdistr R (x i) (y i) (z i)))
       = R .add (sum (i ↦ R .mul (x i) (z i))) (sum (i ↦ R .mul (y i) (z i)))
         by fin_module_sum_add R M n (i ↦ R .mul (x i) (z i)) (i ↦ R .mul (y i) (z i)) ∎,
     smul_left ≔ a x y ↦ calc
       sum (i ↦ R .mul (R .mul a (x i)) (y i))
       = sum (i ↦ R .mul a (R .mul (x i) (y i)))
         by refl sum (funext (Fin n) (_ ↦ S) (i ↦ R .mul (R .mul a (x i)) (y i)) (i ↦ R .mul a (R .mul (x i) (y i)))
           (i ↦ inverse S (R .mul a (R .mul (x i) (y i))) (R .mul (R .mul a (x i)) (y i)) (ring_mul_assoc R a (x i) (y i))))
       = R .mul a (sum (i ↦ R .mul (x i) (y i)))
         by fin_module_sum_smul R M n a (i ↦ R .mul (x i) (y i)) ∎,
     pos ≔ x ↦ blind_sum_nonneg K n (i ↦ R .mul (x i) (x i)) (i ↦ K .nonneg_square (x i)),
     definite ≔ x p ↦
       funext (Fin n) (_ ↦ S) x (_ ↦ R .zero)
         (i ↦ blind_square_zero K (x i)
           (blind_sum_nonneg_zero K n (j ↦ R .mul (x j) (x j)) (j ↦ K .nonneg_square (x j)) p i)))

def blind_std_basis_free (K : BlindEuclideanField) (n : Nat) : HasDimension (K .field) n (standard_vector_space (K .field) n)
  ≔ mere (Σ (Fin n → Fin n → K .field .fst .carrier)
           (i ↦ IsFreeVectorSpace (K .field) (standard_set n) (standard_vector_space (K .field) n) i))
      (standard_basis (K .field .fst) n, standard_vector_space_free (K .field) n)

{` The standard inner product space V^n = (RR^n, dot product). `}
def blind_std_inner_product_space (K : BlindEuclideanField) (n : Nat) : BlindInnerProductSpace K
  ≔ (space ≔ standard_vector_space (K .field) n,
     finite_dim ≔ mere (Σ Nat (m ↦ HasDimension (K .field) m (standard_vector_space (K .field) n)))
       (n, blind_std_basis_free K n),
     inner ≔ blind_dot K n,
     laws ≔ blind_dot_laws K n)

def blind_std_inner_product_space_dim (K : BlindEuclideanField) (n : Nat) : BlindInnerProductSpaceDim K n
  ≔ (blind_std_inner_product_space K n, blind_std_basis_free K n)

{` thm:GramSchmidt. Any inner product space V is merely equal to V^n,
   n = dim V. "n = dim V" is read as: for every n such that V has
   dimension n (dimension is unique, so this is the same). `}
def blind_gram_schmidt (K : BlindEuclideanField) : Type
  ≔ (V : BlindInnerProductSpace K) (n : Nat) → HasDimension (K .field) n (V .space)
    → Mere (Id (BlindInnerProductSpace K) V (blind_std_inner_product_space K n))

{` lem:InnerProductSpace1Type. OS is a 1-type. `}
def blind_inner_product_space_one_type (K : BlindEuclideanField) : Type ≔ isGroupoid (BlindInnerProductSpace K)

{` def:OrthogonalGroup, the facts it relies on: for each n, OS_n is a
   connected groupoid (consequences of thm:GramSchmidt and
   lem:InnerProductSpace1Type). `}
def blind_orthogonal_group_data (K : BlindEuclideanField) : Type
  ≔ (n : Nat) → Product (Connected (BlindInnerProductSpaceDim K n)) (isGroupoid (BlindInnerProductSpaceDim K n))

{` def:OrthogonalGroup. O(n) ≔ mkgroup OS_n, pointed at V^n. The proofs of
   connectedness and of the groupoid property (propositions) are taken as
   arguments; the book obtains them from thm:GramSchmidt and
   lem:InnerProductSpace1Type (see blind_orthogonal_group_data). `}
def BlindOrthogonalGroup (K : BlindEuclideanField) (n : Nat)
  (conn : Connected (BlindInnerProductSpaceDim K n)) (grpd : isGroupoid (BlindInnerProductSpaceDim K n)) : Group
  ≔ mkgroup (BlindInnerProductSpaceDim K n, blind_std_inner_product_space_dim K n, conn, grpd)
