export "1493-plane-loops"

{` Chapter 14, geometry.tex 80: "an isosceles non-equilateral triangle has
   a total of 2 symmetries: the identity and the reflection through the
   midline". The triangle T in 𝔼² has vertices C = (0,0) (apex),
   A = (1,0), B = (0,1): |CA|² = |CB|² = 1 and |AB|² = 2 ≠ 1. It is the
   geometric object (𝔼², P ↦ P ∈ {C, A, B}) with materials Prop
   (triangle_object; its vertex set, which has the same symmetries as the
   solid triangle). The midline of T is the line y = x; the reflection
   through it is the coordinate swap.

   Theorem (isosceles_triangle_symmetries): USym Sym(T) ≃ Bool, true for
   the identity and false for the reflection (they are different).

   Proof. A symmetry is a loop ℓ of 𝔼² in ES with g(τ P) = g(P) for the
   transport τ of points. τ is affine with isometric linear part
   (module 1493), maps T onto T and is injective; comparing norms
   (1 ≠ 2) shows τ(C) = C. So ℓ is also a loop of (𝔼², {0}), hence comes
   from a linear isometry φ of K²; φ permutes A, B and is determined by
   φ(A), φ(B). `}

def plane_vec (K : EuclideanField) (a b : ef_carrier K) : Fin 2 → ef_carrier K ≔ [ inl. _ ↦ a | inr. _ ↦ b ]

def triangle_apex (K : EuclideanField) : Fin 2 → ef_carrier K ≔ plane_origin K

def triangle_vertex_a (K : EuclideanField) : Fin 2 → ef_carrier K ≔ plane_vec K (K .field .fst .one) (K .field .fst .zero)

def triangle_vertex_b (K : EuclideanField) : Fin 2 → ef_carrier K ≔ plane_vec K (K .field .fst .zero) (K .field .fst .one)

def TriangleVertex (K : EuclideanField) (P : Fin 2 → ef_carrier K) : Type
  ≔ Sum (Id (Fin 2 → ef_carrier K) P (triangle_apex K))
      (Sum (Id (Fin 2 → ef_carrier K) P (triangle_vertex_a K)) (Id (Fin 2 → ef_carrier K) P (triangle_vertex_b K)))

def triangle_pred (K : EuclideanField) (P : Fin 2 → ef_carrier K) : PropTypes
  ≔ (Mere (TriangleVertex K P), mere_isprop (TriangleVertex K P))

def triangle_object (K : EuclideanField) : EuclideanObject K propositions_settype ≔ (standard_plane K, triangle_pred K)

def TriangleLoop (K : EuclideanField) : Type
  ≔ Id (EuclideanObject K propositions_settype) (triangle_object K) (triangle_object K)

def triangle_loops_set (K : EuclideanField) : isSet (TriangleLoop K)
  ≔ euclidean_object_groupoid K propositions_settype (triangle_object K) (triangle_object K)

{` Small computations. `}
def plane_set (K : EuclideanField) : isSet (Fin 2 → ef_carrier K) ≔ module_set (K .field .fst) (standard_vector_space (K .field) 2)

def ef_one_ne_zero (K : EuclideanField) (e : Id (ef_carrier K) (K .field .fst .one) (K .field .fst .zero)) : Empty
  ≔ ef_non_trivial K (inverse (ef_carrier K) (K .field .fst .one) (K .field .fst .zero) e)

def ef_two_ne_one (K : EuclideanField)
  (e : Id (ef_carrier K) (K .field .fst .one) (K .field .fst .add (K .field .fst .one) (K .field .fst .one))) : Empty
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in
    ef_non_trivial K
      (ag_cancel_left (ring_additive_group R) (R .one) (R .zero) (R .one)
        (concat S (R .add (R .one) (R .zero)) (R .one) (R .add (R .one) (R .one)) (R .add_laws .unit_right (R .one)) e))

def triangle_first (K : EuclideanField) (P Q : Fin 2 → ef_carrier K) (e : Id (Fin 2 → ef_carrier K) P Q)
  : Id (ef_carrier K) (P fin_two_first) (Q fin_two_first)
  ≔ refl ((f ↦ f fin_two_first) : (Fin 2 → ef_carrier K) → ef_carrier K) e

def triangle_second (K : EuclideanField) (P Q : Fin 2 → ef_carrier K) (e : Id (Fin 2 → ef_carrier K) P Q)
  : Id (ef_carrier K) (P fin_two_second) (Q fin_two_second)
  ≔ refl ((f ↦ f fin_two_second) : (Fin 2 → ef_carrier K) → ef_carrier K) e

def triangle_a_ne_c (K : EuclideanField) (e : Id (Fin 2 → ef_carrier K) (triangle_vertex_a K) (triangle_apex K)) : Empty
  ≔ ef_one_ne_zero K (triangle_first K (triangle_vertex_a K) (triangle_apex K) e)

def triangle_b_ne_c (K : EuclideanField) (e : Id (Fin 2 → ef_carrier K) (triangle_vertex_b K) (triangle_apex K)) : Empty
  ≔ ef_one_ne_zero K (triangle_second K (triangle_vertex_b K) (triangle_apex K) e)

def triangle_a_ne_b (K : EuclideanField) (e : Id (Fin 2 → ef_carrier K) (triangle_vertex_a K) (triangle_vertex_b K)) : Empty
  ≔ ef_one_ne_zero K (triangle_first K (triangle_vertex_a K) (triangle_vertex_b K) e)

def ring_neg_one_square (R : AbstractRing) : Id (R .carrier) (R .mul (R .add (R .zero) (R .neg (R .one))) (R .add (R .zero) (R .neg (R .one)))) (R .one)
  ≔ let S ≔ R .carrier in let o ≔ R .one in let ng ≔ R .neg in let m ≔ R .mul in
    calc
      m (R .add (R .zero) (ng o)) (R .add (R .zero) (ng o)) = m (ng o) (ng o)
        by refl m (R .add_laws .unit_left (ng o)) (R .add_laws .unit_left (ng o))
      = m o o by inverse S (m o o) (m (ng o) (ng o)) (ring_neg_neg_mul R o o)
      = o by ring_mul_one_left R o ∎

def ring_one_minus_zero_square (R : AbstractRing) : Id (R .carrier) (R .mul (R .add (R .one) (R .neg (R .zero))) (R .add (R .one) (R .neg (R .zero)))) (R .one)
  ≔ let S ≔ R .carrier in let o ≔ R .one in
    let e : Id S (R .add o (R .neg (R .zero))) o
      ≔ concat S (R .add o (R .neg (R .zero))) (R .add o (R .zero)) o
          (refl (R .add o) (ag_inv_unit (ring_additive_group R))) (R .add_laws .unit_right o) in
    concat S (R .mul (R .add o (R .neg (R .zero))) (R .add o (R .neg (R .zero)))) (R .mul o o) o
      (refl (R .mul) e e) (ring_mul_one_left R o)

{` |A|² = |B|² = 1 and |B - A|² = |A - B|² = 2. `}
def triangle_a_norm (K : EuclideanField)
  : Id (ef_carrier K) (dot_product K 2 (triangle_vertex_a K) (triangle_vertex_a K)) (K .field .fst .one)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let z ≔ R .zero in let o ≔ R .one in
    calc
      R .add (R .add z (R .mul o o)) (R .mul z z) = R .add (R .add z o) z by refl (R .add) (refl (R .add z) (ring_mul_one_left R o)) (ring_mul_zero_left R z)
      = R .add o z by refl ((y ↦ R .add y z) : S → S) (R .add_laws .unit_left o)
      = o by R .add_laws .unit_right o ∎

def triangle_b_norm (K : EuclideanField)
  : Id (ef_carrier K) (dot_product K 2 (triangle_vertex_b K) (triangle_vertex_b K)) (K .field .fst .one)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let z ≔ R .zero in let o ≔ R .one in
    calc
      R .add (R .add z (R .mul z z)) (R .mul o o) = R .add (R .add z z) o by refl (R .add) (refl (R .add z) (ring_mul_zero_left R z)) (ring_mul_one_left R o)
      = R .add z o by refl ((y ↦ R .add y o) : S → S) (R .add_laws .unit_left z)
      = o by R .add_laws .unit_left o ∎

def triangle_ba_norm (K : EuclideanField)
  : Id (ef_carrier K)
      (dot_product K 2 (i ↦ K .field .fst .add (triangle_vertex_b K i) (K .field .fst .neg (triangle_vertex_a K i)))
                       (i ↦ K .field .fst .add (triangle_vertex_b K i) (K .field .fst .neg (triangle_vertex_a K i))))
      (K .field .fst .add (K .field .fst .one) (K .field .fst .one))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let z ≔ R .zero in let o ≔ R .one in
    calc
      R .add (R .add z (R .mul (R .add z (R .neg o)) (R .add z (R .neg o)))) (R .mul (R .add o (R .neg z)) (R .add o (R .neg z)))
      = R .add (R .add z o) o by refl (R .add) (refl (R .add z) (ring_neg_one_square R)) (ring_one_minus_zero_square R)
      = R .add o o by refl ((y ↦ R .add y o) : S → S) (R .add_laws .unit_left o) ∎

def triangle_ab_norm (K : EuclideanField)
  : Id (ef_carrier K)
      (dot_product K 2 (i ↦ K .field .fst .add (triangle_vertex_a K i) (K .field .fst .neg (triangle_vertex_b K i)))
                       (i ↦ K .field .fst .add (triangle_vertex_a K i) (K .field .fst .neg (triangle_vertex_b K i))))
      (K .field .fst .add (K .field .fst .one) (K .field .fst .one))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let z ≔ R .zero in let o ≔ R .one in
    calc
      R .add (R .add z (R .mul (R .add o (R .neg z)) (R .add o (R .neg z)))) (R .mul (R .add z (R .neg o)) (R .add z (R .neg o)))
      = R .add (R .add z o) o by refl (R .add) (refl (R .add z) (ring_one_minus_zero_square R)) (ring_neg_one_square R)
      = R .add o o by refl ((y ↦ R .add y o) : S → S) (R .add_laws .unit_left o) ∎

{` Litmus: the triangle is isosceles (|CA| = |CB|) and not equilateral. `}
def triangle_isosceles_not_equilateral (K : EuclideanField)
  : Product (Id (ef_carrier K) (dot_product K 2 (triangle_vertex_a K) (triangle_vertex_a K))
                (dot_product K 2 (triangle_vertex_b K) (triangle_vertex_b K)))
      (Id (ef_carrier K) (dot_product K 2 (triangle_vertex_a K) (triangle_vertex_a K))
         (dot_product K 2 (i ↦ K .field .fst .add (triangle_vertex_a K i) (K .field .fst .neg (triangle_vertex_b K i)))
                          (i ↦ K .field .fst .add (triangle_vertex_a K i) (K .field .fst .neg (triangle_vertex_b K i)))) → Empty)
  ≔ let S ≔ ef_carrier K in
    (concat S (dot_product K 2 (triangle_vertex_a K) (triangle_vertex_a K)) (K .field .fst .one)
       (dot_product K 2 (triangle_vertex_b K) (triangle_vertex_b K))
       (triangle_a_norm K) (inverse S (dot_product K 2 (triangle_vertex_b K) (triangle_vertex_b K)) (K .field .fst .one) (triangle_b_norm K)),
     e ↦ ef_two_ne_one K
       (concat S (K .field .fst .one) (dot_product K 2 (triangle_vertex_a K) (triangle_vertex_a K))
          (K .field .fst .add (K .field .fst .one) (K .field .fst .one))
          (inverse S (dot_product K 2 (triangle_vertex_a K) (triangle_vertex_a K)) (K .field .fst .one) (triangle_a_norm K))
          (concat S (dot_product K 2 (triangle_vertex_a K) (triangle_vertex_a K))
             (dot_product K 2 (i ↦ K .field .fst .add (triangle_vertex_a K i) (K .field .fst .neg (triangle_vertex_b K i)))
                              (i ↦ K .field .fst .add (triangle_vertex_a K i) (K .field .fst .neg (triangle_vertex_b K i))))
             (K .field .fst .add (K .field .fst .one) (K .field .fst .one))
             e (triangle_ab_norm K))))

