export "1441-golden-ratio"
export "1440-icosahedron-vertices"
export "1435-configurations"
export "1436-point-symmetries"

{` Chapter 14, section "The icosahedron" (geometry.tex 292-308).

   Definition: the icosahedron (side length 2) in 𝔼³ with vertices at the
   cyclic permutations of (0, ±1, ±φ). The vertex family is icosa_vertex
   (module 1440) at S = K and φ = golden_ratio K; "the regular solid with
   these vertices" is read as their convex hull (the set of convex
   combinations), a geometric object with materials Prop; the vertex set is
   also given as an object.

   Remark: (0, ±1, ±φ) form a golden rectangle with short side 2 (sides 2
   and 2φ, orthogonal, A - B = D - C, and 2 ≤ 2φ since φ - 1 = φ⁻¹ ≥ 0), and
   ‖(0,1,φ) - (1,φ,0)‖ = √(1 + (φ-1)² + φ²) = √4 = 2. The book's claim that
   this computation suffices for regularity is not formalized as such; the
   edge graph (30 edges of length 2, every vertex of degree 5) is checked by
   computation over ℤ[φ] in module 1440. `}

def icosahedron_vertex (K : EuclideanField) (i : IcosaIndex) : Fin 3 → ef_carrier K
  ≔ icosa_vertex (ef_carrier K) (K .field .fst .zero) (K .field .fst .one) (K .field .fst .neg) (golden_ratio K) i

def standard_space_three (K : EuclideanField) : EuclideanSpace K ≔ euclidean_space_dim_forget K 3 (euclidean_standard K 3)

{` Finite sums over the 12 vertex indices in a module. `}
def icosa_index_sum (R : AbstractRing) (W : RingModule R) (f : IcosaIndex → W .carrier) : W .carrier
  ≔ let g ≔ (k : Fin 3) ↦ W .add (W .add (f (k, (true., true.))) (f (k, (true., false.))))
                                 (W .add (f (k, (false., true.))) (f (k, (false., false.)))) in
    W .add (W .add (g (inl. (inl. (inr. star.)))) (g (inl. (inr. star.)))) (g (inr. star.))

def icosahedron_vertex_set (K : EuclideanField) : EuclideanObject K propositions_settype
  ≔ let Pt ≔ Fin 3 → ef_carrier K in
    (standard_space_three K,
     P ↦ (Mere (Σ IcosaIndex (i ↦ Id Pt (icosahedron_vertex K i) P)), mere_isprop (Σ IcosaIndex (i ↦ Id Pt (icosahedron_vertex K i) P))))

{` The solid: P is a convex combination Σ λ_i v_i (λ_i ≥ 0, Σ λ_i = 1). `}
def IcosahedronConvexCombination (K : EuclideanField) (P : Fin 3 → ef_carrier K) : Type
  ≔ let R ≔ K .field .fst in
    Σ (IcosaIndex → ef_carrier K) (λ ↦
      Product ((i : IcosaIndex) → K .nonneg (λ i))
        (Product (Id (ef_carrier K) (icosa_index_sum R (ring_self_module R) λ) (R .one))
          (Id (Fin 3 → ef_carrier K)
            (icosa_index_sum R (standard_module R 3) (i ↦ standard_module R 3 .smul (λ i) (icosahedron_vertex K i))) P)))

def icosahedron (K : EuclideanField) : EuclideanObject K propositions_settype
  ≔ (standard_space_three K,
     P ↦ (Mere (IcosahedronConvexCombination K P), mere_isprop (IcosahedronConvexCombination K P)))

{` Norms and distances in 𝔼³. `}
def ip_norm (K : EuclideanField) (V : InnerProductSpace K) (v : ip_carrier K V) : ef_carrier K
  ≔ K .sqrt (V .form v v) (V .inner .nonneg v)

def standard_three_difference (K : EuclideanField) (P Q : Fin 3 → ef_carrier K) : Fin 3 → ef_carrier K
  ≔ standard_module (K .field .fst) 3 .add P (standard_module (K .field .fst) 3 .neg Q)

def standard_three_distance (K : EuclideanField) (P Q : Fin 3 → ef_carrier K) : ef_carrier K
  ≔ ip_norm K (standard_inner_product_space K 3) (standard_three_difference K P Q)

def fin_three_funext (S : Type) (f g : Fin 3 → S) (h0 : Id S (f (inl. (inl. (inr. star.)))) (g (inl. (inl. (inr. star.)))))
  (h1 : Id S (f (inl. (inr. star.))) (g (inl. (inr. star.)))) (h2 : Id S (f (inr. star.)) (g (inr. star.)))
  : Id (Fin 3 → S) f g
  ≔ funext (Fin 3) (_ ↦ S) f g
      (t ↦ match t [
       | inl. u ↦ match u [
         | inl. v ↦ match v [ inl. e ↦ match e [ ] | inr. star. ↦ h0 ]
         | inr. star. ↦ h1 ]
       | inr. star. ↦ h2 ])

{` The remark's computation: (0,1,φ) - (1,φ,0) has squared norm 4. `}
def icosahedron_edge_square (K : EuclideanField)
  : Id (ef_carrier K)
      (dot_product K 3 (standard_three_difference K (icosahedron_vertex K (inl. (inl. (inr. star.)), (true., true.)))
                                                      (icosahedron_vertex K (inr. star., (true., true.))))
                       (standard_three_difference K (icosahedron_vertex K (inl. (inl. (inr. star.)), (true., true.)))
                                                      (icosahedron_vertex K (inr. star., (true., true.)))))
      (ring_of_nat (K .field .fst) 4)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let m ≔ R .mul in let a ≔ R .add in let ng ≔ R .neg in
    let z ≔ R .zero in let o ≔ R .one in let φ ≔ golden_ratio K in let G ≔ ring_additive_group R in
    let X ≔ a o (ng φ) in
    let c0 : Id S (m (a z (ng o)) (a z (ng o))) o
      ≔ calc
          m (a z (ng o)) (a z (ng o)) = m (ng o) (ng o) by refl (m) (R .add_laws .unit_left (ng o)) (R .add_laws .unit_left (ng o))
          = m o o by inverse S (m o o) (m (ng o) (ng o)) (ring_neg_neg_mul R o o)
          = o by ring_mul_one_left R o ∎ in
    let c1 : Id S (m X X) (a X o)
      ≔ calc
          m X X = a (m o X) (m (ng φ) X) by ring_rdistr R o (ng φ) X
          = a X (a (m (ng φ) o) (m (ng φ) (ng φ))) by refl (a) (ring_mul_one_left R X) (ring_ldistr R (ng φ) o (ng φ))
          = a X (a (ng φ) (m φ φ))
            by refl (a X) (refl (a) (ring_mul_one_right R (ng φ)) (inverse S (m φ φ) (m (ng φ) (ng φ)) (ring_neg_neg_mul R φ φ)))
          = a X (a (ng φ) (a φ o)) by refl ((y ↦ a X (a (ng φ) y)) : S → S) (golden_ratio_square K)
          = a X (a (a (ng φ) φ) o) by refl (a X) (ring_add_assoc R (ng φ) φ o)
          = a X (a z o) by refl ((y ↦ a X (a y o)) : S → S) (ag_inv_left G φ)
          = a X o by refl (a X) (R .add_laws .unit_left o) ∎ in
    let c2 : Id S (m (a φ (ng z)) (a φ (ng z))) (a φ o)
      ≔ let e : Id S (a φ (ng z)) φ
          ≔ concat S (a φ (ng z)) (a φ z) φ (refl (a φ) (ag_inv_unit G)) (R .add_laws .unit_right φ) in
        concat S (m (a φ (ng z)) (a φ (ng z))) (m φ φ) (a φ o) (refl (m) e e) (golden_ratio_square K) in
    let Xφ : Id S (a X φ) o
      ≔ calc
          a X φ = a o (a (ng φ) φ) by inverse S (a o (a (ng φ) φ)) (a X φ) (ring_add_assoc R o (ng φ) φ)
          = a o z by refl (a o) (ag_inv_left G φ)
          = o by R .add_laws .unit_right o ∎ in
    calc
      a (a (a z (m (a z (ng o)) (a z (ng o)))) (m X X)) (m (a φ (ng z)) (a φ (ng z)))
      = a (a (a z o) (a X o)) (a φ o) by refl (a) (refl (a) (refl (a z) c0) c1) c2
      = a (a o (a X o)) (a φ o) by refl ((y ↦ a (a y (a X o)) (a φ o)) : S → S) (R .add_laws .unit_left o)
      = a (a o (a o X)) (a φ o) by refl ((y ↦ a (a o y) (a φ o)) : S → S) (ring_add_comm R X o)
      = a (a (a o o) X) (a φ o) by refl ((y ↦ a y (a φ o)) : S → S) (ring_add_assoc R o o X)
      = a (a (a (a o o) X) φ) o by ring_add_assoc R (a (a o o) X) φ o
      = a (a (a o o) (a X φ)) o
        by refl ((y ↦ a y o) : S → S) (inverse S (a (a o o) (a X φ)) (a (a (a o o) X) φ) (ring_add_assoc R (a o o) X φ))
      = a (a (a o o) o) o by refl ((y ↦ a (a (a o o) y) o) : S → S) Xφ
      = ring_of_nat R 4 by refl ((y ↦ a (a (a y o) o) o) : S → S) (inverse S (a z o) o (R .add_laws .unit_left o)) ∎

{` ‖(0,1,φ) - (1,φ,0)‖ = 2. `}
def icosahedron_edge_length (K : EuclideanField)
  : Id (ef_carrier K)
      (standard_three_distance K (icosahedron_vertex K (inl. (inl. (inr. star.)), (true., true.)))
        (icosahedron_vertex K (inr. star., (true., true.))))
      (ef_two K)
  ≔ let D ≔ standard_three_difference K (icosahedron_vertex K (inl. (inl. (inr. star.)), (true., true.)))
              (icosahedron_vertex K (inr. star., (true., true.))) in
    let S ≔ ef_carrier K in
    ef_sqrt_unique K (dot_product K 3 D D) (dot_product_inner K 3 .nonneg D) (ef_two K) (ef_two_nonneg K)
      (concat S (K .field .fst .mul (ef_two K) (ef_two K)) (ring_of_nat (K .field .fst) 4) (dot_product K 3 D D)
        (ef_two_square K) (inverse S (dot_product K 3 D D) (ring_of_nat (K .field .fst) 4) (icosahedron_edge_square K)))

{` The golden rectangle A = (0,1,φ), B = (0,-1,φ), C = (0,-1,-φ), D = (0,1,-φ). `}
def golden_rectangle_a (K : EuclideanField) : Fin 3 → ef_carrier K ≔ icosahedron_vertex K (inl. (inl. (inr. star.)), (true., true.))
def golden_rectangle_b (K : EuclideanField) : Fin 3 → ef_carrier K ≔ icosahedron_vertex K (inl. (inl. (inr. star.)), (false., true.))
def golden_rectangle_c (K : EuclideanField) : Fin 3 → ef_carrier K ≔ icosahedron_vertex K (inl. (inl. (inr. star.)), (false., false.))
def golden_rectangle_d (K : EuclideanField) : Fin 3 → ef_carrier K ≔ icosahedron_vertex K (inl. (inl. (inr. star.)), (true., false.))

{` A - B = (0, 2, 0) = D - C. `}
def golden_short_side (K : EuclideanField) : Fin 3 → ef_carrier K
  ≔ triple_vector (ef_carrier K) (K .field .fst .zero) (ef_two K) (K .field .fst .zero)

def golden_long_side (K : EuclideanField) : Fin 3 → ef_carrier K
  ≔ triple_vector (ef_carrier K) (K .field .fst .zero) (K .field .fst .zero) (K .field .fst .add (golden_ratio K) (golden_ratio K))

def golden_rectangle_ab (K : EuclideanField)
  : Id (Fin 3 → ef_carrier K) (standard_three_difference K (golden_rectangle_a K) (golden_rectangle_b K)) (golden_short_side K)
  ≔ let R ≔ K .field .fst in let G ≔ ring_additive_group R in let S ≔ R .carrier in
    fin_three_funext S (standard_three_difference K (golden_rectangle_a K) (golden_rectangle_b K)) (golden_short_side K)
      (R .add_laws .inv_right (R .zero)) (refl (R .add (R .one)) (ag_inv_inv G (R .one))) (R .add_laws .inv_right (golden_ratio K))

def golden_rectangle_dc (K : EuclideanField)
  : Id (Fin 3 → ef_carrier K) (standard_three_difference K (golden_rectangle_d K) (golden_rectangle_c K)) (golden_short_side K)
  ≔ let R ≔ K .field .fst in let G ≔ ring_additive_group R in let S ≔ R .carrier in
    fin_three_funext S (standard_three_difference K (golden_rectangle_d K) (golden_rectangle_c K)) (golden_short_side K)
      (R .add_laws .inv_right (R .zero)) (refl (R .add (R .one)) (ag_inv_inv G (R .one)))
      (R .add_laws .inv_right (R .neg (golden_ratio K)))

def golden_rectangle_ad (K : EuclideanField)
  : Id (Fin 3 → ef_carrier K) (standard_three_difference K (golden_rectangle_a K) (golden_rectangle_d K)) (golden_long_side K)
  ≔ let R ≔ K .field .fst in let G ≔ ring_additive_group R in let S ≔ R .carrier in
    fin_three_funext S (standard_three_difference K (golden_rectangle_a K) (golden_rectangle_d K)) (golden_long_side K)
      (R .add_laws .inv_right (R .zero)) (R .add_laws .inv_right (R .one)) (refl (R .add (golden_ratio K)) (ag_inv_inv G (golden_ratio K)))

{` Short side 2, long side 2φ, orthogonal sides. `}
def golden_short_side_square (K : EuclideanField)
  : Id (ef_carrier K) (dot_product K 3 (golden_short_side K) (golden_short_side K)) (K .field .fst .mul (ef_two K) (ef_two K))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let z ≔ R .zero in let a ≔ R .add in let m ≔ R .mul in
    let t ≔ ef_two K in
    calc
      a (a (a z (m z z)) (m t t)) (m z z) = a (a (a z z) (m t t)) z
        by refl (a) (refl ((y ↦ a (a z y) (m t t)) : S → S) (ring_mul_zero_left R z)) (ring_mul_zero_left R z)
      = a (a z (m t t)) z by refl ((y ↦ a (a y (m t t)) z) : S → S) (R .add_laws .unit_left z)
      = a z (m t t) by R .add_laws .unit_right (a z (m t t))
      = m t t by R .add_laws .unit_left (m t t) ∎

def golden_long_side_square (K : EuclideanField)
  : Id (ef_carrier K) (dot_product K 3 (golden_long_side K) (golden_long_side K))
      (K .field .fst .mul (K .field .fst .add (golden_ratio K) (golden_ratio K)) (K .field .fst .add (golden_ratio K) (golden_ratio K)))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let z ≔ R .zero in let a ≔ R .add in let m ≔ R .mul in
    let u ≔ a (golden_ratio K) (golden_ratio K) in
    calc
      a (a (a z (m z z)) (m z z)) (m u u) = a (a (a z z) z) (m u u)
        by refl ((y ↦ a (a (a z y) y) (m u u)) : S → S) (ring_mul_zero_left R z)
      = a (a z z) (m u u) by refl ((y ↦ a y (m u u)) : S → S) (R .add_laws .unit_right (a z z))
      = a z (m u u) by refl ((y ↦ a y (m u u)) : S → S) (R .add_laws .unit_right z)
      = m u u by R .add_laws .unit_left (m u u) ∎

def golden_sides_orthogonal (K : EuclideanField)
  : Id (ef_carrier K) (dot_product K 3 (golden_short_side K) (golden_long_side K)) (K .field .fst .zero)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let z ≔ R .zero in let a ≔ R .add in let m ≔ R .mul in
    let t ≔ ef_two K in let u ≔ a (golden_ratio K) (golden_ratio K) in
    calc
      a (a (a z (m z z)) (m t z)) (m z u) = a (a (a z z) z) z
        by refl (a) (refl (a) (refl (a z) (ring_mul_zero_left R z)) (ring_mul_zero_right R t)) (ring_mul_zero_left R u)
      = a (a z z) z by refl ((y ↦ a y z) : S → S) (R .add_laws .unit_right (a z z))
      = a z z by R .add_laws .unit_right (a z z)
      = z by R .add_laws .unit_right z ∎

def golden_rectangle_short_length (K : EuclideanField)
  : Id (ef_carrier K) (standard_three_distance K (golden_rectangle_a K) (golden_rectangle_b K)) (ef_two K)
  ≔ let D ≔ standard_three_difference K (golden_rectangle_a K) (golden_rectangle_b K) in
    let S ≔ ef_carrier K in let F ≔ Fin 3 → S in
    ef_sqrt_unique K (dot_product K 3 D D) (dot_product_inner K 3 .nonneg D) (ef_two K) (ef_two_nonneg K)
      (inverse S (dot_product K 3 D D) (K .field .fst .mul (ef_two K) (ef_two K))
        (concat S (dot_product K 3 D D) (dot_product K 3 (golden_short_side K) (golden_short_side K))
           (K .field .fst .mul (ef_two K) (ef_two K))
           (refl ((v ↦ dot_product K 3 v v) : F → S) (golden_rectangle_ab K)) (golden_short_side_square K)))

def golden_rectangle_long_length (K : EuclideanField)
  : Id (ef_carrier K) (standard_three_distance K (golden_rectangle_a K) (golden_rectangle_d K))
      (K .field .fst .add (golden_ratio K) (golden_ratio K))
  ≔ let D ≔ standard_three_difference K (golden_rectangle_a K) (golden_rectangle_d K) in
    let S ≔ ef_carrier K in let F ≔ Fin 3 → S in let u ≔ K .field .fst .add (golden_ratio K) (golden_ratio K) in
    ef_sqrt_unique K (dot_product K 3 D D) (dot_product_inner K 3 .nonneg D) u
      (K .nonneg_add (golden_ratio K) (golden_ratio K) (golden_ratio_nonneg K) (golden_ratio_nonneg K))
      (inverse S (dot_product K 3 D D) (K .field .fst .mul u u)
        (concat S (dot_product K 3 D D) (dot_product K 3 (golden_long_side K) (golden_long_side K)) (K .field .fst .mul u u)
           (refl ((v ↦ dot_product K 3 v v) : F → S) (golden_rectangle_ad K)) (golden_long_side_square K)))

{` φ(φ - 1) = 1, so φ - 1 = φ⁻¹ = φ (φ - 1)² ≥ 0: the side 2 is the short one. `}
def golden_ratio_times_pred (K : EuclideanField)
  : Id (ef_carrier K) (K .field .fst .mul (golden_ratio K) (K .field .fst .add (golden_ratio K) (K .field .fst .neg (K .field .fst .one))))
      (K .field .fst .one)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let a ≔ R .add in let m ≔ R .mul in let ng ≔ R .neg in
    let o ≔ R .one in let φ ≔ golden_ratio K in
    calc
      m φ (a φ (ng o)) = a (m φ φ) (m φ (ng o)) by ring_ldistr R φ φ (ng o)
      = a (a φ o) (ng (m φ o)) by refl (a) (golden_ratio_square K) (ring_mul_neg_right R φ o)
      = a (a φ o) (ng φ) by refl ((y ↦ a (a φ o) (ng y)) : S → S) (ring_mul_one_right R φ)
      = a (a o φ) (ng φ) by refl ((y ↦ a y (ng φ)) : S → S) (ring_add_comm R φ o)
      = a o (a φ (ng φ)) by inverse S (a o (a φ (ng φ))) (a (a o φ) (ng φ)) (ring_add_assoc R o φ (ng φ))
      = a o (R .zero) by refl (a o) (R .add_laws .inv_right φ)
      = o by R .add_laws .unit_right o ∎

def golden_ratio_ge_one (K : EuclideanField)
  : K .nonneg (K .field .fst .add (golden_ratio K) (K .field .fst .neg (K .field .fst .one)))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let m ≔ R .mul in
    let φ ≔ golden_ratio K in let y ≔ R .add φ (R .neg (R .one)) in
    ef_transport_nonneg K (m φ (m y y)) y
      (calc
         m φ (m y y) = m (m φ y) y by ring_mul_assoc R φ y y
         = m (R .one) y by refl ((x ↦ m x y) : S → S) (golden_ratio_times_pred K)
         = y by ring_mul_one_left R y ∎)
      (K .nonneg_mul φ (m y y) (golden_ratio_nonneg K) (K .nonneg_square y))

{` 2φ - 2 = 2(φ - 1) ≥ 0. `}
def golden_rectangle_short_le_long (K : EuclideanField)
  : K .nonneg (K .field .fst .add (K .field .fst .add (golden_ratio K) (golden_ratio K)) (K .field .fst .neg (ef_two K)))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let a ≔ R .add in let ng ≔ R .neg in
    let G ≔ ring_additive_group R in
    let φ ≔ golden_ratio K in let o ≔ R .one in let y ≔ a φ (ng o) in
    ef_transport_nonneg K (a y y) (a (a φ φ) (ng (a o o)))
      (calc
         a y y = a (a φ φ) (a (ng o) (ng o)) by abstract_abelian_interchange G (ring_additive_abelian R) φ (ng o) φ (ng o)
         = a (a φ φ) (ng (a o o))
           by refl (a (a φ φ)) (inverse S (ng (a o o)) (a (ng o) (ng o)) (ag_inv_mul G o o)) ∎)
      (K .nonneg_add y y (golden_ratio_ge_one K) (golden_ratio_ge_one K))
