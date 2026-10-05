export "1494-isosceles-triangle"

{` Transport of points along a symmetry ℓ of T, and T is preserved. `}
def triangle_loop_transport (K : EuclideanField) (ℓL : TriangleLoop K) (X : Fin 2 → ef_carrier K) : Fin 2 → ef_carrier K
  ≔ plane_point_transport K (ℓL .fst) X

def triangle_loop_member (K : EuclideanField) (ℓL : TriangleLoop K) (X : Fin 2 → ef_carrier K) (h : TriangleVertex K X)
  : Mere (TriangleVertex K (triangle_loop_transport K ℓL X))
  ≔ let Pt ≔ refl (euclidean_points K) (ℓL .fst) in
    refl ((p : PropTypes) ↦ p .fst) (ℓL .snd (Pt .liftr X)) .trr (mere (TriangleVertex K X) h)

def triangle_norm_contra (K : EuclideanField) (ℓL : TriangleLoop K) (X Y W : Fin 2 → ef_carrier K)
  (hW : Id (Fin 2 → ef_carrier K) (triangle_loop_transport K ℓL (plane_origin K)) W)
  (hY : Id (Fin 2 → ef_carrier K) (triangle_loop_transport K ℓL X) Y)
  (hX : Id (ef_carrier K) (dot_product K 2 X X) (K .field .fst .one))
  (hD : Id (ef_carrier K) (dot_product K 2 (i ↦ K .field .fst .add (Y i) (K .field .fst .neg (W i)))
                                             (i ↦ K .field .fst .add (Y i) (K .field .fst .neg (W i))))
          (K .field .fst .add (K .field .fst .one) (K .field .fst .one)))
  : Empty
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let F ≔ Fin 2 → S in
    let ℓ ≔ ℓL .fst in
    let lx ≔ plane_vector_transport K ℓ X in
    let D ≔ (i : Fin 2) ↦ R .add (Y i) (R .neg (W i)) in
    ef_two_ne_one K
      (calc
         R .one = dot_product K 2 X X by inverse S (dot_product K 2 X X) (R .one) hX
         = dot_product K 2 lx lx by plane_transport_form K ℓ X X
         = dot_product K 2 D D by refl ((v ↦ dot_product K 2 v v) : F → S) (plane_vector_transport_solve K ℓ X Y W hW hY)
         = R .add (R .one) (R .one) by hD ∎)

{` Every symmetry fixes the apex C = 0. `}
def triangle_case_apex_a (K : EuclideanField) (ℓL : TriangleLoop K)
  (eA : Id (Fin 2 → ef_carrier K) (triangle_loop_transport K ℓL (triangle_apex K)) (triangle_vertex_a K)) : Empty
  ≔ let F ≔ Fin 2 → ef_carrier K in let τ ≔ triangle_loop_transport K ℓL in
    let C ≔ triangle_apex K in let A ≔ triangle_vertex_a K in let B ≔ triangle_vertex_b K in
    let inj ≔ plane_point_transport_injective K (ℓL .fst) in
    let TV ≔ TriangleVertex K in
    mere_rec (TV (τ A)) Empty empty_prop
      (wa ↦ mere_rec (TV (τ B)) Empty empty_prop
        (wb ↦ match wa [
          | inl. a0 ↦ match wb [
            | inl. b0 ↦ triangle_a_ne_b K (inj A B (concat F (τ A) C (τ B) a0 (inverse F (τ B) C b0)))
            | inr. (inl. b1) ↦ triangle_b_ne_c K (inj B C (concat F (τ B) A (τ C) b1 (inverse F (τ C) A eA)))
            | inr. (inr. b2) ↦ triangle_norm_contra K ℓL B B A eA b2 (triangle_b_norm K) (triangle_ba_norm K) ]
          | inr. (inl. a1) ↦ triangle_a_ne_c K (inj A C (concat F (τ A) A (τ C) a1 (inverse F (τ C) A eA)))
          | inr. (inr. a2) ↦ triangle_norm_contra K ℓL A B A eA a2 (triangle_a_norm K) (triangle_ba_norm K) ])
        (triangle_loop_member K ℓL B (inr. (inr. (refl B)))))
      (triangle_loop_member K ℓL A (inr. (inl. (refl A))))

def triangle_case_apex_b (K : EuclideanField) (ℓL : TriangleLoop K)
  (eB : Id (Fin 2 → ef_carrier K) (triangle_loop_transport K ℓL (triangle_apex K)) (triangle_vertex_b K)) : Empty
  ≔ let F ≔ Fin 2 → ef_carrier K in let τ ≔ triangle_loop_transport K ℓL in
    let C ≔ triangle_apex K in let A ≔ triangle_vertex_a K in let B ≔ triangle_vertex_b K in
    let inj ≔ plane_point_transport_injective K (ℓL .fst) in
    let TV ≔ TriangleVertex K in
    mere_rec (TV (τ A)) Empty empty_prop
      (wa ↦ mere_rec (TV (τ B)) Empty empty_prop
        (wb ↦ match wa [
          | inl. a0 ↦ match wb [
            | inl. b0 ↦ triangle_a_ne_b K (inj A B (concat F (τ A) C (τ B) a0 (inverse F (τ B) C b0)))
            | inr. (inl. b1) ↦ triangle_norm_contra K ℓL B A B eB b1 (triangle_b_norm K) (triangle_ab_norm K)
            | inr. (inr. b2) ↦ triangle_b_ne_c K (inj B C (concat F (τ B) B (τ C) b2 (inverse F (τ C) B eB))) ]
          | inr. (inl. a1) ↦ triangle_norm_contra K ℓL A A B eB a1 (triangle_a_norm K) (triangle_ab_norm K)
          | inr. (inr. a2) ↦ triangle_a_ne_c K (inj A C (concat F (τ A) B (τ C) a2 (inverse F (τ C) B eB))) ])
        (triangle_loop_member K ℓL B (inr. (inr. (refl B)))))
      (triangle_loop_member K ℓL A (inr. (inl. (refl A))))

def triangle_loop_fixes_apex (K : EuclideanField) (ℓL : TriangleLoop K)
  : Id (Fin 2 → ef_carrier K) (triangle_loop_transport K ℓL (triangle_apex K)) (triangle_apex K)
  ≔ let τ ≔ triangle_loop_transport K ℓL in let C ≔ triangle_apex K in
    mere_rec (TriangleVertex K (τ C)) (Id (Fin 2 → ef_carrier K) (τ C) C) (plane_set K (τ C) C)
      (w ↦ match w [
        | inl. e ↦ e
        | inr. (inl. eA) ↦ match triangle_case_apex_a K ℓL eA [ ]
        | inr. (inr. eB) ↦ match triangle_case_apex_b K ℓL eB [ ] ])
      (triangle_loop_member K ℓL C (inl. (refl C)))

{` So every symmetry of T is a symmetry of (𝔼², {0}). `}
def triangle_loop_origin (K : EuclideanField) (ℓL : TriangleLoop K)
  : Id (EuclideanObject K propositions_settype) (origin_object K 2) (origin_object K 2)
  ≔ let F ≔ Fin 2 → ef_carrier K in
    let ℓ ≔ ℓL .fst in let τ ≔ plane_point_transport K ℓ in let Pt ≔ refl (euclidean_points K) ℓ in
    let C ≔ plane_origin K in
    let apex ≔ triangle_loop_fixes_apex K ℓL in
    let g0 ≔ origin_pred K 2 in
    (ℓ,
     x ⤇
       let q : Id F (τ x.0) x.1 ≔ type_pathover_transport F F Pt x.0 x.1 x.2 in
       proposition_extensionality (g0 x.0) (g0 x.1)
         (e0 ↦ concat F x.1 (τ x.0) C (inverse F (τ x.0) x.1 q) (concat F (τ x.0) (τ C) C (refl τ e0) apex))
         (e1 ↦ plane_point_transport_injective K ℓ x.0 C
           (concat F (τ x.0) x.1 (τ C) q (concat F x.1 C (τ C) e1 (inverse F (τ C) C apex)))))

