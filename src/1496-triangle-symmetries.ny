export "1495-triangle-apex"

{` For a loop z of (𝔼², {0}) with a lift r (refl pom r = z), the isometry
   of r is the transport of points along z (stated for variables r, z, p so
   that the lift is never unfolded). `}
def origin_loop_isometry_transport (K : EuclideanField) (r : USym (orthogonal_group K 2))
  (z : Id (EuclideanObject K propositions_settype) (origin_object K 2) (origin_object K 2))
  (p : Id (Id (EuclideanObject K propositions_settype) (origin_object K 2) (origin_object K 2)) (refl (point_object_map K 2) r) z)
  (X : Fin 2 → ef_carrier K)
  : Id (Fin 2 → ef_carrier K) (orthogonal_usym_isometry_equiv K 2 .map r .fst .fst .map X) (plane_point_transport K (z .fst) X)
  ≔ let F ≔ Fin 2 → ef_carrier K in
    let Obj ≔ EuclideanObject K propositions_settype in let o0 ≔ origin_object K 2 in
    concat F (orthogonal_usym_isometry_equiv K 2 .map r .fst .fst .map X)
      (plane_point_transport K (refl (point_object_map K 2) r .fst) X) (plane_point_transport K (z .fst) X)
      (inverse F (plane_point_transport K (refl (point_object_map K 2) r .fst) X)
        (orthogonal_usym_isometry_equiv K 2 .map r .fst .fst .map X) (origin_loop_transport K r X))
      (refl ((zz ↦ plane_point_transport K (zz .fst) X) : Id Obj o0 o0 → F) p)

{` A linear map of K² is determined by its values at A = e₁ and B = e₂. `}
def plane_linear_expand (K : EuclideanField) (f : (Fin 2 → ef_carrier K) → Fin 2 → ef_carrier K)
  (hadd : IsAbstractHom (module_group (K .field .fst) (standard_vector_space (K .field) 2))
            (module_group (K .field .fst) (standard_vector_space (K .field) 2)) f)
  (hsm : IsLinear (K .field .fst) (standard_vector_space (K .field) 2) (standard_vector_space (K .field) 2) f)
  (X : Fin 2 → ef_carrier K)
  : Id (Fin 2 → ef_carrier K) (f X)
      (standard_vector_space (K .field) 2 .add
        (standard_vector_space (K .field) 2 .smul (X fin_two_first) (f (triangle_vertex_a K)))
        (standard_vector_space (K .field) 2 .smul (X fin_two_second) (f (triangle_vertex_b K))))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let F ≔ Fin 2 → S in let V ≔ standard_vector_space (K .field) 2 in
    let A ≔ triangle_vertex_a K in let B ≔ triangle_vertex_b K in
    let x0 ≔ X fin_two_first in let x1 ≔ X fin_two_second in
    let Xe : Id F X (V .add (V .smul x0 A) (V .smul x1 B))
      ≔ fin_two_funext S X (V .add (V .smul x0 A) (V .smul x1 B))
          (calc
             x0 = R .add x0 (R .zero) by inverse S (R .add x0 (R .zero)) x0 (R .add_laws .unit_right x0)
             = R .add (R .mul x0 (R .one)) (R .mul x1 (R .zero))
               by refl (R .add) (inverse S (R .mul x0 (R .one)) x0 (ring_mul_one_right R x0))
                    (inverse S (R .mul x1 (R .zero)) (R .zero) (ring_mul_zero_right R x1)) ∎)
          (calc
             x1 = R .add (R .zero) x1 by inverse S (R .add (R .zero) x1) x1 (R .add_laws .unit_left x1)
             = R .add (R .mul x0 (R .zero)) (R .mul x1 (R .one))
               by refl (R .add) (inverse S (R .mul x0 (R .zero)) (R .zero) (ring_mul_zero_right R x0))
                    (inverse S (R .mul x1 (R .one)) x1 (ring_mul_one_right R x1)) ∎) in
    calc
      f X = f (V .add (V .smul x0 A) (V .smul x1 B)) by refl f Xe
      = V .add (f (V .smul x0 A)) (f (V .smul x1 B)) by hadd (V .smul x0 A) (V .smul x1 B)
      = V .add (V .smul x0 (f A)) (V .smul x1 (f B)) by refl (V .add) (hsm x0 A) (hsm x1 B) ∎

def triangle_isometries_agree (K : EuclideanField)
  (φ ψ : LinearIsometry K (standard_inner_product_space K 2) (standard_inner_product_space K 2))
  (hA : Id (Fin 2 → ef_carrier K) (φ .fst .fst .map (triangle_vertex_a K)) (ψ .fst .fst .map (triangle_vertex_a K)))
  (hB : Id (Fin 2 → ef_carrier K) (φ .fst .fst .map (triangle_vertex_b K)) (ψ .fst .fst .map (triangle_vertex_b K)))
  : Id (LinearIsometry K (standard_inner_product_space K 2) (standard_inner_product_space K 2)) φ ψ
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let F ≔ Fin 2 → S in let V ≔ standard_vector_space (K .field) 2 in
    let I ≔ standard_inner_product_space K 2 in
    let f ≔ φ .fst .fst .map in let g ≔ ψ .fst .fst .map in
    linear_isometry_path K I I φ ψ
      (funext F (_ ↦ F) f g
        (X ↦ calc
           f X = V .add (V .smul (X fin_two_first) (f (triangle_vertex_a K))) (V .smul (X fin_two_second) (f (triangle_vertex_b K)))
             by plane_linear_expand K f (φ .fst .snd .fst) (φ .fst .snd .snd) X
           = V .add (V .smul (X fin_two_first) (g (triangle_vertex_a K))) (V .smul (X fin_two_second) (g (triangle_vertex_b K)))
             by refl ((u v ↦ V .add (V .smul (X fin_two_first) u) (V .smul (X fin_two_second) v)) : F → F → F) hA hB
           = g X by inverse F (g X) (V .add (V .smul (X fin_two_first) (g (triangle_vertex_a K))) (V .smul (X fin_two_second) (g (triangle_vertex_b K))))
                      (plane_linear_expand K g (ψ .fst .snd .fst) (ψ .fst .snd .snd) X) ∎))

{` A symmetry of T is determined by the images of A and B. `}
def triangle_loop_determined_core (K : EuclideanField) (ℓ1 ℓ2 : TriangleLoop K) (r1 r2 : USym (orthogonal_group K 2))
  (p1 : Id (Id (EuclideanObject K propositions_settype) (origin_object K 2) (origin_object K 2))
          (refl (point_object_map K 2) r1) (triangle_loop_origin K ℓ1))
  (p2 : Id (Id (EuclideanObject K propositions_settype) (origin_object K 2) (origin_object K 2))
          (refl (point_object_map K 2) r2) (triangle_loop_origin K ℓ2))
  (hA : Id (Fin 2 → ef_carrier K) (triangle_loop_transport K ℓ1 (triangle_vertex_a K)) (triangle_loop_transport K ℓ2 (triangle_vertex_a K)))
  (hB : Id (Fin 2 → ef_carrier K) (triangle_loop_transport K ℓ1 (triangle_vertex_b K)) (triangle_loop_transport K ℓ2 (triangle_vertex_b K)))
  : Id (TriangleLoop K) ℓ1 ℓ2
  ≔ let F ≔ Fin 2 → ef_carrier K in
    let Obj ≔ EuclideanObject K propositions_settype in let o0 ≔ origin_object K 2 in
    let ES ≔ EuclideanSpace K in let E2 ≔ standard_plane K in
    let O ≔ USym (orthogonal_group K 2) in
    let I ≔ standard_inner_product_space K 2 in let LI ≔ LinearIsometry K I I in
    let Iso ≔ orthogonal_usym_isometry_equiv K 2 in
    let inv ≔ equiv_inverse_map O LI Iso in
    let A ≔ triangle_vertex_a K in let B ≔ triangle_vertex_b K in
    let t1 ≔ origin_loop_isometry_transport K r1 (triangle_loop_origin K ℓ1) p1 in
    let t2 ≔ origin_loop_isometry_transport K r2 (triangle_loop_origin K ℓ2) p2 in
    let at : (X : F) → Id F (triangle_loop_transport K ℓ1 X) (triangle_loop_transport K ℓ2 X)
          → Id F (Iso .map r1 .fst .fst .map X) (Iso .map r2 .fst .fst .map X)
      ≔ X h ↦ concat F (Iso .map r1 .fst .fst .map X) (triangle_loop_transport K ℓ1 X) (Iso .map r2 .fst .fst .map X)
          (t1 X)
          (concat F (triangle_loop_transport K ℓ1 X) (triangle_loop_transport K ℓ2 X) (Iso .map r2 .fst .fst .map X) h
            (inverse F (Iso .map r2 .fst .fst .map X) (triangle_loop_transport K ℓ2 X) (t2 X))) in
    let φe : Id LI (Iso .map r1) (Iso .map r2) ≔ triangle_isometries_agree K (Iso .map r1) (Iso .map r2) (at A hA) (at B hB) in
    let re : Id O r1 r2
      ≔ calc
          r1 = inv (Iso .map r1) by equiv_unit O LI Iso r1
          = inv (Iso .map r2) by refl inv φe
          = r2 by inverse O r2 (inv (Iso .map r2)) (equiv_unit O LI Iso r2) ∎ in
    let PO ≔ Id Obj o0 o0 in
    let ze : Id PO (triangle_loop_origin K ℓ1) (triangle_loop_origin K ℓ2)
      ≔ calc
          triangle_loop_origin K ℓ1 = refl (point_object_map K 2) r1
            by inverse PO (refl (point_object_map K 2) r1) (triangle_loop_origin K ℓ1) p1
          = refl (point_object_map K 2) r2 by refl ((r ↦ refl (point_object_map K 2) r) : O → PO) re
          = triangle_loop_origin K ℓ2 by p2 ∎ in
    sigma_set_path_of_fst ES ((E ↦ euclidean_points K E → PropTypes) : ES → Type)
      (E ↦ pi_set (euclidean_points K E) (_ ↦ PropTypes) (_ ↦ propositions_set))
      (triangle_object K) (triangle_object K) ℓ1 ℓ2
      (refl ((zz ↦ zz .fst) : PO → Id ES E2 E2) ze)

def triangle_loop_determined (K : EuclideanField) (ℓ1 ℓ2 : TriangleLoop K)
  (hA : Id (Fin 2 → ef_carrier K) (triangle_loop_transport K ℓ1 (triangle_vertex_a K)) (triangle_loop_transport K ℓ2 (triangle_vertex_a K)))
  (hB : Id (Fin 2 → ef_carrier K) (triangle_loop_transport K ℓ1 (triangle_vertex_b K)) (triangle_loop_transport K ℓ2 (triangle_vertex_b K)))
  : Id (TriangleLoop K) ℓ1 ℓ2
  ≔ let w1 ≔ origin_loop_lift K (triangle_loop_origin K ℓ1) in
    let w2 ≔ origin_loop_lift K (triangle_loop_origin K ℓ2) in
    triangle_loop_determined_core K ℓ1 ℓ2 (w1 .fst) (w2 .fst) (w1 .snd) (w2 .snd) hA hB
