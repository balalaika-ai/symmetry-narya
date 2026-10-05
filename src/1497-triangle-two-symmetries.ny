export "1496-triangle-symmetries"

{` Chapter 14, geometry.tex 80, conclusion: the two symmetries of the
   isosceles triangle T (identity and the reflection in the midline y = x,
   the coordinate swap), and USym Sym(T) ≃ Bool. `}

def triangle_swap_symmetry (K : EuclideanField) : USym (orthogonal_group K 2)
  ≔ orthogonal_symmetry K 2 (coordinate_swap_isometry K)

def triangle_swap_space_loop (K : EuclideanField) : Id (EuclideanSpace K) (standard_plane K) (standard_plane K)
  ≔ refl (point_object_map K 2) (triangle_swap_symmetry K) .fst

def triangle_swap_transport (K : EuclideanField) (X : Fin 2 → ef_carrier K)
  : Id (Fin 2 → ef_carrier K) (plane_point_transport K (triangle_swap_space_loop K) X) (coordinate_swap (ef_carrier K) X)
  ≔ refl (coordinate_swap (ef_carrier K) X)

{` The swap maps T onto T. `}
def triangle_swap_vertex (K : EuclideanField) (Q : Fin 2 → ef_carrier K) (t : TriangleVertex K Q)
  : TriangleVertex K (coordinate_swap (ef_carrier K) Q)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let F ≔ Fin 2 → S in let sw ≔ coordinate_swap S in
    let C ≔ triangle_apex K in let A ≔ triangle_vertex_a K in let B ≔ triangle_vertex_b K in
    match t [
    | inl. e ↦ inl. (concat F (sw Q) (sw C) C (refl sw e) (fin_two_funext S (sw C) C (refl (R .zero)) (refl (R .zero))))
    | inr. (inl. e) ↦ inr. (inr. (concat F (sw Q) (sw A) B (refl sw e) (fin_two_funext S (sw A) B (refl (R .zero)) (refl (R .one)))))
    | inr. (inr. e) ↦ inr. (inl. (concat F (sw Q) (sw B) A (refl sw e) (fin_two_funext S (sw B) A (refl (R .one)) (refl (R .zero))))) ]

def triangle_swap_pred (K : EuclideanField) (P : Fin 2 → ef_carrier K)
  : Id PropTypes (triangle_pred K P) (triangle_pred K (coordinate_swap (ef_carrier K) P))
  ≔ let S ≔ ef_carrier K in let F ≔ Fin 2 → S in let sw ≔ coordinate_swap S in
    let TV ≔ TriangleVertex K in
    let ss : Id F (sw (sw P)) P ≔ fin_two_funext S (sw (sw P)) P (refl (P fin_two_first)) (refl (P fin_two_second)) in
    proposition_extensionality (triangle_pred K P) (triangle_pred K (sw P))
      (mere_rec (TV P) (Mere (TV (sw P))) (mere_isprop (TV (sw P))) (t ↦ mere (TV (sw P)) (triangle_swap_vertex K P t)))
      (mere_rec (TV (sw P)) (Mere (TV P)) (mere_isprop (TV P))
        (t ↦ mere (TV P) (transport F TV (sw (sw P)) P ss (triangle_swap_vertex K (sw P) t))))

def triangle_swap_loop (K : EuclideanField) : TriangleLoop K
  ≔ let S ≔ ef_carrier K in let F ≔ Fin 2 → S in let sw ≔ coordinate_swap S in
    let ℓ ≔ triangle_swap_space_loop K in let Pt ≔ refl (euclidean_points K) ℓ in
    (ℓ,
     x ⤇
       let q : Id F (sw x.0) x.1
         ≔ concat F (sw x.0) (Pt .trr x.0) x.1
             (inverse F (Pt .trr x.0) (sw x.0) (triangle_swap_transport K x.0))
             (type_pathover_transport F F Pt x.0 x.1 x.2) in
       concat PropTypes (triangle_pred K x.0) (triangle_pred K (sw x.0)) (triangle_pred K x.1)
         (triangle_swap_pred K x.0) (refl (triangle_pred K) q))

{` Which of A, B a symmetry sends A to. `}
def TriangleSide (K : EuclideanField) (X : Fin 2 → ef_carrier K) : Type
  ≔ Sum (Id (Fin 2 → ef_carrier K) X (triangle_vertex_a K)) (Id (Fin 2 → ef_carrier K) X (triangle_vertex_b K))

def triangle_side_prop (K : EuclideanField) (X : Fin 2 → ef_carrier K) : isProp (TriangleSide K X)
  ≔ let F ≔ Fin 2 → ef_carrier K in
    disjoint_sum_prop (Id F X (triangle_vertex_a K)) (Id F X (triangle_vertex_b K))
      (plane_set K X (triangle_vertex_a K)) (plane_set K X (triangle_vertex_b K))
      (eA eB ↦ triangle_a_ne_b K (concat F (triangle_vertex_a K) X (triangle_vertex_b K) (inverse F X (triangle_vertex_a K) eA) eB))

def triangle_side_bool (K : EuclideanField) (X : Fin 2 → ef_carrier K) (d : TriangleSide K X) : Bool
  ≔ match d [ inl. _ ↦ true. | inr. _ ↦ false. ]

def triangle_loop_side (K : EuclideanField) (ℓL : TriangleLoop K) (X : Fin 2 → ef_carrier K) (hX : TriangleVertex K X)
  (hXC : Id (Fin 2 → ef_carrier K) X (triangle_apex K) → Empty)
  : TriangleSide K (triangle_loop_transport K ℓL X)
  ≔ let F ≔ Fin 2 → ef_carrier K in let τ ≔ triangle_loop_transport K ℓL in let C ≔ triangle_apex K in
    mere_rec (TriangleVertex K (τ X)) (TriangleSide K (τ X)) (triangle_side_prop K (τ X))
      (w ↦ match w [
        | inl. e ↦ match hXC (plane_point_transport_injective K (ℓL .fst) X C
                     (concat F (τ X) C (τ C) e (inverse F (τ C) C (triangle_loop_fixes_apex K ℓL)))) [ ]
        | inr. (inl. e) ↦ inl. e
        | inr. (inr. e) ↦ inr. e ])
      (triangle_loop_member K ℓL X hX)

def triangle_loop_side_a (K : EuclideanField) (ℓL : TriangleLoop K) : TriangleSide K (triangle_loop_transport K ℓL (triangle_vertex_a K))
  ≔ triangle_loop_side K ℓL (triangle_vertex_a K) (inr. (inl. (refl (triangle_vertex_a K)))) (triangle_a_ne_c K)

def triangle_loop_side_b (K : EuclideanField) (ℓL : TriangleLoop K) : TriangleSide K (triangle_loop_transport K ℓL (triangle_vertex_b K))
  ≔ triangle_loop_side K ℓL (triangle_vertex_b K) (inr. (inr. (refl (triangle_vertex_b K)))) (triangle_b_ne_c K)

def triangle_symmetry_bool (K : EuclideanField) (ℓL : TriangleLoop K) : Bool
  ≔ triangle_side_bool K (triangle_loop_transport K ℓL (triangle_vertex_a K)) (triangle_loop_side_a K ℓL)

def triangle_symmetry_of_bool (K : EuclideanField) (b : Bool) : TriangleLoop K
  ≔ match b [ true. ↦ refl (triangle_object K) | false. ↦ triangle_swap_loop K ]

{` The identity sends A to A, the reflection sends A to B. `}
def triangle_refl_transport (K : EuclideanField) (X : Fin 2 → ef_carrier K)
  : Id (Fin 2 → ef_carrier K) (triangle_loop_transport K (refl (triangle_object K)) X) X
  ≔ transport_refl (EuclideanSpace K) (euclidean_points K) (standard_plane K) X

def triangle_bool_refl (K : EuclideanField) : Id Bool (triangle_symmetry_bool K (refl (triangle_object K))) true.
  ≔ let X ≔ triangle_loop_transport K (refl (triangle_object K)) (triangle_vertex_a K) in
    refl (triangle_side_bool K X)
      (triangle_side_prop K X (triangle_loop_side_a K (refl (triangle_object K))) (inl. (triangle_refl_transport K (triangle_vertex_a K))))

def triangle_swap_a (K : EuclideanField)
  : Id (Fin 2 → ef_carrier K) (triangle_loop_transport K (triangle_swap_loop K) (triangle_vertex_a K)) (triangle_vertex_b K)
  ≔ let S ≔ ef_carrier K in
    concat (Fin 2 → S) (triangle_loop_transport K (triangle_swap_loop K) (triangle_vertex_a K))
      (coordinate_swap S (triangle_vertex_a K)) (triangle_vertex_b K)
      (triangle_swap_transport K (triangle_vertex_a K))
      (fin_two_funext S (coordinate_swap S (triangle_vertex_a K)) (triangle_vertex_b K) (refl (K .field .fst .zero)) (refl (K .field .fst .one)))

def triangle_swap_b (K : EuclideanField)
  : Id (Fin 2 → ef_carrier K) (triangle_loop_transport K (triangle_swap_loop K) (triangle_vertex_b K)) (triangle_vertex_a K)
  ≔ let S ≔ ef_carrier K in
    concat (Fin 2 → S) (triangle_loop_transport K (triangle_swap_loop K) (triangle_vertex_b K))
      (coordinate_swap S (triangle_vertex_b K)) (triangle_vertex_a K)
      (triangle_swap_transport K (triangle_vertex_b K))
      (fin_two_funext S (coordinate_swap S (triangle_vertex_b K)) (triangle_vertex_a K) (refl (K .field .fst .one)) (refl (K .field .fst .zero)))

def triangle_bool_swap (K : EuclideanField) : Id Bool (triangle_symmetry_bool K (triangle_swap_loop K)) false.
  ≔ let X ≔ triangle_loop_transport K (triangle_swap_loop K) (triangle_vertex_a K) in
    refl (triangle_side_bool K X)
      (triangle_side_prop K X (triangle_loop_side_a K (triangle_swap_loop K)) (inr. (triangle_swap_a K)))

{` If A ↦ A then B ↦ B; if A ↦ B then B ↦ A. `}
def triangle_b_fixed (K : EuclideanField) (ℓL : TriangleLoop K)
  (eA : Id (Fin 2 → ef_carrier K) (triangle_loop_transport K ℓL (triangle_vertex_a K)) (triangle_vertex_a K))
  : Id (Fin 2 → ef_carrier K) (triangle_loop_transport K ℓL (triangle_vertex_b K)) (triangle_vertex_b K)
  ≔ let F ≔ Fin 2 → ef_carrier K in let τ ≔ triangle_loop_transport K ℓL in
    let A ≔ triangle_vertex_a K in let B ≔ triangle_vertex_b K in
    match triangle_loop_side_b K ℓL [
    | inl. e ↦ match triangle_a_ne_b K (plane_point_transport_injective K (ℓL .fst) A B
                 (concat F (τ A) A (τ B) eA (inverse F (τ B) A e))) [ ]
    | inr. e ↦ e ]

def triangle_b_swapped (K : EuclideanField) (ℓL : TriangleLoop K)
  (eB : Id (Fin 2 → ef_carrier K) (triangle_loop_transport K ℓL (triangle_vertex_a K)) (triangle_vertex_b K))
  : Id (Fin 2 → ef_carrier K) (triangle_loop_transport K ℓL (triangle_vertex_b K)) (triangle_vertex_a K)
  ≔ let F ≔ Fin 2 → ef_carrier K in let τ ≔ triangle_loop_transport K ℓL in
    let A ≔ triangle_vertex_a K in let B ≔ triangle_vertex_b K in
    match triangle_loop_side_b K ℓL [
    | inl. e ↦ e
    | inr. e ↦ match triangle_a_ne_b K (plane_point_transport_injective K (ℓL .fst) A B
                 (concat F (τ A) B (τ B) eB (inverse F (τ B) B e))) [ ] ]

def triangle_section_aux (K : EuclideanField) (ℓL : TriangleLoop K)
  (d : TriangleSide K (triangle_loop_transport K ℓL (triangle_vertex_a K)))
  : Id (TriangleLoop K) (triangle_symmetry_of_bool K (triangle_side_bool K (triangle_loop_transport K ℓL (triangle_vertex_a K)) d)) ℓL
  ≔ let F ≔ Fin 2 → ef_carrier K in let τ ≔ triangle_loop_transport K ℓL in
    let A ≔ triangle_vertex_a K in let B ≔ triangle_vertex_b K in
    let r ≔ refl (triangle_object K) in let s ≔ triangle_swap_loop K in
    match d [
    | inl. eA ↦
      triangle_loop_determined K r ℓL
        (concat F (triangle_loop_transport K r A) A (τ A) (triangle_refl_transport K A) (inverse F (τ A) A eA))
        (concat F (triangle_loop_transport K r B) B (τ B) (triangle_refl_transport K B) (inverse F (τ B) B (triangle_b_fixed K ℓL eA)))
    | inr. eB ↦
      triangle_loop_determined K s ℓL
        (concat F (triangle_loop_transport K s A) B (τ A) (triangle_swap_a K) (inverse F (τ A) B eB))
        (concat F (triangle_loop_transport K s B) A (τ B) (triangle_swap_b K) (inverse F (τ B) A (triangle_b_swapped K ℓL eB))) ]

def triangle_loops_bool (K : EuclideanField) : Equiv (TriangleLoop K) Bool
  ≔ quasi_inverse_equiv (TriangleLoop K) Bool (triangle_symmetry_bool K) (triangle_symmetry_of_bool K)
      (ℓL ↦ triangle_section_aux K ℓL (triangle_loop_side_a K ℓL))
      (b ↦ match b [ true. ↦ triangle_bool_refl K | false. ↦ triangle_bool_swap K ])

{` geometry.tex 80: the isosceles non-equilateral triangle T has exactly two
   symmetries, the identity (true) and the reflection in its midline (false). `}
def isosceles_triangle_symmetries (K : EuclideanField)
  : Equiv (USym (geometric_object_symmetry_group K propositions_settype (triangle_object K))) Bool
  ≔ let Obj ≔ EuclideanObject K propositions_settype in
    compose_equiv (USym (geometric_object_symmetry_group K propositions_settype (triangle_object K))) (TriangleLoop K) Bool
      (automorphism_group_usym_equiv Obj (euclidean_object_groupoid K propositions_settype) (triangle_object K))
      (triangle_loops_bool K)

{` The two symmetries are different. `}
def triangle_reflection_nontrivial (K : EuclideanField)
  (e : Id (TriangleLoop K) (triangle_swap_loop K) (refl (triangle_object K))) : Empty
  ≔ let S ≔ ef_carrier K in let F ≔ Fin 2 → S in
    triangle_a_ne_b K
      (calc
         triangle_vertex_a K = triangle_loop_transport K (refl (triangle_object K)) (triangle_vertex_a K)
           by inverse F (triangle_loop_transport K (refl (triangle_object K)) (triangle_vertex_a K)) (triangle_vertex_a K) (triangle_refl_transport K (triangle_vertex_a K))
         = triangle_loop_transport K (triangle_swap_loop K) (triangle_vertex_a K)
           by refl ((ℓL ↦ triangle_loop_transport K ℓL (triangle_vertex_a K)) : TriangleLoop K → F)
                (inverse (TriangleLoop K) (triangle_swap_loop K) (refl (triangle_object K)) e)
         = triangle_vertex_b K by triangle_swap_a K ∎)
