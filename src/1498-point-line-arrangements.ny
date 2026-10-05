export "1497-triangle-two-symmetries"
export "1490-integer-ring-maps"
export "1441-golden-ratio"

{` Chapter 14, geometry.tex 279-284: "arrangements consisting of a point
   and a line in the plane. The arrangements where the point is at a
   distance d from the line, where d ≥ 0, are all merely equal to each
   other ... Hence, in some sense, the arrangements are classified by the
   set of nonnegative real numbers d." Formalized for the configurations
   (𝔼², {P}, x-axis) of a point P = (x, y) and the line y = 0 (the
   x-axis of the running text, at distance |y| = √(y²) from P), which are
   arrangements of the point object (𝔼², {0}) and the x-axis object:
   - pl_config_invariant: if (𝔼², {P}, x-axis) = (𝔼², {P'}, x-axis) as
     configurations then y² = y'² (the squared distance is an invariant);
   - pl_config_path: if y' = y or y' = -y then the two configurations are
     equal (by a translation along the x-axis and a reflection in it).
   So two such configurations are (merely) equal exactly when the point is
   at the same distance from the line (the second direction needs the sign
   of y' as data, since equality in K is not decidable). The general
   classification π₀(arrangements) ≃ {d ≥ 0} for arbitrary lines and
   points in arbitrary planes is not formalized (lines and distances to
   lines are not defined in the book). `}

{` Configurations of two objects in E, as pairs of predicates. `}
def PLObject (K : EuclideanField) : Type
  ≔ Σ (EuclideanSpace K) (E ↦ Product (euclidean_points K E → PropTypes) (euclidean_points K E → PropTypes))

def pl_select (A : Type) (p q : A) (b : Bool) : A ≔ match b [ true. ↦ p | false. ↦ q ]

def pl_to_config (K : EuclideanField) (x : PLObject K) : Configuration K Bool (_ ↦ propositions_settype)
  ≔ (x .fst, b ↦ pl_select (euclidean_points K (x .fst) → PropTypes) (x .snd .fst) (x .snd .snd) b)

def pl_from_config (K : EuclideanField) (c : Configuration K Bool (_ ↦ propositions_settype)) : PLObject K
  ≔ (c .fst, (c .snd true., c .snd false.))

def pl_object (K : EuclideanField) (P : Fin 2 → ef_carrier K) : PLObject K
  ≔ (standard_plane K, (single_pred K (standard_plane K) P, x_axis K))

def pl_config (K : EuclideanField) (P : Fin 2 → ef_carrier K) : Configuration K Bool (_ ↦ propositions_settype)
  ≔ pl_to_config K (pl_object K P)

{` These configurations are arrangements of the point object (𝔼², {0})
   and the x-axis object (x_axis_object), via the translation by P. `}
def pl_point_constituent (K : EuclideanField) (P : Fin 2 → ef_carrier K)
  : Id (EuclideanObject K propositions_settype) (origin_object K 2) (standard_plane K, single_pred K (standard_plane K) P)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let F ≔ Fin 2 → S in let V ≔ standard_vector_space (K .field) 2 in
    let ℓ ≔ refl ((E ↦ euclidean_space_dim_forget K 2 E) : EuclideanSpaceDim K 2 → EuclideanSpace K) (euclidean_translation K 2 P) in
    let Pt ≔ refl (euclidean_points K) ℓ in
    let C ≔ plane_origin K in
    let tP : Id F (Pt .trr C) P
      ≔ concat F (Pt .trr C) (V .add C P) P (euclidean_translation_act K 2 P C)
          (funext (Fin 2) (_ ↦ S) (V .add C P) P (i ↦ R .add_laws .unit_left (P i))) in
    (ℓ,
     x ⤇
       let q : Id F (Pt .trr x.0) x.1 ≔ type_pathover_transport F F Pt x.0 x.1 x.2 in
       proposition_extensionality (single_pred K (standard_plane K) C x.0) (single_pred K (standard_plane K) P x.1)
         (e0 ↦ concat F x.1 (Pt .trr x.0) P (inverse F (Pt .trr x.0) x.1 q) (concat F (Pt .trr x.0) (Pt .trr C) P (refl (Pt .trr) e0) tP))
         (e1 ↦ plane_point_transport_injective K ℓ x.0 C
           (concat F (Pt .trr x.0) x.1 (Pt .trr C) q (concat F x.1 P (Pt .trr C) e1 (inverse F (Pt .trr C) P tP)))))

def pl_config_arrangement (K : EuclideanField) (P : Fin 2 → ef_carrier K)
  : Arrangement K Bool (_ ↦ propositions_settype) (b ↦ pl_select (EuclideanObject K propositions_settype) (origin_object K 2) (x_axis_object K) b)
  ≔ let Obj ≔ EuclideanObject K propositions_settype in
    (pl_config K P,
     b ↦ match b [
       | true. ↦ mere (Id Obj (standard_plane K, single_pred K (standard_plane K) P) (origin_object K 2))
                   (inverse Obj (origin_object K 2) (standard_plane K, single_pred K (standard_plane K) P) (pl_point_constituent K P))
       | false. ↦ mere (Id Obj (x_axis_object K) (x_axis_object K)) (refl (x_axis_object K)) ])

{` The linear part of a loop of 𝔼² is linear. `}
def plane_vector_transport_add (K : EuclideanField) (ℓ : Id (EuclideanSpace K) (standard_plane K) (standard_plane K))
  : IsAbstractHom (module_group (K .field .fst) (standard_vector_space (K .field) 2))
      (module_group (K .field .fst) (standard_vector_space (K .field) 2)) (plane_vector_transport K ℓ)
  ≔ let F ≔ Fin 2 → ef_carrier K in let V ≔ refl (euclidean_vectors K) ℓ in
    x y ↦ type_pathover_transport F F V (standard_vector_space (K .field) 2 .add x y)
      (standard_vector_space (K .field) 2 .add (V .trr x) (V .trr y))
      (refl ((E ↦ E .fst .space .add) : (E : EuclideanSpace K) → euclidean_vectors K E → euclidean_vectors K E → euclidean_vectors K E)
        ℓ (V .liftr x) (V .liftr y))

def plane_vector_transport_smul (K : EuclideanField) (ℓ : Id (EuclideanSpace K) (standard_plane K) (standard_plane K))
  : IsLinear (K .field .fst) (standard_vector_space (K .field) 2) (standard_vector_space (K .field) 2) (plane_vector_transport K ℓ)
  ≔ let F ≔ Fin 2 → ef_carrier K in let V ≔ refl (euclidean_vectors K) ℓ in
    a x ↦ type_pathover_transport F F V (standard_vector_space (K .field) 2 .smul a x)
      (standard_vector_space (K .field) 2 .smul a (V .trr x))
      (refl ((E ↦ E .fst .space .smul) : (E : EuclideanSpace K) → ef_carrier K → euclidean_vectors K E → euclidean_vectors K E)
        ℓ (refl a) (V .liftr x))

{` Invariance: equal configurations have the same squared distance y². `}
def pl_config_invariant (K : EuclideanField) (P P' : Fin 2 → ef_carrier K)
  (e : Id (Configuration K Bool (_ ↦ propositions_settype)) (pl_config K P) (pl_config K P'))
  : Id (ef_carrier K) (K .field .fst .mul (P fin_two_second) (P fin_two_second)) (K .field .fst .mul (P' fin_two_second) (P' fin_two_second))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let F ≔ Fin 2 → S in
    let z ≔ R .zero in let o ≔ R .one in let a ≔ R .add in let m ≔ R .mul in
    let snd ≔ (X : F) ↦ X fin_two_second in let fst ≔ (X : F) ↦ X fin_two_first in
    let e' ≔ refl (pl_from_config K) e in
    let ℓ ≔ e' .fst in
    let Pt ≔ refl (euclidean_points K) ℓ in
    let τ ≔ plane_point_transport K ℓ in let λ ≔ plane_vector_transport K ℓ in
    let C ≔ plane_origin K in let A ≔ triangle_vertex_a K in let B ≔ triangle_vertex_b K in
    let axis : (X : F) → Id S (snd X) z → Id S (snd (τ X)) z
      ≔ X h ↦ refl ((p : PropTypes) ↦ p .fst) (e' .snd .snd (Pt .liftr X)) .trr h in
    let tP : Id F (τ P) P'
      ≔ refl ((p : PropTypes) ↦ p .fst) (e' .snd .fst (Pt .liftr P)) .trr (refl P) in
    let w0 : Id S (snd (τ C)) z ≔ axis C (refl z) in
    let aff ≔ (X : F) ↦ triangle_second K (τ X) (euclidean_translate K (standard_plane K) (λ X) (τ C)) (plane_transport_affine K ℓ X) in
    let l1y : Id S (snd (λ A)) z
      ≔ calc
          snd (λ A) = a (snd (λ A)) z by inverse S (a (snd (λ A)) z) (snd (λ A)) (R .add_laws .unit_right (snd (λ A)))
          = a (snd (λ A)) (snd (τ C)) by refl (a (snd (λ A))) (inverse S (snd (τ C)) z w0)
          = snd (τ A) by inverse S (snd (τ A)) (a (snd (λ A)) (snd (τ C))) (aff A)
          = z by axis A (refl z) ∎ in
    let c ≔ fst (λ A) in let u ≔ fst (λ B) in let v ≔ snd (λ B) in
    let cc : Id S (m c c) o
      ≔ calc
          m c c = a z (m c c) by inverse S (a z (m c c)) (m c c) (R .add_laws .unit_left (m c c))
          = a (a z (m c c)) z by inverse S (a (a z (m c c)) z) (a z (m c c)) (R .add_laws .unit_right (a z (m c c)))
          = a (a z (m c c)) (m (snd (λ A)) (snd (λ A)))
            by refl (a (a z (m c c))) (concat S z (m z z) (m (snd (λ A)) (snd (λ A))) (inverse S (m z z) z (ring_mul_zero_left R z))
                 (refl m (inverse S (snd (λ A)) z l1y) (inverse S (snd (λ A)) z l1y)))
          = dot_product K 2 A A by inverse S (dot_product K 2 A A) (dot_product K 2 (λ A) (λ A)) (plane_transport_form K ℓ A A)
          = o by triangle_a_norm K ∎ in
    let ab0 : Id S (dot_product K 2 A B) z
      ≔ calc
          a (a z (m o z)) (m z o) = a (a z z) z by refl a (refl (a z) (ring_mul_zero_right R o)) (ring_mul_zero_left R o)
          = a z z by refl ((y ↦ a y z) : S → S) (R .add_laws .unit_left z)
          = z by R .add_laws .unit_left z ∎ in
    let cu : Id S (m c u) z
      ≔ calc
          m c u = a z (m c u) by inverse S (a z (m c u)) (m c u) (R .add_laws .unit_left (m c u))
          = a (a z (m c u)) z by inverse S (a (a z (m c u)) z) (a z (m c u)) (R .add_laws .unit_right (a z (m c u)))
          = a (a z (m c u)) (m (snd (λ A)) v) by refl (a (a z (m c u))) (concat S z (m z v) (m (snd (λ A)) v)
                 (inverse S (m z v) z (ring_mul_zero_left R v)) (refl ((t ↦ m t v) : S → S) (inverse S (snd (λ A)) z l1y)))
          = dot_product K 2 A B by inverse S (dot_product K 2 A B) (dot_product K 2 (λ A) (λ B)) (plane_transport_form K ℓ A B)
          = z by ab0 ∎ in
    let u0 : Id S u z
      ≔ calc
          u = m o u by inverse S (m o u) u (ring_mul_one_left R u)
          = m (m c c) u by refl ((t ↦ m t u) : S → S) (inverse S (m c c) o cc)
          = m c (m c u) by inverse S (m c (m c u)) (m (m c c) u) (ring_mul_assoc R c c u)
          = m c z by refl (m c) cu
          = z by ring_mul_zero_right R c ∎ in
    let vv : Id S (m v v) o
      ≔ calc
          m v v = a z (m v v) by inverse S (a z (m v v)) (m v v) (R .add_laws .unit_left (m v v))
          = a (a z z) (m v v) by refl ((t ↦ a t (m v v)) : S → S) (inverse S (a z z) z (R .add_laws .unit_left z))
          = a (a z (m u u)) (m v v) by refl ((t ↦ a (a z t) (m v v)) : S → S)
                 (concat S z (m z z) (m u u) (inverse S (m z z) z (ring_mul_zero_left R z)) (refl m (inverse S u z u0) (inverse S u z u0)))
          = dot_product K 2 B B by inverse S (dot_product K 2 B B) (dot_product K 2 (λ B) (λ B)) (plane_transport_form K ℓ B B)
          = o by triangle_b_norm K ∎ in
    let ex ≔ plane_linear_expand K λ (plane_vector_transport_add K ℓ) (plane_vector_transport_smul K ℓ) P in
    let p0 ≔ fst P in let p1 ≔ snd P in
    let y' : Id S (snd P') (m p1 v)
      ≔ calc
          snd P' = snd (τ P) by inverse S (snd (τ P)) (snd P') (triangle_second K (τ P) P' tP)
          = a (snd (λ P)) (snd (τ C)) by aff P
          = a (snd (λ P)) z by refl (a (snd (λ P))) w0
          = snd (λ P) by R .add_laws .unit_right (snd (λ P))
          = a (m p0 (snd (λ A))) (m p1 v) by triangle_second K (λ P) (standard_vector_space (K .field) 2 .add
               (standard_vector_space (K .field) 2 .smul p0 (λ A)) (standard_vector_space (K .field) 2 .smul p1 (λ B))) ex
          = a (m p0 z) (m p1 v) by refl ((t ↦ a (m p0 t) (m p1 v)) : S → S) l1y
          = a z (m p1 v) by refl ((t ↦ a t (m p1 v)) : S → S) (ring_mul_zero_right R p0)
          = m p1 v by R .add_laws .unit_left (m p1 v) ∎ in
    calc
      m p1 p1 = m (m p1 p1) o by inverse S (m (m p1 p1) o) (m p1 p1) (ring_mul_one_right R (m p1 p1))
      = m (m p1 p1) (m v v) by refl (m (m p1 p1)) (inverse S (m v v) o vv)
      = m p1 (m p1 (m v v)) by inverse S (m p1 (m p1 (m v v))) (m (m p1 p1) (m v v)) (ring_mul_assoc R p1 p1 (m v v))
      = m (m p1 v) (m p1 v) by cring_mul_interchange R (ef_commutative K) p1 p1 v v
      = m (snd P') (snd P') by refl m (inverse S (snd P') (m p1 v) y') (inverse S (snd P') (m p1 v) y') ∎

{` Moving the configuration by a loop of 𝔼² that preserves the x-axis. `}
def pl_object_path_of_map (K : EuclideanField) (ℓ : Id (EuclideanSpace K) (standard_plane K) (standard_plane K))
  (f : (Fin 2 → ef_carrier K) → Fin 2 → ef_carrier K)
  (hτ : (X : Fin 2 → ef_carrier K) → Id (Fin 2 → ef_carrier K) (plane_point_transport K ℓ X) (f X))
  (hax : (X : Fin 2 → ef_carrier K) → Id PropTypes (x_axis K X) (x_axis K (f X)))
  (P : Fin 2 → ef_carrier K)
  : Id (PLObject K) (pl_object K P) (pl_object K (f P))
  ≔ let F ≔ Fin 2 → ef_carrier K in
    let Pt ≔ refl (euclidean_points K) ℓ in let τ ≔ plane_point_transport K ℓ in
    (ℓ,
     (x ⤇
        let q : Id F (f x.0) x.1 ≔ concat F (f x.0) (τ x.0) x.1 (inverse F (τ x.0) (f x.0) (hτ x.0)) (type_pathover_transport F F Pt x.0 x.1 x.2) in
        proposition_extensionality (single_pred K (standard_plane K) P x.0) (single_pred K (standard_plane K) (f P) x.1)
          (e0 ↦ concat F x.1 (f x.0) (f P) (inverse F (f x.0) x.1 q) (refl f e0))
          (e1 ↦ plane_point_transport_injective K ℓ x.0 P
            (concat F (τ x.0) (f x.0) (τ P) (hτ x.0)
              (concat F (f x.0) x.1 (τ P) q (concat F x.1 (f P) (τ P) e1 (inverse F (τ P) (f P) (hτ P)))))),
      x ⤇
        let q : Id F (f x.0) x.1 ≔ concat F (f x.0) (τ x.0) x.1 (inverse F (τ x.0) (f x.0) (hτ x.0)) (type_pathover_transport F F Pt x.0 x.1 x.2) in
        concat PropTypes (x_axis K x.0) (x_axis K (f x.0)) (x_axis K x.1) (hax x.0) (refl (x_axis K) q)))

{` Translation by v along the x-axis. `}
def pl_translation (K : EuclideanField) (t : ef_carrier K) (P : Fin 2 → ef_carrier K)
  : Id (PLObject K) (pl_object K P) (pl_object K (standard_vector_space (K .field) 2 .add P (plane_vec K t (K .field .fst .zero))))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in
    let v ≔ plane_vec K t (R .zero) in
    pl_object_path_of_map K
      (refl ((E ↦ euclidean_space_dim_forget K 2 E) : EuclideanSpaceDim K 2 → EuclideanSpace K) (euclidean_translation K 2 v))
      (X ↦ standard_vector_space (K .field) 2 .add X v)
      (X ↦ euclidean_translation_act K 2 v X)
      (X ↦ inverse PropTypes (x_axis K (standard_vector_space (K .field) 2 .add X v)) (x_axis K X)
         (refl ((y ↦ (Id S y (R .zero), ring_set R y (R .zero))) : S → PropTypes) (R .add_laws .unit_right (X fin_two_second))))
      P

{` The reflection in the x-axis, (x, y) ↦ (x, -y). `}
def second_coordinate_negation (S : Type) (neg : S → S) (x : Fin 2 → S) : Fin 2 → S
  ≔ [ inl. _ ↦ x fin_two_first | inr. _ ↦ neg (x fin_two_second) ]

def second_coordinate_negation_isometry (K : EuclideanField)
  : LinearIsometry K (standard_inner_product_space K 2) (standard_inner_product_space K 2)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let V ≔ standard_module R 2 in
    let G ≔ ring_additive_group R in
    let ng ≔ second_coordinate_negation S (R .neg) in
    ((quasi_inverse_equiv (Fin 2 → S) (Fin 2 → S) ng ng
        (x ↦ fin_two_funext S (ng (ng x)) x (refl (x fin_two_first)) (ag_inv_inv G (x fin_two_second)))
        (x ↦ fin_two_funext S (ng (ng x)) x (refl (x fin_two_first)) (ag_inv_inv G (x fin_two_second))),
      (x y ↦ fin_two_funext S (ng (V .add x y)) (V .add (ng x) (ng y))
         (refl (R .add (x fin_two_first) (y fin_two_first)))
         (ring_neg_add R (x fin_two_second) (y fin_two_second)),
       a x ↦ fin_two_funext S (ng (V .smul a x)) (V .smul a (ng x))
         (refl (R .mul a (x fin_two_first)))
         (inverse S (R .mul a (R .neg (x fin_two_second))) (R .neg (R .mul a (x fin_two_second)))
            (ring_mul_neg_right R a (x fin_two_second))))),
     x y ↦ refl ((t ↦ R .add (R .add (R .zero) (R .mul (x fin_two_first) (y fin_two_first))) t) : S → S)
       (ring_neg_neg_mul R (x fin_two_second) (y fin_two_second)))

def pl_reflection_loop (K : EuclideanField) : Id (EuclideanSpace K) (standard_plane K) (standard_plane K)
  ≔ refl (point_object_map K 2) (orthogonal_symmetry K 2 (second_coordinate_negation_isometry K)) .fst

def pl_reflection_transport (K : EuclideanField) (X : Fin 2 → ef_carrier K)
  : Id (Fin 2 → ef_carrier K) (plane_point_transport K (pl_reflection_loop K) X)
      (second_coordinate_negation (ef_carrier K) (K .field .fst .neg) X)
  ≔ refl (second_coordinate_negation (ef_carrier K) (K .field .fst .neg) X)

def pl_reflection (K : EuclideanField) (P : Fin 2 → ef_carrier K)
  : Id (PLObject K) (pl_object K P) (pl_object K (second_coordinate_negation (ef_carrier K) (K .field .fst .neg) P))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let G ≔ ring_additive_group R in
    let ng ≔ second_coordinate_negation S (R .neg) in
    pl_object_path_of_map K (pl_reflection_loop K) ng (pl_reflection_transport K)
      (X ↦ proposition_extensionality (x_axis K X) (x_axis K (ng X))
         (h ↦ concat S (R .neg (X fin_two_second)) (R .neg (R .zero)) (R .zero) (refl (R .neg) h) (ag_inv_unit G))
         (h ↦ calc
            X fin_two_second = R .neg (R .neg (X fin_two_second)) by inverse S (R .neg (R .neg (X fin_two_second))) (X fin_two_second) (ag_inv_inv G (X fin_two_second))
            = R .neg (R .zero) by refl (R .neg) h
            = R .zero by ag_inv_unit G ∎))
      P

{` Same distance gives equal configurations: if y' = y or y' = -y. `}
def pl_shift_point (K : EuclideanField) (P P' : Fin 2 → ef_carrier K)
  : Id (ef_carrier K)
      (standard_vector_space (K .field) 2 .add P
        (plane_vec K (K .field .fst .add (P' fin_two_first) (K .field .fst .neg (P fin_two_first))) (K .field .fst .zero)) fin_two_first)
      (P' fin_two_first)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let x ≔ P fin_two_first in let x' ≔ P' fin_two_first in
    calc
      R .add x (R .add x' (R .neg x)) = R .add x (R .add (R .neg x) x') by refl (R .add x) (ring_add_comm R x' (R .neg x))
      = R .add (R .add x (R .neg x)) x' by ring_add_assoc R x (R .neg x) x'
      = R .add (R .zero) x' by refl ((t ↦ R .add t x') : S → S) (R .add_laws .inv_right x)
      = x' by R .add_laws .unit_left x' ∎

def pl_config_path (K : EuclideanField) (P P' : Fin 2 → ef_carrier K)
  (h : Sum (Id (ef_carrier K) (P' fin_two_second) (P fin_two_second))
           (Id (ef_carrier K) (P' fin_two_second) (K .field .fst .neg (P fin_two_second))))
  : Id (Configuration K Bool (_ ↦ propositions_settype)) (pl_config K P) (pl_config K P')
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let F ≔ Fin 2 → S in
    let V ≔ standard_vector_space (K .field) 2 in
    let t ≔ R .add (P' fin_two_first) (R .neg (P fin_two_first)) in
    let Q ≔ V .add P (plane_vec K t (R .zero)) in
    let ng ≔ second_coordinate_negation S (R .neg) in
    let tr ≔ pl_translation K t P in
    let qy : Id S (Q fin_two_second) (P fin_two_second) ≔ R .add_laws .unit_right (P fin_two_second) in
    refl (pl_to_config K)
      (match h [
       | inl. e ↦
         concat (PLObject K) (pl_object K P) (pl_object K Q) (pl_object K P') tr
           (refl (pl_object K) (fin_two_funext S Q P' (pl_shift_point K P P') (concat S (Q fin_two_second) (P fin_two_second) (P' fin_two_second) qy (inverse S (P' fin_two_second) (P fin_two_second) e))))
       | inr. e ↦
         concat (PLObject K) (pl_object K P) (pl_object K Q) (pl_object K P') tr
           (concat (PLObject K) (pl_object K Q) (pl_object K (ng Q)) (pl_object K P') (pl_reflection K Q)
             (refl (pl_object K) (fin_two_funext S (ng Q) P' (pl_shift_point K P P')
               (concat S (R .neg (Q fin_two_second)) (R .neg (P fin_two_second)) (P' fin_two_second) (refl (R .neg) qy)
                 (inverse S (P' fin_two_second) (R .neg (P fin_two_second)) e))))) ])
