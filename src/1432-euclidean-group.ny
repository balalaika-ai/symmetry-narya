export "1431-euclidean-spaces"
export "802-semidirect-symmetries"
export "709-groups-are-abstract-groups"

{` Chapter 14, def:EuclideanGroup and thm:EuclideanGroupSemidirect
   (geometry.tex 168-191). E(n) ≔ mkgroup ES_n pointed at 𝔼ⁿ; connected by
   thm:EuclideanNormalization, a groupoid by lem:EuclideanSpace1Type. Its
   standard action is on the points of 𝔼ⁿ; translations x ↦ x + v of the
   principal torsor are symmetries acting by translation.

   thm:EuclideanGroupSemidirect: with the action V ↦ concr(additive group of
   V) of O(n) (the standard action of O(n) on 𝕍ⁿ composed with the
   forgetful map, taking additive groups), O(n) ⋉ ℝⁿ has classifying type
   Σ_{V : B O(n)} B(concr V) ≡ Σ_{V : OS_n} Torsor_V ≡ ES_n, pointed at
   (𝕍ⁿ, P) ≡ 𝔼ⁿ, by definition (B(concr G) is the type of G-torsors,
   lem:BGbytorsor). So the identity is a group isomorphism. `}

def euclidean_group_connected (K : EuclideanField) (n : Nat) : Connected (EuclideanSpaceDim K n)
  ≔ let A ≔ EuclideanSpaceDim K n in let a ≔ euclidean_standard K n in
    let k : (x : A) → Mere (Id A a x)
      ≔ x ↦ mere_rec (Id A x a) (Mere (Id A a x)) (mere_isprop (Id A a x)) (p ↦ mere (Id A a x) (inverse A x a p))
          (euclidean_normalization K n x) in
    (mere A a, x y ↦ merely_paths_compose native_truncation A a x y (k x) (k y))

def euclidean_group_classifying (K : EuclideanField) (n : Nat) : PointedConnectedGroupoid
  ≔ (EuclideanSpaceDim K n, euclidean_standard K n, euclidean_group_connected K n, euclidean_space_dim_groupoid K n)

{` def:EuclideanGroup. `}
def euclidean_group (K : EuclideanField) (n : Nat) : Group ≔ mkgroup (euclidean_group_classifying K n)

def euclidean_group_classifying_type (K : EuclideanField) (n : Nat)
  : Id Type (BG (euclidean_group K n) .carrier) (EuclideanSpaceDim K n)
  ≔ refl (EuclideanSpaceDim K n)

{` The standard action of E(n): on the points of 𝔼ⁿ. `}
def euclidean_standard_gset (K : EuclideanField) (n : Nat) : GSet (euclidean_group K n)
  ≔ E ↦ (euclidean_points K (euclidean_space_dim_forget K n E), euclidean_points_set K (euclidean_space_dim_forget K n E))

def euclidean_standard_gset_underlying (K : EuclideanField) (n : Nat)
  : Id Type (gset_underlying (euclidean_group K n) (euclidean_standard_gset K n)) (Fin n → ef_carrier K)
  ≔ refl (Fin n → ef_carrier K)

{` Translations: x ↦ x + v is an automorphism of the principal torsor of
   the (abelian) additive group, hence a symmetry of 𝔼ⁿ. `}
def principal_torsor_translation (G : AbstractGroup) (v : G .carrier) : AbstractGSetIso G (agset_principal G) (agset_principal G)
  ≔ (ag_mul_right_equiv G v, s x ↦ inverse (G .carrier) (G .mul s (G .mul x v)) (G .mul (G .mul s x) v) (G .laws .assoc s x v))

def euclidean_translation (K : EuclideanField) (n : Nat) (v : Fin n → ef_carrier K) : USym (euclidean_group K n)
  ≔ let G ≔ ip_additive_group K (standard_inner_product_space K n) in
    let std ≔ standard_inner_product_space_dim K n in
    let p ≔ agset_path_from_iso G (agset_principal G) (agset_principal G) (principal_torsor_translation G v) in
    (refl std,
     (p, prop_family_pathover (AbstractGSet G) (X ↦ Mere (Id (AbstractGSet G) (agset_principal G) X))
           (X ↦ mere_isprop (Id (AbstractGSet G) (agset_principal G) X)) (agset_principal G) (agset_principal G) p
           (abstract_principal_torsor G .snd) (abstract_principal_torsor G .snd)))

{` The translation by v acts on points of 𝔼ⁿ by P ↦ P + v. `}
def euclidean_translation_act (K : EuclideanField) (n : Nat) (v P : Fin n → ef_carrier K)
  : Id (Fin n → ef_carrier K)
      (gset_usym_act (euclidean_group K n) (euclidean_standard_gset K n) (euclidean_translation K n v) P)
      (standard_vector_space (K .field) n .add P v)
  ≔ let G ≔ ip_additive_group K (standard_inner_product_space K n) in
    let f ≔ principal_torsor_translation G v in
    refl ((φ ↦ φ .fst .map P) : AbstractGSetIso G (agset_principal G) (agset_principal G) → Fin n → ef_carrier K)
      (agset_path_from_iso_section G (agset_principal G) (agset_principal G) f)

{` Litmus: a translation is trivial only if v = 0 (so E(n), n ≥ 1, is not
   trivial). `}
def euclidean_translation_trivial (K : EuclideanField) (n : Nat) (v : Fin n → ef_carrier K)
  (h : Id (USym (euclidean_group K n)) (euclidean_translation K n v) (usym_unit (euclidean_group K n)))
  : Id (Fin n → ef_carrier K) v (standard_vector_space (K .field) n .zero)
  ≔ let F ≔ Fin n → ef_carrier K in let G ≔ euclidean_group K n in let X ≔ euclidean_standard_gset K n in
    let A ≔ module_group (K .field .fst) (standard_vector_space (K .field) n) in
    let P ≔ standard_vector_space (K .field) n .zero in
    let q : Id F (A .mul P v) (A .mul P P)
      ≔ calc
          A .mul P v = gset_usym_act G X (euclidean_translation K n v) P
            by inverse F (gset_usym_act G X (euclidean_translation K n v) P) (A .mul P v) (euclidean_translation_act K n v P)
          = gset_usym_act G X (usym_unit G) P by refl ((g ↦ gset_usym_act G X g P) : USym G → F) h
          = P by gset_act_unit G X P
          = A .mul P P by inverse F (A .mul P P) P (A .laws .unit_right P) ∎ in
    ag_cancel_left A P v P q

{` thm:EuclideanGroupSemidirect. The action of O(n): V ↦ concr(V, +). `}
def euclidean_semidirect_action (K : EuclideanField) (n : Nat) : BG (orthogonal_group K n) .carrier → Group
  ≔ V ↦ concr (ip_additive_group K (V .fst))

def euclidean_semidirect_action_shape (K : EuclideanField) (n : Nat)
  : Id AbstractGroup (abstr (euclidean_semidirect_action K n (shape (orthogonal_group K n))))
      (ip_additive_group K (standard_inner_product_space K n))
  ≔ abstr_concr_path (ip_additive_group K (standard_inner_product_space K n))

def euclidean_semidirect_classifying (K : EuclideanField) (n : Nat)
  : Id Pointed (BG (semidirect_product (orthogonal_group K n) (euclidean_semidirect_action K n)))
      (BG (euclidean_group K n))
  ≔ refl (BG (euclidean_group K n))

def euclidean_group_semidirect_iso (K : EuclideanField) (n : Nat)
  : GroupIso (euclidean_group K n) (semidirect_product (orthogonal_group K n) (euclidean_semidirect_action K n))
  ≔ (mkhom (euclidean_group K n) (semidirect_product (orthogonal_group K n) (euclidean_semidirect_action K n))
       (book_pointed_identity (BG (euclidean_group K n))),
     group_hom_id_iso (euclidean_group K n))

def euclidean_group_semidirect (K : EuclideanField) (n : Nat)
  : Id Group (euclidean_group K n) (semidirect_product (orthogonal_group K n) (euclidean_semidirect_action K n))
  ≔ group_path_from_iso (euclidean_group K n) (semidirect_product (orthogonal_group K n) (euclidean_semidirect_action K n))
      (euclidean_group_semidirect_iso K n)
