export "1433-geometric-objects"

{` Chapter 14, exercise (geometry.tex 251-256): for a point P of a Euclidean
   space E of dimension n, the subset {P} given by the predicate Q ↦ (Q = P)
   (materials M = Prop, a set) has symmetry group isomorphic to O(n).

   For E = 𝔼ⁿ and P = 0 the isomorphism is explicit: V ↦ ((V, P_V), {0_V})
   is a pointed equivalence from OS_n to the component of (𝔼ⁿ, {0}), because
   every object in that component is a singleton {P} (a proposition) and
   pointed torsors (T, t) are contractible. For general (E, P) the object is
   merely equal to (𝔼ⁿ, {0}), so the statement holds merely (an
   isomorphism of automorphism groups at merely equal points is only merely
   given; the type of identifications is what the book's "isomorphic"
   asserts, as a mere proposition). `}

def propositions_settype : SetTypes ≔ (PropTypes, propositions_set)

{` Pointed torsors are contractible: (T, t) = (P_G, e) via the orbit map
   g ↦ g · t, an isomorphism of G-sets P_G ≅ T sending e to t. `}
def torsor_orbit_iso (G : AbstractGroup) (T : AbstractTorsors G) (t : agset_carrier G (T .fst))
  : AbstractGSetIso G (agset_principal G) (T .fst)
  ≔ let X ≔ T .fst in let Pt ≔ agset_carrier G X in let S ≔ G .carrier in
    let f : S → Pt ≔ g ↦ agset_act G X g t in
    ((f, Q ↦ native_contraction (Σ S (v ↦ Id Pt (f v) Q)) (abstract_torsor_difference_contractible G X (T .snd) t Q)),
     s x ↦ agset_act_mul G X s x t)

{` The path (P_G, e) = (T, t) from any identification p : P_G = T whose
   associated isomorphism is the orbit map (p is a variable here, which keeps
   type checking cheap). `}
def pointed_torsor_path_of (G : AbstractGroup) (T : AbstractTorsors G) (t : agset_carrier G (T .fst))
  (p : Id (AbstractGSet G) (agset_principal G) (T .fst))
  (sec : Id (AbstractGSetIso G (agset_principal G) (T .fst)) (agset_path_to_iso G (agset_principal G) (T .fst) p)
           (torsor_orbit_iso G T t))
  : Id (Σ (AbstractTorsors G) (T ↦ agset_carrier G (T .fst))) (abstract_principal_torsor G, G .unit) (T, t)
  ≔ let Tor ≔ AbstractTorsors G in
    let fam ≔ (T : Tor) ↦ agset_carrier G (T .fst) in
    let P0 ≔ abstract_principal_torsor G in
    let φ ≔ torsor_orbit_iso G T t in
    let tp : Id Tor P0 T
      ≔ (p, prop_family_pathover (AbstractGSet G) (X ↦ Mere (Id (AbstractGSet G) (agset_principal G) X))
             (X ↦ mere_isprop (Id (AbstractGSet G) (agset_principal G) X)) (agset_principal G) (T .fst) p
             (P0 .snd) (T .snd)) in
    let q : Id (fam T) (agset_path_to_iso G (agset_principal G) (T .fst) p .fst .map (G .unit)) t
      ≔ concat (fam T) (agset_path_to_iso G (agset_principal G) (T .fst) p .fst .map (G .unit)) (φ .fst .map (G .unit)) t
          (refl ((ψ ↦ ψ .fst .map (G .unit)) : AbstractGSetIso G (agset_principal G) (T .fst) → fam T) sec)
          (agset_act_unit G (T .fst) t) in
    (tp, pathover_of_eq Tor fam P0 T tp (G .unit) t q)

def pointed_torsors_contractible (G : AbstractGroup)
  : BookIsContr (Σ (AbstractTorsors G) (T ↦ agset_carrier G (T .fst)))
  ≔ (center ≔ (abstract_principal_torsor G, G .unit),
     contract ≔ u ↦
       pointed_torsor_path_of G (u .fst) (u .snd)
         (agset_path_from_iso G (agset_principal G) (u .fst .fst) (torsor_orbit_iso G (u .fst) (u .snd)))
         (agset_path_from_iso_section G (agset_principal G) (u .fst .fst) (torsor_orbit_iso G (u .fst) (u .snd))))

{` The singleton {P}: Q ↦ (Q = P). `}
def single_pred (K : EuclideanField) (E : EuclideanSpace K) (P : euclidean_points K E) : euclidean_points K E → PropTypes
  ≔ Q ↦ (Id (euclidean_points K E) Q P, euclidean_points_set K E Q P)

def single_pred_injective (K : EuclideanField) (E : EuclideanSpace K) (P P' : euclidean_points K E)
  (e : Id (euclidean_points K E → PropTypes) (single_pred K E P) (single_pred K E P'))
  : Id (euclidean_points K E) P P'
  ≔ let Pt ≔ euclidean_points K E in
    transport PropTypes (X ↦ X .fst) (single_pred K E P P) (single_pred K E P' P)
      (happly Pt (_ ↦ PropTypes) (single_pred K E P) (single_pred K E P') e P) (refl P)

def IsSingletonObject (K : EuclideanField) (x : EuclideanObject K propositions_settype) : Type
  ≔ Σ (euclidean_points K (x .fst)) (P ↦ Id (euclidean_points K (x .fst) → PropTypes) (x .snd) (single_pred K (x .fst) P))

def is_singleton_object_prop (K : EuclideanField) (x : EuclideanObject K propositions_settype)
  : isProp (IsSingletonObject K x)
  ≔ let E ≔ x .fst in let Pt ≔ euclidean_points K E in let F ≔ Pt → PropTypes in
    u v ↦
      subtype_equal Pt (P ↦ Id F (x .snd) (single_pred K E P))
        (P ↦ pi_set Pt (_ ↦ PropTypes) (_ ↦ propositions_set) (x .snd) (single_pred K E P)) u v
        (single_pred_injective K E (u .fst) (v .fst)
          (concat F (single_pred K E (u .fst)) (x .snd) (single_pred K E (v .fst))
            (inverse F (x .snd) (single_pred K E (u .fst)) (u .snd)) (v .snd)))

{` V ↦ ((V, P_V), {0_V}). `}
def point_object_map (K : EuclideanField) (n : Nat) (V : InnerProductSpaceDim K n) : EuclideanObject K propositions_settype
  ≔ let E : EuclideanSpace K ≔ (V .fst, abstract_principal_torsor (ip_additive_group K (V .fst))) in
    (E, single_pred K E (V .fst .space .zero))

{` The origin predicate {0} on 𝔼ⁿ, and o₀ = (𝔼ⁿ, {0}). `}
def origin_pred (K : EuclideanField) (n : Nat) : (Fin n → ef_carrier K) → PropTypes
  ≔ single_pred K (euclidean_space_dim_forget K n (euclidean_standard K n)) (standard_vector_space (K .field) n .zero)

def origin_object (K : EuclideanField) (n : Nat) : EuclideanObject K propositions_settype
  ≔ standard_object K propositions_settype n (origin_pred K n)

def origin_object_is_point_object (K : EuclideanField) (n : Nat)
  : Id (EuclideanObject K propositions_settype) (point_object_map K n (standard_inner_product_space_dim K n))
      (origin_object K n)
  ≔ refl (origin_object K n)

def origin_component_singleton (K : EuclideanField) (n : Nat)
  (c : NativeComponent (EuclideanObject K propositions_settype) (origin_object K n)) : IsSingletonObject K (c .fst)
  ≔ let Obj ≔ EuclideanObject K propositions_settype in let o0 ≔ origin_object K n in
    mere_rec (Id Obj o0 (c .fst)) (IsSingletonObject K (c .fst)) (is_singleton_object_prop K (c .fst))
      (p ↦ transport Obj (IsSingletonObject K) o0 (c .fst) p
             (standard_vector_space (K .field) n .zero, refl (origin_pred K n)))
      (c .snd)

def point_object_component (K : EuclideanField) (n : Nat) (V : InnerProductSpaceDim K n)
  : NativeComponent (EuclideanObject K propositions_settype) (origin_object K n)
  ≔ let Obj ≔ EuclideanObject K propositions_settype in let o0 ≔ origin_object K n in
    let OSn ≔ InnerProductSpaceDim K n in let std ≔ standard_inner_product_space_dim K n in
    (point_object_map K n V,
     mere_rec (Id OSn V std) (Mere (Id Obj o0 (point_object_map K n V))) (mere_isprop (Id Obj o0 (point_object_map K n V)))
       (p ↦ mere (Id Obj o0 (point_object_map K n V)) (refl (point_object_map K n) (inverse OSn V std p)))
       (gram_schmidt_theorem K n V))

def point_object_component_inverse (K : EuclideanField) (n : Nat)
  (c : NativeComponent (EuclideanObject K propositions_settype) (origin_object K n)) : InnerProductSpaceDim K n
  ≔ (c .fst .fst .fst, object_component_dimension K propositions_settype n (origin_pred K n) c)

