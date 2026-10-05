export "507-subgroups-monos-equiv"

{` Chapter 5: the subgroup associated with a stabilizer (rem:subgrp-is-stabsubgr),
   the identification of underlying groups along E (text before
   def:triv-proper-Mono) and, for (X, pt) : Sub(G), G_pt is the underlying group
   of (X, pt) (def:orbit-stabilizer). `}

{` "The underlying groups of an element of Mono(G) and of its image under E
   can be identified." `}
def mono_subgroup_group_path (G : Group) (m : GroupMonos G)
  : Id Group (subgroup_group G (mono_to_subgroup G m)) (m .fst)
  ≔ map_path (GroupMonos G) Group (n ↦ n .fst) (subgroup_to_mono G (mono_to_subgroup G m)) m
      (mono_subgroup_roundtrip G m)

{` The subgroup (X_[x], x) of the orbit through x. `}
def orbit_subgroup (G : Group) (X : GSet G) (x : gset_underlying G X) : Subgroups G
  ≔ (orbit_gset G X (shape G, x), (x, mere (Id (ActionType G X) (shape G, x) (shape G, x)) (refl (shape G, x))),
     orbit_gset_transitive G X (shape G, x))

{` The fiber of i_x : BG_x → BG at z is X_[x](z). `}
def stabilizer_fiber_map (G : Group) (X : GSet G) (x : gset_underlying G X) (z : BG G .carrier)
  (u : BookFiber (NativeComponent (ActionType G X) (shape G, x)) (BG G .carrier) (c ↦ c .fst .fst) z)
  : orbit_gset G X (shape G, x) z .fst
  ≔ let B ≔ BG G .carrier in
    let T ≔ ActionType G X in
    let z' ≔ u .fst .fst .fst in
    let y ≔ u .fst .fst .snd in
    let q' ≔ inverse B z z' (u .snd) in
    let y' ≔ gset_act G X z' z q' y in
    (y', mere_rec (Id T (shape G, x) (z', y)) (Mere (Id T (shape G, x) (z, y'))) (mere_isprop (Id T (shape G, x) (z, y')))
           (r ↦ mere (Id T (shape G, x) (z, y'))
             (concat T (shape G, x) (z', y) (z, y') r (action_type_path G X z' z y y' q' (refl y'))))
           (u .fst .snd))

def stabilizer_fiber_inv (G : Group) (X : GSet G) (x : gset_underlying G X) (z : BG G .carrier)
  (v : orbit_gset G X (shape G, x) z .fst)
  : BookFiber (NativeComponent (ActionType G X) (shape G, x)) (BG G .carrier) (c ↦ c .fst .fst) z
  ≔ (((z, v .fst), v .snd), refl z)

def stabilizer_fiber_section (G : Group) (X : GSet G) (x : gset_underlying G X) (z : BG G .carrier)
  (v : orbit_gset G X (shape G, x) z .fst)
  : Id (orbit_gset G X (shape G, x) z .fst) (stabilizer_fiber_map G X x z (stabilizer_fiber_inv G X x z v)) v
  ≔ let T ≔ ActionType G X in
    subtype_equal (X z .fst) (y ↦ Mere (Id T (shape G, x) (z, y))) (y ↦ mere_isprop (Id T (shape G, x) (z, y)))
      (stabilizer_fiber_map G X x z (stabilizer_fiber_inv G X x z v)) v
      (action_type_fiber_section G X z (v .fst))

def stabilizer_fiber_retraction (G : Group) (X : GSet G) (x : gset_underlying G X) (z : BG G .carrier)
  (u : BookFiber (NativeComponent (ActionType G X) (shape G, x)) (BG G .carrier) (c ↦ c .fst .fst) z)
  : Id (BookFiber (NativeComponent (ActionType G X) (shape G, x)) (BG G .carrier) (c ↦ c .fst .fst) z)
      (stabilizer_fiber_inv G X x z (stabilizer_fiber_map G X x z u)) u
  ≔ let B ≔ BG G .carrier in
    let T ≔ ActionType G X in
    let C ≔ NativeComponent T (shape G, x) in
    let F ≔ BookFiber C B (c ↦ c .fst .fst) z in
    J B z
      (z' q ↦ (y : X z' .fst) (m : Mere (Id T (shape G, x) (z', y))) →
        Id F (stabilizer_fiber_inv G X x z (stabilizer_fiber_map G X x z (((z', y), m), q))) (((z', y), m), q))
      (y m ↦ map_path (orbit_gset G X (shape G, x) z .fst) F (stabilizer_fiber_inv G X x z)
        (stabilizer_fiber_map G X x z (((z, y), m), refl z)) (y, m)
        (stabilizer_fiber_section G X x z (y, m)))
      (u .fst .fst .fst) (u .snd) (u .fst .fst .snd) (u .fst .snd)

def stabilizer_fiber_equiv (G : Group) (X : GSet G) (x : gset_underlying G X) (z : BG G .carrier)
  : Equiv (BookFiber (NativeComponent (ActionType G X) (shape G, x)) (BG G .carrier) (c ↦ c .fst .fst) z)
      (orbit_gset G X (shape G, x) z .fst)
  ≔ quasi_inverse_equiv
      (BookFiber (NativeComponent (ActionType G X) (shape G, x)) (BG G .carrier) (c ↦ c .fst .fst) z)
      (orbit_gset G X (shape G, x) z .fst)
      (stabilizer_fiber_map G X x z) (stabilizer_fiber_inv G X x z)
      (stabilizer_fiber_retraction G X x z) (stabilizer_fiber_section G X x z)

{` rem:subgrp-is-stabsubgr. E(G_x, i_x) = (X_[x], x). `}
def stabilizer_subgroup_path (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Id (Subgroups G) (mono_to_subgroup G (stabilizer_mono G X x)) (orbit_subgroup G X x)
  ≔ subgroup_path G (mono_to_subgroup G (stabilizer_mono G X x)) (orbit_subgroup G X x)
      (pointed_gset_path G (mono_gset G (stabilizer_mono G X x)) (orbit_gset G X (shape G, x))
        (component_point (ActionType G X) (shape G, x), refl (shape G)) (orbit_subgroup G X x .point)
        (z ↦ stabilizer_fiber_equiv G X x z)
        (stabilizer_fiber_section G X x (shape G) (orbit_subgroup G X x .point)))

{` rem:subgrp-is-stabsubgr, second sentence: if X is transitive, (X_[x], x) = (X, x). `}
def transitive_orbit_gset_equiv (G : Group) (X : GSet G) (x : gset_underlying G X) (hX : IsTransitive G X)
  (z : BG G .carrier) : Equiv (orbit_gset G X (shape G, x) z .fst) (X z .fst)
  ≔ let T ≔ ActionType G X in
    let c ≔ transitive_action_type_connected G X hX in
    quasi_inverse_equiv (orbit_gset G X (shape G, x) z .fst) (X z .fst)
      (v ↦ v .fst) (y ↦ (y, c .snd (shape G, x) (z, y)))
      (v ↦ subtype_equal (X z .fst) (y ↦ Mere (Id T (shape G, x) (z, y))) (y ↦ mere_isprop (Id T (shape G, x) (z, y)))
        (v .fst, c .snd (shape G, x) (z, v .fst)) v (refl (v .fst)))
      (y ↦ refl y)

def transitive_orbit_subgroup_path (G : Group) (X : GSet G) (x : gset_underlying G X) (hX : IsTransitive G X)
  : Id (Subgroups G) (orbit_subgroup G X x) (X, x, hX)
  ≔ subgroup_path G (orbit_subgroup G X x) (X, x, hX)
      (pointed_gset_path G (orbit_gset G X (shape G, x)) X (orbit_subgroup G X x .point) x
        (z ↦ transitive_orbit_gset_equiv G X x hX z) (refl x))

def transitive_stabilizer_subgroup_path (G : Group) (X : GSet G) (x : gset_underlying G X) (hX : IsTransitive G X)
  : Id (Subgroups G) (mono_to_subgroup G (stabilizer_mono G X x)) (X, x, hX)
  ≔ concat (Subgroups G) (mono_to_subgroup G (stabilizer_mono G X x)) (orbit_subgroup G X x) (X, x, hX)
      (stabilizer_subgroup_path G X x) (transitive_orbit_subgroup_path G X x hX)

{` def:orbit-stabilizer (1), remark: for (X, pt) : Sub(G), (G_pt, i_pt) is the
   monomorphism F(X, pt); in particular G_pt is the underlying group of (X, pt). `}
def subgroup_stabilizer_mono_path (G : Group) (S : Subgroups G)
  : Id (GroupMonos G) (subgroup_to_mono G S) (stabilizer_mono G (S .gset) (S .point))
  ≔ let m ≔ stabilizer_mono G (S .gset) (S .point) in
    concat (GroupMonos G) (subgroup_to_mono G S) (subgroup_to_mono G (mono_to_subgroup G m)) m
      (map_path (Subgroups G) (GroupMonos G) (subgroup_to_mono G) S (mono_to_subgroup G m)
        (inverse (Subgroups G) (mono_to_subgroup G m) S
          (transitive_stabilizer_subgroup_path G (S .gset) (S .point) (S .transitive))))
      (mono_subgroup_roundtrip G m)

def subgroup_stabilizer_group_path (G : Group) (S : Subgroups G)
  : Id Group (subgroup_group G S) (stabilizer_group G (S .gset) (S .point))
  ≔ map_path (GroupMonos G) Group (n ↦ n .fst) (subgroup_to_mono G S) (stabilizer_mono G (S .gset) (S .point))
      (subgroup_stabilizer_mono_path G S)
