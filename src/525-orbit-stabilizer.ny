export "521-orbits-set-truncation"
export "523-free-elements"
export "524-fixed-elements"

{` Chapter 5, sec:orbit-stabilizer-theorem: the G_x-set G̃_x
   (def:Gx-action-on-G, xca:Gx-action-on-G), the Orbit–Stabilizer
   construction (con:orbit-stabilizer), G̃_x is free
   (cor:action-subgrp-free), cosets (lem:cosets-Gx.g) and
   con:preLagrange. `}

{` def:Gx-action-on-G. G̃_x ≔ P_G ∘ Bi_x, the restriction of the principal
   G-set along i_x. `}
def stabilizer_tilde_gset (G : Group) (X : GSet G) (x : gset_underlying G X) : GSet (stabilizer_group G X x)
  ≔ gset_restrict (stabilizer_group G X x) G (stabilizer_inclusion G X x) (principal_gset G)

{` Footnote of def:Gx-action-on-G: G̃_x(z, y, !) ≡ (sh_G = z). `}
def stabilizer_tilde_gset_value (G : Group) (X : GSet G) (x : gset_underlying G X)
  (u : BG (stabilizer_group G X x) .carrier)
  : Id Type (stabilizer_tilde_gset G X x u .fst) (Id (BG G .carrier) (shape G) (u .fst .fst))
  ≔ refl (Id (BG G .carrier) (shape G) (u .fst .fst))

{` "The underlying set of G̃_x is USym G" (by definition). `}
def stabilizer_tilde_gset_underlying (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Id Type (gset_underlying (stabilizer_group G X x) (stabilizer_tilde_gset G X x)) (USym G)
  ≔ refl (USym G)

{` xca:Gx-action-on-G. For s : u = v in BG_x with first component s₁ and
   g : sh_G = u₁, s ·_{G̃_x} g = s₁ g (path composition, g first), by
   definition. `}
def stabilizer_tilde_gset_act (G : Group) (X : GSet G) (x : gset_underlying G X)
  (u v : BG (stabilizer_group G X x) .carrier) (s : Id (BG (stabilizer_group G X x) .carrier) u v)
  (g : Id (BG G .carrier) (shape G) (u .fst .fst))
  : Id (Id (BG G .carrier) (shape G) (v .fst .fst))
      (gset_act (stabilizer_group G X x) (stabilizer_tilde_gset G X x) u v s g)
      (concat (BG G .carrier) (shape G) (u .fst .fst) (v .fst .fst) g (s .fst .fst))
  ≔ refl (concat (BG G .carrier) (shape G) (u .fst .fst) (v .fst .fst) g (s .fst .fst))

{` The exercise's case: s from the base point (sh_G, x, !) and g : USym G. `}
def stabilizer_tilde_gset_act_base (G : Group) (X : GSet G) (x : gset_underlying G X)
  (v : BG (stabilizer_group G X x) .carrier)
  (s : Id (BG (stabilizer_group G X x) .carrier) (BG (stabilizer_group G X x) .point) v) (g : USym G)
  : Id (Id (BG G .carrier) (shape G) (v .fst .fst))
      (gset_act (stabilizer_group G X x) (stabilizer_tilde_gset G X x) (BG (stabilizer_group G X x) .point) v s g)
      (concat (BG G .carrier) (shape G) (shape G) (v .fst .fst) g (s .fst .fst))
  ≔ refl (concat (BG G .carrier) (shape G) (shape G) (v .fst .fst) g (s .fst .fst))

{` On symmetries s : USym(G_x) this is left multiplication by s₁ in USym G. `}
def stabilizer_tilde_gset_usym_act (G : Group) (X : GSet G) (x : gset_underlying G X)
  (s : USym (stabilizer_group G X x)) (g : USym G)
  : Id (USym G) (gset_usym_act (stabilizer_group G X x) (stabilizer_tilde_gset G X x) s g)
      (usym_mul G (s .fst .fst) g)
  ≔ refl (usym_mul G (s .fst .fst) g)

{` con:orbit-stabilizer. (G̃_x)_{hG_x} ≡ Σ_{u : BG_x} (sh_G = u₁) is by
   definition the fiber of Bi_x at sh_G; reassociating to
   Σ_{z} Σ_{y : X(z)} ‖(sh_G, x) = (z, y)‖ × (sh_G = z) and contracting
   away z gives Σ_{y : X(sh_G)} ([x] = [y]) ≡ G · x. `}
def orbit_stabilizer_action_type_fiber (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Id Type (ActionType (stabilizer_group G X x) (stabilizer_tilde_gset G X x)) (StabilizerInclusionFiber G X x)
  ≔ refl (StabilizerInclusionFiber G X x)

def orbit_stabilizer_equiv (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Equiv (ActionType (stabilizer_group G X x) (stabilizer_tilde_gset G X x)) (OrbitUnderlying G X x)
  ≔ stabilizer_inclusion_fiber_equiv G X x

{` The inverse sends y : G · x to ((sh_G, y), !) with the path refl. `}
def orbit_stabilizer_inverse_point (G : Group) (X : GSet G) (x : gset_underlying G X) (y : OrbitUnderlying G X x)
  : Id (ActionType G X)
      (equiv_inverse_map (ActionType (stabilizer_group G X x) (stabilizer_tilde_gset G X x)) (OrbitUnderlying G X x)
        (orbit_stabilizer_equiv G X x) y .fst .fst)
      (shape G, y .fst)
  ≔ refl ((shape G, y .fst) : ActionType G X)

{` "(G̃_x)_{hG_x} is a set" (text after con:orbit-stabilizer and
   ft:action-type-tildeGx-set). `}
def stabilizer_tilde_action_type_set (G : Group) (X : GSet G) (x : gset_underlying G X)
  : isSet (ActionType (stabilizer_group G X x) (stabilizer_tilde_gset G X x))
  ≔ let A ≔ ActionType (stabilizer_group G X x) (stabilizer_tilde_gset G X x) in
    hlevel_two_to_set A
      (hlevel_equiv (suc. (suc. zero.)) (OrbitUnderlying G X x) A
        (canonical_inverse_equiv A (OrbitUnderlying G X x) (orbit_stabilizer_equiv G X x))
        (set_to_hlevel_two (OrbitUnderlying G X x) (orbit_underlying_set G X x)))

{` cor:action-subgrp-free. The G_x-set G̃_x is free (lem:X_hG-set-iff-Xfree). `}
def stabilizer_tilde_free (G : Group) (X : GSet G) (x : gset_underlying G X)
  : IsFreeGSet (stabilizer_group G X x) (stabilizer_tilde_gset G X x)
  ≔ action_type_set_free (stabilizer_group G X x) (stabilizer_tilde_gset G X x)
      (stabilizer_tilde_action_type_set G X x)

{` lem:cosets-Gx.g. For g : USym G, (- ·_{G̃_x} g) is an equivalence from
   USym(G_x) to the orbit G_x ·_{G̃_x} g (lem:free-pt-char for G_x and G̃_x). `}
def stabilizer_coset_equiv (G : Group) (X : GSet G) (x : gset_underlying G X) (g : USym G)
  : BookEquiv (USym (stabilizer_group G X x)) (OrbitUnderlying (stabilizer_group G X x) (stabilizer_tilde_gset G X x) g)
  ≔ free_orbit_action_equiv (stabilizer_group G X x) (stabilizer_tilde_gset G X x) g (stabilizer_tilde_free G X x g)

def stabilizer_coset_equiv_map (G : Group) (X : GSet G) (x : gset_underlying G X) (g : USym G)
  (s : USym (stabilizer_group G X x))
  : Id (USym G) (stabilizer_coset_equiv G X x g .map s .fst) (usym_mul G (s .fst .fst) g)
  ≔ refl (usym_mul G (s .fst .fst) g)

{` con:preLagrange. For a subgroup (X, pt), the composite
   X(sh_G) ≃ G · pt (fst⁻¹, X transitive) ≃ (G̃_pt)_{hG_pt} (Orbit–Stabilizer)
   ≃ G̃_pt / G_pt ([-]_0, the action type is a set) is the equivalence
   [-]_pt. `}
def transitive_orbit_underlying_equiv (G : Group) (X : GSet G) (x : gset_underlying G X) (t : IsTransitive G X)
  : Equiv (OrbitUnderlying G X x) (gset_underlying G X)
  ≔ let O ≔ Orbits G X in
    let h ≔ transitive_orbits_contractible G X t in
    contractible_fiber_projection (gset_underlying G X)
      (y ↦ Id O (orbit_of_point G X x) (orbit_of_point G X y))
      (y ↦ let c ≔ concat O (orbit_of_point G X x) (h .center) (orbit_of_point G X y)
              (inverse O (h .center) (orbit_of_point G X x) (h .contract (orbit_of_point G X x)))
              (h .contract (orbit_of_point G X y)) in
        (c, q ↦ orbits_set G X (orbit_of_point G X x) (orbit_of_point G X y) q c))

def subgroup_coset_equiv (G : Group) (S : Subgroups G)
  : Equiv (gset_underlying G (S .gset))
      (Orbits (stabilizer_group G (S .gset) (S .point)) (stabilizer_tilde_gset G (S .gset) (S .point)))
  ≔ let X ≔ S .gset in
    let pt ≔ S .point in
    let H ≔ stabilizer_group G X pt in
    let Y ≔ stabilizer_tilde_gset G X pt in
    let A ≔ ActionType H Y in
    compose_equiv (gset_underlying G X) (OrbitUnderlying G X pt) (Orbits H Y)
      (canonical_inverse_equiv (OrbitUnderlying G X pt) (gset_underlying G X)
        (transitive_orbit_underlying_equiv G X pt (S .transitive)))
      (compose_equiv (OrbitUnderlying G X pt) A (Orbits H Y)
        (canonical_inverse_equiv A (OrbitUnderlying G X pt) (orbit_stabilizer_equiv G X pt))
        (native_equivalence A (Orbits H Y)
          (orbit_map H Y, action_type_set_orbit_map_is_equiv H Y (stabilizer_tilde_action_type_set G X pt))))

{` [x]_pt ≔ [o(fst⁻¹(x))]_0, by definition. `}
def subgroup_coset_class (G : Group) (S : Subgroups G) (x : gset_underlying G (S .gset))
  : Orbits (stabilizer_group G (S .gset) (S .point)) (stabilizer_tilde_gset G (S .gset) (S .point))
  ≔ subgroup_coset_equiv G S .map x

def subgroup_coset_class_definition (G : Group) (S : Subgroups G) (x : gset_underlying G (S .gset))
  : Id (Orbits (stabilizer_group G (S .gset) (S .point)) (stabilizer_tilde_gset G (S .gset) (S .point)))
      (subgroup_coset_class G S x)
      (orbit_map (stabilizer_group G (S .gset) (S .point)) (stabilizer_tilde_gset G (S .gset) (S .point))
        (equiv_inverse_map (ActionType (stabilizer_group G (S .gset) (S .point))
            (stabilizer_tilde_gset G (S .gset) (S .point)))
          (OrbitUnderlying G (S .gset) (S .point)) (orbit_stabilizer_equiv G (S .gset) (S .point))
          (equiv_inverse_map (OrbitUnderlying G (S .gset) (S .point)) (gset_underlying G (S .gset))
            (transitive_orbit_underlying_equiv G (S .gset) (S .point) (S .transitive)) x)))
  ≔ refl (subgroup_coset_class G S x)
