export "525-orbit-stabilizer"
export "526-lagrange-construction"

{` Chapter 5: the counting version of Lagrange's theorem, xca:lagrange
   (from con:lagrange) and xca:lagrange2 (from lem:splitting into orbits,
   lem:cosets-Gx.g and con:preLagrange). The choice functions are obtained
   by finite choice (module 34) over the finite set X(sh_G), resp. the
   finite set of cosets; no classical principle is used. `}

{` USym H ≃ {g : USym G | g · pt = pt} for the underlying group H of (X, pt). `}
def subgroup_usym_fixing_equiv (G : Group) (S : Subgroups G)
  : Equiv (USym (subgroup_group G S))
      (Σ (USym G) (g ↦ Id (gset_underlying G (S .gset)) (gset_usym_act G (S .gset) g (S .point)) (S .point)))
  ≔ action_type_path_equiv G (S .gset) (shape G, S .point) (shape G, S .point)

{` xca:lagrange, first claim: H is finite (a decidable subset of USym G). `}
def lagrange_subgroup_finite (G : Group) (S : Subgroups G) (hG : IsFiniteGroup G) (hX : IsFiniteGSet G (S .gset))
  : IsFiniteGroup (subgroup_group G S)
  ≔ let X ≔ S .gset in
    let Xs ≔ gset_underlying G X in
    let pt ≔ S .point in
    finite_of_equiv (USym (subgroup_group G S)) (Σ (USym G) (g ↦ Id Xs (gset_usym_act G X g pt) pt))
      (subgroup_usym_fixing_equiv G S)
      (finite_decidable_subset (USym G) hG (g ↦ Id Xs (gset_usym_act G X g pt) pt)
        (g ↦ gset_underlying_set G X (gset_usym_act G X g pt) pt)
        (g ↦ finite_decidable_equality Xs hX (gset_usym_act G X g pt) pt))

{` For a transitive finite G-set the premiss of con:lagrange holds merely:
   each [x] = [pt] gives ∃_g (g · x = pt), and finite choice over X(sh_G)
   combines them. `}
def lagrange_choice_merely (G : Group) (X : GSet G) (pt : gset_underlying G X) (t : IsTransitive G X)
  (hX : IsFiniteGSet G X) : Mere (LagrangeChoice G X pt)
  ≔ let Xs ≔ gset_underlying G X in
    let Or ≔ Orbits G X in
    let h ≔ transitive_orbits_contractible G X t in
    finite_choice Xs hX (x ↦ Σ (USym G) (g ↦ Id Xs (gset_usym_act G X g x) pt))
      (x ↦ orbit_relation_from_path G X x pt
        (concat Or (orbit_of_point G X x) (h .center) (orbit_of_point G X pt)
          (inverse Or (h .center) (orbit_of_point G X x) (h .contract (orbit_of_point G X x)))
          (h .contract (orbit_of_point G X pt))))

{` xca:lagrange. For a finite group G and a subgroup (X, pt) with X a
   finite G-set: Card(G) = Card(X) × Card(H). `}
def lagrange_cardinality (G : Group) (S : Subgroups G) (hG : IsFiniteGroup G) (hX : IsFiniteGSet G (S .gset))
  : Id Nat (group_card G hG)
      (mul (gset_card G (S .gset) hX) (group_card (subgroup_group G S) (lagrange_subgroup_finite G S hG hX)))
  ≔ let X ≔ S .gset in
    let Xs ≔ gset_underlying G X in
    let H ≔ subgroup_group G S in
    let hH ≔ lagrange_subgroup_finite G S hG hX in
    let P ≔ Product Xs (USym H) in
    let hP ≔ finite_product Xs (USym H) hX hH in
    let Goal ≔ Id Nat (group_card G hG) (mul (gset_card G X hX) (group_card H hH)) in
    mere_rec (LagrangeChoice G X (S .point)) Goal
      (nat_set (group_card G hG) (mul (gset_card G X hX) (group_card H hH)))
      (f ↦ concat Nat (group_card G hG) (cardinality P hP) (mul (gset_card G X hX) (group_card H hH))
        (cardinality_equiv (USym G) P (lagrange_construction G S f) hG hP)
        (cardinality_product Xs (USym H) hX hH hP))
      (lagrange_choice_merely G X (S .point) (S .transitive) hX)

{` xca:lagrange2. The same counting via cosets. G_pt is the stabilizer of
   pt and G̃_pt the G_pt-set of def:Gx-action-on-G (underlying set USym G).
   USym(G_pt) ≃ USym H (both are (sh_G, pt) = (sh_G, pt)). `}
def lagrange2_stabilizer_usym_equiv (G : Group) (S : Subgroups G)
  : Equiv (USym (stabilizer_group G (S .gset) (S .point))) (USym (subgroup_group G S))
  ≔ let T ≔ ActionType G (S .gset) in
    let c ≔ component_point T (shape G, S .point) in
    component_path_equiv T (shape G, S .point) c c

{` Each coset O : G̃_pt / G_pt with a representative g, O = [g], has fiber
   [O]⁻¹ ≃ G_pt · g ≃ USym(G_pt) ≃ USym H (lem:cosets-Gx.g). `}
def lagrange2_coset_fiber_equiv (G : Group) (S : Subgroups G)
  (O : Orbits (stabilizer_group G (S .gset) (S .point)) (stabilizer_tilde_gset G (S .gset) (S .point)))
  (r : BookFiber (USym G)
         (Orbits (stabilizer_group G (S .gset) (S .point)) (stabilizer_tilde_gset G (S .gset) (S .point)))
         (orbit_of_point (stabilizer_group G (S .gset) (S .point)) (stabilizer_tilde_gset G (S .gset) (S .point))) O)
  : Equiv (BookFiber (USym G)
         (Orbits (stabilizer_group G (S .gset) (S .point)) (stabilizer_tilde_gset G (S .gset) (S .point)))
         (orbit_of_point (stabilizer_group G (S .gset) (S .point)) (stabilizer_tilde_gset G (S .gset) (S .point))) O)
      (USym (subgroup_group G S))
  ≔ let X ≔ S .gset in
    let pt ≔ S .point in
    let K ≔ stabilizer_group G X pt in
    let Y ≔ stabilizer_tilde_gset G X pt in
    let F ≔ BookFiber (USym G) (Orbits K Y) (orbit_of_point K Y) O in
    let YO ≔ gset_underlying K (gsubset_gset K Y (O .fst)) in
    compose_equiv F YO (USym (subgroup_group G S))
      (orbit_of_point_fiber_equiv K Y O)
      (compose_equiv YO (OrbitUnderlying K Y (r .fst)) (USym (subgroup_group G S))
        (canonical_inverse_equiv (OrbitUnderlying K Y (r .fst)) YO (orbit_underlying_class_equiv K Y O (r .fst) (r .snd)))
        (compose_equiv (OrbitUnderlying K Y (r .fst)) (USym K) (USym (subgroup_group G S))
          (canonical_inverse_equiv (USym K) (OrbitUnderlying K Y (r .fst))
            (native_equivalence (USym K) (OrbitUnderlying K Y (r .fst)) (stabilizer_coset_equiv G X pt (r .fst))))
          (lagrange2_stabilizer_usym_equiv G S)))

def lagrange2_cosets_finite (G : Group) (S : Subgroups G) (hX : IsFiniteGSet G (S .gset))
  : IsFinite (Orbits (stabilizer_group G (S .gset) (S .point)) (stabilizer_tilde_gset G (S .gset) (S .point)))
  ≔ finite_of_equiv (Orbits (stabilizer_group G (S .gset) (S .point)) (stabilizer_tilde_gset G (S .gset) (S .point)))
      (gset_underlying G (S .gset))
      (canonical_inverse_equiv (gset_underlying G (S .gset))
        (Orbits (stabilizer_group G (S .gset) (S .point)) (stabilizer_tilde_gset G (S .gset) (S .point)))
        (subgroup_coset_equiv G S))
      hX

def lagrange_cardinality_cosets (G : Group) (S : Subgroups G) (hG : IsFiniteGroup G) (hX : IsFiniteGSet G (S .gset))
  : Id Nat (group_card G hG)
      (mul (gset_card G (S .gset) hX) (group_card (subgroup_group G S) (lagrange_subgroup_finite G S hG hX)))
  ≔ let X ≔ S .gset in
    let Xs ≔ gset_underlying G X in
    let pt ≔ S .point in
    let H ≔ subgroup_group G S in
    let hH ≔ lagrange_subgroup_finite G S hG hX in
    let K ≔ stabilizer_group G X pt in
    let Y ≔ stabilizer_tilde_gset G X pt in
    let Or ≔ Orbits K Y in
    let hOr ≔ lagrange2_cosets_finite G S hX in
    let F ≔ (O ↦ BookFiber (USym G) Or (orbit_of_point K Y) O) : Or → Type in
    let spl ≔ orbit_splitting_equiv K Y in
    let hS : IsFinite (Σ Or F) ≔ finite_of_equiv (Σ Or F) (USym G) spl hG in
    let Goal ≔ Id Nat (group_card G hG) (mul (gset_card G X hX) (group_card H hH)) in
    mere_rec ((O : Or) → F O) Goal (nat_set (group_card G hG) (mul (gset_card G X hX) (group_card H hH)))
      (reps ↦
        concat Nat (group_card G hG) (cardinality (Σ Or F) hS) (mul (gset_card G X hX) (group_card H hH))
          (cardinality_equiv (USym G) (Σ Or F) (canonical_inverse_equiv (Σ Or F) (USym G) spl) hG hS)
          (concat Nat (cardinality (Σ Or F) hS) (mul (cardinality Or hOr) (group_card H hH))
            (mul (gset_card G X hX) (group_card H hH))
            (cardinality_equinumerous_sum Or (USym H) F hOr hH (O ↦ lagrange2_coset_fiber_equiv G S O (reps O)) hS)
            (refl ((n ↦ mul n (group_card H hH)) : Nat → Nat)
              (cardinality_equiv Or Xs (canonical_inverse_equiv Xs Or (subgroup_coset_equiv G S)) hOr hX))))
      (finite_choice Or hOr F (orbit_of_point_surjective K Y))
