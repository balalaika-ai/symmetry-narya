{` Bridges for chapter 5, blind file 03-orbits (section "Invariant maps and orbits"), general part.
   The C₄-examples are in bridge-04b-c4. `}
export "03-orbits"
export "bridge-02-subgroups"
export "../../../src/525-orbit-stabilizer"
export "../../../src/571-function-gset-orbits"
export "../../../src/565-standard-symmetric-gsets"
export "../../../src/589-c4-bit-fixed-free"

{` Definition bridges. `}
def bridge_def_action_type (G : Group) (X : GSet G) : Id Type (BlindActionType G X) (ActionType G X) ≔ refl (ActionType G X)

def bridge_def_invariant_maps (G : Group) (X : GSet G) : Id Type (BlindInvariantMaps G X) (InvariantMaps G X)
  ≔ refl (InvariantMaps G X)

def bridge_def_orbits (G : Group) (X : GSet G) : Id Type (BlindOrbits G X) (Orbits G X) ≔ refl (Orbits G X)

def bridge_def_orbit_class0 (G : Group) (X : GSet G) : Id (ActionType G X → GSubsets G X) (blind_orbit_class0 G X) (orbit_subset G X)
  ≔ refl (orbit_subset G X)

def bridge_def_stabilizer (G : Group) (X : GSet G) (x : gset_underlying G X) : Id Group (blind_stabilizer G X x) (stabilizer_group G X x)
  ≔ refl (stabilizer_group G X x)

def bridge_def_stabilizer_incl (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Id (GroupHom (stabilizer_group G X x) G) (blind_stabilizer_incl G X x) (stabilizer_inclusion G X x)
  ≔ refl (stabilizer_inclusion G X x)

def bridge_def_orbit_underlying (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Id (GSet G) (blind_orbit_underlying G X x) (orbit_gset G X (shape G, x))
  ≔ refl (orbit_gset G X (shape G, x))

def bridge_def_fixed (G : Group) (X : GSet G) (x : gset_underlying G X) : Id Type (BlindFixed G X x) (IsFixedElement G X x)
  ≔ refl (IsFixedElement G X x)

def bridge_def_free (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Product (BlindFree G X x → IsFreeElement G X x) (IsFreeElement G X x → BlindFree G X x)
  ≔ (trivial_group_iff_path (stabilizer_group G X x) .snd, trivial_group_iff_path (stabilizer_group G X x) .fst)

def bridge_def_gset_free (G : Group) (X : GSet G)
  : Product (BlindGSetFree G X → IsFreeGSet G X) (IsFreeGSet G X → BlindGSetFree G X)
  ≔ (h x ↦ bridge_def_free G X x .fst (h x), h x ↦ bridge_def_free G X x .snd (h x))

def bridge_def_tilde (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Id (GSet (stabilizer_group G X x)) (blind_tilde G X x) (stabilizer_tilde_gset G X x)
  ≔ refl (stabilizer_tilde_gset G X x)

def bridge_def_fun_gset (G : Group) (X Y : GSet G) : Id (GSet G) (blind_fun_gset G X Y) (gset_hom_gset G X Y)
  ≔ refl (gset_hom_gset G X Y)

{` The orbit map [-]_0 needs a transitivity witness τ (a proposition); for our witness it is our orbit_map on the
   nose, and every τ equals ours. `}
def bridge_tau0 (G : Group) (X : GSet G) : BlindOrbitWitness G X ≔ u ↦ orbit_gset_transitive G X u

def bridge_tau_path (G : Group) (X : GSet G) (τ : BlindOrbitWitness G X) : Id (BlindOrbitWitness G X) (bridge_tau0 G X) τ
  ≔ funext (ActionType G X) (u ↦ IsTransitive G (gsubset_gset G X (orbit_subset G X u))) (bridge_tau0 G X) τ
      (u ↦ is_transitive_prop G (gsubset_gset G X (orbit_subset G X u)) (bridge_tau0 G X u) (τ u))

def bridge_def_orbit_class (G : Group) (X : GSet G) : Id (ActionType G X → Orbits G X) (blind_orbit_class G X (bridge_tau0 G X)) (orbit_map G X)
  ≔ refl (orbit_map G X)

def bridge_def_orbit_set (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Id Type (BlindOrbitSet G X (bridge_tau0 G X) x) (OrbitUnderlying G X x)
  ≔ refl (OrbitUnderlying G X x)

def bridge_tau (G : Group) (X : GSet G) (P : BlindOrbitWitness G X → Type) (h : P (bridge_tau0 G X)) (τ : BlindOrbitWitness G X) : P τ
  ≔ transport (BlindOrbitWitness G X) P (bridge_tau0 G X) τ (bridge_tau_path G X τ) h

def bridge_iff_of_equiv (A B : Type) (e : Equiv A B) : BlindIff A B ≔ (e .map, equiv_inverse_map A B e)

{` def:actiontype (footnotes). `}
def bridge_invariant_map_fixed : blind_invariant_map_fixed
  ≔ G X f z g ↦ inverse (X z .fst) (gset_act G X z z g (f z)) (f z)
      (pathover_transport_equiv (BG G .carrier) (u ↦ X u .fst) z z g (f z) (f z) .map (refl f g))

def bridge_princ_Z_no_invariant_maps : blind_princ_Z_no_invariant_maps
  ≔ C s ↦ principal_circle_no_invariant_maps C s

{` rem:path-in-action-type. `}
def bridge_path_in_action_type : blind_path_in_action_type
  ≔ G X z w x y ↦ (action_type_path_equiv G X (z, x) (w, y), action_type_mere_path_equiv G X (z, x) (w, y))

{` lem:[]0-maps-to-X/G. `}
def bridge_orbit_class0_transitive : blind_orbit_class0_transitive ≔ G X ↦ bridge_tau0 G X

{` lem:X/G=setTruncX_hG. Our pair uses our proof that X/G is a set; the blind one its own (a proposition). `}
def BridgeSetTruncStmt (G : Group) (X : GSet G) (h : isSet (Orbits G X)) : Type
  ≔ BookIsContr (Id (Σ SetTypes (S ↦ ActionType G X → S .fst))
      ((Orbits G X, h), orbit_map G X) ((SetTrunc (ActionType G X), set_trunc_set (ActionType G X)), set_trunc (ActionType G X)))

def bridge_X_G_setTrunc : blind_X_G_setTrunc
  ≔ G X ↦ bridge_tau G X (τ ↦ Product (Surjective (ActionType G X) (Orbits G X) (blind_orbit_class G X τ))
        (BookIsContr (Id (Σ SetTypes (S ↦ ActionType G X → S .fst))
           ((Orbits G X, blind_orbits_set G X), blind_orbit_class G X τ)
           ((SetTrunc (ActionType G X), set_trunc_set (ActionType G X)), set_trunc (ActionType G X)))))
      (orbit_map_surjective G X,
       transport (isSet (Orbits G X)) (BridgeSetTruncStmt G X) (orbits_set G X) (blind_orbits_set G X)
         (isset_isprop (Orbits G X) (orbits_set G X) (blind_orbits_set G X))
         (orbits_set_trunc_path_unique G X))

{` cor:orbit-equiv. For any equivalence relation R with the orbit predicate, [-] factors uniquely through X(sh)/R, by
   an equivalence (our surjection_quotient_unique for R, and maps out of a quotient are determined on classes). `}
def BridgeFactor (G : Group) (X : GSet G) (R : EquivalenceRelation (gset_underlying G X)) : Type
  ≔ Σ (Quotient (gset_underlying G X) R → Orbits G X)
      (f ↦ (x : gset_underlying G X) → Id (Orbits G X) (f (quotient_class (gset_underlying G X) R x)) (orbit_of_point G X x))

def bridge_factor_prop (G : Group) (X : GSet G) (R : EquivalenceRelation (gset_underlying G X)) : isProp (BridgeFactor G X R)
  ≔ let S ≔ gset_underlying G X in
    let Q ≔ Quotient S R in
    let O ≔ Orbits G X in
    let cls ≔ quotient_class S R in
    t1 t2 ↦ subtype_equal (Q → O) (f ↦ (x : S) → Id O (f (cls x)) (orbit_of_point G X x))
      (f ↦ pi_prop S (x ↦ Id O (f (cls x)) (orbit_of_point G X x)) (x ↦ orbits_set G X (f (cls x)) (orbit_of_point G X x)))
      t1 t2
      (equiv_inverse_map (Id (Q → O) (t1 .fst) (t2 .fst)) (Id (S → O) (precompose S Q O cls (t1 .fst)) (precompose S Q O cls (t2 .fst)))
        (cancel_surjection_into_set S Q O cls (quotient_surjective S R) (orbits_set G X) (t1 .fst) (t2 .fst))
        (funext S (_ ↦ O) (precompose S Q O cls (t1 .fst)) (precompose S Q O cls (t2 .fst))
          (x ↦ concat O (t1 .fst (cls x)) (orbit_of_point G X x) (t2 .fst (cls x)) (t1 .snd x)
                 (inverse O (t2 .fst (cls x)) (orbit_of_point G X x) (t2 .snd x)))))

def bridge_orbit_factor (G : Group) (X : GSet G) (R : EquivalenceRelation (gset_underlying G X))
  (hR : (x y : gset_underlying G X) → Id Type (R .predicate x y .fst) (OrbitRelation G X x y))
  : Σ (BookIsContr (BridgeFactor G X R)) (c ↦ BookIsEquiv (Quotient (gset_underlying G X) R) (Orbits G X) (c .center .fst))
  ≔ let S ≔ gset_underlying G X in
    let O ≔ Orbits G X in
    let o ≔ orbit_of_point G X in
    let cls ≔ quotient_class S R in
    let resp : Respects S O R o
      ≔ x y r ↦ orbit_relation_to_path G X x y (transport Type (A ↦ A) (R .predicate x y .fst) (OrbitRelation G X x y) (hR x y) r) in
    let back : (x y : S) → Id O (o x) (o y) → Rel S R x y
      ≔ x y e ↦ transport Type (A ↦ A) (OrbitRelation G X x y) (R .predicate x y .fst)
          (inverse Type (R .predicate x y .fst) (OrbitRelation G X x y) (hR x y))
          (orbit_point_path_exists_equiv G X x y .map e) in
    let L ≔ surjection_quotient_unique S O (orbits_set G X) R o (orbit_of_point_surjective G X) resp back in
    let e ≔ L .center .fst in
    let a : BridgeFactor G X R
      ≔ (e .map, x ↦ inverse O (o x) (e .map (cls x)) (happly S (_ ↦ O) o (compose S (Quotient S R) O (e .map) cls) (L .center .snd) x)) in
    ((a, t ↦ bridge_factor_prop G X R a t), e .equiv)

def bridge_orbit_equiv : blind_orbit_equiv
  ≔ G X ↦ bridge_tau G X (τ ↦ Product
        ((x y : gset_underlying G X) → Equiv (Id (Orbits G X) (blind_orbit_of G X τ x) (blind_orbit_of G X τ y))
           (BlindSameOrbitRel G X x y))
      (Product
        (Surjective (gset_underlying G X) (Orbits G X) (blind_orbit_of G X τ))
        ((R : EquivalenceRelation (gset_underlying G X))
         (hR : (x y : gset_underlying G X) → Id Type (R .predicate x y .fst) (BlindSameOrbitRel G X x y))
         → Σ (BookIsContr (Σ (Quotient (gset_underlying G X) R → Orbits G X)
                (f ↦ (x : gset_underlying G X) → Id (Orbits G X) (f (quotient_class (gset_underlying G X) R x)) (blind_orbit_of G X τ x))))
             (c ↦ BookIsEquiv (Quotient (gset_underlying G X) R) (Orbits G X) (c .center .fst)))))
      (x y ↦ orbit_point_path_exists_equiv G X x y, (orbit_of_point_surjective G X, R hR ↦ bridge_orbit_factor G X R hR))

{` rem:SubGX=Sub(X/G), xca:transX-just1orbit. `}
def bridge_SubGX_Sub_orbits : blind_SubGX_Sub_orbits ≔ G X ↦ gsubsets_orbit_subsets_equiv G X

def bridge_transX_just1orbit : blind_transX_just1orbit
  ≔ G X ↦ (h ↦ contractible_orbits_transitive G X h, t ↦ transitive_orbits_contractible G X t)

{` rem:equivalents-of-[x]=[y]. `}
def bridge_equivalents_xy : blind_equivalents_xy
  ≔ G X ↦ bridge_tau G X (τ ↦ (x y : gset_underlying G X)
      → Product
        (BlindIff (Id (Orbits G X) (blind_orbit_of G X τ x) (blind_orbit_of G X τ y))
           (Id (gset_underlying G X → PropTypes) (blind_orbit_of G X τ x .fst (shape G)) (blind_orbit_of G X τ y .fst (shape G))))
      (Product
        (BlindIff (Id (Orbits G X) (blind_orbit_of G X τ x) (blind_orbit_of G X τ y)) (BlindSameOrbitRel G X x y))
      (Product
        (BlindIff (Id (Orbits G X) (blind_orbit_of G X τ x) (blind_orbit_of G X τ y))
           (Mere (Id (ActionType G X) (shape G, x) (shape G, y))))
      (Product
        (BlindIff (Id (Orbits G X) (blind_orbit_of G X τ x) (blind_orbit_of G X τ y))
           (blind_orbit_of G X τ x .fst (shape G) y .fst))
        (BlindIff (Id (Orbits G X) (blind_orbit_of G X τ x) (blind_orbit_of G X τ y))
           (blind_orbit_of G X τ y .fst (shape G) x .fst))))))
      (x y ↦
        let P ≔ Id (Orbits G X) (orbit_of_point G X x) (orbit_of_point G X y) in
        (bridge_iff_of_equiv P (Id (gset_underlying G X → PropTypes) (orbit_of_point G X x .fst (shape G)) (orbit_of_point G X y .fst (shape G)))
           (orbit_point_path_subset_equiv G X x y),
         (bridge_iff_of_equiv P (OrbitRelation G X x y) (orbit_point_path_exists_equiv G X x y),
          (bridge_iff_of_equiv P (Mere (Id (ActionType G X) (shape G, x) (shape G, y))) (orbit_point_path_mere_equiv G X x y),
           (bridge_iff_of_equiv P (OrbitMember G X (orbit_of_point G X x) (shape G, y)) (orbit_point_path_member_equiv G X x y),
            bridge_iff_of_equiv P (OrbitMember G X (orbit_of_point G X y) (shape G, x)) (orbit_point_path_member_symm_equiv G X x y))))))

{` def:orbit-stabilizer. `}
def bridge_stabilizer_covering : blind_stabilizer_covering ≔ G X x ↦ stabilizer_inclusion_covering G X x

def bridge_stabilizer_mono : blind_stabilizer_mono ≔ G X x ↦ stabilizer_inclusion_mono G X x

def bridge_stabilizer_of_subgroup : blind_stabilizer_of_subgroup
  ≔ G S ↦
    let S' ≔ bridge_sub_from G S in
    concat (BlindHomInto G) (bridge_forget_mono G (stabilizer_mono G (S .fst) (S .snd .fst)))
      (bridge_forget_mono G (subgroup_to_mono G S')) (blind_F0 G S)
      (refl (bridge_forget_mono G)
        (inverse (GroupMonos G) (subgroup_to_mono G S') (stabilizer_mono G (S .fst) (S .snd .fst)) (subgroup_stabilizer_mono_path G S')))
      (inverse (BlindHomInto G) (blind_F0 G S) (bridge_forget_mono G (subgroup_to_mono G S')) (bridge_def_F0 G S))

{` rem:orbit-fibs (with y : X(z)). `}
def bridge_orbit_fibs : blind_orbit_fibs
  ≔ G X ↦ bridge_tau G X (τ ↦ (x : gset_underlying G X)
      → Product
          (BookPointedEquiv
             (ActionType G (orbit_gset G X (shape G, x)),
              (shape G, (x, mere (Id (ActionType G X) (shape G, x) (shape G, x)) (refl (shape G, x)))))
             (BG (stabilizer_group G X x)))
          (Equiv (orbit_gset G X (shape G, x) (shape G) .fst) (BlindOrbitSet G X τ x)))
      (x ↦ (((orbit_action_type_stabilizer_equiv G X x .map,
              inverse (BG (stabilizer_group G X x) .carrier)
                (orbit_action_type_stabilizer_equiv G X x .map
                  (shape G, (x, mere (Id (ActionType G X) (shape G, x) (shape G, x)) (refl (shape G, x)))))
                (BG (stabilizer_group G X x) .point) (orbit_action_type_stabilizer_point G X x)),
             book_equivalence (ActionType G (orbit_gset G X (shape G, x))) (BG (stabilizer_group G X x) .carrier)
               (orbit_action_type_stabilizer_equiv G X x) .equiv),
            orbit_gset_underlying_equiv G X x))

{` xca:[x]=[y]-implies-||Gx=Gy||. `}
def bridge_same_orbit_stabilizers : blind_same_orbit_stabilizers
  ≔ G X ↦ bridge_tau G X (τ ↦ (x y : gset_underlying G X)
      → Id (Orbits G X) (blind_orbit_of G X τ x) (blind_orbit_of G X τ y)
      → Mere (Id Group (stabilizer_group G X x) (stabilizer_group G X y)))
      (x y p ↦ stabilizer_groups_merely_equal G X x y p)

{` rem:subgrp-is-stabsubgr. `}
def bridge_stab_mono_orbit (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Id (GroupMonos G) (subgroup_to_mono G (orbit_subgroup G X x)) (stabilizer_mono G X x)
  ≔ concat (GroupMonos G) (subgroup_to_mono G (orbit_subgroup G X x))
      (subgroup_to_mono G (mono_to_subgroup G (stabilizer_mono G X x))) (stabilizer_mono G X x)
      (refl (subgroup_to_mono G)
        (inverse (Subgroups G) (mono_to_subgroup G (stabilizer_mono G X x)) (orbit_subgroup G X x) (stabilizer_subgroup_path G X x)))
      (mono_subgroup_roundtrip G (stabilizer_mono G X x))

def bridge_subgrp_is_stabsubgr : blind_subgrp_is_stabsubgr
  ≔ G X τ x ↦
    let K ≔ BlindHomInto G in
    let Y ≔ orbit_gset G X (shape G, x) in
    let y0 : gset_underlying G Y ≔ (x, mere (Id (ActionType G X) (shape G, x) (shape G, x)) (refl (shape G, x))) in
    let Gx : BlindHomInto G ≔ (stabilizer_group G X x, stabilizer_inclusion G X x) in
    (concat K (blind_F0 G (Y, (y0, τ (shape G, x))))
        (bridge_forget_mono G (subgroup_to_mono G (orbit_subgroup G X x))) Gx
        (bridge_hominto_conn G Y y0 (blind_tot_connected G Y (τ (shape G, x)))
          (transitive_action_type_connected G Y (orbit_gset_transitive G X (shape G, x))))
        (refl (bridge_forget_mono G) (bridge_stab_mono_orbit G X x)),
     t ↦ concat K Gx (bridge_forget_mono G (subgroup_to_mono G (X, x, t))) (blind_F0 G (X, (x, t)))
        (refl (bridge_forget_mono G)
          (concat (GroupMonos G) (stabilizer_mono G X x) (subgroup_to_mono G (mono_to_subgroup G (stabilizer_mono G X x)))
             (subgroup_to_mono G (X, x, t))
             (inverse (GroupMonos G) (subgroup_to_mono G (mono_to_subgroup G (stabilizer_mono G X x))) (stabilizer_mono G X x)
               (mono_subgroup_roundtrip G (stabilizer_mono G X x)))
             (refl (subgroup_to_mono G) (transitive_stabilizer_subgroup_path G X x t))))
        (inverse K (blind_F0 G (X, (x, t))) (bridge_forget_mono G (subgroup_to_mono G (X, x, t))) (bridge_def_F0 G (X, (x, t)))))

{` lem:splitting into orbits. `}
def bridge_splitting_into_orbits : blind_splitting_into_orbits
  ≔ G X ↦ bridge_tau G X (τ ↦ BookIsEquiv (Σ (Orbits G X) (O ↦ BookFiber (gset_underlying G X) (Orbits G X) (blind_orbit_of G X τ) O))
        (gset_underlying G X) (u ↦ u .snd .fst))
      (book_isequiv_homotopic (Σ (Orbits G X) (O ↦ BookFiber (gset_underlying G X) (Orbits G X) (orbit_of_point G X) O))
         (gset_underlying G X) (orbit_splitting_equiv G X .map) (u ↦ u .snd .fst) (orbit_splitting_map G X)
         (book_equivalence (Σ (Orbits G X) (O ↦ BookFiber (gset_underlying G X) (Orbits G X) (orbit_of_point G X) O))
            (gset_underlying G X) (orbit_splitting_equiv G X) .equiv))

{` exa:fixed-free-neither (general part). `}
def bridge_triv_fixed : blind_triv_fixed ≔ G S s ↦ trivial_gset_fixed G S s

def bridge_princ_free : blind_princ_free
  ≔ G g ↦ trivial_group_path (stabilizer_group G (principal_gset G) g) (principal_gset_free G g)

def bridge_princ_tot_contractible : blind_princ_tot_contractible ≔ G ↦ gset_paths_action_type_contractible G (shape G)

{` lem:free-pt-char. The blind (- · x) agrees with ours (the second components lie in a proposition). `}
def bridge_orbit_map_agree (G : Group) (X : GSet G) (x : gset_underlying G X) (g : USym G)
  : Id (OrbitUnderlying G X x) (orbit_action_map G X x g) (blind_orbit_map G X (bridge_tau0 G X) x g)
  ≔ subtype_equal (gset_underlying G X) (y ↦ Id (Orbits G X) (orbit_of_point G X x) (orbit_of_point G X y))
      (y ↦ orbits_set G X (orbit_of_point G X x) (orbit_of_point G X y))
      (orbit_action_map G X x g) (blind_orbit_map G X (bridge_tau0 G X) x g) (refl (gset_usym_act G X g x))

def bridge_orbit_map_path (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Id (USym G → OrbitUnderlying G X x) (orbit_action_map G X x) (blind_orbit_map G X (bridge_tau0 G X) x)
  ≔ funext (USym G) (_ ↦ OrbitUnderlying G X x) (orbit_action_map G X x) (blind_orbit_map G X (bridge_tau0 G X) x)
      (bridge_orbit_map_agree G X x)

def BridgeFreePt (G : Group) (X : GSet G) (x : gset_underlying G X) (f : USym G → OrbitUnderlying G X x) : Type
  ≔ Product (Surjective (USym G) (OrbitUnderlying G X x) f)
      (BlindIff (BlindFree G X x) (IsEmbedding (USym G) (OrbitUnderlying G X x) f))

def bridge_free_pt_char : blind_free_pt_char
  ≔ G X ↦ bridge_tau G X (τ ↦ (x : gset_underlying G X)
      → Product (Surjective (USym G) (BlindOrbitSet G X τ x) (blind_orbit_map G X τ x))
          (BlindIff (BlindFree G X x) (IsEmbedding (USym G) (BlindOrbitSet G X τ x) (blind_orbit_map G X τ x))))
      (x ↦ transport (USym G → OrbitUnderlying G X x) (BridgeFreePt G X x) (orbit_action_map G X x)
         (blind_orbit_map G X (bridge_tau0 G X) x) (bridge_orbit_map_path G X x)
         (orbit_action_map_surjective G X x,
          (h ↦ free_iff_orbit_action_injective G X x .map (bridge_def_free G X x .fst h),
           h ↦ bridge_def_free G X x .snd (equiv_inverse_map (IsFreeElement G X x)
             (IsEmbedding (USym G) (OrbitUnderlying G X x) (orbit_action_map G X x)) (free_iff_orbit_action_injective G X x) h))))

{` lem:X_hG-set-iff-Xfree. `}
def bridge_X_hG_set_iff_free : blind_X_hG_set_iff_free
  ≔ G X ↦ bridge_tau G X (τ ↦ Product
        (BlindIff (isSet (ActionType G X)) (BookIsEquiv (ActionType G X) (Orbits G X) (blind_orbit_class G X τ)))
        (BlindIff (isSet (ActionType G X)) (BlindGSetFree G X)))
      (bridge_iff_of_equiv (isSet (ActionType G X)) (BookIsEquiv (ActionType G X) (Orbits G X) (orbit_map G X))
         (action_type_set_orbit_map_equiv G X),
       (h ↦ bridge_def_gset_free G X .snd (action_type_set_free_equiv G X .map h),
        h ↦ equiv_inverse_map (isSet (ActionType G X)) (IsFreeGSet G X) (action_type_set_free_equiv G X) (bridge_def_gset_free G X .fst h)))

{` lem:fixed-char, lem:fixpts-are-fixed, xca:HomGsets-ev. `}
def bridge_fixed_char : blind_fixed_char
  ≔ G X ↦ bridge_tau G X (τ ↦ (x : gset_underlying G X)
      → Product (BlindIff (IsFixedElement G X x) (BookIsContr (BlindOrbitSet G X τ x)))
          (BlindIff (IsFixedElement G X x) ((g : USym G) → Id (gset_underlying G X) x (gset_usym_act G X g x))))
      (x ↦ (bridge_iff_of_equiv (IsFixedElement G X x) (BookIsContr (OrbitUnderlying G X x)) (fixed_element_orbit_contractible G X x),
            bridge_iff_of_equiv (IsFixedElement G X x) ((g : USym G) → Id (gset_underlying G X) x (gset_usym_act G X g x))
              (fixed_element_fixed_by_all G X x)))

def bridge_fixpts_are_fixed : blind_fixpts_are_fixed
  ≔ G X ↦ (invariant_map_eval_injective G X,
             x ↦ bridge_iff_of_equiv (Mere (BookFiber (InvariantMaps G X) (gset_underlying G X) (invariant_map_eval G X) x))
               (IsFixedElement G X x) (invariant_map_eval_image G X x))

def bridge_HomGsets_ev : blind_HomGsets_ev
  ≔ G X Y ↦ (invariant_map_eval_injective G (gset_hom_gset G X Y),
             φ ↦ bridge_iff_of_equiv
               (Mere (BookFiber (InvariantMaps G (gset_hom_gset G X Y)) (gset_underlying G (gset_hom_gset G X Y))
                  (invariant_map_eval G (gset_hom_gset G X Y)) φ))
               (IsFixedElement G (gset_hom_gset G X Y) φ) (invariant_map_eval_image G (gset_hom_gset G X Y) φ))

{` xca:Gset-A->B. `}
def bridge_def_S2xS2 : Id Group blind_S2xS2 sigma_two_squared ≔ refl sigma_two_squared

def bridge_def_AB_set : Id (GSet sigma_two_squared) blind_AB_set function_gset ≔ refl function_gset

def bridge_def_A2_set : Id (GSet sigma_two) blind_A2_set function_gset_left ≔ refl function_gset_left

def bridge_def_2B_set : Id (GSet sigma_two) blind_2B_set function_gset_right ≔ refl function_gset_right

def bridge_def_const22_set : Id (GSet sigma_two_squared) blind_const22_set constant_square_gset ≔ refl constant_square_gset

def bridge_AB_action : blind_AB_action
  ≔ g f a ↦
    let S2 ≔ symmetric_group two in
    let X2 ≔ standard_symmetric_gset two in
    let b ≔ gset_usym_act S2 X2 (usym_inv S2 (g .fst)) a in
    concat (Fin two) (gset_usym_act sigma_two_squared function_gset g f a)
      (gset_usym_act sigma_two_squared function_gset g f (gset_usym_act S2 X2 (g .fst) b))
      (gset_usym_act S2 X2 (g .snd) (f b))
      (refl (gset_usym_act sigma_two_squared function_gset g f)
        (inverse (Fin two) (gset_usym_act S2 X2 (g .fst) b) a (gset_act_inv_right S2 X2 (g .fst) a)))
      (function_gset_act g f b)

def bridge_AB_orbits_invariants : blind_AB_orbits_invariants
  ≔ (compose_equiv (Orbits sigma_two_squared function_gset) Bool (Fin two) function_gset_orbits_equiv
       (canonical_inverse_equiv (Fin two) Bool fin_two_equiv),
     s ↦ function_gset_no_invariant_maps s)

def bridge_const22_orbits_invariants : blind_const22_orbits_invariants
  ≔ (constant_square_orbits_equiv, constant_square_invariant_equiv)

def bridge_A2_orbits_invariants : blind_A2_orbits_invariants
  ≔ (function_gset_left_orbits_equiv, function_gset_left_invariant_equiv)

def bridge_2B_orbits_invariants : blind_2B_orbits_invariants
  ≔ (compose_equiv (Orbits sigma_two function_gset_right) Bool (Fin two) function_gset_right_orbits_equiv
       (canonical_inverse_equiv (Fin two) Bool fin_two_equiv),
     s ↦ function_gset_right_no_invariant_maps s)

{` xca:Gx-action-on-G, con:orbit-stabilizer, cor:action-subgrp-free, lem:cosets-Gx.g, con:preLagrange. `}
def bridge_Gx_action_on_G : blind_Gx_action_on_G
  ≔ G X x v s g ↦ stabilizer_tilde_gset_act G X x (shape (stabilizer_group G X x)) v s g

def bridge_orbit_stabilizer : blind_orbit_stabilizer
  ≔ G X ↦ bridge_tau G X (τ ↦ (x : gset_underlying G X)
      → Equiv (ActionType (stabilizer_group G X x) (stabilizer_tilde_gset G X x)) (BlindOrbitSet G X τ x))
      (x ↦ orbit_stabilizer_equiv G X x)

def bridge_action_subgrp_free : blind_action_subgrp_free
  ≔ G X x ↦ bridge_def_gset_free (stabilizer_group G X x) (stabilizer_tilde_gset G X x) .snd (stabilizer_tilde_free G X x)

def bridge_cosets_Gx_g : blind_cosets_Gx_g
  ≔ G X x τ g ↦
    let H ≔ stabilizer_group G X x in
    let Y ≔ stabilizer_tilde_gset G X x in
    let e ≔ stabilizer_coset_equiv G X x g in
    bridge_tau H Y (τ' ↦ BookIsEquiv (USym H) (BlindOrbitSet H Y τ' g) (blind_orbit_map H Y τ' g))
      (book_isequiv_homotopic (USym H) (OrbitUnderlying H Y g) (e .map) (blind_orbit_map H Y (bridge_tau0 H Y) g)
        (s ↦ subtype_equal (USym G) (y ↦ Id (Orbits H Y) (orbit_of_point H Y g) (orbit_of_point H Y y))
           (y ↦ orbits_set H Y (orbit_of_point H Y g) (orbit_of_point H Y y))
           (e .map s) (blind_orbit_map H Y (bridge_tau0 H Y) g s)
           (concat (USym G) (e .map s .fst) (usym_mul G (s .fst .fst) g) (gset_usym_act H Y s g)
              (stabilizer_coset_equiv_map G X x g s)
              (inverse (USym G) (gset_usym_act H Y s g) (usym_mul G (s .fst .fst) g) (stabilizer_tilde_gset_usym_act G X x s g))))
        (e .equiv))
      τ

def bridge_preLagrange : blind_preLagrange ≔ G S ↦ subgroup_coset_equiv G (bridge_sub_from G S)

{` xca:fixed-free-neither and xca:fixed-free-neither-action-types (general parts). `}
def bridge_triv_stabilizer_path (G : Group) (S : SetTypes) (s : S .fst)
  : Id Group (stabilizer_group G (gset_trivial G S) s) G
  ≔ group_path_from_iso (stabilizer_group G (gset_trivial G S) s) G
      (stabilizer_inclusion G (gset_trivial G S) s, trivial_gset_fixed G S s)
