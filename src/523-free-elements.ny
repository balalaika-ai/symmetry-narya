export "522-orbit-fibers"

{` Chapter 5, sec:fixpts-orbits: free elements. lem:free-pt-char (x free
   iff (- · x) : USym G → G · x is injective, and then a bijection) and
   lem:X_hG-set-iff-Xfree (X_hG is a set iff [-]_0 is an equivalence iff X
   is free). `}

{` xca:connected-trivia as used in lem:free-pt-char: BH contractible iff
   USym H contractible. These are local copies of
   is_trivial_group_usym_contractible / usym_contractible_trivial_group of
   module 506 (same proofs), kept here because importing 506 currently adds
   about two minutes of checking time to every module of this range. `}
def orbit_trivial_group_usym_contractible (H : Group) (h : IsTrivialGroup H) : BookIsContr (USym H)
  ≔ let B ≔ BG H .carrier in
    let hp : isProp B ≔ contractible_prop B (native_contraction B h) in
    (refl (shape H), q ↦ prop_is_set B hp (shape H) (shape H) (refl (shape H)) q)

def orbit_usym_contractible_trivial_group (H : Group) (h : BookIsContr (USym H)) : IsTrivialGroup H
  ≔ let B ≔ BG H .carrier in
    connected_loops_prop_contractible native_truncation B (bg_connected H)
      (connected_based_elim native_truncation B (bg_connected H) (shape H)
        (a ↦ isProp (Id B a a)) (a ↦ isprop_isprop (Id B a a))
        (contractible_prop (USym H) (native_contraction (USym H) h)))

{` USym(G_x) ≃ Σ_{g : USym G} (g · x = x): symmetries of (sh_G, x, !) in
   the component BG_x are symmetries of (sh_G, x) in X_hG
   (component_path_equiv), i.e. pairs (g, g · x = x)
   (rem:path-in-action-type). `}
def stabilizer_usym_equiv (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Equiv (USym (stabilizer_group G X x)) (Σ (USym G) (g ↦ Id (gset_underlying G X) (gset_usym_act G X g x) x))
  ≔ let T ≔ ActionType G X in
    let c ≔ component_point T (shape G, x) in
    compose_equiv (Id (NativeComponent T (shape G, x)) c c) (Id T (shape G, x) (shape G, x))
      (Σ (USym G) (g ↦ Id (gset_underlying G X) (gset_usym_act G X g x) x))
      (component_path_equiv T (shape G, x) c c)
      (action_type_path_equiv G X (shape G, x) (shape G, x))

{` If x is free, Σ_{g} (g · x = x) ≃ USym(G_x) is contractible, hence a
   proposition (xca:connected-trivia). `}
def stabilizer_fixing_prop_of_free (G : Group) (X : GSet G) (x : gset_underlying G X) (h : IsFreeElement G X x)
  : isProp (Σ (USym G) (g ↦ Id (gset_underlying G X) (gset_usym_act G X g x) x))
  ≔ let F ≔ Σ (USym G) (g ↦ Id (gset_underlying G X) (gset_usym_act G X g x) x) in
    contractible_prop F (native_contraction F
      (book_contractibility_equiv (USym (stabilizer_group G X x)) F (stabilizer_usym_equiv G X x)
        .map (orbit_trivial_group_usym_contractible (stabilizer_group G X x) h)))

{` Free ⇒ injective: g · x = g' · x gives (g'⁻¹ g) · x = x, so g'⁻¹ g = e,
   so g = g'. `}
def orbit_action_map_reflects_of_free (G : Group) (X : GSet G) (x : gset_underlying G X) (h : IsFreeElement G X x)
  : PathReflecting (USym G) (OrbitUnderlying G X x) (orbit_action_map G X x)
  ≔ g g' e ↦
    let S ≔ gset_underlying G X in
    let B ≔ BG G .carrier in
    let sh ≔ shape G in
    let gx ≔ gset_usym_act G X g x in
    let g'x ≔ gset_usym_act G X g' x in
    let ig' ≔ usym_inv G g' in
    let k ≔ usym_mul G ig' g in
    let e1 : Id S gx g'x ≔ refl ((w ↦ w .fst) : OrbitUnderlying G X x → S) e in
    let kx : Id S (gset_usym_act G X k x) x
      ≔ concat S (gset_usym_act G X k x) (gset_usym_act G X ig' gx) x
          (gset_act_mul G X ig' g x)
          (concat S (gset_usym_act G X ig' gx) (gset_usym_act G X ig' g'x) x
            (refl (gset_usym_act G X ig') e1) (gset_act_inv_left G X g' x)) in
    let pk : Id (USym G) k (usym_unit G)
      ≔ refl ((w ↦ w .fst) : Σ (USym G) (l ↦ Id S (gset_usym_act G X l x) x) → USym G)
          (stabilizer_fixing_prop_of_free G X x h (k, kx) (usym_unit G, gset_act_unit G X x)) in
    concat_cancel_right B sh sh sh g g' (inverse B sh sh g')
      (concat (Id B sh sh) (concat B sh sh sh g (inverse B sh sh g')) (refl sh)
        (concat B sh sh sh g' (inverse B sh sh g'))
        pk (inverse (Id B sh sh) (concat B sh sh sh g' (inverse B sh sh g')) (refl sh)
          (concat_inverse_right B sh sh g')))

{` Injective ⇒ free: Σ_{g} (g · x = x) is then a proposition with the
   element (e, !), hence contractible, and so is USym(G_x). `}
def free_of_orbit_action_map_reflects (G : Group) (X : GSet G) (x : gset_underlying G X)
  (inj : PathReflecting (USym G) (OrbitUnderlying G X x) (orbit_action_map G X x)) : IsFreeElement G X x
  ≔ let S ≔ gset_underlying G X in
    let Or ≔ Orbits G X in
    let F ≔ Σ (USym G) (g ↦ Id S (gset_usym_act G X g x) x) in
    let hprop : isProp F
      ≔ u v ↦ subtype_equal (USym G) (g ↦ Id S (gset_usym_act G X g x) x)
          (g ↦ gset_underlying_set G X (gset_usym_act G X g x) x) u v
          (inj (u .fst) (v .fst)
            (subtype_equal S (w ↦ Id Or (orbit_of_point G X x) (orbit_of_point G X w))
              (w ↦ orbits_set G X (orbit_of_point G X x) (orbit_of_point G X w))
              (orbit_action_map G X x (u .fst)) (orbit_action_map G X x (v .fst))
              (concat S (gset_usym_act G X (u .fst) x) x (gset_usym_act G X (v .fst) x) (u .snd)
                (inverse S (gset_usym_act G X (v .fst) x) x (v .snd))))) in
    let hcontr : BookIsContr F ≔ ((usym_unit G, gset_act_unit G X x), w ↦ hprop (usym_unit G, gset_act_unit G X x) w) in
    orbit_usym_contractible_trivial_group (stabilizer_group G X x)
      (equiv_inverse_map (BookIsContr (USym (stabilizer_group G X x))) (BookIsContr F)
        (book_contractibility_equiv (USym (stabilizer_group G X x)) F (stabilizer_usym_equiv G X x)) hcontr)

def embedding_prop_w1 (A B : Type) (f : A → B) : isProp (IsEmbedding A B f)
  ≔ pi_prop B (b ↦ isProp (BookFiber A B f b)) (b ↦ isprop_isprop (BookFiber A B f b))

{` lem:free-pt-char. x is free iff (- · x) : USym G → G · x is injective. `}
def free_iff_orbit_action_injective (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Equiv (IsFreeElement G X x) (IsEmbedding (USym G) (OrbitUnderlying G X x) (orbit_action_map G X x))
  ≔ iff_equiv (IsFreeElement G X x) (IsEmbedding (USym G) (OrbitUnderlying G X x) (orbit_action_map G X x))
      (is_free_element_prop G X x) (embedding_prop_w1 (USym G) (OrbitUnderlying G X x) (orbit_action_map G X x))
      (h ↦ path_reflecting_set_embedding (USym G) (OrbitUnderlying G X x) (orbit_underlying_set G X x)
        (orbit_action_map G X x) (orbit_action_map_reflects_of_free G X x h))
      (m ↦ free_of_orbit_action_map_reflects G X x
        (embedding_reflects_paths (USym G) (OrbitUnderlying G X x) (orbit_action_map G X x) m))

{` lem:free-pt-char, "(and hence a bijection)". `}
def free_orbit_action_equiv (G : Group) (X : GSet G) (x : gset_underlying G X) (h : IsFreeElement G X x)
  : BookEquiv (USym G) (OrbitUnderlying G X x)
  ≔ embedding_surjection_equiv native_truncation (USym G) (OrbitUnderlying G X x) (orbit_action_map G X x)
      (free_iff_orbit_action_injective G X x .map h) (orbit_action_map_surjective G X x)

{` lem:X_hG-set-iff-Xfree. (1) X_hG is a set; (2) [-]_0 is an
   equivalence; (3) X is free. `}
def action_type_set_orbit_map_is_equiv (G : Group) (X : GSet G) (hT : isSet (ActionType G X))
  : BookIsEquiv (ActionType G X) (Orbits G X) (orbit_map G X)
  ≔ let T ≔ ActionType G X in
    embedding_surjection_equiv native_truncation T (Orbits G X) (orbit_map G X)
      (path_reflecting_set_embedding T (Orbits G X) (orbits_set G X) (orbit_map G X)
        (u v e ↦ mere_rec (Id T u v) (Id T u v) (hT u v) (q ↦ q) (orbit_map_path_to_mere G X u v e)))
      (orbit_map_surjective G X)
    .equiv

def orbit_map_is_equiv_action_type_set (G : Group) (X : GSet G)
  (h : BookIsEquiv (ActionType G X) (Orbits G X) (orbit_map G X)) : isSet (ActionType G X)
  ≔ let T ≔ ActionType G X in
    hlevel_two_to_set T
      (hlevel_equiv (suc. (suc. zero.)) (Orbits G X) T
        (canonical_inverse_equiv T (Orbits G X) (native_equivalence T (Orbits G X) (orbit_map G X, h)))
        (set_to_hlevel_two (Orbits G X) (orbits_set G X)))

def action_type_set_free (G : Group) (X : GSet G) (hT : isSet (ActionType G X)) : IsFreeGSet G X
  ≔ let T ≔ ActionType G X in
    x ↦ connected_set_contractible native_truncation (NativeComponent T (shape G, x))
      (native_component_connected T (shape G, x))
      (sigma_set T (u ↦ Mere (Id T (shape G, x) u)) hT
        (u ↦ prop_is_set (Mere (Id T (shape G, x) u)) (mere_isprop (Id T (shape G, x) u))))

{` If the component of u is contractible then u = v is a proposition. `}
def component_contractible_paths_prop (A : Type) (u v : A) (h : BookIsContr (NativeComponent A u))
  : isProp (Id A u v)
  ≔ p q ↦
    let C ≔ NativeComponent A u in
    let c0 ≔ component_point A u in
    let cv : C ≔ (v, mere (Id A u v) p) in
    let e ≔ component_path_equiv A u c0 cv in
    let hC : isProp C ≔ contractible_prop C (native_contraction C h) in
    retract_prop (Id C c0 cv) (Id A u v) (prop_is_set C hC c0 cv) (e .map)
      (equiv_inverse_map (Id C c0 cv) (Id A u v) e) (equiv_counit (Id C c0 cv) (Id A u v) e) p q

def free_action_type_set (G : Group) (X : GSet G) (hfree : IsFreeGSet G X) : isSet (ActionType G X)
  ≔ let T ≔ ActionType G X in
    let B ≔ BG G .carrier in
    let comp_contr : (z : B) (y : X z .fst) → BookIsContr (NativeComponent T (z, y))
      ≔ connected_based_elim native_truncation B (bg_connected G) (shape G)
          (z ↦ (y : X z .fst) → BookIsContr (NativeComponent T (z, y)))
          (z ↦ pi_prop (X z .fst) (y ↦ BookIsContr (NativeComponent T (z, y)))
            (y ↦ book_iscontr_isprop (NativeComponent T (z, y))))
          hfree in
    u v ↦ component_contractible_paths_prop T u v (comp_contr (u .fst) (u .snd))

def orbit_map_is_equiv_free (G : Group) (X : GSet G)
  (h : BookIsEquiv (ActionType G X) (Orbits G X) (orbit_map G X)) : IsFreeGSet G X
  ≔ action_type_set_free G X (orbit_map_is_equiv_action_type_set G X h)

def action_type_set_free_equiv (G : Group) (X : GSet G) : Equiv (isSet (ActionType G X)) (IsFreeGSet G X)
  ≔ iff_equiv (isSet (ActionType G X)) (IsFreeGSet G X) (isset_isprop (ActionType G X)) (is_free_gset_prop G X)
      (action_type_set_free G X) (free_action_type_set G X)

def action_type_set_orbit_map_equiv (G : Group) (X : GSet G)
  : Equiv (isSet (ActionType G X)) (BookIsEquiv (ActionType G X) (Orbits G X) (orbit_map G X))
  ≔ iff_equiv (isSet (ActionType G X)) (BookIsEquiv (ActionType G X) (Orbits G X) (orbit_map G X))
      (isset_isprop (ActionType G X)) (book_isequiv_isprop (ActionType G X) (Orbits G X) (orbit_map G X))
      (action_type_set_orbit_map_is_equiv G X) (orbit_map_is_equiv_action_type_set G X)

