export "560-gset-action-equivalences"
export "485-infinity-groups"
export "541-cayley"
export "81-circle-degree-coverings"
export "1030-subgroup-containment"
export "260-root-degree-comparison"

{` Chapter 5: running-text claims of actions.tex that were only
   partly formalized.

   * Line 84: actions of an ∞-group G in a type A (InftyActionInType,
     functions BG → A), G-types (A = U), actions on an element a : A
     (pointed maps into the component of a), and the splitting
     (BG → A) ≃ Σ_{a:A} (action on a) for ∞-groups, as for groups (560).
   * Line 686: the symmetries picked out by deg_m (m > 0, pointed by its
     computation rule) are exactly the iterates loop^(qm) (Ω deg_m is the
     based action of module 80, whose windings are the multiples of m).
   * Line 709: deg_m (m > 0) and cst_base, pointed, classify homomorphisms
     Z → Z and 1 → Z that are monomorphisms.
   * Line 933: two monomorphisms into G are identified exactly when they pick
     out the same symmetries of G (same subset of USym G).
   * Footnote at line 1966: given g : sh = sh and g' : sh = z there is at
     most one s : sh = z with s g = g' (concat g s = g').
   * Footnote at line 2573: identifications of pointed maps BG →* BΣ_{USym G}
     (in particular the commutativity of the Cayley triangle) form a
     proposition. `}

{` Line 84: ∞-group actions. `}
def InftyActionInType (G : InftyGroup) (A : Type) : Type ≔ infty_BG G .carrier → A

def infty_action_object (G : InftyGroup) (A : Type) (X : InftyActionInType G A) : A ≔ X (infty_shape G)

def InftyGType (G : InftyGroup) : Type ≔ InftyActionInType G Type

def InftyActionOnElement (G : InftyGroup) (A : Type) (a : A) : Type
  ≔ BookPointedMap (infty_BG G) (NativeComponent A a, component_point A a)

def InftyActionInTypePointed (G : InftyGroup) (A : Type) : Type ≔ Σ A (a ↦ BookPointedMap (infty_BG G) (A, a))

def infty_action_in_type_pointed (G : InftyGroup) (A : Type) (X : infty_BG G .carrier → A) : InftyActionInTypePointed G A
  ≔ (X (infty_shape G), (X, refl (X (infty_shape G))))

def infty_action_in_type_pointed_counit (G : InftyGroup) (A : Type) (u : InftyActionInTypePointed G A)
  : Id (InftyActionInTypePointed G A) (infty_action_in_type_pointed G A (u .snd .fst)) u
  ≔ let f ≔ u .snd .fst in
    let b ≔ f (infty_shape G) in
    let T ≔ Σ A (x ↦ Id A x b) in
    refl ((t ↦ (t .fst, (f, t .snd))) : T → InftyActionInTypePointed G A)
      (contractible_prop T (path_to_contractible A b) (b, refl b) (u .fst, u .snd .snd))

def infty_action_in_type_split_equiv (G : InftyGroup) (A : Type)
  : Equiv (infty_BG G .carrier → A) (InftyActionInTypePointed G A)
  ≔ quasi_inverse_equiv (infty_BG G .carrier → A) (InftyActionInTypePointed G A)
      (infty_action_in_type_pointed G A) (u ↦ u .snd .fst) (X ↦ refl X) (infty_action_in_type_pointed_counit G A)

def infty_action_in_type_equiv (G : InftyGroup) (A : Type)
  : Equiv (InftyActionInType G A) (Σ A (a ↦ InftyActionOnElement G A a))
  ≔ compose_equiv (InftyActionInType G A) (InftyActionInTypePointed G A) (Σ A (a ↦ InftyActionOnElement G A a))
      (infty_action_in_type_split_equiv G A)
      (family_equiv A (a ↦ BookPointedMap (infty_BG G) (A, a)) (a ↦ InftyActionOnElement G A a)
        (a ↦ pointed_maps_into_component (infty_BG G) (G .classifying .connected) A a))

{` Line 709: deg_m, pointed by its computation rule at base, classifies a
   homomorphism Z → Z which is a monomorphism for m > 0 (it is a covering,
   cor:dgm-conncov). `}
def circle_degree_hom (C : CircleSignature) (m : Nat) : GroupHom (circle_group C) (circle_group C)
  ≔ mkhom (circle_group C) (circle_group C)
      (circle_degree_map C m,
       inverse (C .carrier) (circle_degree_map C m (C .base)) (C .base) (circle_degree_boundary C m .fst))

def circle_degree_hom_mono (C : CircleSignature) (m : Nat) (positive : BookLt zero. m)
  : IsGroupMono (circle_group C) (circle_group C) (circle_degree_hom C m)
  ≔ covering_group_mono (circle_group C) (circle_group C) (circle_degree_hom C m) (circle_degree_is_covering C m positive)

{` cst_base, pointed by refl: every homomorphism out of the trivial group is
   a monomorphism (its symmetries form a contractible type). `}
def trivial_group_hom_to (G : Group) : GroupHom trivial_group G
  ≔ mkhom trivial_group G (_ ↦ shape G, refl (shape G))

def trivial_group_hom_mono (G : Group) (f : GroupHom trivial_group G) : IsGroupMono trivial_group G f
  ≔ let c ≔ trivial_group_usym_contractible in
    path_reflecting_set_embedding (USym trivial_group) (USym G) (usym_set G) (usym_hom trivial_group G f)
      (p q _ ↦ concat (USym trivial_group) p (c .center) q (inverse (USym trivial_group) (c .center) p (c .contract p))
        (c .contract q))

def circle_constant_hom (C : CircleSignature) : GroupHom trivial_group (circle_group C)
  ≔ trivial_group_hom_to (circle_group C)

def circle_constant_hom_mono (C : CircleSignature) : IsGroupMono trivial_group (circle_group C) (circle_constant_hom C)
  ≔ trivial_group_hom_mono (circle_group C) (circle_constant_hom C)

{` Line 933: Mono(G) identifies exactly the monomorphisms that pick out the
   same symmetries of G. `}
def mono_path_preserves_picked (G : Group) (m m' : GroupMonos G) (p : Id (GroupMonos G) m m') (g : USym G)
  (h : SymmetryPickedOut G m g) : SymmetryPickedOut G m' g
  ≔ transport (GroupMonos G) (n ↦ SymmetryPickedOut G n g) m m' p h

def mono_path_of_same_symmetries (G : Group) (m m' : GroupMonos G)
  (h : (g : USym G) → SymmetryPickedOut G m g → SymmetryPickedOut G m' g)
  (h' : (g : USym G) → SymmetryPickedOut G m' g → SymmetryPickedOut G m g)
  : Id (GroupMonos G) m m'
  ≔ let S ≔ mono_to_subgroup G m in
    let S' ≔ mono_to_subgroup G m' in
    let p : Id (GroupMonos G) m (subgroup_to_mono G S)
      ≔ inverse (GroupMonos G) (subgroup_to_mono G S) m (mono_subgroup_roundtrip G m) in
    let p' : Id (GroupMonos G) m' (subgroup_to_mono G S')
      ≔ inverse (GroupMonos G) (subgroup_to_mono G S') m' (mono_subgroup_roundtrip G m') in
    let le : SubgroupLe G S S'
      ≔ g r ↦ mono_preserves_symmetries G S' m' p' g .snd (h g (mono_preserves_symmetries G S m p g .fst r)) in
    let le' : SubgroupLe G S' S
      ≔ g r ↦ mono_preserves_symmetries G S m p g .snd (h' g (mono_preserves_symmetries G S' m' p' g .fst r)) in
    concat (GroupMonos G) m (subgroup_to_mono G S) m' p
      (concat (GroupMonos G) (subgroup_to_mono G S) (subgroup_to_mono G S') m'
        (refl ((T ↦ subgroup_to_mono G T) : Subgroups G → GroupMonos G) (subgroup_le_antisym G S S' le le'))
        (mono_subgroup_roundtrip G m'))

{` Footnote ft:action-type-tildeGx-set (line 1966): at most one s : sh = z
   with s g = g' (the fiber of s ↦ s g over g' is contractible). `}
def stabilizer_tilde_mover_unique (G : Group) (z : BG G .carrier) (g : USym G) (g' : Id (BG G .carrier) (shape G) z)
  : isProp (Σ (Id (BG G .carrier) (shape G) z)
      (s ↦ Id (Id (BG G .carrier) (shape G) z) (concat (BG G .carrier) (shape G) (shape G) z g s) g'))
  ≔ contractible_prop
      (Σ (Id (BG G .carrier) (shape G) z)
        (s ↦ Id (Id (BG G .carrier) (shape G) z) (concat (BG G .carrier) (shape G) (shape G) z g s) g'))
      (concat_left_equiv (BG G .carrier) (shape G) (shape G) z g .equiv g')

{` Footnote at line 2573: identifications of pointed maps BG →* BΣ_{USym G}
   are propositions (source connected, target a groupoid); in particular any
   pointed factorization of Bρ_G is unique. `}
def cayley_triangle_prop (G : Group) (f : BookPointedMap (BG G) (BG (permutation_group (cayley_set G))))
  : isProp (Id (BookPointedMap (BG G) (BG (permutation_group (cayley_set G)))) f
      (hom_B G (permutation_group (cayley_set G)) (cayley_hom G)))
  ≔ pointed_maps_set (BG G) (BG (permutation_group (cayley_set G))) (bg_connected G)
      (bg_groupoid (permutation_group (cayley_set G))) f (hom_B G (permutation_group (cayley_set G)) (cayley_hom G))

{` Line 686: the symmetries picked out by deg_m are the loop^(qm). `}
def circle_degree_mono (C : CircleSignature) (m : Nat) (positive : BookLt zero. m) : GroupMonos (circle_group C)
  ≔ (circle_group C, (circle_degree_hom C m, circle_degree_hom_mono C m positive))

def circle_degree_hom_based_action (C : CircleSignature) (m : Nat) (l : USym (circle_group C))
  : Id (USym (circle_group C)) (usym_hom (circle_group C) (circle_group C) (circle_degree_hom C m) l)
      (circle_degree_based_action C m l)
  ≔ conjugate_inverse_transport (C .carrier) (C .base) (circle_degree_map C m (C .base)) (circle_degree_boundary C m .fst)
      (refl (circle_degree_map C m) l)

def circle_degree_picked_multiple (C : CircleSignature) (m : Nat) (positive : BookLt zero. m) (g : USym (circle_group C))
  (h : SymmetryPickedOut (circle_group C) (circle_degree_mono C m positive) g)
  : Mere (Σ Int (q ↦ Id (USym (circle_group C)) g (loop_power (C .carrier) (C .base) (C .loop) (int_mul q (pos. m)))))
  ≔ let Z ≔ circle_group C in
    let L ≔ USym Z in
    let lp ≔ loop_power (C .carrier) (C .base) (C .loop) in
    let u ≔ usym_hom Z Z (circle_degree_hom C m) in
    let K ≔ Σ Int (q ↦ Id L g (lp (int_mul q (pos. m)))) in
    let wg ≔ circle_winding C g in
    let img : degree_winding_image C m wg .fst
      ≔ mere_rec (Σ L (k ↦ Id L g (u k))) (degree_winding_image C m wg .fst) (degree_winding_image C m wg .snd)
          (w ↦ mere (BookFiber L Int (degree_winding_map C m) wg)
            (w .fst, refl (circle_winding C)
              (concat L g (u (w .fst)) (circle_degree_based_action C m (w .fst)) (w .snd)
                (circle_degree_hom_based_action C m (w .fst)))))
          h in
    mere_rec (MultipleWitness m wg) (Mere K) (mere_isprop K)
      (v ↦ mere K (v .fst, concat L g (lp wg) (lp (int_mul (v .fst) (pos. m)))
          (inverse L (lp wg) g (circle_power_winding C g)) (refl lp (v .snd))))
      (degree_winding_multiple C m wg img)

def circle_degree_multiple_picked (C : CircleSignature) (m : Nat) (positive : BookLt zero. m) (g : USym (circle_group C))
  (h : Mere (Σ Int (q ↦ Id (USym (circle_group C)) g (loop_power (C .carrier) (C .base) (C .loop) (int_mul q (pos. m))))))
  : SymmetryPickedOut (circle_group C) (circle_degree_mono C m positive) g
  ≔ let Z ≔ circle_group C in
    let L ≔ USym Z in
    let lp ≔ loop_power (C .carrier) (C .base) (C .loop) in
    let u ≔ usym_hom Z Z (circle_degree_hom C m) in
    let ba ≔ circle_degree_based_action C m in
    let P ≔ Σ L (k ↦ Id L g (u k)) in
    mere_rec (Σ Int (q ↦ Id L g (lp (int_mul q (pos. m))))) (Mere P) (mere_isprop P)
      (v ↦
        let z ≔ int_mul (v .fst) (pos. m) in
        mere_rec (BookFiber L Int (degree_winding_map C m) z) (Mere P) (mere_isprop P)
          (w ↦ mere P (w .fst,
            concat L g (lp z) (u (w .fst)) (v .snd)
              (concat L (lp z) (ba (w .fst)) (u (w .fst))
                (concat L (lp z) (lp (degree_winding_map C m (w .fst))) (ba (w .fst)) (refl lp (w .snd))
                  (circle_power_winding C (ba (w .fst))))
                (inverse L (u (w .fst)) (ba (w .fst)) (circle_degree_hom_based_action C m (w .fst))))))
          (multiple_degree_winding C m z (mere (MultipleWitness m z) (v .fst, refl z))))
      h
