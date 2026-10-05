export "520-orbit-relations"

{` Chapter 5, sec:fixpts-orbits: the fibers of [-]_0 and [-] (the
   paragraphs after rem:equivalents-of-[x]=[y]), rem:orbit-fibs with
   fig:fibs-at-[x], xca:[x]=[y]-implies-||Gx=Gy|| and lem:splitting into
   orbits (with its footnote on equivalence classes). `}

{` Σ_{u : X_hG} O(u) is the action type of the underlying G-set X_O
   (reassociation of Σ_{(z, x)} O(z)(x)). `}
def orbit_members_action_type_equiv (G : Group) (X : GSet G) (O : Orbits G X)
  : Equiv (Σ (ActionType G X) (u ↦ OrbitMember G X O u)) (ActionType G (gsubset_gset G X (O .fst)))
  ≔ quasi_inverse_equiv (Σ (ActionType G X) (u ↦ OrbitMember G X O u)) (ActionType G (gsubset_gset G X (O .fst)))
      (t ↦ (t .fst .fst, (t .fst .snd, t .snd))) (s ↦ ((s .fst, s .snd .fst), s .snd .snd))
      (t ↦ refl t) (s ↦ refl s)

{` The fiber of [-]_0 at an orbit O, Σ_{u : X_hG} (O = [u]_0), is
   equivalent to the action type (X_O)_hG. `}
def orbit_map_fiber_equiv (G : Group) (X : GSet G) (O : Orbits G X)
  : Equiv (BookFiber (ActionType G X) (Orbits G X) (orbit_map G X) O) (ActionType G (gsubset_gset G X (O .fst)))
  ≔ let T ≔ ActionType G X in
    compose_equiv (BookFiber T (Orbits G X) (orbit_map G X) O) (Σ T (u ↦ OrbitMember G X O u))
      (ActionType G (gsubset_gset G X (O .fst)))
      (family_equiv T (u ↦ Id (Orbits G X) O (orbit_map G X u)) (u ↦ OrbitMember G X O u)
        (u ↦ canonical_inverse_equiv (OrbitMember G X O u) (Id (Orbits G X) O (orbit_map G X u))
          (orbit_member_path_equiv G X O u)))
      (orbit_members_action_type_equiv G X O)

{` The fiber of [-] at O, Σ_{x : X(sh_G)} (O = [x]), is equivalent to the
   underlying set X_O(sh_G) = Σ_{x : X(sh_G)} O(sh_G)(x), via the identity
   on first components. `}
def orbit_of_point_fiber_equiv (G : Group) (X : GSet G) (O : Orbits G X)
  : Equiv (BookFiber (gset_underlying G X) (Orbits G X) (orbit_of_point G X) O)
      (gset_underlying G (gsubset_gset G X (O .fst)))
  ≔ family_equiv (gset_underlying G X) (x ↦ Id (Orbits G X) O (orbit_of_point G X x))
      (x ↦ OrbitMember G X O (shape G, x))
      (x ↦ canonical_inverse_equiv (OrbitMember G X O (shape G, x)) (Id (Orbits G X) O (orbit_of_point G X x))
        (orbit_member_path_equiv G X O (shape G, x)))

def orbit_of_point_fiber_equiv_fst (G : Group) (X : GSet G) (O : Orbits G X)
  (t : BookFiber (gset_underlying G X) (Orbits G X) (orbit_of_point G X) O)
  : Id (gset_underlying G X) (orbit_of_point_fiber_equiv G X O .map t .fst) (t .fst)
  ≔ refl (t .fst)

{` lem:splitting into orbits. (O, x) ↦ x : Σ_{O : X/G} [O]⁻¹ ≃ X(sh_G),
   with [O]⁻¹ = Σ_{x : X(sh_G)} (O = [x]) (lem:contract-away, here
   lem:sum-of-fibers). `}
def orbit_splitting_equiv (G : Group) (X : GSet G)
  : Equiv (Σ (Orbits G X) (O ↦ BookFiber (gset_underlying G X) (Orbits G X) (orbit_of_point G X) O))
      (gset_underlying G X)
  ≔ sum_of_fibers_equiv (gset_underlying G X) (Orbits G X) (orbit_of_point G X)

def orbit_splitting_map (G : Group) (X : GSet G)
  (t : Σ (Orbits G X) (O ↦ BookFiber (gset_underlying G X) (Orbits G X) (orbit_of_point G X) O))
  : Id (gset_underlying G X) (orbit_splitting_equiv G X .map t) (t .snd .fst)
  ≔ refl (t .snd .fst)

{` The same with the fibers replaced by the underlying sets of the orbits
   (as used in the proof of lem:burnside): Σ_{O : X/G} X_O(sh_G) ≃ X(sh_G),
   (O, (x, !)) ↦ x. `}
def orbit_splitting_members_equiv (G : Group) (X : GSet G)
  : Equiv (Σ (Orbits G X) (O ↦ gset_underlying G (gsubset_gset G X (O .fst)))) (gset_underlying G X)
  ≔ let F ≔ (O ↦ BookFiber (gset_underlying G X) (Orbits G X) (orbit_of_point G X) O) : Orbits G X → Type in
    compose_equiv (Σ (Orbits G X) (O ↦ gset_underlying G (gsubset_gset G X (O .fst)))) (Σ (Orbits G X) F)
      (gset_underlying G X)
      (family_equiv (Orbits G X) (O ↦ gset_underlying G (gsubset_gset G X (O .fst))) F
        (O ↦ canonical_inverse_equiv (F O) (gset_underlying G (gsubset_gset G X (O .fst)))
          (orbit_of_point_fiber_equiv G X O)))
      (orbit_splitting_equiv G X)

def orbit_splitting_members_map (G : Group) (X : GSet G)
  (t : Σ (Orbits G X) (O ↦ gset_underlying G (gsubset_gset G X (O .fst))))
  : Id (gset_underlying G X) (orbit_splitting_members_equiv G X .map t) (t .snd .fst)
  ≔ refl (t .snd .fst)

{` Footnote to lem:splitting into orbits: for every set A and every
   equivalence relation R on A, the equivalence classes sum up to A,
   Σ_{c : A/R} Σ_{a : A} c(a) ≃ A, (c, a, !) ↦ a. (No set hypothesis is
   needed.) `}
def quotient_classes_total_equiv (A : Type) (R : EquivalenceRelation A)
  : Equiv (Σ (Quotient A R) (c ↦ Σ A (a ↦ c .fst a .fst))) A
  ≔ let Q ≔ Quotient A R in
    compose_equiv (Σ Q (c ↦ Σ A (a ↦ c .fst a .fst))) (Σ Q (c ↦ BookFiber A Q (quotient_class A R) c)) A
      (family_equiv Q (c ↦ Σ A (a ↦ c .fst a .fst)) (c ↦ BookFiber A Q (quotient_class A R) c)
        (c ↦ family_equiv A (a ↦ c .fst a .fst) (a ↦ Id Q c (quotient_class A R a))
          (a ↦ canonical_inverse_equiv (Id Q c (quotient_class A R a)) (c .fst a .fst)
            (quotient_class_property A R c a))))
      (sum_of_fibers_equiv A Q (quotient_class A R))

def quotient_classes_total_map (A : Type) (R : EquivalenceRelation A)
  (t : Σ (Quotient A R) (c ↦ Σ A (a ↦ c .fst a .fst)))
  : Id A (quotient_classes_total_equiv A R .map t) (t .snd .fst)
  ≔ refl (t .snd .fst)

{` rem:orbit-fibs. The action type of X_{[x]}, pointed at (sh_G, x), is
   the classifying type BG_x (pointed by (sh_G, x, !), by definition). `}
def orbit_action_type_stabilizer_equiv (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Equiv (ActionType G (orbit_gset G X (shape G, x))) (BG (stabilizer_group G X x) .carrier)
  ≔ orbit_gset_component_equiv G X (shape G, x)

def orbit_action_type_stabilizer_point (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Id (BG (stabilizer_group G X x) .carrier)
      (orbit_action_type_stabilizer_equiv G X x .map
        (shape G, (x, mere (Id (ActionType G X) (shape G, x) (shape G, x)) (refl (shape G, x)))))
      (BG (stabilizer_group G X x) .point)
  ≔ refl (BG (stabilizer_group G X x) .point)

{` rem:orbit-fibs. X_{[x]} is a transitive G-set (lem:[]0-maps-to-X/G)
   whose underlying set Σ_{y : X(sh_G)} ‖(sh_G, x) = (sh_G, y)‖ is G · x.
   (The remark prints X_{[x]}(z) with y : X(sh_G); the definition gives
   y : X(z).) `}
def orbit_gset_underlying_equiv (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Equiv (gset_underlying G (orbit_gset G X (shape G, x))) (OrbitUnderlying G X x)
  ≔ family_equiv (gset_underlying G X) (y ↦ Mere (Id (ActionType G X) (shape G, x) (shape G, y)))
      (y ↦ Id (Orbits G X) (orbit_of_point G X x) (orbit_of_point G X y))
      (y ↦ canonical_inverse_equiv (Id (Orbits G X) (orbit_of_point G X x) (orbit_of_point G X y))
        (Mere (Id (ActionType G X) (shape G, x) (shape G, y))) (orbit_point_path_mere_equiv G X x y))

def orbit_gset_point_transitive (G : Group) (X : GSet G) (x : gset_underlying G X)
  : IsTransitive G (orbit_gset G X (shape G, x))
  ≔ orbit_gset_transitive G X (shape G, x)

{` rem:orbit-fibs. G · x and BG_x depend only on the class O = [x]: they
   are identified with X_O(sh_G) and (X_O)_hG. `}
def orbit_underlying_class_equiv (G : Group) (X : GSet G) (O : Orbits G X) (x : gset_underlying G X)
  (p : Id (Orbits G X) O (orbit_of_point G X x))
  : Equiv (OrbitUnderlying G X x) (gset_underlying G (gsubset_gset G X (O .fst)))
  ≔ let Or ≔ Orbits G X in
    family_equiv (gset_underlying G X) (y ↦ Id Or (orbit_of_point G X x) (orbit_of_point G X y))
      (y ↦ OrbitMember G X O (shape G, y))
      (y ↦ iff_equiv (Id Or (orbit_of_point G X x) (orbit_of_point G X y)) (OrbitMember G X O (shape G, y))
        (orbits_set G X (orbit_of_point G X x) (orbit_of_point G X y)) (orbit_member_prop G X O (shape G, y))
        (q ↦ orbit_member_of_path G X O (shape G, y)
          (concat Or O (orbit_of_point G X x) (orbit_of_point G X y) p q))
        (o ↦ concat Or (orbit_of_point G X x) O (orbit_of_point G X y)
          (inverse Or O (orbit_of_point G X x) p) (orbit_path_of_member G X O (shape G, y) o)))

def orbit_component_class_equiv (G : Group) (X : GSet G) (O : Orbits G X) (x : gset_underlying G X)
  (p : Id (Orbits G X) O (orbit_of_point G X x))
  : Equiv (BG (stabilizer_group G X x) .carrier) (ActionType G (gsubset_gset G X (O .fst)))
  ≔ let T ≔ ActionType G X in
    let Or ≔ Orbits G X in
    compose_equiv (NativeComponent T (shape G, x)) (Σ T (u ↦ OrbitMember G X O u))
      (ActionType G (gsubset_gset G X (O .fst)))
      (family_equiv T (u ↦ Mere (Id T (shape G, x) u)) (u ↦ OrbitMember G X O u)
        (u ↦ iff_equiv (Mere (Id T (shape G, x) u)) (OrbitMember G X O u)
          (mere_isprop (Id T (shape G, x) u)) (orbit_member_prop G X O u)
          (r ↦ orbit_member_of_path G X O u
            (concat Or O (orbit_of_point G X x) (orbit_map G X u) p (orbit_map_path_from_mere G X (shape G, x) u r)))
          (o ↦ orbit_map_path_to_mere G X (shape G, x) u
            (concat Or (orbit_of_point G X x) O (orbit_map G X u)
              (inverse Or O (orbit_of_point G X x) p) (orbit_path_of_member G X O u o)))))
      (orbit_members_action_type_equiv G X O)

{` fig:fibs-at-[x]: the map Σ_{O : X/G} X_O(sh_G) → Σ_{O : X/G} (X_O)_hG,
   (O, y) ↦ (O, (sh_G, y)), over X/G (both triangles commute by
   definition); at O = [x] the second component y : G · x goes to
   (sh_G, y) : BG_x. `}
def orbit_fibs_map (G : Group) (X : GSet G)
  (t : Σ (Orbits G X) (O ↦ gset_underlying G (gsubset_gset G X (O .fst))))
  : Σ (Orbits G X) (O ↦ ActionType G (gsubset_gset G X (O .fst)))
  ≔ (t .fst, (shape G, t .snd))

def orbit_fibs_map_over (G : Group) (X : GSet G)
  (t : Σ (Orbits G X) (O ↦ gset_underlying G (gsubset_gset G X (O .fst))))
  : Id (Orbits G X) (orbit_fibs_map G X t .fst) (t .fst)
  ≔ refl (t .fst)

def orbit_fibs_horizontal (G : Group) (X : GSet G) (x : gset_underlying G X) (y : OrbitUnderlying G X x)
  : BG (stabilizer_group G X x) .carrier
  ≔ ((shape G, y .fst), orbit_map_path_to_mere G X (shape G, x) (shape G, y .fst) (y .snd))

def orbit_fibs_horizontal_fst (G : Group) (X : GSet G) (x : gset_underlying G X) (y : OrbitUnderlying G X x)
  : Id (ActionType G X) (orbit_fibs_horizontal G X x y .fst) (shape G, y .fst)
  ≔ refl ((shape G, y .fst) : ActionType G X)

{` xca:[x]=[y]-implies-||Gx=Gy||. If [x] = [y] then ‖G_x = G_y‖: a path
   (sh_G, x) = (sh_G, y) in X_hG gives G_x = G_y by application of
   u ↦ Aut_{X_hG}(u). `}
def stabilizer_groups_merely_equal (G : Group) (X : GSet G) (x y : gset_underlying G X)
  (p : Id (Orbits G X) (orbit_of_point G X x) (orbit_of_point G X y))
  : Mere (Id Group (stabilizer_group G X x) (stabilizer_group G X y))
  ≔ let T ≔ ActionType G X in
    trunc_map native_truncation (Id T (shape G, x) (shape G, y))
      (Id Group (stabilizer_group G X x) (stabilizer_group G X y))
      (map_path T Group (u ↦ automorphism_group T (action_type_groupoid G X) u) (shape G, x) (shape G, y))
      (orbit_point_path_mere_equiv G X x y .map p)

{` lem:free-pt-char. The map (- · x) : USym G → G · x, g ↦ (g · x, !). `}
def orbit_action_map (G : Group) (X : GSet G) (x : gset_underlying G X) (g : USym G) : OrbitUnderlying G X x
  ≔ let S ≔ gset_underlying G X in
    (gset_usym_act G X g x,
     orbit_relation_to_path G X x (gset_usym_act G X g x)
       (mere (Σ (USym G) (h ↦ Id S (gset_usym_act G X h x) (gset_usym_act G X g x)))
         (g, refl (gset_usym_act G X g x))))

def orbit_action_map_surjective (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Surjective (USym G) (OrbitUnderlying G X x) (orbit_action_map G X x)
  ≔ let S ≔ gset_underlying G X in
    let Or ≔ Orbits G X in
    y ↦
      let F ≔ BookFiber (USym G) (OrbitUnderlying G X x) (orbit_action_map G X x) y in
      mere_rec (Σ (USym G) (g ↦ Id S (gset_usym_act G X g x) (y .fst))) (Mere F) (mere_isprop F)
        (ge ↦ mere F (ge .fst,
          subtype_equal S (w ↦ Id Or (orbit_of_point G X x) (orbit_of_point G X w))
            (w ↦ orbits_set G X (orbit_of_point G X x) (orbit_of_point G X w))
            y (orbit_action_map G X x (ge .fst))
            (inverse S (gset_usym_act G X (ge .fst) x) (y .fst) (ge .snd))))
        (orbit_relation_from_path G X x (y .fst) (y .snd))
