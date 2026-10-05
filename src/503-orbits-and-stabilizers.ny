export "502-subgroups"

{` Chapter 5, sec:fixpts-orbits: invariant maps, the set of orbits X/G,
   the orbit maps [-]_0 and [-] (def:actiontype, def:orbit-map,
   lem:[]0-maps-to-X/G), stabilizer groups and orbits of elements
   (def:orbit-stabilizer), fixed and free elements (def:fixed-free).
   The action type X_hG is ActionType (module 501). `}

{` def:actiontype (2). The type of invariant maps X^hG ≔ Π_{z:BG} X(z). `}
def InvariantMaps (G : Group) (X : GSet G) : Type ≔ (z : BG G .carrier) → X z .fst

def invariant_maps_set (G : Group) (X : GSet G) : isSet (InvariantMaps G X)
  ≔ pi_set (BG G .carrier) (z ↦ X z .fst) (z ↦ X z .snd)

{` def:actiontype (3). The set of orbits
   X/G ≔ Σ_{P : Sub_G(X)} istrans(X_P). `}
def Orbits (G : Group) (X : GSet G) : Type
  ≔ Σ (GSubsets G X) (P ↦ IsTransitive G (gsubset_gset G X P))

def orbits_set (G : Group) (X : GSet G) : isSet (Orbits G X)
  ≔ hlevel_two_to_set (Orbits G X)
      (hlevel_sigma (suc. (suc. zero.)) (GSubsets G X) (P ↦ IsTransitive G (gsubset_gset G X P))
        (set_to_hlevel_two (GSubsets G X) (gsubsets_set G X))
        (P ↦ hlevel_raise (suc. zero.) (IsTransitive G (gsubset_gset G X P))
          (prop_to_hlevel_one (IsTransitive G (gsubset_gset G X P)) (is_transitive_prop G (gsubset_gset G X P)))))

{` Orbits are determined by their G-subsets. `}
def orbit_path (G : Group) (X : GSet G) (O O' : Orbits G X) (p : Id (GSubsets G X) (O .fst) (O' .fst))
  : Id (Orbits G X) O O'
  ≔ subtype_equal (GSubsets G X) (P ↦ IsTransitive G (gsubset_gset G X P))
      (P ↦ is_transitive_prop G (gsubset_gset G X P)) O O' p

{` def:orbit-map. [u]_0 is the G-subset z ↦ (x ↦ ‖u = (z, x)‖). `}
def orbit_subset (G : Group) (X : GSet G) (u : ActionType G X) : GSubsets G X
  ≔ z x ↦ (Mere (Id (ActionType G X) u (z, x)), mere_isprop (Id (ActionType G X) u (z, x)))

{` The underlying G-set X_{[u]_0}(z) = Σ_{x:X(z)} ‖u = (z, x)‖ of the orbit
   through u. Its action type is the component of u in X_hG. `}
def orbit_gset (G : Group) (X : GSet G) (u : ActionType G X) : GSet G
  ≔ gsubset_gset G X (orbit_subset G X u)

def orbit_gset_component_equiv (G : Group) (X : GSet G) (u : ActionType G X)
  : Equiv (ActionType G (orbit_gset G X u)) (NativeComponent (ActionType G X) u)
  ≔ quasi_inverse_equiv (ActionType G (orbit_gset G X u)) (NativeComponent (ActionType G X) u)
      (v ↦ ((v .fst, v .snd .fst), v .snd .snd)) (c ↦ (c .fst .fst, (c .fst .snd, c .snd)))
      (v ↦ refl v) (c ↦ refl c)

{` lem:[]0-maps-to-X/G. The underlying G-set of [u]_0 is transitive. `}
def orbit_gset_transitive (G : Group) (X : GSet G) (u : ActionType G X)
  : IsTransitive G (orbit_gset G X u)
  ≔ connected_action_type_transitive G (orbit_gset G X u)
      (connected_equiv (NativeComponent (ActionType G X) u) (ActionType G (orbit_gset G X u))
        (canonical_inverse_equiv (ActionType G (orbit_gset G X u)) (NativeComponent (ActionType G X) u)
          (orbit_gset_component_equiv G X u))
        .map (native_component_connected (ActionType G X) u))

{` The orbit map [-]_0 : X_hG → X/G, the orbit through u. `}
def orbit_map (G : Group) (X : GSet G) (u : ActionType G X) : Orbits G X
  ≔ (orbit_subset G X u, orbit_gset_transitive G X u)

{` cor:orbit-equiv. [x] ≔ [(sh_G, x)]_0 for x : X(sh_G), the orbit through x. `}
def orbit_of_point (G : Group) (X : GSet G) (x : gset_underlying G X) : Orbits G X
  ≔ orbit_map G X (shape G, x)

{` def:orbit-stabilizer (1). The stabilizer group G_x ≔ Aut_{X_hG}(sh_G, x),
   with i_x : Hom(G_x, G) classified by fst (pointed by reflexivity), a
   monomorphism since fst : BG_x → BG is a covering (the component
   inclusion and Tot(X) → BG are coverings). `}
def stabilizer_group (G : Group) (X : GSet G) (x : gset_underlying G X) : Group
  ≔ automorphism_group (ActionType G X) (action_type_groupoid G X) (shape G, x)

def stabilizer_group_classifying (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Id Type (BG (stabilizer_group G X x) .carrier) (NativeComponent (ActionType G X) (shape G, x))
  ≔ refl (NativeComponent (ActionType G X) (shape G, x))

def stabilizer_inclusion (G : Group) (X : GSet G) (x : gset_underlying G X)
  : GroupHom (stabilizer_group G X x) G
  ≔ mkhom (stabilizer_group G X x) G (c ↦ c .fst .fst, refl (shape G))

def stabilizer_component_covering (A : Type) (a : A)
  : IsCovering (NativeComponent A a) A (c ↦ c .fst)
  ≔ setfamily_to_covering A (x ↦ (Mere (Id A a x), prop_is_set (Mere (Id A a x)) (mere_isprop (Id A a x)))) .snd

def stabilizer_inclusion_covering (G : Group) (X : GSet G) (x : gset_underlying G X)
  : IsCovering (BG (stabilizer_group G X x) .carrier) (BG G .carrier)
      (hom_function (stabilizer_group G X x) G (stabilizer_inclusion G X x))
  ≔ coverings_compose (NativeComponent (ActionType G X) (shape G, x)) (ActionType G X) (BG G .carrier)
      (c ↦ c .fst) (u ↦ u .fst)
      (stabilizer_component_covering (ActionType G X) (shape G, x))
      (action_type_projection_covering G X)

def stabilizer_inclusion_mono (G : Group) (X : GSet G) (x : gset_underlying G X)
  : IsGroupMono (stabilizer_group G X x) G (stabilizer_inclusion G X x)
  ≔ covering_group_mono (stabilizer_group G X x) G (stabilizer_inclusion G X x)
      (stabilizer_inclusion_covering G X x)

def stabilizer_mono (G : Group) (X : GSet G) (x : gset_underlying G X) : GroupMonos G
  ≔ (stabilizer_group G X x, (stabilizer_inclusion G X x, stabilizer_inclusion_mono G X x))

{` def:orbit-stabilizer (2). G · x ≔ {y : X(sh_G) | [x] = [y]}, the
   underlying set of the orbit through x. `}
def OrbitUnderlying (G : Group) (X : GSet G) (x : gset_underlying G X) : Type
  ≔ Σ (gset_underlying G X) (y ↦ Id (Orbits G X) (orbit_of_point G X x) (orbit_of_point G X y))

def orbit_underlying_set (G : Group) (X : GSet G) (x : gset_underlying G X) : isSet (OrbitUnderlying G X x)
  ≔ sigma_set (gset_underlying G X) (y ↦ Id (Orbits G X) (orbit_of_point G X x) (orbit_of_point G X y))
      (gset_underlying_set G X)
      (y ↦ prop_is_set (Id (Orbits G X) (orbit_of_point G X x) (orbit_of_point G X y))
        (orbits_set G X (orbit_of_point G X x) (orbit_of_point G X y)))

{` def:fixed-free. x is fixed if i_x is an isomorphism, free if G_x is
   trivial (BG_x contractible, see IsTrivialGroup); X is free if every
   element of X(sh_G) is free. `}
def IsFixedElement (G : Group) (X : GSet G) (x : gset_underlying G X) : Type
  ≔ IsGroupIso (stabilizer_group G X x) G (stabilizer_inclusion G X x)

def is_fixed_element_prop (G : Group) (X : GSet G) (x : gset_underlying G X) : isProp (IsFixedElement G X x)
  ≔ is_group_iso_prop (stabilizer_group G X x) G (stabilizer_inclusion G X x)

def IsFreeElement (G : Group) (X : GSet G) (x : gset_underlying G X) : Type
  ≔ IsTrivialGroup (stabilizer_group G X x)

def is_free_element_prop (G : Group) (X : GSet G) (x : gset_underlying G X) : isProp (IsFreeElement G X x)
  ≔ is_trivial_group_prop (stabilizer_group G X x)

def IsFreeGSet (G : Group) (X : GSet G) : Type ≔ (x : gset_underlying G X) → IsFreeElement G X x

def is_free_gset_prop (G : Group) (X : GSet G) : isProp (IsFreeGSet G X)
  ≔ pi_prop (gset_underlying G X) (x ↦ IsFreeElement G X x) (x ↦ is_free_element_prop G X x)

{` lem:burnside. X^g ≔ {x : X(sh_G) | g · x = x}, the points fixed by g. `}
def FixedBy (G : Group) (X : GSet G) (g : USym G) : Type
  ≔ Σ (gset_underlying G X) (x ↦ Id (gset_underlying G X) (gset_usym_act G X g x) x)
