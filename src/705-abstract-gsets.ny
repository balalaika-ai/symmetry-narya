export "701-abstract-homomorphisms"
export "404-group-examples"

{` Chapter 7 (absgroup.tex), sec:Gsetforabstract: G-sets of an abstract
   group G = (S, e, μ, ι) (def:abstrGtorsors), their action, the principal
   G-torsor, maps of G-sets (def:Hom-absG) and isomorphisms of G-sets.

   A G-set is literally a pair (X, ·_X) of a set X and an abstract
   homomorphism ·_X : G → abstr(Σ_X). For s : S the symmetry s ·_X of X in
   Σ_X acts on x : X by transport (permutation_action of module 404); this
   is the book's s ·_X x (footnote to def:abstrGtorsors). `}

def AbstractGSet (G : AbstractGroup) : Type ≔ Σ SetTypes (X ↦ AbstractHom G (abstr (permutation_group X)))

def agset_carrier (G : AbstractGroup) (X : AbstractGSet G) : Type ≔ X .fst .fst

def agset_carrier_set (G : AbstractGroup) (X : AbstractGSet G) : isSet (agset_carrier G X) ≔ X .fst .snd

{` s ·_X x. `}
def agset_act (G : AbstractGroup) (X : AbstractGSet G) (s : G .carrier) (x : agset_carrier G X) : agset_carrier G X
  ≔ permutation_action (X .fst) (X .snd .fst s) x

{` The action laws: (s · t) ·_X x = s ·_X (t ·_X x) and e ·_X x = x. `}
def agset_act_mul (G : AbstractGroup) (X : AbstractGSet G) (s t : G .carrier) (x : agset_carrier G X)
  : Id (agset_carrier G X) (agset_act G X (G .mul s t) x) (agset_act G X s (agset_act G X t x))
  ≔ let P ≔ permutation_group (X .fst) in let h ≔ X .snd .fst in
    concat (X .fst .fst) (agset_act G X (G .mul s t) x) (permutation_action (X .fst) (usym_mul P (h s) (h t)) x)
      (agset_act G X s (agset_act G X t x))
      (refl ((q ↦ permutation_action (X .fst) q x) : USym P → X .fst .fst) (X .snd .snd s t))
      (permutation_action_mul (X .fst) (h s) (h t) x)

def agset_act_unit (G : AbstractGroup) (X : AbstractGSet G) (x : agset_carrier G X)
  : Id (agset_carrier G X) (agset_act G X (G .unit) x) x
  ≔ let P ≔ permutation_group (X .fst) in let h ≔ X .snd .fst in
    concat (X .fst .fst) (agset_act G X (G .unit) x) (permutation_action (X .fst) (usym_unit P) x) x
      (refl ((q ↦ permutation_action (X .fst) q x) : USym P → X .fst .fst)
        (abstract_hom_preserves_unit G (abstr P) h (X .snd .snd)))
      (permutation_action_unit (X .fst) x)

{` Two symmetries of S in Σ_S with the same action are equal. This is
   permutation_symmetry_ext of module 434, repeated here (same proof) so
   that the chapter-7 core does not import modules 406 and 431–434. `}
def agset_permutation_symmetry_ext (S : SetTypes) (g h : USym (permutation_group S))
  (H : (x : S .fst) → Id (S .fst) (permutation_action S g x) (permutation_action S h x))
  : Id (USym (permutation_group S)) g h
  ≔ let X ≔ S .fst in
    let E ≔ permutation_group_usym_equiv S in
    equivalence_injective (USym (permutation_group S)) (Equiv X X) E g h
      (equiv_path X X (E .map g) (E .map h)
        (funext X (_ ↦ X) (E .map g .map) (E .map h .map)
          (x ↦ concat X (E .map g .map x) (permutation_action S g x) (E .map h .map x)
            (id_to_equiv_transport X X (g .fst .fst) x)
            (concat X (permutation_action S g x) (permutation_action S h x) (E .map h .map x)
              (H x)
              (inverse X (E .map h .map x) (permutation_action S h x) (id_to_equiv_transport X X (h .fst .fst) x))))))

{` Two G-set structures on the same set with the same action are equal. `}
def agset_structure_ext (G : AbstractGroup) (X : SetTypes) (f g : AbstractHom G (abstr (permutation_group X)))
  (H : (s : G .carrier) (x : X .fst) → Id (X .fst) (permutation_action X (f .fst s) x) (permutation_action X (g .fst s) x))
  : Id (AbstractHom G (abstr (permutation_group X))) f g
  ≔ abstract_hom_ext G (abstr (permutation_group X)) f g
      (s ↦ agset_permutation_symmetry_ext X (f .fst s) (g .fst s) (H s))

{` A G-set from an action s ↦ (x ↦ s · x) satisfying the action laws;
   its action is the given one by refl. `}
def agset_action_equiv (G : AbstractGroup) (X : SetTypes) (act : G .carrier → X .fst → X .fst)
  (hmul : (s t : G .carrier) (x : X .fst) → Id (X .fst) (act (G .mul s t) x) (act s (act t x)))
  (hunit : (x : X .fst) → Id (X .fst) (act (G .unit) x) x) (s : G .carrier)
  : Equiv (X .fst) (X .fst)
  ≔ let A ≔ X .fst in let is ≔ G .inv s in
    quasi_inverse_equiv A A (act s) (act is)
      (x ↦ calc
         act is (act s x) = act (G .mul is s) x by inverse A (act (G .mul is s) x) (act is (act s x)) (hmul is s x)
         = act (G .unit) x by refl ((u ↦ act u x) : G .carrier → A) (ag_inv_left G s)
         = x by hunit x ∎)
      (x ↦ calc
         act s (act is x) = act (G .mul s is) x by inverse A (act (G .mul s is) x) (act s (act is x)) (hmul s is x)
         = act (G .unit) x by refl ((u ↦ act u x) : G .carrier → A) (G .laws .inv_right s)
         = x by hunit x ∎)

def agset_from_action (G : AbstractGroup) (X : SetTypes) (act : G .carrier → X .fst → X .fst)
  (hmul : (s t : G .carrier) (x : X .fst) → Id (X .fst) (act (G .mul s t) x) (act s (act t x)))
  (hunit : (x : X .fst) → Id (X .fst) (act (G .unit) x) x)
  : AbstractGSet G
  ≔ let P ≔ permutation_group X in
    let symf : G .carrier → USym P ≔ s ↦ permutation_symmetry X (agset_action_equiv G X act hmul hunit s) in
    (X, (symf,
         s t ↦ agset_permutation_symmetry_ext X (symf (G .mul s t)) (usym_mul P (symf s) (symf t))
           (x ↦ concat (X .fst) (act (G .mul s t) x) (act s (act t x)) (permutation_action X (usym_mul P (symf s) (symf t)) x)
             (hmul s t x)
             (inverse (X .fst) (permutation_action X (usym_mul P (symf s) (symf t)) x) (act s (act t x))
               (permutation_action_mul X (symf s) (symf t) x)))))

def agset_from_action_act (G : AbstractGroup) (X : SetTypes) (act : G .carrier → X .fst → X .fst)
  (hmul : (s t : G .carrier) (x : X .fst) → Id (X .fst) (act (G .mul s t) x) (act s (act t x)))
  (hunit : (x : X .fst) → Id (X .fst) (act (G .unit) x) x) (s : G .carrier) (x : X .fst)
  : Id (X .fst) (agset_act G (agset_from_action G X act hmul hunit) s x) (act s x)
  ≔ refl (act s x)

{` def:abstrGtorsors: the principal G-torsor (S, g ↦ (s ↦ μ(g, s))). `}
def agset_principal (G : AbstractGroup) : AbstractGSet G
  ≔ agset_from_action G (G .carrier, abstract_group_set G) (s x ↦ G .mul s x)
      (s t x ↦ inverse (G .carrier) (G .mul s (G .mul t x)) (G .mul (G .mul s t) x) (G .laws .assoc s t x))
      (x ↦ G .laws .unit_left x)

def agset_principal_act (G : AbstractGroup) (s x : G .carrier)
  : Id (G .carrier) (agset_act G (agset_principal G) s x) (G .mul s x)
  ≔ refl (G .mul s x)

{` def:Hom-absG. Maps of G-sets, with the printed equation of functions
   f ∘ (s ·_X -) = (s ·_Y -) ∘ f. `}
def AbstractGSetHom (G : AbstractGroup) (X Y : AbstractGSet G) : Type
  ≔ Σ (agset_carrier G X → agset_carrier G Y) (f ↦
      (s : G .carrier) → Id (agset_carrier G X → agset_carrier G Y)
        (x ↦ f (agset_act G X s x)) (x ↦ agset_act G Y s (f x)))

{` Isomorphisms of G-sets: equivalences commuting with the actions
   (pointwise form, as in the proof of lem:Groupsareidentitytypes). `}
def AgsetEquivariant (G : AbstractGroup) (X Y : AbstractGSet G) (f : agset_carrier G X → agset_carrier G Y) : Type
  ≔ (s : G .carrier) (x : agset_carrier G X) → Id (agset_carrier G Y) (f (agset_act G X s x)) (agset_act G Y s (f x))

def agset_equivariant_prop (G : AbstractGroup) (X Y : AbstractGSet G) (f : agset_carrier G X → agset_carrier G Y)
  : isProp (AgsetEquivariant G X Y f)
  ≔ pi_prop (G .carrier) (s ↦ (x : agset_carrier G X) → Id (agset_carrier G Y) (f (agset_act G X s x)) (agset_act G Y s (f x)))
      (s ↦ pi_prop (agset_carrier G X) (x ↦ Id (agset_carrier G Y) (f (agset_act G X s x)) (agset_act G Y s (f x)))
        (x ↦ agset_carrier_set G Y (f (agset_act G X s x)) (agset_act G Y s (f x))))

def AbstractGSetIso (G : AbstractGroup) (X Y : AbstractGSet G) : Type
  ≔ Σ (Equiv (agset_carrier G X) (agset_carrier G Y)) (e ↦ AgsetEquivariant G X Y (e .map))

def agset_iso_id (G : AbstractGroup) (X : AbstractGSet G) : AbstractGSetIso G X X
  ≔ (identity_equiv (agset_carrier G X), s x ↦ refl (agset_act G X s x))

{` agset_iso_compose G X Y Z f g is g ∘ f. `}
def agset_iso_compose (G : AbstractGroup) (X Y Z : AbstractGSet G) (f : AbstractGSetIso G X Y) (g : AbstractGSetIso G Y Z)
  : AbstractGSetIso G X Z
  ≔ (compose_equiv (agset_carrier G X) (agset_carrier G Y) (agset_carrier G Z) (f .fst) (g .fst),
     s x ↦ concat (agset_carrier G Z) (g .fst .map (f .fst .map (agset_act G X s x)))
       (g .fst .map (agset_act G Y s (f .fst .map x))) (agset_act G Z s (g .fst .map (f .fst .map x)))
       (refl (g .fst .map) (f .snd s x)) (g .snd s (f .fst .map x)))

def agset_iso_path (G : AbstractGroup) (X Y : AbstractGSet G) (f g : AbstractGSetIso G X Y)
  (h : (x : agset_carrier G X) → Id (agset_carrier G Y) (f .fst .map x) (g .fst .map x))
  : Id (AbstractGSetIso G X Y) f g
  ≔ subtype_equal (Equiv (agset_carrier G X) (agset_carrier G Y)) (e ↦ AgsetEquivariant G X Y (e .map))
      (e ↦ agset_equivariant_prop G X Y (e .map)) f g
      (equiv_homotopy (agset_carrier G X) (agset_carrier G Y) (f .fst) (g .fst) h)

def agset_iso_set (G : AbstractGroup) (X Y : AbstractGSet G) : isSet (AbstractGSetIso G X Y)
  ≔ sigma_set (Equiv (agset_carrier G X) (agset_carrier G Y)) (e ↦ AgsetEquivariant G X Y (e .map))
      (equivalences_set (agset_carrier G X) (agset_carrier G Y) (agset_carrier_set G Y))
      (e ↦ prop_is_set (AgsetEquivariant G X Y (e .map)) (agset_equivariant_prop G X Y (e .map)))

{` The underlying map of a G-set isomorphism, as an element of
   Hom_G(X, Y) of def:Hom-absG. `}
def agset_iso_hom (G : AbstractGroup) (X Y : AbstractGSet G) (f : AbstractGSetIso G X Y) : AbstractGSetHom G X Y
  ≔ (f .fst .map,
     s ↦ funext (agset_carrier G X) (_ ↦ agset_carrier G Y) (x ↦ f .fst .map (agset_act G X s x))
       (x ↦ agset_act G Y s (f .fst .map x)) (f .snd s))

{` Litmus: in the principal torsor of the abstract group of a group G,
   g acts by left multiplication g · h = concat h g. `}
def agset_principal_abstr_act (G : Group) (g h : USym G)
  : Id (USym G) (agset_act (abstr G) (agset_principal (abstr G)) g h) (concat (BG G .carrier) (shape G) (shape G) (shape G) h g)
  ≔ refl (concat (BG G .carrier) (shape G) (shape G) (shape G) h g)
