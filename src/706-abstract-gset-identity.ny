export "705-abstract-gsets"
export "600-wild-precategories"
export "287-chapter-two-text-claims"

{` Chapter 7 (absgroup.tex), proof of lem:Groupsareidentitytypes:
   identifications of G-sets (X, ·_X) = (Y, ·_Y) are the equivalences
   f : X ≃ Y commuting with the actions ("by def:pathover-trp and
   lem:isEq-pair= this is equivalent to Σ_f Π_g f ∘ post_x(g) = post_y(g) ∘ f").

   The map is transport in the family of underlying sets. It is an
   equivalence because the total space Σ_Y Iso(X, Y) is contractible: after
   reorganizing it as Σ_{(Z, e) : Σ_{Z : Set} X ≃ Z} Σ_{f : G → abstr(Σ_Z)} (e is
   equivariant), the base is contracted to (X, id) by univalence for sets,
   and the remaining type of G-set structures on X with the same action as
   X is an inhabited proposition (a symmetry in Σ_X is determined by its
   action). `}

{` The map (X = Y) → Iso(X, Y): its underlying function is transport in
   the family of underlying sets (so that it computes), and equivariance
   is proved by path induction (a proposition). `}
def agset_path_transport (G : AbstractGroup) (X Y : AbstractGSet G) (p : Id (AbstractGSet G) X Y)
  : agset_carrier G X → agset_carrier G Y
  ≔ transport (AbstractGSet G) (agset_carrier G) X Y p

def agset_path_transport_equivariant_refl (G : AbstractGroup) (X : AbstractGSet G)
  : AgsetEquivariant G X X (agset_path_transport G X X (refl X))
  ≔ let S ≔ agset_carrier G X in let tr ≔ agset_path_transport G X X (refl X) in
    s x ↦ concat S (tr (agset_act G X s x)) (agset_act G X s x) (agset_act G X s (tr x))
      (transport_refl (AbstractGSet G) (agset_carrier G) X (agset_act G X s x))
      (inverse S (agset_act G X s (tr x)) (agset_act G X s x)
        (refl (agset_act G X s) (transport_refl (AbstractGSet G) (agset_carrier G) X x)))

def agset_path_transport_equivariant (G : AbstractGroup) (X Y : AbstractGSet G) (p : Id (AbstractGSet G) X Y)
  : AgsetEquivariant G X Y (agset_path_transport G X Y p)
  ≔ J (AbstractGSet G) X (Y p ↦ AgsetEquivariant G X Y (agset_path_transport G X Y p))
      (agset_path_transport_equivariant_refl G X) Y p

def agset_path_to_iso (G : AbstractGroup) (X Y : AbstractGSet G) (p : Id (AbstractGSet G) X Y) : AbstractGSetIso G X Y
  ≔ (transport_equiv (agset_carrier G X) (agset_carrier G Y) (refl (agset_carrier G) p),
     agset_path_transport_equivariant G X Y p)

def agset_path_to_iso_map (G : AbstractGroup) (X Y : AbstractGSet G) (p : Id (AbstractGSet G) X Y) (x : agset_carrier G X)
  : Id (agset_carrier G Y) (agset_path_to_iso G X Y p .fst .map x) (agset_path_transport G X Y p x)
  ≔ refl (agset_path_transport G X Y p x)

{` Litmus: refl gives the identity map (transport along refl). `}
def agset_path_to_iso_refl_map (G : AbstractGroup) (X : AbstractGSet G) (x : agset_carrier G X)
  : Id (agset_carrier G X) (agset_path_to_iso G X X (refl X) .fst .map x) x
  ≔ transport_refl (AbstractGSet G) (agset_carrier G) X x

def agset_path_to_iso_refl (G : AbstractGroup) (X : AbstractGSet G)
  : Id (AbstractGSetIso G X X) (agset_iso_id G X) (agset_path_to_iso G X X (refl X))
  ≔ agset_iso_path G X X (agset_iso_id G X) (agset_path_to_iso G X X (refl X))
      (x ↦ inverse (agset_carrier G X) (agset_path_to_iso G X X (refl X) .fst .map x) x (agset_path_to_iso_refl_map G X x))

{` The layered form of the total space. `}
def AgsetCompatFamily (G : AbstractGroup) (X : AbstractGSet G)
  (W : Σ SetTypes (Z ↦ Equiv (agset_carrier G X) (Z .fst))) : Type
  ≔ Σ (AbstractHom G (abstr (permutation_group (W .fst)))) (f ↦
      (s : G .carrier) (x : agset_carrier G X)
      → Id (W .fst .fst) (W .snd .map (agset_act G X s x)) (permutation_action (W .fst) (f .fst s) (W .snd .map x)))

def AgsetIsoTotalLayered (G : AbstractGroup) (X : AbstractGSet G) : Type
  ≔ Σ (Σ SetTypes (Z ↦ Equiv (agset_carrier G X) (Z .fst))) (AgsetCompatFamily G X)

def agset_iso_total_reorganize (G : AbstractGroup) (X : AbstractGSet G)
  : Equiv (Σ (AbstractGSet G) (AbstractGSetIso G X)) (AgsetIsoTotalLayered G X)
  ≔ quasi_inverse_equiv (Σ (AbstractGSet G) (AbstractGSetIso G X)) (AgsetIsoTotalLayered G X)
      (u ↦ ((u .fst .fst, u .snd .fst), (u .fst .snd, u .snd .snd)))
      (w ↦ ((w .fst .fst, w .snd .fst), (w .fst .snd, w .snd .snd)))
      (u ↦ refl u) (w ↦ refl w)

{` Σ_{Z : Set} (A ≃ Z) is contractible, centred at any given point. `}
def agset_settypes_equiv_singleton (A : SetTypes) : isContr (Σ SetTypes (Z ↦ Equiv (A .fst) (Z .fst)))
  ≔ hlevel_equiv zero. (Σ SetTypes (Z ↦ Id SetTypes A Z)) (Σ SetTypes (Z ↦ Equiv (A .fst) (Z .fst)))
      (family_equiv SetTypes (Z ↦ Id SetTypes A Z) (Z ↦ Equiv (A .fst) (Z .fst)) (Z ↦ set_paths_equiv A Z))
      (iscontr_idfrom SetTypes A)

def agset_recenter (A : Type) (h : isContr A) (a0 : A) : isContr A
  ≔ (a0, a ↦ concat A a (h .center) a0 (h .contract a) (inverse A a0 (h .center) (h .contract a0)))

{` The fibre over (X, id): G-set structures on the set of X with the same
   action as X. It is an inhabited proposition. `}
def agset_compat_identity_prop (G : AbstractGroup) (X : AbstractGSet G)
  : isProp (AgsetCompatFamily G X (X .fst, identity_equiv (agset_carrier G X)))
  ≔ let A ≔ X .fst in let S ≔ A .fst in
    let P : AbstractHom G (abstr (permutation_group A)) → Type
      ≔ f ↦ (s : G .carrier) (x : S) → Id S (agset_act G X s x) (permutation_action A (f .fst s) x) in
    b1 b2 ↦ subtype_equal (AbstractHom G (abstr (permutation_group A))) P
      (f ↦ pi_prop (G .carrier) (s ↦ (x : S) → Id S (agset_act G X s x) (permutation_action A (f .fst s) x))
        (s ↦ pi_prop S (x ↦ Id S (agset_act G X s x) (permutation_action A (f .fst s) x))
          (x ↦ A .snd (agset_act G X s x) (permutation_action A (f .fst s) x))))
      b1 b2
      (agset_structure_ext G A (b1 .fst) (b2 .fst)
        (s x ↦ concat S (permutation_action A (b1 .fst .fst s) x) (agset_act G X s x) (permutation_action A (b2 .fst .fst s) x)
          (inverse S (agset_act G X s x) (permutation_action A (b1 .fst .fst s) x) (b1 .snd s x))
          (b2 .snd s x)))

def agset_compat_identity_contractible (G : AbstractGroup) (X : AbstractGSet G)
  : isContr (AgsetCompatFamily G X (X .fst, identity_equiv (agset_carrier G X)))
  ≔ let c : AgsetCompatFamily G X (X .fst, identity_equiv (agset_carrier G X))
      ≔ (X .snd, s x ↦ refl (agset_act G X s x)) in
    (c, b ↦ agset_compat_identity_prop G X b c)

def agset_iso_total_contractible (G : AbstractGroup) (X : AbstractGSet G)
  : isContr (Σ (AbstractGSet G) (AbstractGSetIso G X))
  ≔ let A ≔ X .fst in let S ≔ A .fst in
    let B ≔ Σ SetTypes (Z ↦ Equiv S (Z .fst)) in
    let w0 : B ≔ (A, identity_equiv S) in
    let e1 : Equiv (AgsetIsoTotalLayered G X) (AgsetCompatFamily G X w0)
      ≔ contractible_base_sigma_equiv B (AgsetCompatFamily G X) (agset_recenter B (agset_settypes_equiv_singleton A) w0) in
    hlevel_equiv zero. (AgsetCompatFamily G X w0) (Σ (AbstractGSet G) (AbstractGSetIso G X))
      (canonical_inverse_equiv (Σ (AbstractGSet G) (AbstractGSetIso G X)) (AgsetCompatFamily G X w0)
        (compose_equiv (Σ (AbstractGSet G) (AbstractGSetIso G X)) (AgsetIsoTotalLayered G X) (AgsetCompatFamily G X w0)
          (agset_iso_total_reorganize G X) e1))
      (agset_compat_identity_contractible G X)

def agset_path_to_iso_is_equiv (G : AbstractGroup) (X Y : AbstractGSet G)
  : isEquiv (Id (AbstractGSet G) X Y) (AbstractGSetIso G X Y) (agset_path_to_iso G X Y)
  ≔ fiberwise_from_total (AbstractGSet G) (Y ↦ Id (AbstractGSet G) X Y) (AbstractGSetIso G X) (agset_path_to_iso G X)
      (cat_contractible_map_is_equiv (Σ (AbstractGSet G) (Y ↦ Id (AbstractGSet G) X Y)) (Σ (AbstractGSet G) (AbstractGSetIso G X))
        (totalize (AbstractGSet G) (Y ↦ Id (AbstractGSet G) X Y) (AbstractGSetIso G X) (agset_path_to_iso G X))
        (iscontr_idfrom (AbstractGSet G) X) (agset_iso_total_contractible G X)) Y

{` (X = Y) ≃ Iso(X, Y) for G-sets. `}
def agset_path_iso_equiv (G : AbstractGroup) (X Y : AbstractGSet G)
  : Equiv (Id (AbstractGSet G) X Y) (AbstractGSetIso G X Y)
  ≔ (agset_path_to_iso G X Y, agset_path_to_iso_is_equiv G X Y)

def agset_path_from_iso (G : AbstractGroup) (X Y : AbstractGSet G) (f : AbstractGSetIso G X Y) : Id (AbstractGSet G) X Y
  ≔ equiv_inverse_map (Id (AbstractGSet G) X Y) (AbstractGSetIso G X Y) (agset_path_iso_equiv G X Y) f

def agset_path_from_iso_section (G : AbstractGroup) (X Y : AbstractGSet G) (f : AbstractGSetIso G X Y)
  : Id (AbstractGSetIso G X Y) (agset_path_to_iso G X Y (agset_path_from_iso G X Y f)) f
  ≔ equiv_counit (Id (AbstractGSet G) X Y) (AbstractGSetIso G X Y) (agset_path_iso_equiv G X Y) f

{` "Clearly, the types GSet and GTor are groupoids." `}
def agset_paths_set (G : AbstractGroup) (X Y : AbstractGSet G) : isSet (Id (AbstractGSet G) X Y)
  ≔ hlevel_two_to_set (Id (AbstractGSet G) X Y)
      (hlevel_equiv (suc. (suc. zero.)) (AbstractGSetIso G X Y) (Id (AbstractGSet G) X Y)
        (canonical_inverse_equiv (Id (AbstractGSet G) X Y) (AbstractGSetIso G X Y) (agset_path_iso_equiv G X Y))
        (set_to_hlevel_two (AbstractGSetIso G X Y) (agset_iso_set G X Y)))

def agset_groupoid (G : AbstractGroup) : isGroupoid (AbstractGSet G) ≔ X Y ↦ agset_paths_set G X Y

{` Composition of identifications corresponds to composition of
   isomorphisms: iso(p q) = iso(q) ∘ iso(p) (p first). `}
def agset_path_to_iso_concat (G : AbstractGroup) (X Y Z : AbstractGSet G) (p : Id (AbstractGSet G) X Y)
  (q : Id (AbstractGSet G) Y Z)
  : Id (AbstractGSetIso G X Z) (agset_path_to_iso G X Z (concat (AbstractGSet G) X Y Z p q))
      (agset_iso_compose G X Y Z (agset_path_to_iso G X Y p) (agset_path_to_iso G Y Z q))
  ≔ agset_iso_path G X Z (agset_path_to_iso G X Z (concat (AbstractGSet G) X Y Z p q))
      (agset_iso_compose G X Y Z (agset_path_to_iso G X Y p) (agset_path_to_iso G Y Z q))
      (x ↦ transport_concat (AbstractGSet G) (agset_carrier G) X Y Z p q x)
