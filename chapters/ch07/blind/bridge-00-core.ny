export "03-torsors"
export "../../../src/709-groups-are-abstract-groups"
export "../../../src/410-pointed-connected-groupoids"

{` Bridges for absgroup.tex: definition bridges shared by all bridge
   files.

   BlindAbsGroup (laws as the nested Σ MonoidLaws × InverseLaw) and our
   record AbstractGroup (laws as the 5-field record of module 403) are
   inverse up to η, so bridge_def_abs_group is an equivalence with refl round
   trips, blind_abstr G maps to abstr G by refl, and the blind notions of
   homomorphism, G-set and action are ours definitionally (checked by refl).
   The blind principal torsor and blind_gset_of_action use other proof terms
   for the inverse of an action than our agset_from_action, so they agree
   with ours up to a path (same set, same action), and so do the torsor
   types and concr. `}

def bridge_ag7 (G : BlindAbsGroup) : AbstractGroup
  ≔ (G .carrier, G .unit, G .mul, G .inv,
     (carrier_set ≔ G .laws .fst .fst,
      unit_right ≔ g ↦ G .laws .fst .snd .fst g .fst,
      unit_left ≔ g ↦ G .laws .fst .snd .fst g .snd,
      assoc ≔ G .laws .fst .snd .snd,
      inv_right ≔ G .laws .snd))

def bridge_ag7_inv (G : AbstractGroup) : BlindAbsGroup
  ≔ (G .carrier, G .unit, G .mul, G .inv, group_laws_from_record (G .carrier) (G .unit) (G .mul) (G .inv) (G .laws))

{` def:type-abstrgp. `}
def bridge_def_abs_group : Equiv BlindAbsGroup AbstractGroup
  ≔ quasi_inverse_equiv BlindAbsGroup AbstractGroup bridge_ag7 bridge_ag7_inv (G ↦ refl G) (G ↦ refl G)

def bridge_def_group_laws (S : Type) (e : S) (mu : S → S → S) (iota : S → S)
  : Id Type (BlindGroupLaws S e mu iota) (GroupLaws S e mu iota)
  ≔ refl (GroupLaws S e mu iota)

{` def:monoid. `}
def bridge_def_monoid : Equiv BlindMonoid Monoid
  ≔ quasi_inverse_equiv BlindMonoid Monoid (M ↦ (M .carrier, M .unit, M .mul, M .laws))
      (M ↦ (M .carrier, M .unit, M .mul, M .laws)) (M ↦ refl M) (M ↦ refl M)

{` def:abstrG: blind_abstr is abstr on the nose. `}
def bridge_def_abstr7 (G : Group) : Id AbstractGroup (bridge_ag7 (blind_abstr G)) (abstr G) ≔ refl (abstr G)

def bridge_def_abstr_inv (G : Group) : Id BlindAbsGroup (blind_abstr G) (bridge_ag7_inv (abstr G))
  ≔ refl (blind_abstr G)

{` def:abstrisfunctor. `}
def bridge_def_abs_hom (G H : BlindAbsGroup) : Id Type (BlindAbsHom G H) (AbstractHom (bridge_ag7 G) (bridge_ag7 H))
  ≔ refl (BlindAbsHom G H)

def bridge_def_abstr_hom (G H : Group) (f : GroupHom G H)
  : Id (AbstractHom (abstr G) (abstr H)) (blind_abstr_hom G H f) (abstr_hom G H f)
  ≔ refl (abstr_hom G H f)

{` def:abstrGtorsors: G-sets and their actions. `}
def bridge_def_gset7 (G : BlindAbsGroup) : Id Type (BlindAbsGSet G) (AbstractGSet (bridge_ag7 G))
  ≔ refl (BlindAbsGSet G)

def bridge_def_gset_act (G : BlindAbsGroup) (X : BlindAbsGSet G) (s : G .carrier) (x : X .fst .fst)
  : Id (X .fst .fst) (blind_gset_act G X s x) (agset_act (bridge_ag7 G) X s x)
  ≔ refl (blind_gset_act G X s x)

{` The blind G-set built from an action is ours built from the same action. `}
def bridge_gofa_path (G : BlindAbsGroup) (X : SetTypes) (act : G .carrier → X .fst → X .fst)
  (am : (g h : G .carrier) (x : X .fst) → Id (X .fst) (act (G .mul g h) x) (act g (act h x)))
  (au : (x : X .fst) → Id (X .fst) (act (G .unit) x) x)
  : Id (AbstractGSet (bridge_ag7 G)) (blind_gset_of_action G X act am au) (agset_from_action (bridge_ag7 G) X act am au)
  ≔ (refl X,
     agset_structure_ext (bridge_ag7 G) X (blind_gset_of_action G X act am au .snd)
       (agset_from_action (bridge_ag7 G) X act am au .snd) (s x ↦ refl (act s x)))

{` The principal torsor. `}
def bridge_principal_path (G : BlindAbsGroup)
  : Id (AbstractGSet (bridge_ag7 G)) (blind_abs_principal G) (agset_principal (bridge_ag7 G))
  ≔ bridge_gofa_path G (G .carrier, blind_ag_set G) (G .mul)
      (g h x ↦ inverse (G .carrier) (G .mul g (G .mul h x)) (G .mul (G .mul g h) x) (blind_ag_assoc G g h x))
      (blind_ag_lunit G)

{` Components of a groupoid at two identified points. `}
def bridge_component_map (A : Type) (a b : A) (p : Id A a b) (u : NativeComponent A a) : NativeComponent A b
  ≔ (u .fst, mere_rec (Id A a (u .fst)) (Mere (Id A b (u .fst))) (mere_isprop (Id A b (u .fst)))
      (q ↦ mere (Id A b (u .fst)) (concat A b a (u .fst) (inverse A a b p) q)) (u .snd))

def bridge_component_equiv (A : Type) (a b : A) (p : Id A a b) : Equiv (NativeComponent A a) (NativeComponent A b)
  ≔ quasi_inverse_equiv (NativeComponent A a) (NativeComponent A b)
      (bridge_component_map A a b p) (bridge_component_map A b a (inverse A a b p))
      (u ↦ component_path A a (bridge_component_map A b a (inverse A a b p) (bridge_component_map A a b p u)) u
        (refl (u .fst)))
      (u ↦ component_path A b (bridge_component_map A a b p (bridge_component_map A b a (inverse A a b p) u)) u
        (refl (u .fst)))

{` def:abstrGtorsors: torsors. `}
def bridge_def_torsor (G : BlindAbsGroup) : Equiv (BlindAbsTorsor G) (AbstractTorsors (bridge_ag7 G))
  ≔ bridge_component_equiv (AbstractGSet (bridge_ag7 G)) (blind_abs_principal G) (agset_principal (bridge_ag7 G))
      (bridge_principal_path G)

{` def:concr. `}
def bridge_component_group_path (A : Type) (hA : isGroupoid A) (a b : A) (p : Id A a b)
  : Id Group (automorphism_group A hA a) (automorphism_group A hA b)
  ≔ refl (x ↦ automorphism_group A hA x) p

def bridge_concr_path (G : BlindAbsGroup) : Id Group (blind_concr G) (concr (bridge_ag7 G))
  ≔ let G' ≔ bridge_ag7 G in let A ≔ AbstractGSet G' in let P ≔ agset_principal G' in
    let hb ≔ blind_abs_gset_groupoid G in
    concat Group (blind_concr G) (automorphism_group A hb P) (concr G')
      (bridge_component_group_path A hb (blind_abs_principal G) P (bridge_principal_path G))
      (classifying ≔ pcg_witnesses_unique (NativeComponent A P) (component_point A P)
        (native_component_connected A P) (abstract_torsors_connected G')
        (component_groupoid A hb P) (abstract_torsors_groupoid G'))

{` Homotopy invariance of BookIsEquiv. `}
def bridge_book_equiv_homotopic (A B : Type) (e : BookEquiv A B) (f : A → B) (h : (a : A) → Id B (e .map a) (f a))
  : BookIsEquiv A B f
  ≔ transport (A → B) (BookIsEquiv A B) (e .map) f (funext A (_ ↦ B) (e .map) f h) (e .equiv)

def bridge_book_equiv_compose (A B C : Type) (e : BookEquiv A B) (d : BookEquiv B C) : BookEquiv A C
  ≔ book_equivalence A C (compose_equiv A B C (native_equivalence A B e) (native_equivalence B C d))

def bridge_book_equiv_of (A B : Type) (e : Equiv A B) : BookEquiv A B ≔ book_equivalence A B e

{` Paths of abstract groups. `}
def bridge_ag_paths (G H : BlindAbsGroup) : Equiv (Id BlindAbsGroup G H) (Id AbstractGroup (bridge_ag7 G) (bridge_ag7 H))
  ≔ quasi_inverse_equiv (Id BlindAbsGroup G H) (Id AbstractGroup (bridge_ag7 G) (bridge_ag7 H))
      (p ↦ refl bridge_ag7 p) (p ↦ refl bridge_ag7_inv p) (p ↦ refl p) (p ↦ refl p)

def bridge_ag_transport_carrier (G H : BlindAbsGroup) (p : Id BlindAbsGroup G H) (s : G .carrier)
  : Id (H .carrier) (transport BlindAbsGroup (K ↦ K .carrier) G H p s)
      (transport AbstractGroup (K ↦ K .carrier) (bridge_ag7 G) (bridge_ag7 H) (refl bridge_ag7 p) s)
  ≔ refl (transport BlindAbsGroup (K ↦ K .carrier) G H p s)
