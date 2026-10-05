export "701-abstract-homomorphisms"
export "600-wild-precategories"
export "284-chapter-two-completions"

{` Chapter 7 (absgroup.tex), rem:abs-iso and the exercise after it
   ("perform the abovementioned analysis"): identifications G = G' of
   abstract groups are isomorphisms of abstract groups.

   abstract_group_path_from_iso builds the identification directly: the
   carrier component is ua(f), and the unit, multiplication and inverse
   components are dependent identifications over ua(f), which in Narya are
   one-field records (unglue : f(a) = b). The laws component is a dependent
   identification in a family of propositions. abstract_group_path_to_iso
   transports along the carrier; the composite iso → path → iso is the
   identity on underlying maps by computation (transport along ua f is f),
   so the total space of isomorphisms out of G is a retract of the
   contractible total space of identifications, and path → iso is an
   equivalence (fundamental theorem of identity types). `}

{` The data (S, e, μ, ι) of an abstract group, without the laws. `}
def AbstractGroupData : Type ≔ Σ Type (S ↦ Σ S (e ↦ Σ (S → S → S) (m ↦ S → S)))

def abstract_group_data (G : AbstractGroup) : AbstractGroupData ≔ (G .carrier, (G .unit, (G .mul, G .inv)))

def AbstractGroupLawsAt (d : AbstractGroupData) : Type
  ≔ AbstractGroupLaws (d .fst) (d .snd .fst) (d .snd .snd .fst) (d .snd .snd .snd)

def abstract_group_laws_pathover (d d' : AbstractGroupData) (q : Id AbstractGroupData d d')
  (l : AbstractGroupLawsAt d) (l' : AbstractGroupLawsAt d') : Id AbstractGroupLawsAt q l l'
  ≔ pathover_hlevel zero. AbstractGroupData AbstractGroupLawsAt
      (d ↦ prop_to_hlevel_one (AbstractGroupLawsAt d)
        (abstract_group_laws_prop (d .fst) (d .snd .fst) (d .snd .snd .fst) (d .snd .snd .snd)))
      d d' q l l' .center

{` An identification of the data gives an identification of abstract
   groups (the laws are a proposition). `}
def abstract_group_path_of_data (G H : AbstractGroup)
  (q : Id AbstractGroupData (abstract_group_data G) (abstract_group_data H)) : Id AbstractGroup G H
  ≔ (q .fst, q .snd .fst, q .snd .snd .fst, q .snd .snd .snd,
     abstract_group_laws_pathover (abstract_group_data G) (abstract_group_data H) q (G .laws) (H .laws))

{` The data identification over ua(f) for an isomorphism f. `}
def abstract_group_data_path_from_iso (G H : AbstractGroup) (φ : AbstractIso G H)
  : Id AbstractGroupData (abstract_group_data G) (abstract_group_data H)
  ≔ let S ≔ G .carrier in let T ≔ H .carrier in let f ≔ φ .fst in let hf ≔ φ .snd in
    (ua S T f,
     ((unglue ≔ abstract_hom_preserves_unit G H (f .map) hf),
      (x y ⤇ (unglue ≔ concat T (f .map (G .mul x.0 y.0)) (H .mul (f .map x.0) (f .map y.0)) (H .mul x.1 y.1)
                (hf x.0 y.0) (refl (H .mul) (x.2 .unglue) (y.2 .unglue))),
       x ⤇ (unglue ≔ concat T (f .map (G .inv x.0)) (H .inv (f .map x.0)) (H .inv x.1)
                (abstract_hom_preserves_inv G H (f .map) hf x.0) (refl (H .inv) (x.2 .unglue))))))

{` rem:abs-iso: the identification of abstract groups obtained by
   univalence from an isomorphism. Its carrier component is ua(f). `}
def abstract_group_path_from_iso (G H : AbstractGroup) (φ : AbstractIso G H) : Id AbstractGroup G H
  ≔ abstract_group_path_of_data G H (abstract_group_data_path_from_iso G H φ)

def abstract_group_path_from_iso_carrier (G H : AbstractGroup) (φ : AbstractIso G H)
  : Id (Id Type (G .carrier) (H .carrier)) (abstract_group_path_from_iso G H φ .carrier) (ua (G .carrier) (H .carrier) (φ .fst))
  ≔ refl (ua (G .carrier) (H .carrier) (φ .fst))

{` A dependent identification over P : S = T gives an identification
   P(u) = v after transport. `}
def type_pathover_transport (S T : Type) (P : Id Type S T) (u : S) (v : T) (r : P u v) : Id T (P .trr u) v
  ≔ pathover_transport_equiv Type (X ↦ X) S T P u v .map r

{` The isomorphism underlying an identification: transport along the
   carrier, which preserves multiplication by the mul component. `}
def abstract_group_path_to_iso (G H : AbstractGroup) (p : Id AbstractGroup G H) : AbstractIso G H
  ≔ let P ≔ p .carrier in let S ≔ G .carrier in let T ≔ H .carrier in
    (transport_equiv S T P,
     s s' ↦ type_pathover_transport S T P (G .mul s s') (H .mul (P .trr s) (P .trr s'))
       (p .mul (P .liftr s) (P .liftr s')))

{` Isomorphisms are equal when their underlying maps are. `}
def abstract_iso_path (G H : AbstractGroup) (φ ψ : AbstractIso G H)
  (h : Id (G .carrier → H .carrier) (φ .fst .map) (ψ .fst .map)) : Id (AbstractIso G H) φ ψ
  ≔ subtype_equal (Equiv (G .carrier) (H .carrier)) (f ↦ IsAbstractHom G H (f .map))
      (f ↦ is_abstract_hom_prop G H (f .map)) φ ψ
      (equiv_path (G .carrier) (H .carrier) (φ .fst) (ψ .fst) h)

{` iso → path → iso is the identity (transport along ua f is f). `}
def abstract_group_iso_path_section (G H : AbstractGroup) (φ : AbstractIso G H)
  : Id (AbstractIso G H) (abstract_group_path_to_iso G H (abstract_group_path_from_iso G H φ)) φ
  ≔ abstract_iso_path G H (abstract_group_path_to_iso G H (abstract_group_path_from_iso G H φ)) φ
      (refl (φ .fst .map))

def abstract_group_iso_total_contractible (G : AbstractGroup) : isContr (Σ AbstractGroup (AbstractIso G))
  ≔ contractible_retract (Σ AbstractGroup (H ↦ Id AbstractGroup G H)) (Σ AbstractGroup (AbstractIso G))
      (iscontr_idfrom AbstractGroup G)
      (totalize AbstractGroup (H ↦ Id AbstractGroup G H) (AbstractIso G) (abstract_group_path_to_iso G))
      (totalize AbstractGroup (AbstractIso G) (H ↦ Id AbstractGroup G H) (abstract_group_path_from_iso G))
      (u ↦ (refl (u .fst), abstract_group_iso_path_section G (u .fst) (u .snd)))

def abstract_group_path_to_iso_is_equiv (G H : AbstractGroup)
  : isEquiv (Id AbstractGroup G H) (AbstractIso G H) (abstract_group_path_to_iso G H)
  ≔ fiberwise_from_total AbstractGroup (H ↦ Id AbstractGroup G H) (AbstractIso G) (abstract_group_path_to_iso G)
      (cat_contractible_map_is_equiv (Σ AbstractGroup (H ↦ Id AbstractGroup G H)) (Σ AbstractGroup (AbstractIso G))
        (totalize AbstractGroup (H ↦ Id AbstractGroup G H) (AbstractIso G) (abstract_group_path_to_iso G))
        (iscontr_idfrom AbstractGroup G) (abstract_group_iso_total_contractible G)) H

{` rem:abs-iso, exercise "perform the analysis": (G = G') ≃ Iso(G, G'). `}
def abstract_group_path_iso_equiv (G H : AbstractGroup) : Equiv (Id AbstractGroup G H) (AbstractIso G H)
  ≔ (abstract_group_path_to_iso G H, abstract_group_path_to_iso_is_equiv G H)

{` The printed form of the analysis: G = G' is equivalent to the type of
   identifications p : S = S' with e' = p(e) and μ'(p(s), p(t)) = p(μ(s, t)),
   where p(x) is transport along p. `}
def AbstractGroupPathEquations (G H : AbstractGroup) : Type
  ≔ Σ (Id Type (G .carrier) (H .carrier)) (p ↦
      Product (Id (H .carrier) (H .unit) (p .trr (G .unit)))
        ((s t : G .carrier) → Id (H .carrier) (H .mul (p .trr s) (p .trr t)) (p .trr (G .mul s t))))

def abstract_group_path_equations_equiv (G H : AbstractGroup)
  : Equiv (Id AbstractGroup G H) (AbstractGroupPathEquations G H)
  ≔ let S ≔ G .carrier in let T ≔ H .carrier in
    let C : Equiv S T → Type ≔ f ↦ Product (Id T (H .unit) (f .map (G .unit)))
        ((s t : S) → Id T (H .mul (f .map s) (f .map t)) (f .map (G .mul s t))) in
    compose_equiv (Id AbstractGroup G H) (AbstractIsoEquations G H) (AbstractGroupPathEquations G H)
      (compose_equiv (Id AbstractGroup G H) (AbstractIso G H) (AbstractIsoEquations G H)
        (abstract_group_path_iso_equiv G H) (abstract_iso_equations_equiv G H))
      (canonical_inverse_equiv (AbstractGroupPathEquations G H) (AbstractIsoEquations G H)
        (sigma_reindex_equiv (Id Type S T) (Equiv S T) (transport_univalence_equiv S T) C))

{` xca:typemonoidisgroupoid (abstract groups): the identity types of
   AbstractGroup are sets, so AbstractGroup is a groupoid. `}
def abstract_iso_set (G H : AbstractGroup) : isSet (AbstractIso G H)
  ≔ sigma_set (Equiv (G .carrier) (H .carrier)) (f ↦ IsAbstractHom G H (f .map))
      (equivalences_set (G .carrier) (H .carrier) (abstract_group_set H))
      (f ↦ prop_is_set (IsAbstractHom G H (f .map)) (is_abstract_hom_prop G H (f .map)))

def abstract_group_paths_set (G H : AbstractGroup) : isSet (Id AbstractGroup G H)
  ≔ hlevel_two_to_set (Id AbstractGroup G H)
      (hlevel_equiv (suc. (suc. zero.)) (AbstractIso G H) (Id AbstractGroup G H)
        (canonical_inverse_equiv (Id AbstractGroup G H) (AbstractIso G H) (abstract_group_path_iso_equiv G H))
        (set_to_hlevel_two (AbstractIso G H) (abstract_iso_set G H)))

def abstract_group_groupoid : isGroupoid AbstractGroup ≔ G H ↦ abstract_group_paths_set G H

{` Litmus: transport along the identification of an isomorphism is the
   isomorphism, by computation. `}
def abstract_group_path_from_iso_transport (G H : AbstractGroup) (φ : AbstractIso G H) (s : G .carrier)
  : Id (H .carrier) (abstract_group_path_from_iso G H φ .carrier .trr s) (φ .fst .map s)
  ≔ refl (φ .fst .map s)
