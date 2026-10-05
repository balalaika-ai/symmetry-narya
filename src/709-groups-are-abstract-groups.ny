export "708-concr-of-abstr"
export "702-abstract-group-identity"

{` Chapter 7 (absgroup.tex), thm:Groupsareidentitytypes: abstr : Group →
   AbstractGroup is an equivalence, with inverse concr. One round trip is
   lem:Groupsareidentitytypes (concr_abstr_path, module 708). For the other,
   the book's r_G : S ≃ (P_G = P_G) is promoted to an isomorphism of
   abstract groups G ≅ abstr(concr(G)): the symmetries of the principal
   torsor are its automorphisms (concr_usym_iso_equiv), r_G is an equivalence
   onto them (abstract_r_equiv), and r_G(μ(u, v)) = r_G(u) ∘ r_G(v)
   (abstract_r_mul) matches concatenation of symmetries
   (agset_path_to_iso_concat). The footnote ft:abstract-Cayley (Cayley's
   theorem) is abstract_cayley_injective below. `}

def concr_usym_of (G : AbstractGroup) (u : G .carrier) : USym (concr G)
  ≔ equiv_inverse_map (USym (concr G)) (AbstractGSetIso G (agset_principal G) (agset_principal G))
      (concr_usym_iso_equiv G) (abstract_r_map G u)

def concr_abstr_carrier_equiv (G : AbstractGroup) : Equiv (G .carrier) (USym (concr G))
  ≔ let I ≔ AbstractGSetIso G (agset_principal G) (agset_principal G) in
    compose_equiv (G .carrier) I (USym (concr G)) (abstract_r_equiv G)
      (canonical_inverse_equiv (USym (concr G)) I (concr_usym_iso_equiv G))

{` Concatenation of symmetries of the principal torsor is composition of
   automorphisms (first one first). `}
def concr_usym_iso_concat (G : AbstractGroup) (a b : USym (concr G))
  : Id (AbstractGSetIso G (agset_principal G) (agset_principal G))
      (concr_usym_iso_equiv G .map (concat (AbstractTorsors G) (abstract_principal_torsor G) (abstract_principal_torsor G)
        (abstract_principal_torsor G) a b))
      (agset_iso_compose G (agset_principal G) (agset_principal G) (agset_principal G)
        (concr_usym_iso_equiv G .map a) (concr_usym_iso_equiv G .map b))
  ≔ let P ≔ agset_principal G in let P0 ≔ abstract_principal_torsor G in
    let Tor ≔ AbstractTorsors G in
    concat (AbstractGSetIso G P P)
      (agset_path_to_iso G P P (refl ((u ↦ u .fst) : Tor → AbstractGSet G) (concat Tor P0 P0 P0 a b)))
      (agset_path_to_iso G P P (concat (AbstractGSet G) P P P (a .fst) (b .fst)))
      (agset_iso_compose G P P P (agset_path_to_iso G P P (a .fst)) (agset_path_to_iso G P P (b .fst)))
      (refl (agset_path_to_iso G P P)
        (map_path_concat Tor (AbstractGSet G) (u ↦ u .fst) P0 P0 P0 a b))
      (agset_path_to_iso_concat G P P P (a .fst) (b .fst))

{` The map S → USym(concr G) preserves multiplication. `}
def concr_abstr_hom (G : AbstractGroup) : IsAbstractHom G (abstr (concr G)) (concr_usym_of G)
  ≔ u v ↦
    let P ≔ agset_principal G in
    let I ≔ AbstractGSetIso G P P in
    let E ≔ concr_usym_iso_equiv G in
    let T ≔ concr_usym_of G in
    let ru ≔ abstract_r_map G u in let rv ≔ abstract_r_map G v in
    equivalence_injective (USym (concr G)) I E (T (G .mul u v)) (usym_mul (concr G) (T u) (T v))
      (calc
         E .map (T (G .mul u v)) = abstract_r_map G (G .mul u v)
           by equiv_counit (USym (concr G)) I E (abstract_r_map G (G .mul u v))
         = agset_iso_compose G P P P rv ru by abstract_r_mul G u v
         = agset_iso_compose G P P P (E .map (T v)) (E .map (T u))
           by inverse I (agset_iso_compose G P P P (E .map (T v)) (E .map (T u))) (agset_iso_compose G P P P rv ru)
             (refl (agset_iso_compose G P P P) (equiv_counit (USym (concr G)) I E rv) (equiv_counit (USym (concr G)) I E ru))
         = E .map (usym_mul (concr G) (T u) (T v))
           by inverse I (E .map (usym_mul (concr G) (T u) (T v))) (agset_iso_compose G P P P (E .map (T v)) (E .map (T u)))
             (concr_usym_iso_concat G (T v) (T u)) ∎)

{` Proof of thm:Groupsareidentitytypes: the abstract isomorphism
   G ≅ abstr(concr(G)) (the book's r_G, promoted). `}
def concr_abstr_iso (G : AbstractGroup) : AbstractIso G (abstr (concr G))
  ≔ (concr_abstr_carrier_equiv G, concr_abstr_hom G)

{` abstr(concr(G)) = G. `}
def abstr_concr_path (G : AbstractGroup) : Id AbstractGroup (abstr (concr G)) G
  ≔ inverse AbstractGroup G (abstr (concr G)) (abstract_group_path_from_iso G (abstr (concr G)) (concr_abstr_iso G))

{` thm:Groupsareidentitytypes (and the remark after lem:group-inv-operation):
   abstr : Group → AbstractGroup is an equivalence with inverse concr. `}
def abstr_book_equiv : BookEquiv Group AbstractGroup
  ≔ book_quasi_inverse_equiv Group AbstractGroup abstr concr concr_abstr_path abstr_concr_path

def abstr_is_equiv : BookIsEquiv Group AbstractGroup abstr ≔ abstr_book_equiv .equiv

def group_abstract_group_equiv : Equiv Group AbstractGroup
  ≔ quasi_inverse_equiv Group AbstractGroup abstr concr concr_abstr_path abstr_concr_path

{` The underlying isomorphism of abstr ∘ concr is the book's r_G: the
   symmetry associated with u is the automorphism r_G(u) of the principal
   torsor, which acts by x ↦ x · u⁻¹ (by refl). `}
def concr_usym_of_iso (G : AbstractGroup) (u : G .carrier)
  : Id (AbstractGSetIso G (agset_principal G) (agset_principal G))
      (concr_usym_iso_equiv G .map (concr_usym_of G u)) (abstract_r_map G u)
  ≔ equiv_counit (USym (concr G)) (AbstractGSetIso G (agset_principal G) (agset_principal G))
      (concr_usym_iso_equiv G) (abstract_r_map G u)

def abstract_r_map_action (G : AbstractGroup) (u x : G .carrier)
  : Id (G .carrier) (abstract_r_map G u .fst .map x) (G .mul x (G .inv u))
  ≔ refl (G .mul x (G .inv u))

{` ft:abstract-Cayley (Cayley's theorem for abstract groups): the
   homomorphism G → abstr(Σ_S) of the principal torsor (s ↦ left
   multiplication by s) is injective. `}
def abstract_cayley_hom (G : AbstractGroup) : AbstractHom G (abstr (permutation_group (G .carrier, abstract_group_set G)))
  ≔ agset_principal G .snd

def abstract_cayley_injective (G : AbstractGroup) (s t : G .carrier)
  (h : Id (USym (permutation_group (G .carrier, abstract_group_set G))) (abstract_cayley_hom G .fst s) (abstract_cayley_hom G .fst t))
  : Id (G .carrier) s t
  ≔ let S ≔ G .carrier in let X : SetTypes ≔ (S, abstract_group_set G) in
    calc
      s = G .mul s (G .unit) by inverse S (G .mul s (G .unit)) s (G .laws .unit_right s)
      = G .mul t (G .unit)
        by refl ((q ↦ permutation_action X q (G .unit)) : USym (permutation_group X) → S) h
      = t by G .laws .unit_right t ∎
