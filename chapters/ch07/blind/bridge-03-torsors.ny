export "bridge-00-core"
export "../../../src/712-abstract-torsor-examples"

{` Bridges for absgroup.tex, sec "Groups: from abstract to concrete
   and back" (blind file 03-torsors). The definition bridges for G-sets,
   the principal torsor, torsors and concr are in bridge-00-core. `}

def bridge_def_perm_group (X : SetTypes) : Id AbstractGroup (bridge_ag7 (blind_perm_group X)) (abstr (permutation_group X))
  ≔ refl (abstr (permutation_group X))

{` xca:absprtorsor (the action laws are ours, copied from
   agset_principal_right). `}
def bridge_absprtorsor_mul (G : BlindAbsGroup) (g h x : G .carrier)
  : Id (G .carrier) (G .mul x (G .inv (G .mul g h))) (G .mul (G .mul x (G .inv h)) (G .inv g))
  ≔ let G' ≔ bridge_ag7 G in let m ≔ G .mul in
    calc
      m x (G .inv (m g h)) = m x (m (G .inv h) (G .inv g)) by refl (m x) (ag_inv_mul G' g h)
      = m (m x (G .inv h)) (G .inv g) by G' .laws .assoc x (G .inv h) (G .inv g) ∎

def bridge_absprtorsor_unit (G : BlindAbsGroup) (x : G .carrier)
  : Id (G .carrier) (G .mul x (G .inv (G .unit))) x
  ≔ let G' ≔ bridge_ag7 G in let m ≔ G .mul in
    concat (G .carrier) (m x (G .inv (G .unit))) (m x (G .unit)) x (refl (m x) (ag_inv_unit G')) (G' .laws .unit_right x)

def bridge_xca_absprtorsor : blind_xca_absprtorsor
  ≔ G ↦ let G' ≔ bridge_ag7 G in let A ≔ AbstractGSet G' in let X : SetTypes ≔ (G .carrier, blind_ag_set G) in
    let act : G .carrier → G .carrier → G .carrier ≔ g x ↦ G .mul x (G .inv g) in
    (bridge_absprtorsor_mul G, (bridge_absprtorsor_unit G,
     concat A (blind_abs_principal G) (agset_principal G')
       (blind_gset_of_action G X act (bridge_absprtorsor_mul G) (bridge_absprtorsor_unit G))
       (bridge_principal_path G)
       (concat A (agset_principal G') (agset_principal_right G')
         (blind_gset_of_action G X act (bridge_absprtorsor_mul G) (bridge_absprtorsor_unit G))
         (agset_principal_right_path G')
         (inverse A (blind_gset_of_action G X act (bridge_absprtorsor_mul G) (bridge_absprtorsor_unit G))
           (agset_principal_right G')
           (bridge_gofa_path G X act (bridge_absprtorsor_mul G) (bridge_absprtorsor_unit G))))))

{` Example (absgroup.tex 505). `}
def bridge_ex_abstr_gset_unfold : blind_ex_abstr_gset_unfold ≔ G ↦ abstr_gset_unfold G

{` def:concr: bridge_concr_path (core). "Clearly AbsGSet is a groupoid":
   the blind proof and ours are proofs of the same proposition. `}
def bridge_def_concr (G : BlindAbsGroup) : Id Group (blind_concr G) (concr (bridge_ag7 G)) ≔ bridge_concr_path G

def bridge_def_concr_abstr (G : Group) : Id Group (blind_concr (blind_abstr G)) (concr (abstr G))
  ≔ bridge_concr_path (blind_abstr G)

{` ex:BqG: the blind Bq_G(z) is ours up to the proof terms of the action. `}
def bridge_bq_gset_path (G : Group) (z : BG G .carrier)
  : Id (AbstractGSet (abstr G)) (blind_bq_gset G z) (bq_gset G z)
  ≔ let A ≔ BG G .carrier in let a ≔ shape G in
    bridge_gofa_path (blind_abstr G) (blind_bq_set G z) (blind_post G z)
      (g h p ↦ inverse (Id A z a) (concat A z a a (concat A z a a p h) g) (concat A z a a p (concat A a a a h g))
        (concat_assoc A z a a a p h g))
      (p ↦ concat_p1 A z a p)

def bridge_ex_bqg_principal : blind_ex_bqg_principal
  ≔ G ↦ let A ≔ AbstractGSet (abstr G) in
    concat A (blind_bq_gset G (shape G)) (bq_gset G (shape G)) (blind_abs_principal (blind_abstr G))
      (bridge_bq_gset_path G (shape G))
      (concat A (bq_gset G (shape G)) (agset_principal (abstr G)) (blind_abs_principal (blind_abstr G))
        (bq_gset_principal G)
        (inverse A (blind_abs_principal (blind_abstr G)) (agset_principal (abstr G))
          (bridge_principal_path (blind_abstr G))))

{` ft:shG=z (the action laws are ours, copied from preinv_gset). `}
def bridge_preinv_mul (G : Group) (z : BG G .carrier) (g h : USym G) (r : Id (BG G .carrier) (shape G) z)
  : Id (Id (BG G .carrier) (shape G) z)
      (concat (BG G .carrier) (shape G) (shape G) z (inverse (BG G .carrier) (shape G) (shape G) (usym_mul G g h)) r)
      (concat (BG G .carrier) (shape G) (shape G) z (inverse (BG G .carrier) (shape G) (shape G) g)
        (concat (BG G .carrier) (shape G) (shape G) z (inverse (BG G .carrier) (shape G) (shape G) h) r))
  ≔ let A ≔ BG G .carrier in let a ≔ shape G in
    calc
      concat A a a z (inverse A a a (concat A a a a h g)) r
        = concat A a a z (concat A a a a (inverse A a a g) (inverse A a a h)) r
        by refl ((q ↦ concat A a a z q r) : Id A a a → Id A a z) (inverse_concat A a a a h g)
      = concat A a a z (inverse A a a g) (concat A a a z (inverse A a a h) r)
        by concat_assoc A a a a z (inverse A a a g) (inverse A a a h) r ∎

def bridge_preinv_unit (G : Group) (z : BG G .carrier) (r : Id (BG G .carrier) (shape G) z)
  : Id (Id (BG G .carrier) (shape G) z)
      (concat (BG G .carrier) (shape G) (shape G) z (inverse (BG G .carrier) (shape G) (shape G) (usym_unit G)) r) r
  ≔ let A ≔ BG G .carrier in let a ≔ shape G in
    concat (Id A a z) (concat A a a z (inverse A a a (refl a)) r) (concat A a a z (refl a) r) r
      (refl ((q ↦ concat A a a z q r) : Id A a a → Id A a z) (inverse_refl A a))
      (concat_1p A a z r)

def bridge_ft_shg_z : blind_ft_shg_z
  ≔ G ↦ let A ≔ BG G .carrier in let a ≔ shape G in let AG ≔ AbstractGSet (abstr G) in
    let act : USym G → Id A a a → Id A a a ≔ g r ↦ concat A a a a (inverse A a a g) r in
    let Xb ≔ blind_gset_of_action (blind_abstr G) (Id A a a, bg_groupoid G a a) act
               (bridge_preinv_mul G a) (bridge_preinv_unit G a) in
    (bridge_preinv_mul G, (bridge_preinv_unit G,
     concat AG Xb (preinv_gset G a) (blind_abs_principal (blind_abstr G))
       (bridge_gofa_path (blind_abstr G) (Id A a a, bg_groupoid G a a) act (bridge_preinv_mul G a) (bridge_preinv_unit G a))
       (concat AG (preinv_gset G a) (agset_principal (abstr G)) (blind_abs_principal (blind_abstr G))
         (inverse AG (agset_principal (abstr G)) (preinv_gset G a) (preinv_gset_principal_path G))
         (inverse AG (blind_abs_principal (blind_abstr G)) (agset_principal (abstr G))
           (bridge_principal_path (blind_abstr G))))))

{` lem:Groupsareidentitytypes: the blind Bq_G is our Bq_G followed by the
   equivalence of the two torsor types (up to a homotopy). `}
def bridge_lem_groups_are_identity_types : blind_lem_groups_are_identity_types
  ≔ G ↦ let G0 ≔ blind_abstr G in let A ≔ AbstractGSet (abstr G) in
    let Pb ≔ blind_abs_principal G0 in let P ≔ agset_principal (abstr G) in
    let e ≔ bridge_component_equiv A P Pb (inverse A Pb P (bridge_principal_path G0)) in
    let q : BookEquiv (BG G .carrier) (AbstractTorsors (abstr G)) ≔ (bq_map G, q_hom_is_iso G) in
    bridge_book_equiv_homotopic (BG G .carrier) (NativeComponent A Pb)
      (bridge_book_equiv_compose (BG G .carrier) (AbstractTorsors (abstr G)) (NativeComponent A Pb) q
        (book_equivalence (AbstractTorsors (abstr G)) (NativeComponent A Pb) e))
      (blind_bq G)
      (z ↦ component_path A Pb (e .map (bq_map G z)) (blind_bq G z)
        (inverse A (blind_bq_gset G z) (bq_gset G z) (bridge_bq_gset_path G z)))

{` def:qG-concr-abstr: the blind Bq_G is our Bq_G (bq_map) followed by the
   identification of the two torsor types, pointwise. `}
def bridge_def_qG (G : Group) (z : BG G .carrier)
  : Id (BlindAbsTorsor (blind_abstr G))
      (bridge_component_map (AbstractGSet (abstr G)) (agset_principal (abstr G)) (blind_abs_principal (blind_abstr G))
        (inverse (AbstractGSet (abstr G)) (blind_abs_principal (blind_abstr G)) (agset_principal (abstr G))
          (bridge_principal_path (blind_abstr G)))
        (bq_map G z))
      (hom_function G (blind_concr (blind_abstr G)) (blind_qG G) z)
  ≔ let A ≔ AbstractGSet (abstr G) in let Pb ≔ blind_abs_principal (blind_abstr G) in
    component_path A Pb
      (bridge_component_map A (agset_principal (abstr G)) Pb
        (inverse A Pb (agset_principal (abstr G)) (bridge_principal_path (blind_abstr G))) (bq_map G z))
      (blind_bq G z)
      (inverse A (blind_bq_gset G z) (bq_gset G z) (bridge_bq_gset_path G z))

{` thm:Groupsareidentitytypes. `}
def bridge_ag_inv_equiv : Equiv AbstractGroup BlindAbsGroup
  ≔ quasi_inverse_equiv AbstractGroup BlindAbsGroup bridge_ag7_inv bridge_ag7 (G ↦ refl G) (G ↦ refl G)

def bridge_thm_groups_are_identity_types : blind_thm_groups_are_identity_types
  ≔ bridge_book_equiv_homotopic Group BlindAbsGroup
      (bridge_book_equiv_compose Group AbstractGroup BlindAbsGroup abstr_book_equiv
        (book_equivalence AbstractGroup BlindAbsGroup bridge_ag_inv_equiv))
      blind_abstr (G ↦ refl (blind_abstr G))

{` ft:abstract-Cayley. `}
def bridge_inj_embedding (A B : Type) (f : A → B) (hb : isSet B) (hi : (x y : A) → Id B (f x) (f y) → Id A x y)
  : IsEmbedding A B f
  ≔ b u v ↦ subtype_equal A (a ↦ Id B b (f a)) (a ↦ hb b (f a)) u v
      (hi (u .fst) (v .fst) (concat B (f (u .fst)) b (f (v .fst)) (inverse B b (f (u .fst)) (u .snd)) (v .snd)))

def bridge_ft_abstract_cayley : blind_ft_abstract_cayley
  ≔ G ↦ let G' ≔ bridge_ag7 G in let X : SetTypes ≔ (G .carrier, blind_ag_set G) in
    (abstract_cayley_hom G',
     bridge_inj_embedding (G .carrier) (USym (permutation_group X)) (abstract_cayley_hom G' .fst)
       (usym_set (permutation_group X)) (abstract_cayley_injective G'))
