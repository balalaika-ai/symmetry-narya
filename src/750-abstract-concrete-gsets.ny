export "560-gset-action-equivalences"
export "706-abstract-gset-identity"
export "710-hom-delooping"

{` Chapter 7 (absgroup.tex), sec:Gsetsabstrconcr, lem:actionsconcr2abstr and
   the running text before it.

   For a group G the map ev_{sh_G} : GSet → absGSet(abstr G) sends X to
   (X(sh_G), a_X) where a_X is abstr of the homomorphism G → Σ_{X(sh_G)}
   classified by z ↦ (X(z), !) (gset_to_action, rem:GSet=SetHomG); a_X(g)
   acts on X(sh_G) as g ·_X - (ev_gset_act, typal) and is the symmetry of
   X(sh_G) given by the permutation X(g) (ev_gset_symmetry). The book's chain
     GSet ≃ Σ_S Hom(G, Σ_S) ≃ Σ_S absHom(abstr G, abstr Σ_S) ≡ absGSet(abstr G)
   is ev_gset_chain_equiv (gset_action_equiv of module 560, then
   abstr_hom_equiv of lem:homomabstrconcr fibrewise); its map is ev_gset by
   refl, and the last step is a judgmental equality of types. `}

{` a_X : abstr(G) → abstr(Σ_{X(sh_G)}). `}
def ev_gset_action (G : Group) (X : GSet G) : AbstractHom (abstr G) (abstr (permutation_group (X (shape G))))
  ≔ abstr_hom G (permutation_group (X (shape G))) (gset_to_action G X)

{` lem:actionsconcr2abstr: ev_{sh_G}(X) ≔ (X(sh_G), a_X). `}
def ev_gset (G : Group) (X : GSet G) : AbstractGSet (abstr G) ≔ (X (shape G), ev_gset_action G X)

def ev_gset_underlying (G : Group) (X : GSet G)
  : Id Type (agset_carrier (abstr G) (ev_gset G X)) (gset_underlying G X)
  ≔ refl (gset_underlying G X)

{` a_X(g) acts by g ·_X - (transport in X along g). `}
def ev_gset_act (G : Group) (X : GSet G) (g : USym G) (a : gset_underlying G X)
  : Id (gset_underlying G X) (agset_act (abstr G) (ev_gset G X) g a) (gset_usym_act G X g a)
  ≔ gset_to_action_usym_act G X g a

{` a_X(g) ≔ X(g): as a symmetry of X(sh_G) in Σ_{X(sh_G)}, a_X(g) is the
   permutation X(g) = trp^X(g) (gset_act_equiv). `}
def ev_gset_symmetry (G : Group) (X : GSet G) (g : USym G)
  : Id (USym (permutation_group (X (shape G)))) (ev_gset_action G X .fst g)
      (permutation_symmetry (X (shape G)) (gset_act_equiv G X (shape G) (shape G) g))
  ≔ agset_permutation_symmetry_ext (X (shape G)) (ev_gset_action G X .fst g)
      (permutation_symmetry (X (shape G)) (gset_act_equiv G X (shape G) (shape G) g))
      (a ↦ gset_to_action_usym_act G X g a)

{` The chain GSet ≃ Σ_S Hom(G, Σ_S) ≃ Σ_S absHom(abstr G, abstr Σ_S) ≡ absGSet(abstr G). `}
def ev_gset_chain_equiv (G : Group) : Equiv (GSet G) (AbstractGSet (abstr G))
  ≔ compose_equiv (GSet G) (Σ SetTypes (S ↦ GroupActionOnSet G S)) (AbstractGSet (abstr G))
      (gset_action_equiv G)
      (family_equiv SetTypes (S ↦ GroupActionOnSet G S) (S ↦ AbstractHom (abstr G) (abstr (permutation_group S)))
        (S ↦ abstr_hom_equiv G (permutation_group S)))

{` The last step of the chain is a judgmental equality of types. `}
def ev_gset_chain_last_step (G : Group)
  : Id Type (Σ SetTypes (S ↦ AbstractHom (abstr G) (abstr (permutation_group S)))) (AbstractGSet (abstr G))
  ≔ refl (AbstractGSet (abstr G))

{` "Backtracking these equivalences": the composite is ev_{sh_G}. `}
def ev_gset_chain_map (G : Group) (X : GSet G)
  : Id (AbstractGSet (abstr G)) (ev_gset_chain_equiv G .map X) (ev_gset G X)
  ≔ refl (ev_gset G X)

{` lem:actionsconcr2abstr: ev_{sh_G} is an equivalence. `}
def gset_abstract_gset_equiv (G : Group) : Equiv (GSet G) (AbstractGSet (abstr G))
  ≔ (ev_gset G, ev_gset_chain_equiv G .equiv)

def gset_abstract_gset_equiv_map (G : Group) (X : GSet G)
  : Id (AbstractGSet (abstr G)) (gset_abstract_gset_equiv G .map X) (ev_gset G X)
  ≔ refl (ev_gset G X)

def ev_gset_is_equiv (G : Group) : BookIsEquiv (GSet G) (AbstractGSet (abstr G)) (ev_gset G)
  ≔ book_equivalence (GSet G) (AbstractGSet (abstr G)) (gset_abstract_gset_equiv G) .equiv

{` "The component information is moot by xca:ptd-conn-to-comp": Σ_S is
   classified by the component Set_(S), and pointed maps BG →* (Set, S) are
   the same as homomorphisms G → Σ_S. `}
def ev_gset_component_moot (G : Group) (S : SetTypes)
  : Equiv (BookPointedMap (BG G) (SetTypes, S)) (GroupActionOnSet G S)
  ≔ compose_equiv (BookPointedMap (BG G) (SetTypes, S))
      (BookPointedMap (BG G) (NativeComponent SetTypes S, component_point SetTypes S)) (GroupActionOnSet G S)
      (ptd_conn_to_comp_equiv (BG G) (SetTypes, S) (bg_connected G))
      (canonical_inverse_equiv (GroupHom G (permutation_group S)) (BookPointedMap (BG G) (BG (permutation_group S)))
        (group_hom_classifying_equiv G (permutation_group S)))

{` Litmus (Σ_3 on Fin 3): in ev of the standard Σ_3-set, τ = (0 1) sends 0 to 1. `}
def ev_gset_sigma3_tau_zero
  : Id (Fin three)
      (agset_act (abstr (symmetric_group three)) (ev_gset (symmetric_group three) (standard_symmetric_gset three))
        sigma3_tau fin3_zero)
      fin3_one
  ≔ gset_to_action_sigma3_tau_zero

{` Litmus: ev sends the principal G-torsor P_G to the principal
   abstr(G)-torsor (identity map, equivariant by ev_gset_act). `}
def ev_gset_principal_iso (G : Group)
  : AbstractGSetIso (abstr G) (ev_gset G (principal_gset G)) (agset_principal (abstr G))
  ≔ (identity_equiv (USym G), s x ↦ ev_gset_act G (principal_gset G) s x)

def ev_gset_principal_path (G : Group)
  : Id (AbstractGSet (abstr G)) (ev_gset G (principal_gset G)) (agset_principal (abstr G))
  ≔ agset_path_from_iso (abstr G) (ev_gset G (principal_gset G)) (agset_principal (abstr G)) (ev_gset_principal_iso G)
