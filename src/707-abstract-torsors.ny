export "706-abstract-gset-identity"

{` Chapter 7 (absgroup.tex), def:abstrGtorsors (torsors) and def:concr:
   the concrete group concr(G) classified by the pointed connected
   groupoid (GTor, P_G) of G-torsors. `}

{` def:abstrGtorsors. GTor ≔ Σ_{X : GSet} ‖P_G = X‖. `}
def AbstractTorsors (G : AbstractGroup) : Type
  ≔ Σ (AbstractGSet G) (X ↦ Mere (Id (AbstractGSet G) (agset_principal G) X))

def abstract_principal_torsor (G : AbstractGroup) : AbstractTorsors G
  ≔ (agset_principal G, mere (Id (AbstractGSet G) (agset_principal G) (agset_principal G)) (refl (agset_principal G)))

def abstract_torsors_path_equiv (G : AbstractGroup) (S T : AbstractTorsors G)
  : Equiv (Id (AbstractTorsors G) S T) (Id (AbstractGSet G) (S .fst) (T .fst))
  ≔ subtype_path_equiv (AbstractGSet G) (X ↦ Mere (Id (AbstractGSet G) (agset_principal G) X))
      (X ↦ mere_isprop (Id (AbstractGSet G) (agset_principal G) X)) S T

def abstract_torsors_path (G : AbstractGroup) (S T : AbstractTorsors G) (p : Id (AbstractGSet G) (S .fst) (T .fst))
  : Id (AbstractTorsors G) S T
  ≔ subtype_equal (AbstractGSet G) (X ↦ Mere (Id (AbstractGSet G) (agset_principal G) X))
      (X ↦ mere_isprop (Id (AbstractGSet G) (agset_principal G) X)) S T p

{` "the latter is by definition connected". `}
def abstract_torsors_connected (G : AbstractGroup) : Connected (AbstractTorsors G)
  ≔ let Tor ≔ AbstractTorsors G in
    let P ≔ agset_principal G in
    let P0 ≔ abstract_principal_torsor G in
    let reach : (S : Tor) → Mere (Id Tor P0 S)
      ≔ S ↦ mere_rec (Id (AbstractGSet G) P (S .fst)) (Mere (Id Tor P0 S)) (mere_isprop (Id Tor P0 S))
          (p ↦ mere (Id Tor P0 S) (abstract_torsors_path G P0 S p))
          (S .snd) in
    (mere Tor P0, S T ↦ merely_paths_compose native_truncation Tor P0 S T (reach S) (reach T))

def abstract_torsors_groupoid (G : AbstractGroup) : isGroupoid (AbstractTorsors G)
  ≔ hlevel_to_groupoid (AbstractTorsors G)
      (subtype_hlevel (suc. (suc. zero.)) (AbstractGSet G) (X ↦ Mere (Id (AbstractGSet G) (agset_principal G) X))
        (groupoid_to_hlevel (AbstractGSet G) (agset_groupoid G))
        (X ↦ mere_isprop (Id (AbstractGSet G) (agset_principal G) X)))

{` def:concr. concr(G) ≔ mkgroup (GTor, P_G). `}
def concr_classifying (G : AbstractGroup) : PointedConnectedGroupoid
  ≔ (AbstractTorsors G, abstract_principal_torsor G, abstract_torsors_connected G, abstract_torsors_groupoid G)

def concr (G : AbstractGroup) : Group ≔ mkgroup (concr_classifying G)

def concr_classifying_type (G : AbstractGroup) : Id Type (BG (concr G) .carrier) (AbstractTorsors G)
  ≔ refl (AbstractTorsors G)

def concr_shape (G : AbstractGroup) : Id (AbstractTorsors G) (shape (concr G)) (abstract_principal_torsor G)
  ≔ refl (abstract_principal_torsor G)

{` The symmetries of concr(G) are the automorphisms of the principal
   torsor: USym(concr G) ≃ Iso(P_G, P_G). `}
def concr_usym_iso_equiv (G : AbstractGroup)
  : Equiv (USym (concr G)) (AbstractGSetIso G (agset_principal G) (agset_principal G))
  ≔ compose_equiv (USym (concr G)) (Id (AbstractGSet G) (agset_principal G) (agset_principal G))
      (AbstractGSetIso G (agset_principal G) (agset_principal G))
      (abstract_torsors_path_equiv G (abstract_principal_torsor G) (abstract_principal_torsor G))
      (agset_path_iso_equiv G (agset_principal G) (agset_principal G))
