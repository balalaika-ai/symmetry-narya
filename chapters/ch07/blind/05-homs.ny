export "04-phi-functors"
export "../../../src/686-category-of-groups"

{` Blind statements, chapter 7, section "Homomorphisms, from abstract to concrete and back". `}

{` lem:homomabstrconcr. `}
def blind_lem_homomabstrconcr : Type
  ≔ (G H : Group) → BookIsEquiv (GroupHom G H) (BlindAbsHom (blind_abstr G) (blind_abstr H)) (blind_abstr_hom G H)

{` The (wild) category of abstract groups, with the composition of
   xca:abshomcomposition. `}
def blind_is_abshom_prop (G H : BlindAbsGroup) (f : G .carrier → H .carrier) : isProp (BlindIsAbsHom G H f)
  ≔ pi_prop (G .carrier) (s ↦ (s' : G .carrier) → Id (H .carrier) (f (G .mul s s')) (H .mul (f s) (f s')))
      (s ↦ pi_prop (G .carrier) (s' ↦ Id (H .carrier) (f (G .mul s s')) (H .mul (f s) (f s')))
        (s' ↦ blind_ag_set H (f (G .mul s s')) (H .mul (f s) (f s'))))

def blind_abshom_path (G H : BlindAbsGroup) (f g : BlindAbsHom G H) (p : Id (G .carrier → H .carrier) (f .fst) (g .fst))
  : Id (BlindAbsHom G H) f g
  ≔ subtype_equal (G .carrier → H .carrier) (BlindIsAbsHom G H) (blind_is_abshom_prop G H) f g p

def BlindAbsGroupWild : WildPrecat
  ≔ (ob ≔ BlindAbsGroup,
     hom ≔ BlindAbsHom,
     idn ≔ blind_abshom_id,
     comp ≔ G H K g f ↦ blind_abshom_compose G H K f g,
     lu ≔ G H f ↦ blind_abshom_path G H (blind_abshom_compose G H H f (blind_abshom_id H)) f (refl (f .fst)),
     ru ≔ G H f ↦ blind_abshom_path G H (blind_abshom_compose G G H (blind_abshom_id G) f) f (refl (f .fst)),
     assoc ≔ G H K L f g h ↦
       blind_abshom_path G L
         (blind_abshom_compose G K L (blind_abshom_compose G H K f g) h)
         (blind_abshom_compose G H L f (blind_abshom_compose H K L g h))
         (refl (s ↦ h .fst (g .fst (f .fst s)))))

{` xca:Bconcr-OK (1): (t,x) ↦ t φ(x) induces a path φ_!(P_G) = P_H (an
   identification of H-sets whose underlying map sends [(t,x)] to t φ(x)). `}
def BlindBconcrOK1 (G H : BlindAbsGroup) (phi : BlindAbsHom G H)
  (okS : (X : BlindAbsGSet G) → BlindPhiShriekOK G H phi X) : Type
  ≔ Σ (Id (BlindAbsGSet H) (blind_phi_shriek G H phi okS (blind_abs_principal G)) (blind_abs_principal H)) (p ↦
      (t : H .carrier) (s : G .carrier)
      → Id (H .carrier)
          (transport (BlindAbsGSet H) (W ↦ W .fst .fst) (blind_phi_shriek G H phi okS (blind_abs_principal G))
            (blind_abs_principal H) p (blind_phi_class G H phi (blind_abs_principal G) (okS (blind_abs_principal G)) t s))
          (H .mul t (phi .fst s)))

def blind_xca_bconcr_ok1 : Type
  ≔ (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (okS : (X : BlindAbsGSet G) → BlindPhiShriekOK G H phi X)
    → BlindBconcrOK1 G H phi okS

{` concr on morphisms: Bconcr(φ) is φ_! restricted to the torsor
   components, pointed by the inverse of the path of xca:Bconcr-OK (1). `}
def blind_bconcr (G H : BlindAbsGroup) (phi : BlindAbsHom G H)
  (okS : (X : BlindAbsGSet G) → BlindPhiShriekOK G H phi X) (ok1 : BlindBconcrOK1 G H phi okS)
  (X : BlindAbsTorsor G) : BlindAbsTorsor H
  ≔ let PG ≔ blind_abs_principal G in let PH ≔ blind_abs_principal H in
    let F ≔ blind_phi_shriek G H phi okS in
    (F (X .fst),
     mere_rec (Id (BlindAbsGSet G) PG (X .fst)) (Mere (Id (BlindAbsGSet H) PH (F (X .fst))))
       (mere_isprop (Id (BlindAbsGSet H) PH (F (X .fst))))
       (p ↦ mere (Id (BlindAbsGSet H) PH (F (X .fst)))
         (concat (BlindAbsGSet H) PH (F PG) (F (X .fst))
           (inverse (BlindAbsGSet H) (F PG) PH (ok1 .fst))
           (map_path (BlindAbsGSet G) (BlindAbsGSet H) F PG (X .fst) p)))
       (X .snd))

def blind_concr_mor (G H : BlindAbsGroup) (phi : BlindAbsHom G H)
  (okS : (X : BlindAbsGSet G) → BlindPhiShriekOK G H phi X) (ok1 : BlindBconcrOK1 G H phi okS)
  : GroupHom (blind_concr G) (blind_concr H)
  ≔ let PG ≔ blind_abs_principal G in let PH ≔ blind_abs_principal H in
    mkhom (blind_concr G) (blind_concr H)
      (blind_bconcr G H phi okS ok1,
       component_path (BlindAbsGSet H) PH (component_point (BlindAbsGSet H) PH)
         (blind_bconcr G H phi okS ok1 (component_point (BlindAbsGSet G) PG))
         (inverse (BlindAbsGSet H) (blind_phi_shriek G H phi okS PG) PH (ok1 .fst)))

{` Global choices of the data of xca:phi_!-OK and xca:Bconcr-OK (1). `}
def BlindConcrData : Type
  ≔ Σ ((G H : BlindAbsGroup) (phi : BlindAbsHom G H) (X : BlindAbsGSet G) → BlindPhiShriekOK G H phi X) (okS ↦
      (G H : BlindAbsGroup) (phi : BlindAbsHom G H) → BlindBconcrOK1 G H phi (okS G H phi))

def blind_concr_mor_d (d : BlindConcrData) (G H : BlindAbsGroup) (phi : BlindAbsHom G H)
  : GroupHom (blind_concr G) (blind_concr H)
  ≔ blind_concr_mor G H phi (d .fst G H phi) (d .snd G H phi)

def BlindConcrMapId (d : BlindConcrData) : Type
  ≔ (G : BlindAbsGroup)
    → Id (GroupHom (blind_concr G) (blind_concr G)) (blind_concr_mor_d d G G (blind_abshom_id G)) (group_hom_id (blind_concr G))

def BlindConcrMapComp (d : BlindConcrData) : Type
  ≔ (G H K : BlindAbsGroup) (f : BlindAbsHom G H) (g : BlindAbsHom H K)
    → Id (GroupHom (blind_concr G) (blind_concr K)) (blind_concr_mor_d d G K (blind_abshom_compose G H K f g))
        (group_hom_compose (blind_concr G) (blind_concr H) (blind_concr K) (blind_concr_mor_d d G H f) (blind_concr_mor_d d H K g))

{` xca:Bconcr-OK (2): concr is a functor (for any choice of the data). `}
def blind_xca_bconcr_ok2 : Type
  ≔ (d : BlindConcrData) → Product (BlindConcrMapId d) (BlindConcrMapComp d)

{` thm:concr-equiv-cats: concr is functorial and an equivalence of categories. `}
def blind_thm_concr_equiv_cats : Type
  ≔ (d : BlindConcrData)
    → Σ (BlindConcrMapId d) (mid ↦ Σ (BlindConcrMapComp d) (mc ↦
        IsCatEquivalence BlindAbsGroupWild GroupWild
          (obj ≔ blind_concr, mor ≔ blind_concr_mor_d d, map_id ≔ mid, map_comp ≔ mc)))

{` xca:SG2=SG2-contractible: Iso(Σ_2, C_2) is contractible. `}
def blind_xca_sg2_c2_contractible : Type
  ≔ BookIsContr (GroupIso (symmetric_group two) (cyclic_group_fin (suc. zero.)))
