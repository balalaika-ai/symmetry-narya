export "../../../src/624-adjunctions-via-representability"
export "../../../src/625-adjunction-units"
export "../../../src/604-wild-pointed-types"
export "08-limits"

{` Bridges for cats.tex: the definition bridges shared by all
   bridge files (blind files 01-05).
   The blind records (sig types with fields lunit/runit, Σ-packed
   precategories) are translated into ours (WildPrecat with lu/ru,
   Precat/Category records). The translations are inverse up to η, so the
   definition bridges are equivalences with refl round trips; most blind
   predicates then agree with ours definitionally (checked by refl). `}

{` def:wild-cat. `}
def bridge_w (C : BlindWildPrecat) : WildPrecat
  ≔ (ob ≔ C .ob, hom ≔ C .hom, idn ≔ C .idn, comp ≔ C .comp, lu ≔ C .lunit, ru ≔ C .runit,
     assoc ≔ C .assoc)

def bridge_w_inv (C : WildPrecat) : BlindWildPrecat
  ≔ (C .ob, C .hom, C .idn, C .comp, C .lu, C .ru, C .assoc)

def bridge_def_wild_precat : Equiv BlindWildPrecat WildPrecat
  ≔ quasi_inverse_equiv BlindWildPrecat WildPrecat bridge_w bridge_w_inv (C ↦ refl C) (C ↦ refl C)

{` BlindWildPrecatStr Ob hom is the type of wild precategory structures on
   given objects and arrows; it maps to WildPrecat with .ob ≡ Ob and
   .hom ≡ hom, and every WildPrecat arises this way from its own structure. `}
def bridge_wstr (Ob : Type) (hom : Ob → Ob → Type) (s : BlindWildPrecatStr Ob hom) : WildPrecat
  ≔ (ob ≔ Ob, hom ≔ hom, idn ≔ s .idn, comp ≔ s .comp, lu ≔ s .lunit, ru ≔ s .runit, assoc ≔ s .assoc)

def bridge_wstr_of (C : WildPrecat) : BlindWildPrecatStr (C .ob) (C .hom)
  ≔ (C .idn, C .comp, C .lu, C .ru, C .assoc)

def bridge_wstr_roundtrip (C : WildPrecat) : Id WildPrecat (bridge_wstr (C .ob) (C .hom) (bridge_wstr_of C)) C
  ≔ refl C

{` def:precategory, def:category. `}
def bridge_p (C : BlindPrecat) : Precat ≔ (bridge_w (C .fst), C .snd)

def bridge_def_precat : Equiv BlindPrecat Precat
  ≔ quasi_inverse_equiv BlindPrecat Precat bridge_p (C ↦ (bridge_w_inv (C .wild), C .homset))
      (C ↦ refl C) (C ↦ refl C)

def bridge_c (C : BlindCat) : Category ≔ (bridge_w (C .fst .fst), C .fst .snd, C .snd)

def bridge_c_inv (C : Category) : BlindCat ≔ ((bridge_w_inv (C .wild), C .homset), C .univalent)

def bridge_def_category : Equiv BlindCat Category
  ≔ quasi_inverse_equiv BlindCat Category bridge_c bridge_c_inv (C ↦ refl C) (C ↦ refl C)

def bridge_def_wild_category : Equiv BlindWildCat WildCategory
  ≔ quasi_inverse_equiv BlindWildCat WildCategory (C ↦ (bridge_w (C .fst), C .snd))
      (C ↦ (bridge_w_inv (C .wild), C .univalent)) (C ↦ refl C) (C ↦ refl C)

{` def:iso-in-cat, def:univalent-cat: definitionally ours. `}
def bridge_def_is_iso (C : BlindWildPrecat) (a b : C .ob) (f : C .hom a b)
  : Id Type (BlindIsIso C a b f) (CatIsIso (bridge_w C) a b f)
  ≔ refl (BlindIsIso C a b f)

def bridge_def_iso (C : BlindWildPrecat) (a b : C .ob) : Id Type (BlindIso C a b) (CatIso (bridge_w C) a b)
  ≔ refl (BlindIso C a b)

def bridge_def_idtoiso (C : BlindWildPrecat) (a b : C .ob) (p : Id (C .ob) a b)
  : Id (CatIso (bridge_w C) a b) (blind_idtoiso C a b p) (cat_idtoiso (bridge_w C) a b p)
  ≔ refl (blind_idtoiso C a b p)

def bridge_def_univalent (C : BlindWildPrecat) : Id Type (BlindIsUnivalent C) (IsUnivalentCat (bridge_w C))
  ≔ refl (BlindIsUnivalent C)


{` def:op-cat. `}
def bridge_def_op (C : BlindWildPrecat) : Id WildPrecat (bridge_w (blind_op C)) (OppositeWild (bridge_w C))
  ≔ refl (OppositeWild (bridge_w C))

{` The category of sets. `}
def bridge_def_set_precat : Id Precat (bridge_p blind_set_precat) (category_precat SetCat)
  ≔ refl (category_precat SetCat)

{` def:functor. `}
def bridge_f (C D : BlindWildPrecat) (F : BlindWildFunctor C D) : WildFunctor (bridge_w C) (bridge_w D)
  ≔ (obj ≔ F .fob, mor ≔ F .fhom, map_id ≔ F .fid, map_comp ≔ F .fcomp)

def bridge_f_inv (C D : BlindWildPrecat) (F : WildFunctor (bridge_w C) (bridge_w D)) : BlindWildFunctor C D
  ≔ (F .obj, F .mor, F .map_id, F .map_comp)

def bridge_def_functor (C D : BlindWildPrecat) : Equiv (BlindWildFunctor C D) (WildFunctor (bridge_w C) (bridge_w D))
  ≔ quasi_inverse_equiv (BlindWildFunctor C D) (WildFunctor (bridge_w C) (bridge_w D)) (bridge_f C D)
      (bridge_f_inv C D) (F ↦ refl F) (F ↦ refl F)

def bridge_def_functor_laws (C D : BlindWildPrecat) (fo : C .ob → D .ob)
  (fh : (a b : C .ob) → C .hom a b → D .hom (fo a) (fo b))
  : Id Type (BlindWildFunctorLaws C D fo fh) (FunctorLaws (bridge_w C) (bridge_w D) (fo, fh))
  ≔ refl (BlindWildFunctorLaws C D fo fh)

def bridge_def_functor_id (C : BlindWildPrecat)
  : Id (WildFunctor (bridge_w C) (bridge_w C)) (bridge_f C C (blind_functor_id C)) (functor_identity (bridge_w C))
  ≔ refl (functor_identity (bridge_w C))

def bridge_def_functor_comp (C D E : BlindWildPrecat) (G : BlindWildFunctor D E) (F : BlindWildFunctor C D)
  : Id (WildFunctor (bridge_w C) (bridge_w E)) (bridge_f C E (blind_functor_comp C D E G F))
      (functor_compose (bridge_w C) (bridge_w D) (bridge_w E) (bridge_f D E G) (bridge_f C D F))
  ≔ refl (functor_compose (bridge_w C) (bridge_w D) (bridge_w E) (bridge_f D E G) (bridge_f C D F))

{` def:full-faithful, def:functor-split-eso, def:we-cat. Ours is
   faithful × full, the blind one full × faithful. `}
def bridge_ff (C D : BlindWildPrecat) (F : BlindWildFunctor C D) (h : IsFullyFaithful (bridge_w C) (bridge_w D) (bridge_f C D F))
  : BlindIsFullyFaithful C D F ≔ (h .snd, h .fst)

def bridge_ff_inv (C D : BlindWildPrecat) (F : BlindWildFunctor C D) (h : BlindIsFullyFaithful C D F)
  : IsFullyFaithful (bridge_w C) (bridge_w D) (bridge_f C D F) ≔ (h .snd, h .fst)

def bridge_def_fully_faithful (C D : BlindWildPrecat) (F : BlindWildFunctor C D)
  : Equiv (BlindIsFullyFaithful C D F) (IsFullyFaithful (bridge_w C) (bridge_w D) (bridge_f C D F))
  ≔ quasi_inverse_equiv (BlindIsFullyFaithful C D F) (IsFullyFaithful (bridge_w C) (bridge_w D) (bridge_f C D F))
      (bridge_ff_inv C D F) (bridge_ff C D F) (h ↦ refl h) (h ↦ refl h)

def bridge_def_split_eso (C D : BlindWildPrecat) (F : BlindWildFunctor C D)
  : Id Type (BlindIsSplitEso C D F) (IsSplitEso (bridge_w C) (bridge_w D) (bridge_f C D F))
  ≔ refl (BlindIsSplitEso C D F)

def bridge_def_eso (C D : BlindWildPrecat) (F : BlindWildFunctor C D)
  : Id Type (BlindIsEso C D F) (IsEso (bridge_w C) (bridge_w D) (bridge_f C D F))
  ≔ refl (BlindIsEso C D F)

def bridge_we (C D : BlindWildPrecat) (F : BlindWildFunctor C D)
  (h : IsWeakEquivalence (bridge_w C) (bridge_w D) (bridge_f C D F)) : BlindIsWeakEquiv C D F
  ≔ (bridge_ff C D F (h .fst), h .snd)

def bridge_we_inv (C D : BlindWildPrecat) (F : BlindWildFunctor C D) (h : BlindIsWeakEquiv C D F)
  : IsWeakEquivalence (bridge_w C) (bridge_w D) (bridge_f C D F)
  ≔ (bridge_ff_inv C D F (h .fst), h .snd)

{` def:nat-trans. `}
def bridge_nt (C D : BlindWildPrecat) (F G : BlindWildFunctor C D) (al : BlindNatTrans C D F G)
  : WildNatTrans (bridge_w C) (bridge_w D) (bridge_f C D F) (bridge_f C D G)
  ≔ (component ≔ al .fst, natural ≔ al .snd)

def bridge_nt_inv (C D : BlindWildPrecat) (F G : BlindWildFunctor C D)
  (al : WildNatTrans (bridge_w C) (bridge_w D) (bridge_f C D F) (bridge_f C D G)) : BlindNatTrans C D F G
  ≔ (al .component, al .natural)

def bridge_def_nat_trans (C D : BlindWildPrecat) (F G : BlindWildFunctor C D)
  : Equiv (BlindNatTrans C D F G) (WildNatTrans (bridge_w C) (bridge_w D) (bridge_f C D F) (bridge_f C D G))
  ≔ quasi_inverse_equiv (BlindNatTrans C D F G) (WildNatTrans (bridge_w C) (bridge_w D) (bridge_f C D F) (bridge_f C D G))
      (bridge_nt C D F G) (bridge_nt_inv C D F G) (al ↦ refl al) (al ↦ refl al)

def bridge_def_nat_squares (C D : BlindWildPrecat) (F G : BlindWildFunctor C D)
  (al : (a : C .ob) → D .hom (F .fob a) (G .fob a))
  : Id Type (BlindNatSquares C D F G al) (NatSquare (bridge_w C) (bridge_w D) (bridge_f C D F) (bridge_f C D G) al)
  ≔ refl (BlindNatSquares C D F G al)

def bridge_def_nat_id (C D : BlindWildPrecat) (F : BlindWildFunctor C D)
  : Id (WildNatTrans (bridge_w C) (bridge_w D) (bridge_f C D F) (bridge_f C D F))
      (bridge_nt C D F F (blind_nat_id C D F)) (nat_trans_identity (bridge_w C) (bridge_w D) (bridge_f C D F))
  ≔ refl (nat_trans_identity (bridge_w C) (bridge_w D) (bridge_f C D F))

def bridge_def_nat_comp (C D : BlindWildPrecat) (F G H : BlindWildFunctor C D) (be : BlindNatTrans C D G H)
  (al : BlindNatTrans C D F G)
  : Id (WildNatTrans (bridge_w C) (bridge_w D) (bridge_f C D F) (bridge_f C D H))
      (bridge_nt C D F H (blind_nat_comp C D F G H be al))
      (nat_trans_compose (bridge_w C) (bridge_w D) (bridge_f C D F) (bridge_f C D G) (bridge_f C D H)
        (bridge_nt C D G H be) (bridge_nt C D F G al))
  ≔ refl (bridge_nt C D F H (blind_nat_comp C D F G H be al))

{` def:functor-cat. The blind functor precategory has objects
   BlindWildFunctor and arrows BlindNatTrans (nominally different records),
   so it is related to ours by a strict isomorphism: translation functors
   both ways whose composites are the identity on the nose. `}
def BridgeFP (C : BlindWildPrecat) (D : BlindPrecat) : WildPrecat ≔ bridge_w (blind_functor_precat C D .fst)

def BridgeOurFP (C : BlindWildPrecat) (D : BlindPrecat) : WildPrecat ≔ FunctorWild (bridge_w C) (bridge_p D)

def bridge_fp_functor (C : BlindWildPrecat) (D : BlindPrecat) : WildFunctor (BridgeFP C D) (BridgeOurFP C D)
  ≔ (obj ≔ bridge_f C (D .fst),
     mor ≔ bridge_nt C (D .fst),
     map_id ≔ F ↦ refl (nat_trans_identity (bridge_w C) (bridge_w (D .fst)) (bridge_f C (D .fst) F)),
     map_comp ≔ F G H al be ↦ refl (bridge_nt C (D .fst) F H (blind_nat_comp C (D .fst) F G H be al)))

def bridge_fp_functor_inv (C : BlindWildPrecat) (D : BlindPrecat) : WildFunctor (BridgeOurFP C D) (BridgeFP C D)
  ≔ (obj ≔ bridge_f_inv C (D .fst),
     mor ≔ F G ↦ bridge_nt_inv C (D .fst) (bridge_f_inv C (D .fst) F) (bridge_f_inv C (D .fst) G),
     map_id ≔ F ↦ refl (blind_nat_id C (D .fst) (bridge_f_inv C (D .fst) F)),
     map_comp ≔ F G H al be ↦ refl (blind_nat_comp C (D .fst) (bridge_f_inv C (D .fst) F) (bridge_f_inv C (D .fst) G)
        (bridge_f_inv C (D .fst) H) (bridge_nt_inv C (D .fst) (bridge_f_inv C (D .fst) G) (bridge_f_inv C (D .fst) H) be)
        (bridge_nt_inv C (D .fst) (bridge_f_inv C (D .fst) F) (bridge_f_inv C (D .fst) G) al)))


{` Isomorphisms in the two functor precategories correspond (the iso
   conditions are propositions, so the round trips reduce to the arrows,
   which round-trip on the nose). `}
def bridge_fp_iso_equiv (C : BlindWildPrecat) (D : BlindPrecat) (F G : BlindWildFunctor C (D .fst))
  : Equiv (CatIso (BridgeFP C D) F G) (CatIso (BridgeOurFP C D) (bridge_f C (D .fst) F) (bridge_f C (D .fst) G))
  ≔ quasi_inverse_equiv (CatIso (BridgeFP C D) F G)
      (CatIso (BridgeOurFP C D) (bridge_f C (D .fst) F) (bridge_f C (D .fst) G))
      (functor_iso (BridgeFP C D) (BridgeOurFP C D) (bridge_fp_functor C D) F G)
      (functor_iso (BridgeOurFP C D) (BridgeFP C D) (bridge_fp_functor_inv C D)
         (bridge_f C (D .fst) F) (bridge_f C (D .fst) G))
      (e ↦ cat_iso_path (BridgeFP C D) F G
         (functor_iso (BridgeOurFP C D) (BridgeFP C D) (bridge_fp_functor_inv C D)
           (bridge_f C (D .fst) F) (bridge_f C (D .fst) G)
           (functor_iso (BridgeFP C D) (BridgeOurFP C D) (bridge_fp_functor C D) F G e))
         e (refl (e .fst)))
      (e ↦ cat_iso_path (BridgeOurFP C D) (bridge_f C (D .fst) F) (bridge_f C (D .fst) G)
         (functor_iso (BridgeFP C D) (BridgeOurFP C D) (bridge_fp_functor C D) F G
           (functor_iso (BridgeOurFP C D) (BridgeFP C D) (bridge_fp_functor_inv C D)
             (bridge_f C (D .fst) F) (bridge_f C (D .fst) G) e))
         e (refl (e .fst)))

def bridge_functor_path_equiv (C D : BlindWildPrecat) (F G : BlindWildFunctor C D)
  : Equiv (Id (BlindWildFunctor C D) F G) (Id (WildFunctor (bridge_w C) (bridge_w D)) (bridge_f C D F) (bridge_f C D G))
  ≔ quasi_inverse_equiv (Id (BlindWildFunctor C D) F G)
      (Id (WildFunctor (bridge_w C) (bridge_w D)) (bridge_f C D F) (bridge_f C D G))
      (p ↦ refl (bridge_f C D) p) (q ↦ refl (bridge_f_inv C D) q) (p ↦ refl p) (q ↦ refl q)

{` Univalence transfers from ours to the blind functor precategory. `}
def bridge_fp_univalent (C : BlindWildPrecat) (D : BlindPrecat) (u : IsUnivalentCat (BridgeOurFP C D))
  : BlindIsUnivalent (blind_functor_precat C D .fst)
  ≔ cat_univalent_from_equivalences (BridgeFP C D) (F G ↦
      compose_equiv (Id (BlindWildFunctor C (D .fst)) F G)
        (Id (WildFunctor (bridge_w C) (bridge_w (D .fst))) (bridge_f C (D .fst) F) (bridge_f C (D .fst) G))
        (CatIso (BridgeFP C D) F G)
        (bridge_functor_path_equiv C (D .fst) F G)
        (compose_equiv (Id (WildFunctor (bridge_w C) (bridge_w (D .fst))) (bridge_f C (D .fst) F) (bridge_f C (D .fst) G))
          (CatIso (BridgeOurFP C D) (bridge_f C (D .fst) F) (bridge_f C (D .fst) G))
          (CatIso (BridgeFP C D) F G)
          (cat_idtoiso_equiv (BridgeOurFP C D) u (bridge_f C (D .fst) F) (bridge_f C (D .fst) G))
          (canonical_inverse_equiv (CatIso (BridgeFP C D) F G)
            (CatIso (BridgeOurFP C D) (bridge_f C (D .fst) F) (bridge_f C (D .fst) G))
            (bridge_fp_iso_equiv C D F G))))

{` Presheaves and the Yoneda embedding. `}
def bridge_def_psh (C : BlindPrecat)
  : Id WildPrecat (BridgeOurFP (blind_op (C .fst)) blind_set_precat) (PresheafCategory (bridge_p C) .wild)
  ≔ refl (PresheafCategory (bridge_p C) .wild)

def bridge_def_yo_ob (C : BlindPrecat) (c : C .fst .ob)
  : Id (WildFunctor (OppositeWild (bridge_w (C .fst))) SetWild)
      (bridge_f (blind_op (C .fst)) (blind_set_precat .fst) (blind_yo_ob C c)) (representable_presheaf (bridge_p C) c)
  ≔ refl (representable_presheaf (bridge_p C) c)

def bridge_def_yo_hom (C : BlindPrecat) (c c' : C .fst .ob) (k : C .fst .hom c c')
  : Id (WildNatTrans (OppositeWild (bridge_w (C .fst))) SetWild (representable_presheaf (bridge_p C) c)
        (representable_presheaf (bridge_p C) c'))
      (bridge_nt (blind_op (C .fst)) (blind_set_precat .fst) (blind_yo_ob C c) (blind_yo_ob C c') (blind_yo_hom C c c' k))
      (yoneda_nat_trans (bridge_p C) c c' k)
  ≔ refl (yoneda_nat_trans (bridge_p C) c c' k)

{` def:adjunction. Our RightAdjointData has the same fields; the blind
   left-naturality takes (c c' d f), ours (c c' f d). `}
def bridge_radj (C D : BlindWildPrecat) (F : BlindWildFunctor C D) (R : BlindRightAdjoint C D F)
  : RightAdjointData (bridge_w C) (bridge_w D) (bridge_f C D F)
  ≔ (right ≔ bridge_f D C (R .fst),
     transpose ≔ R .snd .fst,
     transpose_iso ≔ R .snd .snd .fst,
     natural_left ≔ c c' f d ↦ R .snd .snd .snd .snd c c' d f,
     natural_right ≔ R .snd .snd .snd .fst)

def bridge_radj_inv (C D : BlindWildPrecat) (F : BlindWildFunctor C D)
  (R : RightAdjointData (bridge_w C) (bridge_w D) (bridge_f C D F)) : BlindRightAdjoint C D F
  ≔ (bridge_f_inv D C (R .right),
     (R .transpose, (R .transpose_iso, (R .natural_right, (c c' d f ↦ R .natural_left c c' f d)))))

def bridge_def_right_adjoint (C D : BlindWildPrecat) (F : BlindWildFunctor C D)
  : Equiv (BlindRightAdjoint C D F) (RightAdjointData (bridge_w C) (bridge_w D) (bridge_f C D F))
  ≔ quasi_inverse_equiv (BlindRightAdjoint C D F) (RightAdjointData (bridge_w C) (bridge_w D) (bridge_f C D F))
      (bridge_radj C D F) (bridge_radj_inv C D F) (R ↦ refl R) (R ↦ refl R)

def bridge_def_adj_unit (C D : BlindWildPrecat) (A : BlindAdjunction C D) (c : C .ob)
  : Id (C .hom c (A .right .fob (A .left .fob c))) (blind_adj_unit C D A c)
      (adjunction_unit (bridge_w C) (bridge_w D) (bridge_f C D (A .left)) (bridge_radj C D (A .left) (A .right, A .adj)) c)
  ≔ refl (blind_adj_unit C D A c)

def bridge_def_adj_counit (C D : BlindWildPrecat) (A : BlindAdjunction C D) (d : D .ob)
  : Id (D .hom (A .left .fob (A .right .fob d)) d) (blind_adj_counit C D A d)
      (adjunction_counit (bridge_w C) (bridge_w D) (bridge_f C D (A .left)) (bridge_radj C D (A .left) (A .right, A .adj)) d)
  ≔ refl (blind_adj_counit C D A d)

{` def:cat-equiv. `}
def bridge_ce (C D : BlindWildPrecat) (F : BlindWildFunctor C D) (e : BlindIsCatEquiv C D F)
  : IsCatEquivalence (bridge_w C) (bridge_w D) (bridge_f C D F)
  ≔ (bridge_radj C D F (e .fst), e .snd)

def bridge_ce_inv (C D : BlindWildPrecat) (F : BlindWildFunctor C D)
  (e : IsCatEquivalence (bridge_w C) (bridge_w D) (bridge_f C D F)) : BlindIsCatEquiv C D F
  ≔ (bridge_radj_inv C D F (e .fst), e .snd)

def bridge_def_cat_equiv (C D : BlindWildPrecat) (F : BlindWildFunctor C D)
  : Equiv (BlindIsCatEquiv C D F) (IsCatEquivalence (bridge_w C) (bridge_w D) (bridge_f C D F))
  ≔ quasi_inverse_equiv (BlindIsCatEquiv C D F) (IsCatEquivalence (bridge_w C) (bridge_w D) (bridge_f C D F))
      (bridge_ce C D F) (bridge_ce_inv C D F) (e ↦ refl e) (e ↦ refl e)

def bridge_def_cat_equivalence (C D : BlindWildPrecat)
  : Equiv (BlindCatEquiv C D) (CatEquivalence (bridge_w C) (bridge_w D))
  ≔ quasi_inverse_equiv (BlindCatEquiv C D) (CatEquivalence (bridge_w C) (bridge_w D))
      (e ↦ (bridge_f C D (e .fst), bridge_ce C D (e .fst) (e .snd)))
      (e ↦ (bridge_f_inv C D (e .fst), bridge_ce_inv C D (bridge_f_inv C D (e .fst)) (e .snd)))
      (e ↦ refl e) (e ↦ refl e)
