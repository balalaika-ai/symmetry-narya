import "bridge-00-core"
import "bridge-03-functors"

{` Bridges for cats.tex, section "The Yoneda Lemma" (blind file 05).
   Blind presheaves are blind functors C^op → Set and blind natural
   transformations; ours are WildFunctor/WildNatTrans into SetWild. The
   core identifies the representables and yo on arrows on the nose. `}

def BridgeBX (C : BlindPrecat) (c : C .fst .ob) (F : BlindWildFunctor (blind_op (C .fst)) (blind_set_precat .fst))
  : SetTypes ≔ blind_yoneda_hom_set C c F

def BridgeOX (C : BlindPrecat) (c : C .fst .ob) (F : BlindWildFunctor (blind_op (C .fst)) (blind_set_precat .fst))
  : SetTypes
  ≔ presheaf_hom_set (bridge_p C) (representable_presheaf (bridge_p C) c)
      (bridge_f (blind_op (C .fst)) (blind_set_precat .fst) F)

def bridge_nt_set_iso (C : BlindPrecat) (c : C .fst .ob) (F : BlindWildFunctor (blind_op (C .fst)) (blind_set_precat .fst))
  : CatIso SetWild (BridgeBX C c F) (BridgeOX C c F)
  ≔ (bridge_nt (blind_op (C .fst)) (blind_set_precat .fst) (blind_yo_ob C c) F,
     ((bridge_nt_inv (blind_op (C .fst)) (blind_set_precat .fst) (blind_yo_ob C c) F,
       refl ((x ↦ x) : BridgeOX C c F .fst → BridgeOX C c F .fst)),
      (bridge_nt_inv (blind_op (C .fst)) (blind_set_precat .fst) (blind_yo_ob C c) F,
       refl ((x ↦ x) : BridgeBX C c F .fst → BridgeBX C c F .fst))))

{` def:yoneda: the blind Yoneda functor followed by the translation of
   presheaves has ours as action on objects and arrows. `}
def bridge_def_yoneda (C : BlindPrecat)
  : Id (FunctorData (bridge_w (C .fst)) (PresheafCategory (bridge_p C) .wild))
      (functor_data (bridge_w (C .fst)) (PresheafCategory (bridge_p C) .wild)
        (functor_compose (bridge_w (C .fst)) (BridgeFP (blind_op (C .fst)) blind_set_precat)
          (PresheafCategory (bridge_p C) .wild) (bridge_fp_functor (blind_op (C .fst)) blind_set_precat)
          (bridge_f (C .fst) (blind_psh C .fst) (blind_yoneda C))))
      (functor_data (bridge_w (C .fst)) (PresheafCategory (bridge_p C) .wild) (yoneda_functor (bridge_p C)))
  ≔ refl (functor_data (bridge_w (C .fst)) (PresheafCategory (bridge_p C) .wild) (yoneda_functor (bridge_p C)))

{` thm:yoneda-lemma. (1) evaluation is an iso in Set: ours composed with the
   iso of hom-sets given by the record translation; (2), (3) naturality in
   F and in c: ours precomposed with the translation. `}
def bridge_thm_yoneda_lemma : blind_thm_yoneda_lemma
  ≔ C ↦
    let W ≔ C .fst in
    let Cp ≔ bridge_p C in
    let tr ≔ bridge_f (blind_op W) (blind_set_precat .fst) in
    ((F c ↦ cat_iso_compose SetWild (BridgeBX C c F) (BridgeOX C c F) (F .fob c)
              (yoneda_evaluation Cp (tr F) c, yoneda_lemma_set_iso Cp (tr F) c)
              (bridge_nt_set_iso C c F) .snd),
     ((c F F' be ↦
        refl ((h : BridgeOX C c F .fst → F' .fob c .fst)
                ↦ (al : BridgeBX C c F .fst) ↦ h (bridge_nt (blind_op W) (blind_set_precat .fst) (blind_yo_ob C c) F al))
          (yoneda_natural_in_presheaf Cp c .fst .natural (tr F) (tr F')
             (bridge_nt (blind_op W) (blind_set_precat .fst) F F' be))),
      (F c c' k ↦
        refl ((h : BridgeOX C c F .fst → F .fob c' .fst)
                ↦ (al : BridgeBX C c F .fst) ↦ h (bridge_nt (blind_op W) (blind_set_precat .fst) (blind_yo_ob C c) F al))
          (yoneda_natural_in_object Cp (tr F) .fst .natural c c' k))))

{` cor:yo-ff: the blind arrow maps are ours followed by the inverse record
   translation (an equivalence). `}
def bridge_cor_yo_ff : blind_cor_yo_ff
  ≔ C ↦
    let W ≔ C .fst in
    bridge_ff W (blind_psh C .fst) (blind_yoneda C)
      (fully_faithful_from_equivs (bridge_w W) (BridgeFP (blind_op W) blind_set_precat)
        (bridge_f W (blind_psh C .fst) (blind_yoneda C))
        (a b ↦ book_two_out_of_three_composite (W .hom a b)
           (WildNatTrans (OppositeWild (bridge_w W)) SetWild (representable_presheaf (bridge_p C) a)
              (representable_presheaf (bridge_p C) b))
           (BlindNatTrans (blind_op W) (blind_set_precat .fst) (blind_yo_ob C a) (blind_yo_ob C b))
           (yoneda_functor (bridge_p C) .mor a b) (blind_yoneda C .fhom a b)
           (bridge_nt_inv (blind_op W) (blind_set_precat .fst) (blind_yo_ob C a) (blind_yo_ob C b))
           (refl (blind_yoneda C .fhom a b))
           (fully_faithful_equiv (bridge_w W) (PresheafCategory (bridge_p C) .wild) (yoneda_functor (bridge_p C))
              (yoneda_fully_faithful (bridge_p C)) a b .equiv)
           (book_equivalence
              (WildNatTrans (OppositeWild (bridge_w W)) SetWild (representable_presheaf (bridge_p C) a)
                 (representable_presheaf (bridge_p C) b))
              (BlindNatTrans (blind_op W) (blind_set_precat .fst) (blind_yo_ob C a) (blind_yo_ob C b))
              (canonical_inverse_equiv
                 (BlindNatTrans (blind_op W) (blind_set_precat .fst) (blind_yo_ob C a) (blind_yo_ob C b))
                 (WildNatTrans (OppositeWild (bridge_w W)) SetWild (representable_presheaf (bridge_p C) a)
                    (representable_presheaf (bridge_p C) b))
                 (bridge_def_nat_trans (blind_op W) (blind_set_precat .fst) (blind_yo_ob C a) (blind_yo_ob C b)))
              .equiv)))

{` cor:yo-emb-obj: fibers of the blind object map are equivalent to fibers
   of ours (ap of the record translation). `}
def bridge_yo_fiber_equiv (C : BlindCat) (F : BlindWildFunctor (blind_op (C .fst .fst)) (blind_set_precat .fst))
  : Equiv (BookFiber (C .fst .fst .ob) (BlindWildFunctor (blind_op (C .fst .fst)) (blind_set_precat .fst))
             (blind_yoneda (C .fst) .fob) F)
      (BookFiber (C .fst .fst .ob) (WildFunctor (OppositeWild (bridge_w (C .fst .fst))) SetWild)
         (yoneda_functor (bridge_p (C .fst)) .obj) (bridge_f (blind_op (C .fst .fst)) (blind_set_precat .fst) F))
  ≔ let W ≔ C .fst .fst in
    let tr ≔ bridge_f (blind_op W) (blind_set_precat .fst) in
    let tri ≔ bridge_f_inv (blind_op W) (blind_set_precat .fst) in
    family_equiv (W .ob)
      (c ↦ Id (BlindWildFunctor (blind_op W) (blind_set_precat .fst)) F (blind_yo_ob (C .fst) c))
      (c ↦ Id (WildFunctor (OppositeWild (bridge_w W)) SetWild) (tr F) (representable_presheaf (bridge_p (C .fst)) c))
      (c ↦ quasi_inverse_equiv (Id (BlindWildFunctor (blind_op W) (blind_set_precat .fst)) F (blind_yo_ob (C .fst) c))
         (Id (WildFunctor (OppositeWild (bridge_w W)) SetWild) (tr F) (representable_presheaf (bridge_p (C .fst)) c))
         (p ↦ refl tr p) (q ↦ refl tri q) (p ↦ refl p) (q ↦ refl q))

def bridge_cor_yo_emb_obj : blind_cor_yo_emb_obj
  ≔ C F ↦ prop_from_equiv
      (BookFiber (C .fst .fst .ob) (BlindWildFunctor (blind_op (C .fst .fst)) (blind_set_precat .fst))
         (blind_yoneda (C .fst) .fob) F)
      (BookFiber (C .fst .fst .ob) (WildFunctor (OppositeWild (bridge_w (C .fst .fst))) SetWild)
         (yoneda_functor (bridge_p (C .fst)) .obj) (bridge_f (blind_op (C .fst .fst)) (blind_set_precat .fst) F))
      (bridge_yo_fiber_equiv C F)
      (yoneda_object_embedding (bridge_c C) (bridge_f (blind_op (C .fst .fst)) (blind_set_precat .fst) F))

{` def:repr. The blind Σ-type of representations is ours (IsRepresentable)
   up to the iso translation of the core; the blind mere version is its
   propositional truncation (ours: MerelyRepresentable, module 673). `}
def bridge_def_representation (C : BlindPrecat) (F : BlindWildFunctor (blind_op (C .fst)) (blind_set_precat .fst))
  : Equiv (BlindRepresentation C F) (IsRepresentable (bridge_p C) (bridge_f (blind_op (C .fst)) (blind_set_precat .fst) F))
  ≔ family_equiv (C .fst .ob) (c ↦ BlindIso (blind_psh C .fst) (blind_yo_ob C c) F)
      (c ↦ CatIso (PresheafCategory (bridge_p C) .wild) (representable_presheaf (bridge_p C) c)
             (bridge_f (blind_op (C .fst)) (blind_set_precat .fst) F))
      (c ↦ bridge_fp_iso_equiv (blind_op (C .fst)) blind_set_precat (blind_yo_ob C c) F)

{` cor:repr-prop. `}
def bridge_cor_repr_prop : blind_cor_repr_prop
  ≔ C F ↦ prop_from_equiv (BlindRepresentation (C .fst) F)
      (IsRepresentable (bridge_p (C .fst)) (bridge_f (blind_op (C .fst .fst)) (blind_set_precat .fst) F))
      (bridge_def_representation (C .fst) F)
      (representability_prop (bridge_c C) (bridge_f (blind_op (C .fst .fst)) (blind_set_precat .fst) F))

{` cor:adj-unique. `}
def bridge_cor_adj_unique : blind_cor_adj_unique
  ≔ C D F ↦ prop_from_equiv (BlindRightAdjoint (C .fst .fst) D F)
      (RightAdjointData (bridge_w (C .fst .fst)) (bridge_w D) (bridge_f (C .fst .fst) D F))
      (bridge_def_right_adjoint (C .fst .fst) D F)
      (right_adjoint_data_prop (bridge_c C) (bridge_w D) (bridge_f (C .fst .fst) D F))

{` lem:adj-via-repr. A blind family of isomorphisms of Set-valued
   presheaves Hom_D(F-, d) ≅ yo(G0 d) gives ours (AdjRepresentingData:
   U-valued natural isomorphisms with the same components and squares;
   componentwise invertibility by xca:funext-nat-trans). The blind type of
   extensions is a retract of ours (reassociation, and naturality in d
   pointwise instead of as identifications of functions), hence
   contractible. `}
def bridge_adj_repr_data (C D : BlindPrecat) (F : BlindWildFunctor (C .fst) (D .fst)) (G0 : D .fst .ob → C .fst .ob)
  (al : (d : D .fst .ob) → BlindIso (blind_psh C .fst) (blind_hom_from_functor C D F d) (blind_yo_ob C (G0 d)))
  : AdjRepresentingData (bridge_p C) (bridge_w (D .fst)) (bridge_f (C .fst) (D .fst) F) G0
  ≔ d ↦ ((component ≔ al d .fst .fst, natural ≔ al d .fst .snd),
         bridge_xca_funext_nat_trans (blind_op (C .fst)) blind_set_precat (blind_hom_from_functor C D F d)
           (blind_yo_ob C (G0 d)) (al d .fst) .fst (al d .snd))

def BridgeBlindExt (C D : BlindPrecat) (F : BlindWildFunctor (C .fst) (D .fst)) (G0 : D .fst .ob → C .fst .ob)
  (al : (d : D .fst .ob) → BlindIso (blind_psh C .fst) (blind_hom_from_functor C D F d) (blind_yo_ob C (G0 d)))
  (Gh : (d d' : D .fst .ob) → D .fst .hom d d' → C .fst .hom (G0 d) (G0 d')) : Type
  ≔ Product (BlindWildFunctorLaws (D .fst) (C .fst) G0 Gh)
      ((d d' : D .fst .ob) (k : D .fst .hom d d') (c : C .fst .ob) (h : D .fst .hom (F .fob c) d)
        → Id (C .fst .hom c (G0 d'))
            (C .fst .comp c (G0 d) (G0 d') (Gh d d' k) (al d .fst .fst c h))
            (al d' .fst .fst c (D .fst .comp (F .fob c) d d' k h)))

def bridge_blind_ext_prop (C D : BlindPrecat) (F : BlindWildFunctor (C .fst) (D .fst)) (G0 : D .fst .ob → C .fst .ob)
  (al : (d : D .fst .ob) → BlindIso (blind_psh C .fst) (blind_hom_from_functor C D F d) (blind_yo_ob C (G0 d)))
  (Gh : (d d' : D .fst .ob) → D .fst .hom d d' → C .fst .hom (G0 d) (G0 d')) : isProp (BridgeBlindExt C D F G0 al Gh)
  ≔ let Cw ≔ C .fst in let Dw ≔ D .fst in
    product_prop (BlindWildFunctorLaws Dw Cw G0 Gh)
      ((d d' : Dw .ob) (k : Dw .hom d d') (c : Cw .ob) (h : Dw .hom (F .fob c) d)
        → Id (Cw .hom c (G0 d')) (Cw .comp c (G0 d) (G0 d') (Gh d d' k) (al d .fst .fst c h))
            (al d' .fst .fst c (Dw .comp (F .fob c) d d' k h)))
      (functor_laws_prop (bridge_w Dw) (bridge_w Cw) (C .snd) (G0, Gh))
      (pi_prop (Dw .ob) (d ↦ (d' : Dw .ob) (k : Dw .hom d d') (c : Cw .ob) (h : Dw .hom (F .fob c) d)
          → Id (Cw .hom c (G0 d')) (Cw .comp c (G0 d) (G0 d') (Gh d d' k) (al d .fst .fst c h))
              (al d' .fst .fst c (Dw .comp (F .fob c) d d' k h)))
        (d ↦ pi_prop (Dw .ob) (d' ↦ (k : Dw .hom d d') (c : Cw .ob) (h : Dw .hom (F .fob c) d)
            → Id (Cw .hom c (G0 d')) (Cw .comp c (G0 d) (G0 d') (Gh d d' k) (al d .fst .fst c h))
                (al d' .fst .fst c (Dw .comp (F .fob c) d d' k h)))
          (d' ↦ pi_prop (Dw .hom d d') (k ↦ (c : Cw .ob) (h : Dw .hom (F .fob c) d)
              → Id (Cw .hom c (G0 d')) (Cw .comp c (G0 d) (G0 d') (Gh d d' k) (al d .fst .fst c h))
                  (al d' .fst .fst c (Dw .comp (F .fob c) d d' k h)))
            (k ↦ pi_prop (Cw .ob) (c ↦ (h : Dw .hom (F .fob c) d)
                → Id (Cw .hom c (G0 d')) (Cw .comp c (G0 d) (G0 d') (Gh d d' k) (al d .fst .fst c h))
                    (al d' .fst .fst c (Dw .comp (F .fob c) d d' k h)))
              (c ↦ pi_prop (Dw .hom (F .fob c) d) (h ↦ Id (Cw .hom c (G0 d'))
                    (Cw .comp c (G0 d) (G0 d') (Gh d d' k) (al d .fst .fst c h))
                    (al d' .fst .fst c (Dw .comp (F .fob c) d d' k h)))
                (h ↦ C .snd c (G0 d') (Cw .comp c (G0 d) (G0 d') (Gh d d' k) (al d .fst .fst c h))
                    (al d' .fst .fst c (Dw .comp (F .fob c) d d' k h))))))))

def bridge_lem_adj_via_repr : blind_lem_adj_via_repr
  ≔ C D F G0 al ↦
    let Cw ≔ C .fst in let Dw ≔ D .fst in
    let A ≔ bridge_adj_repr_data C D F G0 al in
    let Ours ≔ AdjunctionExtension (bridge_p C) (bridge_w Dw) (bridge_f Cw Dw F) G0 A in
    let Blind ≔ Σ ((d d' : Dw .ob) → Dw .hom d d' → Cw .hom (G0 d) (G0 d')) (BridgeBlindExt C D F G0 al) in
    let to : Ours → Blind
      ≔ m ↦ (m .fst, ((m .snd .fst, m .snd .snd .fst),
                      d d' k c h ↦ m .snd .snd .snd c d d' k (refl h))) in
    let from : Blind → Ours
      ≔ b ↦ (b .fst, (b .snd .fst .fst, (b .snd .fst .snd,
               c d d' k ↦ funext (Dw .hom (F .fob c) d) (_ ↦ Cw .hom c (G0 d'))
                 (h ↦ Cw .comp c (G0 d) (G0 d') (b .fst d d' k) (al d .fst .fst c h))
                 (h ↦ al d' .fst .fst c (Dw .comp (F .fob c) d d' k h))
                 (h ↦ b .snd .snd d d' k c h)))) in
    book_contraction Blind
      (contractible_retract Ours Blind
        (adjunction_via_representability (bridge_p C) (bridge_w Dw) (bridge_f Cw Dw F) G0 A) to from
        (b ↦ subtype_equal ((d d' : Dw .ob) → Dw .hom d d' → Cw .hom (G0 d) (G0 d')) (BridgeBlindExt C D F G0 al)
           (bridge_blind_ext_prop C D F G0 al) (to (from b)) b (refl (b .fst))))
