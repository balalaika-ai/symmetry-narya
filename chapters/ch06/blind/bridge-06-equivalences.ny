import "bridge-00-core"
import "bridge-03-functors"
import "../../../src/646-category-identity"
import "../../../src/648-cat-equivalence-prop-adj-unique"
import "../../../src/652-precomposition-equivalence"

{` Bridges for cats.tex, section "Equivalences of categories" up to
   lem:precomp-equiv-cat (blind file 06). def:cat-equiv, def:functor-split-eso
   and def:we-cat are bridged in the core (bridge_def_cat_equiv,
   bridge_def_cat_equivalence, bridge_def_split_eso, bridge_def_eso,
   bridge_we). `}

{` lem:cat-equiv-is-prop (ours: C a category, D any wild precategory). `}
def bridge_lem_cat_equiv_is_prop : blind_lem_cat_equiv_is_prop
  ≔ C D F ↦ prop_from_equiv (BlindIsCatEquiv (C .fst .fst) (D .fst) F)
      (IsCatEquivalence (bridge_w (C .fst .fst)) (bridge_w (D .fst)) (bridge_f (C .fst .fst) (D .fst) F))
      (bridge_def_cat_equiv (C .fst .fst) (D .fst) F)
      (is_cat_equivalence_prop (bridge_c C) (bridge_w (D .fst)) (bridge_f (C .fst .fst) (D .fst) F))

{` lem:cat-equiv-ff. `}
def bridge_lem_cat_equiv_ff : blind_lem_cat_equiv_ff
  ≔ C D F e ↦ bridge_ff (C .fst) (D .fst) F
      (cat_equivalence_ff (bridge_p C) (bridge_p D) (bridge_f (C .fst) (D .fst) F) (bridge_ce (C .fst) (D .fst) F e))

{` lem:equiv-precat-is-ff-split-eso. The blind map (ff e, d ↦ (G d, ε_d))
   is ours (cat_equivalence_to_ff_split_eso) conjugated by the record
   translations; ours is an equivalence (cat_equivalence_ff_split_eso_equiv). `}
def bridge_ff_se_swap (C D : BlindWildPrecat) (F : BlindWildFunctor C D)
  : Equiv (Product (IsFullyFaithful (bridge_w C) (bridge_w D) (bridge_f C D F)) (IsSplitEso (bridge_w C) (bridge_w D) (bridge_f C D F)))
      (Product (BlindIsFullyFaithful C D F) (BlindIsSplitEso C D F))
  ≔ quasi_inverse_equiv
      (Product (IsFullyFaithful (bridge_w C) (bridge_w D) (bridge_f C D F)) (IsSplitEso (bridge_w C) (bridge_w D) (bridge_f C D F)))
      (Product (BlindIsFullyFaithful C D F) (BlindIsSplitEso C D F))
      (x ↦ (bridge_ff C D F (x .fst), x .snd)) (x ↦ (bridge_ff_inv C D F (x .fst), x .snd))
      (x ↦ refl x) (x ↦ refl x)

def bridge_lem_equiv_precat_is_ff_split_eso : blind_lem_equiv_precat_is_ff_split_eso
  ≔ C D F ↦
    let Cw ≔ C .fst in let Dw ≔ D .fst in
    let FF ≔ IsFullyFaithful (bridge_w Cw) (bridge_w Dw) (bridge_f Cw Dw F) in
    let SE ≔ IsSplitEso (bridge_w Cw) (bridge_w Dw) (bridge_f Cw Dw F) in
    let OE ≔ IsCatEquivalence (bridge_w Cw) (bridge_w Dw) (bridge_f Cw Dw F) in
    ((e ↦ bridge_ff Cw Dw F (cat_equivalence_ff (bridge_p C) (bridge_p D) (bridge_f Cw Dw F) (bridge_ce Cw Dw F e))),
     book_equivalence (BlindIsCatEquiv Cw Dw F) (Product (BlindIsFullyFaithful Cw Dw F) (BlindIsSplitEso Cw Dw F))
       (compose_equiv (BlindIsCatEquiv Cw Dw F) OE (Product (BlindIsFullyFaithful Cw Dw F) (BlindIsSplitEso Cw Dw F))
          (bridge_def_cat_equiv Cw Dw F)
          (compose_equiv OE (Product FF SE) (Product (BlindIsFullyFaithful Cw Dw F) (BlindIsSplitEso Cw Dw F))
             (native_equivalence OE (Product FF SE)
                (cat_equivalence_ff_split_eso_equiv (bridge_p C) (bridge_p D) (bridge_f Cw Dw F)))
             (bridge_ff_se_swap Cw Dw F)))
       .equiv)

{` lem:ff-eso (ours: D any wild precategory). `}
def bridge_lem_ff_eso : blind_lem_ff_eso
  ≔ C D F h d ↦ ff_iso_fiber_prop (bridge_c C) (bridge_w (D .fst)) (bridge_f (C .fst .fst) (D .fst) F)
      (bridge_ff_inv (C .fst .fst) (D .fst) F h) d

{` thm:ff-eso-equiv. Fibers of the blind projection BlindCatEquiv → functors
   are fibers of ours (module 643). `}
def bridge_ce_fiber_equiv (C D : BlindWildPrecat) (F : BlindWildFunctor C D)
  : Equiv (BookFiber (BlindCatEquiv C D) (BlindWildFunctor C D) (e ↦ e .fst) F)
      (BookFiber (CatEquivalence (bridge_w C) (bridge_w D)) (WildFunctor (bridge_w C) (bridge_w D))
         (cat_equivalence_projection (bridge_w C) (bridge_w D)) (bridge_f C D F))
  ≔ quasi_inverse_equiv (BookFiber (BlindCatEquiv C D) (BlindWildFunctor C D) (e ↦ e .fst) F)
      (BookFiber (CatEquivalence (bridge_w C) (bridge_w D)) (WildFunctor (bridge_w C) (bridge_w D))
         (cat_equivalence_projection (bridge_w C) (bridge_w D)) (bridge_f C D F))
      (t ↦ (bridge_def_cat_equivalence C D .map (t .fst), refl (bridge_f C D) (t .snd)))
      (t ↦ (equiv_inverse_map (BlindCatEquiv C D) (CatEquivalence (bridge_w C) (bridge_w D))
              (bridge_def_cat_equivalence C D) (t .fst),
            refl (bridge_f_inv C D) (t .snd)))
      (t ↦ refl t) (t ↦ refl t)

def bridge_mere_map (A B : Type) (f : A → B) (t : Mere A) : Mere B
  ≔ mere_rec A (Mere B) (mere_isprop B) (a ↦ mere B (f a)) t

def bridge_thm_ff_eso_equiv : blind_thm_ff_eso_equiv
  ≔ C D ↦
    let Cw ≔ C .fst .fst in let Dw ≔ D .fst in
    let Ow ≔ bridge_w Dw in
    (F ↦ prop_from_equiv (BookFiber (BlindCatEquiv Cw Dw) (BlindWildFunctor Cw Dw) (e ↦ e .fst) F)
           (BookFiber (CatEquivalence (bridge_w Cw) Ow) (WildFunctor (bridge_w Cw) Ow)
              (cat_equivalence_projection (bridge_w Cw) Ow) (bridge_f Cw Dw F))
           (bridge_ce_fiber_equiv Cw Dw F)
           (cat_equivalence_projection_injective (bridge_c C) Ow (bridge_f Cw Dw F)),
     F ↦
       let BF ≔ BookFiber (BlindCatEquiv Cw Dw) (BlindWildFunctor Cw Dw) (e ↦ e .fst) F in
       let OF ≔ BookFiber (CatEquivalence (bridge_w Cw) Ow) (WildFunctor (bridge_w Cw) Ow)
                  (cat_equivalence_projection (bridge_w Cw) Ow) (bridge_f Cw Dw F) in
       let im ≔ native_equivalence (Mere OF) (IsWeakEquivalence (bridge_w Cw) Ow (bridge_f Cw Dw F))
                  (cat_equivalence_projection_image (bridge_c C) Ow (bridge_f Cw Dw F)) in
       (m ↦ bridge_we Cw Dw F (im .map (bridge_mere_map BF OF (bridge_ce_fiber_equiv Cw Dw F .map) m)),
        w ↦ bridge_mere_map OF BF (equiv_inverse_map BF OF (bridge_ce_fiber_equiv Cw Dw F))
              (equiv_inverse_map (Mere OF) (IsWeakEquivalence (bridge_w Cw) Ow (bridge_f Cw Dw F)) im
                 (bridge_we_inv Cw Dw F w))))

{` cor:cat-2-type. `}
def bridge_cor_cat_2_type : blind_cor_cat_2_type
  ≔ hlevel_equiv (suc. (suc. (suc. (suc. zero.)))) Category BlindCat
      (canonical_inverse_equiv BlindCat Category bridge_def_category) category_type_two_truncated

{` cor:Cat-ua. The blind idtoeqv (J on BlindCat, refl ↦ identity
   equivalence) is homotopic to ours (category_path_equiv, module 646)
   conjugated by the record translations; both send refl to the identity
   equivalence (typal β-rules of J on both sides). `}
def bridge_ce_inv_map (C D : BlindWildPrecat) (e : CatEquivalence (bridge_w C) (bridge_w D)) : BlindCatEquiv C D
  ≔ (bridge_f_inv C D (e .fst), bridge_ce_inv C D (bridge_f_inv C D (e .fst)) (e .snd))

def bridge_cat_ua_equiv (C D : BlindCat)
  : Equiv (Id BlindCat C D) (BlindCatEquiv (C .fst .fst) (D .fst .fst))
  ≔ compose_equiv (Id BlindCat C D) (Id Category (bridge_c C) (bridge_c D)) (BlindCatEquiv (C .fst .fst) (D .fst .fst))
      (quasi_inverse_equiv (Id BlindCat C D) (Id Category (bridge_c C) (bridge_c D))
         (p ↦ refl bridge_c p) (q ↦ refl bridge_c_inv q) (p ↦ refl p) (q ↦ refl q))
      (compose_equiv (Id Category (bridge_c C) (bridge_c D))
         (CatEquivalence (bridge_w (C .fst .fst)) (bridge_w (D .fst .fst))) (BlindCatEquiv (C .fst .fst) (D .fst .fst))
         (native_equivalence (Id Category (bridge_c C) (bridge_c D))
            (CatEquivalence (bridge_w (C .fst .fst)) (bridge_w (D .fst .fst))) (category_path_equiv (bridge_c C) (bridge_c D)))
         (quasi_inverse_equiv (CatEquivalence (bridge_w (C .fst .fst)) (bridge_w (D .fst .fst)))
            (BlindCatEquiv (C .fst .fst) (D .fst .fst))
            (bridge_ce_inv_map (C .fst .fst) (D .fst .fst))
            (e ↦ (bridge_f (C .fst .fst) (D .fst .fst) (e .fst), bridge_ce (C .fst .fst) (D .fst .fst) (e .fst) (e .snd)))
            (e ↦ refl e) (e ↦ refl e)))

def bridge_cat_ua_base (C : BlindCat)
  : Id (BlindCatEquiv (C .fst .fst) (C .fst .fst)) (bridge_cat_ua_equiv C C .map (refl C)) (blind_idtoeqv_cat C C (refl C))
  ≔ concat (BlindCatEquiv (C .fst .fst) (C .fst .fst)) (bridge_cat_ua_equiv C C .map (refl C))
      (blind_id_cat_equiv (C .fst .fst)) (blind_idtoeqv_cat C C (refl C))
      (refl (bridge_ce_inv_map (C .fst .fst) (C .fst .fst))
         (inverse (CatEquivalence (bridge_w (C .fst .fst)) (bridge_w (C .fst .fst)))
            (cat_equivalence_identity (bridge_w (C .fst .fst)))
            (category_path_to_equivalence (bridge_c C) (bridge_c C) (refl (bridge_c C)))
            (Jβ Category (bridge_c C) (D _ ↦ CatEquivalence (bridge_w (C .fst .fst)) (D .wild))
               (cat_equivalence_identity (bridge_w (C .fst .fst))))))
      (Jβ BlindCat C (E _ ↦ BlindCatEquiv (C .fst .fst) (E .fst .fst)) (blind_id_cat_equiv (C .fst .fst)))

def bridge_cat_ua_homotopy (C D : BlindCat) (p : Id BlindCat C D)
  : Id (BlindCatEquiv (C .fst .fst) (D .fst .fst)) (bridge_cat_ua_equiv C D .map p) (blind_idtoeqv_cat C D p)
  ≔ J BlindCat C (D p ↦ Id (BlindCatEquiv (C .fst .fst) (D .fst .fst)) (bridge_cat_ua_equiv C D .map p)
        (blind_idtoeqv_cat C D p))
      (bridge_cat_ua_base C) D p

def bridge_cor_cat_ua : blind_cor_cat_ua
  ≔ C D ↦ book_two_out_of_three_composite (Id BlindCat C D) (BlindCatEquiv (C .fst .fst) (D .fst .fst))
      (BlindCatEquiv (C .fst .fst) (D .fst .fst))
      (bridge_cat_ua_equiv C D .map) (blind_idtoeqv_cat C D) (x ↦ x)
      (funext (Id BlindCat C D) (_ ↦ BlindCatEquiv (C .fst .fst) (D .fst .fst))
         (p ↦ bridge_cat_ua_equiv C D .map p) (blind_idtoeqv_cat C D) (bridge_cat_ua_homotopy C D))
      (book_equivalence (Id BlindCat C D) (BlindCatEquiv (C .fst .fst) (D .fst .fst)) (bridge_cat_ua_equiv C D) .equiv)
      (book_equivalence (BlindCatEquiv (C .fst .fst) (D .fst .fst)) (BlindCatEquiv (C .fst .fst) (D .fst .fst))
         (identity_equiv (BlindCatEquiv (C .fst .fst) (D .fst .fst))) .equiv)

{` lem:precomp-equiv-cat. The blind precomposition functor is ours
   (module 652) conjugated by the strict isomorphisms between the blind and
   our functor precategories (same composite on objects, whiskering on
   arrows). Full faithfulness and split essential surjectivity transfer,
   and ff + split eso gives an equivalence (module 641). `}
def bridge_precomp_ff (C D : BlindPrecat) (E : BlindCat) (H : BlindWildFunctor (C .fst) (D .fst))
  (w : BlindIsWeakEquiv (C .fst) (D .fst) H)
  : IsFullyFaithful (BridgeFP (D .fst) (E .fst)) (BridgeFP (C .fst) (E .fst))
      (bridge_f (blind_functor_precat (D .fst) (E .fst) .fst) (blind_functor_precat (C .fst) (E .fst) .fst)
        (blind_precomp_functor (C .fst) (D .fst) (E .fst) H))
  ≔ let Cw ≔ C .fst in let Dw ≔ D .fst in let Ew ≔ E .fst .fst in
    let Po ≔ precomposition_functor (bridge_w Cw) (bridge_w Dw) (bridge_p (E .fst)) (bridge_f Cw Dw H) in
    let oe ≔ precomposition_cat_equivalence (bridge_p C) (bridge_p D) (bridge_c E) (bridge_f Cw Dw H)
               (bridge_we_inv Cw Dw H w) in
    let ffo ≔ cat_equivalence_to_ff_split_eso (BridgeOurFP Dw (E .fst)) (BridgeOurFP Cw (E .fst)) Po oe .fst in
    fully_faithful_from_equivs (BridgeFP Dw (E .fst)) (BridgeFP Cw (E .fst))
      (bridge_f (blind_functor_precat Dw (E .fst) .fst) (blind_functor_precat Cw (E .fst) .fst)
        (blind_precomp_functor Cw Dw (E .fst) H))
      (G G' ↦
        let GH ≔ blind_functor_comp Cw Dw Ew G H in
        let G'H ≔ blind_functor_comp Cw Dw Ew G' H in
        book_two_out_of_three_composite (BlindNatTrans Dw Ew G G')
          (WildNatTrans (bridge_w Cw) (bridge_w Ew) (bridge_f Cw Ew GH) (bridge_f Cw Ew G'H))
          (BlindNatTrans Cw Ew GH G'H)
          (x ↦ Po .mor (bridge_f Dw Ew G) (bridge_f Dw Ew G') (bridge_nt Dw Ew G G' x))
          (blind_whisker Cw Dw Ew H G G') (bridge_nt_inv Cw Ew GH G'H)
          (refl (blind_whisker Cw Dw Ew H G G'))
          (book_two_out_of_three_composite (BlindNatTrans Dw Ew G G')
             (WildNatTrans (bridge_w Dw) (bridge_w Ew) (bridge_f Dw Ew G) (bridge_f Dw Ew G'))
             (WildNatTrans (bridge_w Cw) (bridge_w Ew) (bridge_f Cw Ew GH) (bridge_f Cw Ew G'H))
             (bridge_nt Dw Ew G G')
             (x ↦ Po .mor (bridge_f Dw Ew G) (bridge_f Dw Ew G') (bridge_nt Dw Ew G G' x))
             (Po .mor (bridge_f Dw Ew G) (bridge_f Dw Ew G'))
             (refl ((x ↦ Po .mor (bridge_f Dw Ew G) (bridge_f Dw Ew G') (bridge_nt Dw Ew G G' x))
                      : BlindNatTrans Dw Ew G G' → WildNatTrans (bridge_w Cw) (bridge_w Ew) (bridge_f Cw Ew GH) (bridge_f Cw Ew G'H)))
             (book_equivalence (BlindNatTrans Dw Ew G G')
                (WildNatTrans (bridge_w Dw) (bridge_w Ew) (bridge_f Dw Ew G) (bridge_f Dw Ew G'))
                (bridge_def_nat_trans Dw Ew G G') .equiv)
             (fully_faithful_equiv (BridgeOurFP Dw (E .fst)) (BridgeOurFP Cw (E .fst)) Po ffo
                (bridge_f Dw Ew G) (bridge_f Dw Ew G') .equiv))
          (book_equivalence (WildNatTrans (bridge_w Cw) (bridge_w Ew) (bridge_f Cw Ew GH) (bridge_f Cw Ew G'H))
             (BlindNatTrans Cw Ew GH G'H)
             (canonical_inverse_equiv (BlindNatTrans Cw Ew GH G'H)
                (WildNatTrans (bridge_w Cw) (bridge_w Ew) (bridge_f Cw Ew GH) (bridge_f Cw Ew G'H))
                (bridge_def_nat_trans Cw Ew GH G'H)) .equiv))

def bridge_precomp_split_eso (C D : BlindPrecat) (E : BlindCat) (H : BlindWildFunctor (C .fst) (D .fst))
  (w : BlindIsWeakEquiv (C .fst) (D .fst) H)
  : IsSplitEso (BridgeFP (D .fst) (E .fst)) (BridgeFP (C .fst) (E .fst))
      (bridge_f (blind_functor_precat (D .fst) (E .fst) .fst) (blind_functor_precat (C .fst) (E .fst) .fst)
        (blind_precomp_functor (C .fst) (D .fst) (E .fst) H))
  ≔ let Cw ≔ C .fst in let Dw ≔ D .fst in let Ew ≔ E .fst .fst in
    let Po ≔ precomposition_functor (bridge_w Cw) (bridge_w Dw) (bridge_p (E .fst)) (bridge_f Cw Dw H) in
    let oe ≔ precomposition_cat_equivalence (bridge_p C) (bridge_p D) (bridge_c E) (bridge_f Cw Dw H)
               (bridge_we_inv Cw Dw H w) in
    let seo ≔ cat_equivalence_to_ff_split_eso (BridgeOurFP Dw (E .fst)) (BridgeOurFP Cw (E .fst)) Po oe .snd in
    d ↦ (bridge_f_inv Dw Ew (seo (bridge_f Cw Ew d) .fst),
         functor_iso (BridgeOurFP Cw (E .fst)) (BridgeFP Cw (E .fst)) (bridge_fp_functor_inv Cw (E .fst))
           (Po .obj (seo (bridge_f Cw Ew d) .fst)) (bridge_f Cw Ew d) (seo (bridge_f Cw Ew d) .snd))

def bridge_lem_precomp_equiv_cat : blind_lem_precomp_equiv_cat
  ≔ C D E H w ↦
    bridge_ce_inv (blind_functor_precat (D .fst) (E .fst) .fst) (blind_functor_precat (C .fst) (E .fst) .fst)
      (blind_precomp_functor (C .fst) (D .fst) (E .fst) H)
      (ff_split_eso_is_cat_equivalence (BridgeFP (D .fst) (E .fst)) (BridgeFP (C .fst) (E .fst))
         (bridge_f (blind_functor_precat (D .fst) (E .fst) .fst) (blind_functor_precat (C .fst) (E .fst) .fst)
           (blind_precomp_functor (C .fst) (D .fst) (E .fst) H))
         (bridge_precomp_ff C D E H w) (bridge_precomp_split_eso C D E H w))
