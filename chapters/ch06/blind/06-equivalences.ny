export "05-yoneda"

{` Blind statements, chapter 6, section "Equivalences of categories"
   (up to lem:precomp-equiv-cat). `}

{` def:cat-equiv. A left adjoint whose unit and counit (eq:adj-unit-counit)
   are isomorphisms; "isomorphism" of the transformations is taken
   componentwise (for precategories equivalent to invertibility in the
   functor category by xca:funext-nat-trans). `}
def BlindIsCatEquiv (C D : BlindWildPrecat) (F : BlindWildFunctor C D) : Type
  ≔ Σ (BlindRightAdjoint C D F) (R ↦
      let A : BlindAdjunction C D ≔ (F, R .fst, R .snd) in
      Product ((c : C .ob) → BlindIsIso C c (R .fst .fob (F .fob c)) (blind_adj_unit C D A c))
        ((d : D .ob) → BlindIsIso D (F .fob (R .fst .fob d)) d (blind_adj_counit C D A d)))

def BlindCatEquiv (C D : BlindWildPrecat) : Type ≔ Σ (BlindWildFunctor C D) (BlindIsCatEquiv C D)

{` lem:cat-equiv-is-prop. `}
def blind_lem_cat_equiv_is_prop : Type
  ≔ (C : BlindCat) (D : BlindPrecat) (F : BlindWildFunctor (C .fst .fst) (D .fst))
    → isProp (BlindIsCatEquiv (C .fst .fst) (D .fst) F)

{` lem:cat-equiv-ff. `}
def blind_lem_cat_equiv_ff : Type
  ≔ (C D : BlindPrecat) (F : BlindWildFunctor (C .fst) (D .fst))
    → BlindIsCatEquiv (C .fst) (D .fst) F → BlindIsFullyFaithful (C .fst) (D .fst) F

{` def:functor-split-eso. `}
def BlindIsSplitEso (C D : BlindWildPrecat) (F : BlindWildFunctor C D) : Type
  ≔ (d : D .ob) → Σ (C .ob) (c ↦ BlindIso D (F .fob c) d)

def BlindIsEso (C D : BlindWildPrecat) (F : BlindWildFunctor C D) : Type
  ≔ (d : D .ob) → Mere (Σ (C .ob) (c ↦ BlindIso D (F .fob c) d))

{` lem:equiv-precat-is-ff-split-eso. The map uses some proof ff of
   lem:cat-equiv-ff (full faithfulness is a proposition) and d ↦ (G d, ε_d). `}
def blind_lem_equiv_precat_is_ff_split_eso : Type
  ≔ (C D : BlindPrecat) (F : BlindWildFunctor (C .fst) (D .fst))
    → Σ (BlindIsCatEquiv (C .fst) (D .fst) F → BlindIsFullyFaithful (C .fst) (D .fst) F) (ff ↦
        BookIsEquiv (BlindIsCatEquiv (C .fst) (D .fst) F)
          (Product (BlindIsFullyFaithful (C .fst) (D .fst) F) (BlindIsSplitEso (C .fst) (D .fst) F))
          (e ↦ (ff e,
                d ↦ (e .fst .fst .fob d,
                     (blind_adj_counit (C .fst) (D .fst) (F, e .fst .fst, e .fst .snd) d, e .snd .snd d)))))

{` lem:ff-eso. `}
def blind_lem_ff_eso : Type
  ≔ (C : BlindCat) (D : BlindPrecat) (F : BlindWildFunctor (C .fst .fst) (D .fst))
    → BlindIsFullyFaithful (C .fst .fst) (D .fst) F
    → (d : D .fst .ob) → isProp (Σ (C .fst .fst .ob) (c ↦ BlindIso (D .fst) (F .fob c) d))

{` thm:ff-eso-equiv. `}
def blind_thm_ff_eso_equiv : Type
  ≔ (C : BlindCat) (D : BlindPrecat)
    → let Cw ≔ C .fst .fst in let Dw ≔ D .fst in
      Product (IsEmbedding (BlindCatEquiv Cw Dw) (BlindWildFunctor Cw Dw) (e ↦ e .fst))
        ((F : BlindWildFunctor Cw Dw)
          → Product (Mere (BookFiber (BlindCatEquiv Cw Dw) (BlindWildFunctor Cw Dw) (e ↦ e .fst) F)
                       → Product (BlindIsFullyFaithful Cw Dw F) (BlindIsEso Cw Dw F))
              (Product (BlindIsFullyFaithful Cw Dw F) (BlindIsEso Cw Dw F)
                → Mere (BookFiber (BlindCatEquiv Cw Dw) (BlindWildFunctor Cw Dw) (e ↦ e .fst) F)))

{` The identity equivalence. `}
def blind_id_iso_proof (C : BlindWildPrecat) (a : C .ob) : BlindIsIso C a a (C .idn a)
  ≔ ((C .idn a, C .lunit a a (C .idn a)), (C .idn a, C .lunit a a (C .idn a)))

def blind_id_fun_iso (A : Type) : BlindIsIso blind_universe_wild_precat A A (x ↦ x)
  ≔ (((x ↦ x), refl (x ↦ x)), ((x ↦ x), refl (x ↦ x)))

def blind_id_cat_equiv (C : BlindWildPrecat) : BlindCatEquiv C C
  ≔ (blind_functor_id C,
     ((blind_functor_id C,
       ((c d h ↦ h),
        ((c d ↦ blind_id_fun_iso (C .hom c d)),
         ((c d d' k ↦ refl (h ↦ C .comp c d d' k h)),
          (c c' d f ↦ refl (h ↦ C .comp c' c d h f)))))),
      ((c ↦ blind_id_iso_proof C c), (d ↦ blind_id_iso_proof C d))))

{` cor:Cat-ua. `}
def blind_idtoeqv_cat (C D : BlindCat) (p : Id BlindCat C D) : BlindCatEquiv (C .fst .fst) (D .fst .fst)
  ≔ J BlindCat C (E _ ↦ BlindCatEquiv (C .fst .fst) (E .fst .fst)) (blind_id_cat_equiv (C .fst .fst)) D p

def blind_cor_cat_ua : Type
  ≔ (C D : BlindCat) → BookIsEquiv (Id BlindCat C D) (BlindCatEquiv (C .fst .fst) (D .fst .fst)) (blind_idtoeqv_cat C D)

{` cor:cat-2-type. Book level 2 = HLevel 4. `}
def blind_cor_cat_2_type : Type ≔ HLevel (suc. (suc. (suc. (suc. zero.)))) BlindCat

{` def:we-cat. `}
def BlindIsWeakEquiv (C D : BlindWildPrecat) (F : BlindWildFunctor C D) : Type
  ≔ Product (BlindIsFullyFaithful C D F) (BlindIsEso C D F)

{` lem:precomp-equiv-cat. − ∘ H : E^D → E^C (whiskering on arrows). `}
def blind_whisker (C D : BlindWildPrecat) (E : BlindWildPrecat) (H : BlindWildFunctor C D)
  (G G' : BlindWildFunctor D E) (al : BlindNatTrans D E G G')
  : BlindNatTrans C E (blind_functor_comp C D E G H) (blind_functor_comp C D E G' H)
  ≔ ((c ↦ al .fst (H .fob c)), (a b f ↦ al .snd (H .fob a) (H .fob b) (H .fhom a b f)))

def blind_precomp_functor (C D : BlindWildPrecat) (E : BlindPrecat) (H : BlindWildFunctor C D)
  : BlindWildFunctor (blind_functor_precat D E .fst) (blind_functor_precat C E .fst)
  ≔ let W ≔ E .fst in
    ((G ↦ blind_functor_comp C D W G H), blind_whisker C D W H,
     (G ↦ blind_nat_path C E (blind_functor_comp C D W G H) (blind_functor_comp C D W G H)
        (blind_whisker C D W H G G (blind_nat_id D W G)) (blind_nat_id C W (blind_functor_comp C D W G H))
        (c ↦ refl (W .idn (G .fob (H .fob c))))),
     (G G' G'' al be ↦ blind_nat_path C E (blind_functor_comp C D W G H) (blind_functor_comp C D W G'' H)
        (blind_whisker C D W H G G'' (blind_nat_comp D W G G' G'' be al))
        (blind_nat_comp C W (blind_functor_comp C D W G H) (blind_functor_comp C D W G' H)
           (blind_functor_comp C D W G'' H) (blind_whisker C D W H G' G'' be) (blind_whisker C D W H G G' al))
        (c ↦ refl (W .comp (G .fob (H .fob c)) (G' .fob (H .fob c)) (G'' .fob (H .fob c))
                     (be .fst (H .fob c)) (al .fst (H .fob c))))))

def blind_lem_precomp_equiv_cat : Type
  ≔ (C D : BlindPrecat) (E : BlindCat) (H : BlindWildFunctor (C .fst) (D .fst))
    → BlindIsWeakEquiv (C .fst) (D .fst) H
    → BlindIsCatEquiv (blind_functor_precat (D .fst) (E .fst) .fst) (blind_functor_precat (C .fst) (E .fst) .fst)
        (blind_precomp_functor (C .fst) (D .fst) (E .fst) H)
