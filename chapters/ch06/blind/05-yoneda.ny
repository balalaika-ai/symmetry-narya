export "04-adjunctions"

{` Blind statements, chapter 6, section "The Yoneda Lemma".
   Set is blind_set_precat (sets of Narya's single universe), so every
   precategory is "locally small" for it; universe levels are not modelled. `}

{` Presheaves Set^{C^op}. `}
def blind_psh (C : BlindPrecat) : BlindPrecat ≔ blind_functor_precat (blind_op (C .fst)) blind_set_precat

{` def:yoneda. yo(c) = h_c = Hom_C(−, c), action by precomposition. `}
def blind_yo_ob (C : BlindPrecat) (c : C .fst .ob) : BlindWildFunctor (blind_op (C .fst)) (blind_set_precat .fst)
  ≔ let W ≔ C .fst in
    ((x ↦ (W .hom x c, C .snd x c)), (x y f ↦ g ↦ W .comp y x c g f),
     (x ↦ funext (W .hom x c) (_ ↦ W .hom x c) (g ↦ W .comp x x c g (W .idn x)) (g ↦ g) (g ↦ W .runit x c g)),
     (x y z f f' ↦ funext (W .hom x c) (_ ↦ W .hom z c)
        (g ↦ W .comp z x c g (W .comp z y x f f')) (g ↦ W .comp z y c (W .comp y x c g f) f')
        (g ↦ W .assoc z y x c f' f g)))

def blind_yo_hom (C : BlindPrecat) (c c' : C .fst .ob) (k : C .fst .hom c c')
  : BlindNatTrans (blind_op (C .fst)) (blind_set_precat .fst) (blind_yo_ob C c) (blind_yo_ob C c')
  ≔ let W ≔ C .fst in
    ((x ↦ g ↦ W .comp x c c' k g),
     (x y f ↦ funext (W .hom x c) (_ ↦ W .hom y c')
        (g ↦ W .comp y x c' (W .comp x c c' k g) f) (g ↦ W .comp y c c' k (W .comp y x c g f))
        (g ↦ inverse (W .hom y c') (W .comp y c c' k (W .comp y x c g f)) (W .comp y x c' (W .comp x c c' k g) f)
           (W .assoc y x c c' f g k))))

def blind_yoneda (C : BlindPrecat) : BlindWildFunctor (C .fst) (blind_psh C .fst)
  ≔ let W ≔ C .fst in
    (blind_yo_ob C, blind_yo_hom C,
     (c ↦ blind_nat_path (blind_op W) blind_set_precat (blind_yo_ob C c) (blind_yo_ob C c)
        (blind_yo_hom C c c (W .idn c)) (blind_nat_id (blind_op W) (blind_set_precat .fst) (blind_yo_ob C c))
        (x ↦ funext (W .hom x c) (_ ↦ W .hom x c) (g ↦ W .comp x c c (W .idn c) g) (g ↦ g) (g ↦ W .lunit x c g))),
     (c c' c'' k k' ↦ blind_nat_path (blind_op W) blind_set_precat (blind_yo_ob C c) (blind_yo_ob C c'')
        (blind_yo_hom C c c'' (W .comp c c' c'' k' k))
        (blind_nat_comp (blind_op W) (blind_set_precat .fst) (blind_yo_ob C c) (blind_yo_ob C c') (blind_yo_ob C c'')
           (blind_yo_hom C c' c'' k') (blind_yo_hom C c c' k))
        (x ↦ funext (W .hom x c) (_ ↦ W .hom x c'')
           (g ↦ W .comp x c c'' (W .comp c c' c'' k' k) g) (g ↦ W .comp x c' c'' k' (W .comp x c c' k g))
           (g ↦ inverse (W .hom x c'') (W .comp x c' c'' k' (W .comp x c c' k g)) (W .comp x c c'' (W .comp c c' c'' k' k) g)
              (W .assoc x c c' c'' g k k')))))

{` thm:yoneda-lemma. Evaluation at id_c : Hom(yo c, F) → F(c) is an iso in
   Set, natural in F (postcomposition with β : F → F') and in c (for
   k : c' → c: precomposition with yo(k), and F(k)). Squares in the
   orientation of def:nat-trans. `}
def blind_yoneda_hom_set (C : BlindPrecat) (c : C .fst .ob) (F : BlindWildFunctor (blind_op (C .fst)) (blind_set_precat .fst))
  : SetTypes
  ≔ (BlindNatTrans (blind_op (C .fst)) (blind_set_precat .fst) (blind_yo_ob C c) F, blind_psh C .snd (blind_yo_ob C c) F)

def blind_yoneda_eval (C : BlindPrecat) (c : C .fst .ob) (F : BlindWildFunctor (blind_op (C .fst)) (blind_set_precat .fst))
  (al : BlindNatTrans (blind_op (C .fst)) (blind_set_precat .fst) (blind_yo_ob C c) F) : F .fob c .fst
  ≔ al .fst c (C .fst .idn c)

def blind_thm_yoneda_lemma : Type
  ≔ (C : BlindPrecat)
    → let W ≔ C .fst in
      let S ≔ blind_set_precat .fst in
      let P ≔ blind_psh C .fst in
      Product
        ((F : BlindWildFunctor (blind_op W) S) (c : W .ob)
          → BlindIsIso S (blind_yoneda_hom_set C c F) (F .fob c) (blind_yoneda_eval C c F))
        (Product
          ((c : W .ob) (F F' : BlindWildFunctor (blind_op W) S) (be : BlindNatTrans (blind_op W) S F F')
            → Id (BlindNatTrans (blind_op W) S (blind_yo_ob C c) F → F' .fob c .fst)
                (al ↦ be .fst c (blind_yoneda_eval C c F al))
                (al ↦ blind_yoneda_eval C c F' (P .comp (blind_yo_ob C c) F F' be al)))
          ((F : BlindWildFunctor (blind_op W) S) (c c' : W .ob) (k : W .hom c' c)
            → Id (BlindNatTrans (blind_op W) S (blind_yo_ob C c) F → F .fob c' .fst)
                (al ↦ F .fhom c c' k (blind_yoneda_eval C c F al))
                (al ↦ blind_yoneda_eval C c' F
                   (P .comp (blind_yo_ob C c') (blind_yo_ob C c) F al (blind_yo_hom C c' c k)))))

{` cor:yo-ff. `}
def blind_cor_yo_ff : Type
  ≔ (C : BlindPrecat) → BlindIsFullyFaithful (C .fst) (blind_psh C .fst) (blind_yoneda C)

{` cor:yo-emb-obj. Injection = embedding. `}
def blind_cor_yo_emb_obj : Type
  ≔ (C : BlindCat) → IsEmbedding (C .fst .fst .ob) (BlindWildFunctor (blind_op (C .fst .fst)) (blind_set_precat .fst))
      (blind_yoneda (C .fst) .fob)

{` def:repr. AMBIGUOUS: "there exists C together with an iso". cor:repr-prop
   treats it as the type of pairs (a Σ-type, BlindRepresentation), while
   def:Rezk-completion uses isRepr as a predicate for a full subcategory,
   which must be a proposition for an arbitrary precategory: there we use
   the mere existence BlindIsRepr. `}
def BlindRepresentation (C : BlindPrecat) (F : BlindWildFunctor (blind_op (C .fst)) (blind_set_precat .fst)) : Type
  ≔ Σ (C .fst .ob) (c ↦ BlindIso (blind_psh C .fst) (blind_yo_ob C c) F)

def BlindIsRepr (C : BlindPrecat) (F : BlindWildFunctor (blind_op (C .fst)) (blind_set_precat .fst)) : PropTypes
  ≔ (Mere (BlindRepresentation C F), mere_isprop (BlindRepresentation C F))

{` cor:repr-prop. `}
def blind_cor_repr_prop : Type
  ≔ (C : BlindCat) (F : BlindWildFunctor (blind_op (C .fst .fst)) (blind_set_precat .fst))
    → isProp (BlindRepresentation (C .fst) F)

{` lem:adj-via-repr. Hom_D(F−, d) as a presheaf on C. D is taken to be a
   precategory (for a wild D the presheaf would not be Set-valued). `}
def blind_hom_from_functor (C D : BlindPrecat) (F : BlindWildFunctor (C .fst) (D .fst)) (d : D .fst .ob)
  : BlindWildFunctor (blind_op (C .fst)) (blind_set_precat .fst)
  ≔ let W ≔ D .fst in
    ((x ↦ (W .hom (F .fob x) d, D .snd (F .fob x) d)),
     (x y f ↦ h ↦ W .comp (F .fob y) (F .fob x) d h (F .fhom y x f)),
     (x ↦ funext (W .hom (F .fob x) d) (_ ↦ W .hom (F .fob x) d)
        (h ↦ W .comp (F .fob x) (F .fob x) d h (F .fhom x x (C .fst .idn x))) (h ↦ h)
        (h ↦ concat (W .hom (F .fob x) d)
           (W .comp (F .fob x) (F .fob x) d h (F .fhom x x (C .fst .idn x)))
           (W .comp (F .fob x) (F .fob x) d h (W .idn (F .fob x))) h
           (refl (W .comp (F .fob x) (F .fob x) d h) (F .fid x))
           (W .runit (F .fob x) d h))),
     (x y z f g ↦ funext (W .hom (F .fob x) d) (_ ↦ W .hom (F .fob z) d)
        (h ↦ W .comp (F .fob z) (F .fob x) d h (F .fhom z x (C .fst .comp z y x f g)))
        (h ↦ W .comp (F .fob z) (F .fob y) d (W .comp (F .fob y) (F .fob x) d h (F .fhom y x f)) (F .fhom z y g))
        (h ↦ concat (W .hom (F .fob z) d)
           (W .comp (F .fob z) (F .fob x) d h (F .fhom z x (C .fst .comp z y x f g)))
           (W .comp (F .fob z) (F .fob x) d h (W .comp (F .fob z) (F .fob y) (F .fob x) (F .fhom y x f) (F .fhom z y g)))
           (W .comp (F .fob z) (F .fob y) d (W .comp (F .fob y) (F .fob x) d h (F .fhom y x f)) (F .fhom z y g))
           (refl (W .comp (F .fob z) (F .fob x) d h) (F .fcomp z y x g f))
           (W .assoc (F .fob z) (F .fob y) (F .fob x) d (F .fhom z y g) (F .fhom y x f) h))))

def blind_lem_adj_via_repr : Type
  ≔ (C D : BlindPrecat) (F : BlindWildFunctor (C .fst) (D .fst)) (G0 : D .fst .ob → C .fst .ob)
    (al : (d : D .fst .ob) → BlindIso (blind_psh C .fst) (blind_hom_from_functor C D F d) (blind_yo_ob C (G0 d)))
    → BookIsContr
        (Σ ((d d' : D .fst .ob) → D .fst .hom d d' → C .fst .hom (G0 d) (G0 d')) (Gh ↦
          Product (BlindWildFunctorLaws (D .fst) (C .fst) G0 Gh)
            ((d d' : D .fst .ob) (k : D .fst .hom d d') (c : C .fst .ob) (h : D .fst .hom (F .fob c) d)
              → Id (C .fst .hom c (G0 d'))
                  (C .fst .comp c (G0 d) (G0 d') (Gh d d' k) (al d .fst .fst c h))
                  (al d' .fst .fst c (D .fst .comp (F .fob c) d d' k h)))))

{` cor:adj-unique. `}
def blind_cor_adj_unique : Type
  ≔ (C : BlindCat) (D : BlindWildPrecat) (F : BlindWildFunctor (C .fst .fst) D)
    → isProp (BlindRightAdjoint (C .fst .fst) D F)
