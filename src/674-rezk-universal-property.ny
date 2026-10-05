export "673-rezk-completion"
export "646-category-identity"
export "151-equivalence-exercises"

{` Chapter 6, section 6.8: a weak equivalence F : C → D from a precategory
   into a category identifies D with the Rezk completion L(C), compatibly
   with the maps on objects (used for xca:Rezk-completion-1trunc,
   thm:flagged-cat-equiv and rem:chicken-or-egg; it is the step "hence
   inducing an equivalence L(A) ≃ C" in the proof of thm:flagged-cat-equiv).

   Construction (restricted Yoneda): N : D → L(C), N(d) ≔ hom_D(F(-), d)
   = yo_D(d) ∘ F^op. For c : C there is a natural isomorphism
   θ_c : yo_C(c) ≅ N(F c) with components F_{x,c} (F is fully faithful), so
   every N(d) is merely representable (F is essentially surjective). N is
   fully faithful: for d = F c, the composite of N with precomposition by
   θ_c and the Yoneda evaluation is the identity of hom_D(F c, d'), and an
   arbitrary d is merely of this form; N is essentially surjective since
   every object of L(C) is merely some yo_C(c) ≅ N(F c). Hence N is an
   equivalence of categories (thm:ff-eso-equiv), i.e. an identification
   D = L(C) (cor:Cat-ua), and it carries F(c) to η(c). `}

{` Whiskering a natural transformation by a functor on the right. `}
def rezk_whisker_right (B C D : WildPrecat) (G H : WildFunctor C D) (alpha : WildNatTrans C D G H)
  (F : WildFunctor B C)
  : WildNatTrans B D (functor_compose B C D G F) (functor_compose B C D H F)
  ≔ (component ≔ x ↦ alpha .component (F .obj x),
     natural ≔ x y f ↦ alpha .natural (F .obj x) (F .obj y) (F .mor x y f))

{` N(d) ≔ hom_D(F(-), d) : C^op → Set. `}
def restricted_yoneda_presheaf (C : Precat) (D : Category) (F : WildFunctor (C .wild) (D .wild)) (d : D .wild .ob)
  : PresheafCategory C .wild .ob
  ≔ functor_compose (OppositeWild (C .wild)) (OppositeWild (D .wild)) SetWild
      (representable_presheaf (category_precat D) d) (opposite_functor (C .wild) (D .wild) F)

def restricted_yoneda_nat_trans (C : Precat) (D : Category) (F : WildFunctor (C .wild) (D .wild))
  (d d' : D .wild .ob) (g : D .wild .hom d d')
  : PresheafCategory C .wild .hom (restricted_yoneda_presheaf C D F d) (restricted_yoneda_presheaf C D F d')
  ≔ rezk_whisker_right (OppositeWild (C .wild)) (OppositeWild (D .wild)) SetWild
      (representable_presheaf (category_precat D) d) (representable_presheaf (category_precat D) d')
      (yoneda_nat_trans (category_precat D) d d' g) (opposite_functor (C .wild) (D .wild) F)

def restricted_yoneda (C : Precat) (D : Category) (F : WildFunctor (C .wild) (D .wild))
  : WildFunctor (D .wild) (PresheafCategory C .wild)
  ≔ let W ≔ C .wild in
    let V ≔ D .wild in
    let N ≔ restricted_yoneda_presheaf C D F in
    (obj ≔ N,
     mor ≔ restricted_yoneda_nat_trans C D F,
     map_id ≔ d ↦ nat_trans_path_pointwise (OppositeWild W) SetWild set_wild_homset (N d) (N d)
       (restricted_yoneda_nat_trans C D F d d (V .idn d))
       (nat_trans_identity (OppositeWild W) SetWild (N d))
       (x ↦ funext (V .hom (F .obj x) d) (_ ↦ V .hom (F .obj x) d)
          (k ↦ V .comp (F .obj x) d d (V .idn d) k) (k ↦ k) (k ↦ V .lu (F .obj x) d k)),
     map_comp ≔ d d' d'' g g' ↦ nat_trans_path_pointwise (OppositeWild W) SetWild set_wild_homset (N d) (N d'')
       (restricted_yoneda_nat_trans C D F d d'' (V .comp d d' d'' g' g))
       (nat_trans_compose (OppositeWild W) SetWild (N d) (N d') (N d'')
         (restricted_yoneda_nat_trans C D F d' d'' g') (restricted_yoneda_nat_trans C D F d d' g))
       (x ↦ funext (V .hom (F .obj x) d) (_ ↦ V .hom (F .obj x) d'')
          (k ↦ V .comp (F .obj x) d d'' (V .comp d d' d'' g' g) k)
          (k ↦ V .comp (F .obj x) d' d'' g' (V .comp (F .obj x) d d' g k))
          (k ↦ inverse (V .hom (F .obj x) d'') (V .comp (F .obj x) d' d'' g' (V .comp (F .obj x) d d' g k))
             (V .comp (F .obj x) d d'' (V .comp d d' d'' g' g) k)
             (V .assoc (F .obj x) d d' d'' k g g'))))

{` θ_c : yo_C(c) ⇒ N(F c), with components F_{x,c}; natural by F_∘. `}
def restricted_yoneda_theta (C : Precat) (D : Category) (F : WildFunctor (C .wild) (D .wild)) (c : C .wild .ob)
  : PresheafCategory C .wild .hom (yoneda_functor C .obj c) (restricted_yoneda_presheaf C D F (F .obj c))
  ≔ let W ≔ C .wild in
    let V ≔ D .wild in
    (component ≔ x ↦ F .mor x c,
     natural ≔ x y g ↦ funext (W .hom x c) (_ ↦ V .hom (F .obj y) (F .obj c))
       (k ↦ V .comp (F .obj y) (F .obj x) (F .obj c) (F .mor x c k) (F .mor y x g))
       (k ↦ F .mor y c (W .comp y x c k g))
       (k ↦ inverse (V .hom (F .obj y) (F .obj c)) (F .mor y c (W .comp y x c k g))
          (V .comp (F .obj y) (F .obj x) (F .obj c) (F .mor x c k) (F .mor y x g))
          (F .map_comp y x c g k)))

def restricted_yoneda_theta_is_iso (C : Precat) (D : Category) (F : WildFunctor (C .wild) (D .wild))
  (ff : IsFullyFaithful (C .wild) (D .wild) F) (c : C .wild .ob)
  : CatIsIso (PresheafCategory C .wild) (yoneda_functor C .obj c) (restricted_yoneda_presheaf C D F (F .obj c))
      (restricted_yoneda_theta C D F c)
  ≔ functor_cat_components_iso (OppositeWild (C .wild)) (category_precat SetCat)
      (yoneda_functor C .obj c) (restricted_yoneda_presheaf C D F (F .obj c)) (restricted_yoneda_theta C D F c)
      (x ↦ type_equiv_to_is_iso (C .wild .hom x c) (D .wild .hom (F .obj x) (F .obj c)) (F .mor x c)
        (ff_hom_equiv (C .wild) (D .wild) F ff x c .equiv))

def restricted_yoneda_theta_iso (C : Precat) (D : Category) (F : WildFunctor (C .wild) (D .wild))
  (ff : IsFullyFaithful (C .wild) (D .wild) F) (c : C .wild .ob)
  : CatIso (PresheafCategory C .wild) (yoneda_functor C .obj c) (restricted_yoneda_presheaf C D F (F .obj c))
  ≔ (restricted_yoneda_theta C D F c, restricted_yoneda_theta_is_iso C D F ff c)

{` Each N(d) is merely representable. `}
def restricted_yoneda_representable (C : Precat) (D : Category) (F : WildFunctor (C .wild) (D .wild))
  (w : IsWeakEquivalence (C .wild) (D .wild) F) (d : D .wild .ob)
  : Mere (IsRepresentable C (restricted_yoneda_presheaf C D F d))
  ≔ let P ≔ PresheafCategory C .wild in
    let N ≔ restricted_yoneda C D F in
    mere_rec (Σ (C .wild .ob) (c ↦ CatIso (D .wild) (F .obj c) d))
      (Mere (IsRepresentable C (N .obj d))) (mere_isprop (IsRepresentable C (N .obj d)))
      (t ↦ mere (IsRepresentable C (N .obj d))
        (t .fst, cat_iso_compose P (yoneda_functor C .obj (t .fst)) (N .obj (F .obj (t .fst))) (N .obj d)
          (functor_iso (D .wild) P N (F .obj (t .fst)) d (t .snd))
          (restricted_yoneda_theta_iso C D F (w .fst) (t .fst))))
      (w .snd d)

{` N as a functor D → L(C). `}
def restricted_yoneda_rezk (C : Precat) (D : Category) (F : WildFunctor (C .wild) (D .wild))
  (w : IsWeakEquivalence (C .wild) (D .wild) F)
  : WildFunctor (D .wild) (RezkCompletion C .wild)
  ≔ (obj ≔ d ↦ (restricted_yoneda_presheaf C D F d, restricted_yoneda_representable C D F w d),
     mor ≔ restricted_yoneda C D F .mor,
     map_id ≔ restricted_yoneda C D F .map_id,
     map_comp ≔ restricted_yoneda C D F .map_comp)

{` Full faithfulness of N at objects F(c): the composite
   hom_D(F c, d') → Nat(N(F c), N d') → Nat(yo c, N d') → N(d')(c) is the
   identity (by F_id and ρ). `}
def restricted_yoneda_eval_equiv (C : Precat) (D : Category) (F : WildFunctor (C .wild) (D .wild))
  (ff : IsFullyFaithful (C .wild) (D .wild) F) (c : C .wild .ob) (d' : D .wild .ob)
  : Equiv (PresheafCategory C .wild .hom (restricted_yoneda_presheaf C D F (F .obj c)) (restricted_yoneda_presheaf C D F d'))
      (D .wild .hom (F .obj c) d')
  ≔ let P ≔ PresheafCategory C .wild in
    let N ≔ restricted_yoneda_presheaf C D F in
    compose_equiv (P .hom (N (F .obj c)) (N d')) (P .hom (yoneda_functor C .obj c) (N d'))
      (D .wild .hom (F .obj c) d')
      (cat_precompose_equiv P (yoneda_functor C .obj c) (N (F .obj c)) (restricted_yoneda_theta C D F c)
        (restricted_yoneda_theta_is_iso C D F ff c) (N d'))
      (native_equivalence (P .hom (yoneda_functor C .obj c) (N d')) (D .wild .hom (F .obj c) d')
        (yoneda_lemma C (N d') c))

def restricted_yoneda_eval_section (C : Precat) (D : Category) (F : WildFunctor (C .wild) (D .wild))
  (ff : IsFullyFaithful (C .wild) (D .wild) F) (c : C .wild .ob) (d' : D .wild .ob) (g : D .wild .hom (F .obj c) d')
  : Id (D .wild .hom (F .obj c) d')
      (restricted_yoneda_eval_equiv C D F ff c d' .map (restricted_yoneda C D F .mor (F .obj c) d' g)) g
  ≔ let V ≔ D .wild in
    let Fc ≔ F .obj c in
    concat (V .hom Fc d') (V .comp Fc Fc d' g (F .mor c c (C .wild .idn c))) (V .comp Fc Fc d' g (V .idn Fc)) g
      (cat_whisker_left V Fc Fc d' g (F .mor c c (C .wild .idn c)) (V .idn Fc) (F .map_id c))
      (V .ru Fc d' g)

def restricted_yoneda_mor_is_equiv_at (C : Precat) (D : Category) (F : WildFunctor (C .wild) (D .wild))
  (ff : IsFullyFaithful (C .wild) (D .wild) F) (c : C .wild .ob) (d' : D .wild .ob)
  : isEquiv (D .wild .hom (F .obj c) d')
      (PresheafCategory C .wild .hom (restricted_yoneda_presheaf C D F (F .obj c)) (restricted_yoneda_presheaf C D F d'))
      (restricted_yoneda C D F .mor (F .obj c) d')
  ≔ let A ≔ D .wild .hom (F .obj c) d' in
    let B ≔ PresheafCategory C .wild .hom (restricted_yoneda_presheaf C D F (F .obj c)) (restricted_yoneda_presheaf C D F d') in
    let E ≔ restricted_yoneda_eval_equiv C D F ff c d' in
    two_out_of_three_left A B A (restricted_yoneda C D F .mor (F .obj c) d') (identity A) (E .map)
      (funext A (_ ↦ A) (compose A B A (E .map) (restricted_yoneda C D F .mor (F .obj c) d')) (identity A)
        (restricted_yoneda_eval_section C D F ff c d'))
      (identity_equiv A .equiv) (E .equiv)

def restricted_yoneda_mor_is_equiv (C : Precat) (D : Category) (F : WildFunctor (C .wild) (D .wild))
  (w : IsWeakEquivalence (C .wild) (D .wild) F) (d d' : D .wild .ob)
  : isEquiv (D .wild .hom d d')
      (PresheafCategory C .wild .hom (restricted_yoneda_presheaf C D F d) (restricted_yoneda_presheaf C D F d'))
      (restricted_yoneda C D F .mor d d')
  ≔ let N ≔ restricted_yoneda C D F in
    let Q : D .wild .ob → Type
      ≔ z ↦ isEquiv (D .wild .hom z d') (PresheafCategory C .wild .hom (N .obj z) (N .obj d')) (N .mor z d') in
    mere_rec (BookFiber (C .wild .ob) (D .wild .ob) (F .obj) d) (Q d)
      (isequiv_isprop (D .wild .hom d d') (PresheafCategory C .wild .hom (N .obj d) (N .obj d')) (N .mor d d'))
      (t ↦ transport (D .wild .ob) Q (F .obj (t .fst)) d (inverse (D .wild .ob) d (F .obj (t .fst)) (t .snd))
        (restricted_yoneda_mor_is_equiv_at C D F (w .fst) (t .fst) d'))
      (eso_univalent_obj_surjective (C .wild) (D .wild) (D .univalent) F (w .snd) d)

def restricted_yoneda_rezk_ff (C : Precat) (D : Category) (F : WildFunctor (C .wild) (D .wild))
  (w : IsWeakEquivalence (C .wild) (D .wild) F)
  : IsFullyFaithful (D .wild) (RezkCompletion C .wild) (restricted_yoneda_rezk C D F w)
  ≔ fully_faithful_from_equivs (D .wild) (RezkCompletion C .wild) (restricted_yoneda_rezk C D F w)
      (d d' ↦ book_equivalence (D .wild .hom d d')
        (PresheafCategory C .wild .hom (restricted_yoneda_presheaf C D F d) (restricted_yoneda_presheaf C D F d'))
        (restricted_yoneda C D F .mor d d', restricted_yoneda_mor_is_equiv C D F w d d') .equiv)

def restricted_yoneda_rezk_eso (C : Precat) (D : Category) (F : WildFunctor (C .wild) (D .wild))
  (w : IsWeakEquivalence (C .wild) (D .wild) F)
  : IsEso (D .wild) (RezkCompletion C .wild) (restricted_yoneda_rezk C D F w)
  ≔ let P ≔ PresheafCategory C .wild in
    let N ≔ restricted_yoneda_presheaf C D F in
    X ↦ mere_rec (IsRepresentable C (X .fst)) (Mere (Σ (D .wild .ob) (d ↦ CatIso P (N d) (X .fst))))
      (mere_isprop (Σ (D .wild .ob) (d ↦ CatIso P (N d) (X .fst))))
      (r ↦ mere (Σ (D .wild .ob) (d ↦ CatIso P (N d) (X .fst)))
        (F .obj (r .fst),
         cat_iso_compose P (N (F .obj (r .fst))) (yoneda_functor C .obj (r .fst)) (X .fst) (r .snd)
           (cat_iso_inverse P (yoneda_functor C .obj (r .fst)) (N (F .obj (r .fst)))
             (restricted_yoneda_theta_iso C D F (w .fst) (r .fst)))))
      (X .snd)

def restricted_yoneda_rezk_equivalence (C : Precat) (D : Category) (F : WildFunctor (C .wild) (D .wild))
  (w : IsWeakEquivalence (C .wild) (D .wild) F) : CatEquivalence (D .wild) (RezkCompletion C .wild)
  ≔ (restricted_yoneda_rezk C D F w,
     ff_eso_is_cat_equivalence D (category_precat (RezkCompletion C)) (restricted_yoneda_rezk C D F w)
       (restricted_yoneda_rezk_ff C D F w) (restricted_yoneda_rezk_eso C D F w))

{` N(F c) = η(c) in L(C), by univalence of L(C) applied to θ_c. `}
def restricted_yoneda_unit_path (C : Precat) (D : Category) (F : WildFunctor (C .wild) (D .wild))
  (w : IsWeakEquivalence (C .wild) (D .wild) F) (c : C .wild .ob)
  : Id (RezkCompletion C .wild .ob) (restricted_yoneda_rezk C D F w .obj (F .obj c)) (rezk_unit C .obj c)
  ≔ let L ≔ RezkCompletion C in
    inverse (L .wild .ob) (rezk_unit C .obj c) (restricted_yoneda_rezk C D F w .obj (F .obj c))
      (cat_isotoid (L .wild) (L .univalent) (rezk_unit C .obj c) (restricted_yoneda_rezk C D F w .obj (F .obj c))
        (restricted_yoneda_theta_iso C D F (w .fst) c))

{` The identification X = Y given by an equivalence (cor:Cat-ua), and the
   object part of the equivalence it corresponds to. (Stated for variable
   categories: instantiating directly at the concrete record L(C) raised
   bug[E0500] in the pinned Narya.) `}
def category_path_from_equivalence (X Y : Category) (e : CatEquivalence (X .wild) (Y .wild)) : Id Category X Y
  ≔ category_path_equiv X Y .equiv e .center .fst

def category_path_from_equivalence_obj (X Y : Category) (e : CatEquivalence (X .wild) (Y .wild)) (x : X .wild .ob)
  : Id (Y .wild .ob) (category_path_to_equivalence X Y (category_path_from_equivalence X Y e) .fst .obj x)
      (e .fst .obj x)
  ≔ (inverse (CatEquivalence (X .wild) (Y .wild)) e
        (category_path_to_equivalence X Y (category_path_from_equivalence X Y e))
        (category_path_equiv X Y .equiv e .center .snd)) .fst .obj (refl x)

{` The identification D = L(C) induced by a weak equivalence C → D into a
   category D. `}
def rezk_weak_equivalence_path (C : Precat) (D : Category) (F : WildFunctor (C .wild) (D .wild))
  (w : IsWeakEquivalence (C .wild) (D .wild) F) : Id Category D (RezkCompletion C)
  ≔ category_path_from_equivalence D (RezkCompletion C) (restricted_yoneda_rezk_equivalence C D F w)

{` Compatibility with the maps on objects: the equivalence D ≃ L(C)
   corresponding to the identification D = L(C) (cor:Cat-ua) sends F(c)
   to η(c). `}
def rezk_weak_equivalence_path_obj (C : Precat) (D : Category) (F : WildFunctor (C .wild) (D .wild))
  (w : IsWeakEquivalence (C .wild) (D .wild) F) (c : C .wild .ob)
  : Id (RezkCompletion C .wild .ob)
      (category_path_to_equivalence D (RezkCompletion C) (rezk_weak_equivalence_path C D F w) .fst .obj (F .obj c))
      (rezk_unit C .obj c)
  ≔ concat (RezkCompletion C .wild .ob)
      (category_path_to_equivalence D (RezkCompletion C) (rezk_weak_equivalence_path C D F w) .fst .obj (F .obj c))
      (restricted_yoneda_rezk C D F w .obj (F .obj c)) (rezk_unit C .obj c)
      (category_path_from_equivalence_obj D (RezkCompletion C) (restricted_yoneda_rezk_equivalence C D F w) (F .obj c))
      (restricted_yoneda_unit_path C D F w c)

{` Induction on equivalences out of a category (cor:Cat-ua): the type of
   pairs (Y, e : X ≃ Y) is contractible, so a statement about all of them
   follows from the case of the identity equivalence. (This avoids
   computing with path induction over Category, which raised bug[E0500]
   in the pinned Narya.) `}
def CatEquivTotal (X : Category) : Type ≔ Σ Category (Y ↦ CatEquivalence (X .wild) (Y .wild))

def cat_equiv_total_contractible (X : Category) : isContr (CatEquivTotal X)
  ≔ hlevel_equiv zero. (Σ Category (Y ↦ Id Category X Y)) (CatEquivTotal X)
      (family_equiv Category (Y ↦ Id Category X Y) (Y ↦ CatEquivalence (X .wild) (Y .wild))
        (Y ↦ native_equivalence (Id Category X Y) (CatEquivalence (X .wild) (Y .wild)) (category_path_equiv X Y)))
      (iscontr_idfrom Category X)

def cat_equiv_induction (X : Category) (Q : CatEquivTotal X → Type)
  (q0 : Q (X, cat_equivalence_identity (X .wild))) (t : CatEquivTotal X) : Q t
  ≔ transport (CatEquivTotal X) Q (X, cat_equivalence_identity (X .wild)) t
      (contractible_prop (CatEquivTotal X) (cat_equiv_total_contractible X) (X, cat_equivalence_identity (X .wild)) t)
      q0

{` Litmus: N(d) evaluated at x is hom_D(F x, d), and θ_c has components F. `}
def restricted_yoneda_value (C : Precat) (D : Category) (F : WildFunctor (C .wild) (D .wild))
  (d : D .wild .ob) (x : C .wild .ob)
  : Id Type (restricted_yoneda_presheaf C D F d .obj x .fst) (D .wild .hom (F .obj x) d)
  ≔ refl (D .wild .hom (F .obj x) d)
