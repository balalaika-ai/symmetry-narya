export "645-precategory-identity"

{` Chapter 6, section 6.7: cor:Cat-ua (identifications of categories are
   equivalences of categories) and cor:cat-2-type (the type of categories
   is 2-truncated). `}

{` Identifications of categories are identifications of the underlying
   precategories (univalence is a proposition). `}
def category_sigma_equiv : Equiv Category (Σ Precat (P ↦ IsUnivalentCat (P .wild)))
  ≔ quasi_inverse_equiv Category (Σ Precat (P ↦ IsUnivalentCat (P .wild)))
      (C ↦ ((C .wild, C .homset), C .univalent))
      (u ↦ (u .fst .wild, u .fst .homset, u .snd))
      (C ↦ refl C) (u ↦ refl u)

def category_path_precat_equiv (C D : Category)
  : Equiv (Id Category C D) (Id Precat (category_precat C) (category_precat D))
  ≔ let S ≔ Σ Precat (P ↦ IsUnivalentCat (P .wild)) in
    compose_equiv (Id Category C D) (Id S (category_sigma_equiv .map C) (category_sigma_equiv .map D))
      (Id Precat (category_precat C) (category_precat D))
      (equivalence_on_paths Category S category_sigma_equiv C D)
      (subtype_path_equiv Precat (P ↦ IsUnivalentCat (P .wild)) (P ↦ is_univalent_cat_prop (P .wild))
        (category_sigma_equiv .map C) (category_sigma_equiv .map D))

{` Between categories, an isomorphism of precategories is the same as an
   equivalence: "for categories, this is the same as equivalence". An
   equivalence on objects gives essential surjectivity; conversely the
   fibers of F on objects are Σ_c (d = F c) ≃ Σ_c (F c ≅ d), which is a
   proposition (lem:ff-eso) with an element (G d, ε_d). `}
def obj_equiv_eso (C D : WildPrecat) (F : WildFunctor C D) (h : BookIsEquiv (C .ob) (D .ob) (F .obj)) : IsEso C D F
  ≔ d ↦ mere (Σ (C .ob) (c ↦ CatIso D (F .obj c) d))
      (h d .center .fst,
       cat_idtoiso D (F .obj (h d .center .fst)) d
         (inverse (D .ob) d (F .obj (h d .center .fst)) (h d .center .snd)))

def cat_equivalence_obj_fiber_contractible (C D : Category) (F : WildFunctor (C .wild) (D .wild))
  (E : IsCatEquivalence (C .wild) (D .wild) F) (d : D .wild .ob)
  : isContr (BookFiber (C .wild .ob) (D .wild .ob) (F .obj) d)
  ≔ let V ≔ D .wild in
    let I ≔ Σ (C .wild .ob) (c ↦ CatIso V (F .obj c) d) in
    let ff ≔ wild_cat_equivalence_ff (C .wild) V F E in
    ch6c_contr_transfer I (BookFiber (C .wild .ob) (V .ob) (F .obj) d)
      (canonical_inverse_equiv (BookFiber (C .wild .ob) (V .ob) (F .obj) d) I
        (family_equiv (C .wild .ob) (c ↦ Id (V .ob) d (F .obj c)) (c ↦ CatIso V (F .obj c) d)
          (c ↦ compose_equiv (Id (V .ob) d (F .obj c)) (Id (V .ob) (F .obj c) d) (CatIso V (F .obj c) d)
            (inverse_path_equiv (V .ob) d (F .obj c))
            (cat_idtoiso_equiv V (D .univalent) (F .obj c) d))))
      (cat_equivalence_split_eso (C .wild) V F E d, x ↦ ff_iso_fiber_prop C V F ff d x (cat_equivalence_split_eso (C .wild) V F E d))

def cat_equivalence_obj_is_equiv (C D : Category) (F : WildFunctor (C .wild) (D .wild))
  (E : IsCatEquivalence (C .wild) (D .wild) F) : BookIsEquiv (C .wild .ob) (D .wild .ob) (F .obj)
  ≔ d ↦ book_contraction (BookFiber (C .wild .ob) (D .wild .ob) (F .obj) d)
      (cat_equivalence_obj_fiber_contractible C D F E d)

def precat_iso_cat_equivalence_equiv (C D : Category)
  : Equiv (PrecatIsomorphism (category_precat C) (category_precat D)) (CatEquivalence (C .wild) (D .wild))
  ≔ let W ≔ C .wild in
    let V ≔ D .wild in
    family_equiv (WildFunctor W V)
      (F ↦ Product (IsFullyFaithful W V F) (BookIsEquiv (W .ob) (V .ob) (F .obj)))
      (IsCatEquivalence W V)
      (F ↦ iff_equiv (Product (IsFullyFaithful W V F) (BookIsEquiv (W .ob) (V .ob) (F .obj))) (IsCatEquivalence W V F)
        (product_prop (IsFullyFaithful W V F) (BookIsEquiv (W .ob) (V .ob) (F .obj))
          (is_fully_faithful_prop W V F) (book_isequiv_isprop (W .ob) (V .ob) (F .obj)))
        (is_cat_equivalence_prop C V F)
        (x ↦ wild_ff_eso_is_cat_equivalence C V F (x .fst) (obj_equiv_eso W V F (x .snd)))
        (E ↦ (wild_cat_equivalence_ff W V F E, cat_equivalence_obj_is_equiv C D F E)))

{` cor:Cat-ua. The map (C = D) → (C ≃ D) defined by path induction,
   sending refl C to the identity equivalence. `}
def category_path_to_equivalence (C D : Category) (p : Id Category C D) : CatEquivalence (C .wild) (D .wild)
  ≔ J Category C (D _ ↦ CatEquivalence (C .wild) (D .wild)) (cat_equivalence_identity (C .wild)) D p

def category_path_composite_equiv (C D : Category) : Equiv (Id Category C D) (CatEquivalence (C .wild) (D .wild))
  ≔ compose_equiv (Id Category C D) (Id Precat (category_precat C) (category_precat D)) (CatEquivalence (C .wild) (D .wild))
      (category_path_precat_equiv C D)
      (compose_equiv (Id Precat (category_precat C) (category_precat D))
        (PrecatIsomorphism (category_precat C) (category_precat D)) (CatEquivalence (C .wild) (D .wild))
        (native_equivalence (Id Precat (category_precat C) (category_precat D))
          (PrecatIsomorphism (category_precat C) (category_precat D))
          (precategory_path_equiv (category_precat C) (category_precat D)))
        (precat_iso_cat_equivalence_equiv C D))

{` Equivalences out of a category are determined by their functors. `}
def cat_equivalence_path (C : Category) (D : WildPrecat) (e e' : CatEquivalence (C .wild) D)
  (p : Id (WildFunctor (C .wild) D) (e .fst) (e' .fst)) : Id (CatEquivalence (C .wild) D) e e'
  ≔ equiv_inverse_map (Id (CatEquivalence (C .wild) D) e e') (Id (WildFunctor (C .wild) D) (e .fst) (e' .fst))
      (subtype_path_equiv (WildFunctor (C .wild) D) (IsCatEquivalence (C .wild) D) (is_cat_equivalence_prop C D) e e')
      p

def category_path_composite_refl (C : Category)
  : Id (CatEquivalence (C .wild) (C .wild)) (category_path_composite_equiv C C .map (refl C))
      (category_path_to_equivalence C C (refl C))
  ≔ cat_equivalence_path C (C .wild) (category_path_composite_equiv C C .map (refl C))
      (category_path_to_equivalence C C (refl C))
      (concat (WildFunctor (C .wild) (C .wild))
        (category_path_composite_equiv C C .map (refl C) .fst) (functor_identity (C .wild))
        (category_path_to_equivalence C C (refl C) .fst)
        (inverse (PrecatIsomorphism (category_precat C) (category_precat C))
          (precat_identity_isomorphism (category_precat C))
          (precategory_path_to_isomorphism (category_precat C) (category_precat C) (refl (category_precat C)))
          (precategory_path_to_isomorphism_refl (category_precat C)) .fst)
        (Jβ Category C (D _ ↦ CatEquivalence (C .wild) (D .wild)) (cat_equivalence_identity (C .wild)) .fst))

def category_path_composite_homotopy (C D : Category) (p : Id Category C D)
  : Id (CatEquivalence (C .wild) (D .wild)) (category_path_composite_equiv C D .map p) (category_path_to_equivalence C D p)
  ≔ J Category C (D p ↦ Id (CatEquivalence (C .wild) (D .wild)) (category_path_composite_equiv C D .map p)
        (category_path_to_equivalence C D p))
      (category_path_composite_refl C) D p

def category_path_to_equivalence_is_equiv (C D : Category)
  : BookIsEquiv (Id Category C D) (CatEquivalence (C .wild) (D .wild)) (category_path_to_equivalence C D)
  ≔ book_equivalence (Id Category C D) (CatEquivalence (C .wild) (D .wild))
      (equiv_change_map (Id Category C D) (CatEquivalence (C .wild) (D .wild)) (category_path_composite_equiv C D)
        (category_path_to_equivalence C D) (category_path_composite_homotopy C D)) .equiv

def category_path_equiv (C D : Category) : BookEquiv (Id Category C D) (CatEquivalence (C .wild) (D .wild))
  ≔ (category_path_to_equivalence C D, category_path_to_equivalence_is_equiv C D)

{` "the type of functors between categories is 1-truncated" (only the
   codomain needs to be a category). `}
def functor_type_groupoid (C : WildPrecat) (D : Category) : isGroupoid (WildFunctor C (D .wild))
  ≔ let V ≔ D .wild in
    let three : Nat ≔ suc. (suc. (suc. zero.)) in
    let mor_set : (obj : C .ob → V .ob) → isSet ((a b : C .ob) → C .hom a b → V .hom (obj a) (obj b))
      ≔ obj ↦ pi_set (C .ob) (a ↦ (b : C .ob) → C .hom a b → V .hom (obj a) (obj b))
          (a ↦ pi_set (C .ob) (b ↦ C .hom a b → V .hom (obj a) (obj b))
            (b ↦ pi_set (C .hom a b) (_ ↦ V .hom (obj a) (obj b)) (_ ↦ D .homset (obj a) (obj b)))) in
    let data_level : HLevel three (FunctorData C V)
      ≔ hlevel_sigma three (C .ob → V .ob) (obj ↦ (a b : C .ob) → C .hom a b → V .hom (obj a) (obj b))
          (hlevel_function three (C .ob) (V .ob) (groupoid_to_hlevel (V .ob) (category_objects_groupoid D)))
          (obj ↦ hlevel_raise (suc. (suc. zero.)) ((a b : C .ob) → C .hom a b → V .hom (obj a) (obj b))
            (set_to_hlevel_two ((a b : C .ob) → C .hom a b → V .hom (obj a) (obj b)) (mor_set obj))) in
    hlevel_to_groupoid (WildFunctor C V)
      (hlevel_equiv three (Σ (FunctorData C V) (FunctorLaws C V)) (WildFunctor C V)
        (canonical_inverse_equiv (WildFunctor C V) (Σ (FunctorData C V) (FunctorLaws C V)) (functor_sigma_equiv C V))
        (hlevel_sigma three (FunctorData C V) (FunctorLaws C V) data_level
          (t ↦ hlevel_raise (suc. (suc. zero.)) (FunctorLaws C V t)
            (hlevel_raise (suc. zero.) (FunctorLaws C V t)
              (prop_to_hlevel_one (FunctorLaws C V t) (functor_laws_prop C V (D .homset) t))))))

def cat_equivalence_groupoid (C D : Category) : isGroupoid (CatEquivalence (C .wild) (D .wild))
  ≔ let three : Nat ≔ suc. (suc. (suc. zero.)) in
    hlevel_to_groupoid (CatEquivalence (C .wild) (D .wild))
      (hlevel_sigma three (WildFunctor (C .wild) (D .wild)) (IsCatEquivalence (C .wild) (D .wild))
        (groupoid_to_hlevel (WildFunctor (C .wild) (D .wild)) (functor_type_groupoid (C .wild) D))
        (F ↦ hlevel_raise (suc. (suc. zero.)) (IsCatEquivalence (C .wild) (D .wild) F)
          (hlevel_raise (suc. zero.) (IsCatEquivalence (C .wild) (D .wild) F)
            (prop_to_hlevel_one (IsCatEquivalence (C .wild) (D .wild) F) (is_cat_equivalence_prop C (D .wild) F)))))

{` cor:cat-2-type: the type of categories is 2-truncated (HLevel 4 in the
   repository's numbering, HLevel n = book level n-2). `}
def category_type_two_truncated : HLevel (suc. (suc. (suc. (suc. zero.))))  Category
  ≔ C D ↦ hlevel_equiv (suc. (suc. (suc. zero.))) (CatEquivalence (C .wild) (D .wild)) (Id Category C D)
      (canonical_inverse_equiv (Id Category C D) (CatEquivalence (C .wild) (D .wild)) (category_path_composite_equiv C D))
      (groupoid_to_hlevel (CatEquivalence (C .wild) (D .wild)) (cat_equivalence_groupoid C D))

def category_paths_groupoid (C D : Category) : isGroupoid (Id Category C D)
  ≔ hlevel_to_groupoid (Id Category C D) (category_type_two_truncated C D)

{` Litmus: the equivalence sends refl to an equivalence whose functor is
   (identified with) the identity functor. `}
def category_path_equiv_refl (C : Category)
  : Id (CatEquivalence (C .wild) (C .wild)) (cat_equivalence_identity (C .wild))
      (category_path_equiv C C .map (refl C))
  ≔ Jβ Category C (D _ ↦ CatEquivalence (C .wild) (D .wild)) (cat_equivalence_identity (C .wild))

{` The category of sets has a nontrivial self-identification: negation
   on Bool is not the identity, and paths SetCat = SetCat include the
   identity; we check that the type of self-identifications is a
   groupoid (instance of cor:cat-2-type). `}
def set_cat_self_paths_groupoid : isGroupoid (Id Category SetCat SetCat)
  ≔ category_paths_groupoid SetCat SetCat
