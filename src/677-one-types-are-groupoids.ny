export "675-flagged-category-equivalence"
export "626-path-functor-categories"
export "284-chapter-two-completions"

{` Chapter 6, section 6.8 (cats.tex, thm:1types-are-groupoids, the
   consequences). For a 1-type A its path groupoid is a category
   (path_groupoid_of_groupoid, ex:path-groupoid). `}

def path_category (A : Type) (hA : isGroupoid A) : Category
  ≔ groupoid_cat_category (path_groupoid_of_groupoid A hA)

{` "The functor groupoid [A, B]": the functor category from the path
   groupoid of A to the path category of B (FunctorCategory, module 621)
   is a groupoid, since natural transformations into a groupoid have
   invertible components (xca:funext-nat-trans, module 620). Its objects
   are the functors of path groupoids, so the first sentence of the
   theorem reads as follows. `}
def path_functor_category (A B : Type) (hB : isGroupoid B) : Category
  ≔ FunctorCategory (PathWild A) (path_category B hB)

def path_functor_category_invertible (A B : Type) (hB : isGroupoid B)
  : IsPregroupoid (path_functor_category A B hB .wild)
  ≔ F G alpha ↦ functor_cat_components_iso (PathWild A) (category_precat (path_category B hB)) F G alpha
      (a ↦ path_wild_invertible B (F .obj a) (G .obj a) (alpha .component a))

def path_functor_groupoid (A B : Type) (hB : isGroupoid B) : GroupoidCat
  ≔ (path_functor_category A B hB .wild, path_functor_category A B hB .homset,
     path_functor_category A B hB .univalent, path_functor_category_invertible A B hB)

def one_types_functor_groupoid_projection (A B : Type) (hA : isGroupoid A) (hB : isGroupoid B)
  : BookIsEquiv (path_functor_groupoid A B hB .wild .ob) (A → B) (F ↦ F .obj)
  ≔ one_types_functor_projection_equiv A B hA hB

{` A functor between path groupoids whose object part is an equivalence is
   fully faithful: it acts on paths by ap (path_functor_mor_ap), and ap of
   an equivalence is an equivalence. `}
def path_functor_equivalence_ff (A B : Type) (F : WildFunctor (PathWild A) (PathWild B)) (e : isEquiv A B (F .obj))
  : IsFullyFaithful (PathWild A) (PathWild B) F
  ≔ fully_faithful_from_equivs (PathWild A) (PathWild B) F
      (x y ↦ book_equivalence (Id A x y) (Id B (F .obj x) (F .obj y))
        (equiv_change_map (Id A x y) (Id B (F .obj x) (F .obj y)) (equivalence_on_paths A B (F .obj, e) x y)
          (F .mor x y) (path_functor_mor_ap A B F x y)) .equiv)

{` A functor of path groupoids of 1-types is an equivalence of categories
   iff its object part is an equivalence of types. `}
def path_functor_cat_equivalence_to_equiv (A B : Type) (hA : isGroupoid A) (hB : isGroupoid B)
  (F : WildFunctor (PathWild A) (PathWild B)) (E : IsCatEquivalence (PathWild A) (PathWild B) F)
  : isEquiv A B (F .obj)
  ≔ native_equivalence A B (F .obj, cat_equivalence_obj_is_equiv (path_category A hA) (path_category B hB) F E) .equiv

def path_functor_equiv_to_cat_equivalence (A B : Type) (hA : isGroupoid A)
  (F : WildFunctor (PathWild A) (PathWild B)) (e : isEquiv A B (F .obj))
  : IsCatEquivalence (PathWild A) (PathWild B) F
  ≔ wild_ff_eso_is_cat_equivalence (path_category A hA) (PathWild B) F (path_functor_equivalence_ff A B F e)
      (obj_equiv_eso (PathWild A) (PathWild B) F (book_equivalence A B (F .obj, e) .equiv))

{` "As a first consequence, the projection from the type of equivalences
   of groupoids, A ≃ B, to the type of equivalences of types, A ≃ B, is
   an equivalence." The projection sends (F, E) to F₀ with the proof
   that F₀ is an equivalence. `}
def path_equivalence_projection (A B : Type) (hA : isGroupoid A) (hB : isGroupoid B)
  (E : CatEquivalence (PathWild A) (PathWild B)) : Equiv A B
  ≔ (E .fst .obj, path_functor_cat_equivalence_to_equiv A B hA hB (E .fst) (E .snd))

def path_equivalence_section (A B : Type) (hA : isGroupoid A) (e : Equiv A B) : CatEquivalence (PathWild A) (PathWild B)
  ≔ (path_wild_functor A B (e .map), path_functor_equiv_to_cat_equivalence A B hA (path_wild_functor A B (e .map)) (e .equiv))

def path_groupoid_equivalences_equiv (A B : Type) (hA : isGroupoid A) (hB : isGroupoid B)
  : Equiv (CatEquivalence (PathWild A) (PathWild B)) (Equiv A B)
  ≔ quasi_inverse_equiv (CatEquivalence (PathWild A) (PathWild B)) (Equiv A B)
      (path_equivalence_projection A B hA hB) (path_equivalence_section A B hA)
      (E ↦ cat_equivalence_path (path_category A hA) (PathWild B)
        (path_equivalence_section A B hA (path_equivalence_projection A B hA hB E)) E
        (path_functor_eta A B hB (E .fst)))
      (e ↦ equiv_homotopy A B (path_equivalence_projection A B hA hB (path_equivalence_section A B hA e)) e
        (a ↦ refl (e .map a)))

def path_groupoid_equivalences_projection_is_equiv (A B : Type) (hA : isGroupoid A) (hB : isGroupoid B)
  : BookIsEquiv (CatEquivalence (PathWild A) (PathWild B)) (Equiv A B) (path_equivalence_projection A B hA hB)
  ≔ book_equivalence (CatEquivalence (PathWild A) (PathWild B)) (Equiv A B)
      (path_groupoid_equivalences_equiv A B hA hB) .equiv

{` Gpd: the subtype of groupoids in Cat. It is equivalent to the record
   GroupoidCat of module 600. `}
def Gpd : Type ≔ Σ Category (C ↦ IsPregroupoid (C .wild))

def gpd_groupoid_cat_equiv : Equiv Gpd GroupoidCat
  ≔ quasi_inverse_equiv Gpd GroupoidCat
      (G ↦ (G .fst .wild, G .fst .homset, G .fst .univalent, G .snd))
      (G ↦ ((G .wild, G .homset, G .univalent), G .invertible))
      (G ↦ refl G) (G ↦ refl G)

{` The path groupoid construction U^{≤1} → Gpd (GroupoidTypes = Σ Type
   isGroupoid, module 284). `}
def path_gpd (X : GroupoidTypes) : Gpd
  ≔ (path_category (X .fst) (X .snd), path_wild_invertible (X .fst))

def gpd_objects (G : Gpd) : GroupoidTypes ≔ (G .fst .wild .ob, category_objects_groupoid (G .fst))

def gpd_objects_path_gpd (X : GroupoidTypes) : Id GroupoidTypes (gpd_objects (path_gpd X)) X
  ≔ (refl (X .fst), isgroupoid_isprop (X .fst) (category_objects_groupoid (path_category (X .fst) (X .snd))) (X .snd))

{` Surjectivity part of the proof: every groupoid G is identified with the
   path groupoid of its objects. The comparison functor is the identity on
   objects and p ↦ idtoiso(p) on arrows (B's path_functor_from_objects);
   its functor laws express that identities and composition of G are
   forced by univalence and the unit law (cat_idtoiso_refl_arrow,
   cat_idtoiso_concat). It is an isomorphism of precategories since
   idtoiso is an equivalence and, in a groupoid, forgetting invertibility
   is an equivalence CatIso ≃ hom. `}
def gpd_comparison_functor (G : Gpd) : WildFunctor (PathWild (G .fst .wild .ob)) (G .fst .wild)
  ≔ path_functor_from_objects (G .fst .wild .ob) (G .fst .wild) (x ↦ x)

def gpd_iso_forget_equiv (G : Gpd) (x y : G .fst .wild .ob)
  : Equiv (CatIso (G .fst .wild) x y) (G .fst .wild .hom x y)
  ≔ contractible_fiber_projection (G .fst .wild .hom x y) (CatIsIso (G .fst .wild) x y)
      (f ↦ cat_is_iso_contractible (G .fst .wild) x y f (G .snd x y f))

def gpd_comparison_mor_equiv (G : Gpd) (x y : G .fst .wild .ob)
  : Equiv (Id (G .fst .wild .ob) x y) (G .fst .wild .hom x y)
  ≔ compose_equiv (Id (G .fst .wild .ob) x y) (CatIso (G .fst .wild) x y) (G .fst .wild .hom x y)
      (cat_idtoiso_equiv (G .fst .wild) (G .fst .univalent) x y) (gpd_iso_forget_equiv G x y)

def gpd_comparison_isomorphism (G : Gpd)
  : PrecatIsomorphism (category_precat (path_gpd (gpd_objects G) .fst)) (category_precat (G .fst))
  ≔ (gpd_comparison_functor G,
     (fully_faithful_from_equivs (PathWild (G .fst .wild .ob)) (G .fst .wild) (gpd_comparison_functor G)
        (x y ↦ book_equivalence (Id (G .fst .wild .ob) x y) (G .fst .wild .hom x y)
          (equiv_change_map (Id (G .fst .wild .ob) x y) (G .fst .wild .hom x y) (gpd_comparison_mor_equiv G x y)
            (gpd_comparison_functor G .mor x y) (p ↦ refl (cat_idtoiso (G .fst .wild) x y p .fst))) .equiv),
      book_equivalence (G .fst .wild .ob) (G .fst .wild .ob) (identity_equiv (G .fst .wild .ob)) .equiv))

{` (Stated for variable categories, see module 674.) `}
def category_path_from_precat_path (X Y : Category) (p : Id Precat (category_precat X) (category_precat Y))
  : Id Category X Y
  ≔ equiv_inverse_map (Id Category X Y) (Id Precat (category_precat X) (category_precat Y))
      (category_path_precat_equiv X Y) p

def gpd_path_from_category_path (G H : Gpd) (p : Id Category (G .fst) (H .fst)) : Id Gpd G H
  ≔ equiv_inverse_map (Id Gpd G H) (Id Category (G .fst) (H .fst))
      (subtype_path_equiv Category (C ↦ IsPregroupoid (C .wild)) (C ↦ is_pregroupoid_prop (C .wild)) G H) p

def path_gpd_gpd_objects (G : Gpd) : Id Gpd (path_gpd (gpd_objects G)) G
  ≔ gpd_path_from_category_path (path_gpd (gpd_objects G)) G
      (category_path_from_precat_path (path_gpd (gpd_objects G) .fst) (G .fst)
        (precat_path_from_isomorphism (category_precat (path_gpd (gpd_objects G) .fst)) (category_precat (G .fst))
          (gpd_comparison_isomorphism G)))

{` thm:1types-are-groupoids, second sentence: the path groupoid
   construction is an equivalence U^{≤1} → Gpd. (The book argues
   "injective and surjective" via lem:inj+surj; we give the inverse
   G ↦ Ob(G) directly; injectivity and surjectivity follow.) `}
def one_types_groupoids_equiv : Equiv GroupoidTypes Gpd
  ≔ quasi_inverse_equiv GroupoidTypes Gpd path_gpd gpd_objects gpd_objects_path_gpd path_gpd_gpd_objects

def one_types_groupoids_is_equiv : BookIsEquiv GroupoidTypes Gpd path_gpd
  ≔ book_equivalence GroupoidTypes Gpd one_types_groupoids_equiv .equiv

def path_gpd_injective : IsEmbedding GroupoidTypes Gpd path_gpd
  ≔ G ↦ contractible_prop (BookFiber GroupoidTypes Gpd path_gpd G)
      (native_contraction (BookFiber GroupoidTypes Gpd path_gpd G) (one_types_groupoids_is_equiv G))

def path_gpd_surjective : Surjective GroupoidTypes Gpd path_gpd
  ≔ G ↦ mere (BookFiber GroupoidTypes Gpd path_gpd G) (one_types_groupoids_is_equiv G .center)

{` Litmus: the objects of the path groupoid of a 1-type X are X, and the
   comparison functor of a groupoid is the identity on objects. `}
def path_gpd_objects (X : GroupoidTypes) : Id Type (path_gpd X .fst .wild .ob) (X .fst) ≔ refl (X .fst)

def gpd_comparison_obj (G : Gpd) (x : G .fst .wild .ob)
  : Id (G .fst .wild .ob) (gpd_comparison_functor G .obj x) x ≔ refl x
