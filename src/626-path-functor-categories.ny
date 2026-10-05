export "621-functor-categories"

{` Chapter 6 (cats.tex), xca:path-core-adj: for a type A and a category
   C, restriction to objects [A, C] → (A → Ob C) is an equivalence, where
   [A, C] is the functor category from the wild path category of A. The
   inverse sends f : A → Ob C to the functor acting on paths by
   p ↦ idtoiso(ap f p). Only the hom-sets of C are used (univalence of C is
   not needed), so we prove it for precategories and specialize. `}

{` idtoiso turns concatenation into composition. `}
def cat_idtoiso_concat (C : WildPrecat) (a b c : C .ob) (p : Id (C .ob) a b) (q : Id (C .ob) b c)
  : Id (C .hom a c) (cat_idtoiso C a c (concat (C .ob) a b c p q) .fst)
      (C .comp a b c (cat_idtoiso C b c q .fst) (cat_idtoiso C a b p .fst))
  ≔ J (C .ob) b (c q ↦ Id (C .hom a c) (cat_idtoiso C a c (concat (C .ob) a b c p q) .fst)
        (C .comp a b c (cat_idtoiso C b c q .fst) (cat_idtoiso C a b p .fst)))
      (calc
        cat_idtoiso C a b (concat (C .ob) a b b p (refl b)) .fst
        = cat_idtoiso C a b p .fst
          by refl ((r ↦ cat_idtoiso C a b r .fst) : Id (C .ob) a b → C .hom a b) (concat_p1 (C .ob) a b p)
        = C .comp a b b (C .idn b) (cat_idtoiso C a b p .fst)
          by inverse (C .hom a b) (C .comp a b b (C .idn b) (cat_idtoiso C a b p .fst)) (cat_idtoiso C a b p .fst)
               (C .lu a b (cat_idtoiso C a b p .fst))
        = C .comp a b b (cat_idtoiso C b b (refl b) .fst) (cat_idtoiso C a b p .fst)
          by cat_whisker_right C a b b (C .idn b) (cat_idtoiso C b b (refl b) .fst) (cat_idtoiso C a b p .fst)
               (refl ((e ↦ e .fst) : CatIso C b b → C .hom b b) (cat_idtoiso_refl C b)) ∎)
      c q

def cat_idtoiso_refl_arrow (C : WildPrecat) (a : C .ob)
  : Id (C .hom a a) (cat_idtoiso C a a (refl a) .fst) (C .idn a)
  ≔ inverse (C .hom a a) (C .idn a) (cat_idtoiso C a a (refl a) .fst)
      (refl ((e ↦ e .fst) : CatIso C a a → C .hom a a) (cat_idtoiso_refl C a))

{` The functor PathWild A → C determined by f : A → Ob C. `}
def path_functor_from_objects (A : Type) (C : WildPrecat) (f : A → C .ob) : WildFunctor (PathWild A) C
  ≔ (obj ≔ f,
     mor ≔ x y p ↦ cat_idtoiso C (f x) (f y) (map_path A (C .ob) f x y p) .fst,
     map_id ≔ x ↦ cat_idtoiso_refl_arrow C (f x),
     map_comp ≔ x y z p q ↦
       concat (C .hom (f x) (f z))
         (cat_idtoiso C (f x) (f z) (map_path A (C .ob) f x z (concat A x y z p q)) .fst)
         (cat_idtoiso C (f x) (f z)
           (concat (C .ob) (f x) (f y) (f z) (map_path A (C .ob) f x y p) (map_path A (C .ob) f y z q)) .fst)
         (C .comp (f x) (f y) (f z) (cat_idtoiso C (f y) (f z) (map_path A (C .ob) f y z q) .fst)
           (cat_idtoiso C (f x) (f y) (map_path A (C .ob) f x y p) .fst))
         (refl ((r ↦ cat_idtoiso C (f x) (f z) r .fst) : Id (C .ob) (f x) (f z) → C .hom (f x) (f z))
           (map_path_concat A (C .ob) f x y z p q))
         (cat_idtoiso_concat C (f x) (f y) (f z) (map_path A (C .ob) f x y p) (map_path A (C .ob) f y z q)))

{` Every functor out of a path category acts on paths by idtoiso. `}
def path_functor_mor (A : Type) (C : WildPrecat) (F : WildFunctor (PathWild A) C) (x y : A) (p : Id A x y)
  : Id (C .hom (F .obj x) (F .obj y))
      (cat_idtoiso C (F .obj x) (F .obj y) (map_path A (C .ob) (F .obj) x y p) .fst) (F .mor x y p)
  ≔ J A x (y p ↦ Id (C .hom (F .obj x) (F .obj y))
        (cat_idtoiso C (F .obj x) (F .obj y) (map_path A (C .ob) (F .obj) x y p) .fst) (F .mor x y p))
      (concat (C .hom (F .obj x) (F .obj x)) (cat_idtoiso C (F .obj x) (F .obj x) (refl (F .obj x)) .fst)
        (C .idn (F .obj x)) (F .mor x x (refl x))
        (cat_idtoiso_refl_arrow C (F .obj x))
        (inverse (C .hom (F .obj x) (F .obj x)) (F .mor x x (refl x)) (C .idn (F .obj x)) (F .map_id x)))
      y p

def path_functor_restriction_section (A : Type) (C : Precat) (F : WildFunctor (PathWild A) (C .wild))
  : Id (WildFunctor (PathWild A) (C .wild)) (path_functor_from_objects A (C .wild) (F .obj)) F
  ≔ functor_path (PathWild A) (C .wild) (C .homset) (path_functor_from_objects A (C .wild) (F .obj)) F
      (refl (F .obj),
       funext3 A (_ ↦ A) (x y ↦ Id A x y) (x y _ ↦ C .wild .hom (F .obj x) (F .obj y))
         (path_functor_from_objects A (C .wild) (F .obj) .mor) (F .mor)
         (path_functor_mor A (C .wild) F))

{` xca:path-core-adj for a precategory C. `}
def path_functor_restriction_equiv_precat (A : Type) (C : Precat)
  : BookEquiv (WildFunctor (PathWild A) (C .wild)) (A → C .wild .ob)
  ≔ book_quasi_inverse_equiv (WildFunctor (PathWild A) (C .wild)) (A → C .wild .ob) (F ↦ F .obj)
      (path_functor_from_objects A (C .wild))
      (path_functor_restriction_section A C)
      (f ↦ refl f)

{` xca:path-core-adj: restriction to objects
   [A, C] → (A → Ob(C)) is an equivalence. `}
def path_functor_restriction_is_equiv (A : Type) (C : Category)
  : BookIsEquiv (FunctorCategory (PathWild A) C .wild .ob) (A → C .wild .ob) (F ↦ F .obj)
  ≔ path_functor_restriction_equiv_precat A (category_precat C) .equiv

def path_functor_restriction_equiv (A : Type) (C : Category)
  : BookEquiv (FunctorCategory (PathWild A) C .wild .ob) (A → C .wild .ob)
  ≔ (F ↦ F .obj, path_functor_restriction_is_equiv A C)

{` Litmus: the inverse sends f to a functor with object part f, and the
   restriction of a constant functor is the constant family. `}
def path_functor_from_objects_obj (A : Type) (C : Category) (f : A → C .wild .ob)
  : Id (A → C .wild .ob) (path_functor_restriction_equiv A C .map (path_functor_from_objects A (C .wild) f)) f
  ≔ refl f

def path_restriction_constant_bool
  : Id (Bool → SetCat .wild .ob)
      (path_functor_restriction_equiv Bool SetCat .map (constant_functor (PathWild Bool) SetWild set_cat_bool))
      (_ ↦ set_cat_bool)
  ≔ refl ((_ ↦ set_cat_bool) : Bool → SetCat .wild .ob)
