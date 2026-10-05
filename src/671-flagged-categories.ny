export "670-path-groupoid-functors"

{` Chapter 6, section 6.8 (cats.tex, def:flagged-cat and the construction
   in the proof of thm:flagged-cat-equiv). `}

{` def:flagged-cat. A flagged category (C, A, f): a category C, a type A
   and a surjection f : A → Ob(C) (Surjective: every fibre is merely
   inhabited, with the book's fibre orientation b = f(a)). `}
def FlCat : Type
  ≔ Σ Category (C ↦ Σ Type (A ↦ Σ (A → C .wild .ob) (f ↦ Surjective A (C .wild .ob) f)))

{` The flag structures on a fixed category C, i.e. the fibre of the
   first projection FlCat → Cat at C (footnote to thm:flagged-cat-equiv). `}
def FlagStructure (C : Category) : Type
  ≔ Σ Type (A ↦ Σ (A → C .wild .ob) (f ↦ Surjective A (C .wild .ob) f))

def flagged_cat_sigma_check : Id Type FlCat (Σ Category FlagStructure) ≔ refl FlCat

{` Every category is flagged by its own type of objects. `}
def identity_surjective (A : Type) : Surjective A A (x ↦ x)
  ≔ a ↦ mere (BookFiber A A (x ↦ x) a) (a, refl a)

def category_identity_flag (C : Category) : FlCat
  ≔ (C, (C .wild .ob, ((x ↦ x), identity_surjective (C .wild .ob))))

{` The proof of thm:flagged-cat-equiv: "pulls back" a (pre)category
   structure along f : A → Ob(D), with hom(x, y) ≔ hom_D(f x, f y) and
   identities, composition and the laws taken from D at f. `}
def PulledBackWild (D : WildPrecat) (A : Type) (f : A → D .ob) : WildPrecat
  ≔ (ob ≔ A,
     hom ≔ x y ↦ D .hom (f x) (f y),
     idn ≔ x ↦ D .idn (f x),
     comp ≔ x y z ↦ D .comp (f x) (f y) (f z),
     lu ≔ x y ↦ D .lu (f x) (f y),
     ru ≔ x y ↦ D .ru (f x) (f y),
     assoc ≔ x y z w ↦ D .assoc (f x) (f y) (f z) (f w))

def pulled_back_homset (D : WildPrecat) (hs : HasHomSets D) (A : Type) (f : A → D .ob)
  : HasHomSets (PulledBackWild D A f)
  ≔ x y ↦ hs (f x) (f y)

def pulled_back_precat (D : Precat) (A : Type) (f : A → D .wild .ob) : Precat
  ≔ (PulledBackWild (D .wild) A f, pulled_back_homset (D .wild) (D .homset) A f)

{` "By construction, this extends f to a fully faithful functor f : A → C". `}
def pulled_back_functor (D : WildPrecat) (A : Type) (f : A → D .ob)
  : WildFunctor (PulledBackWild D A f) D
  ≔ (obj ≔ f,
     mor ≔ x y g ↦ g,
     map_id ≔ x ↦ refl (D .idn (f x)),
     map_comp ≔ x y z g h ↦ refl (D .comp (f x) (f y) (f z) h g))

def pulled_back_functor_ff (D : WildPrecat) (A : Type) (f : A → D .ob)
  : IsFullyFaithful (PulledBackWild D A f) D (pulled_back_functor D A f)
  ≔ fully_faithful_from_equivs (PulledBackWild D A f) D (pulled_back_functor D A f)
      (x y ↦ book_equivalence (D .hom (f x) (f y)) (D .hom (f x) (f y)) (identity_equiv (D .hom (f x) (f y))) .equiv)

{` "This is also essentially surjective by the surjectivity of f". `}
def surjective_to_eso_fiber (D : WildPrecat) (A : Type) (f : A → D .ob) (d : D .ob)
  (t : BookFiber A (D .ob) f d) : Σ A (a ↦ CatIso D (f a) d)
  ≔ (t .fst, cat_idtoiso D (f (t .fst)) d (inverse (D .ob) d (f (t .fst)) (t .snd)))

{` A functor that is surjective on objects (book fibres, merely) is
   essentially surjective. `}
def surjective_obj_eso (C D : WildPrecat) (F : WildFunctor C D) (s : Surjective (C .ob) (D .ob) (F .obj))
  : IsEso C D F
  ≔ d ↦ mere_rec (BookFiber (C .ob) (D .ob) (F .obj) d) (Mere (Σ (C .ob) (a ↦ CatIso D (F .obj a) d)))
      (mere_isprop (Σ (C .ob) (a ↦ CatIso D (F .obj a) d)))
      (t ↦ mere (Σ (C .ob) (a ↦ CatIso D (F .obj a) d)) (surjective_to_eso_fiber D (C .ob) (F .obj) d t)) (s d)

def pulled_back_functor_eso (D : WildPrecat) (A : Type) (f : A → D .ob) (s : Surjective A (D .ob) f)
  : IsEso (PulledBackWild D A f) D (pulled_back_functor D A f)
  ≔ surjective_obj_eso (PulledBackWild D A f) D (pulled_back_functor D A f) s

def pulled_back_weak_equivalence (D : WildPrecat) (A : Type) (f : A → D .ob) (s : Surjective A (D .ob) f)
  : IsWeakEquivalence (PulledBackWild D A f) D (pulled_back_functor D A f)
  ≔ (pulled_back_functor_ff D A f, pulled_back_functor_eso D A f s)

{` The precategory underlying a flagged category (the inverse map of
   thm:flagged-cat-equiv). `}
def flagged_to_precat (X : FlCat) : Precat
  ≔ pulled_back_precat (category_precat (X .fst)) (X .snd .fst) (X .snd .snd .fst)

def flagged_to_precat_objects (X : FlCat) : Id Type (flagged_to_precat X .wild .ob) (X .snd .fst)
  ≔ refl (X .snd .fst)

{` Litmus checks. Pulling back along the identity of the objects gives back
   the same wild precategory, definitionally (records have eta). `}
def pulled_back_identity (D : WildPrecat) : Id WildPrecat (PulledBackWild D (D .ob) (x ↦ x)) D ≔ refl D

{` Pulling back SetCat along Unit → Ob(Set), ★ ↦ Bool gives the monoid of
   endomaps of Bool, with composition computed in Set. `}
def bool_endo_precat : Precat ≔ pulled_back_precat (category_precat SetCat) Unit (_ ↦ set_cat_bool)

def bool_endo_composite
  : Id Bool (bool_endo_precat .wild .comp star. star. star. bool_not (x ↦ true.) false.) false.
  ≔ refl (false. : Bool)

def bool_endo_hom : Id Type (bool_endo_precat .wild .hom star. star.) (Bool → Bool) ≔ refl (Bool → Bool)
