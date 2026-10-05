export "623-representable-presheaves"
export "671-flagged-categories"

{` Chapter 6, section 6.8 (cats.tex, def:Rezk-completion and the first
   half of thm:Rezk-completion).

   "Note that Set is a category, and hence so is the functor category
   Set^{C^op}": SetCat (module 601) and PresheafCategory (module 621,
   xca:functor-cat-univalent); in Narya's single universe the book's Set
   (Set_U) is SetTypes, the sets of Type. "From cor:yo-ff we know that the
   Yoneda embedding yo : C → Set^{C^op} is fully faithful":
   yoneda_fully_faithful (module 622). `}

def presheaf_category_is_category (C : Precat) : IsUnivalentCat (PresheafCategory C .wild)
  ≔ PresheafCategory C .univalent

def set_cat_is_category : IsUnivalentCat (SetCat .wild) ≔ SetCat .univalent

{` def:Rezk-completion. isRepr(F) is the proposition that F is merely
   representable, ‖Σ (c : Ob C), yo(c) ≅ F‖: for a precategory the type
   IsRepresentable of def:repr need not be a proposition (cor:repr-prop
   needs a category), and the full subcategory of def:full-subcat needs a
   proposition-valued predicate. `}
def MerelyRepresentable (C : Precat) : Subtypes (PresheafCategory C .wild .ob)
  ≔ F ↦ (Mere (IsRepresentable C F), mere_isprop (IsRepresentable C F))

{` L(C) ≔ (Set^{C^op})_{isRepr}, a category by def:full-subcat. `}
def RezkCompletion (C : Precat) : Category
  ≔ full_subcat_category (PresheafCategory C) (MerelyRepresentable C)

{` η : C → L(C), the factorization of yo through the full subcategory
   via the trivial proofs that each yo(c) is representable. `}
def rezk_unit_object (C : Precat) (c : C .wild .ob) : RezkCompletion C .wild .ob
  ≔ (yoneda_functor C .obj c,
     mere (IsRepresentable C (yoneda_functor C .obj c)) (representable_presheaf_is_representable C c))

def rezk_unit (C : Precat) : WildFunctor (C .wild) (RezkCompletion C .wild)
  ≔ (obj ≔ rezk_unit_object C,
     mor ≔ yoneda_functor C .mor,
     map_id ≔ yoneda_functor C .map_id,
     map_comp ≔ yoneda_functor C .map_comp)

{` thm:Rezk-completion, first sentence. "η is fully faithful since yo is"
   (the hom-sets of the full subcategory are those of Set^{C^op}), "and it
   is essentially surjective by definition" (the proof that an object of
   L(C) is merely representable is literally the required mere iso). `}
def rezk_unit_ff (C : Precat) : IsFullyFaithful (C .wild) (RezkCompletion C .wild) (rezk_unit C)
  ≔ yoneda_fully_faithful C

def rezk_unit_eso (C : Precat) : IsEso (C .wild) (RezkCompletion C .wild) (rezk_unit C)
  ≔ d ↦ d .snd

def rezk_unit_weak_equivalence (C : Precat)
  : IsWeakEquivalence (C .wild) (RezkCompletion C .wild) (rezk_unit C)
  ≔ (rezk_unit_ff C, rezk_unit_eso C)

{` Into a univalent precategory, an essentially surjective functor is
   surjective on objects (isomorphisms give identifications). `}
def eso_iso_fiber_to_book_fiber (C D : WildPrecat) (uD : IsUnivalentCat D) (F : WildFunctor C D) (d : D .ob)
  (t : Σ (C .ob) (c ↦ CatIso D (F .obj c) d)) : BookFiber (C .ob) (D .ob) (F .obj) d
  ≔ (t .fst, inverse (D .ob) (F .obj (t .fst)) d (cat_isotoid D uD (F .obj (t .fst)) d (t .snd)))

def eso_univalent_obj_surjective (C D : WildPrecat) (uD : IsUnivalentCat D) (F : WildFunctor C D)
  (e : IsEso C D F) : Surjective (C .ob) (D .ob) (F .obj)
  ≔ d ↦ mere_rec (Σ (C .ob) (c ↦ CatIso D (F .obj c) d)) (Mere (BookFiber (C .ob) (D .ob) (F .obj) d))
      (mere_isprop (BookFiber (C .ob) (D .ob) (F .obj) d))
      (t ↦ mere (BookFiber (C .ob) (D .ob) (F .obj) d) (eso_iso_fiber_to_book_fiber C D uD F d t)) (e d)

{` Ob(η) : Ob(C) → Ob(L(C)) is a surjection (used for thm:flagged-cat-equiv). `}
def rezk_unit_obj_surjective (C : Precat)
  : Surjective (C .wild .ob) (RezkCompletion C .wild .ob) (rezk_unit C .obj)
  ≔ eso_univalent_obj_surjective (C .wild) (RezkCompletion C .wild) (RezkCompletion C .univalent)
      (rezk_unit C) (rezk_unit_eso C)

{` Litmus checks: η(c) is the representable presheaf hom(-, c) and η acts on
   arrows by postcomposition, definitionally. `}
def rezk_unit_object_value (C : Precat) (c x : C .wild .ob)
  : Id Type (rezk_unit C .obj c .fst .obj x .fst) (C .wild .hom x c)
  ≔ refl (C .wild .hom x c)

def rezk_unit_mor_value (C : Precat) (c c' x : C .wild .ob) (f : C .wild .hom c c') (k : C .wild .hom x c)
  : Id (C .wild .hom x c') (rezk_unit C .mor c c' f .component x k) (C .wild .comp x c c' f k)
  ≔ refl (C .wild .comp x c c' f k)

{` The presheaf constant at the empty set is not an object of L(C): it is
   not even merely representable. `}
def rezk_empty_presheaf_excluded (C : Precat) (r : Mere (IsRepresentable C (empty_presheaf C))) : Empty
  ≔ mere_rec (IsRepresentable C (empty_presheaf C)) Empty empty_prop (empty_presheaf_not_representable C) r
