export "674-rezk-universal-property"

{` Chapter 6, section 6.8 (cats.tex, thm:flagged-cat-equiv with its
   footnote). The theorem says "sending a category C"; it means a
   precategory C (the domain is PreCat). The map is
   F(C) ≔ (L(C), Ob(C), Ob(η)), together with the proof that Ob(η) is a
   surjection (rezk_unit_obj_surjective, needed for the triple to be a
   flagged category). The inverse pulls a category back along the flag
   (flagged_to_precat, module 671). `}

def rezk_flag (C : Precat) : FlCat
  ≔ (RezkCompletion C, (C .wild .ob, (rezk_unit C .obj, rezk_unit_obj_surjective C)))

{` Footnote: the triangle PreCat → FlCat → Cat (first projection) commutes
   definitionally with L. `}
def rezk_flag_triangle : Id (Precat → Category) (C ↦ rezk_flag C .fst) RezkCompletion
  ≔ refl RezkCompletion

{` First round trip: the precategory structure on Ob(C) pulled back from
   L(C) along Ob(η) is C itself; the isomorphism of precategories is the
   identity on objects and η (i.e. yo) on arrows, an equivalence on
   hom-sets since η is fully faithful. `}
def rezk_pullback_iso_functor (C : Precat)
  : WildFunctor (C .wild) (flagged_to_precat (rezk_flag C) .wild)
  ≔ (obj ≔ x ↦ x,
     mor ≔ yoneda_functor C .mor,
     map_id ≔ yoneda_functor C .map_id,
     map_comp ≔ yoneda_functor C .map_comp)

def rezk_pullback_isomorphism (C : Precat) : PrecatIsomorphism C (flagged_to_precat (rezk_flag C))
  ≔ (rezk_pullback_iso_functor C,
     (yoneda_fully_faithful C,
      book_equivalence (C .wild .ob) (C .wild .ob) (identity_equiv (C .wild .ob)) .equiv))

{` (Stated for variable precategories, as an instance of
   precategory_path_equiv of module 645.) `}
def precat_path_from_isomorphism (C D : Precat) (i : PrecatIsomorphism C D) : Id Precat C D
  ≔ precategory_path_equiv C D .equiv i .center .fst

def rezk_flag_round_trip_precat (C : Precat) : Id Precat (flagged_to_precat (rezk_flag C)) C
  ≔ inverse Precat C (flagged_to_precat (rezk_flag C))
      (precat_path_from_isomorphism C (flagged_to_precat (rezk_flag C)) (rezk_pullback_isomorphism C))

{` Identifications of flagged categories from an equivalence of the
   categories under which the flags correspond (by cor:Cat-ua). `}
def flag_subtype_path (X : Category) (A : Type) (g h : A → X .wild .ob)
  (s : Surjective A (X .wild .ob) g) (t : Surjective A (X .wild .ob) h) (r : Id (A → X .wild .ob) g h)
  : Id (Σ (A → X .wild .ob) (k ↦ Surjective A (X .wild .ob) k)) (g, s) (h, t)
  ≔ (r, pathover_of_eq (A → X .wild .ob) (k ↦ Surjective A (X .wild .ob) k) g h r s t
        (surjective_property_prop A (X .wild .ob) h
          (transport (A → X .wild .ob) (k ↦ Surjective A (X .wild .ob) k) g h r s) t))

def flag_path_same_category (X : Category) (A : Type) (g h : A → X .wild .ob)
  (s : Surjective A (X .wild .ob) g) (t : Surjective A (X .wild .ob) h)
  (H : (a : A) → Id (X .wild .ob) (g a) (h a))
  : Id FlCat (X, (A, (g, s))) (X, (A, (h, t)))
  ≔ refl ((v ↦ (X, (A, v))) : Σ (A → X .wild .ob) (k ↦ Surjective A (X .wild .ob) k) → FlCat)
      (flag_subtype_path X A g h s t (funext A (_ ↦ X .wild .ob) g h H))

def FlagEquivMotive (X : Category) (A : Type) (g : A → X .wild .ob) (s : Surjective A (X .wild .ob) g)
  (t : CatEquivTotal X) : Type
  ≔ (h : A → t .fst .wild .ob) (u : Surjective A (t .fst .wild .ob) h)
    (H : (a : A) → Id (t .fst .wild .ob) (t .snd .fst .obj (g a)) (h a))
    → Id FlCat (X, (A, (g, s))) (t .fst, (A, (h, u)))

def flagged_path_from_equivalence (X Y : Category) (e : CatEquivalence (X .wild) (Y .wild)) (A : Type)
  (g : A → X .wild .ob) (s : Surjective A (X .wild .ob) g)
  (h : A → Y .wild .ob) (u : Surjective A (Y .wild .ob) h)
  (H : (a : A) → Id (Y .wild .ob) (e .fst .obj (g a)) (h a))
  : Id FlCat (X, (A, (g, s))) (Y, (A, (h, u)))
  ≔ cat_equiv_induction X (FlagEquivMotive X A g s)
      (h u H ↦ flag_path_same_category X A g h s u H) (Y, e) h u H

{` Second round trip: for a flagged category (D, A, f), the pulled-back
   precategory f*D has a weak equivalence to D (module 671), hence D = L(f*D)
   compatibly with f and Ob(η) (module 674). `}
def flagged_round_trip (X : FlCat) : Id FlCat (rezk_flag (flagged_to_precat X)) X
  ≔ let D ≔ X .fst in
    let A ≔ X .snd .fst in
    let f ≔ X .snd .snd .fst in
    let s ≔ X .snd .snd .snd in
    let P ≔ flagged_to_precat X in
    let F ≔ pulled_back_functor (D .wild) A f in
    let w ≔ pulled_back_weak_equivalence (D .wild) A f s in
    inverse FlCat X (rezk_flag P)
      (flagged_path_from_equivalence D (RezkCompletion P) (restricted_yoneda_rezk_equivalence P D F w) A f s
        (rezk_unit P .obj) (rezk_unit_obj_surjective P) (restricted_yoneda_unit_path P D F w))

{` thm:flagged-cat-equiv: PreCat → FlCat is an equivalence. `}
def precat_flagged_equiv : Equiv Precat FlCat
  ≔ quasi_inverse_equiv Precat FlCat rezk_flag flagged_to_precat rezk_flag_round_trip_precat flagged_round_trip

def precat_flagged_is_equiv : BookIsEquiv Precat FlCat rezk_flag
  ≔ book_equivalence Precat FlCat precat_flagged_equiv .equiv

{` Footnote: the fiber of Rezk completion L : PreCat → Cat at a category D
   is the type Σ (A : U) Σ (f : A → Ob D), issurj(f) of flags on D. `}
def flagged_projection_fiber_equiv (D : Category)
  : Equiv (Σ FlCat (X ↦ Id Category D (X .fst))) (FlagStructure D)
  ≔ compose_equiv (Σ FlCat (X ↦ Id Category D (X .fst)))
      (Σ Category (Z ↦ Σ (Id Category D Z) (_ ↦ FlagStructure Z))) (FlagStructure D)
      (quasi_inverse_equiv (Σ FlCat (X ↦ Id Category D (X .fst)))
        (Σ Category (Z ↦ Σ (Id Category D Z) (_ ↦ FlagStructure Z)))
        (u ↦ (u .fst .fst, (u .snd, u .fst .snd))) (v ↦ ((v .fst, v .snd .snd), v .snd .fst))
        (u ↦ refl u) (v ↦ refl v))
      (contract_away_equiv Category D (Z _ ↦ FlagStructure Z))

def rezk_completion_fiber_equiv (D : Category)
  : Equiv (BookFiber Precat Category RezkCompletion D) (FlagStructure D)
  ≔ compose_equiv (BookFiber Precat Category RezkCompletion D) (Σ FlCat (X ↦ Id Category D (X .fst)))
      (FlagStructure D)
      (sigma_pullback_equiv Precat FlCat precat_flagged_equiv (X ↦ Id Category D (X .fst)))
      (flagged_projection_fiber_equiv D)

{` Litmus: the flag of a precategory consists of its own objects, and the
   inverse recovers the type of objects definitionally. `}
def rezk_flag_objects (C : Precat) : Id Type (rezk_flag C .snd .fst) (C .wild .ob) ≔ refl (C .wild .ob)

def flagged_round_trip_objects (C : Precat)
  : Id Type (flagged_to_precat (rezk_flag C) .wild .ob) (C .wild .ob) ≔ refl (C .wild .ob)
