export "672-truncated-path-pregroupoid"
export "674-rezk-universal-property"

{` Chapter 6, section 6.8 (cats.tex, xca:Rezk-completion-1trunc, second
   part): the Rezk completion of the path pregroupoid of A (hom(x, y) ≔
   ‖x = y‖₀, module 672) is the path groupoid of the 1-truncation ‖A‖₁.
   The unit |-|₁ is a weak equivalence onto the path groupoid of ‖A‖₁, a
   category, so module 674 identifies that category with L. `}

def trunc_path_rezk_equivalence (A : Type)
  : CatEquivalence (one_trunc_category A .wild) (RezkCompletion (trunc_path_precat A) .wild)
  ≔ restricted_yoneda_rezk_equivalence (trunc_path_precat A) (one_trunc_category A)
      (trunc_path_one_trunc_functor A) (trunc_path_one_trunc_weak_equivalence A)

def trunc_path_rezk_path (A : Type) : Id Category (one_trunc_category A) (RezkCompletion (trunc_path_precat A))
  ≔ rezk_weak_equivalence_path (trunc_path_precat A) (one_trunc_category A)
      (trunc_path_one_trunc_functor A) (trunc_path_one_trunc_weak_equivalence A)

{` On objects: ‖A‖₁ ≃ Ob(L), sending |a|₁ to η(a). `}
def trunc_path_rezk_objects_equiv (A : Type) : Equiv (OneTrunc A) (RezkCompletion (trunc_path_precat A) .wild .ob)
  ≔ native_equivalence (OneTrunc A) (RezkCompletion (trunc_path_precat A) .wild .ob)
      (trunc_path_rezk_equivalence A .fst .obj,
       cat_equivalence_obj_is_equiv (one_trunc_category A) (RezkCompletion (trunc_path_precat A))
         (trunc_path_rezk_equivalence A .fst) (trunc_path_rezk_equivalence A .snd))

def trunc_path_rezk_objects_unit (A : Type) (a : A)
  : Id (RezkCompletion (trunc_path_precat A) .wild .ob)
      (trunc_path_rezk_objects_equiv A .map (one_trunc_unit A a)) (rezk_unit (trunc_path_precat A) .obj a)
  ≔ restricted_yoneda_unit_path (trunc_path_precat A) (one_trunc_category A)
      (trunc_path_one_trunc_functor A) (trunc_path_one_trunc_weak_equivalence A) a

{` On arrows: hom_L(η x, η y) ≃ (|x|₁ = |y|₁) ≃ ‖x = y‖₀. `}
def trunc_path_rezk_hom_equiv (A : Type) (x y : A)
  : Equiv (SetTrunc (Id A x y))
      (RezkCompletion (trunc_path_precat A) .wild .hom (rezk_unit (trunc_path_precat A) .obj x)
        (rezk_unit (trunc_path_precat A) .obj y))
  ≔ native_equivalence (SetTrunc (Id A x y))
      (RezkCompletion (trunc_path_precat A) .wild .hom (rezk_unit (trunc_path_precat A) .obj x)
        (rezk_unit (trunc_path_precat A) .obj y))
      (yoneda_functor (trunc_path_precat A) .mor x y, yoneda_mor_equiv (trunc_path_precat A) x y)

{` Litmus: the object of L corresponding to |a|₁ is the presheaf
   x ↦ hom_{‖A‖₁}(|x|₁, |a|₁) = (|x|₁ = |a|₁). `}
def trunc_path_rezk_object_value (A : Type) (a x : A)
  : Id Type (trunc_path_rezk_equivalence A .fst .obj (one_trunc_unit A a) .fst .obj x .fst)
      (Id (OneTrunc A) (one_trunc_unit A x) (one_trunc_unit A a))
  ≔ refl (Id (OneTrunc A) (one_trunc_unit A x) (one_trunc_unit A a))
