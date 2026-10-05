export "671-flagged-categories"
export "210-truncation-smallness"

{` Chapter 6, section 6.8 (cats.tex, xca:Rezk-completion-1trunc, first
   part). For any type A, the path pregroupoid with
   hom(x, y) ≔ ‖x = y‖₀ (SetTrunc, the set truncation of module 43),
   identities |refl x|₀ and composition |q|₀ ∘ |p|₀ ≔ |p · q|₀ (the
   orientation of PathWild, ex:path-groupoid). On representatives the
   composite computes definitionally. Then the comparison with the
   1-truncation ‖A‖₁ = Trunc 2 A (module 202): the unit A → ‖A‖₁ extends to
   a weak equivalence onto the path groupoid of ‖A‖₁. `}

def trunc_path_comp (A : Type) (x y z : A) (g : SetTrunc (Id A y z)) (f : SetTrunc (Id A x y))
  : SetTrunc (Id A x z)
  ≔ set_trunc_rec (Id A x y) (SetTrunc (Id A x z)) (set_trunc_set (Id A x z))
      (p ↦ set_trunc_rec (Id A y z) (SetTrunc (Id A x z)) (set_trunc_set (Id A x z))
        (q ↦ set_trunc (Id A x z) (concat A x y z p q)) g) f

def trunc_path_lu (A : Type) (x y : A) (f : SetTrunc (Id A x y))
  : Id (SetTrunc (Id A x y)) (trunc_path_comp A x y y (set_trunc (Id A y y) (refl y)) f) f
  ≔ set_trunc_induction (Id A x y)
      (f ↦ Id (SetTrunc (Id A x y)) (trunc_path_comp A x y y (set_trunc (Id A y y) (refl y)) f) f)
      (f ↦ prop_is_set (Id (SetTrunc (Id A x y)) (trunc_path_comp A x y y (set_trunc (Id A y y) (refl y)) f) f)
        (set_trunc_set (Id A x y) (trunc_path_comp A x y y (set_trunc (Id A y y) (refl y)) f) f))
      (p ↦ refl (set_trunc (Id A x y)) (concat_p1 A x y p)) f

def trunc_path_ru (A : Type) (x y : A) (f : SetTrunc (Id A x y))
  : Id (SetTrunc (Id A x y)) (trunc_path_comp A x x y f (set_trunc (Id A x x) (refl x))) f
  ≔ set_trunc_induction (Id A x y)
      (f ↦ Id (SetTrunc (Id A x y)) (trunc_path_comp A x x y f (set_trunc (Id A x x) (refl x))) f)
      (f ↦ prop_is_set (Id (SetTrunc (Id A x y)) (trunc_path_comp A x x y f (set_trunc (Id A x x) (refl x))) f)
        (set_trunc_set (Id A x y) (trunc_path_comp A x x y f (set_trunc (Id A x x) (refl x))) f))
      (p ↦ refl (set_trunc (Id A x y)) (concat_1p A x y p)) f

def TruncPathAssocGoal (A : Type) (x y z w : A) (f : SetTrunc (Id A x y)) (g : SetTrunc (Id A y z))
  (h : SetTrunc (Id A z w)) : Type
  ≔ Id (SetTrunc (Id A x w)) (trunc_path_comp A x z w h (trunc_path_comp A x y z g f))
      (trunc_path_comp A x y w (trunc_path_comp A y z w h g) f)

def trunc_path_assoc_goal_set (A : Type) (x y z w : A) (f : SetTrunc (Id A x y)) (g : SetTrunc (Id A y z))
  (h : SetTrunc (Id A z w)) : isSet (TruncPathAssocGoal A x y z w f g h)
  ≔ prop_is_set (TruncPathAssocGoal A x y z w f g h)
      (set_trunc_set (Id A x w) (trunc_path_comp A x z w h (trunc_path_comp A x y z g f))
        (trunc_path_comp A x y w (trunc_path_comp A y z w h g) f))

def trunc_path_assoc (A : Type) (x y z w : A) (f : SetTrunc (Id A x y)) (g : SetTrunc (Id A y z))
  (h : SetTrunc (Id A z w)) : TruncPathAssocGoal A x y z w f g h
  ≔ set_trunc_induction (Id A x y) (f ↦ TruncPathAssocGoal A x y z w f g h)
      (f ↦ trunc_path_assoc_goal_set A x y z w f g h)
      (p ↦ set_trunc_induction (Id A y z) (g ↦ TruncPathAssocGoal A x y z w (set_trunc (Id A x y) p) g h)
        (g ↦ trunc_path_assoc_goal_set A x y z w (set_trunc (Id A x y) p) g h)
        (q ↦ set_trunc_induction (Id A z w)
          (h ↦ TruncPathAssocGoal A x y z w (set_trunc (Id A x y) p) (set_trunc (Id A y z) q) h)
          (h ↦ trunc_path_assoc_goal_set A x y z w (set_trunc (Id A x y) p) (set_trunc (Id A y z) q) h)
          (r ↦ refl (set_trunc (Id A x w)) (concat_assoc A x y z w p q r)) h) g) f

{` xca:Rezk-completion-1trunc: the path pregroupoid of A with
   hom(x, y) ≔ ‖x = y‖₀. `}
def TruncPathWild (A : Type) : WildPrecat
  ≔ (ob ≔ A,
     hom ≔ x y ↦ SetTrunc (Id A x y),
     idn ≔ x ↦ set_trunc (Id A x x) (refl x),
     comp ≔ x y z g f ↦ trunc_path_comp A x y z g f,
     lu ≔ x y f ↦ trunc_path_lu A x y f,
     ru ≔ x y f ↦ trunc_path_ru A x y f,
     assoc ≔ x y z w f g h ↦ trunc_path_assoc A x y z w f g h)

def trunc_path_homset (A : Type) : HasHomSets (TruncPathWild A) ≔ x y ↦ set_trunc_set (Id A x y)

def trunc_path_precat (A : Type) : Precat ≔ (TruncPathWild A, trunc_path_homset A)

{` Every arrow is invertible, with inverse |p⁻¹|₀. `}
def trunc_path_invertible (A : Type) : IsPregroupoid (TruncPathWild A)
  ≔ x y f ↦ set_trunc_induction (Id A x y) (f ↦ CatIsIso (TruncPathWild A) x y f)
      (f ↦ prop_is_set (CatIsIso (TruncPathWild A) x y f) (cat_is_iso_prop (TruncPathWild A) x y f))
      (p ↦ ((set_trunc (Id A y x) (inverse A x y p),
             refl (set_trunc (Id A y y)) (concat_inverse_left A x y p)),
            (set_trunc (Id A y x) (inverse A x y p),
             refl (set_trunc (Id A x x)) (concat_inverse_right A x y p)))) f

def trunc_path_pregroupoid (A : Type) : Pregroupoid
  ≔ (TruncPathWild A, trunc_path_homset A, trunc_path_invertible A)

{` Litmus: composition of representatives is concatenation, by refl. `}
def trunc_path_comp_compute (A : Type) (x y z : A) (p : Id A x y) (q : Id A y z)
  : Id (SetTrunc (Id A x z))
      (TruncPathWild A .comp x y z (set_trunc (Id A y z) q) (set_trunc (Id A x y) p))
      (set_trunc (Id A x z) (concat A x y z p q))
  ≔ refl (set_trunc (Id A x z) (concat A x y z p q))

{` The 1-truncation ‖A‖₁ = Trunc 2 A (HLevel index 3) and its path
   groupoid, a category. `}
def OneTrunc (A : Type) : Type ≔ Trunc (suc. (suc. zero.)) A

def one_trunc_unit (A : Type) : A → OneTrunc A ≔ trunc_unit (suc. (suc. zero.)) A

def one_trunc_groupoid (A : Type) : isGroupoid (OneTrunc A)
  ≔ hlevel_to_groupoid (OneTrunc A) (trunc_level (suc. (suc. zero.)) A)

def one_trunc_category (A : Type) : Category
  ≔ (PathWild (OneTrunc A), one_trunc_groupoid A, path_wild_univalent (OneTrunc A))

{` The comparison functor: |-|₁ on objects, ap |-|₁ on representatives. `}
def trunc_path_one_trunc_mor (A : Type) (x y : A) (f : SetTrunc (Id A x y))
  : Id (OneTrunc A) (one_trunc_unit A x) (one_trunc_unit A y)
  ≔ set_trunc_rec (Id A x y) (Id (OneTrunc A) (one_trunc_unit A x) (one_trunc_unit A y))
      (one_trunc_groupoid A (one_trunc_unit A x) (one_trunc_unit A y))
      (p ↦ refl (one_trunc_unit A) p) f

def TruncPathCompGoal (A : Type) (x y z : A) (f : SetTrunc (Id A x y)) (g : SetTrunc (Id A y z)) : Type
  ≔ let u ≔ one_trunc_unit A in
    Id (Id (OneTrunc A) (u x) (u z)) (trunc_path_one_trunc_mor A x z (trunc_path_comp A x y z g f))
      (concat (OneTrunc A) (u x) (u y) (u z) (trunc_path_one_trunc_mor A x y f) (trunc_path_one_trunc_mor A y z g))

def trunc_path_comp_goal_set (A : Type) (x y z : A) (f : SetTrunc (Id A x y)) (g : SetTrunc (Id A y z))
  : isSet (TruncPathCompGoal A x y z f g)
  ≔ let u ≔ one_trunc_unit A in
    prop_is_set (TruncPathCompGoal A x y z f g)
      (one_trunc_groupoid A (u x) (u z) (trunc_path_one_trunc_mor A x z (trunc_path_comp A x y z g f))
        (concat (OneTrunc A) (u x) (u y) (u z) (trunc_path_one_trunc_mor A x y f) (trunc_path_one_trunc_mor A y z g)))

def trunc_path_one_trunc_map_comp (A : Type) (x y z : A) (f : SetTrunc (Id A x y)) (g : SetTrunc (Id A y z))
  : TruncPathCompGoal A x y z f g
  ≔ set_trunc_induction (Id A x y) (f ↦ TruncPathCompGoal A x y z f g)
      (f ↦ trunc_path_comp_goal_set A x y z f g)
      (p ↦ set_trunc_induction (Id A y z) (g ↦ TruncPathCompGoal A x y z (set_trunc (Id A x y) p) g)
        (g ↦ trunc_path_comp_goal_set A x y z (set_trunc (Id A x y) p) g)
        (q ↦ map_path_concat A (OneTrunc A) (one_trunc_unit A) x y z p q) g) f

def trunc_path_one_trunc_functor (A : Type) : WildFunctor (TruncPathWild A) (PathWild (OneTrunc A))
  ≔ (obj ≔ one_trunc_unit A,
     mor ≔ trunc_path_one_trunc_mor A,
     map_id ≔ x ↦ refl (refl (one_trunc_unit A x)),
     map_comp ≔ x y z f g ↦ trunc_path_one_trunc_map_comp A x y z f g)

{` The action on arrows is an equivalence: it agrees with
   ‖x = y‖₀ ≃ ‖x = y‖ (Trunc 1) ≃ (|x|₁ = |y|₁) (eq:trunc-path-eq,
   trunc_path_equiv of module 202). `}
def one_trunc_gen_base (A : Type) (x : A)
  : Id (Id (OneTrunc A) (one_trunc_unit A x) (one_trunc_unit A x))
      (trunc_step_path_gen (suc. zero.) (truncation (suc. zero.)) A x x (refl x)) (refl (one_trunc_unit A x))
  ≔ transport_refl A (z ↦ Id (OneTrunc A) (one_trunc_unit A x) (one_trunc_unit A z)) x (refl (one_trunc_unit A x))

def one_trunc_gen_ap (A : Type) (x y : A) (r : Id A x y)
  : Id (Id (OneTrunc A) (one_trunc_unit A x) (one_trunc_unit A y))
      (trunc_step_path_gen (suc. zero.) (truncation (suc. zero.)) A x y r) (refl (one_trunc_unit A) r)
  ≔ J A x (y r ↦ Id (Id (OneTrunc A) (one_trunc_unit A x) (one_trunc_unit A y))
        (trunc_step_path_gen (suc. zero.) (truncation (suc. zero.)) A x y r) (refl (one_trunc_unit A) r))
      (one_trunc_gen_base A x) y r

def trunc_path_hom_equiv (A : Type) (x y : A)
  : Equiv (SetTrunc (Id A x y)) (Id (OneTrunc A) (one_trunc_unit A x) (one_trunc_unit A y))
  ≔ compose_equiv (SetTrunc (Id A x y)) (Trunc (suc. zero.) (Id A x y))
      (Id (OneTrunc A) (one_trunc_unit A x) (one_trunc_unit A y))
      (canonical_inverse_equiv (Trunc (suc. zero.) (Id A x y)) (SetTrunc (Id A x y))
        (trunc_one_set_trunc_equiv (Id A x y)))
      (trunc_path_equiv (suc. zero.) A x y)

def trunc_path_hom_equiv_rep (A : Type) (x y : A) (p : Id A x y)
  : Id (Id (OneTrunc A) (one_trunc_unit A x) (one_trunc_unit A y))
      (trunc_path_hom_equiv A x y .map (set_trunc (Id A x y) p)) (refl (one_trunc_unit A) p)
  ≔ let T1 ≔ Trunc (suc. zero.) (Id A x y) in
    let ST ≔ SetTrunc (Id A x y) in
    let e1 ≔ trunc_one_set_trunc_equiv (Id A x y) in
    let E ≔ trunc_path_equiv (suc. zero.) A x y in
    let P ≔ Id (OneTrunc A) (one_trunc_unit A x) (one_trunc_unit A y) in
    let v ≔ trunc_unit (suc. zero.) (Id A x y) p in
    let back : Id T1 (equiv_inverse_map T1 ST e1 (set_trunc (Id A x y) p)) v
      ≔ concat T1 (equiv_inverse_map T1 ST e1 (set_trunc (Id A x y) p)) (equiv_inverse_map T1 ST e1 (e1 .map v)) v
          (refl (equiv_inverse_map T1 ST e1)
            (inverse ST (e1 .map v) (set_trunc (Id A x y) p) (trunc_one_unit_compare (Id A x y) p)))
          (equiv_retraction T1 ST e1 v) in
    concat P (E .map (equiv_inverse_map T1 ST e1 (set_trunc (Id A x y) p))) (E .map v) (refl (one_trunc_unit A) p)
      (refl (E .map) back)
      (concat P (E .map v) (trunc_step_path_gen (suc. zero.) (truncation (suc. zero.)) A x y p)
        (refl (one_trunc_unit A) p)
        (inverse P (trunc_step_path_gen (suc. zero.) (truncation (suc. zero.)) A x y p) (E .map v)
          (trunc_path_equiv_unit (suc. zero.) A x y p))
        (one_trunc_gen_ap A x y p))

def trunc_path_hom_agree (A : Type) (x y : A) (f : SetTrunc (Id A x y))
  : Id (Id (OneTrunc A) (one_trunc_unit A x) (one_trunc_unit A y))
      (trunc_path_hom_equiv A x y .map f) (trunc_path_one_trunc_mor A x y f)
  ≔ let P ≔ Id (OneTrunc A) (one_trunc_unit A x) (one_trunc_unit A y) in
    set_trunc_induction (Id A x y) (f ↦ Id P (trunc_path_hom_equiv A x y .map f) (trunc_path_one_trunc_mor A x y f))
      (f ↦ prop_is_set (Id P (trunc_path_hom_equiv A x y .map f) (trunc_path_one_trunc_mor A x y f))
        (one_trunc_groupoid A (one_trunc_unit A x) (one_trunc_unit A y)
          (trunc_path_hom_equiv A x y .map f) (trunc_path_one_trunc_mor A x y f)))
      (p ↦ trunc_path_hom_equiv_rep A x y p) f

def trunc_path_one_trunc_mor_equiv (A : Type) (x y : A)
  : Equiv (SetTrunc (Id A x y)) (Id (OneTrunc A) (one_trunc_unit A x) (one_trunc_unit A y))
  ≔ equiv_change_map (SetTrunc (Id A x y)) (Id (OneTrunc A) (one_trunc_unit A x) (one_trunc_unit A y))
      (trunc_path_hom_equiv A x y) (trunc_path_one_trunc_mor A x y) (trunc_path_hom_agree A x y)

def trunc_path_one_trunc_ff (A : Type)
  : IsFullyFaithful (TruncPathWild A) (PathWild (OneTrunc A)) (trunc_path_one_trunc_functor A)
  ≔ fully_faithful_from_equivs (TruncPathWild A) (PathWild (OneTrunc A)) (trunc_path_one_trunc_functor A)
      (x y ↦ book_equivalence (SetTrunc (Id A x y)) (Id (OneTrunc A) (one_trunc_unit A x) (one_trunc_unit A y))
        (trunc_path_one_trunc_mor_equiv A x y) .equiv)

{` (Stated separately: elaborating trunc_unit_surjective inline against
   the functor's object map made the checker blow up.) `}
def one_trunc_unit_surjective (A : Type) : Surjective A (OneTrunc A) (one_trunc_unit A)
  ≔ trunc_unit_surjective (suc. (suc. zero.)) A

def trunc_path_one_trunc_eso (A : Type)
  : IsEso (TruncPathWild A) (PathWild (OneTrunc A)) (trunc_path_one_trunc_functor A)
  ≔ surjective_obj_eso (TruncPathWild A) (PathWild (OneTrunc A)) (trunc_path_one_trunc_functor A)
      (one_trunc_unit_surjective A)

{` The unit |-|₁ : A → ‖A‖₁ is a weak equivalence from the path
   pregroupoid of A to the path groupoid of ‖A‖₁. `}
def trunc_path_one_trunc_weak_equivalence (A : Type)
  : IsWeakEquivalence (TruncPathWild A) (PathWild (OneTrunc A)) (trunc_path_one_trunc_functor A)
  ≔ (trunc_path_one_trunc_ff A, trunc_path_one_trunc_eso A)
