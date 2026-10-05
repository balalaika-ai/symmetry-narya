export "603-adjunctions-and-equivalences"
export "202-higher-truncations"

{` Chapter 6 (cats.tex), def:n-trunc-functor and ex:trunc-adj: the
   n-truncation ‖-‖_n of def:join-construction-of-truncation (Trunc k with
   k = n + 1, n ≥ -1, module 202) as a wild functor U → U^{≤n}, and the
   adjunction ‖-‖_n ⊣ ι_n with the inclusion ι_n : U^{≤n} → U. `}

{` U^{≤n}: the full subcategory (def:full-subcat) of the wild category of
   types on the n-types (HLevel (k+1), n = k - 1). `}
def TruncatedPredicate (k : Nat) : Subtypes Type ≔ A ↦ (HLevel (suc. k) A, hlevel_isprop (suc. k) A)

def TruncatedTypeWild (k : Nat) : WildPrecat ≔ FullSubcat TypeWild (TruncatedPredicate k)

{` The action on arrows "given by the universal property": the unique
   extension of |-| ∘ f along |-|. `}
def trunc_functor_mor (k : Nat) (A B : Type) (f : A → B) : Trunc k A → Trunc k B
  ≔ trunc_extend k A (truncation k A) (Trunc k B) (trunc_level k B) (a ↦ trunc_unit k B (f a))

def trunc_functor_mor_beta (k : Nat) (A B : Type) (f : A → B) (a : A)
  : Id (Trunc k B) (trunc_unit k B (f a)) (trunc_functor_mor k A B f (trunc_unit k A a))
  ≔ trunc_extend_beta k A (truncation k A) (Trunc k B) (trunc_level k B) (a ↦ trunc_unit k B (f a)) a

def trunc_functor_map_id (k : Nat) (A : Type)
  : Id (Trunc k A → Trunc k A) (trunc_functor_mor k A A (x ↦ x)) (x ↦ x)
  ≔ trunc_maps_equal k A (truncation k A) (Trunc k A) (trunc_level k A)
      (trunc_functor_mor k A A (x ↦ x)) (x ↦ x)
      (a ↦ inverse (Trunc k A) (trunc_unit k A a) (trunc_functor_mor k A A (x ↦ x) (trunc_unit k A a))
        (trunc_functor_mor_beta k A A (x ↦ x) a))

def trunc_functor_map_comp (k : Nat) (A B C : Type) (f : A → B) (g : B → C)
  : Id (Trunc k A → Trunc k C) (trunc_functor_mor k A C (x ↦ g (f x)))
      (x ↦ trunc_functor_mor k B C g (trunc_functor_mor k A B f x))
  ≔ let F ≔ trunc_functor_mor k A B f in
    let G ≔ trunc_functor_mor k B C g in
    let GF ≔ trunc_functor_mor k A C (x ↦ g (f x)) in
    trunc_maps_equal k A (truncation k A) (Trunc k C) (trunc_level k C) GF (x ↦ G (F x))
      (a ↦ concat (Trunc k C) (GF (trunc_unit k A a)) (trunc_unit k C (g (f a))) (G (F (trunc_unit k A a)))
        (inverse (Trunc k C) (trunc_unit k C (g (f a))) (GF (trunc_unit k A a))
          (trunc_functor_mor_beta k A C (x ↦ g (f x)) a))
        (concat (Trunc k C) (trunc_unit k C (g (f a))) (G (trunc_unit k B (f a))) (G (F (trunc_unit k A a)))
          (trunc_functor_mor_beta k B C g (f a))
          (refl G (trunc_functor_mor_beta k A B f a))))

{` def:n-trunc-functor: ‖-‖_n : U → U^{≤n} is a wild functor. `}
def TruncFunctor (k : Nat) : WildFunctor TypeWild (TruncatedTypeWild k)
  ≔ (obj ≔ A ↦ (Trunc k A, trunc_level k A),
     mor ≔ A B f ↦ trunc_functor_mor k A B f,
     map_id ≔ A ↦ trunc_functor_map_id k A,
     map_comp ≔ A B C f g ↦ trunc_functor_map_comp k A B C f g)

{` "For n = 0, this is a functor from U to Set_U": the same data with
   values in the category of sets (U^{≤0} has the same objects up to
   HLevel 2 ↔ isSet). `}
def TruncSetFunctor : WildFunctor TypeWild SetWild
  ≔ (obj ≔ A ↦ (Trunc (suc. zero.) A, hlevel_two_to_set (Trunc (suc. zero.) A) (trunc_level (suc. zero.) A)),
     mor ≔ A B f ↦ trunc_functor_mor (suc. zero.) A B f,
     map_id ≔ A ↦ trunc_functor_map_id (suc. zero.) A,
     map_comp ≔ A B C f g ↦ trunc_functor_map_comp (suc. zero.) A B C f g)

def trunc_set_functor_agrees (A B : Type) (f : A → B)
  : Id (Trunc (suc. zero.) A → Trunc (suc. zero.) B) (TruncSetFunctor .mor A B f)
      (TruncFunctor (suc. zero.) .mor A B f)
  ≔ refl (trunc_functor_mor (suc. zero.) A B f)

{` The inclusion ι_n : U^{≤n} → U. `}
def truncated_inclusion_functor (k : Nat) : WildFunctor (TruncatedTypeWild k) TypeWild
  ≔ (obj ≔ X ↦ X .fst,
     mor ≔ X Y f ↦ f,
     map_id ≔ X ↦ refl ((x ↦ x) : X .fst → X .fst),
     map_comp ≔ X Y Z f g ↦ refl ((x ↦ g (f x)) : X .fst → Z .fst))

{` ex:trunc-adj: ‖-‖_n ⊣ ι_n. The transposition is precomposition with the
   constructor |-|_n, an equivalence (‖X‖_n → Y) ≃ (X → Y) for X : U and
   Y : U^{≤n} by the universal property; naturality in X follows from the
   computation rule of the action on arrows, naturality in Y is
   judgmental. `}
def trunc_right_adjoint (k : Nat) : RightAdjointData TypeWild (TruncatedTypeWild k) (TruncFunctor k)
  ≔ (right ≔ truncated_inclusion_functor k,
     transpose ≔ A Y h ↦ x ↦ h (trunc_unit k A x),
     transpose_iso ≔ A Y ↦ type_equiv_to_is_iso (Trunc k A → Y .fst) (A → Y .fst)
       (h ↦ x ↦ h (trunc_unit k A x))
       (native_equivalence (Trunc k A → Y .fst) (A → Y .fst) (trunc_universal_property k A (Y .fst) (Y .snd)) .equiv),
     natural_left ≔ A A' f Y ↦
       funext (Trunc k A → Y .fst) (_ ↦ A' → Y .fst)
         (h ↦ x ↦ h (trunc_unit k A (f x)))
         (h ↦ x ↦ h (trunc_functor_mor k A' A f (trunc_unit k A' x)))
         (h ↦ funext A' (_ ↦ Y .fst) (x ↦ h (trunc_unit k A (f x)))
           (x ↦ h (trunc_functor_mor k A' A f (trunc_unit k A' x)))
           (x ↦ refl h (trunc_functor_mor_beta k A' A f x))),
     natural_right ≔ A Y Y' g ↦ refl ((h ↦ x ↦ g (h (trunc_unit k A x))) : (Trunc k A → Y .fst) → A → Y' .fst))

def TruncAdjunction (k : Nat) : WildAdjunction TypeWild (TruncatedTypeWild k)
  ≔ (left ≔ TruncFunctor k, right_adjoint ≔ trunc_right_adjoint k)

{` The displayed equivalence (‖X‖_n → Y) ≃ (X → Y), precomposition with
   |-|_n, for X : U and Y : U^{≤n}. `}
def trunc_adjunction_transpose_equiv (k : Nat) (X : Type) (Y : TruncatedTypeWild k .ob)
  : BookEquiv (Trunc k X → Y .fst) (X → Y .fst)
  ≔ book_equivalence (Trunc k X → Y .fst) (X → Y .fst)
      (adjunction_transpose_equiv TypeWild (TruncatedTypeWild k) (TruncFunctor k) (trunc_right_adjoint k) X Y)

def trunc_adjunction_transpose_map (k : Nat) (X : Type) (Y : TruncatedTypeWild k .ob)
  : Id ((Trunc k X → Y .fst) → X → Y .fst) (trunc_adjunction_transpose_equiv k X Y .map)
      (h ↦ x ↦ h (trunc_unit k X x))
  ≔ refl ((h ↦ x ↦ h (trunc_unit k X x)) : (Trunc k X → Y .fst) → X → Y .fst)

{` "The constructor |-|_n acts as the unit." `}
def trunc_adjunction_unit (k : Nat) (A : Type)
  : Id (A → Trunc k A) (adjunction_unit TypeWild (TruncatedTypeWild k) (TruncFunctor k) (trunc_right_adjoint k) A)
      (trunc_unit k A)
  ≔ refl (trunc_unit k A)

{` Litmus checks: at n = -1 the functor is propositional truncation (Mere),
   and its action on the unit map 1 → Bool sends |*| to |true| up to the
   computation rule. `}
def trunc_functor_minus_one_objects (A : Type) : Id Type (TruncFunctor zero. .obj A .fst) (Mere A)
  ≔ refl (Mere A)

def trunc_functor_minus_one_value
  : Id (Mere Bool) (trunc_unit zero. Bool true.)
      (TruncFunctor zero. .mor Unit Bool (_ ↦ true.) (trunc_unit zero. Unit star.))
  ≔ trunc_functor_mor_beta zero. Unit Bool (_ ↦ true.) star.
