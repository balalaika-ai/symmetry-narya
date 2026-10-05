export "610-preorder-functors-and-adjoints"

{` Chapter 6 (cats.tex), rem:adj-in-posets, last part: for f : A → B the
   string of adjunctions ∃_f ⊣ f^* ⊣ ∀_f between the posets (Sub(A), ⊆)
   and (Sub(B), ⊆) of module 605, with the operations of
   rem:^*-_!-as-(pre)image and rem:coinduced-subset:
   f^*(Y) = Y ∘ f, ∃_f(X)(b) = ∃_{a:A} ((f(a) = b) × X(a)),
   ∀_f(X)(b) = ∏_{a:A} (f(a) = b) → X(a). `}

def subtype_preimage (A B : Type) (f : A → B) (Y : Subtypes B) : Subtypes A ≔ a ↦ Y (f a)

def subtype_image_exists (A B : Type) (f : A → B) (X : Subtypes A) : Subtypes B
  ≔ b ↦ (Mere (Σ A (a ↦ Product (Id B (f a) b) (X a .fst))),
         mere_isprop (Σ A (a ↦ Product (Id B (f a) b) (X a .fst))))

def subtype_coinduced_forall (A B : Type) (f : A → B) (X : Subtypes A) : Subtypes B
  ≔ b ↦ ((a : A) → Id B (f a) b → X a .fst,
         pi_prop A (a ↦ Id B (f a) b → X a .fst) (a ↦ pi_prop (Id B (f a) b) (_ ↦ X a .fst) (_ ↦ X a .snd)))

def subtype_preimage_functor (A B : Type) (f : A → B)
  : WildFunctor (SubtypeInclusionPreorder B .wild) (SubtypeInclusionPreorder A .wild)
  ≔ preorder_functor_of_monotone (SubtypeInclusionPreorder B) (SubtypeInclusionPreorder A)
      (subtype_preimage A B f, Y Y' i ↦ a y ↦ i (f a) y)

{` ∃_f ⊣ f^*: ∃_f(X) ⊆ Y iff X ⊆ f^*(Y). `}
def subtype_exists_preimage_iff (A B : Type) (f : A → B)
  : PreorderAdjointIff (SubtypeInclusionPreorder A) (SubtypeInclusionPreorder B)
      (subtype_image_exists A B f) (subtype_preimage A B f)
  ≔ X Y ↦
    (i ↦ a x ↦ i (f a) (mere (Σ A (a' ↦ Product (Id B (f a') (f a)) (X a' .fst))) (a, (refl (f a), x))),
     j ↦ b e ↦ mere_rec (Σ A (a ↦ Product (Id B (f a) b) (X a .fst))) (Y b .fst) (Y b .snd)
       (t ↦ transport B (c ↦ Y c .fst) (f (t .fst)) b (t .snd .fst) (j (t .fst) (t .snd .snd))) e)

{` f^* ⊣ ∀_f: f^*(Y) ⊆ X iff Y ⊆ ∀_f(X). `}
def subtype_preimage_forall_iff (A B : Type) (f : A → B)
  : PreorderAdjointIff (SubtypeInclusionPreorder B) (SubtypeInclusionPreorder A)
      (subtype_preimage A B f) (subtype_coinduced_forall A B f)
  ≔ Y X ↦
    (i ↦ b y a p ↦ i a (transport B (c ↦ Y c .fst) b (f a) (inverse B (f a) b p) y),
     j ↦ a y ↦ j (f a) y a (refl (f a)))

{` The two adjunctions; ∃_f and ∀_f are functors because of the
   biimplications (module 610). `}
def subtype_exists_adjunction (A B : Type) (f : A → B)
  : WildAdjunction (SubtypeInclusionPreorder A .wild) (SubtypeInclusionPreorder B .wild)
  ≔ preorder_adjunction_from_left_map (SubtypeInclusionPreorder A) (SubtypeInclusionPreorder B)
      (subtype_preimage_functor A B f) (subtype_image_exists A B f) (subtype_exists_preimage_iff A B f)

def subtype_forall_right_adjoint (A B : Type) (f : A → B)
  : RightAdjointData (SubtypeInclusionPreorder B .wild) (SubtypeInclusionPreorder A .wild) (subtype_preimage_functor A B f)
  ≔ preorder_adjunction_from_right_map (SubtypeInclusionPreorder B) (SubtypeInclusionPreorder A)
      (subtype_preimage_functor A B f) (subtype_coinduced_forall A B f) (subtype_preimage_forall_iff A B f)

def subtype_exists_adjunction_right (A B : Type) (f : A → B)
  : Id (WildFunctor (SubtypeInclusionPreorder B .wild) (SubtypeInclusionPreorder A .wild))
      (subtype_exists_adjunction A B f .right_adjoint .right) (subtype_preimage_functor A B f)
  ≔ refl (subtype_preimage_functor A B f)

{` Litmus checks for f : Bool → 1: the image of the full subtype contains
   the point, and the coinduced subtype of {true} does not, since false
   lies over it as well. `}
def subtype_exists_bool_full : subtype_image_exists Bool Unit (_ ↦ star.) (full_subtype Bool) star. .fst
  ≔ mere (Σ Bool (a ↦ Product (Id Unit star. star.) Unit)) (true., (refl (star. : Unit), star.))

def subtype_bool_true : Subtypes Bool ≔ b ↦ (Id Bool b true., bool_set b true.)

def subtype_forall_bool_true_empty (h : subtype_coinduced_forall Bool Unit (_ ↦ star.) subtype_bool_true star. .fst)
  : Empty
  ≔ bool_encode false. true. (h false. (refl (star. : Unit)))
