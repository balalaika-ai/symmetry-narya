export "613-subtype-image-adjunctions"

{` Chapter 5, rem:^*-_!-as-(pre)image and rem:coinduced-subset: preimage
   f^*Y = Y ∘ f, image ∃_f X and coinduced subset ∀_f X of subtypes along
   f : A → B. The three operations are the ones of chapter 6, module 613
   (subtype_preimage, subtype_image_exists, subtype_coinduced_forall), which
   are literally the printed formulas; here are the claims of the remarks. `}

{` f^*Y consists of the a : A with f(a) in Y. `}
def subtype_preimage_member (A B : Type) (f : A → B) (Y : Subtypes B) (a : A)
  : Id Type (subtype_preimage A B f Y a .fst) (Y (f a) .fst)
  ≔ refl (Y (f a) .fst)

{` ∃_f X holds exactly for the b with some a in X and f(a) = b; this is f_!X
   with propositional instead of set truncation. `}
def subtype_image_member (A B : Type) (f : A → B) (X : Subtypes A) (b : B)
  : Id Type (subtype_image_exists A B f X b .fst) (Mere (Σ A (a ↦ Product (Id B (f a) b) (X a .fst))))
  ≔ refl (Mere (Σ A (a ↦ Product (Id B (f a) b) (X a .fst))))

{` rem:coinduced-subset: ∀_f X contains b iff the whole preimage f⁻¹(b) is
   contained in X. `}
def subtype_forall_preimage_equiv (A B : Type) (f : A → B) (X : Subtypes A) (b : B)
  : Equiv (subtype_coinduced_forall A B f X b .fst) ((u : BookFiber A B f b) → X (u .fst) .fst)
  ≔ iff_equiv (subtype_coinduced_forall A B f X b .fst) ((u : BookFiber A B f b) → X (u .fst) .fst)
      (subtype_coinduced_forall A B f X b .snd)
      (pi_prop (BookFiber A B f b) (u ↦ X (u .fst) .fst) (u ↦ X (u .fst) .snd))
      (h u ↦ h (u .fst) (inverse B b (f (u .fst)) (u .snd)))
      (h a p ↦ h (a, inverse B (f a) b p))

{` "Predicates on connected types are constant." `}
def connected_subtype_constant (A : Type) (hA : Connected A) (P : Subtypes A) (x y : A)
  : Id PropTypes (P x) (P y)
  ≔ same_component_properties native_truncation A P x y (hA .snd x y)
