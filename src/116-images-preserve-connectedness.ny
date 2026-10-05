export "115-zero-image-contractibility"

{` A uniform image construction with an explicit reflection and
   constructor. No reflector or surjectivity proof is postulated. `}
def ReflectedImage (R : Type → Type) (A B : Type) (f : A → B) : Type
  ≔ Σ B (b ↦ R (BookFiber A B f b))

def reflected_image_factor (R : Type → Type) (eta : (X : Type) → X → R X) (A B : Type) (f : A → B)
  : A → ReflectedImage R A B f ≔ a ↦ (f a, eta (BookFiber A B f (f a)) (a, refl (f a)))

def reflected_image_factor_fiber_equiv (R : Type → Type) (eta : (X : Type) → X → R X)
  (A B : Type) (f : A → B) (z : ReflectedImage R A B f)
  : Equiv (BookFiber A (ReflectedImage R A B f) (reflected_image_factor R eta A B f) z)
      (BookFiber (BookFiber A B f (z .fst)) (R (BookFiber A B f (z .fst)))
        (eta (BookFiber A B f (z .fst))) (z .snd))
  ≔ let D ≔ Σ B (BookFiber A B f) in
    let G ≔ totalize B (BookFiber A B f) (b ↦ R (BookFiber A B f b)) (b ↦ eta (BookFiber A B f b)) in
    compose_equiv (BookFiber A (ReflectedImage R A B f) (reflected_image_factor R eta A B f) z)
      (BookFiber D (ReflectedImage R A B f) G z)
      (BookFiber (BookFiber A B f (z .fst)) (R (BookFiber A B f (z .fst)))
        (eta (BookFiber A B f (z .fst))) (z .snd))
      (preequivalence_fiber_equiv A D (ReflectedImage R A B f) (fiber_decomposition_equiv A B f) G z)
      (total_fiber_equiv B (BookFiber A B f) (b ↦ R (BookFiber A B f b))
        (b ↦ eta (BookFiber A B f b)) (z .fst) (z .snd))

def reflected_image_factor_surjective (R : Type → Type) (eta : (X : Type) → X → R X)
  (heta : (X : Type) → Surjective X (R X) (eta X)) (A B : Type) (f : A → B)
  : Surjective A (ReflectedImage R A B f) (reflected_image_factor R eta A B f)
  ≔ z ↦ trunc_map native_truncation
      (BookFiber (BookFiber A B f (z .fst)) (R (BookFiber A B f (z .fst)))
        (eta (BookFiber A B f (z .fst))) (z .snd))
      (BookFiber A (ReflectedImage R A B f) (reflected_image_factor R eta A B f) z)
      (equiv_inverse_map (BookFiber A (ReflectedImage R A B f) (reflected_image_factor R eta A B f) z)
        (BookFiber (BookFiber A B f (z .fst)) (R (BookFiber A B f (z .fst)))
          (eta (BookFiber A B f (z .fst))) (z .snd)) (reflected_image_factor_fiber_equiv R eta A B f z))
      (heta (BookFiber A B f (z .fst)) (z .snd))

{` xca:im_preserves_conn reduces uniformly to surjectivity of truncation
   constructors. Higher reflectors are explicit inputs until constructed. `}
def reflected_images_preserve_connectedness (R : Type → Type) (eta : (X : Type) → X → R X)
  (heta : (X : Type) → Surjective X (R X) (eta X)) (A B : Type) (f : A → B) (hA : Connected A)
  : Connected (ReflectedImage R A B f)
  ≔ surjection_preserves_connected native_truncation A (ReflectedImage R A B f)
      (reflected_image_factor R eta A B f) hA (reflected_image_factor_surjective R eta heta A B f)

def propositional_image_connected (A B : Type) (f : A → B) (hA : Connected A) : Connected (Image A B f)
  ≔ surjection_preserves_connected native_truncation A (Image A B f) (image_factor A B f) hA
      (image_factor_surjective A B f)

def zero_image_connected (A B : Type) (f : A → B) (hA : Connected A) : Connected (ZeroImage A B f)
  ≔ reflected_images_preserve_connectedness SetTrunc set_trunc set_trunc_surjective A B f hA
