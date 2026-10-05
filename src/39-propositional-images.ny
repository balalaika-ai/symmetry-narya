export "38-finite-components"

{` def:prop-image, with the exact book fiber orientation. `}
def Image (A B : Type) (f : A → B) : Type ≔ Σ B (b ↦ Mere (BookFiber A B f b))

def image_factor (A B : Type) (f : A → B) (a : A) : Image A B f
  ≔ (f a, mere (BookFiber A B f (f a)) (a, refl (f a)))

def image_include (A B : Type) (f : A → B) (z : Image A B f) : B ≔ z .fst

def image_triangle (A B : Type) (f : A → B)
  : Id (A → B) f (compose A (Image A B f) B (image_include A B f) (image_factor A B f))
  ≔ refl f

def image_factor_surjective (A B : Type) (f : A → B) : Surjective A (Image A B f) (image_factor A B f)
  ≔ z ↦ mere_rec (BookFiber A B f (z .fst))
      (Mere (BookFiber A (Image A B f) (image_factor A B f) z))
      (mere_isprop (BookFiber A (Image A B f) (image_factor A B f) z))
      (w ↦ mere (BookFiber A (Image A B f) (image_factor A B f) z)
        (w .fst, subtype_equal B (b ↦ Mere (BookFiber A B f b))
          (b ↦ mere_isprop (BookFiber A B f b)) z (image_factor A B f (w .fst)) (w .snd))) (z .snd)

def subtype_embedding (A : Type) (P : A → Type) (hp : (a : A) → isProp (P a))
  : IsEmbedding (Σ A P) A (z ↦ z .fst)
  ≔ path_equivalences_embedding (Σ A P) A (z ↦ z .fst)
      (u v ↦ book_equivalence (Id (Σ A P) u v) (Id A (u .fst) (v .fst))
        (subtype_path_equiv A P hp u v) .equiv)

def image_include_embedding (A B : Type) (f : A → B) : IsEmbedding (Image A B f) B (image_include A B f)
  ≔ subtype_embedding B (b ↦ Mere (BookFiber A B f b)) (b ↦ mere_isprop (BookFiber A B f b))

def ImageFactorizations (A B : Type) (f : A → B) : Type
  ≔ Σ Type (C ↦ Σ (A → C) (g ↦ Σ (C → B) (h ↦
      Product (Id (A → B) f (compose A C B h g))
        (Product (Surjective A C g) (IsEmbedding C B h)))))

{` The canonical factorization; module 101 contracts the full factorization type. `}
def image_factorization (A B : Type) (f : A → B) : ImageFactorizations A B f
  ≔ (Image A B f, (image_factor A B f, (image_include A B f,
      (image_triangle A B f, (image_factor_surjective A B f, image_include_embedding A B f)))))

{` xca:prop-image-is-set. `}
def image_set (A B : Type) (f : A → B) (hb : isSet B) : isSet (Image A B f)
  ≔ sigma_set B (b ↦ Mere (BookFiber A B f b)) hb
      (b ↦ prop_is_set (Mere (BookFiber A B f b)) (mere_isprop (BookFiber A B f b)))

def image_prop_eliminate (A B : Type) (f : A → B) (P : B → Type)
  (hp : (b : B) → isProp (P b)) (g : (a : A) → P (f a)) (z : Image A B f) : P (z .fst)
  ≔ mere_rec (BookFiber A B f (z .fst)) (P (z .fst)) (hp (z .fst))
      (w ↦ transport B P (f (w .fst)) (z .fst)
        (inverse B (z .fst) (f (w .fst)) (w .snd)) (g (w .fst))) (z .snd)

{` xca:all-prop-image. `}
def image_all_propositions (A B : Type) (f : A → B) (P : B → Type) (hp : (b : B) → isProp (P b))
  : Equiv ((z : Image A B f) → P (z .fst)) ((a : A) → P (f a))
  ≔ iff_equiv ((z : Image A B f) → P (z .fst)) ((a : A) → P (f a))
      (pi_prop (Image A B f) (z ↦ P (z .fst)) (z ↦ hp (z .fst)))
      (pi_prop A (a ↦ P (f a)) (a ↦ hp (f a)))
      (g a ↦ g (image_factor A B f a)) (image_prop_eliminate A B f P hp)

def WeaklyConstant (A B : Type) (f : A → B) : Type ≔ (x y : A) → Id B (f x) (f y)

def weakly_constant_prop (A B : Type) (f : A → B) (hb : isSet B) : isProp (WeaklyConstant A B f)
  ≔ pi_prop A (x ↦ (y : A) → Id B (f x) (f y))
      (x ↦ pi_prop A (y ↦ Id B (f x) (f y)) (y ↦ hb (f x) (f y)))

def weakly_constant_image_prop (A B : Type) (f : A → B) (hb : isSet B) (h : WeaklyConstant A B f)
  : isProp (Image A B f)
  ≔ u v ↦ subtype_equal B (b ↦ Mere (BookFiber A B f b)) (b ↦ mere_isprop (BookFiber A B f b)) u v
      (mere_rec (BookFiber A B f (u .fst)) (Id B (u .fst) (v .fst)) (hb (u .fst) (v .fst))
        (x ↦ mere_rec (BookFiber A B f (v .fst)) (Id B (u .fst) (v .fst)) (hb (u .fst) (v .fst))
          (y ↦ concat B (u .fst) (f (x .fst)) (v .fst) (x .snd)
            (concat B (f (x .fst)) (f (y .fst)) (v .fst) (h (x .fst) (y .fst))
              (inverse B (v .fst) (f (y .fst)) (y .snd)))) (v .snd)) (u .snd))

{` thm:wconstant-elim. The computation at mere a is judgmental for this recursor. `}
def weakly_constant_rec (A B : Type) (f : A → B) (hb : isSet B) (h : WeaklyConstant A B f)
  (t : Mere A) : B
  ≔ image_include A B f
      (mere_rec A (Image A B f) (weakly_constant_image_prop A B f hb h) (image_factor A B f) t)

def weakly_constant_rec_beta (A B : Type) (f : A → B) (hb : isSet B)
  (h : WeaklyConstant A B f) (a : A)
  : Id B (weakly_constant_rec A B f hb h (mere A a)) (f a) ≔ refl (f a)

def finite_sets_image_equiv : Equiv FiniteSets (Image Nat Type Fin) ≔ finite_sets_universe_equiv

def finite_sets_image_path : Id Type FiniteSets (Image Nat Type Fin)
  ≔ ua FiniteSets (Image Nat Type Fin) finite_sets_image_equiv
