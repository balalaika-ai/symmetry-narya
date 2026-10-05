export "13-function-extensionality"

{` Cancellation is derived from the groupoid laws. It does not assume
   that A, or its identity types, are sets. `}
def concat_left_inverse (A : Type) (a b c : A) (p : Id A a b) (q : Id A b c)
  : Id (Id A b c) (concat A b a c (inverse A a b p) (concat A a b c p q)) q
  ≔ calc
    concat A b a c (inverse A a b p) (concat A a b c p q)
    = concat A b b c (concat A b a b (inverse A a b p) p) q
      by concat_assoc A b a b c (inverse A a b p) p q
    = concat A b b c (refl b) q
      by refl ((r ↦ concat A b b c r q) : Id A b b → Id A b c) (concat_inverse_left A a b p)
    = q by concat_1p A b c q ∎

def concat_cancel_left (A : Type) (a b c : A) (p : Id A a b) (q r : Id A b c)
  (s : Id (Id A a c) (concat A a b c p q) (concat A a b c p r))
  : Id (Id A b c) q r
  ≔ calc
    q
    = concat A b a c (inverse A a b p) (concat A a b c p q)
      by concat_left_inverse A a b c p q
    = concat A b a c (inverse A a b p) (concat A a b c p r)
      by refl (concat A b a c (inverse A a b p)) s
    = r by concat_left_inverse A a b c p r ∎

def contraction_naturality (A : Type) (a : A) (h : (x : A) → Id A a x)
  (x y : A) (p : Id A x y)
  : Id (Id A a y) (concat A a x y (h x) p) (h y)
  ≔ J A x (y p ↦ Id (Id A a y) (concat A a x y (h x) p) (h y))
      (concat_p1 A a x (h x)) y p

{` lem:prop-is-set `}
def prop_is_set (A : Type) (h : isProp A) : isSet A
  ≔ x y p q ↦ concat_cancel_left A x x y (h x x) p q
      (concat (Id A x y) (concat A x x y (h x x) p) (h x y)
        (concat A x x y (h x x) q)
        (contraction_naturality A x (h x) x y p)
        (inverse (Id A x y) (concat A x x y (h x x) q) (h x y)
          (contraction_naturality A x (h x) x y q)))

{` xca:prop-contractible=, both implications. `}
def prop_paths_contractible (A : Type) (h : isProp A) (x y : A) : isContr (Id A x y)
  ≔ (h x y, p ↦ prop_is_set A h x y p (h x y))

def contractible_paths_prop (A : Type) (h : (x y : A) → isContr (Id A x y)) : isProp A
  ≔ x y ↦ h x y .center

{` lem:isX-is-prop and xca:isX-is-prop `}
def isprop_isprop (A : Type) : isProp (isProp A)
  ≔ h k ↦ funext2 A (_ ↦ A) (x y ↦ Id A x y) h k
      (x y ↦ prop_is_set A h x y (h x y) (k x y))

def iscontr_isprop (A : Type) : isProp (isContr A)
  ≔ h k ↦
    let hA ≔ contractible_prop A h in
    let p ≔ hA (h .center) (k .center) in
    let P : A → Type ≔ c ↦ (a : A) → Id A a c in
    (p, pathover_of_eq A P (h .center) (k .center) p (h .contract) (k .contract)
      (pi_prop A (a ↦ Id A a (k .center)) (a ↦ prop_is_set A hA a (k .center))
        (transport A P (h .center) (k .center) p (h .contract)) (k .contract)))

def book_iscontr_isprop (A : Type) : isProp (BookIsContr A)
  ≔ h k ↦
    let hA ≔ contractible_prop A (native_contraction A h) in
    let p ≔ hA (h .center) (k .center) in
    let P : A → Type ≔ c ↦ (a : A) → Id A c a in
    (p, pathover_of_eq A P (h .center) (k .center) p (h .contract) (k .contract)
      (pi_prop A (a ↦ Id A (k .center) a) (a ↦ prop_is_set A hA (k .center) a)
        (transport A P (h .center) (k .center) p (h .contract)) (k .contract)))

def isset_isprop (A : Type) : isProp (isSet A)
  ≔ pi_prop A (x ↦ (y : A) → isProp (Id A x y))
      (x ↦ pi_prop A (y ↦ isProp (Id A x y)) (y ↦ isprop_isprop (Id A x y)))

def isgroupoid_isprop (A : Type) : isProp (isGroupoid A)
  ≔ pi_prop A (x ↦ (y : A) → isSet (Id A x y))
      (x ↦ pi_prop A (y ↦ isSet (Id A x y)) (y ↦ isset_isprop (Id A x y)))

def isequiv_isprop (A B : Type) (f : A → B) : isProp (isEquiv A B f)
  ≔ pi_prop B (b ↦ isContr (Fiber A B f b)) (b ↦ iscontr_isprop (Fiber A B f b))

def book_isequiv_isprop (A B : Type) (f : A → B) : isProp (BookIsEquiv A B f)
  ≔ pi_prop B (b ↦ BookIsContr (BookFiber A B f b)) (b ↦ book_iscontr_isprop (BookFiber A B f b))

{` The missing coproduct case of lem:prop-utils. `}
def decidability_prop (P : Type) (hP : isProp P) : isProp (Decidable P)
  ≔ u v ↦ match u, v [
  | inl. p, inl. q ↦ inl. (hP p q)
  | inl. p, inr. nq ↦ absurd (Id (Decidable P) (inl. p) (inr. nq)) (nq p)
  | inr. np, inl. q ↦ absurd (Id (Decidable P) (inr. np) (inl. q)) (np q)
  | inr. np, inr. nq ↦ inr. (negation_prop P np nq) ]

def equiv_path (A B : Type) (e d : Equiv A B) (p : Id (A → B) (e .map) (d .map))
  : Id (Equiv A B) e d
  ≔ (p, pathover_of_eq (A → B) (isEquiv A B) (e .map) (d .map) p (e .equiv) (d .equiv)
      (isequiv_isprop A B (d .map)
        (transport (A → B) (isEquiv A B) (e .map) (d .map) p (e .equiv)) (d .equiv)))

def equiv_homotopy (A B : Type) (e d : Equiv A B) (h : (a : A) → Id B (e .map a) (d .map a))
  : Id (Equiv A B) e d
  ≔ equiv_path A B e d (funext A (_ ↦ B) (e .map) (d .map) h)
