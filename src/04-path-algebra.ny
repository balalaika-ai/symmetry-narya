export "00-foundations"

{` xca:path-groupoid-laws and the transport laws. J computes propositionally
   in native HOTT, so the reflexive branches include explicit unit proofs. `}
def transport_refl (A : Type) (B : A → Type) (x : A) (b : B x)
  : Id (B x) (transport A B x x (refl x) b) b
  ≔ inverse (B x) b (transport A B x x (refl x) b) (refl B (refl x) .liftr b)

def inverse_refl (A : Type) (x : A)
  : Id (Id A x x) (inverse A x x (refl x)) (refl x)
  ≔ transport_refl A (z ↦ Id A z x) x (refl x)

def concat_assoc (A : Type) (x y z w : A)
  (p : Id A x y) (q : Id A y z) (r : Id A z w)
  : Id (Id A x w)
      (concat A x z w (concat A x y z p q) r)
      (concat A x y w p (concat A y z w q r))
  ≔ J A z
      (w r ↦ Id (Id A x w)
        (concat A x z w (concat A x y z p q) r)
        (concat A x y w p (concat A y z w q r)))
      (concat (Id A x z)
        (concat A x z z (concat A x y z p q) (refl z))
        (concat A x y z p q)
        (concat A x y z p (concat A y z z q (refl z)))
        (concat_p1 A x z (concat A x y z p q))
        (inverse (Id A x z)
          (concat A x y z p (concat A y z z q (refl z)))
          (concat A x y z p q)
          (refl (concat A x y z p) (concat_p1 A y z q))))
      w r

def inverse_inverse (A : Type) (x y : A) (p : Id A x y)
  : Id (Id A x y) (inverse A y x (inverse A x y p)) p
  ≔ J A x
      (y p ↦ Id (Id A x y) (inverse A y x (inverse A x y p)) p)
      (concat (Id A x x)
        (inverse A x x (inverse A x x (refl x)))
        (inverse A x x (refl x)) (refl x)
        (refl (inverse A x x) (inverse_refl A x))
        (inverse_refl A x)) y p

def concat_inverse_right (A : Type) (x y : A) (p : Id A x y)
  : Id (Id A x x) (concat A x y x p (inverse A x y p)) (refl x)
  ≔ J A x
      (y p ↦ Id (Id A x x) (concat A x y x p (inverse A x y p)) (refl x))
      (concat (Id A x x)
        (concat A x x x (refl x) (inverse A x x (refl x)))
        (inverse A x x (refl x)) (refl x)
        (concat_1p A x x (inverse A x x (refl x)))
        (inverse_refl A x)) y p

def concat_inverse_left (A : Type) (x y : A) (p : Id A x y)
  : Id (Id A y y) (concat A y x y (inverse A x y p) p) (refl y)
  ≔ J A x
      (y p ↦ Id (Id A y y) (concat A y x y (inverse A x y p) p) (refl y))
      (concat (Id A x x)
        (concat A x x x (inverse A x x (refl x)) (refl x))
        (inverse A x x (refl x)) (refl x)
        (concat_p1 A x x (inverse A x x (refl x)))
        (inverse_refl A x)) y p

def transport_concat (A : Type) (B : A → Type) (x y z : A)
  (p : Id A x y) (q : Id A y z) (b : B x)
  : Id (B z) (transport A B x z (concat A x y z p q) b)
      (transport A B y z q (transport A B x y p b))
  ≔ J A y
      (z q ↦ Id (B z) (transport A B x z (concat A x y z p q) b)
        (transport A B y z q (transport A B x y p b)))
      (concat (B y)
        (transport A B x y (concat A x y y p (refl y)) b)
        (transport A B x y p b)
        (transport A B y y (refl y) (transport A B x y p b))
        (refl ((r ↦ transport A B x y r b) : Id A x y → B y) (concat_p1 A x y p))
        (inverse (B y)
          (transport A B y y (refl y) (transport A B x y p b))
          (transport A B x y p b)
          (transport_refl A B y (transport A B x y p b)))) z q

def transport_constant (A B : Type) (x y : A) (p : Id A x y) (b : B)
  : Id B (transport A (_ ↦ B) x y p b) b
  ≔ transport_refl A (_ ↦ B) x b

def transport_ap (A B : Type) (C : B → Type) (f : A → B)
  (x y : A) (p : Id A x y) (c : C (f x))
  : Id (C (f y)) (transport A (a ↦ C (f a)) x y p c)
      (transport B C (f x) (f y) (map_path A B f x y p) c)
  ≔ refl (transport A (a ↦ C (f a)) x y p c)

{` The exercises ask for equality of functions, not just pointwise equality. `}
def transport_concat_function (A : Type) (B : A → Type) (x y z : A)
  (p : Id A x y) (q : Id A y z)
  : Id (B x → B z) (transport A B x z (concat A x y z p q))
      (b ↦ transport A B y z q (transport A B x y p b))
  ≔ funext (B x) (_ ↦ B z) (transport A B x z (concat A x y z p q))
      (b ↦ transport A B y z q (transport A B x y p b)) (transport_concat A B x y z p q)

def transport_constant_function (A B : Type) (x y : A) (p : Id A x y)
  : Id (B → B) (transport A (_ ↦ B) x y p) (identity B)
  ≔ funext B (_ ↦ B) (transport A (_ ↦ B) x y p) (identity B)
      (transport_constant A B x y p)

def transport_ap_function (A B : Type) (C : B → Type) (f : A → B)
  (x y : A) (p : Id A x y)
  : Id (C (f x) → C (f y)) (transport A (a ↦ C (f a)) x y p)
      (transport B C (f x) (f y) (map_path A B f x y p))
  ≔ refl (transport A (a ↦ C (f a)) x y p)

{` lem:apcomp: preservation of composition and inverse. `}
def map_path_concat (A B : Type) (f : A → B) (x y z : A)
  (p : Id A x y) (q : Id A y z)
  : Id (Id B (f x) (f z)) (refl f (concat A x y z p q))
      (concat B (f x) (f y) (f z) (refl f p) (refl f q))
  ≔ J A y
      (z q ↦ Id (Id B (f x) (f z)) (refl f (concat A x y z p q))
        (concat B (f x) (f y) (f z) (refl f p) (refl f q)))
      (concat (Id B (f x) (f y))
        (refl f (concat A x y y p (refl y))) (refl f p)
        (concat B (f x) (f y) (f y) (refl f p) (refl (f y)))
        (refl ((r ↦ refl f r) : Id A x y → Id B (f x) (f y)) (concat_p1 A x y p))
        (inverse (Id B (f x) (f y))
          (concat B (f x) (f y) (f y) (refl f p) (refl (f y))) (refl f p)
          (concat_p1 B (f x) (f y) (refl f p)))) z q

def map_path_inverse (A B : Type) (f : A → B) (x y : A) (p : Id A x y)
  : Id (Id B (f y) (f x)) (refl f (inverse A x y p))
      (inverse B (f x) (f y) (refl f p))
  ≔ J A x
      (y p ↦ Id (Id B (f y) (f x)) (refl f (inverse A x y p))
        (inverse B (f x) (f y) (refl f p)))
      (concat (Id B (f x) (f x))
        (refl f (inverse A x x (refl x))) (refl (f x))
        (inverse B (f x) (f x) (refl (f x)))
        (refl ((r ↦ refl f r) : Id A x x → Id B (f x) (f x)) (inverse_refl A x))
        (inverse (Id B (f x) (f x)) (inverse B (f x) (f x) (refl (f x)))
          (refl (f x)) (inverse_refl B (f x)))) y p

def naturality (A B : Type) (f g : A → B) (h : (a : A) → Id B (f a) (g a))
  (x y : A) (p : Id A x y)
  : Id (Id B (f x) (g y))
      (concat B (f x) (f y) (g y) (refl f p) (h y))
      (concat B (f x) (g x) (g y) (h x) (refl g p))
  ≔ J A x
      (y p ↦ Id (Id B (f x) (g y))
        (concat B (f x) (f y) (g y) (refl f p) (h y))
        (concat B (f x) (g x) (g y) (h x) (refl g p)))
      (concat (Id B (f x) (g x))
        (concat B (f x) (f x) (g x) (refl (f x)) (h x)) (h x)
        (concat B (f x) (g x) (g x) (h x) (refl (g x)))
        (concat_1p B (f x) (g x) (h x))
        (inverse (Id B (f x) (g x))
          (concat B (f x) (g x) (g x) (h x) (refl (g x))) (h x)
          (concat_p1 B (f x) (g x) (h x)))) y p
