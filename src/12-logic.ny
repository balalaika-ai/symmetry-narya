export "11-book-conventions"

{` This module is relative to the book's propositional truncation principle. `}
def trunc_rec (T : TruncationSignature) (A P : Type) (hP : isProp P) (f : A → P)
  : T .carrier A → P ≔ T .eliminate A (_ ↦ P) (_ ↦ hP) f

def trunc_map (T : TruncationSignature) (A B : Type) (f : A → B)
  : T .carrier A → T .carrier B
  ≔ trunc_rec T A (T .carrier B) (T .proposition B) (a ↦ T .include B (f a))

def trunc_prop_equiv (T : TruncationSignature) (P : Type) (hP : isProp P)
  : Equiv P (T .carrier P)
  ≔ let back ≔ trunc_rec T P P hP (identity P) in
    quasi_inverse_equiv P (T .carrier P) (T .include P) back
      (p ↦ hP (back (T .include P p)) p)
      (t ↦ T .proposition P (T .include P (back t)) t)

def Or (T : TruncationSignature) (P Q : Type) : Type ≔ T .carrier (Sum P Q)
def Exists (T : TruncationSignature) (A : Type) (P : A → Type) : Type ≔ T .carrier (Σ A P)
def ExistsUnique (A : Type) (P : A → Type) : Type ≔ BookIsContr (Σ A P)

def IsConnected (T : TruncationSignature) (A : Type) : Type
  ≔ Product (T .carrier A) ((x y : A) → T .carrier (Id A x y))

def Component (T : TruncationSignature) (A : Type) (a : A) : Type
  ≔ Σ A (x ↦ T .carrier (Id A a x))

def merely_paths_compose (T : TruncationSignature) (A : Type) (a x y : A)
  (p : T .carrier (Id A a x)) (q : T .carrier (Id A a y)) : T .carrier (Id A x y)
  ≔ trunc_rec T (Id A a x) (T .carrier (Id A x y)) (T .proposition (Id A x y))
      (px ↦ trunc_rec T (Id A a y) (T .carrier (Id A x y)) (T .proposition (Id A x y))
        (py ↦ T .include (Id A x y) (concat A x a y (inverse A a x px) py)) q) p

{` lem:circleisconnected with the full nonempty/pairwise definition. `}
def circle_is_connected (T : TruncationSignature) (C : CircleSignature)
  : IsConnected T (C .carrier)
  ≔ (T .include (C .carrier) (C .base), x y ↦
      merely_paths_compose T (C .carrier) (C .base) x y
        (circle_connected T C x) (circle_connected T C y))

{` def:injection uses proposition-valued fibers. This differs from the
   path-reflection hypothesis used in the elementary set lemmas. `}
def IsEmbedding (A B : Type) (f : A → B) : Type
  ≔ (b : B) → isProp (BookFiber A B f b)

def IsSurjection (T : TruncationSignature) (A B : Type) (f : A → B) : Type
  ≔ (b : B) → T .carrier (BookFiber A B f b)

{` lem:inj+surj, using the book's exact conventions. `}
def embedding_surjection_equiv (T : TruncationSignature) (A B : Type) (f : A → B)
  (inj : IsEmbedding A B f) (surj : IsSurjection T A B f) : BookEquiv A B
  ≔ (f, b ↦
      let center ≔ trunc_rec T (BookFiber A B f b) (BookFiber A B f b) (inj b)
        (identity (BookFiber A B f b)) (surj b) in
      (center, t ↦ inj b center t))
