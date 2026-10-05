export "09-circle"
export "10-equivalence-calculus"

{` The book orients contractions center→point and fiber paths b→f(a).
   The imported Narya library uses the reverse conventions. These explicit
   adapters ensure statements can also be read in the book's exact types. `}
def BookIsContr (A : Type) : Type ≔ sig (center : A, contract : (a : A) → Id A center a)

def BookFiber (A B : Type) (f : A → B) (b : B) : Type ≔ Σ A (a ↦ Id B b (f a))

def BookIsEquiv (A B : Type) (f : A → B) : Type
  ≔ (b : B) → BookIsContr (BookFiber A B f b)

def BookEquiv (A B : Type) : Type ≔ sig (map : A → B, equiv : BookIsEquiv A B map)

def book_contraction (A : Type) (h : isContr A) : BookIsContr A
  ≔ (h .center, a ↦ inverse A a (h .center) (h .contract a))

def native_contraction (A : Type) (h : BookIsContr A) : isContr A
  ≔ (h .center, a ↦ inverse A (h .center) a (h .contract a))

def fiber_to_book (A B : Type) (f : A → B) (b : B) (t : Fiber A B f b)
  : BookFiber A B f b ≔ (t .fst, inverse B (f (t .fst)) b (t .snd))

def fiber_from_book (A B : Type) (f : A → B) (b : B) (t : BookFiber A B f b)
  : Fiber A B f b ≔ (t .fst, inverse B b (f (t .fst)) (t .snd))

def fiber_conventions_equiv (A B : Type) (f : A → B) (b : B)
  : Equiv (Fiber A B f b) (BookFiber A B f b)
  ≔ quasi_inverse_equiv (Fiber A B f b) (BookFiber A B f b)
      (fiber_to_book A B f b) (fiber_from_book A B f b)
      (t ↦ (refl (t .fst), inverse_inverse B (f (t .fst)) b (t .snd)))
      (t ↦ (refl (t .fst), inverse_inverse B b (f (t .fst)) (t .snd)))

def book_equivalence (A B : Type) (e : Equiv A B) : BookEquiv A B
  ≔ (e .map, b ↦ book_contraction (BookFiber A B (e .map) b)
      (contractible_retract (Fiber A B (e .map) b) (BookFiber A B (e .map) b)
        (e .equiv b) (fiber_to_book A B (e .map) b) (fiber_from_book A B (e .map) b)
        (t ↦ (refl (t .fst), inverse_inverse B b (e .map (t .fst)) (t .snd)))))

def native_equivalence (A B : Type) (e : BookEquiv A B) : Equiv A B
  ≔ (e .map, b ↦
      contractible_retract (BookFiber A B (e .map) b) (Fiber A B (e .map) b)
        (native_contraction (BookFiber A B (e .map) b) (e .equiv b))
        (fiber_from_book A B (e .map) b) (fiber_to_book A B (e .map) b)
        (t ↦ (refl (t .fst), inverse_inverse B (e .map (t .fst)) b (t .snd))))

def book_pathspace_contractible (A : Type) (a : A)
  : BookIsContr (Σ A (x ↦ Id A a x))
  ≔ book_contraction (Σ A (x ↦ Id A a x)) (iscontr_idfrom A a)

def book_quasi_inverse_equiv (A B : Type) (f : A → B) (g : B → A)
  (eta : (a : A) → Id A (g (f a)) a) (epsilon : (b : B) → Id B (f (g b)) b)
  : BookEquiv A B ≔ book_equivalence A B (quasi_inverse_equiv A B f g eta epsilon)

def book_circle_universal_property (C : CircleSignature) (A : Type)
  : BookEquiv (C .carrier → A) (FreeLoop A)
  ≔ book_equivalence (C .carrier → A) (FreeLoop A) (circle_universal_property C A)
