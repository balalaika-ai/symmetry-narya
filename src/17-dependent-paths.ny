export "16-inductive-identities"

def PathOver (A : Type) (B : A → Type) (x y : A) (p : Id A x y) (u : B x) (v : B y)
  : Type ≔ Id B p u v

{` def:pathover-trp, as a path in the universe. In the reflexive case,
   native transport has a typal computation law, used explicitly here. `}
def pathover_transport_type (A : Type) (B : A → Type) (x y : A) (p : Id A x y)
  (u : B x) (v : B y)
  : Id Type (Id B p u v) (Id (B y) (transport A B x y p u) v)
  ≔ J A x
      (y p ↦ (v : B y) → Id Type (Id B p u v) (Id (B y) (transport A B x y p u) v))
      (v ↦ refl ((b ↦ Id (B x) b v) : B x → Type)
        (inverse (B x) (transport A B x x (refl x) u) u (transport_refl A B x u))) y p v

def pathover_transport_equiv (A : Type) (B : A → Type) (x y : A) (p : Id A x y)
  (u : B x) (v : B y) : Equiv (Id B p u v) (Id (B y) (transport A B x y p u) v)
  ≔ id_to_equiv (Id B p u v) (Id (B y) (transport A B x y p u) v)
      (pathover_transport_type A B x y p u v)

{` def:pathovercomposition. Native sigma transport retains the base path. `}
def pathover_concat (A : Type) (B : A → Type) (x y z : A)
  (p : Id A x y) (r : Id A y z) (u : B x) (v : B y) (w : B z)
  (q : Id B p u v) (s : Id B r v w) : Id B (concat A x y z p r) u w
  ≔ concat (Σ A B) (x, u) (y, v) (z, w) (p, q) (r, s) .snd

def pathover_inverse (A : Type) (B : A → Type) (x y : A) (p : Id A x y)
  (u : B x) (v : B y) (q : Id B p u v) : Id B (inverse A x y p) v u
  ≔ inverse (Σ A B) (x, u) (y, v) (p, q) .snd

{` Projection of a family of contractible types is an equivalence. `}
def contractible_fiber_projection (A : Type) (B : A → Type) (h : (a : A) → isContr (B a))
  : Equiv (Σ A B) A
  ≔ quasi_inverse_equiv (Σ A B) A (t ↦ t .fst) (a ↦ (a, h a .center))
      (t ↦ (refl (t .fst), inverse (B (t .fst)) (t .snd) (h (t .fst) .center)
        (h (t .fst) .contract (t .snd)))) (a ↦ refl a)

{` lem:subtype-eq-=, with the actual projection on paths. `}
def subtype_path_equiv (A : Type) (B : A → Type) (hB : (a : A) → isProp (B a))
  (u v : Σ A B) : Equiv (Id (Σ A B) u v) (Id A (u .fst) (v .fst))
  ≔ let h : (p : Id A (u .fst) (v .fst)) → isContr (Id B p (u .snd) (v .snd))
      ≔ p ↦ pathover_hlevel zero. A B (a ↦ prop_to_hlevel_one (B a) (hB a))
          (u .fst) (v .fst) p (u .snd) (v .snd) in
    quasi_inverse_equiv (Id (Σ A B) u v) (Id A (u .fst) (v .fst))
      (r ↦ r .fst) (p ↦ (p, h p .center))
      (r ↦ (refl (r .fst), inverse (Id B (r .fst) (u .snd) (v .snd))
        (r .snd) (h (r .fst) .center) (h (r .fst) .contract (r .snd))))
      (p ↦ refl p)

def projection_fiber_to (A : Type) (B : A → Type) (a : A)
  (t : Fiber (Σ A B) A (s ↦ s .fst) a) : B a
  ≔ transport A B (t .fst .fst) a (t .snd) (t .fst .snd)

def projection_fiber_from (A : Type) (B : A → Type) (a : A) (b : B a)
  : Fiber (Σ A B) A (s ↦ s .fst) a ≔ ((a, b), refl a)

def projection_fiber_eta (A : Type) (B : A → Type) (x : A) (u : B x)
  (y : A) (p : Id A x y)
  : Id (Fiber (Σ A B) A (s ↦ s .fst) y)
      (projection_fiber_from A B y (transport A B x y p u)) ((x, u), p)
  ≔ J A x
      (y p ↦ Id (Fiber (Σ A B) A (s ↦ s .fst) y)
        (projection_fiber_from A B y (transport A B x y p u)) ((x, u), p))
      (refl (projection_fiber_from A B x) (transport_refl A B x u)) y p

{` lem:fst-fiber(a)=B(a), first in native fiber orientation. `}
def projection_fiber_equiv (A : Type) (B : A → Type) (a : A)
  : Equiv (Fiber (Σ A B) A (s ↦ s .fst) a) (B a)
  ≔ quasi_inverse_equiv (Fiber (Σ A B) A (s ↦ s .fst) a) (B a)
      (projection_fiber_to A B a) (projection_fiber_from A B a)
      (t ↦ projection_fiber_eta A B (t .fst .fst) (t .fst .snd) a (t .snd))
      (transport_refl A B a)

def book_projection_fiber_equiv (A : Type) (B : A → Type) (a : A)
  : BookEquiv (BookFiber (Σ A B) A (s ↦ s .fst) a) (B a)
  ≔ book_equivalence (BookFiber (Σ A B) A (s ↦ s .fst) a) (B a)
      (compose_equiv (BookFiber (Σ A B) A (s ↦ s .fst) a)
        (Fiber (Σ A B) A (s ↦ s .fst) a) (B a)
        (canonical_inverse_equiv (Fiber (Σ A B) A (s ↦ s .fst) a)
          (BookFiber (Σ A B) A (s ↦ s .fst) a) (fiber_conventions_equiv (Σ A B) A (s ↦ s .fst) a))
        (projection_fiber_equiv A B a))
