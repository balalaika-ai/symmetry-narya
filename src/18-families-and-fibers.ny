export "17-dependent-paths"

{` def:fiberwise and lem:fiberwise. The equivalence has exactly the
   totalization as its underlying map. `}
def totalize (A : Type) (B C : A → Type) (f : (a : A) → B a → C a)
  : Σ A B → Σ A C ≔ t ↦ (t .fst, f (t .fst) (t .snd))

def family_equiv (A : Type) (B C : A → Type) (e : (a : A) → Equiv (B a) (C a))
  : Equiv (Σ A B) (Σ A C)
  ≔ quasi_inverse_equiv (Σ A B) (Σ A C) (totalize A B C (a ↦ e a .map))
      (totalize A C B (a ↦ equiv_inverse_map (B a) (C a) (e a)))
      (t ↦ (refl (t .fst), equiv_retraction (B (t .fst)) (C (t .fst)) (e (t .fst)) (t .snd)))
      (t ↦ (refl (t .fst), equiv_counit (B (t .fst)) (C (t .fst)) (e (t .fst)) (t .snd)))

def contract_away_map (A : Type) (a : A) (B : (x : A) → Id A a x → Type)
  (x : A) (p : Id A a x) : B x p → B a (refl a)
  ≔ J A a (x p ↦ B x p → B a (refl a)) (identity (B a (refl a))) x p

def contract_away_beta (A : Type) (a : A) (B : (x : A) → Id A a x → Type)
  (b : B a (refl a)) : Id (B a (refl a)) (contract_away_map A a B a (refl a) b) b
  ≔ inverse (B a (refl a)) b (contract_away_map A a B a (refl a) b)
      (refl ((f ↦ f b) : (B a (refl a) → B a (refl a)) → B a (refl a))
        (Jβ A a (x p ↦ B x p → B a (refl a)) (identity (B a (refl a)))))

def contract_away_eta (A : Type) (a : A) (B : (x : A) → Id A a x → Type)
  (x : A) (p : Id A a x) (b : B x p)
  : Id (Σ A (y ↦ Σ (Id A a y) (B y)))
      (a, (refl a, contract_away_map A a B x p b)) (x, (p, b))
  ≔ J A a
      (x p ↦ (b : B x p) → Id (Σ A (y ↦ Σ (Id A a y) (B y)))
        (a, (refl a, contract_away_map A a B x p b)) (x, (p, b)))
      (b ↦ (refl a, (refl (refl a), contract_away_beta A a B b))) x p b

{` lem:contract-away, with explicit typal beta for Narya's J. `}
def contract_away_equiv (A : Type) (a : A) (B : (x : A) → Id A a x → Type)
  : Equiv (Σ A (x ↦ Σ (Id A a x) (B x))) (B a (refl a))
  ≔ quasi_inverse_equiv (Σ A (x ↦ Σ (Id A a x) (B x))) (B a (refl a))
      (t ↦ contract_away_map A a B (t .fst) (t .snd .fst) (t .snd .snd))
      (b ↦ (a, (refl a, b)))
      (t ↦ contract_away_eta A a B (t .fst) (t .snd .fst) (t .snd .snd))
      (contract_away_beta A a B)

def contract_away_simple (A : Type) (a : A) (B : A → Type)
  : Equiv (Σ A (x ↦ Product (Id A a x) (B x))) (B a)
  ≔ contract_away_equiv A a (x _ ↦ B x)

{` xca:substitute-away, in the more general path-dependent form. `}
def substitute_away_equiv (A : Type) (a : A) (B : (x : A) → Id A a x → Type)
  : Equiv ((x : A) (p : Id A a x) → B x p) (B a (refl a))
  ≔ quasi_inverse_equiv ((x : A) (p : Id A a x) → B x p) (B a (refl a))
      (f ↦ f a (refl a)) (b x p ↦ J A a B b x p)
      (f ↦ funext2 A (x ↦ Id A a x) B
        (x p ↦ J A a B (f a (refl a)) x p) f (J_section A a B f))
      (b ↦ inverse (B a (refl a)) b (J A a B b a (refl a)) (Jβ A a B b))

{` lem:sum-of-fibers, in the book's orientation b = f(a), with the
   exact map (b,a,p) |-> a. `}
def sum_of_fibers_equiv (A B : Type) (f : A → B)
  : Equiv (Σ B (b ↦ BookFiber A B f b)) A
  ≔ compose_equiv (Σ B (b ↦ BookFiber A B f b))
      (Σ A (a ↦ Σ B (b ↦ Id B b (f a)))) A
      (sigma_comm B A (b a ↦ Id B b (f a)))
      (contractible_fiber_projection A (a ↦ Σ B (b ↦ Id B b (f a)))
        (a ↦ path_to_contractible B (f a)))

def book_sum_of_fibers_equiv (A B : Type) (f : A → B)
  : BookEquiv (Σ B (b ↦ BookFiber A B f b)) A
  ≔ book_equivalence (Σ B (b ↦ BookFiber A B f b)) A (sum_of_fibers_equiv A B f)

{` The exact forward map printed in lem:fst-fiber(a)=B(a), including
   its reflexive path in the book's orientation. `}
def book_projection_inclusion_equiv (A : Type) (B : A → Type) (a : A)
  : BookEquiv (B a) (BookFiber (Σ A B) A (t ↦ t .fst) a)
  ≔ book_quasi_inverse_equiv (B a) (BookFiber (Σ A B) A (t ↦ t .fst) a)
      (b ↦ ((a, b), refl a))
      (t ↦ contract_away_map A a (x _ ↦ B x) (t .fst .fst) (t .snd) (t .fst .snd))
      (contract_away_beta A a (x _ ↦ B x))
      (t ↦ refl
        ((s ↦ ((s .fst, s .snd .snd), s .snd .fst))
          : (Σ A (x ↦ Product (Id A a x) (B x))) → BookFiber (Σ A B) A (t ↦ t .fst) a)
        (contract_away_eta A a (x _ ↦ B x) (t .fst .fst) (t .snd) (t .fst .snd)))

def total_fiber_split (A : Type) (B C : A → Type) (f : (a : A) → B a → C a)
  (a : A) (c : C a)
  : Equiv (BookFiber (Σ A B) (Σ A C) (totalize A B C f) (a, c))
      (Σ A (x ↦ Σ (Id A a x) (p ↦ Σ (B x) (b ↦ Id C p c (f x b)))))
  ≔ quasi_inverse_equiv
      (BookFiber (Σ A B) (Σ A C) (totalize A B C f) (a, c))
      (Σ A (x ↦ Σ (Id A a x) (p ↦ Σ (B x) (b ↦ Id C p c (f x b)))))
      (t ↦ (t .fst .fst, (t .snd .fst, (t .fst .snd, t .snd .snd))))
      (t ↦ ((t .fst, t .snd .snd .fst), (t .snd .fst, t .snd .snd .snd)))
      (t ↦ refl t) (t ↦ refl t)

def total_fiber_equiv (A : Type) (B C : A → Type) (f : (a : A) → B a → C a)
  (a : A) (c : C a)
  : Equiv (BookFiber (Σ A B) (Σ A C) (totalize A B C f) (a, c))
      (BookFiber (B a) (C a) (f a) c)
  ≔ compose_equiv
      (BookFiber (Σ A B) (Σ A C) (totalize A B C f) (a, c))
      (Σ A (x ↦ Σ (Id A a x) (p ↦ Σ (B x) (b ↦ Id C p c (f x b)))))
      (BookFiber (B a) (C a) (f a) c)
      (total_fiber_split A B C f a c)
      (contract_away_equiv A a (x p ↦ Σ (B x) (b ↦ Id C p c (f x b))))

{` lem:fiberwise-equiv-from-tot. Contractibility of each total fiber
   transfers to the corresponding fiber of the family map. `}
def fiberwise_from_total (A : Type) (B C : A → Type) (f : (a : A) → B a → C a)
  (h : isEquiv (Σ A B) (Σ A C) (totalize A B C f))
  : (a : A) → isEquiv (B a) (C a) (f a)
  ≔ a ↦ native_equivalence (B a) (C a)
      (f a, c ↦ book_contraction (BookFiber (B a) (C a) (f a) c)
        (hlevel_equiv zero.
          (BookFiber (Σ A B) (Σ A C) (totalize A B C f) (a, c))
          (BookFiber (B a) (C a) (f a) c) (total_fiber_equiv A B C f a c)
          (native_contraction (BookFiber (Σ A B) (Σ A C) (totalize A B C f) (a, c))
            (book_equivalence (Σ A B) (Σ A C) (totalize A B C f, h) .equiv (a, c))))) .equiv
