export "12-logic"

{` Uniqueness for J, including its propositional rather than judgmental
   computation at reflexivity. No regularity rule is assumed. `}
def J_section (A : Type) (a : A) (P : (y : A) → Id A a y → Type)
  (s : (y : A) (p : Id A a y) → P y p) (b : A) (p : Id A a b)
  : Id (P b p) (J A a P (s a (refl a)) b p) (s b p)
  ≔ J A a
      (b p ↦ Id (P b p) (J A a P (s a (refl a)) b p) (s b p))
      (inverse (P a (refl a)) (s a (refl a))
        (J A a P (s a (refl a)) a (refl a)) (Jβ A a P (s a (refl a)))) b p

def funext2 (A : Type) (B : A → Type) (C : (a : A) → B a → Type)
  (f g : (a : A) (b : B a) → C a b)
  (h : (a : A) (b : B a) → Id (C a b) (f a b) (g a b))
  : Id ((a : A) (b : B a) → C a b) f g
  ≔ funext A (a ↦ (b : B a) → C a b) f g
      (a ↦ funext (B a) (C a) (f a) (g a) (h a))

def funext3 (A : Type) (B : A → Type) (C : (a : A) → B a → Type)
  (D : (a : A) (b : B a) → C a b → Type)
  (f g : (a : A) (b : B a) (c : C a b) → D a b c)
  (h : (a : A) (b : B a) (c : C a b) → Id (D a b c) (f a b c) (g a b c))
  : Id ((a : A) (b : B a) (c : C a b) → D a b c) f g
  ≔ funext2 A B (a b ↦ (c : C a b) → D a b c) f g
      (a b ↦ funext (C a b) (D a b) (f a b) (g a b) (h a b))

{` A native path of functions has an action on every path in its domain.
   Repackaging this action is definitional in Narya. `}
def PathAction (A : Type) (B : A → Type) (f g : (x : A) → B x) : Type
  ≔ (x y : A) (q : Id A x y) → Id B q (f x) (g y)

def path_action (A : Type) (B : A → Type) (f g : (x : A) → B x)
  (p : Id ((x : A) → B x) f g) : PathAction A B f g ≔ x y q ↦ p q

def action_path (A : Type) (B : A → Type) (f g : (x : A) → B x)
  (h : PathAction A B f g) : Id ((x : A) → B x) f g
  ≔ x ⤇ h x.0 x.1 x.2

def function_path_ext (A : Type) (B : A → Type) (f g : (x : A) → B x)
  (p q : Id ((x : A) → B x) f g)
  (h : (x y : A) (r : Id A x y) → Id (Id B r (f x) (g y)) (p r) (q r))
  : Id (Id ((x : A) → B x) f g) p q
  ≔ refl (action_path A B f g)
      (funext3 A (_ ↦ A) (x y ↦ Id A x y) (x y r ↦ Id B r (f x) (g y))
        (path_action A B f g p) (path_action A B f g q) h)

def funext_eta (A : Type) (B : A → Type) (f g : (x : A) → B x)
  (p : Id ((x : A) → B x) f g)
  : Id (Id ((x : A) → B x) f g) (funext A B f g (happly A B f g p)) p
  ≔ function_path_ext A B f g (funext A B f g (happly A B f g p)) p
      (x y r ↦ J_section A x (y r ↦ Id B r (f x) (g y)) (y r ↦ p r) y r)

def funext_beta_function (A : Type) (B : A → Type) (f g : (x : A) → B x)
  (h : Homotopy A B f g)
  : Id (Homotopy A B f g) (happly A B f g (funext A B f g h)) h
  ≔ funext A (x ↦ Id (B x) (f x) (g x))
      (happly A B f g (funext A B f g h)) h
      (x ↦ inverse (Id (B x) (f x) (g x)) (h x)
        (happly A B f g (funext A B f g h) x) (funext_beta A B f g h x))

{` def:funext, the full equivalence for dependent functions. `}
def function_extensionality (A : Type) (B : A → Type) (f g : (x : A) → B x)
  : Equiv (Id ((x : A) → B x) f g) (Homotopy A B f g)
  ≔ quasi_inverse_equiv (Id ((x : A) → B x) f g) (Homotopy A B f g)
      (happly A B f g) (funext A B f g) (funext_eta A B f g) (funext_beta_function A B f g)

def book_function_extensionality (A : Type) (B : A → Type) (f g : (x : A) → B x)
  : BookEquiv (Id ((x : A) → B x) f g) (Homotopy A B f g)
  ≔ book_equivalence (Id ((x : A) → B x) f g) (Homotopy A B f g)
      (function_extensionality A B f g)
