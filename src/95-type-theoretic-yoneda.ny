export "94-circle-infinite-cycles"

def YonedaSections (X : Type) (F : X → Type) (x : X) : Type
  ≔ (y : X) → Id X x y → F y

def yoneda_transport (X : Type) (F : X → Type) (x : X) (u : F x) : YonedaSections X F x
  ≔ y p ↦ transport X F x y p u

def yoneda_evaluate (X : Type) (F : X → Type) (x : X) (s : YonedaSections X F x) : F x
  ≔ s x (refl x)

def yoneda_transport_evaluate (X : Type) (F : X → Type) (x : X) (u : F x)
  : Id (F x) (yoneda_evaluate X F x (yoneda_transport X F x u)) u
  ≔ transport_refl X F x u

def yoneda_section_eta (X : Type) (F : X → Type) (x : X) (s : YonedaSections X F x)
  (y : X) (p : Id X x y)
  : Id (F y) (yoneda_transport X F x (yoneda_evaluate X F x s) y p) (s y p)
  ≔ J X x (y p ↦ Id (F y) (transport X F x y p (s x (refl x))) (s y p))
      (transport_refl X F x (s x (refl x))) y p

def yoneda_transport_eta (X : Type) (F : X → Type) (x : X) (s : YonedaSections X F x)
  : Id (YonedaSections X F x) (yoneda_transport X F x (yoneda_evaluate X F x s)) s
  ≔ funext2 X (y ↦ Id X x y) (y _ ↦ F y)
      (yoneda_transport X F x (yoneda_evaluate X F x s)) s (yoneda_section_eta X F x s)

{` xca:TTYoneda, first clause.  The forward map is exactly transport;
   its inverse evaluates at the chosen point and reflexivity. `}
def type_theoretic_yoneda (X : Type) (F : X → Type) (x : X)
  : BookEquiv (F x) (YonedaSections X F x)
  ≔ book_quasi_inverse_equiv (F x) (YonedaSections X F x)
      (yoneda_transport X F x) (yoneda_evaluate X F x)
      (yoneda_transport_evaluate X F x) (yoneda_transport_eta X F x)

def yoneda_evaluation_equiv (X : Type) (F : X → Type) (x : X)
  : Equiv (YonedaSections X F x) (F x)
  ≔ quasi_inverse_equiv (YonedaSections X F x) (F x)
      (yoneda_evaluate X F x) (yoneda_transport X F x)
      (yoneda_transport_eta X F x) (yoneda_transport_evaluate X F x)

def Representable (X : Type) (x : X) : X → Type ≔ y ↦ Id X x y

def representable_section_eta (X : Type) (x z : X) (f : YonedaSections X (Representable X z) x)
  (y : X) (p : Id X x y)
  : Id (Id X z y) (concat X z x y (f x (refl x)) p) (f y p)
  ≔ J X x (y p ↦ Id (Id X z y) (concat X z x y (f x (refl x)) p) (f y p))
      (concat_p1 X z x (f x (refl x))) y p

{` A dependent family of maps between representables is already a family
   of equivalences, even when X is not a set or a groupoid. `}
def representable_section_equiv (X : Type) (x z : X) (f : YonedaSections X (Representable X z) x) (y : X)
  : Equiv (Id X x y) (Id X z y)
  ≔ equiv_change_map (Id X x y) (Id X z y) (concat_left_equiv X z x y (f x (refl x)))
      (f y) (representable_section_eta X x z f y)

def RepresentableEquivalences (X : Type) (x z : X) : Type
  ≔ (y : X) → Equiv (Id X x y) (Id X z y)

def representable_equivalences_forget (X : Type) (x z : X) (e : RepresentableEquivalences X x z)
  : YonedaSections X (Representable X z) x ≔ y p ↦ e y .map p

def representable_equivalences_sections (X : Type) (x z : X)
  : Equiv (RepresentableEquivalences X x z) (YonedaSections X (Representable X z) x)
  ≔ quasi_inverse_equiv (RepresentableEquivalences X x z) (YonedaSections X (Representable X z) x)
      (representable_equivalences_forget X x z) (representable_section_equiv X x z)
      (e ↦ funext X (y ↦ Equiv (Id X x y) (Id X z y))
        (representable_section_equiv X x z (representable_equivalences_forget X x z e)) e
        (y ↦ equiv_homotopy (Id X x y) (Id X z y)
          (representable_section_equiv X x z (representable_equivalences_forget X x z e) y) (e y)
          (p ↦ refl (e y .map p)))) (f ↦ refl f)
