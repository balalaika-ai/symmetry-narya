export "603-adjunctions-and-equivalences"

{` Chapter 6 (cats.tex), section 6.9: def:pullback, xca:univpropofpullback,
   the inline definition of a pullback diagram, and the example after it
   (the preimage of a point is a pullback). `}

{` def:pullback: B ×_D C ≔ Σ_{(b,c) : B × C} f(b) = g(c), with the two
   projections. `}
def TypePullback (B C D : Type) (f : B → D) (g : C → D) : Type
  ≔ Σ (Product B C) (bc ↦ Id D (f (bc .fst)) (g (bc .snd)))

def pullback_proj_left (B C D : Type) (f : B → D) (g : C → D) : TypePullback B C D f g → B
  ≔ t ↦ t .fst .fst

def pullback_proj_right (B C D : Type) (f : B → D) (g : C → D) : TypePullback B C D f g → C
  ≔ t ↦ t .fst .snd

{` The square of def:pullback commutes: f ∘ prj_B = g ∘ prj_C. `}
def pullback_square_commutes (B C D : Type) (f : B → D) (g : C → D)
  : Id (TypePullback B C D f g → D) (t ↦ f (pullback_proj_left B C D f g t)) (t ↦ g (pullback_proj_right B C D f g t))
  ≔ funext (TypePullback B C D f g) (_ ↦ D) (t ↦ f (t .fst .fst)) (t ↦ g (t .fst .snd)) (t ↦ t .snd)

{` xca:univpropofpullback. The domain is the pullback of f ∘ - and g ∘ -,
   (A → B) ×_{(A → D)} (A → C), whose elements are triples (β, γ, p) with
   p : f ∘ β = g ∘ γ. The book prints the image of (β, γ, p) as
   a ↦ (f(a), g(a), p(a)), which does not typecheck; the intended map is
   a ↦ (β(a), γ(a), p(a)) with p(a) the pointwise identification
   (happly). `}
def PullbackOfPostcomp (A B C D : Type) (f : B → D) (g : C → D) : Type
  ≔ TypePullback (A → B) (A → C) (A → D) (beta ↦ x ↦ f (beta x)) (gamma ↦ x ↦ g (gamma x))

def pullback_gap_map (A B C D : Type) (f : B → D) (g : C → D) (w : PullbackOfPostcomp A B C D f g)
  : A → TypePullback B C D f g
  ≔ a ↦ ((w .fst .fst a, w .fst .snd a),
         happly A (_ ↦ D) (x ↦ f (w .fst .fst x)) (x ↦ g (w .fst .snd x)) (w .snd) a)

def pullback_gap_inverse (A B C D : Type) (f : B → D) (g : C → D) (h : A → TypePullback B C D f g)
  : PullbackOfPostcomp A B C D f g
  ≔ ((x ↦ h x .fst .fst, x ↦ h x .fst .snd),
     funext A (_ ↦ D) (x ↦ f (h x .fst .fst)) (x ↦ g (h x .fst .snd)) (x ↦ h x .snd))

def pullback_universal_property (A B C D : Type) (f : B → D) (g : C → D)
  : BookIsEquiv (PullbackOfPostcomp A B C D f g) (A → TypePullback B C D f g) (pullback_gap_map A B C D f g)
  ≔ book_quasi_inverse_equiv (PullbackOfPostcomp A B C D f g) (A → TypePullback B C D f g)
      (pullback_gap_map A B C D f g) (pullback_gap_inverse A B C D f g)
      (w ↦ refl ((t ↦ (w .fst, t)) : Id (A → D) (x ↦ f (w .fst .fst x)) (x ↦ g (w .fst .snd x)) → PullbackOfPostcomp A B C D f g)
             (funext_eta A (_ ↦ D) (x ↦ f (w .fst .fst x)) (x ↦ g (w .fst .snd x)) (w .snd)))
      (h ↦ funext A (_ ↦ TypePullback B C D f g) (pullback_gap_map A B C D f g (pullback_gap_inverse A B C D f g h)) h
        (a ↦ refl ((t ↦ (h a .fst, t)) : Id D (f (h a .fst .fst)) (g (h a .fst .snd)) → TypePullback B C D f g)
               (inverse (Id D (f (h a .fst .fst)) (g (h a .fst .snd))) (h a .snd)
                 (happly A (_ ↦ D) (x ↦ f (h x .fst .fst)) (x ↦ g (h x .fst .snd))
                   (funext A (_ ↦ D) (x ↦ f (h x .fst .fst)) (x ↦ g (h x .fst .snd)) (x ↦ h x .snd)) a)
                 (funext_beta A (_ ↦ D) (x ↦ f (h x .fst .fst)) (x ↦ g (h x .fst .snd)) (x ↦ h x .snd) a))))
      .equiv

{` "we will say that we have a pullback diagram ... to indicate that we have
   an element in (A → B) ×_{(A → D)} (A → C) such that the resulting map
   A → B ×_D C is an equivalence". `}
def IsPullbackSquare (A B C D : Type) (f : B → D) (g : C → D) (w : PullbackOfPostcomp A B C D f g) : Type
  ≔ BookIsEquiv A (TypePullback B C D f g) (pullback_gap_map A B C D f g w)

{` The pullback itself, with its projections and the square of
   def:pullback, is a pullback diagram (the gap map is homotopic to the
   identity). `}
def pullback_canonical_square (B C D : Type) (f : B → D) (g : C → D)
  : PullbackOfPostcomp (TypePullback B C D f g) B C D f g
  ≔ ((pullback_proj_left B C D f g, pullback_proj_right B C D f g), pullback_square_commutes B C D f g)

def pullback_canonical_is_pullback (B C D : Type) (f : B → D) (g : C → D)
  : IsPullbackSquare (TypePullback B C D f g) B C D f g (pullback_canonical_square B C D f g)
  ≔ let P ≔ TypePullback B C D f g in
    let gap ≔ pullback_gap_map P B C D f g (pullback_canonical_square B C D f g) in
    let back : (t : P) → Id P (gap t) t
      ≔ t ↦ refl ((w ↦ (t .fst, w)) : Id D (f (t .fst .fst)) (g (t .fst .snd)) → P)
              (inverse (Id D (f (t .fst .fst)) (g (t .fst .snd))) (t .snd)
                (happly P (_ ↦ D) (s ↦ f (s .fst .fst)) (s ↦ g (s .fst .snd))
                  (funext P (_ ↦ D) (s ↦ f (s .fst .fst)) (s ↦ g (s .fst .snd)) (s ↦ s .snd)) t)
                (funext_beta P (_ ↦ D) (s ↦ f (s .fst .fst)) (s ↦ g (s .fst .snd)) (s ↦ s .snd) t)) in
    book_quasi_inverse_equiv P P gap (t ↦ t) back back .equiv

{` The example after xca:univpropofpullback: for d : 1 → D the constant map
   at d and g : C → D, 1 ×_D C ≃ g⁻¹(d) ≡ Σ_{c:C} d = g(c). (The book
   writes Σ_{b:B} d = g(b); the variable ranges over C.) `}
def pullback_point_fiber_eta (C D : Type) (d : D) (g : C → D) (u : Unit) (c : C) (p : Id D d (g c))
  : Id (TypePullback Unit C D (_ ↦ d) g) ((star., c), p) ((u, c), p)
  ≔ match u [ star. ↦ refl (((star., c), p) : TypePullback Unit C D (_ ↦ d) g) ]

def pullback_point_fiber_equiv (C D : Type) (d : D) (g : C → D)
  : BookEquiv (TypePullback Unit C D (_ ↦ d) g) (BookFiber C D g d)
  ≔ book_quasi_inverse_equiv (TypePullback Unit C D (_ ↦ d) g) (BookFiber C D g d)
      (t ↦ (t .fst .snd, t .snd)) (s ↦ ((star., s .fst), s .snd))
      (t ↦ pullback_point_fiber_eta C D d g (t .fst .fst) (t .fst .snd) (t .snd))
      (s ↦ refl s)

{` Footnote: the preimage is a pullback, via the square g⁻¹(d) → C (first
   projection), g⁻¹(d) → 1, filled by the identifications d = g(c). `}
def fiber_pullback_square (C D : Type) (d : D) (g : C → D)
  : PullbackOfPostcomp (BookFiber C D g d) Unit C D (_ ↦ d) g
  ≔ ((_ ↦ star., s ↦ s .fst), funext (BookFiber C D g d) (_ ↦ D) (_ ↦ d) (s ↦ g (s .fst)) (s ↦ s .snd))

def fiber_is_pullback (C D : Type) (d : D) (g : C → D)
  : IsPullbackSquare (BookFiber C D g d) Unit C D (_ ↦ d) g (fiber_pullback_square C D d g)
  ≔ let F ≔ BookFiber C D g d in
    let P ≔ TypePullback Unit C D (_ ↦ d) g in
    let hp : (s : F) → Id D d (g (s .fst)) ≔ s ↦ s .snd in
    let beta : (s : F) → Id (Id D d (g (s .fst))) (s .snd)
                 (happly F (_ ↦ D) (_ ↦ d) (s' ↦ g (s' .fst)) (funext F (_ ↦ D) (_ ↦ d) (s' ↦ g (s' .fst)) hp) s)
      ≔ funext_beta F (_ ↦ D) (_ ↦ d) (s' ↦ g (s' .fst)) hp in
    book_quasi_inverse_equiv F P (pullback_gap_map F Unit C D (_ ↦ d) g (fiber_pullback_square C D d g))
      (t ↦ (t .fst .snd, t .snd))
      (s ↦ refl ((w ↦ (s .fst, w)) : Id D d (g (s .fst)) → F)
             (inverse (Id D d (g (s .fst))) (s .snd)
               (happly F (_ ↦ D) (_ ↦ d) (s' ↦ g (s' .fst)) (funext F (_ ↦ D) (_ ↦ d) (s' ↦ g (s' .fst)) hp) s)
               (beta s)))
      (t ↦ concat P
         ((star., t .fst .snd),
          happly F (_ ↦ D) (_ ↦ d) (s' ↦ g (s' .fst)) (funext F (_ ↦ D) (_ ↦ d) (s' ↦ g (s' .fst)) hp)
            (t .fst .snd, t .snd))
         ((star., t .fst .snd), t .snd) t
         (refl ((w ↦ ((star., t .fst .snd), w)) : Id D d (g (t .fst .snd)) → P)
           (inverse (Id D d (g (t .fst .snd))) (t .snd)
             (happly F (_ ↦ D) (_ ↦ d) (s' ↦ g (s' .fst)) (funext F (_ ↦ D) (_ ↦ d) (s' ↦ g (s' .fst)) hp)
               (t .fst .snd, t .snd))
             (beta (t .fst .snd, t .snd))))
         (pullback_point_fiber_eta C D d g (t .fst .fst) (t .fst .snd) (t .snd)))
      .equiv

{` Litmus: the pullback of id and not on Bool contains (true, false), the
   projections compute, and the gap map of the constant square from Unit
   evaluates to that point. `}
def pullback_litmus_point : TypePullback Bool Bool Bool (x ↦ x) bool_not
  ≔ ((true., false.), refl (true. : Bool))

def pullback_litmus_projections
  : Product (Id Bool (pullback_proj_left Bool Bool Bool (x ↦ x) bool_not pullback_litmus_point) true.)
      (Id Bool (pullback_proj_right Bool Bool Bool (x ↦ x) bool_not pullback_litmus_point) false.)
  ≔ (refl (true. : Bool), refl (false. : Bool))

def pullback_litmus_square : PullbackOfPostcomp Unit Bool Bool Bool (x ↦ x) bool_not
  ≔ ((_ ↦ true., _ ↦ false.), refl ((_ ↦ true.) : Unit → Bool))

def pullback_litmus_gap
  : Id (TypePullback Bool Bool Bool (x ↦ x) bool_not)
      (pullback_gap_map Unit Bool Bool Bool (x ↦ x) bool_not pullback_litmus_square star.) pullback_litmus_point
  ≔ refl pullback_litmus_point

def pullback_litmus_fiber
  : Id Bool (pullback_point_fiber_equiv Bool Bool true. bool_not .map ((star., false.), refl (true. : Bool)) .fst) false.
  ≔ refl (false. : Bool)
