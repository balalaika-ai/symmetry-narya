export "150-paths-over-and-pairs"

{` xca:2-out-of-3, for e : hf = g as an identification of functions.
   Each case uses the other two equivalences and returns the third. `}
def two_out_of_three_composite (A B C : Type) (f : A → B) (g : A → C) (h : B → C)
  (e : Id (A → C) (compose A B C h f) g) (hf : isEquiv A B f) (hh : isEquiv B C h)
  : isEquiv A C g
  ≔ transport (A → C) (isEquiv A C) (compose A B C h f) g e
      (compose_equiv A B C (f, hf) (h, hh) .equiv)

def two_out_of_three_right (A B C : Type) (f : A → B) (g : A → C) (h : B → C)
  (e : Id (A → C) (compose A B C h f) g) (hf : isEquiv A B f) (hg : isEquiv A C g)
  : isEquiv B C h
  ≔ let finv ≔ equiv_inverse_map A B (f, hf) in
    equiv_change_map B C (compose_equiv B A C (canonical_inverse_equiv A B (f, hf)) (g, hg)) h
      (b ↦ concat C (g (finv b)) (h (f (finv b))) (h b)
        (inverse C (h (f (finv b))) (g (finv b))
          (happly A (_ ↦ C) (compose A B C h f) g e (finv b)))
        (refl h (equiv_counit A B (f, hf) b))) .equiv

def two_out_of_three_left (A B C : Type) (f : A → B) (g : A → C) (h : B → C)
  (e : Id (A → C) (compose A B C h f) g) (hg : isEquiv A C g) (hh : isEquiv B C h)
  : isEquiv A B f
  ≔ let hinv ≔ equiv_inverse_map B C (h, hh) in
    equiv_change_map A B (compose_equiv A C B (g, hg) (canonical_inverse_equiv B C (h, hh))) f
      (a ↦ concat B (hinv (g a)) (hinv (h (f a))) (f a)
        (refl hinv (inverse C (h (f a)) (g a) (happly A (_ ↦ C) (compose A B C h f) g e a)))
        (equiv_retraction B C (h, hh) (f a))) .equiv

{` The same three cases with the book's notion of equivalence. `}
def book_two_out_of_three_composite (A B C : Type) (f : A → B) (g : A → C) (h : B → C)
  (e : Id (A → C) (compose A B C h f) g) (hf : BookIsEquiv A B f) (hh : BookIsEquiv B C h)
  : BookIsEquiv A C g
  ≔ book_equivalence A C (g, two_out_of_three_composite A B C f g h e
      (native_equivalence A B (f, hf) .equiv) (native_equivalence B C (h, hh) .equiv)) .equiv

def book_two_out_of_three_right (A B C : Type) (f : A → B) (g : A → C) (h : B → C)
  (e : Id (A → C) (compose A B C h f) g) (hf : BookIsEquiv A B f) (hg : BookIsEquiv A C g)
  : BookIsEquiv B C h
  ≔ book_equivalence B C (h, two_out_of_three_right A B C f g h e
      (native_equivalence A B (f, hf) .equiv) (native_equivalence A C (g, hg) .equiv)) .equiv

def book_two_out_of_three_left (A B C : Type) (f : A → B) (g : A → C) (h : B → C)
  (e : Id (A → C) (compose A B C h f) g) (hg : BookIsEquiv A C g) (hh : BookIsEquiv B C h)
  : BookIsEquiv A B f
  ≔ book_equivalence A B (f, two_out_of_three_left A B C f g h e
      (native_equivalence A C (g, hg) .equiv) (native_equivalence B C (h, hh) .equiv)) .equiv

{` Induction on paths ending at a fixed point, via the contractible
   type of such paths. `}
def singleton_to_ind (A : Type) (a : A) (P : Σ A (y ↦ Id A y a) → Type)
  (d : P (a, refl a)) (s : Σ A (y ↦ Id A y a)) : P s
  ≔ transport (Σ A (y ↦ Id A y a)) P (a, refl a) s
      (inverse (Σ A (y ↦ Id A y a)) s (a, refl a) (path_to_contractible A a .contract s)) d

{` xca:fib-of-comp, with the book's fibers (gf)⁻¹(z) = Σ x, z = g(f(x)). `}
def CompositeFiberSplit (X Y Z : Type) (f : X → Y) (g : Y → Z) (z : Z) : Type
  ≔ Σ (BookFiber Y Z g z) (w ↦ BookFiber X Y f (w .fst))

def composite_fiber_to (X Y Z : Type) (f : X → Y) (g : Y → Z) (z : Z)
  (t : BookFiber X Z (compose X Y Z g f) z) : CompositeFiberSplit X Y Z f g z
  ≔ ((f (t .fst), t .snd), (t .fst, refl (f (t .fst))))

def composite_fiber_from (X Y Z : Type) (f : X → Y) (g : Y → Z) (z : Z)
  (s : CompositeFiberSplit X Y Z f g z) : BookFiber X Z (compose X Y Z g f) z
  ≔ (s .snd .fst, concat Z z (g (s .fst .fst)) (g (f (s .snd .fst)))
      (s .fst .snd) (refl g (s .snd .snd)))

def composite_fiber_from_to (X Y Z : Type) (f : X → Y) (g : Y → Z) (z : Z)
  (t : BookFiber X Z (compose X Y Z g f) z)
  : Id (BookFiber X Z (compose X Y Z g f) z)
      (composite_fiber_from X Y Z f g z (composite_fiber_to X Y Z f g z t)) t
  ≔ (refl (t .fst), concat_p1 Z z (g (f (t .fst))) (t .snd))

def composite_fiber_to_from (X Y Z : Type) (f : X → Y) (g : Y → Z) (z : Z)
  (s : CompositeFiberSplit X Y Z f g z)
  : Id (CompositeFiberSplit X Y Z f g z)
      (composite_fiber_to X Y Z f g z (composite_fiber_from X Y Z f g z s)) s
  ≔ let x ≔ s .snd .fst in
    singleton_to_ind Y (f x)
      (r ↦ (p : Id Z z (g (r .fst))) → Id (CompositeFiberSplit X Y Z f g z)
        (composite_fiber_to X Y Z f g z (composite_fiber_from X Y Z f g z ((r .fst, p), (x, r .snd))))
        ((r .fst, p), (x, r .snd)))
      (p ↦ ((refl (f x), concat_p1 Z z (g (f x)) p), refl (x, refl (f x))))
      (s .fst .fst, s .snd .snd) (s .fst .snd)

def composite_fiber_equiv (X Y Z : Type) (f : X → Y) (g : Y → Z) (z : Z)
  : Equiv (BookFiber X Z (compose X Y Z g f) z) (CompositeFiberSplit X Y Z f g z)
  ≔ quasi_inverse_equiv (BookFiber X Z (compose X Y Z g f) z) (CompositeFiberSplit X Y Z f g z)
      (composite_fiber_to X Y Z f g z) (composite_fiber_from X Y Z f g z)
      (composite_fiber_from_to X Y Z f g z) (composite_fiber_to_from X Y Z f g z)

{` xca:section-above-f. The equivalence has the evident map
   s |-> (z |-> (f z, s z), refl f). `}
def SectionAbove (X Z : Type) (Y : X → Type) (f : Z → X) : Type
  ≔ Σ (Z → Σ X Y) (g ↦ Id (Z → X) f (compose Z (Σ X Y) X (t ↦ t .fst) g))

def section_above_map (X Z : Type) (Y : X → Type) (f : Z → X) (s : (z : Z) → Y (f z))
  : SectionAbove X Z Y f
  ≔ (z ↦ (f z, s z), refl f)

def section_above_expand (X Z : Type) (Y : X → Type) (f : Z → X)
  : Equiv ((z : Z) → Y (f z))
      (Σ (Z → X) (h ↦ Σ (Id (Z → X) f h) (_ ↦ (z : Z) → Y (h z))))
  ≔ quasi_inverse_equiv ((z : Z) → Y (f z))
      (Σ (Z → X) (h ↦ Σ (Id (Z → X) f h) (_ ↦ (z : Z) → Y (h z))))
      (s ↦ (f, (refl f, s)))
      (t ↦ contract_away_map (Z → X) f (h _ ↦ (z : Z) → Y (h z)) (t .fst) (t .snd .fst) (t .snd .snd))
      (contract_away_beta (Z → X) f (h _ ↦ (z : Z) → Y (h z)))
      (t ↦ contract_away_eta (Z → X) f (h _ ↦ (z : Z) → Y (h z)) (t .fst) (t .snd .fst) (t .snd .snd))

def section_above_regroup (X Z : Type) (Y : X → Type) (f : Z → X)
  : Equiv (Σ (Z → X) (h ↦ Σ (Id (Z → X) f h) (_ ↦ (z : Z) → Y (h z)))) (SectionAbove X Z Y f)
  ≔ quasi_inverse_equiv (Σ (Z → X) (h ↦ Σ (Id (Z → X) f h) (_ ↦ (z : Z) → Y (h z))))
      (SectionAbove X Z Y f)
      (t ↦ (z ↦ (t .fst z, t .snd .snd z), t .snd .fst))
      (u ↦ (z ↦ u .fst z .fst, (u .snd, z ↦ u .fst z .snd)))
      (t ↦ refl t) (u ↦ refl u)

def section_above_equiv (X Z : Type) (Y : X → Type) (f : Z → X)
  : Equiv ((z : Z) → Y (f z)) (SectionAbove X Z Y f)
  ≔ compose_equiv ((z : Z) → Y (f z))
      (Σ (Z → X) (h ↦ Σ (Id (Z → X) f h) (_ ↦ (z : Z) → Y (h z)))) (SectionAbove X Z Y f)
      (section_above_expand X Z Y f) (section_above_regroup X Z Y f)

def section_above_equiv_map (X Z : Type) (Y : X → Type) (f : Z → X) (s : (z : Z) → Y (f z))
  : Id (SectionAbove X Z Y f) (section_above_equiv X Z Y f .map s) (section_above_map X Z Y f s)
  ≔ refl (section_above_map X Z Y f s)
