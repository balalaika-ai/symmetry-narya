export "160-logic-notations"

def pi_family_equiv (X : Type) (B C : X → Type) (e : (x : X) → Equiv (B x) (C x))
  : Equiv ((x : X) → B x) ((x : X) → C x)
  ≔ quasi_inverse_equiv ((x : X) → B x) ((x : X) → C x)
      (s x ↦ e x .map (s x)) (s x ↦ equiv_inverse_map (B x) (C x) (e x) (s x))
      (s ↦ funext X B (x ↦ equiv_inverse_map (B x) (C x) (e x) (e x .map (s x))) s
        (x ↦ equiv_retraction (B x) (C x) (e x) (s x)))
      (s ↦ funext X C (x ↦ e x .map (equiv_inverse_map (B x) (C x) (e x) (s x))) s
        (x ↦ equiv_counit (B x) (C x) (e x) (s x)))

{` The type displayed in xca:subtype-univ-prop, with its triangle. `}
def SubtypeFactorizations (X T : Type) (f : X → T) (P : Subtypes T) : Type
  ≔ Σ (X → SubtypeCarrier T P)
      (g ↦ Id (X → T) f (compose X (SubtypeCarrier T P) T (u ↦ u .fst) g))

def subtype_factorization_equiv (X T : Type) (f : X → T) (P : Subtypes T)
  : Equiv (SubtypeFactorizations X T f P) ((x : X) → P (f x) .fst)
  ≔ let S ≔ SubtypeCarrier T P in
    let H ≔ Σ (X → S) (g ↦ (x : X) → Id T (f x) (g x .fst)) in
    let F ≔ (x : X) → BookFiber S T (u ↦ u .fst) (f x) in
    compose_equiv (SubtypeFactorizations X T f P) H ((x : X) → P (f x) .fst)
      (family_equiv (X → S)
        (g ↦ Id (X → T) f (compose X S T (u ↦ u .fst) g))
        (g ↦ (x : X) → Id T (f x) (g x .fst))
        (g ↦ function_extensionality X (_ ↦ T) f (x ↦ g x .fst)))
      (compose_equiv H F ((x : X) → P (f x) .fst)
        (canonical_inverse_equiv F H (choice_equiv X (_ ↦ S) (x u ↦ Id T (f x) (u .fst))))
        (pi_family_equiv X (x ↦ BookFiber S T (u ↦ u .fst) (f x)) (x ↦ P (f x) .fst)
          (x ↦ native_equivalence (BookFiber S T (u ↦ u .fst) (f x)) (P (f x) .fst)
            (book_projection_fiber_equiv T (t ↦ P t .fst) (f x)))))

{` xca:subtype-univ-prop: the universal property of subtypes, as an
   equivalence of the two propositions. `}
def subtype_universal_property (X T : Type) (f : X → T) (P : Subtypes T)
  : Equiv ((x : X) → P (f x) .fst) (BookIsContr (SubtypeFactorizations X T f P))
  ≔ let G ≔ (x : X) → P (f x) .fst in
    let e ≔ subtype_factorization_equiv X T f P in
    let hG : isProp G ≔ pi_prop X (x ↦ P (f x) .fst) (x ↦ P (f x) .snd) in
    iff_equiv G (BookIsContr (SubtypeFactorizations X T f P))
      hG (book_iscontr_isprop (SubtypeFactorizations X T f P))
      (s ↦ book_contractibility_equiv G (SubtypeFactorizations X T f P)
        (canonical_inverse_equiv (SubtypeFactorizations X T f P) G e) .map (s, t ↦ hG s t))
      (c ↦ e .map (c .center))

{` The content of rem:subtype-convention: over a point where the
   predicate holds, the fiber of the projection is contractible. `}
def subtype_point_fiber_contractible (T : Type) (P : Subtypes T) (t : T) (p : P t .fst)
  : BookIsContr (BookFiber (SubtypeCarrier T P) T (u ↦ u .fst) t)
  ≔ book_contractibility_equiv (P t .fst) (BookFiber (SubtypeCarrier T P) T (u ↦ u .fst) t)
      (canonical_inverse_equiv (BookFiber (SubtypeCarrier T P) T (u ↦ u .fst) t) (P t .fst)
        (native_equivalence (BookFiber (SubtypeCarrier T P) T (u ↦ u .fst) t) (P t .fst)
          (book_projection_fiber_equiv T (s ↦ P s .fst) t)))
      .map (p, q ↦ P t .snd p q)

{` def:decidable-set: every identity type is a decidable proposition. `}
def DecidableSet (A : Type) : Type
  ≔ (x y : A) → Product (isProp (Id A x y)) (Decidable (Id A x y))

def decidable_set_prop (A : Type) : isProp (DecidableSet A)
  ≔ pi_prop A (x ↦ (y : A) → Product (isProp (Id A x y)) (Decidable (Id A x y)))
      (x ↦ pi_prop A (y ↦ Product (isProp (Id A x y)) (Decidable (Id A x y)))
        (y ↦ sigma_prop (isProp (Id A x y)) (_ ↦ Decidable (Id A x y))
          (isprop_isprop (Id A x y)) (h ↦ decidability_prop (Id A x y) h)))

def decidable_set_is_set (A : Type) (h : DecidableSet A) : isSet A ≔ x y ↦ h x y .fst

def decidable_set_equality (A : Type) (h : DecidableSet A) : DecidableEquality A
  ≔ x y ↦ h x y .snd

{` The remark after def:decidable-set: every proposition is a decidable set. `}
def proposition_decidable_set (P : Type) (hP : isProp P) : DecidableSet P
  ≔ x y ↦ (prop_is_set P hP x y, inl. (hP x y))

{` thm:hedberg, via a weakly constant endomap of each identity type. `}
def decision_collapse (A : Type) (x y : A) (d : Decidable (Id A x y)) (p : Id A x y) : Id A x y
  ≔ match d [ inl. q ↦ q | inr. n ↦ absurd (Id A x y) (n p) ]

def decision_collapse_constant (A : Type) (x y : A) (d : Decidable (Id A x y)) (p q : Id A x y)
  : Id (Id A x y) (decision_collapse A x y d p) (decision_collapse A x y d q)
  ≔ match d [ inl. r ↦ refl r | inr. n ↦ absurd (Id (Id A x y) (decision_collapse A x y (inr. n) p)
      (decision_collapse A x y (inr. n) q)) (n p) ]

def path_collapse_decomposition (A : Type) (c : (x y : A) → Id A x y → Id A x y)
  (x y : A) (p : Id A x y)
  : Id (Id A x y) p (concat A x x y (inverse A x x (c x x (refl x))) (c x y p))
  ≔ J A x (y p ↦ Id (Id A x y) p (concat A x x y (inverse A x x (c x x (refl x))) (c x y p)))
      (inverse (Id A x x) (concat A x x x (inverse A x x (c x x (refl x))) (c x x (refl x))) (refl x)
        (concat_inverse_left A x x (c x x (refl x)))) y p

def collapsible_paths_set (A : Type) (c : (x y : A) → Id A x y → Id A x y)
  (w : (x y : A) (p q : Id A x y) → Id (Id A x y) (c x y p) (c x y q)) : isSet A
  ≔ x y p q ↦
    let r ≔ inverse A x x (c x x (refl x)) in
    concat (Id A x y) p (concat A x x y r (c x y p)) q (path_collapse_decomposition A c x y p)
      (concat (Id A x y) (concat A x x y r (c x y p)) (concat A x x y r (c x y q)) q
        (refl (concat A x x y r) (w x y p q))
        (inverse (Id A x y) q (concat A x x y r (c x y q)) (path_collapse_decomposition A c x y q)))

def hedberg (A : Type) (d : DecidableEquality A) : DecidableSet A
  ≔ let s ≔ collapsible_paths_set A (x y ↦ decision_collapse A x y (d x y))
      (x y ↦ decision_collapse_constant A x y (d x y)) in
    x y ↦ (s x y, d x y)
