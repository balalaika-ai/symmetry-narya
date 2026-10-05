export "174-cyclic-permutations"

def unit_decidable_equality : DecidableEquality Unit ≔ x y ↦ inl. (unit_prop x y)

def option_decidable_equality (A : Type) (d : DecidableEquality A) : DecidableEquality (Sum A Unit)
  ≔ sum_decidable_equality A Unit d unit_decidable_equality

def option_point (A : Type) : Sum A Unit ≔ inr. star.

def inl_injective (A : Type) (x y : A) (p : Id (Sum A Unit) (inl. x) (inl. y)) : Id A x y
  ≔ sum_encode A Unit (inl. x) (inl. y) p

def option_value_inl (A : Type) (u : Sum A Unit) (h : Id (Sum A Unit) u (inr. star.) → Empty)
  : Id (Sum A Unit) (inl. (without_last_to A u h)) u
  ≔ match u [
  | inl. a ↦ refl (inl. a : Sum A Unit)
  | inr. s ↦ absurd (Id (Sum A Unit) (inl. (without_last_to A (inr. s) h)) (inr. s))
      (h (inr. (unit_prop s star.))) ]

{` A permutation of A + 1 fixing the added point restricts to A. `}
def fixed_point_avoid (A : Type) (t : Equiv (Sum A Unit) (Sum A Unit))
  (fix : Id (Sum A Unit) (t .map (inr. star.)) (inr. star.)) (a : A)
  : Id (Sum A Unit) (t .map (inl. a)) (inr. star.) → Empty
  ≔ p ↦ sum_encode A Unit (inl. a) (inr. star.)
      (equivalence_injective (Sum A Unit) (Sum A Unit) t (inl. a) (inr. star.)
        (concat (Sum A Unit) (t .map (inl. a)) (inr. star.) (t .map (inr. star.)) p
          (inverse (Sum A Unit) (t .map (inr. star.)) (inr. star.) fix)))

def fixed_restriction_map (A : Type) (t : Equiv (Sum A Unit) (Sum A Unit))
  (fix : Id (Sum A Unit) (t .map (inr. star.)) (inr. star.)) (a : A) : A
  ≔ without_last_to A (t .map (inl. a)) (fixed_point_avoid A t fix a)

def fixed_restriction_beta (A : Type) (t : Equiv (Sum A Unit) (Sum A Unit))
  (fix : Id (Sum A Unit) (t .map (inr. star.)) (inr. star.)) (a : A)
  : Id (Sum A Unit) (inl. (fixed_restriction_map A t fix a)) (t .map (inl. a))
  ≔ option_value_inl A (t .map (inl. a)) (fixed_point_avoid A t fix a)

def inverse_fixes_point (A : Type) (t : Equiv (Sum A Unit) (Sum A Unit))
  (fix : Id (Sum A Unit) (t .map (inr. star.)) (inr. star.))
  : Id (Sum A Unit) (equiv_inverse_map (Sum A Unit) (Sum A Unit) t (inr. star.)) (inr. star.)
  ≔ let g ≔ equiv_inverse_map (Sum A Unit) (Sum A Unit) t in
    concat (Sum A Unit) (g (inr. star.)) (g (t .map (inr. star.))) (inr. star.)
      (refl g (inverse (Sum A Unit) (t .map (inr. star.)) (inr. star.) fix))
      (equiv_retraction (Sum A Unit) (Sum A Unit) t (inr. star.))

def fixed_restriction_roundtrip (A : Type) (t s : Equiv (Sum A Unit) (Sum A Unit))
  (ft : Id (Sum A Unit) (t .map (inr. star.)) (inr. star.))
  (fs : Id (Sum A Unit) (s .map (inr. star.)) (inr. star.))
  (inv : (x : Sum A Unit) → Id (Sum A Unit) (s .map (t .map x)) x) (a : A)
  : Id A (fixed_restriction_map A s fs (fixed_restriction_map A t ft a)) a
  ≔ inl_injective A (fixed_restriction_map A s fs (fixed_restriction_map A t ft a)) a (calc
      (inl. (fixed_restriction_map A s fs (fixed_restriction_map A t ft a)) : Sum A Unit)
      = s .map (inl. (fixed_restriction_map A t ft a))
        by fixed_restriction_beta A s fs (fixed_restriction_map A t ft a)
      = s .map (t .map (inl. a)) by refl (s .map) (fixed_restriction_beta A t ft a)
      = inl. a by inv (inl. a) ∎)

def fixed_restriction (A : Type) (t : Equiv (Sum A Unit) (Sum A Unit))
  (fix : Id (Sum A Unit) (t .map (inr. star.)) (inr. star.)) : Equiv A A
  ≔ let g ≔ canonical_inverse_equiv (Sum A Unit) (Sum A Unit) t in
    let fg ≔ inverse_fixes_point A t fix in
    quasi_inverse_equiv A A (fixed_restriction_map A t fix) (fixed_restriction_map A g fg)
      (fixed_restriction_roundtrip A t g fix fg (equiv_retraction (Sum A Unit) (Sum A Unit) t))
      (fixed_restriction_roundtrip A g t fg fix (equiv_counit (Sum A Unit) (Sum A Unit) t))

def option_extension (A : Type) (r : Equiv A A) : Equiv (Sum A Unit) (Sum A Unit)
  ≔ sum_equiv A Unit A Unit r (identity_equiv Unit)

{` eq:type-factorial for any decidable set A:
   Aut(A + 1) ≃ (A + 1) × Aut(A), sending s to (s(pt), restriction of (pt s(pt)) s). `}
def option_swap_normalize (A : Type) (d : DecidableEquality A) (s : Equiv (Sum A Unit) (Sum A Unit))
  : Equiv (Sum A Unit) (Sum A Unit)
  ≔ compose_equiv (Sum A Unit) (Sum A Unit) (Sum A Unit) s
      (transposition_equiv (Sum A Unit) (option_decidable_equality A d) (inr. star.) (s .map (inr. star.)))

def option_swap_normalize_fix (A : Type) (d : DecidableEquality A) (s : Equiv (Sum A Unit) (Sum A Unit))
  : Id (Sum A Unit) (option_swap_normalize A d s .map (inr. star.)) (inr. star.)
  ≔ transposition_right (Sum A Unit) (option_decidable_equality A d) (inr. star.) (s .map (inr. star.))

def permutation_option_to (A : Type) (d : DecidableEquality A) (s : Equiv (Sum A Unit) (Sum A Unit))
  : Product (Sum A Unit) (Equiv A A)
  ≔ (s .map (inr. star.),
      fixed_restriction A (option_swap_normalize A d s) (option_swap_normalize_fix A d s))

def permutation_option_from (A : Type) (d : DecidableEquality A) (u : Product (Sum A Unit) (Equiv A A))
  : Equiv (Sum A Unit) (Sum A Unit)
  ≔ compose_equiv (Sum A Unit) (Sum A Unit) (Sum A Unit) (option_extension A (u .snd))
      (transposition_equiv (Sum A Unit) (option_decidable_equality A d) (inr. star.) (u .fst))

{` The normalized permutation agrees with its restriction extended by the point. `}
def fixed_restriction_extension (A : Type) (t : Equiv (Sum A Unit) (Sum A Unit))
  (fix : Id (Sum A Unit) (t .map (inr. star.)) (inr. star.)) (x : Sum A Unit)
  : Id (Sum A Unit) (option_extension A (fixed_restriction A t fix) .map x) (t .map x)
  ≔ match x [
  | inl. a ↦ fixed_restriction_beta A t fix a
  | inr. u ↦ match u [ star. ↦ inverse (Sum A Unit) (t .map (inr. star.)) (inr. star.) fix ] ]

def permutation_option_eta (A : Type) (d : DecidableEquality A) (s : Equiv (Sum A Unit) (Sum A Unit))
  : Id (Equiv (Sum A Unit) (Sum A Unit)) (permutation_option_from A d (permutation_option_to A d s)) s
  ≔ let dB ≔ option_decidable_equality A d in
    let sw ≔ transposition (Sum A Unit) dB (inr. star.) (s .map (inr. star.)) in
    let t ≔ option_swap_normalize A d s in
    equiv_homotopy (Sum A Unit) (Sum A Unit) (permutation_option_from A d (permutation_option_to A d s)) s
      (x ↦ calc
        sw (option_extension A (fixed_restriction A t (option_swap_normalize_fix A d s)) .map x)
        = sw (t .map x) by refl sw (fixed_restriction_extension A t (option_swap_normalize_fix A d s) x)
        = s .map x by transposition_involutive (Sum A Unit) dB (inr. star.) (s .map (inr. star.)) (s .map x) ∎)

def permutation_option_epsilon (A : Type) (d : DecidableEquality A) (u : Product (Sum A Unit) (Equiv A A))
  : Id (Product (Sum A Unit) (Equiv A A)) (permutation_option_to A d (permutation_option_from A d u)) u
  ≔ let dB ≔ option_decidable_equality A d in
    let s ≔ permutation_option_from A d u in
    let first : Id (Sum A Unit) (s .map (inr. star.)) (u .fst)
      ≔ transposition_left (Sum A Unit) dB (inr. star.) (u .fst) in
    let t ≔ option_swap_normalize A d s in
    let tfix ≔ option_swap_normalize_fix A d s in
    (first, equiv_homotopy A A (fixed_restriction A t tfix) (u .snd)
      (a ↦ inl_injective A (fixed_restriction_map A t tfix a) (u .snd .map a) (calc
        (inl. (fixed_restriction_map A t tfix a) : Sum A Unit) = t .map (inl. a) by fixed_restriction_beta A t tfix a
        = transposition (Sum A Unit) dB (inr. star.) (u .fst) (s .map (inl. a))
          by refl ((b ↦ transposition (Sum A Unit) dB (inr. star.) b (s .map (inl. a))) : Sum A Unit → Sum A Unit) first
        = inl. (u .snd .map a)
          by transposition_involutive (Sum A Unit) dB (inr. star.) (u .fst) (inl. (u .snd .map a)) ∎)))

def permutation_option_equiv (A : Type) (d : DecidableEquality A)
  : Equiv (Equiv (Sum A Unit) (Sum A Unit)) (Product (Sum A Unit) (Equiv A A))
  ≔ quasi_inverse_equiv (Equiv (Sum A Unit) (Sum A Unit)) (Product (Sum A Unit) (Equiv A A))
      (permutation_option_to A d) (permutation_option_from A d)
      (permutation_option_eta A d) (permutation_option_epsilon A d)

{` Aut(Fin 0) ≃ Fin 1. `}
def empty_automorphisms_equiv : Equiv (Equiv Empty Empty) (Fin (suc. zero.))
  ≔ quasi_inverse_equiv (Equiv Empty Empty) (Fin (suc. zero.)) (_ ↦ inr. star.) (_ ↦ identity_equiv Empty)
      (e ↦ equiv_homotopy Empty Empty (identity_equiv Empty) e (x ↦ match x []))
      [ inl. x ↦ match x [] | inr. u ↦ inr. (unit_prop star. u) ]

{` fact, as in sec:natural-numbers: fact(0) = 1, fact(m+1) = (m+1) fact(m). `}
def factorial (n : Nat) : Nat ≔ match n [ zero. ↦ suc. zero. | suc. k ↦ mul (suc. k) (factorial k) ]

def fin_automorphisms_equiv (n : Nat) : Equiv (Equiv (Fin n) (Fin n)) (Fin (factorial n))
  ≔ match n [
  | zero. ↦ empty_automorphisms_equiv
  | suc. k ↦ compose_equiv (Equiv (Fin (suc. k)) (Fin (suc. k))) (Product (Fin (suc. k)) (Equiv (Fin k) (Fin k)))
      (Fin (factorial (suc. k)))
      (permutation_option_equiv (Fin k) (fin_decidable_equality k))
      (compose_equiv (Product (Fin (suc. k)) (Equiv (Fin k) (Fin k))) (Product (Fin (suc. k)) (Fin (factorial k)))
        (Fin (factorial (suc. k)))
        (product_equiv (Fin (suc. k)) (Equiv (Fin k) (Fin k)) (Fin (suc. k)) (Fin (factorial k))
          (identity_equiv (Fin (suc. k))) (fin_automorphisms_equiv k))
        (fin_product_equiv (suc. k) (factorial k))) ]

def automorphisms_finite (A : Type) (ha : IsFinite A) : IsFinite (Equiv A A)
  ≔ mere_rec (Σ Nat (n ↦ Id Type A (Fin n))) (IsFinite (Equiv A A)) (isfinite_prop (Equiv A A))
      (p ↦ mere (Σ Nat (n ↦ Id Type (Equiv A A) (Fin n))) (factorial (p .fst),
        concat Type (Equiv A A) (Equiv (Fin (p .fst)) (Fin (p .fst))) (Fin (factorial (p .fst)))
          (refl ((X ↦ Equiv X X) : Type → Type) (p .snd))
          (ua (Equiv (Fin (p .fst)) (Fin (p .fst))) (Fin (factorial (p .fst))) (fin_automorphisms_equiv (p .fst)))))
      ha

{` xca:factorial: a finite set of cardinality n has n! permutations.  The
   finiteness witness of the automorphism type is arbitrary. `}
def automorphisms_cardinality (A : Type) (ha : IsFinite A) (h : IsFinite (Equiv A A))
  : Id Nat (cardinality (Equiv A A) h) (factorial (cardinality A ha))
  ≔ let n ≔ cardinality A ha in
    mere_rec (Id Type A (Fin n)) (Id Nat (cardinality (Equiv A A) h) (factorial n))
      (nat_set (cardinality (Equiv A A) h) (factorial n))
      (p ↦ cardinality_from_path (Equiv A A) h (factorial n)
        (concat Type (Equiv A A) (Equiv (Fin n) (Fin n)) (Fin (factorial n))
          (refl ((X ↦ Equiv X X) : Type → Type) p)
          (ua (Equiv (Fin n) (Fin n)) (Fin (factorial n)) (fin_automorphisms_equiv n))))
      (cardinality_spec A ha)

{` The same count for Aut(A) as self-identifications A = A in the universe. `}
def universe_loops_finite (A : Type) (ha : IsFinite A) : IsFinite (Id Type A A)
  ≔ finite_of_equiv (Id Type A A) (Equiv A A) (transport_univalence_equiv A A) (automorphisms_finite A ha)

def universe_loops_cardinality (A : Type) (ha : IsFinite A) (h : IsFinite (Id Type A A))
  : Id Nat (cardinality (Id Type A A) h) (factorial (cardinality A ha))
  ≔ concat Nat (cardinality (Id Type A A) h) (cardinality (Equiv A A) (automorphisms_finite A ha))
      (factorial (cardinality A ha))
      (cardinality_equiv (Id Type A A) (Equiv A A) (transport_univalence_equiv A A) h (automorphisms_finite A ha))
      (automorphisms_cardinality A ha (automorphisms_finite A ha))

def fin_zero_loops_equiv : Equiv (Id Type (Fin zero.) (Fin zero.)) (Fin (suc. zero.))
  ≔ compose_equiv (Id Type (Fin zero.) (Fin zero.)) (Equiv Empty Empty) (Fin (suc. zero.))
      (transport_univalence_equiv (Fin zero.) (Fin zero.)) empty_automorphisms_equiv
