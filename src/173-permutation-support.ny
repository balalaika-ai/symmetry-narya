export "172-power-bundle-degree"

{` def:support-permutation.  Permutations are self-equivalences. `}
def FixedPoint (A : Type) (s : Equiv A A) (a : A) : Type ≔ Id A (s .map a) a
def MovedPoint (A : Type) (s : Equiv A A) (a : A) : Type ≔ Not (Id A (s .map a) a)

def fixed_point_prop (A : Type) (hA : isSet A) (s : Equiv A A) (a : A) : isProp (FixedPoint A s a)
  ≔ hA (s .map a) a

def permutation_support (A : Type) (s : Equiv A A) : Subtypes A
  ≔ a ↦ (MovedPoint A s a, negation_prop (Id A (s .map a) a))

{` The remark after the definition: in a decidable set it is decidable
   whether a point is fixed or moved. `}
def fixed_or_moved (A : Type) (d : DecidableEquality A) (s : Equiv A A) (a : A)
  : Sum (FixedPoint A s a) (MovedPoint A s a)
  ≔ d (s .map a) a

def DisjointSupports (A : Type) (s t : Equiv A A) : Type
  ≔ (a : A) → MovedPoint A s a → MovedPoint A t a → Empty

def moved_image_moved (A : Type) (s : Equiv A A) (a : A) (m : MovedPoint A s a)
  : MovedPoint A s (s .map a)
  ≔ p ↦ m (equivalence_injective A A s (s .map a) a p)

def disjoint_moved_fixed (A : Type) (d : DecidableEquality A) (s t : Equiv A A)
  (disjoint : DisjointSupports A s t) (a : A) (m : MovedPoint A s a) : FixedPoint A t a
  ≔ match d (t .map a) a [
  | inl. q ↦ q
  | inr. n ↦ absurd (FixedPoint A t a) (disjoint a m n) ]

def disjoint_supports_symmetric (A : Type) (s t : Equiv A A) (disjoint : DisjointSupports A s t)
  : DisjointSupports A t s
  ≔ a mt ms ↦ disjoint a ms mt

def disjoint_supports_commute_at (A : Type) (d : DecidableEquality A) (s t : Equiv A A)
  (disjoint : DisjointSupports A s t) (a : A)
  : Id A (s .map (t .map a)) (t .map (s .map a))
  ≔ match d (s .map a) a [
  | inl. p ↦ match d (t .map a) a [
    | inl. q ↦ calc
        s .map (t .map a) = s .map a by refl (s .map) q
        = a by p
        = t .map a by inverse A (t .map a) a q
        = t .map (s .map a) by inverse A (t .map (s .map a)) (t .map a) (refl (t .map) p) ∎
    | inr. nq ↦ calc
        s .map (t .map a) = t .map a
          by disjoint_moved_fixed A d t s (disjoint_supports_symmetric A s t disjoint) (t .map a)
            (moved_image_moved A t a nq)
        = t .map (s .map a) by inverse A (t .map (s .map a)) (t .map a) (refl (t .map) p) ∎ ]
  | inr. np ↦ calc
      s .map (t .map a) = s .map a by refl (s .map) (disjoint_moved_fixed A d s t disjoint a np)
      = t .map (s .map a)
        by inverse A (t .map (s .map a)) (s .map a)
          (disjoint_moved_fixed A d s t disjoint (s .map a) (moved_image_moved A s a np)) ∎ ]

{` The unlabeled exercise after def:support-permutation: permutations of a
   decidable set with disjoint supports commute, st = ts. `}
def disjoint_supports_commute (A : Type) (d : DecidableEquality A) (s t : Equiv A A)
  (disjoint : DisjointSupports A s t)
  : Id (Equiv A A) (compose_equiv A A A t s) (compose_equiv A A A s t)
  ≔ equiv_homotopy A A (compose_equiv A A A t s) (compose_equiv A A A s t)
      (disjoint_supports_commute_at A d s t disjoint)
