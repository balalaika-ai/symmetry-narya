export "700-monoids-and-group-laws"

{` Chapter 7 (absgroup.tex), exa:monoid and rem:ee=e_coherence (the set
   case).

   exa:monoid. For a set S the lists S* (List S, module 01) form a monoid
   with the empty list as unit and concatenation (append, xca:reverse) as
   multiplication. S* is a set by list_set (module 16, the list case of
   thm:isset-inductive-types). The unit law ε * xs = xs holds by
   computation; xs * ε = xs is append_nil; associativity in the book's
   orientation is append_assoc_book. `}

def list_monoid_laws (S : Type) (hS : isSet S) : MonoidLaws (List S) nil. (append S)
  ≔ (list_set S hS,
     (xs ↦ (append_nil S xs, refl xs),
      xs ys zs ↦ append_assoc_book S xs ys zs))

def list_monoid (S : Type) (hS : isSet S) : Monoid
  ≔ (List S, nil., append S, list_monoid_laws S hS)

{` Litmus: the product is concatenation and the unit is the empty list,
   both judgmentally; [true] * [false] = [true, false]. `}
def list_monoid_mul_litmus
  : Id (List Bool) (list_monoid Bool bool_set .mul (cons. true. nil.) (cons. false. nil.))
      (cons. true. (cons. false. nil.))
  ≔ refl (cons. true. (cons. false. nil.) : List Bool)

def list_monoid_unit_litmus (S : Type) (hS : isSet S) : Id (List S) (list_monoid S hS .unit) nil.
  ≔ refl (nil. : List S)

{` Litmus: S* is a monoid but (for inhabited S) not a group: a one-element
   list has no right inverse, so no inverse operation satisfies the law of
   inverses. `}
def list_monoid_no_inverse (S : Type) (inv : List S → List S)
  (law : InverseLaw (List S) nil. (append S) inv) (x : S) : Empty
  ≔ list_encode S (cons. x (inv (cons. x nil.))) nil. (law (cons. x nil.))

{` rem:ee=e_coherence, the set case: in a monoid the two identifications
   e · e = e given by the two unit laws agree (the carrier is a set). The
   counterexample without the set condition is in module 727. `}
def monoid_unit_coherence (M : Monoid)
  : Id (Id (M .carrier) (M .mul (M .unit) (M .unit)) (M .unit))
      (monoid_unit_right M (M .unit)) (monoid_unit_left M (M .unit))
  ≔ monoid_set M (M .mul (M .unit) (M .unit)) (M .unit) (monoid_unit_right M (M .unit)) (monoid_unit_left M (M .unit))
