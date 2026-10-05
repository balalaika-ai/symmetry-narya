export "41-set-quotients"

{` Dependent elimination into sets is derived through the total space.
   Its beta law below is propositional, not the judgmental rule of the book HIT. `}
def QuotientBoundary (A : Type) (R : EquivalenceRelation A) (S : Quotient A R → Type)
  (b : (a : A) → S (quotient_class A R a)) : Type
  ≔ (x y : A) (r : Rel A R x y) → Id S (quotient_encode A R x y r) (b x) (b y)

def quotient_induction_lift (A : Type) (R : EquivalenceRelation A) (S : Quotient A R → Type)
  (hs : (z : Quotient A R) → isSet (S z)) (b : (a : A) → S (quotient_class A R a))
  (hb : QuotientBoundary A R S b) : Quotient A R → Σ (Quotient A R) S
  ≔ quotient_rec A (Σ (Quotient A R) S) R (sigma_set (Quotient A R) S (quotient_set A R) hs)
      (a ↦ (quotient_class A R a, b a)) (x y r ↦ (quotient_encode A R x y r, hb x y r))

def quotient_induction_base (A : Type) (R : EquivalenceRelation A) (S : Quotient A R → Type)
  (hs : (z : Quotient A R) → isSet (S z)) (b : (a : A) → S (quotient_class A R a))
  (hb : QuotientBoundary A R S b)
  : Id (Quotient A R → Quotient A R) (z ↦ quotient_induction_lift A R S hs b hb z .fst) (identity (Quotient A R))
  ≔ let f : Quotient A R → Quotient A R ≔ (z ↦ quotient_induction_lift A R S hs b hb z .fst) in
    equiv_inverse_map (Id (Quotient A R → Quotient A R) f (identity (Quotient A R)))
      (Id (A → Quotient A R) (a ↦ f (quotient_class A R a)) (quotient_class A R))
      (cancel_surjection_into_set A (Quotient A R) (Quotient A R)
        (quotient_class A R) (quotient_surjective A R) (quotient_set A R) f (identity (Quotient A R)))
      (refl (quotient_class A R))

def quotient_induction (A : Type) (R : EquivalenceRelation A) (S : Quotient A R → Type)
  (hs : (z : Quotient A R) → isSet (S z)) (b : (a : A) → S (quotient_class A R a))
  (hb : QuotientBoundary A R S b) (z : Quotient A R) : S z
  ≔ transport (Quotient A R) S (quotient_induction_lift A R S hs b hb z .fst) z
      (quotient_induction_base A R S hs b hb (refl z)) (quotient_induction_lift A R S hs b hb z .snd)

def quotient_induction_beta (A : Type) (R : EquivalenceRelation A) (S : Quotient A R → Type)
  (hs : (z : Quotient A R) → isSet (S z)) (b : (a : A) → S (quotient_class A R a))
  (hb : QuotientBoundary A R S b) (a : A)
  : Id (S (quotient_class A R a)) (quotient_induction A R S hs b hb (quotient_class A R a)) (b a)
  ≔ let z ≔ quotient_class A R a in
    let p ≔ quotient_induction_base A R S hs b hb (refl z) in
    concat (S z) (transport (Quotient A R) S z z p (b a))
      (transport (Quotient A R) S z z (refl z) (b a)) (b a)
      (map_path (Id (Quotient A R) z z) (S z) (q ↦ transport (Quotient A R) S z z q (b a))
        p (refl z) (quotient_set A R z z p (refl z)))
      (transport_refl (Quotient A R) S z (b a))

def indiscrete_relation (A : Type) : EquivalenceRelation A
  ≔ ((x y ↦ (Unit, unit_prop)), (x ↦ star.), (x y r ↦ star.), (x y z r s ↦ star.))

def indiscrete_quotient_prop (A : Type) : isProp (Quotient A (indiscrete_relation A))
  ≔ weakly_constant_image_prop A (A → PropTypes) (indiscrete_relation A .predicate) (subtypes_set A)
      (x y ↦ refl (indiscrete_relation A .predicate x))

{` xca:A/True-prop-trunc. `}
def indiscrete_quotient_equiv (A : Type) : Equiv (Quotient A (indiscrete_relation A)) (Mere A)
  ≔ iff_equiv (Quotient A (indiscrete_relation A)) (Mere A) (indiscrete_quotient_prop A) (mere_isprop A)
      (quotient_rec A (Mere A) (indiscrete_relation A) (prop_is_set (Mere A) (mere_isprop A))
        (mere A) (x y r ↦ mere_isprop A (mere A x) (mere A y)))
      (mere_rec A (Quotient A (indiscrete_relation A)) (indiscrete_quotient_prop A)
        (quotient_class A (indiscrete_relation A)))
