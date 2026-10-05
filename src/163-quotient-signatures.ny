export "162-pointed-maps"

{` def:quotient-as-HIT as an explicit signature. Narya has no higher
   inductive types, and the judgmental computation rule of the book is
   replaced by a typal one. `}
def QuotientSignature (A : Type) (R : EquivalenceRelation A) : Type ≔ sig (
  carrier : Type,
  set : isSet carrier,
  class : A → carrier,
  relate : (x y : A) → Rel A R x y → Id carrier (class x) (class y),
  induction : (S : carrier → Type) → ((z : carrier) → isSet (S z))
    → (b : (a : A) → S (class a))
    → ((x y : A) (r : Rel A R x y) → Id S (relate x y r) (b x) (b y))
    → Σ ((z : carrier) → S z) (f ↦ (a : A) → Id (S (class a)) (f (class a)) (b a)))

{` The image quotient of def:quotient-set inhabits the signature. `}
def image_quotient_signature (A : Type) (R : EquivalenceRelation A) : QuotientSignature A R
  ≔ (Quotient A R, quotient_set A R, quotient_class A R, quotient_encode A R,
     S hs b hb ↦ (quotient_induction A R S hs b hb, quotient_induction_beta A R S hs b hb))

def prop_family_pathover (A : Type) (B : A → Type) (hB : (a : A) → isProp (B a))
  (x y : A) (p : Id A x y) (u : B x) (v : B y) : Id B p u v
  ≔ pathover_of_eq A B x y p u v (hB y (transport A B x y p u) v)

def quotient_signature_to_image (A : Type) (R : EquivalenceRelation A) (Q : QuotientSignature A R)
  : Q .carrier → Quotient A R
  ≔ Q .induction (_ ↦ Quotient A R) (_ ↦ quotient_set A R) (quotient_class A R)
      (x y r ↦ quotient_encode A R x y r) .fst

def image_to_quotient_signature (A : Type) (R : EquivalenceRelation A) (Q : QuotientSignature A R)
  : Quotient A R → Q .carrier
  ≔ quotient_rec A (Q .carrier) R (Q .set) (Q .class) (Q .relate)

def quotient_signature_retraction (A : Type) (R : EquivalenceRelation A) (Q : QuotientSignature A R)
  (z : Q .carrier)
  : Id (Q .carrier) (image_to_quotient_signature A R Q (quotient_signature_to_image A R Q z)) z
  ≔ let forth ≔ quotient_signature_to_image A R Q in
    let back ≔ image_to_quotient_signature A R Q in
    let S : Q .carrier → Type ≔ w ↦ Id (Q .carrier) (back (forth w)) w in
    let b : (a : A) → S (Q .class a)
      ≔ a ↦ refl back (Q .induction (_ ↦ Quotient A R) (_ ↦ quotient_set A R) (quotient_class A R)
        (x y r ↦ quotient_encode A R x y r) .snd a) in
    Q .induction S (w ↦ prop_is_set (S w) (Q .set (back (forth w)) w)) b
      (x y r ↦ prop_family_pathover (Q .carrier) S (w ↦ Q .set (back (forth w)) w)
        (Q .class x) (Q .class y) (Q .relate x y r) (b x) (b y)) .fst z

def quotient_signature_section (A : Type) (R : EquivalenceRelation A) (Q : QuotientSignature A R)
  (w : Quotient A R)
  : Id (Quotient A R) (quotient_signature_to_image A R Q (image_to_quotient_signature A R Q w)) w
  ≔ let forth ≔ quotient_signature_to_image A R Q in
    let back ≔ image_to_quotient_signature A R Q in
    let S : Quotient A R → Type ≔ v ↦ Id (Quotient A R) (forth (back v)) v in
    let b : (a : A) → S (quotient_class A R a)
      ≔ a ↦ Q .induction (_ ↦ Quotient A R) (_ ↦ quotient_set A R) (quotient_class A R)
        (x y r ↦ quotient_encode A R x y r) .snd a in
    quotient_induction A R S (v ↦ prop_is_set (S v) (quotient_set A R (forth (back v)) v)) b
      (x y r ↦ prop_family_pathover (Quotient A R) S (v ↦ quotient_set A R (forth (back v)) v)
        (quotient_class A R x) (quotient_class A R y) (quotient_encode A R x y r) (b x) (b y)) w

{` xca:quotients-equivalence: any type with the displayed constructors
   and set-valued induction is equivalent to the image quotient. `}
def quotient_signature_equiv (A : Type) (R : EquivalenceRelation A) (Q : QuotientSignature A R)
  : Equiv (Q .carrier) (Quotient A R)
  ≔ quasi_inverse_equiv (Q .carrier) (Quotient A R)
      (quotient_signature_to_image A R Q) (image_to_quotient_signature A R Q)
      (quotient_signature_retraction A R Q) (quotient_signature_section A R Q)
