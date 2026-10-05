export "40-map-cancellation"

def EquivalenceRelation (A : Type) : Type ≔ sig (
  predicate : A → A → PropTypes,
  reflexive : (a : A) → predicate a a .fst,
  symmetric : (a b : A) → predicate a b .fst → predicate b a .fst,
  transitive : (a b c : A) → predicate a b .fst → predicate b c .fst → predicate a c .fst)

def Rel (A : Type) (R : EquivalenceRelation A) (x y : A) : Type ≔ R .predicate x y .fst

{` def:quotient-set: the image of the equivalence-predicate map, not a new axiom. `}
def Quotient (A : Type) (R : EquivalenceRelation A) : Type ≔ Image A (A → PropTypes) (R .predicate)
def quotient_class (A : Type) (R : EquivalenceRelation A) : A → Quotient A R
  ≔ image_factor A (A → PropTypes) (R .predicate)

def quotient_set (A : Type) (R : EquivalenceRelation A) : isSet (Quotient A R)
  ≔ image_set A (A → PropTypes) (R .predicate) (subtypes_set A)

def quotient_surjective (A : Type) (R : EquivalenceRelation A)
  : Surjective A (Quotient A R) (quotient_class A R)
  ≔ image_factor_surjective A (A → PropTypes) (R .predicate)

def relation_predicate_path (A : Type) (R : EquivalenceRelation A) (x y : A) (r : Rel A R x y)
  : Id (A → PropTypes) (R .predicate x) (R .predicate y)
  ≔ funext A (_ ↦ PropTypes) (R .predicate x) (R .predicate y)
      (z ↦ proposition_extensionality (R .predicate x z) (R .predicate y z)
        (s ↦ R .transitive y x z (R .symmetric x y r) s)
        (s ↦ R .transitive x y z r s))

def relation_of_predicate_path (A : Type) (R : EquivalenceRelation A) (x y : A)
  (p : Id (A → PropTypes) (R .predicate x) (R .predicate y)) : Rel A R x y
  ≔ transport (A → PropTypes) (P ↦ P y .fst) (R .predicate y) (R .predicate x)
      (inverse (A → PropTypes) (R .predicate x) (R .predicate y) p) (R .reflexive y)

def quotient_member_of_path (A : Type) (R : EquivalenceRelation A) (z : Quotient A R) (a : A)
  (p : Id (Quotient A R) z (quotient_class A R a)) : z .fst a .fst
  ≔ transport (A → PropTypes) (P ↦ P a .fst) (R .predicate a) (z .fst)
      (inverse (A → PropTypes) (z .fst) (R .predicate a) (p .fst)) (R .reflexive a)

def quotient_path_of_member (A : Type) (R : EquivalenceRelation A) (z : Quotient A R) (a : A)
  (h : z .fst a .fst) : Id (Quotient A R) z (quotient_class A R a)
  ≔ mere_rec (BookFiber A (A → PropTypes) (R .predicate) (z .fst))
      (Id (Quotient A R) z (quotient_class A R a)) (quotient_set A R z (quotient_class A R a))
      (w ↦ subtype_equal (A → PropTypes) (P ↦ Mere (BookFiber A (A → PropTypes) (R .predicate) P))
        (P ↦ mere_isprop (BookFiber A (A → PropTypes) (R .predicate) P)) z (quotient_class A R a)
        (concat (A → PropTypes) (z .fst) (R .predicate (w .fst)) (R .predicate a) (w .snd)
          (relation_predicate_path A R (w .fst) a
            (transport (A → PropTypes) (P ↦ P a .fst) (z .fst) (R .predicate (w .fst)) (w .snd) h)))) (z .snd)

{` lem:equiv-class-prop, with the actual predicate at a quotient element. `}
def quotient_class_property (A : Type) (R : EquivalenceRelation A) (z : Quotient A R) (a : A)
  : Equiv (Id (Quotient A R) z (quotient_class A R a)) (z .fst a .fst)
  ≔ iff_equiv (Id (Quotient A R) z (quotient_class A R a)) (z .fst a .fst)
      (quotient_set A R z (quotient_class A R a)) (z .fst a .snd)
      (quotient_member_of_path A R z a) (quotient_path_of_member A R z a)

def quotient_effective (A : Type) (R : EquivalenceRelation A) (x y : A)
  : Equiv (Id (Quotient A R) (quotient_class A R x) (quotient_class A R y)) (Rel A R x y)
  ≔ quotient_class_property A R (quotient_class A R x) y

def quotient_encode (A : Type) (R : EquivalenceRelation A) (x y : A) (r : Rel A R x y)
  : Id (Quotient A R) (quotient_class A R x) (quotient_class A R y)
  ≔ quotient_path_of_member A R (quotient_class A R x) y r

def Respects (A B : Type) (R : EquivalenceRelation A) (f : A → B) : Type
  ≔ (x y : A) → Rel A R x y → Id B (f x) (f y)

def quotient_witness_relation (A : Type) (R : EquivalenceRelation A) (P : A → PropTypes)
  (u v : BookFiber A (A → PropTypes) (R .predicate) P) : Rel A R (u .fst) (v .fst)
  ≔ relation_of_predicate_path A R (u .fst) (v .fst)
      (concat (A → PropTypes) (R .predicate (u .fst)) P (R .predicate (v .fst))
        (inverse (A → PropTypes) P (R .predicate (u .fst)) (u .snd)) (v .snd))

def quotient_rec (A B : Type) (R : EquivalenceRelation A) (hb : isSet B)
  (f : A → B) (h : Respects A B R f) (z : Quotient A R) : B
  ≔ weakly_constant_rec (BookFiber A (A → PropTypes) (R .predicate) (z .fst)) B
      (w ↦ f (w .fst)) hb
      (u v ↦ h (u .fst) (v .fst) (quotient_witness_relation A R (z .fst) u v)) (z .snd)

def quotient_rec_beta (A B : Type) (R : EquivalenceRelation A) (hb : isSet B)
  (f : A → B) (h : Respects A B R f) (a : A)
  : Id B (quotient_rec A B R hb f h (quotient_class A R a)) (f a) ≔ refl (f a)

def QuotientLifts (A B : Type) (R : EquivalenceRelation A) (f : A → B) : Type
  ≔ Σ (Quotient A R → B) (g ↦ Id (A → B) f (compose A (Quotient A R) B g (quotient_class A R)))

def quotient_lifts_prop (A B : Type) (R : EquivalenceRelation A) (hb : isSet B) (f : A → B)
  : isProp (QuotientLifts A B R f)
  ≔ u v ↦ subtype_equal (Quotient A R → B)
      (g ↦ Id (A → B) f (compose A (Quotient A R) B g (quotient_class A R)))
      (g ↦ pi_set A (_ ↦ B) (_ ↦ hb) f (compose A (Quotient A R) B g (quotient_class A R))) u v
      (equiv_inverse_map (Id (Quotient A R → B) (u .fst) (v .fst))
        (Id (A → B) (compose A (Quotient A R) B (u .fst) (quotient_class A R))
          (compose A (Quotient A R) B (v .fst) (quotient_class A R)))
        (cancel_surjection_into_set A (Quotient A R) B (quotient_class A R) (quotient_surjective A R) hb (u .fst) (v .fst))
        (concat (A → B) (compose A (Quotient A R) B (u .fst) (quotient_class A R)) f
          (compose A (Quotient A R) B (v .fst) (quotient_class A R))
          (inverse (A → B) f (compose A (Quotient A R) B (u .fst) (quotient_class A R)) (u .snd)) (v .snd)))

{` thm:quotient-property, second clause, including the whole space of lifts. `}
def quotient_universal_property (A B : Type) (R : EquivalenceRelation A) (hb : isSet B)
  (f : A → B) (h : Respects A B R f) : BookIsContr (QuotientLifts A B R f)
  ≔ let c : QuotientLifts A B R f ≔ (quotient_rec A B R hb f h, refl f) in
    (c, quotient_lifts_prop A B R hb f c)
