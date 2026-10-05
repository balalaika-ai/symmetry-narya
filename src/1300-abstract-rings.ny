export "729-pointwise-hom-products"

{` Chapter 13 (fields.tex), sec:abstrings. Abstract rings (def:abstractring),
   the iterated Σ-type of rings (def:typering), commutative and non-trivial
   rings, xca:ring-group-abelian (the additive group is abelian), abstract
   ring homomorphisms (def:ringhom), and the running-text observations
   before def:mixring (left and right multiplications are abstract
   endomorphisms of the additive group; associativity as an equality of
   the two composites).

   The record AbstractRing flattens the book's pair "(abstract group
   (R,0,+,-), monoid (R,1,·))": its fields are the group data and laws
   (AbstractGroupLaws of module 403), the multiplicative unit and
   multiplication with the book's MonoidLaws (module 700), and DistrLaws.
   ring_additive_group and ring_monoid recover the two structures, and
   abstract_ring_sigma_equiv identifies the record with the book's
   iterated Σ (both round trips refl). `}

{` DistrLaws(R, ·, +): left and right distributive laws. `}
def DistrLaws (R : Type) (mul : R → R → R) (add : R → R → R) : Type
  ≔ Product ((a b c : R) → Id R (mul a (add b c)) (add (mul a b) (mul a c)))
      ((a b c : R) → Id R (mul (add a b) c) (add (mul a c) (mul b c)))

def AbstractRing : Type ≔ sig (
  carrier : Type,
  zero : carrier,
  add : carrier → carrier → carrier,
  neg : carrier → carrier,
  add_laws : AbstractGroupLaws carrier zero add neg,
  one : carrier,
  mul : carrier → carrier → carrier,
  mul_laws : MonoidLaws carrier one mul,
  distr : DistrLaws carrier mul add)

def ring_additive_group (R : AbstractRing) : AbstractGroup
  ≔ (R .carrier, R .zero, R .add, R .neg, R .add_laws)

def ring_monoid (R : AbstractRing) : Monoid ≔ (R .carrier, R .one, R .mul, R .mul_laws)

def ring_set (R : AbstractRing) : isSet (R .carrier) ≔ R .add_laws .carrier_set

def ring_mul_one_right (R : AbstractRing) (a : R .carrier) : Id (R .carrier) (R .mul a (R .one)) a
  ≔ R .mul_laws .snd .fst a .fst

def ring_mul_one_left (R : AbstractRing) (a : R .carrier) : Id (R .carrier) (R .mul (R .one) a) a
  ≔ R .mul_laws .snd .fst a .snd

def ring_mul_assoc (R : AbstractRing) (a b c : R .carrier)
  : Id (R .carrier) (R .mul a (R .mul b c)) (R .mul (R .mul a b) c)
  ≔ R .mul_laws .snd .snd a b c

def ring_ldistr (R : AbstractRing) (a b c : R .carrier)
  : Id (R .carrier) (R .mul a (R .add b c)) (R .add (R .mul a b) (R .mul a c))
  ≔ R .distr .fst a b c

def ring_rdistr (R : AbstractRing) (a b c : R .carrier)
  : Id (R .carrier) (R .mul (R .add a b) c) (R .add (R .mul a c) (R .mul b c))
  ≔ R .distr .snd a b c

def ring_add_assoc (R : AbstractRing) (a b c : R .carrier)
  : Id (R .carrier) (R .add a (R .add b c)) (R .add (R .add a b) c)
  ≔ R .add_laws .assoc a b c

{` def:abstractring, last paragraph. Non-trivial: 0 ≠ 1. Commutative:
   a · b = b · a for all a, b. `}
def IsNonTrivialRing (R : AbstractRing) : Type ≔ Not (Id (R .carrier) (R .zero) (R .one))

def IsCommutativeRing (R : AbstractRing) : Type
  ≔ (a b : R .carrier) → Id (R .carrier) (R .mul a b) (R .mul b a)

def is_commutative_ring_prop (R : AbstractRing) : isProp (IsCommutativeRing R)
  ≔ pi_prop (R .carrier) (a ↦ (b : R .carrier) → Id (R .carrier) (R .mul a b) (R .mul b a))
      (a ↦ pi_prop (R .carrier) (b ↦ Id (R .carrier) (R .mul a b) (R .mul b a))
        (b ↦ ring_set R (R .mul a b) (R .mul b a)))

def is_non_trivial_ring_prop (R : AbstractRing) : isProp (IsNonTrivialRing R)
  ≔ pi_prop (Id (R .carrier) (R .zero) (R .one)) (_ ↦ Empty) (_ ↦ x y ↦ match x [ ])

{` def:typering. The book's iterated Σ over abstract groups. `}
def AbstractRingSigma : Type
  ≔ Σ AbstractGroup (G ↦ Σ (G .carrier) (e ↦ Σ (G .carrier → G .carrier → G .carrier) (μ ↦
      Product (MonoidLaws (G .carrier) e μ) (DistrLaws (G .carrier) μ (G .mul)))))

def abstract_ring_to_sigma (R : AbstractRing) : AbstractRingSigma
  ≔ (ring_additive_group R, (R .one, (R .mul, (R .mul_laws, R .distr))))

def abstract_ring_from_sigma (t : AbstractRingSigma) : AbstractRing
  ≔ (t .fst .carrier, t .fst .unit, t .fst .mul, t .fst .inv, t .fst .laws,
     t .snd .fst, t .snd .snd .fst, t .snd .snd .snd .fst, t .snd .snd .snd .snd)

def abstract_ring_sigma_equiv : Equiv AbstractRing AbstractRingSigma
  ≔ quasi_inverse_equiv AbstractRing AbstractRingSigma abstract_ring_to_sigma abstract_ring_from_sigma
      (R ↦ refl R) (t ↦ refl t)

{` def:typering, second sentence: commutative rings. `}
def CommutativeRing : Type ≔ Σ AbstractRing IsCommutativeRing

def CommutativeRingSigma : Type
  ≔ Σ AbstractGroup (G ↦ Σ (G .carrier) (e ↦ Σ (G .carrier → G .carrier → G .carrier) (μ ↦
      Product (Product (MonoidLaws (G .carrier) e μ) (DistrLaws (G .carrier) μ (G .mul)))
        ((a b : G .carrier) → Id (G .carrier) (μ a b) (μ b a)))))

def commutative_ring_sigma_equiv : Equiv CommutativeRing CommutativeRingSigma
  ≔ quasi_inverse_equiv CommutativeRing CommutativeRingSigma
      (R ↦ (ring_additive_group (R .fst), (R .fst .one, (R .fst .mul, ((R .fst .mul_laws, R .fst .distr), R .snd)))))
      (t ↦ ((t .fst .carrier, t .fst .unit, t .fst .mul, t .fst .inv, t .fst .laws,
             t .snd .fst, t .snd .snd .fst, t .snd .snd .snd .fst .fst, t .snd .snd .snd .fst .snd),
            t .snd .snd .snd .snd))
      (R ↦ refl R) (t ↦ refl t)

{` xca:ring-group-abelian, by the hint: expanding (a+1)(b+1) first by the
   right and then by the left distributive law gives (ab + a) + (b + 1);
   the other order gives (ab + b) + (a + 1). Cancelling ab on the left and
   1 on the right gives a + b = b + a. `}
def ring_expand_right_first (R : AbstractRing) (a b : R .carrier)
  : Id (R .carrier) (R .mul (R .add a (R .one)) (R .add b (R .one)))
      (R .add (R .mul a b) (R .add a (R .add b (R .one))))
  ≔ let S ≔ R .carrier in let p ≔ R .add in let m ≔ R .mul in let o ≔ R .one in
    calc
      m (p a o) (p b o) = p (m a (p b o)) (m o (p b o)) by ring_rdistr R a o (p b o)
      = p (p (m a b) (m a o)) (p (m o b) (m o o))
        by refl p (ring_ldistr R a b o) (ring_ldistr R o b o)
      = p (p (m a b) a) (p b o)
        by refl p (refl (p (m a b)) (ring_mul_one_right R a))
             (refl p (ring_mul_one_left R b) (ring_mul_one_left R o))
      = p (m a b) (p a (p b o)) by inverse S (p (m a b) (p a (p b o))) (p (p (m a b) a) (p b o))
          (ring_add_assoc R (m a b) a (p b o)) ∎

def ring_expand_left_first (R : AbstractRing) (a b : R .carrier)
  : Id (R .carrier) (R .mul (R .add a (R .one)) (R .add b (R .one)))
      (R .add (R .mul a b) (R .add b (R .add a (R .one))))
  ≔ let S ≔ R .carrier in let p ≔ R .add in let m ≔ R .mul in let o ≔ R .one in
    calc
      m (p a o) (p b o) = p (m (p a o) b) (m (p a o) o) by ring_ldistr R (p a o) b o
      = p (p (m a b) (m o b)) (p (m a o) (m o o))
        by refl p (ring_rdistr R a o b) (ring_rdistr R a o o)
      = p (p (m a b) b) (p a o)
        by refl p (refl (p (m a b)) (ring_mul_one_left R b))
             (refl p (ring_mul_one_right R a) (ring_mul_one_left R o))
      = p (m a b) (p b (p a o)) by inverse S (p (m a b) (p b (p a o))) (p (p (m a b) b) (p a o))
          (ring_add_assoc R (m a b) b (p a o)) ∎

def ring_add_comm (R : AbstractRing) (a b : R .carrier) : Id (R .carrier) (R .add a b) (R .add b a)
  ≔ let G ≔ ring_additive_group R in let S ≔ R .carrier in let p ≔ R .add in let o ≔ R .one in
    let e1 : Id S (p (R .mul a b) (p a (p b o))) (p (R .mul a b) (p b (p a o)))
      ≔ concat S (p (R .mul a b) (p a (p b o))) (R .mul (p a o) (p b o)) (p (R .mul a b) (p b (p a o)))
          (inverse S (R .mul (p a o) (p b o)) (p (R .mul a b) (p a (p b o))) (ring_expand_right_first R a b))
          (ring_expand_left_first R a b) in
    let e2 : Id S (p a (p b o)) (p b (p a o)) ≔ ag_cancel_left G (R .mul a b) (p a (p b o)) (p b (p a o)) e1 in
    let e3 : Id S (p (p a b) o) (p (p b a) o)
      ≔ calc
          p (p a b) o = p a (p b o) by inverse S (p a (p b o)) (p (p a b) o) (ring_add_assoc R a b o)
          = p b (p a o) by e2
          = p (p b a) o by ring_add_assoc R b a o ∎ in
    ag_cancel_right G o (p a b) (p b a) e3

def ring_additive_abelian (R : AbstractRing) : IsAbstractAbelian (ring_additive_group R)
  ≔ a b ↦ ring_add_comm R a b

{` Basic consequences of the distributive laws, used later: 0 · a = 0,
   a · 0 = 0, (-a) · b = -(a · b), a · (-b) = -(a · b). `}
def ring_mul_zero_left (R : AbstractRing) (a : R .carrier) : Id (R .carrier) (R .mul (R .zero) a) (R .zero)
  ≔ let S ≔ R .carrier in let z ≔ R .zero in let m ≔ R .mul in
    ag_idempotent_unit (ring_additive_group R) (m z a)
      (calc
         R .add (m z a) (m z a) = m (R .add z z) a by inverse S (m (R .add z z) a) (R .add (m z a) (m z a))
           (ring_rdistr R z z a)
         = m z a by refl ((x ↦ m x a) : S → S) (R .add_laws .unit_right z) ∎)

def ring_mul_zero_right (R : AbstractRing) (a : R .carrier) : Id (R .carrier) (R .mul a (R .zero)) (R .zero)
  ≔ let S ≔ R .carrier in let z ≔ R .zero in let m ≔ R .mul in
    ag_idempotent_unit (ring_additive_group R) (m a z)
      (calc
         R .add (m a z) (m a z) = m a (R .add z z) by inverse S (m a (R .add z z)) (R .add (m a z) (m a z))
           (ring_ldistr R a z z)
         = m a z by refl (m a) (R .add_laws .unit_right z) ∎)

def ring_mul_neg_left (R : AbstractRing) (a b : R .carrier)
  : Id (R .carrier) (R .mul (R .neg a) b) (R .neg (R .mul a b))
  ≔ let S ≔ R .carrier in let m ≔ R .mul in
    ag_inv_unique_right (ring_additive_group R) (m a b) (m (R .neg a) b)
      (calc
         R .add (m a b) (m (R .neg a) b) = m (R .add a (R .neg a)) b
           by inverse S (m (R .add a (R .neg a)) b) (R .add (m a b) (m (R .neg a) b)) (ring_rdistr R a (R .neg a) b)
         = m (R .zero) b by refl ((x ↦ m x b) : S → S) (R .add_laws .inv_right a)
         = R .zero by ring_mul_zero_left R b ∎)

def ring_mul_neg_right (R : AbstractRing) (a b : R .carrier)
  : Id (R .carrier) (R .mul a (R .neg b)) (R .neg (R .mul a b))
  ≔ let S ≔ R .carrier in let m ≔ R .mul in
    ag_inv_unique_right (ring_additive_group R) (m a b) (m a (R .neg b))
      (calc
         R .add (m a b) (m a (R .neg b)) = m a (R .add b (R .neg b))
           by inverse S (m a (R .add b (R .neg b))) (R .add (m a b) (m a (R .neg b))) (ring_ldistr R a b (R .neg b))
         = m a (R .zero) by refl (m a) (R .add_laws .inv_right b)
         = R .zero by ring_mul_zero_right R a ∎)

{` In a non-trivial ring 0 ≠ 1 also in the other orientation. `}
def ring_one_ne_zero (R : AbstractRing) (h : IsNonTrivialRing R) (p : Id (R .carrier) (R .one) (R .zero)) : Empty
  ≔ h (inverse (R .carrier) (R .one) (R .zero) p)

{` def:ringhom. An abstract ring homomorphism is an abstract homomorphism
   of the additive groups that is a monoid homomorphism of the
   multiplicative monoids (rem:monoid-hom: f(1) = 1 and f(st) = f(s)f(t)). `}
def IsRingHomFn (R S : AbstractRing) (f : R .carrier → S .carrier) : Type
  ≔ Product (IsAbstractHom (ring_additive_group R) (ring_additive_group S) f)
      (Product (Id (S .carrier) (f (R .one)) (S .one))
        ((s s' : R .carrier) → Id (S .carrier) (f (R .mul s s')) (S .mul (f s) (f s'))))

def RingHom (R S : AbstractRing) : Type
  ≔ Σ (AbstractHom (ring_additive_group R) (ring_additive_group S)) (φ ↦
      Product (Id (S .carrier) (φ .fst (R .one)) (S .one))
        ((s s' : R .carrier) → Id (S .carrier) (φ .fst (R .mul s s')) (S .mul (φ .fst s) (φ .fst s'))))

def ring_hom_fn (R S : AbstractRing) (φ : RingHom R S) : R .carrier → S .carrier ≔ φ .fst .fst

{` The multiplicative part of a ring homomorphism is a monoid homomorphism. `}
def ring_hom_monoid_hom (R S : AbstractRing) (φ : RingHom R S) : MonoidHom (ring_monoid R) (ring_monoid S)
  ≔ (φ .fst .fst, (φ .snd .fst, φ .snd .snd))

def is_ring_hom_extra_prop (R S : AbstractRing) (f : R .carrier → S .carrier)
  : isProp (Product (Id (S .carrier) (f (R .one)) (S .one))
      ((s s' : R .carrier) → Id (S .carrier) (f (R .mul s s')) (S .mul (f s) (f s'))))
  ≔ product_prop (Id (S .carrier) (f (R .one)) (S .one))
      ((s s' : R .carrier) → Id (S .carrier) (f (R .mul s s')) (S .mul (f s) (f s')))
      (ring_set S (f (R .one)) (S .one))
      (pi_prop (R .carrier) (s ↦ (s' : R .carrier) → Id (S .carrier) (f (R .mul s s')) (S .mul (f s) (f s')))
        (s ↦ pi_prop (R .carrier) (s' ↦ Id (S .carrier) (f (R .mul s s')) (S .mul (f s) (f s')))
          (s' ↦ ring_set S (f (R .mul s s')) (S .mul (f s) (f s')))))

{` Ring homomorphisms are determined by their underlying functions. `}
def ring_hom_ext (R S : AbstractRing) (φ ψ : RingHom R S)
  (h : (s : R .carrier) → Id (S .carrier) (φ .fst .fst s) (ψ .fst .fst s))
  : Id (RingHom R S) φ ψ
  ≔ subtype_equal (AbstractHom (ring_additive_group R) (ring_additive_group S))
      (χ ↦ Product (Id (S .carrier) (χ .fst (R .one)) (S .one))
        ((s s' : R .carrier) → Id (S .carrier) (χ .fst (R .mul s s')) (S .mul (χ .fst s) (χ .fst s'))))
      (χ ↦ is_ring_hom_extra_prop R S (χ .fst)) φ ψ
      (abstract_hom_ext (ring_additive_group R) (ring_additive_group S) (φ .fst) (ψ .fst) h)

def ring_hom_id (R : AbstractRing) : RingHom R R
  ≔ (abstract_hom_id (ring_additive_group R), (refl (R .one), s s' ↦ refl (R .mul s s')))

{` ψ ∘ φ (φ first), as abstract_hom_compose. `}
def ring_hom_compose (R S T : AbstractRing) (φ : RingHom R S) (ψ : RingHom S T) : RingHom R T
  ≔ let f ≔ φ .fst .fst in let g ≔ ψ .fst .fst in
    (abstract_hom_compose (ring_additive_group R) (ring_additive_group S) (ring_additive_group T) (φ .fst) (ψ .fst),
     (concat (T .carrier) (g (f (R .one))) (g (S .one)) (T .one) (refl g (φ .snd .fst)) (ψ .snd .fst),
      s s' ↦ concat (T .carrier) (g (f (R .mul s s'))) (g (S .mul (f s) (f s'))) (T .mul (g (f s)) (g (f s')))
        (refl g (φ .snd .snd s s')) (ψ .snd .snd (f s) (f s'))))

{` Running text before def:mixring (fields.tex 100-109): for a, b : R the
   left multiplication (a · -) and the right multiplication (- · b) are
   abstract homomorphisms of the additive group to itself. `}
def ring_left_mul_hom (R : AbstractRing) (a : R .carrier)
  : AbstractHom (ring_additive_group R) (ring_additive_group R)
  ≔ (R .mul a, s s' ↦ ring_ldistr R a s s')

def ring_right_mul_hom (R : AbstractRing) (b : R .carrier)
  : AbstractHom (ring_additive_group R) (ring_additive_group R)
  ≔ (x ↦ R .mul x b, s s' ↦ ring_rdistr R s s' b)

{` "Equality of the two composites (a · (- · b)) and ((a · -) · b) is an
   elegant way of expressing associativity": for any multiplication on a
   type, associativity is logically equivalent to the equality of these
   two functions for all a, b. `}
def ComposedMultiplicationsAgree (S : Type) (mul : S → S → S) : Type
  ≔ (a b : S) → Id (S → S) (x ↦ mul a (mul x b)) (x ↦ mul (mul a x) b)

def assoc_to_composed_multiplications (S : Type) (mul : S → S → S) (h : AssocLaw S mul)
  : ComposedMultiplicationsAgree S mul
  ≔ a b ↦ funext S (_ ↦ S) (x ↦ mul a (mul x b)) (x ↦ mul (mul a x) b) (x ↦ h a x b)

def composed_multiplications_to_assoc (S : Type) (mul : S → S → S) (h : ComposedMultiplicationsAgree S mul)
  : AssocLaw S mul
  ≔ a x b ↦ happly S (_ ↦ S) (x ↦ mul a (mul x b)) (x ↦ mul (mul a x) b) (h a b) x

{` absHom_ptw(H, G) for an abelian abstract group G (xca:abs-homgroup with
   xca:abstract-group-of-maps, used in the running text of sec:concrings):
   abstract homomorphisms H → G with pointwise operations. `}
def ptw_unit_hom (H G : AbstractGroup) : AbstractHom H G
  ≔ (_ ↦ G .unit, _ _ ↦ inverse (G .carrier) (G .mul (G .unit) (G .unit)) (G .unit) (G .laws .unit_right (G .unit)))

def ptw_mul_hom (H G : AbstractGroup) (hab : IsAbstractAbelian G) (f g : AbstractHom H G) : AbstractHom H G
  ≔ (abstract_hom_pointwise_mul H G f g, abelian_pointwise_mul_hom H G hab f g)

def ptw_inv_hom (H G : AbstractGroup) (hab : IsAbstractAbelian G) (f : AbstractHom H G) : AbstractHom H G
  ≔ (t ↦ G .inv (f .fst t),
     t t' ↦ let S ≔ G .carrier in
       calc
         G .inv (f .fst (H .mul t t')) = G .inv (G .mul (f .fst t) (f .fst t')) by refl (G .inv) (f .snd t t')
         = G .mul (G .inv (f .fst t')) (G .inv (f .fst t)) by ag_inv_mul G (f .fst t) (f .fst t')
         = G .mul (G .inv (f .fst t)) (G .inv (f .fst t')) by hab (G .inv (f .fst t')) (G .inv (f .fst t)) ∎)

def abstract_hom_ptw_group_laws (H G : AbstractGroup) (hab : IsAbstractAbelian G)
  : AbstractGroupLaws (AbstractHom H G) (ptw_unit_hom H G) (ptw_mul_hom H G hab) (ptw_inv_hom H G hab)
  ≔ let L ≔ G .laws in
    (carrier_set ≔ abstract_hom_set H G,
     unit_right ≔ f ↦ abstract_hom_ext H G (ptw_mul_hom H G hab f (ptw_unit_hom H G)) f (t ↦ L .unit_right (f .fst t)),
     unit_left ≔ f ↦ abstract_hom_ext H G (ptw_mul_hom H G hab (ptw_unit_hom H G) f) f (t ↦ L .unit_left (f .fst t)),
     assoc ≔ f1 f2 f3 ↦ abstract_hom_ext H G
       (ptw_mul_hom H G hab f1 (ptw_mul_hom H G hab f2 f3)) (ptw_mul_hom H G hab (ptw_mul_hom H G hab f1 f2) f3)
       (t ↦ L .assoc (f1 .fst t) (f2 .fst t) (f3 .fst t)),
     inv_right ≔ f ↦ abstract_hom_ext H G (ptw_mul_hom H G hab f (ptw_inv_hom H G hab f)) (ptw_unit_hom H G)
       (t ↦ L .inv_right (f .fst t)))

def abstract_hom_ptw_group (H G : AbstractGroup) (hab : IsAbstractAbelian G) : AbstractGroup
  ≔ (AbstractHom H G, ptw_unit_hom H G, ptw_mul_hom H G hab, ptw_inv_hom H G hab,
     abstract_hom_ptw_group_laws H G hab)

def abstract_hom_ptw_group_abelian (H G : AbstractGroup) (hab : IsAbstractAbelian G)
  : IsAbstractAbelian (abstract_hom_ptw_group H G hab)
  ≔ f g ↦ abstract_hom_ext H G (ptw_mul_hom H G hab f g) (ptw_mul_hom H G hab g f) (t ↦ hab (f .fst t) (g .fst t))

{` Running text of sec:concrings (fields.tex 1120-1123): a ↦ (a · -) is an
   abstract homomorphism from (R,0,+,-) to absHom_ptw(R,R). `}
def ring_left_mul_ptw_hom (R : AbstractRing)
  : AbstractHom (ring_additive_group R)
      (abstract_hom_ptw_group (ring_additive_group R) (ring_additive_group R) (ring_additive_abelian R))
  ≔ let G ≔ ring_additive_group R in
    (a ↦ ring_left_mul_hom R a,
     a b ↦ abstract_hom_ext G G (ring_left_mul_hom R (R .add a b))
       (ptw_mul_hom G G (ring_additive_abelian R) (ring_left_mul_hom R a) (ring_left_mul_hom R b))
       (x ↦ ring_rdistr R a b x))
