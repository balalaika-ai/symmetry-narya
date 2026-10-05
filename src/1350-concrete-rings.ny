export "1208-abelian-hom-pointwise"
export "435-circle-group-homomorphisms"
export "1300-abstract-rings"

{` Chapter 13 (fields.tex 1106-1226), sec:concrings. Concrete rings
   (def:ring) and xca:Rconcring->URabstring.

   def:ring: an abelian group R, a homomorphism 1_R : Hom(ℤ, R) and a
   homomorphism μ : Hom(R, Hom(R, R)), with Hom(R, R) the group of
   def:AbHomgroup (abelian_hom_group, module 1207). ℤ is circle_group C for
   an arbitrary circle C. The laws are "TBD" in the book (only half of the
   unit law is printed); we complete them as follows, writing
   ℓ_a ≔ hom_of_symmetry(USym μ (a)) : Hom(R, R) (module 1208; the book's
   ev ∘ - of the footnote) and a · b ≔ USym ℓ_a (b) for a, b : USym R and
   1 ≔ USym 1_R (loop):
   (1) unit laws: the printed ev ∘ (USym(μ ∘ 1_R)(loop)) = B id_R, read
       literally as hom_of_symmetry(USym(μ ∘ 1_R)(loop)) = id_R (this is
       1 · b = b for all b), and the other unit law a · 1 = a;
   (2) associative law: a · (b · c) = (a · b) · c.
   Commutative: a · b = b · a. Non-trivial: 1_R is not the trivial
   homomorphism (footnote: the one classified by the constant map at the
   shape). The distributive laws need no axiom: a · - is USym of a
   homomorphism, and (a + a') · b = a · b + a' · b is the pointwise
   product of homomorphisms in Hom(R, R) (abelian_hom_usym_mul).

   Formal deviation (performance). In the pinned Narya, comparing types
   that contain USym(hom_of_symmetry(USym μ (a)))(b) does not finish in
   reasonable time (tests of > 500 s on trivial goals). The record
   ConcreteRing therefore carries the left multiplications as a field
   left : USym R → Hom(R, R) together with
   left_spec : left(a) = hom_of_symmetry(USym μ (a)) for all a, and the
   laws are stated with a · b ≔ USym(left a)(b). The pair (left,
   left_spec) is uniquely determined by μ (concrete_ring_left_unique), so
   this is the book's data up to a contractible choice. The algebra is
   proved for an arbitrary evaluation ev and then instantiated with
   hom_of_symmetry (only Hom-level comparisons, which are cheap);
   congruences use map_path instead of refl f p. `}

def concrete_ring_unit (C : CircleSignature) (R : AbelianGroup) (one : GroupHom (circle_group C) (R .fst)) : USym (R .fst)
  ≔ usym_hom (circle_group C) (R .fst) one (circle_group_loop C)

{` ℓ_a = ev ∘ USym μ (a) (footnote: USym Hom(R,R) ≃ Hom(R,R)). `}
def ConcreteRingLeftSpec (R : AbelianGroup) (μ : GroupHom (R .fst) (abelian_hom_group (R .fst) R))
  (left : USym (R .fst) → GroupHom (R .fst) (R .fst)) : Type
  ≔ (a : USym (R .fst))
    → Id (GroupHom (R .fst) (R .fst)) (left a) (hom_of_symmetry (R .fst) R (usym_hom (R .fst) (abelian_hom_group (R .fst) R) μ a))

{` RingProps(R, 1_R, μ), completed as described above (a · b ≔ USym(ℓ_a)(b)). `}
def ConcreteRingProps (C : CircleSignature) (R : AbelianGroup) (one : GroupHom (circle_group C) (R .fst))
  (μ : GroupHom (R .fst) (abelian_hom_group (R .fst) R)) (left : USym (R .fst) → GroupHom (R .fst) (R .fst)) : Type
  ≔ Product
      (Product
        (Id (GroupHom (R .fst) (R .fst))
          (hom_of_symmetry (R .fst) R
            (usym_hom (circle_group C) (abelian_hom_group (R .fst) R)
              (group_hom_compose (circle_group C) (R .fst) (abelian_hom_group (R .fst) R) one μ) (circle_group_loop C)))
          (group_hom_id (R .fst)))
        ((a : USym (R .fst)) → Id (USym (R .fst)) (usym_hom (R .fst) (R .fst) (left a) (concrete_ring_unit C R one)) a))
      ((a b c : USym (R .fst))
        → Id (USym (R .fst))
            (usym_hom (R .fst) (R .fst) (left a) (usym_hom (R .fst) (R .fst) (left b) c))
            (usym_hom (R .fst) (R .fst) (left (usym_hom (R .fst) (R .fst) (left a) b)) c))

{` def:ring. `}
def ConcreteRing (C : CircleSignature) : Type ≔ sig (
  group : AbelianGroup,
  one : GroupHom (circle_group C) (group .fst),
  mu : GroupHom (group .fst) (abelian_hom_group (group .fst) group),
  left : USym (group .fst) → GroupHom (group .fst) (group .fst),
  left_spec : ConcreteRingLeftSpec group mu left,
  props : ConcreteRingProps C group one mu left)

def concrete_ring_mul (C : CircleSignature) (R : ConcreteRing C) (a b : USym (R .group .fst)) : USym (R .group .fst)
  ≔ usym_hom (R .group .fst) (R .group .fst) (R .left a) b

{` The left multiplications are determined by μ. `}
def concrete_ring_left_unique (R : AbelianGroup) (μ : GroupHom (R .fst) (abelian_hom_group (R .fst) R))
  (l l' : USym (R .fst) → GroupHom (R .fst) (R .fst)) (h : ConcreteRingLeftSpec R μ l) (h' : ConcreteRingLeftSpec R μ l')
  : Id (USym (R .fst) → GroupHom (R .fst) (R .fst)) l l'
  ≔ funext (USym (R .fst)) (_ ↦ GroupHom (R .fst) (R .fst)) l l'
      (a ↦ concat (GroupHom (R .fst) (R .fst)) (l a)
        (hom_of_symmetry (R .fst) R (usym_hom (R .fst) (abelian_hom_group (R .fst) R) μ a)) (l' a)
        (h a)
        (inverse (GroupHom (R .fst) (R .fst)) (l' a)
          (hom_of_symmetry (R .fst) R (usym_hom (R .fst) (abelian_hom_group (R .fst) R) μ a)) (h' a)))

{` The trivial homomorphism: classified by the constant map at the shape. `}
def concrete_trivial_hom (G H : Group) : GroupHom G H ≔ mkhom G H (book_pointed_constant (BG G) (BG H))

def IsCommutativeConcreteRing (C : CircleSignature) (R : ConcreteRing C) : Type
  ≔ (a b : USym (R .group .fst)) → Id (USym (R .group .fst)) (concrete_ring_mul C R a b) (concrete_ring_mul C R b a)

def IsNonTrivialConcreteRing (C : CircleSignature) (R : ConcreteRing C) : Type
  ≔ Not (Id (GroupHom (circle_group C) (R .group .fst)) (R .one) (concrete_trivial_hom (circle_group C) (R .group .fst)))

{` Generic algebra with an arbitrary evaluation ev : USym H → Hom(G, G)
   (instantiated with ev = hom_of_symmetry) and left multiplications
   ℓ with ℓ(a) = ev(USym μ (a)). `}
def evaluation_left_unit (Z G H : Group) (one : GroupHom Z G) (μ : GroupHom G H) (ev : USym H → GroupHom G G)
  (l : USym Z) (h : Id (GroupHom G G) (ev (usym_hom Z H (group_hom_compose Z G H one μ) l)) (group_hom_id G))
  (ℓ : USym G → GroupHom G G) (hℓ : (a : USym G) → Id (GroupHom G G) (ℓ a) (ev (usym_hom G H μ a)))
  : Id (GroupHom G G) (ℓ (usym_hom Z G one l)) (group_hom_id G)
  ≔ let K ≔ GroupHom G G in
    calc
      ℓ (usym_hom Z G one l) = ev (usym_hom G H μ (usym_hom Z G one l)) by hℓ (usym_hom Z G one l)
      = ev (usym_hom Z H (group_hom_compose Z G H one μ) l)
        by map_path (USym H) K ev (usym_hom G H μ (usym_hom Z G one l)) (usym_hom Z H (group_hom_compose Z G H one μ) l)
          (inverse (USym H) (usym_hom Z H (group_hom_compose Z G H one μ) l) (usym_hom G H μ (usym_hom Z G one l))
            (refl ((φ ↦ φ l) : (USym Z → USym H) → USym H) (usym_hom_compose Z G H one μ)))
      = group_hom_id G by h ∎

{` (a + a') · b = a · b + a' · b when ev turns products into pointwise
   products. `}
def evaluation_rdistr (G H : Group) (μ : GroupHom G H) (ev : USym H → GroupHom G G)
  (hmul : (p q : USym H) (b : USym G)
    → Id (USym G) (usym_hom G G (ev (usym_mul H p q)) b) (usym_mul G (usym_hom G G (ev p) b) (usym_hom G G (ev q) b)))
  (ℓ : USym G → GroupHom G G) (hℓ : (a : USym G) → Id (GroupHom G G) (ℓ a) (ev (usym_hom G H μ a)))
  (a a' b : USym G)
  : Id (USym G) (usym_hom G G (ℓ (usym_mul G a a')) b) (usym_mul G (usym_hom G G (ℓ a) b) (usym_hom G G (ℓ a') b))
  ≔ let U ≔ USym G in
    let apb ≔ (f ↦ usym_hom G G f b) : GroupHom G G → U in
    calc
      usym_hom G G (ℓ (usym_mul G a a')) b = usym_hom G G (ev (usym_hom G H μ (usym_mul G a a'))) b
        by map_path (GroupHom G G) U apb (ℓ (usym_mul G a a')) (ev (usym_hom G H μ (usym_mul G a a'))) (hℓ (usym_mul G a a'))
      = usym_hom G G (ev (usym_mul H (usym_hom G H μ a) (usym_hom G H μ a'))) b
        by map_path (USym H) U (p ↦ usym_hom G G (ev p) b) (usym_hom G H μ (usym_mul G a a'))
          (usym_mul H (usym_hom G H μ a) (usym_hom G H μ a')) (usym_hom_mul G H μ a a')
      = usym_mul G (usym_hom G G (ev (usym_hom G H μ a)) b) (usym_hom G G (ev (usym_hom G H μ a')) b)
        by hmul (usym_hom G H μ a) (usym_hom G H μ a') b
      = usym_mul G (usym_hom G G (ℓ a) b) (usym_hom G G (ℓ a') b)
        by refl (usym_mul G)
          (map_path (GroupHom G G) U apb (ev (usym_hom G H μ a)) (ℓ a)
            (inverse (GroupHom G G) (ℓ a) (ev (usym_hom G H μ a)) (hℓ a)))
          (map_path (GroupHom G G) U apb (ev (usym_hom G H μ a')) (ℓ a')
            (inverse (GroupHom G G) (ℓ a') (ev (usym_hom G H μ a')) (hℓ a'))) ∎

{` An abstract ring on USym G from left multiplications L : USym G → Hom(G, G). `}
def left_multiplication_abstract_ring (G : Group) (L : USym G → GroupHom G G) (one : USym G)
  (unit_left : Id (GroupHom G G) (L one) (group_hom_id G))
  (unit_right : (a : USym G) → Id (USym G) (usym_hom G G (L a) one) a)
  (assoc : (a b c : USym G)
    → Id (USym G) (usym_hom G G (L a) (usym_hom G G (L b) c)) (usym_hom G G (L (usym_hom G G (L a) b)) c))
  (rdistr : (a a' b : USym G)
    → Id (USym G) (usym_hom G G (L (usym_mul G a a')) b) (usym_mul G (usym_hom G G (L a) b) (usym_hom G G (L a') b)))
  : AbstractRing
  ≔ (USym G, usym_unit G, usym_mul G, usym_inv G, usym_abstract_laws G,
     one, a b ↦ usym_hom G G (L a) b,
     (usym_set G,
      (a ↦ (unit_right a,
            concat (USym G) (usym_hom G G (L one) a) (usym_hom G G (group_hom_id G) a) a
              (map_path (GroupHom G G) (USym G) (f ↦ usym_hom G G f a) (L one) (group_hom_id G) unit_left)
              (usym_hom_id G a)),
       assoc)),
     (a b c ↦ usym_hom_mul G G (L a) b c, rdistr))

{` The printed unit law gives ℓ_1 = id_R, i.e. 1 · b = b. `}
def concrete_ring_left_unit (C : CircleSignature) (R : ConcreteRing C)
  : Id (GroupHom (R .group .fst) (R .group .fst)) (R .left (concrete_ring_unit C (R .group) (R .one))) (group_hom_id (R .group .fst))
  ≔ evaluation_left_unit (circle_group C) (R .group .fst) (abelian_hom_group (R .group .fst) (R .group)) (R .one) (R .mu)
      (hom_of_symmetry (R .group .fst) (R .group)) (circle_group_loop C) (R .props .fst .fst) (R .left) (R .left_spec)

{` Right distributivity (pointwise products in Hom(R, R), abelian_hom_usym_mul). `}
def concrete_ring_rdistr (C : CircleSignature) (R : ConcreteRing C) (a a' b : USym (R .group .fst))
  : Id (USym (R .group .fst)) (concrete_ring_mul C R (usym_mul (R .group .fst) a a') b)
      (usym_mul (R .group .fst) (concrete_ring_mul C R a b) (concrete_ring_mul C R a' b))
  ≔ evaluation_rdistr (R .group .fst) (abelian_hom_group (R .group .fst) (R .group)) (R .mu)
      (hom_of_symmetry (R .group .fst) (R .group)) (abelian_hom_usym_mul (R .group .fst) (R .group))
      (R .left) (R .left_spec) a a' b

{` Right multiplication by b is an abstract endomorphism of abstr(R). `}
def concrete_ring_right_hom (C : CircleSignature) (R : ConcreteRing C) (b : USym (R .group .fst))
  : AbstractHom (abstr (R .group .fst)) (abstr (R .group .fst))
  ≔ (a ↦ concrete_ring_mul C R a b, a a' ↦ concrete_ring_rdistr C R a a' b)

{` xca:Rconcring->URabstring: USym R is an abstract ring with additive
   group abstr(R) and multiplicative monoid (USym R, USym 1_R (loop), ·),
   where a · b = USym(ℓ_a)(b) = USym(ev ∘ USym μ (a))(b). `}
def concrete_ring_abstract_ring (C : CircleSignature) (R : ConcreteRing C) : AbstractRing
  ≔ left_multiplication_abstract_ring (R .group .fst) (R .left) (concrete_ring_unit C (R .group) (R .one))
      (concrete_ring_left_unit C R) (R .props .fst .snd) (R .props .snd) (concrete_ring_rdistr C R)

def concrete_ring_additive_is_abstr (C : CircleSignature) (R : ConcreteRing C)
  : Id AbstractGroup (ring_additive_group (concrete_ring_abstract_ring C R)) (abstr (R .group .fst))
  ≔ refl (abstr (R .group .fst))

def concrete_ring_abstract_commutative (C : CircleSignature) (R : ConcreteRing C) (h : IsCommutativeConcreteRing C R)
  : IsCommutativeRing (concrete_ring_abstract_ring C R)
  ≔ h

{` If 1 = USym 1_R (loop) were refl, 1_R would be trivial (homomorphisms
   out of ℤ are determined by their value at loop, module 435). `}
def concrete_ring_abstract_non_trivial (C : CircleSignature) (R : ConcreteRing C) (h : IsNonTrivialConcreteRing C R)
  : IsNonTrivialRing (concrete_ring_abstract_ring C R)
  ≔ p ↦
    let G ≔ R .group .fst in let Z ≔ circle_group C in
    h (equivalence_injective (GroupHom Z G) (USym G) (circle_group_hom_ev C G) (R .one) (concrete_trivial_hom Z G)
        (concat (USym G) (usym_hom Z G (R .one) (circle_group_loop C)) (usym_unit G)
          (usym_hom Z G (concrete_trivial_hom Z G) (circle_group_loop C))
          (inverse (USym G) (usym_unit G) (usym_hom Z G (R .one) (circle_group_loop C)) p)
          (inverse (USym G) (usym_hom Z G (concrete_trivial_hom Z G) (circle_group_loop C)) (usym_unit G)
            (circle_group_hom_ev_trivial C G))))
