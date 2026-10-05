export "1300-abstract-rings"
export "710-hom-delooping"

{` Chapter 13 (fields.tex 94-172), sec:mixring. Mixed rings: a (concrete)
   group R with a symmetry 1_R : USym R and maps ℓ, r : USym R → Hom(R, R)
   (def:mixring), the type of mixed rings (def:typemixring), the
   abbreviation g · h (running text 135-139) and xca:Rmixring->URabstring
   (USym R is an abstract ring with additive group abstr(R)).

   Corrections to the printed definition. (1) The unit law reads
   "ℓ_{1_R} = id_G = r_{1_R}"; G is R. (2) The associativity law is printed
   "ℓ ∘ r = r ∘ ℓ", which does not type-check (ℓ, r : USym R → Hom(R,R));
   the intended law, used in xca:Rmixring->URabstring, is
   ℓ_g ∘ r_h = r_h ∘ ℓ_g in Hom(R,R) for all g, h (i.e. g(xh) = (gx)h).
   Composition of homomorphisms is group_hom_compose (first argument
   first), so ℓ_g ∘ r_h is group_hom_compose R R R (r h) (ℓ g). `}

def MixedRingProps (R : Group) (one : USym R) (l r : USym R → GroupHom R R) : Type
  ≔ Product (Product (Id (GroupHom R R) (l one) (group_hom_id R)) (Id (GroupHom R R) (r one) (group_hom_id R)))
      (Product ((g h : USym R) → Id (USym R) (usym_hom R R (l g) h) (usym_hom R R (r h) g))
        ((g h : USym R) → Id (GroupHom R R) (group_hom_compose R R R (r h) (l g)) (group_hom_compose R R R (l g) (r h))))

{` def:mixring. `}
def MixedRing : Type ≔ sig (
  group : Group,
  one : USym group,
  left : USym group → GroupHom group group,
  right : USym group → GroupHom group group,
  props : MixedRingProps group one left right)

def mixed_ring_left_unit (R : MixedRing) : Id (GroupHom (R .group) (R .group)) (R .left (R .one)) (group_hom_id (R .group))
  ≔ R .props .fst .fst

def mixed_ring_right_unit (R : MixedRing) : Id (GroupHom (R .group) (R .group)) (R .right (R .one)) (group_hom_id (R .group))
  ≔ R .props .fst .snd

def mixed_ring_coherence (R : MixedRing) (g h : USym (R .group))
  : Id (USym (R .group)) (usym_hom (R .group) (R .group) (R .left g) h) (usym_hom (R .group) (R .group) (R .right h) g)
  ≔ R .props .snd .fst g h

def mixed_ring_assoc (R : MixedRing) (g h : USym (R .group))
  : Id (GroupHom (R .group) (R .group))
      (group_hom_compose (R .group) (R .group) (R .group) (R .right h) (R .left g))
      (group_hom_compose (R .group) (R .group) (R .group) (R .left g) (R .right h))
  ≔ R .props .snd .snd g h

{` Commutative: ℓ = r. Non-trivial: 1_R ≠ refl. `}
def IsCommutativeMixedRing (R : MixedRing) : Type
  ≔ Id (USym (R .group) → GroupHom (R .group) (R .group)) (R .left) (R .right)

def IsNonTrivialMixedRing (R : MixedRing) : Type ≔ Not (Id (USym (R .group)) (R .one) (usym_unit (R .group)))

{` def:typemixring: the iterated Σ, and commutative mixed rings. `}
def MixedRingSigma : Type
  ≔ Σ Group (R ↦ Σ (USym R) (one ↦ Σ (USym R → GroupHom R R) (l ↦ Σ (USym R → GroupHom R R) (r ↦
      MixedRingProps R one l r))))

def mixed_ring_sigma_equiv : Equiv MixedRing MixedRingSigma
  ≔ quasi_inverse_equiv MixedRing MixedRingSigma
      (R ↦ (R .group, (R .one, (R .left, (R .right, R .props)))))
      (t ↦ (t .fst, t .snd .fst, t .snd .snd .fst, t .snd .snd .snd .fst, t .snd .snd .snd .snd))
      (R ↦ refl R) (t ↦ refl t)

def CommutativeMixedRingSigma : Type
  ≔ Σ Group (R ↦ Σ (USym R) (one ↦ Σ (USym R → GroupHom R R) (l ↦ Σ (USym R → GroupHom R R) (r ↦
      Product (MixedRingProps R one l r) (Id (USym R → GroupHom R R) l r)))))

def CommutativeMixedRing : Type ≔ Σ MixedRing IsCommutativeMixedRing

def commutative_mixed_ring_sigma_equiv : Equiv CommutativeMixedRing CommutativeMixedRingSigma
  ≔ quasi_inverse_equiv CommutativeMixedRing CommutativeMixedRingSigma
      (R ↦ (R .fst .group, (R .fst .one, (R .fst .left, (R .fst .right, (R .fst .props, R .snd))))))
      (t ↦ ((t .fst, t .snd .fst, t .snd .snd .fst, t .snd .snd .snd .fst, t .snd .snd .snd .snd .fst),
            t .snd .snd .snd .snd .snd))
      (R ↦ refl R) (t ↦ refl t)

{` The abbreviation g · h ≔ (USym ℓ_g)(h) = (USym r_h)(g) (running text). `}
def mixed_mul (R : MixedRing) (g h : USym (R .group)) : USym (R .group)
  ≔ usym_hom (R .group) (R .group) (R .left g) h

{` Homomorphisms are determined by their action on symmetries (from
   lem:homomabstrconcr, module 710). `}
def group_hom_from_usym_agreement (G H : Group) (f f' : GroupHom G H)
  (e : (g : USym G) → Id (USym H) (usym_hom G H f g) (usym_hom G H f' g)) : Id (GroupHom G H) f f'
  ≔ let D ≔ GroupHom G H in
    concat D f (deloop_hom G H (abstr_hom G H f)) f'
      (inverse D (deloop_hom G H (abstr_hom G H f)) f (deloop_hom_retraction G H f))
      (concat D (deloop_hom G H (abstr_hom G H f)) (deloop_hom G H (abstr_hom G H f')) f'
        (refl (deloop_hom G H)
          (abstract_hom_ext (abstr G) (abstr H) (abstr_hom G H f) (abstr_hom G H f') e))
        (deloop_hom_retraction G H f'))

{` Running text 137-139: "ℓ = r amounts to g · h = h · g for all g, h". `}
def mixed_commutative_to_mul_comm (R : MixedRing) (c : IsCommutativeMixedRing R) (g h : USym (R .group))
  : Id (USym (R .group)) (mixed_mul R g h) (mixed_mul R h g)
  ≔ let G ≔ R .group in
    concat (USym G) (mixed_mul R g h) (usym_hom G G (R .right g) h) (mixed_mul R h g)
      (refl ((L ↦ usym_hom G G (L g) h) : (USym G → GroupHom G G) → USym G) c)
      (inverse (USym G) (mixed_mul R h g) (usym_hom G G (R .right g) h) (mixed_ring_coherence R h g))

def mixed_mul_comm_to_commutative (R : MixedRing)
  (c : (g h : USym (R .group)) → Id (USym (R .group)) (mixed_mul R g h) (mixed_mul R h g))
  : IsCommutativeMixedRing R
  ≔ let G ≔ R .group in
    funext (USym G) (_ ↦ GroupHom G G) (R .left) (R .right)
      (g ↦ group_hom_from_usym_agreement G G (R .left g) (R .right g)
        (h ↦ concat (USym G) (mixed_mul R g h) (mixed_mul R h g) (usym_hom G G (R .right g) h)
          (c g h) (mixed_ring_coherence R h g)))

{` xca:Rmixring->URabstring: USym R is an abstract ring with additive
   group abstr(R) and multiplicative monoid (USym R, 1_R, ·). `}
def mixed_mul_one_right (R : MixedRing) (g : USym (R .group))
  : Id (USym (R .group)) (mixed_mul R g (R .one)) g
  ≔ let G ≔ R .group in
    calc
      mixed_mul R g (R .one) = usym_hom G G (R .right (R .one)) g by mixed_ring_coherence R g (R .one)
      = usym_hom G G (group_hom_id G) g
        by refl ((f ↦ usym_hom G G f g) : GroupHom G G → USym G) (mixed_ring_right_unit R)
      = g by usym_hom_id G g ∎

def mixed_mul_one_left (R : MixedRing) (g : USym (R .group))
  : Id (USym (R .group)) (mixed_mul R (R .one) g) g
  ≔ let G ≔ R .group in
    concat (USym G) (mixed_mul R (R .one) g) (usym_hom G G (group_hom_id G) g) g
      (refl ((f ↦ usym_hom G G f g) : GroupHom G G → USym G) (mixed_ring_left_unit R))
      (usym_hom_id G g)

def mixed_mul_assoc (R : MixedRing) (a b c : USym (R .group))
  : Id (USym (R .group)) (mixed_mul R a (mixed_mul R b c)) (mixed_mul R (mixed_mul R a b) c)
  ≔ let G ≔ R .group in let U ≔ USym G in
    let la ≔ R .left a in let rc ≔ R .right c in
    calc
      mixed_mul R a (mixed_mul R b c) = usym_hom G G la (usym_hom G G rc b)
        by refl (usym_hom G G la) (mixed_ring_coherence R b c)
      = usym_hom G G (group_hom_compose G G G rc la) b
        by inverse U (usym_hom G G (group_hom_compose G G G rc la) b) (usym_hom G G la (usym_hom G G rc b))
          (refl ((φ ↦ φ b) : (U → U) → U) (usym_hom_compose G G G rc la))
      = usym_hom G G (group_hom_compose G G G la rc) b
        by refl ((f ↦ usym_hom G G f b) : GroupHom G G → U) (mixed_ring_assoc R a c)
      = usym_hom G G rc (usym_hom G G la b)
        by refl ((φ ↦ φ b) : (U → U) → U) (usym_hom_compose G G G la rc)
      = mixed_mul R (mixed_mul R a b) c
        by inverse U (mixed_mul R (mixed_mul R a b) c) (usym_hom G G rc (mixed_mul R a b))
          (mixed_ring_coherence R (mixed_mul R a b) c) ∎

def mixed_rdistr (R : MixedRing) (a b c : USym (R .group))
  : Id (USym (R .group)) (mixed_mul R (usym_mul (R .group) a b) c)
      (usym_mul (R .group) (mixed_mul R a c) (mixed_mul R b c))
  ≔ let G ≔ R .group in let U ≔ USym G in let rc ≔ R .right c in
    calc
      mixed_mul R (usym_mul G a b) c = usym_hom G G rc (usym_mul G a b) by mixed_ring_coherence R (usym_mul G a b) c
      = usym_mul G (usym_hom G G rc a) (usym_hom G G rc b) by usym_hom_mul G G rc a b
      = usym_mul G (mixed_mul R a c) (mixed_mul R b c)
        by refl (usym_mul G)
          (inverse U (mixed_mul R a c) (usym_hom G G rc a) (mixed_ring_coherence R a c))
          (inverse U (mixed_mul R b c) (usym_hom G G rc b) (mixed_ring_coherence R b c)) ∎

def mixed_ring_abstract_ring (R : MixedRing) : AbstractRing
  ≔ let G ≔ R .group in
    (USym G, usym_unit G, usym_mul G, usym_inv G, usym_abstract_laws G,
     R .one, mixed_mul R,
     (usym_set G, (g ↦ (mixed_mul_one_right R g, mixed_mul_one_left R g), mixed_mul_assoc R)),
     (a b c ↦ usym_hom_mul G G (R .left a) b c, mixed_rdistr R))

def mixed_ring_additive_is_abstr (R : MixedRing)
  : Id AbstractGroup (ring_additive_group (mixed_ring_abstract_ring R)) (abstr (R .group))
  ≔ refl (abstr (R .group))

{` Footnote to def:mixring: "it will follow as in xca:ring-group-abelian
   that the group R is abelian". `}
def mixed_ring_group_abelian (R : MixedRing) : IsAbelian (R .group)
  ≔ ring_additive_abelian (mixed_ring_abstract_ring R)

{` A commutative mixed ring gives a commutative abstract ring; a
   non-trivial one a non-trivial abstract ring (0 = refl, 1 = 1_R). `}
def mixed_ring_abstract_commutative (R : MixedRing) (c : IsCommutativeMixedRing R)
  : IsCommutativeRing (mixed_ring_abstract_ring R)
  ≔ mixed_commutative_to_mul_comm R c

def mixed_ring_abstract_non_trivial (R : MixedRing) (h : IsNonTrivialMixedRing R)
  : IsNonTrivialRing (mixed_ring_abstract_ring R)
  ≔ p ↦ h (inverse (USym (R .group)) (usym_unit (R .group)) (R .one) p)
