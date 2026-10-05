export "02-mixed-rings"
export "bridge-01-abstract-rings"
export "../../../src/1361-integer-mixed-ring"

{` Bridges for sec:mixring (blocks 112, 143, 157, 167). The blind RingProps is a 4-field record, ours
   (MixedRingProps) nested products with the same four laws (same corrected readings: id_G = id_R, pointwise
   associativity ℓ_g ∘ r_h = r_h ∘ ℓ_g); the conversions are inverse by refl. The blind ℓ of the integer example is
   our integer_mixed_left by refl. xca:Rmixring->URabstring with the blind's choice g · h = (USym ℓ_g)(h) is exactly
   our mixed_ring_abstract_ring. `}

def b02_props_to (R : Group) (one : USym R) (l r : USym R → GroupHom R R) (p : BlindRingProps R one l r)
  : MixedRingProps R one l r
  ≔ ((p .unit_left, p .unit_right), (p .coherence, p .assoc))

def b02_props_from (R : Group) (one : USym R) (l r : USym R → GroupHom R R) (p : MixedRingProps R one l r)
  : BlindRingProps R one l r
  ≔ (p .fst .fst, p .fst .snd, p .snd .fst, p .snd .snd)

def bridge_def_ring_props (R : Group) (one : USym R) (l r : USym R → GroupHom R R)
  : Equiv (BlindRingProps R one l r) (MixedRingProps R one l r)
  ≔ quasi_inverse_equiv (BlindRingProps R one l r) (MixedRingProps R one l r)
      (b02_props_to R one l r) (b02_props_from R one l r) (p ↦ refl p) (p ↦ refl p)

def b02_ring (R : BlindMixRing) : MixedRing
  ≔ (R .grp, R .one, R .l, R .r, b02_props_to (R .grp) (R .one) (R .l) (R .r) (R .props))

def b02_blind_ring (R : MixedRing) : BlindMixRing
  ≔ (R .group, R .one, R .left, R .right, b02_props_from (R .group) (R .one) (R .left) (R .right) (R .props))

{` def:mixring (112). `}
def bridge_def_mixring : Equiv BlindMixRing MixedRing
  ≔ quasi_inverse_equiv BlindMixRing MixedRing b02_ring b02_blind_ring (R ↦ refl R) (R ↦ refl R)

def bridge_def_mixring_commutative (R : BlindMixRing)
  : Id Type (BlindMixRingCommutative R) (IsCommutativeMixedRing (b02_ring R))
  ≔ refl (IsCommutativeMixedRing (b02_ring R))

def bridge_def_mixring_non_trivial (R : BlindMixRing)
  : Id Type (BlindMixRingNonTrivial R) (IsNonTrivialMixedRing (b02_ring R))
  ≔ refl (IsNonTrivialMixedRing (b02_ring R))

def bridge_mixring_group_abelian : blind_mixring_group_abelian ≔ R ↦ mixed_ring_group_abelian (b02_ring R)

def bridge_mixring_group_abelian_converse (h : blind_mixring_group_abelian) (R : MixedRing) : IsAbelian (R .group)
  ≔ h (b02_blind_ring R)

{` Example (143): the blind ℓ is ours by refl, and the claim follows from integer_mixed_ring. `}
def bridge_def_circle_ell (C : CircleSignature) (g : USym (circle_group C))
  : Id (GroupHom (circle_group C) (circle_group C)) (blind_circle_ell C g) (integer_mixed_left C g)
  ≔ refl (integer_mixed_left C g)

def bridge_mixring_integers : blind_mixring_integers
  ≔ C ↦ (b02_props_from (circle_group C) (C .loop) (integer_mixed_left C) (integer_mixed_left C)
           (integer_mixed_ring C .props),
         (integer_mixed_ring_non_trivial C, integer_mixed_ring_commutative C))

{` def:typemixring (157). `}
def bridge_def_type_mixring : Equiv BlindTypeMixRing MixedRingSigma
  ≔ quasi_inverse_equiv BlindTypeMixRing MixedRingSigma
      (t ↦ (t .fst, (t .snd .fst, (t .snd .snd .fst, (t .snd .snd .snd .fst,
             b02_props_to (t .fst) (t .snd .fst) (t .snd .snd .fst) (t .snd .snd .snd .fst) (t .snd .snd .snd .snd))))))
      (t ↦ (t .fst, (t .snd .fst, (t .snd .snd .fst, (t .snd .snd .snd .fst,
             b02_props_from (t .fst) (t .snd .fst) (t .snd .snd .fst) (t .snd .snd .snd .fst) (t .snd .snd .snd .snd))))))
      (t ↦ refl t) (t ↦ refl t)

def bridge_def_type_mixcommring : Equiv BlindTypeMixCommRing CommutativeMixedRingSigma
  ≔ quasi_inverse_equiv BlindTypeMixCommRing CommutativeMixedRingSigma
      (t ↦ (t .fst, (t .snd .fst, (t .snd .snd .fst, (t .snd .snd .snd .fst,
             (b02_props_to (t .fst) (t .snd .fst) (t .snd .snd .fst) (t .snd .snd .snd .fst) (t .snd .snd .snd .snd .fst),
              t .snd .snd .snd .snd .snd))))))
      (t ↦ (t .fst, (t .snd .fst, (t .snd .snd .fst, (t .snd .snd .snd .fst,
             (b02_props_from (t .fst) (t .snd .fst) (t .snd .snd .fst) (t .snd .snd .snd .fst) (t .snd .snd .snd .snd .fst),
              t .snd .snd .snd .snd .snd))))))
      (t ↦ refl t) (t ↦ refl t)

{` xca:Rmixring->URabstring (167). `}
def bridge_def_mixring_mul (R : BlindMixRing) (g h : USym (R .grp))
  : Id (USym (R .grp)) (blind_mixring_mul R g h) (mixed_mul (b02_ring R) g h)
  ≔ refl (mixed_mul (b02_ring R) g h)

def bridge_mixring_abstract_ring : blind_mixring_abstract_ring
  ≔ R ↦ (mixed_ring_abstract_ring (b02_ring R) .mul_laws, mixed_ring_abstract_ring (b02_ring R) .distr)

def bridge_mixring_abstract_ring_additive (R : BlindMixRing)
  : Id AbstractGroup (ring_additive_group (mixed_ring_abstract_ring (b02_ring R))) (abstr (R .grp))
  ≔ refl (abstr (R .grp))
