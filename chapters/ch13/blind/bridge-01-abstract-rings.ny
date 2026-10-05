export "01-abstract-rings"
export "../../../src/1300-abstract-rings"

{` Bridges for fields.tex sec:abstrings (blocks 38, 59, 71, 76; 89 is a TBD stub). The blind record
   BlindAbsRing nests the additive AbstractGroup, ours (AbstractRing) is flat; the two conversions are inverse by
   refl (records have η). Distributive laws, commutativity, non-triviality, the iterated Σ of def:typering and ring
   homomorphisms agree by refl along the conversion. `}

def b01_ring (R : BlindAbsRing) : AbstractRing
  ≔ (R .add .carrier, R .add .unit, R .add .mul, R .add .inv, R .add .laws, R .one, R .mul, R .monoid, R .distr)

def b01_blind_ring (R : AbstractRing) : BlindAbsRing
  ≔ (ring_additive_group R, R .one, R .mul, R .mul_laws, R .distr)

{` def:abstractring (38). `}
def bridge_def_distr_laws (R : Type) (mul add : R → R → R)
  : Id Type (BlindDistrLaws R mul add) (DistrLaws R mul add)
  ≔ refl (DistrLaws R mul add)

def bridge_def_absring : Equiv BlindAbsRing AbstractRing
  ≔ quasi_inverse_equiv BlindAbsRing AbstractRing b01_ring b01_blind_ring (R ↦ refl R) (R ↦ refl R)

def bridge_def_absring_monoid (R : BlindAbsRing)
  : Id Monoid (blind_absring_monoid R) (ring_monoid (b01_ring R))
  ≔ refl (ring_monoid (b01_ring R))

def bridge_def_absring_additive (R : BlindAbsRing)
  : Id AbstractGroup (R .add) (ring_additive_group (b01_ring R))
  ≔ refl (R .add)

def bridge_def_absring_non_trivial (R : BlindAbsRing)
  : Id Type (BlindAbsRingNonTrivial R) (IsNonTrivialRing (b01_ring R))
  ≔ refl (IsNonTrivialRing (b01_ring R))

def bridge_def_absring_commutative (R : BlindAbsRing)
  : Id Type (BlindAbsRingCommutative R) (IsCommutativeRing (b01_ring R))
  ≔ refl (IsCommutativeRing (b01_ring R))

{` def:typering (59): both iterated Σ-types are ours by refl. `}
def bridge_def_type_ring : Id Type BlindTypeRing AbstractRingSigma ≔ refl AbstractRingSigma

def bridge_def_type_ring_record : Equiv BlindTypeRing AbstractRing
  ≔ quasi_inverse_equiv BlindTypeRing AbstractRing abstract_ring_from_sigma abstract_ring_to_sigma
      (t ↦ refl t) (R ↦ refl R)

def bridge_def_type_comm_ring : Equiv BlindTypeCommRing CommutativeRing
  ≔ quasi_inverse_equiv BlindTypeCommRing CommutativeRing
      (t ↦ ((t .fst .carrier, t .fst .unit, t .fst .mul, t .fst .inv, t .fst .laws,
             t .snd .fst, t .snd .snd .fst, t .snd .snd .snd .fst, t .snd .snd .snd .snd .fst),
            t .snd .snd .snd .snd .snd))
      (R ↦ (ring_additive_group (R .fst), (R .fst .one, (R .fst .mul, (R .fst .mul_laws, (R .fst .distr, R .snd))))))
      (t ↦ refl t) (R ↦ refl R)

{` xca:ring-group-abelian (71), and the converse. `}
def bridge_ring_group_abelian : blind_ring_group_abelian ≔ R ↦ ring_additive_abelian (b01_ring R)

def bridge_ring_group_abelian_converse (h : blind_ring_group_abelian) (R : AbstractRing)
  : IsAbstractAbelian (ring_additive_group R)
  ≔ h (b01_blind_ring R)

{` def:ringhom (76). `}
def bridge_def_is_ring_monoid_hom (R S : BlindAbsRing) (f : R .add .carrier → S .add .carrier)
  : Id Type (BlindIsRingMonoidHom R S f)
      (Product (Id (S .add .carrier) (f (R .one)) (S .one))
        ((s s' : R .add .carrier) → Id (S .add .carrier) (f (R .mul s s')) (S .mul (f s) (f s'))))
  ≔ refl (BlindIsRingMonoidHom R S f)

def bridge_def_absring_hom (R S : BlindAbsRing)
  : Id Type (BlindAbsRingHom R S) (RingHom (b01_ring R) (b01_ring S))
  ≔ refl (RingHom (b01_ring R) (b01_ring S))
