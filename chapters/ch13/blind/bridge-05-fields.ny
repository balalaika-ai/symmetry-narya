export "05-fields"
export "bridge-01-abstract-rings"
export "../../../src/1301-fields"

{` Bridges for the fields part of fields.tex (blocks 1239, 1244, 1253, 1263, 1268, 1273; 1259 is a
   terminology remark). Only difference: the blind isNonTrivialCRing is (non-trivial × commutative), ours
   (commutative × non-trivial); the swap gives equivalences with refl round trips. isInvertible is the same type by
   refl. The theorem (1244) and the "equivalently" sentence of 1253 follow from ours. `}

def b05_nt_to (R : BlindAbsRing) (h : BlindIsNonTrivialCRing R) : IsNonTrivialCRing (b01_ring R)
  ≔ (h .snd, h .fst)

def b05_nt_from (R : BlindAbsRing) (h : IsNonTrivialCRing (b01_ring R)) : BlindIsNonTrivialCRing R
  ≔ (h .snd, h .fst)

def bridge_def_non_trivial_cring (R : BlindAbsRing)
  : Equiv (BlindIsNonTrivialCRing R) (IsNonTrivialCRing (b01_ring R))
  ≔ quasi_inverse_equiv (BlindIsNonTrivialCRing R) (IsNonTrivialCRing (b01_ring R)) (b05_nt_to R) (b05_nt_from R)
      (h ↦ refl h) (h ↦ refl h)

{` isInvertible (1239). `}
def bridge_def_is_invertible (R : BlindAbsRing) (e : R .add .carrier)
  : Id Type (BlindIsInvertible R e) (IsInvertible (b01_ring R) e)
  ≔ refl (IsInvertible (b01_ring R) e)

{` Theorem (1244), and the converse (ours from blind). `}
def bridge_zero_not_invertible : blind_zero_not_invertible
  ≔ R h ↦ zero_not_invertible (b01_ring R) (b05_nt_to R h)

def bridge_zero_not_invertible_converse (h : blind_zero_not_invertible) (R : AbstractRing)
  (n : IsNonTrivialCRing R) : Not (IsInvertible R (R .zero))
  ≔ h (b01_blind_ring R) (n .snd, n .fst)

{` isField (1253). `}
def b05_field_to (R : BlindAbsRing) (h : BlindIsField R) : IsField (b01_ring R) ≔ (b05_nt_to R (h .fst), h .snd)

def b05_field_from (R : BlindAbsRing) (h : IsField (b01_ring R)) : BlindIsField R ≔ (b05_nt_from R (h .fst), h .snd)

def bridge_def_is_field (R : BlindAbsRing) : Equiv (BlindIsField R) (IsField (b01_ring R))
  ≔ quasi_inverse_equiv (BlindIsField R) (IsField (b01_ring R)) (b05_field_to R) (b05_field_from R)
      (h ↦ refl h) (h ↦ refl h)

def b05_to_field (K : BlindField) : Field ≔ (b01_ring (K .fst), b05_field_to (K .fst) (K .snd))

def b05_from_field (K : Field) : BlindField ≔ (b01_blind_ring (K .fst), b05_field_from (b01_blind_ring (K .fst)) (K .snd))

def bridge_def_field : Equiv BlindField Field
  ≔ quasi_inverse_equiv BlindField Field b05_to_field b05_from_field (K ↦ refl K) (K ↦ refl K)

def bridge_field_iff_noninvertible_zero : blind_field_iff_noninvertible_zero
  ≔ R n ↦ (h ↦ field_non_invertible_zero (b01_ring R) (b05_field_to R h),
           k ↦ b05_field_from R (field_from_non_invertible_zero (b01_ring R) (b05_nt_to R n) k))

{` Discrete fields (1263), local rings (1268), Heyting fields (1273). `}
def bridge_def_is_discrete_field (R : BlindAbsRing) : Equiv (BlindIsDiscreteField R) (IsDiscreteField (b01_ring R))
  ≔ quasi_inverse_equiv (BlindIsDiscreteField R) (IsDiscreteField (b01_ring R))
      (h ↦ (b05_field_to R (h .fst), h .snd)) (h ↦ (b05_field_from R (h .fst), h .snd))
      (h ↦ refl h) (h ↦ refl h)

def bridge_def_is_local_ring (R : BlindAbsRing) : Equiv (BlindIsLocalRing R) (IsLocalRing (b01_ring R))
  ≔ quasi_inverse_equiv (BlindIsLocalRing R) (IsLocalRing (b01_ring R))
      (h ↦ (b05_nt_to R (h .fst), h .snd)) (h ↦ (b05_nt_from R (h .fst), h .snd))
      (h ↦ refl h) (h ↦ refl h)

def bridge_def_is_heyting_field (R : BlindAbsRing) : Equiv (BlindIsHeytingField R) (IsHeytingField (b01_ring R))
  ≔ quasi_inverse_equiv (BlindIsHeytingField R) (IsHeytingField (b01_ring R))
      (h ↦ (b05_field_to R (h .fst), (b05_nt_to R (h .snd .fst), h .snd .snd)))
      (h ↦ (b05_field_from R (h .fst), (b05_nt_from R (h .snd .fst), h .snd .snd)))
      (h ↦ refl h) (h ↦ refl h)
