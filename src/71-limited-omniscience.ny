export "70-classical-principles"

{` Numeric Fin 2: the right summand is zero in fin_below_equiv. `}
def Bit : Type ≔ Fin (suc. (suc. zero.))
def bit_zero : Bit ≔ inr. star.
def bit_one : Bit ≔ inl. (inr. star.)
def bit_set : isSet Bit ≔ fin_set (suc. (suc. zero.))

def bit_zero_index : Id Nat (fin_below_equiv (suc. (suc. zero.)) .map bit_zero .fst) zero.
  ≔ refl zero.
def bit_one_index : Id Nat (fin_below_equiv (suc. (suc. zero.)) .map bit_one .fst) (suc. zero.)
  ≔ refl (suc. zero.)

def bit_zero_ne_one (p : Id Bit bit_zero bit_one) : Empty
  ≔ bool_encode true. false. (refl fin_two_to_bool p)

def bit_cases (b : Bit) : Sum (Id Bit b bit_zero) (Id Bit b bit_one)
  ≔ match b [
  | inl. (inl. x) ↦ match x []
  | inl. (inr. u) ↦ inr. (inl. (inr. (unit_prop u star.)))
  | inr. u ↦ inl. (inr. (unit_prop u star.)) ]

def bit_not_one_zero (b : Bit) (no : Id Bit b bit_one → Empty) : Id Bit b bit_zero
  ≔ match bit_cases b [ inl. p ↦ p | inr. p ↦ absurd (Id Bit b bit_zero) (no p) ]

def BitHit (P : Nat → Bit) (n : Nat) : Type ≔ Id Bit (P n) bit_one
def bit_hit_decidable (P : Nat → Bit) (n : Nat) : Decidable (BitHit P n)
  ≔ fin_decidable_equality (suc. (suc. zero.)) (P n) bit_one
def BitMinimum (P : Nat → Bit) : Type ≔ Σ Nat (IsMinimum (BitHit P))
def BitConstantZero (P : Nat → Bit) : Type ≔ Id (Nat → Bit) P (_ ↦ bit_zero)
def LPOInstance (P : Nat → Bit) : Type ≔ Sum (BitMinimum P) (BitConstantZero P)

def bit_minimum_not_zero (P : Nat → Bit) (m : BitMinimum P) (z : BitConstantZero P) : Empty
  ≔ bit_zero_ne_one (concat Bit bit_zero (P (m .fst)) bit_one
      (inverse Bit (P (m .fst)) bit_zero (z (refl (m .fst)))) (m .snd .fst))

def lpo_instance_prop (P : Nat → Bit) : isProp (LPOInstance P)
  ≔ disjoint_sum_prop (BitMinimum P) (BitConstantZero P)
      (minimum_prop (BitHit P) (n ↦ bit_set (P n) bit_one))
      (pi_set Nat (_ ↦ Bit) (_ ↦ bit_set) P (_ ↦ bit_zero)) (bit_minimum_not_zero P)

{` LPO is a type of additional principles. No inhabitant is postulated. `}
def LimitedOmniscience : Type ≔ (P : Nat → Bit) → LPOInstance P
def limited_omniscience_prop : isProp LimitedOmniscience
  ≔ pi_prop (Nat → Bit) LPOInstance lpo_instance_prop

def no_bit_hit_constant_zero (P : Nat → Bit) (no : (n : Nat) → BitHit P n → Empty) : BitConstantZero P
  ≔ funext Nat (_ ↦ Bit) P (_ ↦ bit_zero) (n ↦ bit_not_one_zero (P n) (no n))

def excluded_middle_implies_lpo (lem : ExcludedMiddle) : LimitedOmniscience
  ≔ P ↦ match lem (Mere (Σ Nat (BitHit P))) (mere_isprop (Σ Nat (BitHit P))) [
  | inl. hit ↦ inl. (least_number (BitHit P) (n ↦ bit_set (P n) bit_one) (bit_hit_decidable P) hit)
  | inr. no ↦ inr. (no_bit_hit_constant_zero P (n p ↦ no (mere (Σ Nat (BitHit P)) (n, p)))) ]

{` xca:not-not-lpoP. This is pointwise double negation, not a proof of LPO. `}
def double_negated_lpo_instance (P : Nat → Bit) : Not (Not (LPOInstance P))
  ≔ no ↦ no (inr. (no_bit_hit_constant_zero P
      (n p ↦ no (inl. (minimum_from_witness (BitHit P) (bit_hit_decidable P) n p)))))

def decision_bit (P : Type) (d : Decidable P) : Bit ≔ match d [ inl. p ↦ bit_one | inr. no ↦ bit_zero ]
def decision_bit_yes (P : Type) (d : Decidable P) (p : P) : Id Bit (decision_bit P d) bit_one
  ≔ match d [ inl. q ↦ refl bit_one | inr. no ↦ absurd (Id Bit bit_zero bit_one) (no p) ]
def decision_bit_sound (P : Type) (d : Decidable P) (p : Id Bit (decision_bit P d) bit_one) : P
  ≔ match d [ inl. q ↦ q | inr. no ↦ absurd P (bit_zero_ne_one p) ]

def DecidableSearchResult (P : Nat → Type) : Type
  ≔ Sum (Σ Nat (IsMinimum P)) ((n : Nat) → P n → Empty)

{` A reusable form for the decidable positive-period predicate of a cycle. `}
def lpo_decidable_search (lpo : LimitedOmniscience) (P : Nat → Type) (d : (n : Nat) → Decidable (P n))
  : DecidableSearchResult P
  ≔ match lpo (n ↦ decision_bit (P n) (d n)) [
  | inl. m ↦ inl. (m .fst, (decision_bit_sound (P (m .fst)) (d (m .fst)) (m .snd .fst),
      k p ↦ m .snd .snd k (decision_bit_yes (P k) (d k) p)))
  | inr. z ↦ inr. (n p ↦ bit_zero_ne_one
      (concat Bit bit_zero (decision_bit (P n) (d n)) bit_one
        (inverse Bit (decision_bit (P n) (d n)) bit_zero (z (refl n))) (decision_bit_yes (P n) (d n) p))) ]
