export "1705-circle-choice"

{` rem:LPO-solves-halting problem (metamath.tex:189). The remark's LPO is
   LimitedOmniscience of module 71 (pri LPO, circle.tex:2347), literally:
   for every P : ℕ → 2 either a least n₀ with P(n₀) = 1 or P = const 0.
   The unprovability of LPO is a metatheorem (canonicity of closed terms,
   undecidability of the halting problem); only its internal ingredients are
   formalized here. Turing machines are not formalized: the step function
   T(e, n, k) is an arbitrary parameter T : ℕ → ℕ → ℕ → 2. `}

def bit_constant_zero_no_hit (P : Nat → Bit) (z : BitConstantZero P) (n : Nat) (p : BitHit P n) : Empty
  ≔ bit_zero_ne_one (concat Bit bit_zero (P n) bit_one (inverse Bit (P n) bit_zero (z (refl n))) p)

def bit_constant_zero_prop (P : Nat → Bit) : isProp (BitConstantZero P)
  ≔ pi_set Nat (_ ↦ Bit) (_ ↦ bit_set) P (_ ↦ bit_zero)

{` "P is constantly 0" is equivalent to "there is no n with P(n) = 1". `}
def bit_constant_zero_iff_no_hit (P : Nat → Bit)
  : Equiv (BitConstantZero P) (Not (Mere (Σ Nat (BitHit P))))
  ≔ iff_equiv (BitConstantZero P) (Not (Mere (Σ Nat (BitHit P)))) (bit_constant_zero_prop P)
      (negation_prop (Mere (Σ Nat (BitHit P))))
      (z h ↦ mere_rec (Σ Nat (BitHit P)) Empty empty_prop (w ↦ bit_constant_zero_no_hit P z (w .fst) (w .snd)) h)
      (nh ↦ no_bit_hit_constant_zero P (n p ↦ nh (mere (Σ Nat (BitHit P)) (n, p))))

{` LPO is equivalent to deciding, for every P : ℕ → 2, whether some n has
   P(n) = 1 (the least such n is then found by bounded search). `}
def LPODecidedHits : Type ≔ (P : Nat → Bit) → Decidable (Mere (Σ Nat (BitHit P)))

def lpo_decided_hits_prop : isProp LPODecidedHits
  ≔ pi_prop (Nat → Bit) (P ↦ Decidable (Mere (Σ Nat (BitHit P))))
      (P ↦ decidability_prop (Mere (Σ Nat (BitHit P))) (mere_isprop (Σ Nat (BitHit P))))

def lpo_decides_hits (lpo : LimitedOmniscience) : LPODecidedHits
  ≔ P ↦ match lpo P [
  | inl. m ↦ inl. (mere (Σ Nat (BitHit P)) (m .fst, m .snd .fst))
  | inr. z ↦ inr. (bit_constant_zero_iff_no_hit P .map z) ]

def decided_hits_lpo (d : LPODecidedHits) : LimitedOmniscience
  ≔ P ↦ match d P [
  | inl. h ↦ inl. (least_number (BitHit P) (n ↦ bit_set (P n) bit_one) (bit_hit_decidable P) h)
  | inr. nh ↦ inr. (equiv_inverse_map (BitConstantZero P) (Not (Mere (Σ Nat (BitHit P))))
      (bit_constant_zero_iff_no_hit P) nh) ]

def lpo_decided_hits_equiv : Equiv LimitedOmniscience LPODecidedHits
  ≔ iff_equiv LimitedOmniscience LPODecidedHits limited_omniscience_prop lpo_decided_hits_prop
      lpo_decides_hits decided_hits_lpo

{` An inhabitant of LPO decides, for every sequence, whether it is constantly 0. `}
def lpo_decides_constant_zero (lpo : LimitedOmniscience) (P : Nat → Bit) : Decidable (BitConstantZero P)
  ≔ match lpo P [ inl. m ↦ inr. (bit_minimum_not_zero P m) | inr. z ↦ inl. z ]

{` The halting predicate for a step function T: "M_e halts on n" is
   ∃k T(e,n,k) = 1. The remark's "k ↦ T(e,n,k) is constantly 0 iff M_e does
   not halt on n" holds for every T. `}
def Halts (T : Nat → Nat → Nat → Bit) (e n : Nat) : Type ≔ Mere (Σ Nat (BitHit (T e n)))

def halting_constant_zero_iff (T : Nat → Nat → Nat → Bit) (e n : Nat)
  : Equiv (BitConstantZero (T e n)) (Not (Halts T e n))
  ≔ bit_constant_zero_iff_no_hit (T e n)

{` The decision procedure of the remark: case analysis on t(k ↦ T(e,n,k)) : L ⊔ R.
   inl gives halting, inr (constantly 0) gives non-halting. `}
def lpo_decides_halting (lpo : LimitedOmniscience) (T : Nat → Nat → Nat → Bit) (e n : Nat)
  : Decidable (Halts T e n)
  ≔ match lpo (T e n) [
  | inl. m ↦ inl. (mere (Σ Nat (BitHit (T e n))) (m .fst, m .snd .fst))
  | inr. z ↦ inr. (halting_constant_zero_iff T e n .map z) ]

def lpo_left_halts (T : Nat → Nat → Nat → Bit) (e n : Nat) (l : BitMinimum (T e n)) : Halts T e n
  ≔ mere (Σ Nat (BitHit (T e n))) (l .fst, l .snd .fst)

def lpo_right_not_halts (T : Nat → Nat → Nat → Bit) (e n : Nat) (r : BitConstantZero (T e n))
  : Not (Halts T e n)
  ≔ halting_constant_zero_iff T e n .map r

{` "The argument must fail if we allow t to use LEM": with LEM as a
   hypothesis, LPO holds (module 71) and the halting predicate of every T is
   decided. `}
def excluded_middle_decides_halting (lem : ExcludedMiddle) (T : Nat → Nat → Nat → Bit) (e n : Nat)
  : Decidable (Halts T e n)
  ≔ lpo_decides_halting (excluded_middle_implies_lpo lem) T e n

{` Litmus: a step function where machine e halts exactly at step e, and the
   never-halting step function. `}
def halts_at_own_index (e n k : Nat) : Bit ≔ decision_bit (Id Nat k e) (nat_dec_eq k e)

def never_halts (e n k : Nat) : Bit ≔ bit_zero

def halts_at_own_index_halts (e n : Nat) : Halts halts_at_own_index e n
  ≔ mere (Σ Nat (BitHit (halts_at_own_index e n))) (e, decision_bit_yes (Id Nat e e) (nat_dec_eq e e) (refl e))

def never_halts_not_halts (e n : Nat) : Not (Halts never_halts e n)
  ≔ halting_constant_zero_iff never_halts e n .map (refl (never_halts e n))
