{` Blind statements for chapter 10 (fingp.tex): arithmetic vocabulary, def:finitegrd, orders of the
   first examples, products, and the counting remarks about C_2^n. `}
export "../../../src/407-group-family-products"
export "../../../src/502-subgroups"

{` Arithmetic vocabulary used by the chapter (the book has no formal definition of "prime"). `}
def blind_pow (b e : Nat) : Nat ≔ match e [ zero. ↦ 1 | suc. k ↦ mul (blind_pow b k) b ]

{` p is prime: p ≥ 2 and its only divisors are 1 and p. `}
def BlindIsPrime (p : Nat) : Type
  ≔ Product (Le 2 p) ((d : Nat) → NatDivides d p → Sum (Id Nat d 1) (Id Nat d p))

{` a and b are coprime: every common divisor is 1. `}
def BlindCoprime (a b : Nat) : Type ≔ (d : Nat) → NatDivides d a → NatDivides d b → Id Nat d 1

{` A finite set A has cardinality n. `}
def BlindHasCard (A : Type) (n : Nat) : Type ≔ Σ (IsFinite A) (h ↦ Id Nat (cardinality A h) n)

{` def:finitegrd. G is finite when the set USym G is finite; its order |G| is the cardinality of USym G. `}
def BlindIsFiniteGroup (G : Group) : Type ≔ IsFinite (USym G)

def blind_group_order (G : Group) (h : BlindIsFiniteGroup G) : Nat ≔ cardinality (USym G) h

{` "G is a finite group of order n" (USym G : FinSet_n). `}
def BlindHasOrder (G : Group) (n : Nat) : Type ≔ BlindHasCard (USym G) n

{` Example (fingp.tex:59). The trivial group has order 1, C_n has order n (n ≥ 1), Σ_n has order n!. `}
def blind_trivial_group_order : Type ≔ BlindHasOrder trivial_group 1

def blind_cyclic_group_order : Type ≔ (n : Nat) → BlindHasOrder (cyclic_group (suc. n)) (suc. n)

def blind_symmetric_group_order : Type ≔ (n : Nat) → BlindHasOrder (symmetric_group n) (factorial n)

{` Corollary (fingp.tex:102). |G × G'| = |G| · |G'|. `}
def blind_product_order : Type
  ≔ (G G' : Group) (hG : BlindIsFiniteGroup G) (hG' : BlindIsFiniteGroup G')
    → BlindHasOrder (product_group G G') (mul (blind_group_order G hG) (blind_group_order G' hG'))

{` C_2^n, the n-fold product of C_2 with itself. `}
def blind_c2_power (n : Nat) : Group ≔ power_group (Fin n) (fin_is_finite n) (cyclic_group 2)

{` The (decidable) subgroups of a group. Constructively only decidable subgroups of a finite group form a
   finite set (Sub(C_2) contains {e} ∪ {g | P} for every proposition P), so the counting claims below are
   stated for them; the literal readings with all subgroups are stated too. `}
def BlindDecSubgroups (G : Group) : Type ≔ Σ (Subgroups G) (S ↦ IsDecidableSubgroup G S)

{` Decimal numerals (little-endian digit lists), to state a 26-digit cardinality without ever building it
   as a unary Nat: Card(...) is converted to decimal, not the literal to unary. `}
def BlindDigit : Type ≔ data [ d0. | d1. | d2. | d3. | d4. | d5. | d6. | d7. | d8. | d9. ]

def BlindDec : Type ≔ data [ nil. | cons. (_ : BlindDigit) (_ : BlindDec) ]

def blind_dec_succ : BlindDec → BlindDec ≔ [
  | nil. ↦ cons. d1. nil.
  | cons. d0. r ↦ cons. d1. r
  | cons. d1. r ↦ cons. d2. r
  | cons. d2. r ↦ cons. d3. r
  | cons. d3. r ↦ cons. d4. r
  | cons. d4. r ↦ cons. d5. r
  | cons. d5. r ↦ cons. d6. r
  | cons. d6. r ↦ cons. d7. r
  | cons. d7. r ↦ cons. d8. r
  | cons. d8. r ↦ cons. d9. r
  | cons. d9. r ↦ cons. d0. (blind_dec_succ r) ]

def blind_nat_to_dec : Nat → BlindDec ≔ [ zero. ↦ nil. | suc. n ↦ blind_dec_succ (blind_nat_to_dec n) ]

def blind_dec_litmus : Id BlindDec (blind_nat_to_dec 13) (cons. d3. (cons. d1. nil.)) ≔ refl (blind_nat_to_dec 13)

{` 17741753171749626840952685, little-endian. `}
def blind_a006116_18 : BlindDec
  ≔ cons. d5. (cons. d8. (cons. d6. (cons. d2. (cons. d5. (cons. d9. (cons. d0. (cons. d4. (cons. d8. (cons. d6.
    (cons. d2. (cons. d6. (cons. d9. (cons. d4. (cons. d7. (cons. d1. (cons. d7. (cons. d1. (cons. d3. (cons. d5.
    (cons. d7. (cons. d1. (cons. d4. (cons. d7. (cons. d7. (cons. d1. nil.)))))))))))))))))))))))))

{` rem:noofsubgps. C_2^{×18} has 17741753171749626840952685 subgroups (literal: all subgroups; this
   reading implies excluded middle, see BlindDecSubgroups). `}
def blind_noofsubgps_c2_18 : Type
  ≔ Σ (IsFinite (Subgroups (blind_c2_power 18)))
      (h ↦ Id BlindDec (blind_nat_to_dec (cardinality (Subgroups (blind_c2_power 18)) h)) blind_a006116_18)

{` rem:noofsubgps, corrected: the same count for decidable subgroups. `}
def blind_noofsubgps_c2_18_corrected : Type
  ≔ Σ (IsFinite (BlindDecSubgroups (blind_c2_power 18)))
      (h ↦ Id BlindDec (blind_nat_to_dec (cardinality (BlindDecSubgroups (blind_c2_power 18)) h)) blind_a006116_18)

{` Remark (fingp.tex:105). |C_2^n| = 2^n ... `}
def blind_c2_power_order : Type ≔ (n : Nat) → BlindHasOrder (blind_c2_power n) (blind_pow 2 n)

{` ... and it is dwarfed by the number of (decidable) subgroups: this number is finite and, for every k,
   eventually at least k · 2^n. `}
def blind_c2_power_subgroups_dwarf : Type
  ≔ Σ ((n : Nat) → IsFinite (BlindDecSubgroups (blind_c2_power n)))
      (fin ↦ (k : Nat) → Mere (Σ Nat (N ↦ (n : Nat) → Le N n
         → Le (mul k (blind_pow 2 n)) (cardinality (BlindDecSubgroups (blind_c2_power n)) (fin n)))))
