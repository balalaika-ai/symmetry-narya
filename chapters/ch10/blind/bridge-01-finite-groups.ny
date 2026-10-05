export "01-finite-groups"
export "../../../src/1012-finite-group-orders"

{` Bridges for fingp.tex: arithmetic vocabulary, def:finitegrd, the
   orders of the first examples (line 59), products (line 102) and the order
   of C_2^n (line 105). The blind prime, coprime, finite-group, order and
   C_2^n notions are ours by refl; the blind power function has the same
   recursion as nat_power and agrees with it by induction. `}

def bridge_def_pow (b e : Nat) : Id Nat (blind_pow b e) (nat_power b e)
  ≔ match e [
  | zero. ↦ refl (suc. zero. : Nat)
  | suc. k ↦ refl ((x ↦ mul x b) : Nat → Nat) (bridge_def_pow b k) ]

def bridge_def_is_prime (p : Nat) : Id Type (BlindIsPrime p) (NatIsPrime p) ≔ refl (NatIsPrime p)

def bridge_def_coprime (a b : Nat) : Id Type (BlindCoprime a b) (NatCoprime a b) ≔ refl (NatCoprime a b)

def bridge_def_is_finite_group (G : Group) : Id Type (BlindIsFiniteGroup G) (IsFiniteGroup G) ≔ refl (IsFiniteGroup G)

def bridge_def_group_order (G : Group) (h : IsFiniteGroup G) : Id Nat (blind_group_order G h) (group_card G h)
  ≔ refl (group_card G h)

def bridge_def_has_order (G : Group) (n : Nat)
  : Id Type (BlindHasOrder G n) (Σ (IsFiniteGroup G) (h ↦ Id Nat (group_card G h) n))
  ≔ refl (BlindHasOrder G n)

def bridge_def_c2_power (n : Nat)
  : Id Group (blind_c2_power n) (power_group (Fin n) (fin_is_finite n) (cyclic_group two))
  ≔ refl (blind_c2_power n)

def bridge_def_dec_subgroups (G : Group)
  : Id Type (BlindDecSubgroups G) (Σ (Subgroups G) (S ↦ IsDecidableSubgroup G S))
  ≔ refl (BlindDecSubgroups G)

{` Example (fingp.tex:59). `}
def bridge_trivial_group_order : blind_trivial_group_order
  ≔ (trivial_group_finite, trivial_group_card trivial_group_finite)

def bridge_cyclic_group_order : blind_cyclic_group_order
  ≔ n ↦ (cyclic_group_finite n, cyclic_group_card n (cyclic_group_finite n))

def bridge_symmetric_group_order : blind_symmetric_group_order
  ≔ n ↦ (symmetric_group_finite n, symmetric_group_card n)

{` Corollary (fingp.tex:102). `}
def bridge_product_order : blind_product_order
  ≔ G G' hG hG' ↦
    (product_group_finite G G' hG hG',
     product_group_card G G' hG hG' (product_group_finite G G' hG hG'))

{` Remark (fingp.tex:105), first half: |C_2^n| = 2^n. `}
def bridge_c2_power_order : blind_c2_power_order
  ≔ n ↦
    (cyclic_two_power_finite n,
     concat Nat (group_card (blind_c2_power n) (cyclic_two_power_finite n)) (nat_power two n) (blind_pow two n)
       (cyclic_two_power_card n (cyclic_two_power_finite n))
       (inverse Nat (blind_pow two n) (nat_power two n) (bridge_def_pow two n)))
