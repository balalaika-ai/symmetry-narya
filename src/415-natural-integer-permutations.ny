export "414-trivial-and-permutation-groups"
export "288-chapter-three-text-claims"

{` xca:group-example-details, last part: Aut_Set(ℕ) = Aut_Set(ℤ), induced by
   the equivalence ℕ ≃ ℤ of module 288 (parity encoding: 2n ↦ n, 2n+1 ↦ -n-1). `}
def nat_set_type : SetTypes ≔ (Nat, nat_set)

def int_set_type : SetTypes ≔ (Int, int_set)

def nat_int_permutation_groups_path
  : Id Group (permutation_group nat_set_type) (permutation_group int_set_type)
  ≔ permutation_group_equiv_path nat_set_type int_set_type parity_nat_int_equiv
