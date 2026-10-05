export "bridge-01-finite-groups"
export "../../../src/1043-c2-power-subgroup-counts"
export "../../../src/1046-c2-power-subgroups-dwarf"

{` Bridges for rem:noofsubgps (fingp.tex:35) and the remark at
   fingp.tex:105, using modules 1040-1046: decidable subgroups
   of a group are the Bool-valued abstract subgroups (so they are finite for
   a finite group), C_2^n has 1, 2, 5 decidable subgroups for n = 0, 1, 2,
   and their number eventually exceeds k·2^n for every k (3^m ≤ number for
   C_2^(m+1)). The 26-digit count for n = 18 is not formalized (gap). `}

{` Remark (fingp.tex:105), second half: "dwarfed by the number of subgroups". `}
def bridge_c2_power_subgroups_dwarf : blind_c2_power_subgroups_dwarf
  ≔ let P ≔ c2_power_decidable_subgroups_dwarf_package in
    (P .fst, k ↦
      let D : Nat → Type ≔ n ↦ BlindDecSubgroups (blind_c2_power n) in
      let R : Type ≔ Σ Nat (N ↦ (n : Nat) → Le N n → Le (mul k (blind_pow 2 n)) (cardinality (D n) (P .fst n))) in
      mere_rec (Σ Nat (N ↦ (n : Nat) → Le N n → Le (mul k (nat_power two n)) (cardinality (D n) (P .fst n)))) (Mere R) (mere_isprop R)
        (u ↦ mere R (u .fst, n l ↦
          transport Nat (x ↦ Le (mul k x) (cardinality (D n) (P .fst n))) (nat_power two n) (blind_pow 2 n)
            (inverse Nat (blind_pow 2 n) (nat_power two n) (bridge_def_pow 2 n)) (u .snd n l)))
        (P .snd k))

{` rem:noofsubgps, corrected reading, the cases proved here:
   C_2^0, C_2^1, C_2^2 have 1, 2, 5 decidable subgroups (OEIS A006116). `}
def bridge_noofsubgps_small_counts
  : Product (BlindHasCard (BlindDecSubgroups (blind_c2_power 0)) 1)
      (Product (BlindHasCard (BlindDecSubgroups (blind_c2_power 1)) 2) (BlindHasCard (BlindDecSubgroups (blind_c2_power 2)) 5))
  ≔ let f ≔ c2_power_decidable_subgroups_dwarf_package .fst in
    ((f 0, c2_power_decidable_subgroups_count_zero (f 0)),
     ((f 1, c2_power_decidable_subgroups_count_one (f 1)),
      (f 2, c2_power_decidable_subgroups_count_two (f 2))))

{` The decimal encoding of the blind file is a faithful numeral (litmus). `}
def bridge_dec_litmus : Id BlindDec (blind_nat_to_dec 120) (cons. d0. (cons. d2. (cons. d1. nil.))) ≔ refl (blind_nat_to_dec 120)
