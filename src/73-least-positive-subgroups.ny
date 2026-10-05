export "72-decidable-cycle-periods"

def subgroup_nat_multiple (H : Subtypes Int) (h : IntegerSubgroupLaws H) (g : Int) (hg : SubgroupMember H g) (n : Nat)
  : SubgroupMember H (iterate Int (int_add g) n int_zero)
  ≔ match n [ zero. ↦ h .fst | suc. n ↦ h .snd .fst g (iterate Int (int_add g) n int_zero) hg (subgroup_nat_multiple H h g hg n) ]

def subgroup_left_multiple (H : Subtypes Int) (h : IntegerSubgroupLaws H) (g : Int) (hg : SubgroupMember H g) (q : Int)
  : SubgroupMember H (int_mul g q)
  ≔ match q [
  | pos. n ↦ subgroup_nat_multiple H h g hg n
  | neg. n ↦ subgroup_nat_multiple H h (int_neg g) (h .snd .snd g hg) (suc. n) ]

def subgroup_multiple (H : Subtypes Int) (h : IntegerSubgroupLaws H) (g : Int) (hg : SubgroupMember H g) (q : Int)
  : SubgroupMember H (int_mul q g)
  ≔ refl (SubgroupMember H) (int_mul_comm g q) .trr (subgroup_left_multiple H h g hg q)

def int_sub_sum_left (x y : Int) : Id Int (int_sub (int_add x y) x) y
  ≔ calc
      int_sub (int_add x y) x = int_sub (int_add y x) x
        by refl ((z ↦ int_sub z x) : Int → Int) (int_add_comm x y)
      = y by int_add_sub y x ∎

def division_remainder_in_subgroup (H : Subtypes Int) (h : IntegerSubgroupLaws H) (z : Int) (m : Nat)
  (hm : SubgroupMember H (pos. m)) (hz : SubgroupMember H z) (u : IntegerDivisionResult z m)
  : SubgroupMember H (pos. (u .fst .snd))
  ≔ let q ≔ int_mul (u .fst .fst) (pos. m) in
    let eq : Id Int (int_sub z q) (pos. (u .fst .snd)) ≔ calc
      int_sub z q = int_sub (int_add q (pos. (u .fst .snd))) q
        by refl ((w ↦ int_sub w q) : Int → Int) (u .snd .snd)
      = pos. (u .fst .snd) by int_sub_sum_left q (pos. (u .fst .snd)) ∎ in
    refl (SubgroupMember H) eq .trr
      (h .snd .fst z (int_neg q) hz (h .snd .snd q (subgroup_multiple H h (pos. m) hm (u .fst .fst))))

def PositiveSubgroupMember (H : Subtypes Int) (n : Nat) : Type ≔ SubgroupMember H (pos. (suc. n))

def least_subgroup_small_zero (H : Subtypes Int) (n : Nat) (minimal : IsMinimum (PositiveSubgroupMember H) n)
  (r : Nat) (bound : BookLt r (suc. n)) (hr : SubgroupMember H (pos. r)) : Id Nat r zero.
  ≔ match r [
  | zero. ↦ refl zero.
  | suc. k ↦ absurd (Id Nat (suc. k) zero.)
      (lt_irrefl k (lt_le_trans k n k (lt_from_book (suc. k) (suc. n) bound)
        (le_from_book n k (minimal .snd k hr)))) ]

def MultipleWitness (m : Nat) (z : Int) : Type ≔ Σ Int (q ↦ Id Int z (int_mul q (pos. m)))
def Multiples (m : Nat) : Subtypes Int ≔ z ↦ (Mere (MultipleWitness m z), mere_isprop (MultipleWitness m z))

def least_subgroup_member_multiple (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  (n : Nat) (minimal : IsMinimum (PositiveSubgroupMember H) n) (z : Int) (hz : SubgroupMember H z)
  : MultipleWitness (suc. n) z
  ≔ let u ≔ integer_euclidean_division z (suc. n) (lt_to_book zero. (suc. n) star.) in
    let rzero ≔ least_subgroup_small_zero H n minimal (u .fst .snd) (u .snd .fst)
      (division_remainder_in_subgroup H h z (suc. n) (minimal .fst) hz u) in
    (u .fst .fst, concat Int z (integer_division_value (u .fst .fst) (u .fst .snd) (suc. n))
      (int_mul (u .fst .fst) (pos. (suc. n))) (u .snd .snd)
      (map_path Nat Int (r ↦ integer_division_value (u .fst .fst) r (suc. n)) (u .fst .snd) zero. rzero))

def multiple_subgroup_member (H : Subtypes Int) (h : IntegerSubgroupLaws H) (m : Nat)
  (hm : SubgroupMember H (pos. m)) (z : Int) : Multiples m z .fst → SubgroupMember H z
  ≔ mere_rec (MultipleWitness m z) (SubgroupMember H z) (H z .snd)
      (w ↦ refl (SubgroupMember H) (w .snd) .trl (subgroup_multiple H h (pos. m) hm (w .fst)))

def least_subgroup_is_multiples (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  (n : Nat) (minimal : IsMinimum (PositiveSubgroupMember H) n) : Id (Subtypes Int) H (Multiples (suc. n))
  ≔ funext Int (_ ↦ PropTypes) H (Multiples (suc. n))
      (z ↦ proposition_extensionality (H z) (Multiples (suc. n) z)
        (hz ↦ mere (MultipleWitness (suc. n) z) (least_subgroup_member_multiple H h n minimal z hz))
        (multiple_subgroup_member H h (suc. n) (minimal .fst) z))

def least_cycle_periods_multiples (c : Cycles) (n : Nat) (minimal : IsMinimum (PositiveCyclePeriod c) n)
  : Id (Subtypes Int) (CyclePeriods c) (Multiples (suc. n))
  ≔ least_subgroup_is_multiples (CyclePeriods c) (cycle_subgroup_laws c) n minimal
