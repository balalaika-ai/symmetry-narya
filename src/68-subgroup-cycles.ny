export "67-integer-differences"

def SubgroupMember (H : Subtypes Int) (n : Int) : Type ≔ H n .fst
def SubgroupAddClosed (H : Subtypes Int) : Type
  ≔ (n k : Int) → SubgroupMember H n → SubgroupMember H k → SubgroupMember H (int_add n k)
def SubgroupNegClosed (H : Subtypes Int) : Type
  ≔ (n : Int) → SubgroupMember H n → SubgroupMember H (int_neg n)
def IntegerSubgroupLaws (H : Subtypes Int) : Type
  ≔ Product (SubgroupMember H int_zero) (Product (SubgroupAddClosed H) (SubgroupNegClosed H))

def integer_subgroup_laws_prop (H : Subtypes Int) : isProp (IntegerSubgroupLaws H)
  ≔ product_prop (SubgroupMember H int_zero) (Product (SubgroupAddClosed H) (SubgroupNegClosed H)) (H int_zero .snd)
      (product_prop (SubgroupAddClosed H) (SubgroupNegClosed H)
        (pi_prop Int (n ↦ (k : Int) → SubgroupMember H n → SubgroupMember H k → SubgroupMember H (int_add n k))
          (n ↦ pi_prop Int (k ↦ SubgroupMember H n → SubgroupMember H k → SubgroupMember H (int_add n k))
            (k ↦ pi_prop (SubgroupMember H n) (_ ↦ SubgroupMember H k → SubgroupMember H (int_add n k))
              (_ ↦ pi_prop (SubgroupMember H k) (_ ↦ SubgroupMember H (int_add n k)) (_ ↦ H (int_add n k) .snd)))))
        (pi_prop Int (n ↦ SubgroupMember H n → SubgroupMember H (int_neg n))
          (n ↦ pi_prop (SubgroupMember H n) (_ ↦ SubgroupMember H (int_neg n)) (_ ↦ H (int_neg n) .snd))))

def IntegerSubgroups : Type ≔ Σ (Subtypes Int) IntegerSubgroupLaws

def subgroup_relation (H : Subtypes Int) (h : IntegerSubgroupLaws H) : EquivalenceRelation Int
  ≔ ((x y ↦ H (int_sub x y)),
      (x ↦ refl (SubgroupMember H) (int_sub_self x) .trl (h .fst)),
      (x y p ↦ refl (SubgroupMember H) (int_neg_sub x y) .trr (h .snd .snd (int_sub x y) p)),
      (x y z p q ↦ refl (SubgroupMember H) (int_sub_chain x y z) .trr (h .snd .fst (int_sub x y) (int_sub y z) p q)))

def SubgroupQuotient (H : Subtypes Int) (h : IntegerSubgroupLaws H) : Type ≔ Quotient Int (subgroup_relation H h)
def subgroup_class (H : Subtypes Int) (h : IntegerSubgroupLaws H) : Int → SubgroupQuotient H h
  ≔ quotient_class Int (subgroup_relation H h)
def subgroup_quotient_set (H : Subtypes Int) (h : IntegerSubgroupLaws H) : isSet (SubgroupQuotient H h)
  ≔ quotient_set Int (subgroup_relation H h)

def subgroup_translation (H : Subtypes Int) (h : IntegerSubgroupLaws H) (z : Int)
  : SubgroupQuotient H h → SubgroupQuotient H h
  ≔ quotient_rec Int (SubgroupQuotient H h) (subgroup_relation H h) (subgroup_quotient_set H h)
      (x ↦ subgroup_class H h (int_add x z))
      (x y p ↦ quotient_encode Int (subgroup_relation H h) (int_add x z) (int_add y z)
        (refl (SubgroupMember H) (int_sub_translate x y z) .trl p))

def subgroup_translation_inverse (H : Subtypes Int) (h : IntegerSubgroupLaws H) (z : Int)
  : Id (SubgroupQuotient H h → SubgroupQuotient H h)
      (q ↦ subgroup_translation H h (int_neg z) (subgroup_translation H h z q)) (identity (SubgroupQuotient H h))
  ≔ surjection_function_ext Int (SubgroupQuotient H h) (SubgroupQuotient H h)
      (subgroup_class H h) (quotient_surjective Int (subgroup_relation H h)) (subgroup_quotient_set H h)
      (q ↦ subgroup_translation H h (int_neg z) (subgroup_translation H h z q)) (identity (SubgroupQuotient H h))
      (funext Int (_ ↦ SubgroupQuotient H h)
        (x ↦ subgroup_class H h (int_sub (int_add x z) z)) (subgroup_class H h)
        (x ↦ refl (subgroup_class H h) (int_add_sub x z)))

def subgroup_translation_inverse_other (H : Subtypes Int) (h : IntegerSubgroupLaws H) (z : Int)
  : Id (SubgroupQuotient H h → SubgroupQuotient H h)
      (q ↦ subgroup_translation H h z (subgroup_translation H h (int_neg z) q)) (identity (SubgroupQuotient H h))
  ≔ surjection_function_ext Int (SubgroupQuotient H h) (SubgroupQuotient H h)
      (subgroup_class H h) (quotient_surjective Int (subgroup_relation H h)) (subgroup_quotient_set H h)
      (q ↦ subgroup_translation H h z (subgroup_translation H h (int_neg z) q)) (identity (SubgroupQuotient H h))
      (funext Int (_ ↦ SubgroupQuotient H h)
        (x ↦ subgroup_class H h (int_add (int_sub x z) z)) (subgroup_class H h)
        (x ↦ refl (subgroup_class H h) (int_sub_add x z)))

def subgroup_translation_equiv (H : Subtypes Int) (h : IntegerSubgroupLaws H) (z : Int)
  : Equiv (SubgroupQuotient H h) (SubgroupQuotient H h)
  ≔ quasi_inverse_equiv (SubgroupQuotient H h) (SubgroupQuotient H h)
      (subgroup_translation H h z) (subgroup_translation H h (int_neg z))
      (q ↦ subgroup_translation_inverse H h z (refl q)) (q ↦ subgroup_translation_inverse_other H h z (refl q))

def subgroup_successor (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : Equiv (SubgroupQuotient H h) (SubgroupQuotient H h)
  ≔ subgroup_translation_equiv H h (pos. (suc. zero.))

def subgroup_power_class (H : Subtypes Int) (h : IntegerSubgroupLaws H) (n x : Int)
  : Id (SubgroupQuotient H h) (subgroup_class H h (int_add x n))
      (permutation_power (SubgroupQuotient H h) (subgroup_successor H h) n (subgroup_class H h x))
  ≔ permutation_power_intertwine Int (SubgroupQuotient H h) int_succ_equiv (subgroup_successor H h)
      (subgroup_class H h) (x ↦ refl (subgroup_class H h (int_succ x))) n x

def subgroup_power_zero (H : Subtypes Int) (h : IntegerSubgroupLaws H) (n : Int)
  : Id (SubgroupQuotient H h) (subgroup_class H h n)
      (permutation_power (SubgroupQuotient H h) (subgroup_successor H h) n (subgroup_class H h int_zero))
  ≔ calc
      subgroup_class H h n = subgroup_class H h (int_add int_zero n) by refl (subgroup_class H h) (int_add_zero_left n)
      = permutation_power (SubgroupQuotient H h) (subgroup_successor H h) n (subgroup_class H h int_zero)
        by subgroup_power_class H h n int_zero ∎

def subgroup_cycle_property (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : Cyclic (SubgroupQuotient H h) (subgroup_successor H h)
  ≔ cyclic_from_orbit_surjective (SubgroupQuotient H h) (subgroup_successor H h) (subgroup_class H h int_zero)
      (q ↦ trunc_map native_truncation (BookFiber Int (SubgroupQuotient H h) (subgroup_class H h) q)
        (BookFiber Int (SubgroupQuotient H h)
          (n ↦ permutation_power (SubgroupQuotient H h) (subgroup_successor H h) n (subgroup_class H h int_zero)) q)
        (w ↦ (w .fst, concat (SubgroupQuotient H h) q (subgroup_class H h (w .fst))
          (permutation_power (SubgroupQuotient H h) (subgroup_successor H h) (w .fst) (subgroup_class H h int_zero))
          (w .snd) (subgroup_power_zero H h (w .fst)))) (quotient_surjective Int (subgroup_relation H h) q))

def subgroup_cycle (H : Subtypes Int) (h : IntegerSubgroupLaws H) : Cycles
  ≔ (((SubgroupQuotient H h, subgroup_quotient_set H h), subgroup_successor H h), subgroup_cycle_property H h)

def subgroup_fix_to_member (H : Subtypes Int) (h : IntegerSubgroupLaws H) (n : Int)
  (p : Id (SubgroupQuotient H h)
    (permutation_power (SubgroupQuotient H h) (subgroup_successor H h) n (subgroup_class H h int_zero))
    (subgroup_class H h int_zero)) : SubgroupMember H n
  ≔ quotient_effective Int (subgroup_relation H h) n int_zero .map
      (concat (SubgroupQuotient H h) (subgroup_class H h n)
        (permutation_power (SubgroupQuotient H h) (subgroup_successor H h) n (subgroup_class H h int_zero))
        (subgroup_class H h int_zero) (subgroup_power_zero H h n) p)

def subgroup_member_to_fix (H : Subtypes Int) (h : IntegerSubgroupLaws H) (n : Int) (p : SubgroupMember H n)
  : Id (SubgroupQuotient H h)
    (permutation_power (SubgroupQuotient H h) (subgroup_successor H h) n (subgroup_class H h int_zero))
    (subgroup_class H h int_zero)
  ≔ concat (SubgroupQuotient H h)
      (permutation_power (SubgroupQuotient H h) (subgroup_successor H h) n (subgroup_class H h int_zero))
      (subgroup_class H h n) (subgroup_class H h int_zero)
      (inverse (SubgroupQuotient H h) (subgroup_class H h n)
        (permutation_power (SubgroupQuotient H h) (subgroup_successor H h) n (subgroup_class H h int_zero)) (subgroup_power_zero H h n))
      (quotient_encode Int (subgroup_relation H h) n int_zero p)

def subgroup_cycle_periods (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : Id (Subtypes Int) (CyclePeriods (subgroup_cycle H h)) H
  ≔ funext Int (_ ↦ PropTypes) (CyclePeriods (subgroup_cycle H h)) H
      (n ↦ proposition_extensionality (CyclePeriods (subgroup_cycle H h) n) (H n)
        (p ↦ subgroup_fix_to_member H h n (p (refl (subgroup_class H h int_zero))))
        (p ↦ cycle_period_from_point (SubgroupQuotient H h) (subgroup_quotient_set H h) (subgroup_successor H h)
          (subgroup_cycle_property H h) (subgroup_class H h int_zero) n (subgroup_member_to_fix H h n p)))
