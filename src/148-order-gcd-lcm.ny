export "147-principal-divisibility"

def int_add_right_swap (a b c : Int) : Id Int (int_add (int_add a b) c) (int_add (int_add a c) b)
  ≔ calc
      int_add (int_add a b) c = int_add a (int_add b c) by int_add_assoc a b c
      = int_add a (int_add c b) by refl (int_add a) (int_add_comm b c)
      = int_add (int_add a c) b by inverse Int (int_add (int_add a c) b) (int_add a (int_add c b)) (int_add_assoc a c b) ∎

def int_add_cancel_mix (a b c : Int) : Id Int (int_add (int_add a b) (int_add c (int_neg a))) (int_add c b)
  ≔ calc
      int_add (int_add a b) (int_add c (int_neg a)) = int_add (int_add b a) (int_add c (int_neg a))
        by refl ((v ↦ int_add v (int_add c (int_neg a))) : Int → Int) (int_add_comm a b)
      = int_add b (int_add a (int_add c (int_neg a))) by int_add_assoc b a (int_add c (int_neg a))
      = int_add b (int_add a (int_add (int_neg a) c))
        by refl ((v ↦ int_add b (int_add a v)) : Int → Int) (int_add_comm c (int_neg a))
      = int_add b c by refl (int_add b) (int_translate_inverse_other a c)
      = int_add c b by int_add_comm b c ∎

def int_mul_division_expand (x : Int) (q b r : Nat)
  : Id Int (int_mul x (pos. (add (mul q b) r))) (int_add (int_mul (int_mul x (pos. q)) (pos. b)) (int_mul x (pos. r)))
  ≔ concat Int (int_mul x (pos. (add (mul q b) r))) (int_add (int_mul x (pos. (mul q b))) (int_mul x (pos. r)))
      (int_add (int_mul (int_mul x (pos. q)) (pos. b)) (int_mul x (pos. r)))
      (int_mul_pos_add x (mul q b) r)
      (refl ((v ↦ int_add v (int_mul x (pos. r))) : Int → Int) (int_mul_pos_mul x q b))

def multiples_laws (m : Nat) : IntegerSubgroupLaws (Multiples m)
  ≔ transport (Subtypes Int) IntegerSubgroupLaws (order_periods (principal_order m)) (Multiples m)
      (principal_order_periods m) (order_subgroup_laws (principal_order m))

def multiple_of (m : Nat) (x : Int) : Multiples m (int_mul x (pos. m)) .fst
  ≔ mere (MultipleWitness m (int_mul x (pos. m))) (x, refl (int_mul x (pos. m)))

{` aZ + bZ = bZ + rZ for a = qb + r, the step of Euclid's algorithm. `}
def sum_division_invariant (a b q r : Nat) (pa : Id Nat a (add (mul q b) r))
  : Id (Subtypes Int) (SubgroupSum (Multiples a) (Multiples b)) (SubgroupSum (Multiples b) (Multiples r))
  ≔ let S1 ≔ SubgroupSum (Multiples a) (Multiples b) in let S2 ≔ SubgroupSum (Multiples b) (Multiples r) in
    inclusion_antisym Int S1 S2
      (z s ↦ mere_rec (SubgroupSumWitness (Multiples a) (Multiples b) z) (S2 z .fst) (S2 z .snd)
        (w ↦ let x ≔ w .fst in let y ≔ w .snd .fst in
          mere_rec (MultipleWitness a x) (S2 z .fst) (S2 z .snd)
            (u ↦ let U ≔ u .fst in
              let A ≔ int_mul (int_mul U (pos. q)) (pos. b) in
              mere (SubgroupSumWitness (Multiples b) (Multiples r) z)
                (int_add A y, (int_mul U (pos. r),
                  ((multiples_laws b .snd .fst A y (multiple_of b (int_mul U (pos. q))) (w .snd .snd .fst .snd),
                    multiple_of r U),
                   calc
                    z = int_add x y by w .snd .snd .snd
                    = int_add (int_mul U (pos. a)) y by refl ((v ↦ int_add v y) : Int → Int) (u .snd)
                    = int_add (int_mul U (pos. (add (mul q b) r))) y
                      by refl ((k ↦ int_add (int_mul U (pos. k)) y) : Nat → Int) pa
                    = int_add (int_add A (int_mul U (pos. r))) y
                      by refl ((v ↦ int_add v y) : Int → Int) (int_mul_division_expand U q b r)
                    = int_add (int_add A y) (int_mul U (pos. r)) by int_add_right_swap A (int_mul U (pos. r)) y ∎))))
            (w .snd .snd .fst .fst))
        s)
      (z s ↦ mere_rec (SubgroupSumWitness (Multiples b) (Multiples r) z) (S1 z .fst) (S1 z .snd)
        (w ↦ let x ≔ w .fst in let y ≔ w .snd .fst in
          mere_rec (MultipleWitness r y) (S1 z .fst) (S1 z .snd)
            (u ↦ let U ≔ u .fst in
              let A ≔ int_mul (int_mul U (pos. q)) (pos. b) in
              let B ≔ int_mul (int_neg (int_mul U (pos. q))) (pos. b) in
              mere (SubgroupSumWitness (Multiples a) (Multiples b) z)
                (int_mul U (pos. a), (int_add x B,
                  ((multiple_of a U,
                    multiples_laws b .snd .fst x B (w .snd .snd .fst .fst) (multiple_of b (int_neg (int_mul U (pos. q))))),
                   calc
                    z = int_add x y by w .snd .snd .snd
                    = int_add x (int_mul U (pos. r)) by refl (int_add x) (u .snd)
                    = int_add (int_add A (int_mul U (pos. r))) (int_add x (int_neg A))
                      by inverse Int (int_add (int_add A (int_mul U (pos. r))) (int_add x (int_neg A)))
                        (int_add x (int_mul U (pos. r))) (int_add_cancel_mix A (int_mul U (pos. r)) x)
                    = int_add (int_mul U (pos. (add (mul q b) r))) (int_add x (int_neg A))
                      by refl ((v ↦ int_add v (int_add x (int_neg A))) : Int → Int)
                        (inverse Int (int_mul U (pos. (add (mul q b) r))) (int_add A (int_mul U (pos. r)))
                          (int_mul_division_expand U q b r))
                    = int_add (int_mul U (pos. a)) (int_add x (int_neg A))
                      by refl ((k ↦ int_add (int_mul U (pos. k)) (int_add x (int_neg A))) : Nat → Int)
                        (inverse Nat a (add (mul q b) r) pa)
                    = int_add (int_mul U (pos. a)) (int_add x B)
                      by refl ((v ↦ int_add (int_mul U (pos. a)) (int_add x v)) : Int → Int)
                        (inverse Int B (int_neg A) (int_mul_neg_left_pos (int_mul U (pos. q)) b)) ∎))))
            (w .snd .snd .fst .snd))
        s)

def sum_zero_multiples (a : Nat) : Id (Subtypes Int) (SubgroupSum (Multiples a) (Multiples zero.)) (Multiples a)
  ≔ inclusion_antisym Int (SubgroupSum (Multiples a) (Multiples zero.)) (Multiples a)
      (z s ↦ mere_rec (SubgroupSumWitness (Multiples a) (Multiples zero.) z) (Multiples a z .fst) (Multiples a z .snd)
        (w ↦ mere_rec (MultipleWitness zero. (w .snd .fst)) (Multiples a z .fst) (Multiples a z .snd)
          (v ↦ transport Int (k ↦ Multiples a k .fst) (w .fst) z
            (inverse Int z (w .fst) (concat Int z (int_add (w .fst) (w .snd .fst)) (w .fst) (w .snd .snd .snd)
              (refl (int_add (w .fst)) (v .snd))))
            (w .snd .snd .fst .fst))
          (w .snd .snd .fst .snd)) s)
      (z h ↦ mere (SubgroupSumWitness (Multiples a) (Multiples zero.) z)
        (z, (int_zero, ((h, mere (MultipleWitness zero. int_zero) (int_zero, refl int_zero)), refl z))))

{` Euclid's algorithm, with fuel bounding the second argument. `}
def gcd_fuel (f a b : Nat) : Nat
  ≔ match f [
  | zero. ↦ a
  | suc. f ↦ match b [
    | zero. ↦ a
    | suc. c ↦ gcd_fuel f (suc. c) (euclidean_division a (suc. c) (lt_to_book zero. (suc. c) star.) .fst .snd) ] ]

def nat_gcd (a b : Nat) : Nat ≔ gcd_fuel (suc. b) a b

def gcd_fuel_sum (f a b : Nat) (bound : Lt b f)
  : Id (Subtypes Int) (SubgroupSum (Multiples a) (Multiples b)) (Multiples (gcd_fuel f a b))
  ≔ match f [
  | zero. ↦ match bound []
  | suc. f ↦ match b [
    | zero. ↦ sum_zero_multiples a
    | suc. c ↦ let u ≔ euclidean_division a (suc. c) (lt_to_book zero. (suc. c) star.) in
        concat (Subtypes Int) (SubgroupSum (Multiples a) (Multiples (suc. c)))
          (SubgroupSum (Multiples (suc. c)) (Multiples (u .fst .snd))) (Multiples (gcd_fuel f (suc. c) (u .fst .snd)))
          (sum_division_invariant a (suc. c) (u .fst .fst) (u .fst .snd) (u .snd .snd))
          (gcd_fuel_sum f (suc. c) (u .fst .snd)
            (le_trans (suc. (u .fst .snd)) (suc. c) f (lt_from_book (u .fst .snd) (suc. c) (u .snd .fst)) bound)) ] ]

def nat_gcd_sum (a b : Nat) : Id (Subtypes Int) (SubgroupSum (Multiples a) (Multiples b)) (Multiples (nat_gcd a b))
  ≔ gcd_fuel_sum (suc. b) a b (le_refl (suc. b))

def nat_divides_multiples (c a : Nat) (h : NatDivides c a) : Inclusion Int (Multiples a) (Multiples c)
  ≔ z p ↦ mere_rec (Σ Nat (q ↦ Id Nat a (mul q c))) (Multiples c z .fst) (Multiples c z .snd)
      (v ↦ mere_rec (MultipleWitness a z) (Multiples c z .fst) (Multiples c z .snd)
        (r ↦ mere (MultipleWitness c z) (int_mul (r .fst) (pos. (v .fst)), calc
          z = int_mul (r .fst) (pos. a) by r .snd
          = int_mul (r .fst) (pos. (mul (v .fst) c)) by refl ((k ↦ int_mul (r .fst) (pos. k)) : Nat → Int) (v .snd)
          = int_mul (int_mul (r .fst) (pos. (v .fst))) (pos. c) by int_mul_pos_mul (r .fst) (v .fst) c ∎)) p) h

def nat_gcd_divides_left (a b : Nat) : NatDivides (nat_gcd a b) a
  ≔ let g ≔ nat_gcd a b in
    mere_rec (MultipleWitness g (pos. a)) (NatDivides g a) (nat_divides_prop g a) (multiple_nat_divides g a)
      (transport (Subtypes Int) (H ↦ H (pos. a) .fst) (SubgroupSum (Multiples a) (Multiples b)) (Multiples g) (nat_gcd_sum a b)
        (mere (SubgroupSumWitness (Multiples a) (Multiples b) (pos. a))
          (pos. a, (int_zero, ((self_multiple a, multiples_laws b .fst), refl (pos. a : Int))))))

def nat_gcd_divides_right (a b : Nat) : NatDivides (nat_gcd a b) b
  ≔ let g ≔ nat_gcd a b in
    mere_rec (MultipleWitness g (pos. b)) (NatDivides g b) (nat_divides_prop g b) (multiple_nat_divides g b)
      (transport (Subtypes Int) (H ↦ H (pos. b) .fst) (SubgroupSum (Multiples a) (Multiples b)) (Multiples g) (nat_gcd_sum a b)
        (mere (SubgroupSumWitness (Multiples a) (Multiples b) (pos. b))
          (int_zero, (pos. b, ((multiples_laws a .fst, self_multiple b),
            inverse Int (int_add int_zero (pos. b)) (pos. b) (int_add_zero_left (pos. b)))))))

def nat_gcd_greatest (a b c : Nat) (ha : NatDivides c a) (hb : NatDivides c b) : NatDivides c (nat_gcd a b)
  ≔ let g ≔ nat_gcd a b in
    mere_rec (MultipleWitness c (pos. g)) (NatDivides c g) (nat_divides_prop c g) (multiple_nat_divides c g)
      (mere_rec (SubgroupSumWitness (Multiples a) (Multiples b) (pos. g)) (Multiples c (pos. g) .fst) (Multiples c (pos. g) .snd)
        (w ↦ transport Int (k ↦ Multiples c k .fst) (int_add (w .fst) (w .snd .fst)) (pos. g)
          (inverse Int (pos. g) (int_add (w .fst) (w .snd .fst)) (w .snd .snd .snd))
          (multiples_laws c .snd .fst (w .fst) (w .snd .fst)
            (nat_divides_multiples c a ha (w .fst) (w .snd .snd .fst .fst))
            (nat_divides_multiples c b hb (w .snd .fst) (w .snd .snd .fst .snd))))
        (transport (Subtypes Int) (H ↦ H (pos. g) .fst) (Multiples g) (SubgroupSum (Multiples a) (Multiples b))
          (inverse (Subtypes Int) (SubgroupSum (Multiples a) (Multiples b)) (Multiples g) (nat_gcd_sum a b)) (self_multiple g)))

{` The meet of principal orders is the principal order of the gcd. `}
def principal_meet_gcd (a b : Nat)
  : Id Order (order_meet (principal_order a) (principal_order b)) (principal_order (nat_gcd a b))
  ≔ let Ha ≔ order_periods (principal_order a) in let Hb ≔ order_periods (principal_order b) in
    order_periods_injective (order_meet (principal_order a) (principal_order b)) (principal_order (nat_gcd a b)) (calc
      order_periods (order_meet (principal_order a) (principal_order b)) = SubgroupSum Ha Hb
        by subgroup_cycle_periods (SubgroupSum Ha Hb)
          (subgroup_sum_laws Ha Hb (order_subgroup_laws (principal_order a)) (order_subgroup_laws (principal_order b)))
      = SubgroupSum (Multiples a) (Multiples b) by refl SubgroupSum (principal_order_periods a) (principal_order_periods b)
      = Multiples (nat_gcd a b) by nat_gcd_sum a b
      = order_periods (principal_order (nat_gcd a b))
        by inverse (Subtypes Int) (order_periods (principal_order (nat_gcd a b))) (Multiples (nat_gcd a b))
          (principal_order_periods (nat_gcd a b)) ∎)

{` lcm as the least positive common multiple. `}
def multiples_decidable (n : Nat) (z : Int) : Decidable (Multiples (suc. n) z .fst)
  ≔ transport (Subtypes Int) (H ↦ Decidable (H z .fst)) (CyclePeriods (finite_standard_cycle n)) (Multiples (suc. n))
      (finite_standard_periods n) (cycle_period_decidable (finite_standard_cycle n) (remainder_decidable_equality (suc. n)) z)

def product_decidability (A B : Type) (da : Decidable A) (db : Decidable B) : Decidable (Product A B)
  ≔ match da [
  | inl. x ↦ match db [ inl. y ↦ inl. (x, y) | inr. ny ↦ inr. (p ↦ ny (p .snd)) ]
  | inr. nx ↦ inr. (p ↦ nx (p .fst)) ]

def lcm_positive_search (a b : Nat)
  : Σ Nat (IsMinimum (PositiveSubgroupMember (SubgroupIntersection (Multiples (suc. a)) (Multiples (suc. b)))))
  ≔ let H ≔ SubgroupIntersection (Multiples (suc. a)) (Multiples (suc. b)) in
    let k ≔ add (mul (suc. a) b) a in
    minimum_from_witness (PositiveSubgroupMember H)
      (j ↦ product_decidability (Multiples (suc. a) (pos. (suc. j)) .fst) (Multiples (suc. b) (pos. (suc. j)) .fst)
        (multiples_decidable a (pos. (suc. j))) (multiples_decidable b (pos. (suc. j))))
      k
      (mere (MultipleWitness (suc. a) (pos. (suc. k)))
         (pos. (suc. b), concat Int (pos. (mul (suc. a) (suc. b))) (pos. (mul (suc. b) (suc. a)))
           (int_mul (pos. (suc. b)) (pos. (suc. a)))
           (refl ((j ↦ pos. j) : Nat → Int) (mul_comm (suc. a) (suc. b))) (int_mul_naturals (suc. b) (suc. a))),
       mere (MultipleWitness (suc. b) (pos. (suc. k))) (pos. (suc. a), int_mul_naturals (suc. a) (suc. b)))

def nat_lcm (a b : Nat) : Nat
  ≔ match a [ zero. ↦ zero. | suc. a ↦ match b [ zero. ↦ zero. | suc. b ↦ suc. (lcm_positive_search a b .fst) ] ]

def zero_intersection_left (b : Nat)
  : Id (Subtypes Int) (SubgroupIntersection (Multiples zero.) (Multiples b)) (Multiples zero.)
  ≔ inclusion_antisym Int (SubgroupIntersection (Multiples zero.) (Multiples b)) (Multiples zero.)
      (z p ↦ p .fst)
      (z p ↦ (p, mere_rec (MultipleWitness zero. z) (Multiples b z .fst) (Multiples b z .snd)
        (v ↦ transport Int (k ↦ Multiples b k .fst) int_zero z (inverse Int z int_zero (v .snd)) (multiples_laws b .fst)) p))

def zero_intersection_right (a : Nat)
  : Id (Subtypes Int) (SubgroupIntersection (Multiples a) (Multiples zero.)) (Multiples zero.)
  ≔ inclusion_antisym Int (SubgroupIntersection (Multiples a) (Multiples zero.)) (Multiples zero.)
      (z p ↦ p .snd)
      (z p ↦ (mere_rec (MultipleWitness zero. z) (Multiples a z .fst) (Multiples a z .snd)
        (v ↦ transport Int (k ↦ Multiples a k .fst) int_zero z (inverse Int z int_zero (v .snd)) (multiples_laws a .fst)) p, p))

def nat_lcm_intersection (a b : Nat)
  : Id (Subtypes Int) (SubgroupIntersection (Multiples a) (Multiples b)) (Multiples (nat_lcm a b))
  ≔ match a [
  | zero. ↦ zero_intersection_left b
  | suc. a ↦ match b [
    | zero. ↦ zero_intersection_right (suc. a)
    | suc. b ↦ least_subgroup_is_multiples (SubgroupIntersection (Multiples (suc. a)) (Multiples (suc. b)))
        (subgroup_intersection_laws (Multiples (suc. a)) (Multiples (suc. b)) (multiples_laws (suc. a)) (multiples_laws (suc. b)))
        (lcm_positive_search a b .fst) (lcm_positive_search a b .snd) ] ]

def nat_lcm_multiple_left (a b : Nat) : NatDivides a (nat_lcm a b)
  ≔ let l ≔ nat_lcm a b in
    mere_rec (MultipleWitness a (pos. l)) (NatDivides a l) (nat_divides_prop a l) (multiple_nat_divides a l)
      (transport (Subtypes Int) (H ↦ H (pos. l) .fst) (Multiples l) (SubgroupIntersection (Multiples a) (Multiples b))
        (inverse (Subtypes Int) (SubgroupIntersection (Multiples a) (Multiples b)) (Multiples l) (nat_lcm_intersection a b))
        (self_multiple l) .fst)

def nat_lcm_multiple_right (a b : Nat) : NatDivides b (nat_lcm a b)
  ≔ let l ≔ nat_lcm a b in
    mere_rec (MultipleWitness b (pos. l)) (NatDivides b l) (nat_divides_prop b l) (multiple_nat_divides b l)
      (transport (Subtypes Int) (H ↦ H (pos. l) .fst) (Multiples l) (SubgroupIntersection (Multiples a) (Multiples b))
        (inverse (Subtypes Int) (SubgroupIntersection (Multiples a) (Multiples b)) (Multiples l) (nat_lcm_intersection a b))
        (self_multiple l) .snd)

def nat_lcm_least (a b c : Nat) (ha : NatDivides a c) (hb : NatDivides b c) : NatDivides (nat_lcm a b) c
  ≔ let l ≔ nat_lcm a b in
    mere_rec (MultipleWitness l (pos. c)) (NatDivides l c) (nat_divides_prop l c) (multiple_nat_divides l c)
      (transport (Subtypes Int) (H ↦ H (pos. c) .fst) (SubgroupIntersection (Multiples a) (Multiples b)) (Multiples l)
        (nat_lcm_intersection a b)
        (nat_divides_multiples a c ha (pos. c) (self_multiple c), nat_divides_multiples b c hb (pos. c) (self_multiple c)))

{` The join of principal orders is the principal order of the lcm. `}
def principal_join_lcm (a b : Nat)
  : Id Order (order_join (principal_order a) (principal_order b)) (principal_order (nat_lcm a b))
  ≔ let Ha ≔ order_periods (principal_order a) in let Hb ≔ order_periods (principal_order b) in
    order_periods_injective (order_join (principal_order a) (principal_order b)) (principal_order (nat_lcm a b)) (calc
      order_periods (order_join (principal_order a) (principal_order b)) = SubgroupIntersection Ha Hb
        by subgroup_cycle_periods (SubgroupIntersection Ha Hb)
          (subgroup_intersection_laws Ha Hb (order_subgroup_laws (principal_order a)) (order_subgroup_laws (principal_order b)))
      = SubgroupIntersection (Multiples a) (Multiples b)
        by refl SubgroupIntersection (principal_order_periods a) (principal_order_periods b)
      = Multiples (nat_lcm a b) by nat_lcm_intersection a b
      = order_periods (principal_order (nat_lcm a b))
        by inverse (Subtypes Int) (order_periods (principal_order (nat_lcm a b))) (Multiples (nat_lcm a b))
          (principal_order_periods (nat_lcm a b)) ∎)
