export "143-infinite-quotient-images"

{` Sum and intersection of subgroups of Z. `}
def SubgroupSumWitness (H K : Subtypes Int) (z : Int) : Type
  ≔ Σ Int (a ↦ Σ Int (b ↦ Product (Product (H a .fst) (K b .fst)) (Id Int z (int_add a b))))
def SubgroupSum (H K : Subtypes Int) : Subtypes Int
  ≔ z ↦ (Mere (SubgroupSumWitness H K z), mere_isprop (SubgroupSumWitness H K z))
def SubgroupIntersection (H K : Subtypes Int) : Subtypes Int
  ≔ z ↦ (Product (H z .fst) (K z .fst), product_prop (H z .fst) (K z .fst) (H z .snd) (K z .snd))

def subgroup_sum_laws (H K : Subtypes Int) (hH : IntegerSubgroupLaws H) (hK : IntegerSubgroupLaws K)
  : IntegerSubgroupLaws (SubgroupSum H K)
  ≔ (mere (SubgroupSumWitness H K int_zero) (int_zero, (int_zero, ((hH .fst, hK .fst), refl int_zero))),
     ((z w p q ↦ mere_rec (SubgroupSumWitness H K z) (SubgroupSum H K (int_add z w) .fst) (SubgroupSum H K (int_add z w) .snd)
        (u ↦ mere_rec (SubgroupSumWitness H K w) (SubgroupSum H K (int_add z w) .fst) (SubgroupSum H K (int_add z w) .snd)
          (v ↦ mere (SubgroupSumWitness H K (int_add z w))
            (int_add (u .fst) (v .fst), (int_add (u .snd .fst) (v .snd .fst),
              ((hH .snd .fst (u .fst) (v .fst) (u .snd .snd .fst .fst) (v .snd .snd .fst .fst),
                hK .snd .fst (u .snd .fst) (v .snd .fst) (u .snd .snd .fst .snd) (v .snd .snd .fst .snd)),
               calc
                int_add z w = int_add (int_add (u .fst) (u .snd .fst)) w
                  by refl ((y ↦ int_add y w) : Int → Int) (u .snd .snd .snd)
                = int_add (int_add (u .fst) (u .snd .fst)) (int_add (v .fst) (v .snd .fst))
                  by refl (int_add (int_add (u .fst) (u .snd .fst))) (v .snd .snd .snd)
                = int_add (int_add (u .fst) (v .fst)) (int_add (u .snd .fst) (v .snd .fst))
                  by int_add_interchange (u .fst) (u .snd .fst) (v .fst) (v .snd .fst) ∎)))) q) p),
      (z p ↦ mere_rec (SubgroupSumWitness H K z) (SubgroupSum H K (int_neg z) .fst) (SubgroupSum H K (int_neg z) .snd)
        (u ↦ mere (SubgroupSumWitness H K (int_neg z))
          (int_neg (u .fst), (int_neg (u .snd .fst),
            ((hH .snd .snd (u .fst) (u .snd .snd .fst .fst), hK .snd .snd (u .snd .fst) (u .snd .snd .fst .snd)),
             calc
              int_neg z = int_neg (int_add (u .fst) (u .snd .fst)) by refl int_neg (u .snd .snd .snd)
              = int_add (int_neg (u .fst)) (int_neg (u .snd .fst)) by int_neg_additive (u .fst) (u .snd .fst) ∎)))) p)))

def subgroup_intersection_laws (H K : Subtypes Int) (hH : IntegerSubgroupLaws H) (hK : IntegerSubgroupLaws K)
  : IntegerSubgroupLaws (SubgroupIntersection H K)
  ≔ ((hH .fst, hK .fst),
     ((z w p q ↦ (hH .snd .fst z w (p .fst) (q .fst), hK .snd .fst z w (p .snd) (q .snd))),
      (z p ↦ (hH .snd .snd z (p .fst), hK .snd .snd z (p .snd)))))

def order_periods_of_subgroup (H : Subtypes Int) (h : IntegerSubgroupLaws H) (z : Int)
  (p : H z .fst) : order_periods (subgroup_to_order (H, h)) z .fst
  ≔ transport (Subtypes Int) (S ↦ S z .fst) H (order_periods (subgroup_to_order (H, h)))
      (inverse (Subtypes Int) (order_periods (subgroup_to_order (H, h))) H (subgroup_cycle_periods H h)) p

def subgroup_of_order_periods (H : Subtypes Int) (h : IntegerSubgroupLaws H) (z : Int)
  (p : order_periods (subgroup_to_order (H, h)) z .fst) : H z .fst
  ≔ transport (Subtypes Int) (S ↦ S z .fst) (order_periods (subgroup_to_order (H, h))) H
      (subgroup_cycle_periods H h) p

{` gcd: the meet in (Order, |), with period subgroup H_d + H_k. `}
def order_meet (d k : Order) : Order
  ≔ subgroup_to_order (SubgroupSum (order_periods d) (order_periods k),
      subgroup_sum_laws (order_periods d) (order_periods k) (order_subgroup_laws d) (order_subgroup_laws k))

{` lcm: the join in (Order, |), with period subgroup H_d ∩ H_k. `}
def order_join (d k : Order) : Order
  ≔ subgroup_to_order (SubgroupIntersection (order_periods d) (order_periods k),
      subgroup_intersection_laws (order_periods d) (order_periods k) (order_subgroup_laws d) (order_subgroup_laws k))

def order_meet_divides_left (d k : Order) : OrderDivides (order_meet d k) d
  ≔ let H ≔ order_periods d in let K ≔ order_periods k in
    z p ↦ order_periods_of_subgroup (SubgroupSum H K)
      (subgroup_sum_laws H K (order_subgroup_laws d) (order_subgroup_laws k)) z
      (mere (SubgroupSumWitness H K z) (z, (int_zero, ((p, order_subgroup_laws k .fst), refl z))))

def order_meet_divides_right (d k : Order) : OrderDivides (order_meet d k) k
  ≔ let H ≔ order_periods d in let K ≔ order_periods k in
    z p ↦ order_periods_of_subgroup (SubgroupSum H K)
      (subgroup_sum_laws H K (order_subgroup_laws d) (order_subgroup_laws k)) z
      (mere (SubgroupSumWitness H K z) (int_zero, (z, ((order_subgroup_laws d .fst, p),
        inverse Int (int_add int_zero z) z (int_add_zero_left z)))))

def order_meet_greatest (d k e : Order) (hd : OrderDivides e d) (hk : OrderDivides e k)
  : OrderDivides e (order_meet d k)
  ≔ let H ≔ order_periods d in let K ≔ order_periods k in
    z p ↦ mere_rec (SubgroupSumWitness H K z) (order_periods e z .fst) (order_periods e z .snd)
      (u ↦ transport Int (w ↦ order_periods e w .fst) (int_add (u .fst) (u .snd .fst)) z
        (inverse Int z (int_add (u .fst) (u .snd .fst)) (u .snd .snd .snd))
        (order_subgroup_laws e .snd .fst (u .fst) (u .snd .fst)
          (hd (u .fst) (u .snd .snd .fst .fst)) (hk (u .snd .fst) (u .snd .snd .fst .snd))))
      (subgroup_of_order_periods (SubgroupSum H K)
        (subgroup_sum_laws H K (order_subgroup_laws d) (order_subgroup_laws k)) z p)

def order_join_divided_left (d k : Order) : OrderDivides d (order_join d k)
  ≔ let H ≔ order_periods d in let K ≔ order_periods k in
    z p ↦ subgroup_of_order_periods (SubgroupIntersection H K)
      (subgroup_intersection_laws H K (order_subgroup_laws d) (order_subgroup_laws k)) z p .fst

def order_join_divided_right (d k : Order) : OrderDivides k (order_join d k)
  ≔ let H ≔ order_periods d in let K ≔ order_periods k in
    z p ↦ subgroup_of_order_periods (SubgroupIntersection H K)
      (subgroup_intersection_laws H K (order_subgroup_laws d) (order_subgroup_laws k)) z p .snd

def order_join_least (d k e : Order) (hd : OrderDivides d e) (hk : OrderDivides k e)
  : OrderDivides (order_join d k) e
  ≔ let H ≔ order_periods d in let K ≔ order_periods k in
    z p ↦ order_periods_of_subgroup (SubgroupIntersection H K)
      (subgroup_intersection_laws H K (order_subgroup_laws d) (order_subgroup_laws k)) z (hd z p, hk z p)

{` The finite order 1 is least and the infinite order is greatest. `}
def one_divides (d : Order) : OrderDivides (principal_order (suc. zero.)) d
  ≔ z p ↦ transport (Subtypes Int) (S ↦ S z .fst) (Multiples (suc. zero.)) (CyclePeriods (finite_standard_cycle zero.))
      (inverse (Subtypes Int) (CyclePeriods (finite_standard_cycle zero.)) (Multiples (suc. zero.)) (finite_standard_periods zero.))
      (mere (MultipleWitness (suc. zero.) z) (z, refl z))

def divides_infinite (d : Order) : OrderDivides d infinite_order
  ≔ z p ↦ transport Int (w ↦ order_periods d w .fst) int_zero z
      (inverse Int z int_zero (infinite_period_is_zero z p)) (order_subgroup_laws d .fst)
