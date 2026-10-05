export "568-s2-acts-on-c3"
export "475-standard-bicycle-normality"

{` Chapter 8 (congp.tex 60-95): the "bidirectional cycle" (X, f) attached to a
   2-element set S and an order n.

   Orders enter through their subgroups of periods: n ↦ (H, h) with
   H = order_periods n and h its subgroup laws (module 69), so Z/~_n is
   SubgroupQuotient H h and the standard n-cycle is subgroup_cycle H h
   (standard_cycle n ≡ subgroup_cycle (order_periods n) (order_subgroup_laws n)).
   Everything below is stated for an arbitrary subgroup (H, h) of Z.

   X ≔ (S × Z)/~ with (s,z) ~ (s',z') iff (s = s' and z ~_n z') or
   (s ≠ s' and z ~_n -z'), i.e. z - z' ∈ H, resp. z + z' ∈ H.  The two cases
   exclude each other, so the relation is proposition-valued without using
   decidability; transitivity in the case s ≠ s' ≠ s'' uses that S has two
   elements (footnote "check that ~ defines an equivalence relation").
   f_s[(s,z)] ≔ [(s,z+1)] and f_s[(s',z)] ≔ [(s',z-1)] for s' ≠ s is defined by
   the universal property of the set quotient (xca, congp.tex:79, first
   part), with the case split given by the decidable equality of S. `}

def DihedralPair (S : TwoElementSets) : Type ≔ Product (two_set_carrier S) Int

def DihedralRel (S : TwoElementSets) (H : Subtypes Int) (u v : DihedralPair S) : Type
  ≔ Sum (Product (Id (two_set_carrier S) (u .fst) (v .fst)) (SubgroupMember H (int_sub (u .snd) (v .snd))))
        (Product (Not (Id (two_set_carrier S) (u .fst) (v .fst))) (SubgroupMember H (int_add (u .snd) (v .snd))))

def dihedral_rel_prop (S : TwoElementSets) (H : Subtypes Int) (u v : DihedralPair S) : isProp (DihedralRel S H u v)
  ≔ disjoint_sum_prop
      (Product (Id (two_set_carrier S) (u .fst) (v .fst)) (SubgroupMember H (int_sub (u .snd) (v .snd))))
      (Product (Not (Id (two_set_carrier S) (u .fst) (v .fst))) (SubgroupMember H (int_add (u .snd) (v .snd))))
      (product_prop (Id (two_set_carrier S) (u .fst) (v .fst)) (SubgroupMember H (int_sub (u .snd) (v .snd)))
        (S .fst .snd (u .fst) (v .fst)) (H (int_sub (u .snd) (v .snd)) .snd))
      (product_prop (Not (Id (two_set_carrier S) (u .fst) (v .fst))) (SubgroupMember H (int_add (u .snd) (v .snd)))
        (negation_prop (Id (two_set_carrier S) (u .fst) (v .fst))) (H (int_add (u .snd) (v .snd)) .snd))
      (a b ↦ b .fst (a .fst))

{` Integer identities used for symmetry and transitivity. `}
def dihedral_int_cancel (x y c : Int) : Id Int (int_add (int_add x c) (int_add y (int_neg c))) (int_add x y)
  ≔ calc
      int_add (int_add x c) (int_add y (int_neg c)) = int_add x (int_add c (int_add y (int_neg c)))
        by int_add_assoc x c (int_add y (int_neg c))
      = int_add x (int_add (int_add y (int_neg c)) c)
        by refl (int_add x) (int_add_comm c (int_add y (int_neg c)))
      = int_add x y by refl (int_add x) (int_sub_add y c) ∎

def dihedral_int_same_diff (x y z : Int) : Id Int (int_add (int_sub x y) (int_add y z)) (int_add x z)
  ≔ calc
      int_add (int_sub x y) (int_add y z) = int_add (int_add z y) (int_sub x y)
        by concat Int (int_add (int_sub x y) (int_add y z)) (int_add (int_add y z) (int_sub x y))
             (int_add (int_add z y) (int_sub x y))
             (int_add_comm (int_sub x y) (int_add y z)) (refl (x' ↦ int_add x' (int_sub x y)) (int_add_comm y z))
      = int_add z x by dihedral_int_cancel z x y
      = int_add x z by int_add_comm z x ∎

def dihedral_int_diff_same (x y z : Int) : Id Int (int_add (int_add x y) (int_neg (int_sub y z))) (int_add x z)
  ≔ concat Int (int_add (int_add x y) (int_neg (int_sub y z))) (int_add (int_add x y) (int_add z (int_neg y)))
      (int_add x z) (refl (int_add (int_add x y)) (int_neg_sub y z)) (dihedral_int_cancel x z y)

def dihedral_int_diff_diff (x y z : Int) : Id Int (int_add (int_add x y) (int_neg (int_add y z))) (int_sub x z)
  ≔ calc
      int_add (int_add x y) (int_neg (int_add y z)) = int_add (int_add x y) (int_add (int_neg y) (int_neg z))
        by refl (int_add (int_add x y)) (int_neg_additive y z)
      = int_add (int_add x y) (int_add (int_neg z) (int_neg y))
        by refl (int_add (int_add x y)) (int_add_comm (int_neg y) (int_neg z))
      = int_sub x z by dihedral_int_cancel x (int_neg z) y ∎

def dihedral_int_succ_pred (x y : Int) : Id Int (int_add (int_succ x) (int_pred y)) (int_add x y)
  ≔ dihedral_int_cancel x y (pos. (suc. zero.))

def dihedral_int_pred_succ (x y : Int) : Id Int (int_add (int_pred x) (int_succ y)) (int_add x y)
  ≔ dihedral_int_cancel x y (neg. zero.)

{` In a 2-element set, s ≠ s' and s' ≠ s'' imply s = s''. `}
def dihedral_two_set_cancel (S : TwoElementSets) (s s' s'' : two_set_carrier S)
  (a : Not (Id (two_set_carrier S) s s')) (b : Not (Id (two_set_carrier S) s' s''))
  : Id (two_set_carrier S) s s''
  ≔ concat (two_set_carrier S) s (two_set_swap S s') s''
      (two_set_other_is_swap S s' s a)
      (inverse (two_set_carrier S) s'' (two_set_swap S s')
        (two_set_other_is_swap S s' s'' (q ↦ b (inverse (two_set_carrier S) s'' s' q))))

def dihedral_rel_symmetric (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  (u v : DihedralPair S) (r : DihedralRel S H u v) : DihedralRel S H v u
  ≔ match r [
  | inl. a ↦ inl. (inverse (two_set_carrier S) (u .fst) (v .fst) (a .fst),
      refl (SubgroupMember H) (int_neg_sub (u .snd) (v .snd)) .trr (h .snd .snd (int_sub (u .snd) (v .snd)) (a .snd)))
  | inr. b ↦ inr. (p ↦ b .fst (inverse (two_set_carrier S) (v .fst) (u .fst) p),
      refl (SubgroupMember H) (int_add_comm (u .snd) (v .snd)) .trr (b .snd)) ]

def dihedral_rel_transitive (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  (u v w : DihedralPair S) (r1 : DihedralRel S H u v) (r2 : DihedralRel S H v w) : DihedralRel S H u w
  ≔ match r1, r2 [
  | inl. a, inl. b ↦ inl. (concat (two_set_carrier S) (u .fst) (v .fst) (w .fst) (a .fst) (b .fst),
      refl (SubgroupMember H) (int_sub_chain (u .snd) (v .snd) (w .snd)) .trr
        (h .snd .fst (int_sub (u .snd) (v .snd)) (int_sub (v .snd) (w .snd)) (a .snd) (b .snd)))
  | inl. a, inr. b ↦ inr. (p ↦ b .fst (concat (two_set_carrier S) (v .fst) (u .fst) (w .fst)
        (inverse (two_set_carrier S) (u .fst) (v .fst) (a .fst)) p),
      refl (SubgroupMember H) (dihedral_int_same_diff (u .snd) (v .snd) (w .snd)) .trr
        (h .snd .fst (int_sub (u .snd) (v .snd)) (int_add (v .snd) (w .snd)) (a .snd) (b .snd)))
  | inr. a, inl. b ↦ inr. (p ↦ a .fst (concat (two_set_carrier S) (u .fst) (w .fst) (v .fst) p
        (inverse (two_set_carrier S) (v .fst) (w .fst) (b .fst))),
      refl (SubgroupMember H) (dihedral_int_diff_same (u .snd) (v .snd) (w .snd)) .trr
        (h .snd .fst (int_add (u .snd) (v .snd)) (int_neg (int_sub (v .snd) (w .snd))) (a .snd)
          (h .snd .snd (int_sub (v .snd) (w .snd)) (b .snd))))
  | inr. a, inr. b ↦ inl. (dihedral_two_set_cancel S (u .fst) (v .fst) (w .fst) (a .fst) (b .fst),
      refl (SubgroupMember H) (dihedral_int_diff_diff (u .snd) (v .snd) (w .snd)) .trr
        (h .snd .fst (int_add (u .snd) (v .snd)) (int_neg (int_add (v .snd) (w .snd))) (a .snd)
          (h .snd .snd (int_add (v .snd) (w .snd)) (b .snd)))) ]

def dihedral_relation (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : EquivalenceRelation (DihedralPair S)
  ≔ ((u v ↦ (DihedralRel S H u v, dihedral_rel_prop S H u v)),
     (u ↦ inl. (refl (u .fst), refl (SubgroupMember H) (int_sub_self (u .snd)) .trl (h .fst))),
     (u v r ↦ dihedral_rel_symmetric S H h u v r),
     (u v w r1 r2 ↦ dihedral_rel_transitive S H h u v w r1 r2))

{` X ≔ (S × Z)/~, a set. `}
def DihedralCycleSet (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) : Type
  ≔ Quotient (DihedralPair S) (dihedral_relation S H h)

def dihedral_class (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S) (z : Int)
  : DihedralCycleSet S H h
  ≔ quotient_class (DihedralPair S) (dihedral_relation S H h) (s, z)

def dihedral_cycle_set_set (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : isSet (DihedralCycleSet S H h)
  ≔ quotient_set (DihedralPair S) (dihedral_relation S H h)

def dihedral_cycle_set (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) : SetTypes
  ≔ (DihedralCycleSet S H h, dihedral_cycle_set_set S H h)

def dihedral_class_path (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (u v : DihedralPair S)
  (r : DihedralRel S H u v)
  : Id (DihedralCycleSet S H h) (quotient_class (DihedralPair S) (dihedral_relation S H h) u)
      (quotient_class (DihedralPair S) (dihedral_relation S H h) v)
  ≔ quotient_encode (DihedralPair S) (dihedral_relation S H h) u v r

{` x_0 ≔ [(s,0)] is unambiguous since 0 ~_n -0: [(s,0)] = [(s',0)] for all s, s'. `}
def dihedral_zero_unambiguous (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  (s s' : two_set_carrier S)
  : Id (DihedralCycleSet S H h) (dihedral_class S H h s int_zero) (dihedral_class S H h s' int_zero)
  ≔ dihedral_class_path S H h (s, int_zero) (s', int_zero)
      (match two_set_decidable S s s' [
       | inl. p ↦ inl. (p, refl (SubgroupMember H) (int_sub_self int_zero) .trl (h .fst))
       | inr. n ↦ inr. (n, h .fst) ])

def dihedral_two_set_mere (S : TwoElementSets) : Mere (two_set_carrier S)
  ≔ two_set_prop_transfer (T ↦ Mere (T .fst)) (T ↦ mere_isprop (T .fst)) (mere (Fin two) s2c3_fin2_yes) S

def DihedralBasePoint (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) : Type
  ≔ Σ (DihedralCycleSet S H h) (x ↦ (s : two_set_carrier S) → Id (DihedralCycleSet S H h) x (dihedral_class S H h s int_zero))

def dihedral_base_point_prop (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : isProp (DihedralBasePoint S H h)
  ≔ u v ↦ subtype_equal (DihedralCycleSet S H h)
      (x ↦ (s : two_set_carrier S) → Id (DihedralCycleSet S H h) x (dihedral_class S H h s int_zero))
      (x ↦ pi_prop (two_set_carrier S) (s ↦ Id (DihedralCycleSet S H h) x (dihedral_class S H h s int_zero))
        (s ↦ dihedral_cycle_set_set S H h x (dihedral_class S H h s int_zero)))
      u v
      (mere_rec (two_set_carrier S) (Id (DihedralCycleSet S H h) (u .fst) (v .fst))
        (dihedral_cycle_set_set S H h (u .fst) (v .fst))
        (s ↦ concat (DihedralCycleSet S H h) (u .fst) (dihedral_class S H h s int_zero) (v .fst)
          (u .snd s) (inverse (DihedralCycleSet S H h) (v .fst) (dihedral_class S H h s int_zero) (v .snd s)))
        (dihedral_two_set_mere S))

def dihedral_base_point_witness (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H)
  : DihedralBasePoint S H h
  ≔ mere_rec (two_set_carrier S) (DihedralBasePoint S H h) (dihedral_base_point_prop S H h)
      (s ↦ (dihedral_class S H h s int_zero, s' ↦ dihedral_zero_unambiguous S H h s s'))
      (dihedral_two_set_mere S)

{` x_0 : X, constructed without choosing s. `}
def dihedral_base_point (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) : DihedralCycleSet S H h
  ≔ dihedral_base_point_witness S H h .fst

def dihedral_decidable_prop (P : Type) (hP : isProp P) : isProp (Decidable P)
  ≔ disjoint_sum_prop P (Not P) hP (negation_prop P) (p n ↦ n p)

{` The step z ↦ z ± 1 used by f_s at (s', z), by the decision s' = s. `}
def dihedral_step (A : Type) (s s' : A) (d : Decidable (Id A s' s)) (z : Int) : Int
  ≔ match d [ inl. _ ↦ int_succ z | inr. _ ↦ int_pred z ]

def dihedral_step_pair (S : TwoElementSets) (s : two_set_carrier S) (u : DihedralPair S) : DihedralPair S
  ≔ (u .fst, dihedral_step (two_set_carrier S) s (u .fst) (two_set_decidable S (u .fst) s) (u .snd))

def dihedral_step_respects_same (S : TwoElementSets) (H : Subtypes Int) (s : two_set_carrier S)
  (u v : DihedralPair S) (a : Id (two_set_carrier S) (u .fst) (v .fst))
  (k : SubgroupMember H (int_sub (u .snd) (v .snd)))
  (du : Decidable (Id (two_set_carrier S) (u .fst) s)) (dv : Decidable (Id (two_set_carrier S) (v .fst) s))
  : DihedralRel S H (u .fst, dihedral_step (two_set_carrier S) s (u .fst) du (u .snd))
      (v .fst, dihedral_step (two_set_carrier S) s (v .fst) dv (v .snd))
  ≔ match du, dv [
  | inl. _, inl. _ ↦ inl. (a, refl (SubgroupMember H) (int_sub_translate (u .snd) (v .snd) (pos. (suc. zero.))) .trl k)
  | inl. p, inr. q ↦ match q (concat (two_set_carrier S) (v .fst) (u .fst) s
        (inverse (two_set_carrier S) (u .fst) (v .fst) a) p) []
  | inr. q, inl. p ↦ match q (concat (two_set_carrier S) (u .fst) (v .fst) s a p) []
  | inr. _, inr. _ ↦ inl. (a, refl (SubgroupMember H) (int_sub_translate (u .snd) (v .snd) (neg. zero.)) .trl k) ]

def dihedral_step_respects_other (S : TwoElementSets) (H : Subtypes Int) (s : two_set_carrier S)
  (u v : DihedralPair S) (a : Not (Id (two_set_carrier S) (u .fst) (v .fst)))
  (k : SubgroupMember H (int_add (u .snd) (v .snd)))
  (du : Decidable (Id (two_set_carrier S) (u .fst) s)) (dv : Decidable (Id (two_set_carrier S) (v .fst) s))
  : DihedralRel S H (u .fst, dihedral_step (two_set_carrier S) s (u .fst) du (u .snd))
      (v .fst, dihedral_step (two_set_carrier S) s (v .fst) dv (v .snd))
  ≔ match du, dv [
  | inl. p, inl. q ↦ match a (concat (two_set_carrier S) (u .fst) s (v .fst) p
        (inverse (two_set_carrier S) (v .fst) s q)) []
  | inl. _, inr. _ ↦ inr. (a, refl (SubgroupMember H) (dihedral_int_succ_pred (u .snd) (v .snd)) .trl k)
  | inr. _, inl. _ ↦ inr. (a, refl (SubgroupMember H) (dihedral_int_pred_succ (u .snd) (v .snd)) .trl k)
  | inr. p, inr. q ↦ match a (dihedral_two_set_cancel S (u .fst) s (v .fst) p
        (e ↦ q (inverse (two_set_carrier S) s (v .fst) e))) [] ]

def dihedral_step_respects (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  (u v : DihedralPair S) (r : DihedralRel S H u v)
  : DihedralRel S H (dihedral_step_pair S s u) (dihedral_step_pair S s v)
  ≔ match r [
  | inl. a ↦ dihedral_step_respects_same S H s u v (a .fst) (a .snd)
      (two_set_decidable S (u .fst) s) (two_set_decidable S (v .fst) s)
  | inr. b ↦ dihedral_step_respects_other S H s u v (b .fst) (b .snd)
      (two_set_decidable S (u .fst) s) (two_set_decidable S (v .fst) s) ]

{` xca (congp.tex:79), first part: f is well defined by the universal
   property of the set quotient; f_s [(s',z)] computes judgmentally to
   [(s', z ± 1)] (quotient_rec_beta is refl). `}
def dihedral_move (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  : DihedralCycleSet S H h → DihedralCycleSet S H h
  ≔ quotient_rec (DihedralPair S) (DihedralCycleSet S H h) (dihedral_relation S H h) (dihedral_cycle_set_set S H h)
      (u ↦ quotient_class (DihedralPair S) (dihedral_relation S H h) (dihedral_step_pair S s u))
      (u v r ↦ dihedral_class_path S H h (dihedral_step_pair S s u) (dihedral_step_pair S s v)
        (dihedral_step_respects S H h s u v r))

def dihedral_move_self (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S) (z : Int)
  : Id (DihedralCycleSet S H h) (dihedral_move S H h s (dihedral_class S H h s z)) (dihedral_class S H h s (int_succ z))
  ≔ refl ((d ↦ dihedral_class S H h s (dihedral_step (two_set_carrier S) s s d z))
          : Decidable (Id (two_set_carrier S) s s) → DihedralCycleSet S H h)
      (dihedral_decidable_prop (Id (two_set_carrier S) s s) (S .fst .snd s s) (two_set_decidable S s s) (inl. (refl s)))

def dihedral_move_other (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s s' : two_set_carrier S)
  (n : Not (Id (two_set_carrier S) s' s)) (z : Int)
  : Id (DihedralCycleSet S H h) (dihedral_move S H h s (dihedral_class S H h s' z)) (dihedral_class S H h s' (int_pred z))
  ≔ refl ((d ↦ dihedral_class S H h s' (dihedral_step (two_set_carrier S) s s' d z))
          : Decidable (Id (two_set_carrier S) s' s) → DihedralCycleSet S H h)
      (dihedral_decidable_prop (Id (two_set_carrier S) s' s) (S .fst .snd s' s) (two_set_decidable S s' s) (inr. n))

{` The point (X, f) of T_S = Σ_{X:Set} (S → (X → X)) (module 568's S2C3Type). `}
def dihedral_point (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) : S2C3Type S
  ≔ (dihedral_cycle_set S H h, s ↦ dihedral_move S H h s)
