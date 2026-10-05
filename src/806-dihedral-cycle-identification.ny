export "805-dihedral-cycle-quotients"

{` Chapter 8 (congp.tex 87-91): "for any s : S, we can let s be the forwards
   direction, and get an identification (X, f_s) = (Z/~_n, z_s) by sending
   [(s,z)] to [z] (and [(s',z)] to [-z] for s' ≠ s)".

   dihedral_eval S H h s is that map; dihedral_insert is z ↦ [(s,z)]; they are
   inverse, and dihedral_eval ∘ f_s = succ ∘ dihedral_eval.  Hence f_s is an
   equivalence, (X, f_s) is a cycle, and it is identified with the standard
   cycle subgroup_cycle H h = (Z/H, succ) in Cycles (dihedral_cycle_path). `}

def dihedral_sign (A : Type) (s s' : A) (d : Decidable (Id A s' s)) (z : Int) : Int
  ≔ match d [ inl. _ ↦ z | inr. _ ↦ int_neg z ]

def dihedral_sign_respects_same (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  (u v : DihedralPair S) (a : Id (two_set_carrier S) (u .fst) (v .fst))
  (k : SubgroupMember H (int_sub (u .snd) (v .snd)))
  (du : Decidable (Id (two_set_carrier S) (u .fst) s)) (dv : Decidable (Id (two_set_carrier S) (v .fst) s))
  : SubgroupMember H (int_sub (dihedral_sign (two_set_carrier S) s (u .fst) du (u .snd))
      (dihedral_sign (two_set_carrier S) s (v .fst) dv (v .snd)))
  ≔ match du, dv [
  | inl. _, inl. _ ↦ k
  | inl. p, inr. q ↦ match q (concat (two_set_carrier S) (v .fst) (u .fst) s
        (inverse (two_set_carrier S) (u .fst) (v .fst) a) p) []
  | inr. q, inl. p ↦ match q (concat (two_set_carrier S) (u .fst) (v .fst) s a p) []
  | inr. _, inr. _ ↦ refl (SubgroupMember H) (int_neg_additive (u .snd) (int_neg (v .snd))) .trr
      (h .snd .snd (int_sub (u .snd) (v .snd)) k) ]

def dihedral_sign_respects_other (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  (u v : DihedralPair S) (a : Not (Id (two_set_carrier S) (u .fst) (v .fst)))
  (k : SubgroupMember H (int_add (u .snd) (v .snd)))
  (du : Decidable (Id (two_set_carrier S) (u .fst) s)) (dv : Decidable (Id (two_set_carrier S) (v .fst) s))
  : SubgroupMember H (int_sub (dihedral_sign (two_set_carrier S) s (u .fst) du (u .snd))
      (dihedral_sign (two_set_carrier S) s (v .fst) dv (v .snd)))
  ≔ match du, dv [
  | inl. p, inl. q ↦ match a (concat (two_set_carrier S) (u .fst) s (v .fst) p
        (inverse (two_set_carrier S) (v .fst) s q)) []
  | inl. _, inr. _ ↦ refl (SubgroupMember H) (refl (int_add (u .snd)) (int_neg_neg (v .snd))) .trl k
  | inr. _, inl. _ ↦ refl (SubgroupMember H) (int_neg_additive (u .snd) (v .snd)) .trr
      (h .snd .snd (int_add (u .snd) (v .snd)) k)
  | inr. p, inr. q ↦ match a (dihedral_two_set_cancel S (u .fst) s (v .fst) p
        (e ↦ q (inverse (two_set_carrier S) s (v .fst) e))) [] ]

def dihedral_sign_pair (S : TwoElementSets) (s : two_set_carrier S) (u : DihedralPair S) : Int
  ≔ dihedral_sign (two_set_carrier S) s (u .fst) (two_set_decidable S (u .fst) s) (u .snd)

def dihedral_sign_respects (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  (u v : DihedralPair S) (r : DihedralRel S H u v)
  : SubgroupMember H (int_sub (dihedral_sign_pair S s u) (dihedral_sign_pair S s v))
  ≔ match r [
  | inl. a ↦ dihedral_sign_respects_same S H h s u v (a .fst) (a .snd)
      (two_set_decidable S (u .fst) s) (two_set_decidable S (v .fst) s)
  | inr. b ↦ dihedral_sign_respects_other S H h s u v (b .fst) (b .snd)
      (two_set_decidable S (u .fst) s) (two_set_decidable S (v .fst) s) ]

{` [(s,z)] ↦ [z], [(s',z)] ↦ [-z]. `}
def dihedral_eval (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  : DihedralCycleSet S H h → SubgroupQuotient H h
  ≔ quotient_rec (DihedralPair S) (SubgroupQuotient H h) (dihedral_relation S H h) (subgroup_quotient_set H h)
      (u ↦ subgroup_class H h (dihedral_sign_pair S s u))
      (u v r ↦ quotient_encode Int (subgroup_relation H h) (dihedral_sign_pair S s u) (dihedral_sign_pair S s v)
        (dihedral_sign_respects S H h s u v r))

{` z ↦ [(s,z)]. `}
def dihedral_insert (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  : SubgroupQuotient H h → DihedralCycleSet S H h
  ≔ quotient_rec Int (DihedralCycleSet S H h) (subgroup_relation H h) (dihedral_cycle_set_set S H h)
      (z ↦ dihedral_class S H h s z)
      (x y r ↦ dihedral_class_path S H h (s, x) (s, y) (inl. (refl s, r)))

def dihedral_eval_insert_at (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  (z : Int) (d : Decidable (Id (two_set_carrier S) s s))
  : Id (SubgroupQuotient H h) (subgroup_class H h (dihedral_sign (two_set_carrier S) s s d z)) (subgroup_class H h z)
  ≔ match d [
  | inl. _ ↦ refl (subgroup_class H h z)
  | inr. n ↦ match n (refl s) [] ]

def dihedral_eval_insert (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  (q : SubgroupQuotient H h) : Id (SubgroupQuotient H h) (dihedral_eval S H h s (dihedral_insert S H h s q)) q
  ≔ quotient_prop_induction Int (subgroup_relation H h)
      (q ↦ Id (SubgroupQuotient H h) (dihedral_eval S H h s (dihedral_insert S H h s q)) q)
      (q ↦ subgroup_quotient_set H h (dihedral_eval S H h s (dihedral_insert S H h s q)) q)
      (z ↦ dihedral_eval_insert_at S H h s z (two_set_decidable S s s)) q

def dihedral_insert_eval_at (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s s' : two_set_carrier S)
  (z : Int) (d : Decidable (Id (two_set_carrier S) s' s))
  : Id (DihedralCycleSet S H h) (dihedral_class S H h s (dihedral_sign (two_set_carrier S) s s' d z))
      (dihedral_class S H h s' z)
  ≔ match d [
  | inl. p ↦ dihedral_class_path S H h (s, z) (s', z)
      (inl. (inverse (two_set_carrier S) s' s p, refl (SubgroupMember H) (int_sub_self z) .trl (h .fst)))
  | inr. n ↦ dihedral_class_path S H h (s, int_neg z) (s', z)
      (inr. (q ↦ n (inverse (two_set_carrier S) s s' q), refl (SubgroupMember H) (int_add_neg_left z) .trl (h .fst))) ]

def dihedral_insert_eval (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  (x : DihedralCycleSet S H h) : Id (DihedralCycleSet S H h) (dihedral_insert S H h s (dihedral_eval S H h s x)) x
  ≔ quotient_prop_induction (DihedralPair S) (dihedral_relation S H h)
      (x ↦ Id (DihedralCycleSet S H h) (dihedral_insert S H h s (dihedral_eval S H h s x)) x)
      (x ↦ dihedral_cycle_set_set S H h (dihedral_insert S H h s (dihedral_eval S H h s x)) x)
      (u ↦ dihedral_insert_eval_at S H h s (u .fst) (u .snd) (two_set_decidable S (u .fst) s)) x

def dihedral_eval_equiv (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  : Equiv (DihedralCycleSet S H h) (SubgroupQuotient H h)
  ≔ quasi_inverse_equiv (DihedralCycleSet S H h) (SubgroupQuotient H h)
      (dihedral_eval S H h s) (dihedral_insert S H h s)
      (dihedral_insert_eval S H h s) (dihedral_eval_insert S H h s)

def dihedral_eval_move_at (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s s' : two_set_carrier S)
  (z : Int) (d : Decidable (Id (two_set_carrier S) s' s))
  : Id (SubgroupQuotient H h)
      (subgroup_class H h (dihedral_sign (two_set_carrier S) s s' d (dihedral_step (two_set_carrier S) s s' d z)))
      (subgroup_class H h (int_succ (dihedral_sign (two_set_carrier S) s s' d z)))
  ≔ match d [
  | inl. _ ↦ refl (subgroup_class H h (int_succ z))
  | inr. _ ↦ refl (subgroup_class H h) (dihedral_neg_pred z) ]

{` The commuting square: eval_s (f_s x) = succ (eval_s x). `}
def dihedral_eval_move (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  (x : DihedralCycleSet S H h)
  : Id (SubgroupQuotient H h) (dihedral_eval S H h s (dihedral_move S H h s x))
      (subgroup_successor H h .map (dihedral_eval S H h s x))
  ≔ quotient_prop_induction (DihedralPair S) (dihedral_relation S H h)
      (x ↦ Id (SubgroupQuotient H h) (dihedral_eval S H h s (dihedral_move S H h s x))
        (subgroup_successor H h .map (dihedral_eval S H h s x)))
      (x ↦ subgroup_quotient_set H h (dihedral_eval S H h s (dihedral_move S H h s x))
        (subgroup_successor H h .map (dihedral_eval S H h s x)))
      (u ↦ dihedral_eval_move_at S H h s (u .fst) (u .snd) (two_set_decidable S (u .fst) s)) x

{` f_s is an equivalence, with inverse insert ∘ pred ∘ eval. `}
def dihedral_move_inverse (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  (x : DihedralCycleSet S H h) : DihedralCycleSet S H h
  ≔ dihedral_insert S H h s (subgroup_translation H h (neg. zero.) (dihedral_eval S H h s x))

def dihedral_move_retraction (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  (x : DihedralCycleSet S H h)
  : Id (DihedralCycleSet S H h) (dihedral_move_inverse S H h s (dihedral_move S H h s x)) x
  ≔ calc
      dihedral_move_inverse S H h s (dihedral_move S H h s x)
        = dihedral_insert S H h s (subgroup_translation H h (neg. zero.)
            (subgroup_successor H h .map (dihedral_eval S H h s x)))
        by refl (q ↦ dihedral_insert S H h s (subgroup_translation H h (neg. zero.) q)) (dihedral_eval_move S H h s x)
      = dihedral_insert S H h s (dihedral_eval S H h s x)
        by refl (dihedral_insert S H h s)
             (subgroup_translation_inverse H h (pos. (suc. zero.)) (refl (dihedral_eval S H h s x)))
      = x by dihedral_insert_eval S H h s x ∎

def dihedral_move_section (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  (x : DihedralCycleSet S H h)
  : Id (DihedralCycleSet S H h) (dihedral_move S H h s (dihedral_move_inverse S H h s x)) x
  ≔ let q : SubgroupQuotient H h ≔ subgroup_translation H h (neg. zero.) (dihedral_eval S H h s x) in
    calc
      dihedral_move S H h s (dihedral_move_inverse S H h s x)
        = dihedral_insert S H h s (dihedral_eval S H h s (dihedral_move S H h s (dihedral_insert S H h s q)))
        by inverse (DihedralCycleSet S H h)
             (dihedral_insert S H h s (dihedral_eval S H h s (dihedral_move S H h s (dihedral_insert S H h s q))))
             (dihedral_move S H h s (dihedral_insert S H h s q))
             (dihedral_insert_eval S H h s (dihedral_move S H h s (dihedral_insert S H h s q)))
      = dihedral_insert S H h s (subgroup_successor H h .map (dihedral_eval S H h s (dihedral_insert S H h s q)))
        by refl (dihedral_insert S H h s) (dihedral_eval_move S H h s (dihedral_insert S H h s q))
      = dihedral_insert S H h s (subgroup_successor H h .map q)
        by refl (r ↦ dihedral_insert S H h s (subgroup_successor H h .map r)) (dihedral_eval_insert S H h s q)
      = dihedral_insert S H h s (dihedral_eval S H h s x)
        by refl (dihedral_insert S H h s)
             (subgroup_translation_inverse_other H h (pos. (suc. zero.)) (refl (dihedral_eval S H h s x)))
      = x by dihedral_insert_eval S H h s x ∎

def dihedral_move_equiv (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  : Equiv (DihedralCycleSet S H h) (DihedralCycleSet S H h)
  ≔ quasi_inverse_equiv (DihedralCycleSet S H h) (DihedralCycleSet S H h)
      (dihedral_move S H h s) (dihedral_move_inverse S H h s)
      (dihedral_move_retraction S H h s) (dihedral_move_section S H h s)

{` (X, f_s) as a permutation, and the identification with (Z/~_n, succ). `}
def dihedral_permutation (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  : Permutations
  ≔ (dihedral_cycle_set S H h, dihedral_move_equiv S H h s)

def dihedral_permutation_iso (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  : PermutationIsomorphisms (dihedral_permutation S H h s) (subgroup_cycle H h .fst)
  ≔ (dihedral_eval_equiv S H h s, x ↦ dihedral_eval_move S H h s x)

def dihedral_permutation_path (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  : Id Permutations (dihedral_permutation S H h s) (subgroup_cycle H h .fst)
  ≔ equiv_inverse_map (Id Permutations (dihedral_permutation S H h s) (subgroup_cycle H h .fst))
      (PermutationIsomorphisms (dihedral_permutation S H h s) (subgroup_cycle H h .fst))
      (permutation_paths_equiv (dihedral_permutation S H h s) (subgroup_cycle H h .fst))
      (dihedral_permutation_iso S H h s)

def dihedral_permutation_cyclic (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  : cyclic_permutation (dihedral_permutation S H h s)
  ≔ transport Permutations cyclic_permutation (subgroup_cycle H h .fst) (dihedral_permutation S H h s)
      (inverse Permutations (dihedral_permutation S H h s) (subgroup_cycle H h .fst) (dihedral_permutation_path S H h s))
      (subgroup_cycle H h .snd)

def dihedral_cycle (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S) : Cycles
  ≔ (dihedral_permutation S H h s, dihedral_permutation_cyclic S H h s)

{` The identification (X, f_s) = (Z/~_n, succ) of congp.tex:89. `}
def dihedral_cycle_path (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S)
  : Id Cycles (dihedral_cycle S H h s) (subgroup_cycle H h)
  ≔ subtype_equal Permutations cyclic_permutation (p ↦ cyclic_prop (p .fst .fst) (p .snd))
      (dihedral_cycle S H h s) (subgroup_cycle H h) (dihedral_permutation_path S H h s)

{` The map underlying the identification sends [(s,z)] to [z] and [(s',z)]
   to [-z] for s' ≠ s (judgmentally, by quotient_rec_beta). `}
def dihedral_eval_self (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s : two_set_carrier S) (z : Int)
  : Id (SubgroupQuotient H h) (dihedral_eval S H h s (dihedral_class S H h s z)) (subgroup_class H h z)
  ≔ dihedral_eval_insert_at S H h s z (two_set_decidable S s s)

def dihedral_eval_other_at (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s s' : two_set_carrier S)
  (n : Not (Id (two_set_carrier S) s' s)) (z : Int) (d : Decidable (Id (two_set_carrier S) s' s))
  : Id (SubgroupQuotient H h) (subgroup_class H h (dihedral_sign (two_set_carrier S) s s' d z)) (subgroup_class H h (int_neg z))
  ≔ match d [
  | inl. p ↦ match n p []
  | inr. _ ↦ refl (subgroup_class H h (int_neg z)) ]

def dihedral_eval_other (S : TwoElementSets) (H : Subtypes Int) (h : IntegerSubgroupLaws H) (s s' : two_set_carrier S)
  (n : Not (Id (two_set_carrier S) s' s)) (z : Int)
  : Id (SubgroupQuotient H h) (dihedral_eval S H h s (dihedral_class S H h s' z)) (subgroup_class H h (int_neg z))
  ≔ dihedral_eval_other_at S H h s s' n z (two_set_decidable S s' s)
