export "808-dihedral-group-cardinality"
export "873-s-action-paths"

{` Chapter 8, xca (congp.tex:79), second part: "give an identification of our
   (X, f) with that of ex:S2-acts-on-C3 when n is 3".

   For n = principal_order 3 and every 2-element set S, the map
   e : 1 ⊔ S → X, inl 0 ↦ x_0, inr t ↦ [(t, 1)], commutes with all f_t and is
   a bijection; this gives an identification (1 ⊔ S, f) = (X, f) in
   T_S = Σ_{X:Set} (S → (X → X)) (dihedral_three_point_path), hence
   C̃_3 = (S ↦ G(S)) as actions BΣ_2 → Group (dihedral_three_action_path,
   G = s2_acts_on_c3 of module 568), and D_3 = Σ_2 ⋉ G. The arithmetic facts
   3 ∈ 3Z and -1, 1, 2 ∉ 3Z are computed in the standard 3-cycle. `}

def dihedral_three_H : Subtypes Int ≔ order_periods (principal_order three)

def dihedral_three_laws : IntegerSubgroupLaws dihedral_three_H ≔ order_subgroup_laws (principal_order three)

def dihedral_three_remainder_zero : Remainder three ≔ remainder_at two zero. star.

def dihedral_three_period (z : Int) (k : SubgroupMember dihedral_three_H z)
  : Id (Remainder three) (permutation_power (Remainder three) (modular_successor_equiv two) z dihedral_three_remainder_zero)
      dihedral_three_remainder_zero
  ≔ k (refl dihedral_three_remainder_zero)

def dihedral_three_not_minus_one (k : SubgroupMember dihedral_three_H (neg. zero.)) : Empty
  ≔ nat_encode two zero. (refl ((r ↦ r .fst) : Remainder three → Nat) (dihedral_three_period (neg. zero.) k))

def dihedral_three_not_one (k : SubgroupMember dihedral_three_H (pos. (suc. zero.))) : Empty
  ≔ nat_encode (suc. zero.) zero. (refl ((r ↦ r .fst) : Remainder three → Nat) (dihedral_three_period (pos. (suc. zero.)) k))

def dihedral_three_not_two (k : SubgroupMember dihedral_three_H (pos. two)) : Empty
  ≔ nat_encode two zero. (refl ((r ↦ r .fst) : Remainder three → Nat) (dihedral_three_period (pos. two) k))

def dihedral_three_three : SubgroupMember dihedral_three_H (pos. three)
  ≔ refl ((K ↦ SubgroupMember K (pos. three)) : Subtypes Int → Type) (principal_order_periods three) .trl
      (multiple_of three (pos. (suc. zero.)))

{` The arithmetic of 3Z used below, as hypotheses on a subgroup H (keeps the
   period predicate of the standard 3-cycle opaque during checking). `}
def DihedralThreeFacts (H : Subtypes Int) : Type
  ≔ Product (SubgroupMember H (pos. three))
      (Product (Not (SubgroupMember H (neg. zero.)))
        (Product (Not (SubgroupMember H (pos. (suc. zero.)))) (Not (SubgroupMember H (pos. two)))))

def dihedral_three_facts : DihedralThreeFacts dihedral_three_H
  ≔ (dihedral_three_three, (k ↦ dihedral_three_not_minus_one k, (k ↦ dihedral_three_not_one k, k ↦ dihedral_three_not_two k)))

def DihedralThreeSet (H : Subtypes Int) (h : IntegerSubgroupLaws H) (F : DihedralThreeFacts H) (S : TwoElementSets) : Type ≔ DihedralCycleSet S H h

def dihedral_three_class (H : Subtypes Int) (h : IntegerSubgroupLaws H) (F : DihedralThreeFacts H) (S : TwoElementSets) (t : two_set_carrier S) (z : Int) : DihedralThreeSet H h F S
  ≔ dihedral_class S H h t z

def dihedral_three_base_class (H : Subtypes Int) (h : IntegerSubgroupLaws H) (F : DihedralThreeFacts H) (S : TwoElementSets) (t : two_set_carrier S)
  : Id (DihedralThreeSet H h F S) (dihedral_base_point S H h) (dihedral_three_class H h F S t int_zero)
  ≔ dihedral_base_point_witness S H h .snd t

{` e : 1 ⊔ S → X. `}
def dihedral_three_map (H : Subtypes Int) (h : IntegerSubgroupLaws H) (F : DihedralThreeFacts H) (S : TwoElementSets) (y : Sum (Fin (suc. zero.)) (two_set_carrier S)) : DihedralThreeSet H h F S
  ≔ match y [
  | inl. _ ↦ dihedral_base_point S H h
  | inr. t ↦ dihedral_three_class H h F S t (pos. (suc. zero.)) ]

def dihedral_three_commutes_at (H : Subtypes Int) (h : IntegerSubgroupLaws H) (F : DihedralThreeFacts H) (S : TwoElementSets) (a t : two_set_carrier S) (d : Decidable (Id (two_set_carrier S) t a))
  : Id (DihedralThreeSet H h F S) (dihedral_three_map H h F S (s2c3_branch S a t d))
      (dihedral_three_class H h F S t (dihedral_step (two_set_carrier S) a t d (pos. (suc. zero.))))
  ≔ match d [
  | inl. p ↦ dihedral_class_path S H h (two_set_swap S a, pos. (suc. zero.)) (t, pos. two)
      (inr. (q ↦ two_set_swap_ne S a (concat (two_set_carrier S) (two_set_swap S a) t a q p), (F .fst)))
  | inr. _ ↦ dihedral_three_base_class H h F S t ]

def dihedral_three_commutes (H : Subtypes Int) (h : IntegerSubgroupLaws H) (F : DihedralThreeFacts H) (S : TwoElementSets)
  : SActionCommutes (two_set_carrier S) (Sum (Fin (suc. zero.)) (two_set_carrier S)) (DihedralThreeSet H h F S)
      (s2c3_move S) (a ↦ dihedral_move S H h a) (dihedral_three_map H h F S)
  ≔ a y ↦ match y [
  | inl. _ ↦ concat (DihedralThreeSet H h F S) (dihedral_three_class H h F S a (pos. (suc. zero.)))
      (dihedral_move S H h a (dihedral_three_class H h F S a int_zero))
      (dihedral_move S H h a (dihedral_base_point S H h))
      (inverse (DihedralThreeSet H h F S) (dihedral_move S H h a (dihedral_three_class H h F S a int_zero))
        (dihedral_three_class H h F S a (pos. (suc. zero.)))
        (dihedral_move_self S H h a int_zero))
      (refl (dihedral_move S H h a)
        (inverse (DihedralThreeSet H h F S) (dihedral_base_point S H h) (dihedral_three_class H h F S a int_zero)
          (dihedral_three_base_class H h F S a)))
  | inr. t ↦ dihedral_three_commutes_at H h F S a t (two_set_decidable S t a) ]

{` Injectivity. `}
def dihedral_three_zero_one (H : Subtypes Int) (h : IntegerSubgroupLaws H) (F : DihedralThreeFacts H) (S : TwoElementSets) (t : two_set_carrier S)
  (r : DihedralRel S H (t, int_zero) (t, pos. (suc. zero.))) : Empty
  ≔ match r [ inl. a ↦ F .snd .fst (a .snd) | inr. b ↦ b .fst (refl t) ]

def dihedral_three_one_zero (H : Subtypes Int) (h : IntegerSubgroupLaws H) (F : DihedralThreeFacts H) (S : TwoElementSets) (t : two_set_carrier S)
  (r : DihedralRel S H (t, pos. (suc. zero.)) (t, int_zero)) : Empty
  ≔ match r [ inl. a ↦ F .snd .snd .fst (a .snd) | inr. b ↦ b .fst (refl t) ]

def dihedral_three_one_one (H : Subtypes Int) (h : IntegerSubgroupLaws H) (F : DihedralThreeFacts H) (S : TwoElementSets) (t t' : two_set_carrier S)
  (r : DihedralRel S H (t, pos. (suc. zero.)) (t', pos. (suc. zero.))) : Id (two_set_carrier S) t t'
  ≔ match r [ inl. a ↦ a .fst | inr. b ↦ match F .snd .snd .snd (b .snd) [] ]

def dihedral_three_rel (H : Subtypes Int) (h : IntegerSubgroupLaws H) (F : DihedralThreeFacts H) (S : TwoElementSets) (u v : DihedralPair S)
  (p : Id (DihedralThreeSet H h F S) (dihedral_three_class H h F S (u .fst) (u .snd)) (dihedral_three_class H h F S (v .fst) (v .snd)))
  : DihedralRel S H u v
  ≔ quotient_effective (DihedralPair S) (dihedral_relation S H h) u v .map p

def dihedral_three_fin_one_center (i : Fin (suc. zero.)) : Id (Fin (suc. zero.)) i (inr. star.)
  ≔ match i [ inl. e ↦ match e [] | inr. star. ↦ refl (inr. star. : Fin (suc. zero.)) ]

def dihedral_three_fin_one_path (i j : Fin (suc. zero.)) : Id (Fin (suc. zero.)) i j
  ≔ concat (Fin (suc. zero.)) i (inr. star.) j (dihedral_three_fin_one_center i)
      (inverse (Fin (suc. zero.)) j (inr. star.) (dihedral_three_fin_one_center j))

def dihedral_three_injective (H : Subtypes Int) (h : IntegerSubgroupLaws H) (F : DihedralThreeFacts H) (S : TwoElementSets)
  : PathReflecting (Sum (Fin (suc. zero.)) (two_set_carrier S)) (DihedralThreeSet H h F S) (dihedral_three_map H h F S)
  ≔ y y' ↦ match y, y' [
  | inl. i, inl. j ↦ _ ↦ refl ((k ↦ inl. k) : Fin (suc. zero.) → Sum (Fin (suc. zero.)) (two_set_carrier S))
      (dihedral_three_fin_one_path i j)
  | inl. _, inr. t ↦ p ↦ match dihedral_three_zero_one H h F S t (dihedral_three_rel H h F S (t, int_zero) (t, pos. (suc. zero.))
        (concat (DihedralThreeSet H h F S) (dihedral_three_class H h F S t int_zero)
          (dihedral_base_point S H h) (dihedral_three_class H h F S t (pos. (suc. zero.)))
          (inverse (DihedralThreeSet H h F S) (dihedral_base_point S H h)
            (dihedral_three_class H h F S t int_zero) (dihedral_three_base_class H h F S t)) p)) []
  | inr. t, inl. _ ↦ p ↦ match dihedral_three_one_zero H h F S t (dihedral_three_rel H h F S (t, pos. (suc. zero.)) (t, int_zero)
        (concat (DihedralThreeSet H h F S) (dihedral_three_class H h F S t (pos. (suc. zero.)))
          (dihedral_base_point S H h) (dihedral_three_class H h F S t int_zero)
          p (dihedral_three_base_class H h F S t))) []
  | inr. t, inr. t' ↦ p ↦ refl ((k ↦ inr. k) : two_set_carrier S → Sum (Fin (suc. zero.)) (two_set_carrier S))
      (dihedral_three_one_one H h F S t t' (dihedral_three_rel H h F S (t, pos. (suc. zero.)) (t', pos. (suc. zero.)) p)) ]

{` Surjectivity: preimages of [(t, z)] by recursion on z. `}
def DihedralThreePreimage (H : Subtypes Int) (h : IntegerSubgroupLaws H) (F : DihedralThreeFacts H) (S : TwoElementSets) (x : DihedralThreeSet H h F S) : Type
  ≔ BookFiber (Sum (Fin (suc. zero.)) (two_set_carrier S)) (DihedralThreeSet H h F S) (dihedral_three_map H h F S) x

def dihedral_three_pre_succ (H : Subtypes Int) (h : IntegerSubgroupLaws H) (F : DihedralThreeFacts H) (S : TwoElementSets) (t : two_set_carrier S) (z : Int)
  (w : DihedralThreePreimage H h F S (dihedral_three_class H h F S t z)) : DihedralThreePreimage H h F S (dihedral_three_class H h F S t (int_succ z))
  ≔ (s2c3_move S t (w .fst),
     calc
       dihedral_three_class H h F S t (int_succ z)
         = dihedral_move S H h t (dihedral_three_class H h F S t z)
         by inverse (DihedralThreeSet H h F S) (dihedral_move S H h t (dihedral_three_class H h F S t z))
              (dihedral_three_class H h F S t (int_succ z)) (dihedral_move_self S H h t z)
       = dihedral_move S H h t (dihedral_three_map H h F S (w .fst))
         by refl (dihedral_move S H h t) (w .snd)
       = dihedral_three_map H h F S (s2c3_move S t (w .fst))
         by inverse (DihedralThreeSet H h F S) (dihedral_three_map H h F S (s2c3_move S t (w .fst)))
              (dihedral_move S H h t (dihedral_three_map H h F S (w .fst)))
              (dihedral_three_commutes H h F S t (w .fst)) ∎)

def dihedral_three_int_step (z : Int) : Id Int (int_sub (int_succ (int_succ z)) (int_pred z)) (pos. three)
  ≔ calc
      int_sub (int_succ (int_succ z)) (int_pred z) = int_sub (int_add (pos. two) z) (int_add (neg. zero.) z)
        by concat Int (int_sub (int_succ (int_succ z)) (int_pred z)) (int_sub (int_add (pos. two) z) (int_pred z))
             (int_sub (int_add (pos. two) z) (int_add (neg. zero.) z))
             (refl ((u ↦ int_sub u (int_pred z)) : Int → Int) (int_add_comm z (pos. two)))
             (refl (int_sub (int_add (pos. two) z)) (int_add_comm z (neg. zero.)))
      = pos. three by int_sub_translate (pos. two) (neg. zero.) z ∎

def dihedral_three_pre_pred (H : Subtypes Int) (h : IntegerSubgroupLaws H) (F : DihedralThreeFacts H) (S : TwoElementSets) (t : two_set_carrier S) (z : Int)
  (w : DihedralThreePreimage H h F S (dihedral_three_class H h F S t z)) : DihedralThreePreimage H h F S (dihedral_three_class H h F S t (int_pred z))
  ≔ let w2 : DihedralThreePreimage H h F S (dihedral_three_class H h F S t (int_succ (int_succ z)))
      ≔ dihedral_three_pre_succ H h F S t (int_succ z) (dihedral_three_pre_succ H h F S t z w) in
    (w2 .fst,
     concat (DihedralThreeSet H h F S) (dihedral_three_class H h F S t (int_pred z)) (dihedral_three_class H h F S t (int_succ (int_succ z)))
       (dihedral_three_map H h F S (w2 .fst))
       (dihedral_class_path S H h (t, int_pred z) (t, int_succ (int_succ z))
         (inl. (refl t, refl (SubgroupMember H) (int_neg_sub (int_succ (int_succ z)) (int_pred z)) .trr
           (h .snd .snd (int_sub (int_succ (int_succ z)) (int_pred z))
             (refl (SubgroupMember H) (dihedral_three_int_step z) .trl (F .fst))))))
       (w2 .snd))

def dihedral_three_pre_pos (H : Subtypes Int) (h : IntegerSubgroupLaws H) (F : DihedralThreeFacts H) (S : TwoElementSets) (t : two_set_carrier S) (n : Nat)
  : DihedralThreePreimage H h F S (dihedral_three_class H h F S t (pos. n))
  ≔ match n [
  | zero. ↦ (inl. (inr. star.), inverse (DihedralThreeSet H h F S) (dihedral_base_point S H h)
      (dihedral_three_class H h F S t int_zero) (dihedral_three_base_class H h F S t))
  | suc. n ↦ dihedral_three_pre_succ H h F S t (pos. n) (dihedral_three_pre_pos H h F S t n) ]

def dihedral_three_pre_neg (H : Subtypes Int) (h : IntegerSubgroupLaws H) (F : DihedralThreeFacts H) (S : TwoElementSets) (t : two_set_carrier S) (n : Nat)
  : DihedralThreePreimage H h F S (dihedral_three_class H h F S t (neg. n))
  ≔ match n [
  | zero. ↦ dihedral_three_pre_pred H h F S t int_zero (dihedral_three_pre_pos H h F S t zero.)
  | suc. n ↦ dihedral_three_pre_pred H h F S t (neg. n) (dihedral_three_pre_neg H h F S t n) ]

def dihedral_three_pre (H : Subtypes Int) (h : IntegerSubgroupLaws H) (F : DihedralThreeFacts H) (S : TwoElementSets)
  (t : two_set_carrier S) (z : Int) : DihedralThreePreimage H h F S (dihedral_three_class H h F S t z)
  ≔ match z [
  | pos. n ↦ dihedral_three_pre_pos H h F S t n
  | neg. n ↦ dihedral_three_pre_neg H h F S t n ]

def dihedral_three_surjective (H : Subtypes Int) (h : IntegerSubgroupLaws H) (F : DihedralThreeFacts H) (S : TwoElementSets)
  : Surjective (Sum (Fin (suc. zero.)) (two_set_carrier S)) (DihedralThreeSet H h F S) (dihedral_three_map H h F S)
  ≔ x ↦ quotient_prop_induction (DihedralPair S) (dihedral_relation S H h)
      (x ↦ Mere (DihedralThreePreimage H h F S x)) (x ↦ mere_isprop (DihedralThreePreimage H h F S x))
      (u ↦ mere (DihedralThreePreimage H h F S (dihedral_three_class H h F S (u .fst) (u .snd))) (dihedral_three_pre H h F S (u .fst) (u .snd))) x

def dihedral_three_equiv (H : Subtypes Int) (h : IntegerSubgroupLaws H) (F : DihedralThreeFacts H) (S : TwoElementSets) : Equiv (Sum (Fin (suc. zero.)) (two_set_carrier S)) (DihedralThreeSet H h F S)
  ≔ native_equivalence (Sum (Fin (suc. zero.)) (two_set_carrier S)) (DihedralThreeSet H h F S)
      (native_embedding_surjection_equiv (Sum (Fin (suc. zero.)) (two_set_carrier S)) (DihedralThreeSet H h F S) (dihedral_three_map H h F S)
        (injective_into_set_embedding (Sum (Fin (suc. zero.)) (two_set_carrier S)) (DihedralThreeSet H h F S) (dihedral_three_map H h F S)
          (dihedral_cycle_set_set S H h) (dihedral_three_injective H h F S))
        (dihedral_three_surjective H h F S))

{` Identifications in T_S from S-equivariant equivalences (module 873's
   s_action_paths_equiv, plus the proposition isSet). `}
def dihedral_s2c3_path (S : TwoElementSets) (u v : S2C3Type S)
  (i : SActionIsos (two_set_carrier S) (u .fst .fst, u .snd) (v .fst .fst, v .snd)) : Id (S2C3Type S) u v
  ≔ let q : Id (SActionTypes (two_set_carrier S)) (u .fst .fst, u .snd) (v .fst .fst, v .snd)
      ≔ equiv_inverse_map (Id (SActionTypes (two_set_carrier S)) (u .fst .fst, u .snd) (v .fst .fst, v .snd))
          (SActionIsos (two_set_carrier S) (u .fst .fst, u .snd) (v .fst .fst, v .snd))
          (s_action_paths_equiv (two_set_carrier S) (u .fst .fst, u .snd) (v .fst .fst, v .snd)) i in
    ((q .fst, pathover_of_eq Type isSet (u .fst .fst) (v .fst .fst) (q .fst) (u .fst .snd) (v .fst .snd)
        (isset_isprop (v .fst .fst) (transport Type isSet (u .fst .fst) (v .fst .fst) (q .fst) (u .fst .snd)) (v .fst .snd))),
     q .snd)

{` The identification of (1 ⊔ S, f) (ex:S2-acts-on-C3) with (X, f) for n = 3. `}
def dihedral_three_point_path (H : Subtypes Int) (h : IntegerSubgroupLaws H) (F : DihedralThreeFacts H) (S : TwoElementSets)
  : Id (S2C3Type S) (s2c3_point S) (dihedral_point S H h)
  ≔ dihedral_s2c3_path S (s2c3_point S) (dihedral_point S H h)
      (dihedral_three_equiv H h F S, dihedral_three_commutes H h F S)

{` Hence C̃_3 = G as actions of Σ_2, and D_3 = Σ_2 ⋉ G. `}
def dihedral_three_action_path
  : Id (TwoElementSets → Group) (dihedral_order_action (principal_order three)) s2_acts_on_c3
  ≔ funext TwoElementSets (_ ↦ Group) (dihedral_order_action (principal_order three)) s2_acts_on_c3
      (S ↦ inverse Group (s2c3_group S) (dihedral_order_action (principal_order three) S)
        (automorphism_group_point_path (S2C3Type S) (s2c3_type_groupoid S) (s2c3_point S)
          (dihedral_point S dihedral_three_H dihedral_three_laws) (dihedral_three_point_path dihedral_three_H dihedral_three_laws dihedral_three_facts S)))

def dihedral_three_semidirect_path
  : Id Group (generalized_dihedral_group (principal_order three)) (semidirect_product (symmetric_group two) s2_acts_on_c3)
  ≔ refl (semidirect_product (symmetric_group two)) dihedral_three_action_path
