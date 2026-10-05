import "../../../src/1713-tarski-choice"
import "../../../src/1740-condition-l"
import "../../../src/505-gset-core-litmus"
import "01-lpo-topology"
import "02-choice-principles"
import "04-finite-choice"
import "bridge-02-choice-principles"

{` Bridges for choicefin.tex: thm:lAC-2-3-4, Tarski's AC(2) ⇒ AC(4),
   and the condition L(Z,n). `}

def bridge_local_ac_two_three_four : blind_local_ac_two_three_four
  ≔ X hX l2 l3 ↦ bridge_def_local_acn_from_ours X 4
      (local_choice_two_three_four X hX (bridge_def_local_acn_to_ours X 2 l2) (bridge_def_local_acn_to_ours X 3 l3))

def bridge_ac_two_implies_ac_four : blind_ac_two_implies_ac_four
  ≔ a ↦ bridge_def_acn_from_ours 4 (tarski_choice_two_four (bridge_def_acn_to_ours 2 a))

{` L(Z,n): both sides use the book's concrete subgroups of Σ_n (chapter 5's
   Subgroups, subgroup_group, IsFiniteGroup, IsProperSubgroup) and the
   restricted standard action. Differences are only in packaging: the blind
   fixed points are x = g·x (ours g·x = x, GSetFixedPoints), the blind index
   is ‖X(sh_G) = Fin m‖ (ours SubgroupHasIndex, every fibre; equivalent by
   gset_index_iff_shape), and the witness is grouped differently. Both are
   propositions, so the definition bridge is a pair of maps. `}
def bridge_def_fin_sum (r : Nat) (m : Fin r → Nat) : Id Nat (blind_fin_sum r m) (fin_family_sum r m)
  ≔ match r [
  | zero. ↦ refl (zero. : Nat)
  | suc. r ↦ refl ((k ↦ add k (m (inr. star.))) : Nat → Nat)
      (bridge_def_fin_sum r (i ↦ m (inl. i))) ]

def bridge_def_witness_to_ours (Z : Subtypes Nat) (G : Group) (w : BlindIndexSumWitness Z G)
  : ConditionLWitness Z G
  ≔ let r ≔ w .fst in
    let K ≔ w .snd .fst in
    let m ≔ w .snd .snd .snd .fst in
    (r, (j ↦ (K j, (w .snd .snd .fst j .fst, (w .snd .snd .fst j .snd,
          (m j, gset_index_iff_shape G (K j .gset) (m j) .snd (w .snd .snd .snd .snd .fst j))))),
      transport Nat (k ↦ Z k .fst) (blind_fin_sum r m) (fin_family_sum r m) (bridge_def_fin_sum r m)
        (w .snd .snd .snd .snd .snd)))

def bridge_def_witness_from_ours (Z : Subtypes Nat) (G : Group) (w : ConditionLWitness Z G)
  : BlindIndexSumWitness Z G
  ≔ let r ≔ w .fst in
    let K ≔ w .snd .fst in
    let m : Fin r → Nat ≔ j ↦ index_of G (K j) in
    (r, (j ↦ K j .fst, ((j ↦ (K j .snd .fst, K j .snd .snd .fst)),
      (m, ((j ↦ gset_index_iff_shape G (K j .fst .gset) (m j) .fst (K j .snd .snd .snd .snd)),
        transport Nat (k ↦ Z k .fst) (fin_family_sum r m) (blind_fin_sum r m)
          (inverse Nat (blind_fin_sum r m) (fin_family_sum r m) (bridge_def_fin_sum r m)) (w .snd .snd))))))

def bridge_def_l_condition_to_ours (Z : Subtypes Nat) (n : Nat) (b : BlindLCondition Z n) : ConditionL Z n
  ≔ S fin fpf ↦ trunc_map native_truncation (BlindIndexSumWitness Z (BlindSymSubgroup n S))
      (ConditionLWitness Z (BlindSymSubgroup n S)) (bridge_def_witness_to_ours Z (BlindSymSubgroup n S))
      (b S fin (u ↦ fpf (u .fst, g ↦ inverse (Fin n) (u .fst)
        (gset_usym_act (BlindSymSubgroup n S) (BlindSymSubgroupAction n S) g (u .fst)) (u .snd g))))

def bridge_def_l_condition_from_ours (Z : Subtypes Nat) (n : Nat) (c : ConditionL Z n) : BlindLCondition Z n
  ≔ S fin fpf ↦ trunc_map native_truncation (ConditionLWitness Z (BlindSymSubgroup n S))
      (BlindIndexSumWitness Z (BlindSymSubgroup n S)) (bridge_def_witness_from_ours Z (BlindSymSubgroup n S))
      (c S fin (u ↦ fpf (u .fst, g ↦ inverse (Fin n)
        (gset_usym_act (BlindSymSubgroup n S) (BlindSymSubgroupAction n S) g (u .fst)) (u .fst) (u .snd g))))

def bridge_def_l_condition (Z : Subtypes Nat) (n : Nat)
  : Product (BlindLCondition Z n → ConditionL Z n) (ConditionL Z n → BlindLCondition Z n)
  ≔ (bridge_def_l_condition_to_ours Z n, bridge_def_l_condition_from_ours Z n)

{` Litmus agreement: L(∅, 1) on both sides, the blind one also derived from ours. `}
def bridge_l_condition_empty_one : BlindLCondition EmptySubsetOfNat 1
  ≔ S _ fpf ↦ absurd (Mere (BlindIndexSumWitness EmptySubsetOfNat (BlindSymSubgroup 1 S)))
      (fpf (inr. star., g ↦ fin_one_prop (inr. star.)
        (gset_usym_act (BlindSymSubgroup 1 S) (BlindSymSubgroupAction 1 S) g (inr. star.))))

def bridge_l_condition_empty_one_ours : ConditionL EmptySubsetOfNat 1 ≔ condition_l_one

def bridge_l_condition_empty_one_from_ours : BlindLCondition EmptySubsetOfNat 1
  ≔ bridge_def_l_condition_from_ours EmptySubsetOfNat 1 condition_l_one

def bridge_l_condition_not_empty_two (b : BlindLCondition EmptySubsetOfNat 2) : Empty
  ≔ not_condition_l_two (bridge_def_l_condition_to_ours EmptySubsetOfNat 2 b)
