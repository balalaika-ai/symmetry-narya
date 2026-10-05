import "../../../src/505-gset-core-litmus"
import "02-choice-principles"

{` Blind statements for choicefin.tex: relations between the choice principles
   for families of n-element sets, and the condition L(Z,n). `}

{` thm:lAC-2-3-4: for any set X, X-AC(2) and X-AC(3) imply X-AC(4). `}
def blind_local_ac_two_three_four : Type
  ≔ (X : Type) → isSet X → BlindLocalACn X 2 → BlindLocalACn X 3 → BlindLocalACn X 4

{` Theorem (Tarski): AC(2) implies AC(4). `}
def blind_ac_two_implies_ac_four : Type ≔ BlindACn 2 → BlindACn 4

{` Definition of L(Z,n). Helpers first. Finite sums m_0 + ... + m_{r-1}. `}
def blind_fin_sum (r : Nat) : (Fin r → Nat) → Nat
  ≔ match r [
  | zero. ↦ _ ↦ zero.
  | suc. r ↦ m ↦ add (blind_fin_sum r (i ↦ m (inl. i))) (m (inr. star.)) ]

{` Litmus: 3 + 3 = 6. `}
def blind_fin_sum_litmus : Id Nat (blind_fin_sum 2 (_ ↦ 3)) 6 ≔ refl (6 : Nat)

{` A subgroup of Σ_n (def:set-of-subgroups: a pointed transitive Σ_n-set) and
   its underlying group. `}
def BlindSymSubgroup (n : Nat) (S : Subgroups (symmetric_group n)) : Group
  ≔ subgroup_group (symmetric_group n) S

{` Its action on Fin n: the standard Σ_n-set (A ↦ A) restricted along the
   inclusion of the subgroup. `}
def BlindSymSubgroupAction (n : Nat) (S : Subgroups (symmetric_group n))
  : GSet (BlindSymSubgroup n S)
  ≔ gset_restrict (BlindSymSubgroup n S) (symmetric_group n)
      (subgroup_inclusion (symmetric_group n) S) (standard_symmetric_gset n)

{` Litmus: the underlying set of that action is Fin n. `}
def blind_sym_subgroup_action_underlying (n : Nat) (S : Subgroups (symmetric_group n))
  : Id Type (gset_underlying (BlindSymSubgroup n S) (BlindSymSubgroupAction n S)) (Fin n)
  ≔ refl (Fin n)

{` Fixed elements (lem:fixed-char): x : X(sh_G) with x = g · x for all g. `}
def BlindFixedElements (G : Group) (X : GSet G) : Type
  ≔ Σ (gset_underlying G X) (x ↦ (g : USym G) → Id (gset_underlying G X) x (gset_usym_act G X g x))

def BlindActsWithoutFixedPoints (n : Nat) (S : Subgroups (symmetric_group n)) : Type
  ≔ Not (BlindFixedElements (BlindSymSubgroup n S) (BlindSymSubgroupAction n S))

{` The index |G : K| is m: the G-set of K at sh_G (the cosets G/K) has m
   elements. Proper subgroup: def:triv-proper-Mono (IsProperSubgroup). `}
def BlindIndexIs (G : Group) (K : Subgroups G) (m : Nat) : Type
  ≔ Mere (Id Type (gset_underlying G (K .gset)) (Fin m))

{` Finitely many proper finite subgroups K_1..K_r of G whose indices sum to an
   element of Z. `}
def BlindIndexSumWitness (Z : Subtypes Nat) (G : Group) : Type
  ≔ Σ Nat (r ↦ Σ (Fin r → Subgroups G) (K ↦
      Product
        ((i : Fin r) → Product (IsProperSubgroup G (K i)) (IsFiniteGroup (subgroup_group G (K i))))
        (Σ (Fin r → Nat) (m ↦
          Product ((i : Fin r) → BlindIndexIs G (K i) (m i)) (Z (blind_fin_sum r m) .fst)))))

{` L(Z,n): for every finite subgroup G of Σ_n acting on Fin n without fixed
   points there exist such K_1..K_r. Z is a subset of N (the text takes a
   finite one; finiteness of Z plays no role in the definition). `}
def BlindLCondition (Z : Subtypes Nat) (n : Nat) : Type
  ≔ (S : Subgroups (symmetric_group n)) → IsFiniteGroup (BlindSymSubgroup n S)
    → BlindActsWithoutFixedPoints n S
    → Mere (BlindIndexSumWitness Z (BlindSymSubgroup n S))
