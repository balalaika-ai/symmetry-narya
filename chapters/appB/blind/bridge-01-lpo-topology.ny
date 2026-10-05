import "../../../src/1751-injections-into-contractible"
import "01-lpo-topology"

{` Bridges for metamath.tex (rem:LPO-solves-halting problem,
   rem:injectionsurjectionisnotwhatyouthink). The blind 2 = Fin 2 uses
   0 = inl (inr ★), 1 = inr ★; module 71's Bit is the same type with the
   opposite naming (bit_zero = inr ★, bit_one = inl (inr ★)). The bridge
   goes through the swap of Fin 2, which maps blind 0/1 to bit_zero/bit_one
   definitionally. `}

def bridge_b_swap (b : BlindTwo) : Bit
  ≔ match b [
  | inl. (inl. e) ↦ match e []
  | inl. (inr. _) ↦ inr. star.
  | inr. _ ↦ inl. (inr. star.) ]

def bridge_b_swap_swap (b : BlindTwo) : Id BlindTwo (bridge_b_swap (bridge_b_swap b)) b
  ≔ match b [
  | inl. (inl. e) ↦ match e []
  | inl. (inr. u) ↦ inl. (inr. (unit_prop star. u))
  | inr. u ↦ inr. (unit_prop star. u) ]

def bridge_b_unswap (b c : BlindTwo) (p : Id Bit (bridge_b_swap b) (bridge_b_swap c)) : Id BlindTwo b c
  ≔ concat BlindTwo b (bridge_b_swap (bridge_b_swap b)) c
      (inverse BlindTwo (bridge_b_swap (bridge_b_swap b)) b (bridge_b_swap_swap b))
      (concat BlindTwo (bridge_b_swap (bridge_b_swap b)) (bridge_b_swap (bridge_b_swap c)) c
        (refl bridge_b_swap p) (bridge_b_swap_swap c))

def bridge_b_one_ne_zero (p : Id BlindTwo blind_two_one blind_two_zero) : Empty ≔ bit_zero_ne_one p

def bridge_b_zero_ne_one (p : Id BlindTwo blind_two_zero blind_two_one) : Empty
  ≔ bit_zero_ne_one (inverse BlindTwo blind_two_zero blind_two_one p)

def bridge_b_seq (P : Nat → BlindTwo) : Nat → Bit ≔ n ↦ bridge_b_swap (P n)

{` The two LPO alternatives, blind ↔ module 71 (on the swapped sequence). `}
def bridge_b_const_to_ours (P : Nat → BlindTwo) (z : BlindLPOConstantZero P) : BitConstantZero (bridge_b_seq P)
  ≔ refl ((Q ↦ n ↦ bridge_b_swap (Q n)) : (Nat → BlindTwo) → Nat → Bit) z

def bridge_b_const_from_ours (P : Nat → BlindTwo) (z : BitConstantZero (bridge_b_seq P)) : BlindLPOConstantZero P
  ≔ funext Nat (_ ↦ BlindTwo) P (_ ↦ blind_two_zero) (n ↦ bridge_b_unswap (P n) blind_two_zero (z (refl n)))

def bridge_b_min_to_ours (P : Nat → BlindTwo) (m : BlindLPOSmallestOne P) : BitMinimum (bridge_b_seq P)
  ≔ (m .fst, (refl bridge_b_swap (m .snd .fst),
      k h ↦ le_to_book (m .fst) k (m .snd .snd k (bridge_b_unswap (P k) blind_two_one h))))

def bridge_b_min_from_ours (P : Nat → BlindTwo) (m : BitMinimum (bridge_b_seq P)) : BlindLPOSmallestOne P
  ≔ (m .fst, (bridge_b_unswap (P (m .fst)) blind_two_one (m .snd .fst),
      k h ↦ le_from_book (m .fst) k (m .snd .snd k (refl bridge_b_swap h))))

def bridge_b_instance_to_ours (P : Nat → BlindTwo) (i : BlindLPOInstance P) : LPOInstance (bridge_b_seq P)
  ≔ match i [
  | inl. m ↦ inl. (bridge_b_min_to_ours P m)
  | inr. z ↦ inr. (bridge_b_const_to_ours P z) ]

def bridge_b_instance_from_ours (P : Nat → BlindTwo) (i : LPOInstance (bridge_b_seq P)) : BlindLPOInstance P
  ≔ match i [
  | inl. m ↦ inl. (bridge_b_min_from_ours P m)
  | inr. z ↦ inr. (bridge_b_const_from_ours P z) ]

def bridge_b_seq_swap_swap (Q : Nat → Bit) : Id (Nat → Bit) (bridge_b_seq (bridge_b_seq Q)) Q
  ≔ funext Nat (_ ↦ Bit) (bridge_b_seq (bridge_b_seq Q)) Q (n ↦ bridge_b_swap_swap (Q n))

{` Definition bridge: the blind LPO and module 71's LimitedOmniscience are
   logically equivalent (both are propositions). `}
def bridge_def_lpo_to_ours (L : BlindLPO) : LimitedOmniscience
  ≔ Q ↦ transport (Nat → Bit) LPOInstance (bridge_b_seq (bridge_b_seq Q)) Q (bridge_b_seq_swap_swap Q)
      (bridge_b_instance_to_ours (bridge_b_seq Q) (L (bridge_b_seq Q)))

def bridge_def_lpo_from_ours (L : LimitedOmniscience) : BlindLPO
  ≔ P ↦ bridge_b_instance_from_ours P (L (bridge_b_seq P))

def bridge_def_lpo : BlindIff BlindLPO LimitedOmniscience ≔ (bridge_def_lpo_to_ours, bridge_def_lpo_from_ours)

{` "constant 0 iff never 1", from bit_constant_zero_iff_no_hit. `}
def bridge_lpo_remark_constant_zero_iff_never_one : blind_lpo_remark_constant_zero_iff_never_one
  ≔ P ↦
    let e ≔ bit_constant_zero_iff_no_hit (bridge_b_seq P) in
    (z w ↦ e .map (bridge_b_const_to_ours P z)
        (mere (Σ Nat (BitHit (bridge_b_seq P))) (w .fst, refl bridge_b_swap (w .snd))),
     nh ↦ bridge_b_const_from_ours P
       (equiv_inverse_map (BitConstantZero (bridge_b_seq P)) (Not (Mere (Σ Nat (BitHit (bridge_b_seq P))))) e
         (mh ↦ mere_rec (Σ Nat (BitHit (bridge_b_seq P))) Empty empty_prop
           (w ↦ nh (w .fst, bridge_b_unswap (P (w .fst)) blind_two_one (w .snd))) mh)))

{` The halting decider: case analysis on our LPO instance of the swapped sequence. `}
def bridge_b_decision (P : Nat → BlindTwo) (i : LPOInstance (bridge_b_seq P)) : BlindTwo
  ≔ match i [ inl. _ ↦ blind_two_one | inr. _ ↦ blind_two_zero ]

def bridge_b_decision_spec (P : Nat → BlindTwo) (i : LPOInstance (bridge_b_seq P))
  : Product
      (BlindIff (Id BlindTwo (bridge_b_decision P i) blind_two_one) (Σ Nat (k ↦ Id BlindTwo (P k) blind_two_one)))
      (BlindIff (Id BlindTwo (bridge_b_decision P i) blind_two_zero) (BlindLPOConstantZero P))
  ≔ match i [
  | inl. m ↦
    ((_ ↦ (m .fst, bridge_b_unswap (P (m .fst)) blind_two_one (m .snd .fst)), _ ↦ refl blind_two_one),
     (p ↦ absurd (BlindLPOConstantZero P) (bridge_b_one_ne_zero p),
      z ↦ absurd (Id BlindTwo blind_two_one blind_two_zero)
        (bit_minimum_not_zero (bridge_b_seq P) m (bridge_b_const_to_ours P z))))
  | inr. z ↦
    ((p ↦ absurd (Σ Nat (k ↦ Id BlindTwo (P k) blind_two_one)) (bridge_b_zero_ne_one p),
      w ↦ absurd (Id BlindTwo blind_two_zero blind_two_one)
        (bit_constant_zero_no_hit (bridge_b_seq P) z (w .fst) (refl bridge_b_swap (w .snd)))),
     (_ ↦ bridge_b_const_from_ours P z, _ ↦ refl blind_two_zero)) ]

def bridge_lpo_remark_halting_decider : blind_lpo_remark_halting_decider
  ≔ L T ↦
    let lpo ≔ bridge_def_lpo_to_ours L in
    ((e n ↦ bridge_b_decision (T e n) (lpo (bridge_b_seq (T e n)))),
     e n ↦ bridge_b_decision_spec (T e n) (lpo (bridge_b_seq (T e n))))

def bridge_lpo_remark_cases_exclusive : blind_lpo_remark_cases_exclusive
  ≔ P m z ↦ bit_minimum_not_zero (bridge_b_seq P) (bridge_b_min_to_ours P m) (bridge_b_const_to_ours P z)

def bridge_lpo_remark_lem_implies_lpo : blind_lpo_remark_lem_implies_lpo
  ≔ lem ↦ bridge_def_lpo_from_ours (excluded_middle_implies_lpo lem)

{` rem:injectionsurjectionisnotwhatyouthink. Bool → Fin 2 sends false/true to blind 0/1. `}
def bridge_b_bool_fin (b : Bool) : BlindTwo ≔ match b [ false. ↦ blind_two_zero | true. ↦ blind_two_one ]

def bridge_topology_remark_preimage_contains_both : blind_topology_remark_preimage_contains_both
  ≔ R hR f r ↦
    let w ≔ bool_fiber_two_points R hR (b ↦ f (bridge_b_bool_fin b)) r in
    ((bridge_b_bool_fin (w .fst .fst), w .fst .snd),
     ((bridge_b_bool_fin (w .snd .fst .fst), w .snd .fst .snd),
      (refl bridge_b_bool_fin (w .snd .snd .fst), refl bridge_b_bool_fin (w .snd .snd .snd .fst))))

def bridge_topology_remark_preimage_not_prop : blind_topology_remark_preimage_not_prop
  ≔ R hR f r h ↦
    let w ≔ bridge_topology_remark_preimage_contains_both R hR f r in
    let u ≔ w .fst in
    let v ≔ w .snd .fst in
    bridge_b_zero_ne_one
      (concat BlindTwo blind_two_zero (u .fst) blind_two_one
        (inverse BlindTwo (u .fst) blind_two_zero (w .snd .snd .fst))
        (concat BlindTwo (u .fst) (v .fst) blind_two_one
          (map_path (BookFiber BlindTwo R f r) BlindTwo (t ↦ t .fst) u v (h u v)) (w .snd .snd .snd)))

def bridge_topology_remark_not_injection : blind_topology_remark_not_injection
  ≔ R hR f e ↦ bridge_b_zero_ne_one (injection_into_contractible_prop BlindTwo R f hR e blind_two_zero blind_two_one)

def bridge_topology_remark_injection_into_contractible : blind_topology_remark_injection_into_contractible
  ≔ A R hR f e ↦ injection_into_contractible_prop A R f hR e

def bridge_topology_remark_two_not_connected : blind_topology_remark_two_not_connected
  ≔ c ↦ boolean_not_connected (transport Type Connected (Fin two) Bool fin_two_path c)

{` Converse (bonus): the blind "domain is a proposition" gives back ours. `}
def bridge_topology_converse_injection_iff (A R : Type) (hR : BookIsContr R) (f : A → R)
  : Equiv (IsEmbedding A R f) (isProp A)
  ≔ iff_equiv (IsEmbedding A R f) (isProp A) (book_injection_prop A R f) (isprop_isprop A)
      (bridge_topology_remark_injection_into_contractible A R hR f) (prop_into_contractible_injection A R f hR)
