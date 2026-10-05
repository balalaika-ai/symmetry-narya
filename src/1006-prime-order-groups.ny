export "1005-cauchy-theorem"
export "1027-cyclic-groups-simple"

{` Chapter 10, running text at fingp.tex 23: "if |G| is a prime number,
   then G has no nontrivial proper subgroups! (actually, G is necessarily
   a cyclic group)". For |G| = p prime: by Cauchy (thm:cauchys) G has a
   subgroup S with underlying group C_p; |S| = p = |G|, so S is the full
   subgroup (lem:Lagrangeascounting, lagrange_counting_equal_order), hence
   G = C_p (merely: the identification depends on the chosen generator).
   Transporting cor:cyclicgroupsaresimple (module 1027) along it gives the
   first claim for every subgroup of G. `}

def fingp_full_subgroup_group_path (G : Group) : Id Group (subgroup_group G (group_full_subgroup G)) G
  ≔ mono_subgroup_group_path G (G, (group_hom_id G, group_hom_id_mono G))

def prime_order_group_cyclic (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (hG : IsFiniteGroup G)
  (hc : Id Nat (group_card G hG) (suc. b)) : Mere (Id Group G (cyclic_group (suc. b)))
  ≔ let C ≔ cyclic_group (suc. b) in
    let hd : NatDivides (suc. b) (group_card G hG)
      ≔ transport Nat (NatDivides (suc. b)) (suc. b) (group_card G hG) (inverse Nat (group_card G hG) (suc. b) hc)
          (nat_divides_refl (suc. b)) in
    mere_rec (Σ (Subgroups G) (S ↦ Id Group (subgroup_group G S) C)) (Mere (Id Group G C)) (mere_isprop (Id Group G C))
      (w ↦
        let S ≔ w .fst in
        let hS ≔ group_finite_path C (subgroup_group G S) (inverse Group (subgroup_group G S) C (w .snd)) (cyclic_group_finite b) in
        let cS : Id Nat (group_card (subgroup_group G S) hS) (group_card G hG)
          ≔ concat Nat (group_card (subgroup_group G S) hS) (suc. b) (group_card G hG)
              (concat Nat (group_card (subgroup_group G S) hS) (group_card C (cyclic_group_finite b)) (suc. b)
                (group_card_path (subgroup_group G S) C (w .snd) hS (cyclic_group_finite b))
                (cyclic_group_card b (cyclic_group_finite b)))
              (inverse Nat (group_card G hG) (suc. b) hc) in
        let full : Id (Subgroups G) S (group_full_subgroup G) ≔ lagrange_counting_equal_order G hG S hS cS in
        mere (Id Group G C)
          (concat Group G (subgroup_group G (group_full_subgroup G)) C
            (inverse Group (subgroup_group G (group_full_subgroup G)) G (fingp_full_subgroup_group_path G))
            (concat Group (subgroup_group G (group_full_subgroup G)) (subgroup_group G S) C
              (refl ((T ↦ subgroup_group G T) : Subgroups G → Group)
                (inverse (Subgroups G) S (group_full_subgroup G) full))
              (w .snd))))
      (cauchy_theorem b hp G hG hd)

def prime_order_group_no_nontrivial_proper (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (hG : IsFiniteGroup G)
  (hc : Id Nat (group_card G hG) (suc. b)) (S : Subgroups G)
  : Not (Product (Not (IsTrivialSubgroup G S)) (IsProperSubgroup G S))
  ≔ let P : Group → Type
      ≔ H ↦ (T : Subgroups H) → Not (Product (Not (IsTrivialSubgroup H T)) (IsProperSubgroup H T)) in
    mere_rec (Id Group G (cyclic_group (suc. b))) (Not (Product (Not (IsTrivialSubgroup G S)) (IsProperSubgroup G S)))
      (negation_prop (Product (Not (IsTrivialSubgroup G S)) (IsProperSubgroup G S)))
      (e ↦ transport Group P (cyclic_group (suc. b)) G (inverse Group G (cyclic_group (suc. b)) e)
        (cyclic_prime_no_nontrivial_proper b hp) S)
      (prime_order_group_cyclic b hp G hG hc)

{` Litmus: Σ_2 (of order 2) is C_2, merely. `}
def sigma2_is_cyclic_two : Mere (Id Group (symmetric_group two) (cyclic_group two))
  ≔ prime_order_group_cyclic (suc. zero.) nat_prime_two (symmetric_group two) sigma2_finite sigma2_card
