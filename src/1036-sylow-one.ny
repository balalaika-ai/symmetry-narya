export "1035-sylow-one-step"
export "1005-cauchy-theorem"
export "1034-sylow-three"

{` Chapter 10, thm:sylow1 (fingp.tex 229-260): if p is prime and p^n
   divides |G| (G finite), then G has a subgroup of cardinality p^n. As in
   the book, by induction on n: for n = 0 the trivial subgroup (P_G, refl);
   for n + 1 a subgroup K of order p^n has p | |G/K| = |X(sh_G)|, so by
   lem:fixedptsize p divides |(G/K)^K| = |W_G K| (lem:WGHisHfixofG/H,
   module 1031), Cauchy's theorem (module 1005) gives φ in W_G K of order
   p, and module 1035 builds H ⊇ K with |H| = p · |K|.

   Consequences: p-Sylow subgroups exist (sylow_exists), and with
   thm:sylow2 the G-set Syl_G^p is transitive (sylow_gset_transitive), the
   form "the G-set Syl_G^p is transitive" of thm:sylow2. `}

{` The trivial subgroup (P_G, refl): its action type is contractible. `}
def fingp_trivial_subgroup (G : Group) : Subgroups G
  ≔ (principal_gset G, refl (shape G), principal_gset_transitive G)

def fingp_trivial_subgroup_usym_contractible (G : Group) : BookIsContr (USym (subgroup_group G (fingp_trivial_subgroup G)))
  ≔ is_trivial_group_usym_contractible (subgroup_group G (fingp_trivial_subgroup G))
      (gset_paths_action_type_contractible G (shape G))

def fingp_trivial_subgroup_prop (G : Group) : isProp (USym (subgroup_group G (fingp_trivial_subgroup G)))
  ≔ contractible_prop (USym (subgroup_group G (fingp_trivial_subgroup G)))
      (native_contraction (USym (subgroup_group G (fingp_trivial_subgroup G))) (fingp_trivial_subgroup_usym_contractible G))

def fingp_trivial_subgroup_finite (G : Group) : IsFiniteGroup (subgroup_group G (fingp_trivial_subgroup G))
  ≔ decidable_prop_finite (USym (subgroup_group G (fingp_trivial_subgroup G))) (fingp_trivial_subgroup_prop G)
      (inl. (fingp_trivial_subgroup_usym_contractible G .center))

def fingp_trivial_subgroup_card (G : Group)
  : Id Nat (group_card (subgroup_group G (fingp_trivial_subgroup G)) (fingp_trivial_subgroup_finite G)) (suc. zero.)
  ≔ inhabited_prop_cardinality (USym (subgroup_group G (fingp_trivial_subgroup G))) (fingp_trivial_subgroup_prop G)
      (fingp_trivial_subgroup_finite G) (fingp_trivial_subgroup_usym_contractible G .center)

{` Subgroups of cardinality p^n containing a given K (for the step). `}
def SubgroupOfOrder (G : Group) (m : Nat) : Type
  ≔ Σ (Subgroups G) (H ↦ Σ (IsFiniteGroup (subgroup_group G H)) (hH ↦ Id Nat (group_card (subgroup_group G H) hH) m))

{` The induction step: K of order p^k with p | |G/K| is contained in a
   subgroup H of order p^(k+1). First p | |W_G K|. `}
def sylow_weyl_divisible (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (hG : IsFiniteGroup G) (K : Subgroups G)
  (hK : IsFiniteGroup (subgroup_group G K)) (k : Nat)
  (hc : Id Nat (group_card (subgroup_group G K) hK) (nat_power (suc. b) k))
  (d : NatDivides (suc. b) (gset_card G (K .gset) (subgroup_gset_finite G hG K hK)))
  : NatDivides (suc. b) (group_card (subgroup_weyl_group G K) (subgroup_weyl_finite G hG K hK))
  ≔ let dF : NatDivides (suc. b) (cardinality (SubgroupFixedSet G K (K .gset))
          (subgroup_fixed_set_finite G hG K (subgroup_gset_decidable_equality G hG K hK) (K .gset) (subgroup_gset_finite G hG K hK)))
      ≔ nat_congruent_divides_iff (suc. b) (gset_card G (K .gset) (subgroup_gset_finite G hG K hK))
          (cardinality (SubgroupFixedSet G K (K .gset))
            (subgroup_fixed_set_finite G hG K (subgroup_gset_decidable_equality G hG K hK) (K .gset) (subgroup_gset_finite G hG K hK)))
          (subgroup_fixed_set_congruence (suc. b) hp k G hG K hK hc (subgroup_gset_decidable_equality G hG K hK) (K .gset)
            (subgroup_gset_finite G hG K hK)) .fst d in
    transport Nat (NatDivides (suc. b))
      (cardinality (SubgroupFixedSet G K (K .gset))
        (subgroup_fixed_set_finite G hG K (subgroup_gset_decidable_equality G hG K hK) (K .gset) (subgroup_gset_finite G hG K hK)))
      (group_card (subgroup_weyl_group G K) (subgroup_weyl_finite G hG K hK))
      (inverse Nat (group_card (subgroup_weyl_group G K) (subgroup_weyl_finite G hG K hK))
        (cardinality (SubgroupFixedSet G K (K .gset))
          (subgroup_fixed_set_finite G hG K (subgroup_gset_decidable_equality G hG K hK) (K .gset) (subgroup_gset_finite G hG K hK)))
        (subgroup_weyl_card G hG K hK))
      dF

{` Cauchy's theorem applied to an arbitrary finite group W (kept generic so
   that the concrete Weyl group is never unfolded). `}
def sylow_one_step_generic (b : Nat) (hp : NatIsPrime (suc. b)) (R : Type) (hR : isProp R) (W : Group)
  (hW : IsFiniteGroup W) (dW : NatDivides (suc. b) (group_card W hW))
  (step : (phi : USym W) → Id (USym W) (usym_power W phi (suc. b)) (usym_unit W) → (Id (USym W) phi (usym_unit W) → Empty) → R)
  : R
  ≔ mere_rec (Σ (USym W) (g ↦ Product (Id (USym W) (usym_power W g (suc. b)) (usym_unit W)) (Not (Id (USym W) g (usym_unit W)))))
      R hR (w ↦ step (w .fst) (w .snd .fst) (w .snd .snd))
      (cauchy_nontrivial_element b hp W hW dW)

def sylow_one_step (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (hG : IsFiniteGroup G) (K : Subgroups G)
  (hK : IsFiniteGroup (subgroup_group G K)) (k : Nat)
  (hc : Id Nat (group_card (subgroup_group G K) hK) (nat_power (suc. b) k))
  (d : NatDivides (suc. b) (gset_card G (K .gset) (subgroup_gset_finite G hG K hK)))
  : Mere (WeylStepResult b G K hK)
  ≔ sylow_one_step_generic b hp (Mere (WeylStepResult b G K hK)) (mere_isprop (WeylStepResult b G K hK))
      (subgroup_weyl_group G K) (subgroup_weyl_finite G hG K hK) (sylow_weyl_divisible b hp G hG K hK k hc d)
      (phi h ne ↦ mere (WeylStepResult b G K hK) (weyl_quotient_step b hp G hG K hK phi h ne))

{` thm:sylow1 for p = b + 1. `}
def sylow_one_at (b : Nat) (hp : NatIsPrime (suc. b)) (G : Group) (hG : IsFiniteGroup G) (n : Nat)
  (d : NatDivides (nat_power (suc. b) n) (group_card G hG))
  : Mere (SubgroupOfOrder G (nat_power (suc. b) n))
  ≔ match n [
    | zero. ↦ mere (SubgroupOfOrder G (suc. zero.))
        (fingp_trivial_subgroup G, (fingp_trivial_subgroup_finite G, fingp_trivial_subgroup_card G))
    | suc. n ↦
      let p : Nat ≔ suc. b in
      let dn : NatDivides (nat_power p n) (group_card G hG)
        ≔ nat_divides_trans (nat_power p n) (nat_power p (suc. n)) (group_card G hG)
            (nat_power_mul_divides p n (suc. zero.)) d in
      mere_rec (SubgroupOfOrder G (nat_power p n)) (Mere (SubgroupOfOrder G (nat_power p (suc. n))))
        (mere_isprop (SubgroupOfOrder G (nat_power p (suc. n))))
        (u ↦ let K ≔ u .fst in
          let hK ≔ u .snd .fst in
          let hX ≔ subgroup_gset_finite G hG K hK in
          let x ≔ gset_card G (K .gset) hX in
          let dx : NatDivides p x
            ≔ nat_power_succ_divides_cofactor p n x (prime_positive p hp)
                (transport Nat (NatDivides (nat_power p (suc. n))) (group_card G hG) (mul x (nat_power p n))
                  (concat Nat (group_card G hG) (mul x (group_card (subgroup_group G K) hK)) (mul x (nat_power p n))
                    (lagrange_counting G hG K hK)
                    (map_path Nat Nat (mul x) (group_card (subgroup_group G K) hK) (nat_power p n) (u .snd .snd)))
                  d) in
          mere_rec (WeylStepResult b G K hK)
            (Mere (SubgroupOfOrder G (nat_power p (suc. n)))) (mere_isprop (SubgroupOfOrder G (nat_power p (suc. n))))
            (v ↦ mere (SubgroupOfOrder G (nat_power p (suc. n))) (v .fst, (v .snd .fst,
              concat Nat (group_card (subgroup_group G (v .fst)) (v .snd .fst)) (mul p (group_card (subgroup_group G K) hK))
                (nat_power p (suc. n)) (v .snd .snd .fst)
                (concat Nat (mul p (group_card (subgroup_group G K) hK)) (mul p (nat_power p n)) (nat_power p (suc. n))
                  (map_path Nat Nat (mul p) (group_card (subgroup_group G K) hK) (nat_power p n) (u .snd .snd))
                  (mul_comm p (nat_power p n))))))
            (sylow_one_step b hp G hG K hK n (u .snd .snd) dx))
        (sylow_one_at b hp G hG n dn) ]

def fingp_prime_pred (p : Nat) (hp : NatIsPrime p) : Σ Nat (b ↦ Id Nat p (suc. b))
  ≔ match p [
    | zero. ↦ absurd (Σ Nat (b ↦ Id Nat zero. (suc. b))) (prime_gt_one zero. hp)
    | suc. b ↦ (b, refl (suc. b : Nat)) ]

def SylowOneStatement (G : Group) (hG : IsFiniteGroup G) (n p : Nat) : Type
  ≔ NatIsPrime p → NatDivides (nat_power p n) (group_card G hG) → Mere (SubgroupOfOrder G (nat_power p n))

{` thm:sylow1: p prime, p^n divides |G| ⇒ G has a subgroup of cardinality p^n. `}
def sylow_one (p : Nat) (hp : NatIsPrime p) (G : Group) (hG : IsFiniteGroup G) (n : Nat)
  (d : NatDivides (nat_power p n) (group_card G hG)) : Mere (SubgroupOfOrder G (nat_power p n))
  ≔ let w ≔ fingp_prime_pred p hp in
    transport Nat (SylowOneStatement G hG n) (suc. (w .fst)) p (inverse Nat p (suc. (w .fst)) (w .snd))
      (hp' d' ↦ sylow_one_at (w .fst) hp' G hG n d') hp d

{` p-Sylow subgroups exist. `}
def sylow_exists (p : Nat) (hp : NatIsPrime p) (G : Group) (hG : IsFiniteGroup G) : Mere (SylowSubgroups p G)
  ≔ let l ≔ largest_prime_power_exists p (group_card G hG) (prime_gt_one p hp) (finite_group_card_positive G hG) in
    mere_rec (SubgroupOfOrder G (nat_power p (l .fst))) (Mere (SylowSubgroups p G)) (mere_isprop (SylowSubgroups p G))
      (u ↦ mere (SylowSubgroups p G) (u .fst, (hG, (u .snd .fst, (l .fst, (u .snd .snd, l .snd))))))
      (sylow_one p hp G hG (l .fst) (l .snd .fst))

{` thm:sylow2, "the G-set Syl_G^p is transitive". `}
def sylow_gset_transitive (p : Nat) (hp : NatIsPrime p) (G : Group) (hG : IsFiniteGroup G)
  : IsTransitive G (sylow_gset p G)
  ≔ let Y ≔ SylowSubgroups p G in
    let T ≔ Σ Y (x ↦ (y : Y) → Mere (Σ (USym G) (g ↦ Id Y x (gset_usym_act G (sylow_gset p G) g y)))) in
    mere_rec Y (Mere T) (mere_isprop T)
      (P ↦ mere T (P, Q ↦
        let R ≔ Σ (USym G) (g ↦ Id Y P (gset_usym_act G (sylow_gset p G) g Q)) in
        mere_rec (Σ (USym G) (g ↦ Id (Subgroups G) (subgroup_conjugate G g (Q .fst)) (P .fst))) (Mere R) (mere_isprop R)
          (w ↦ mere R (w .fst, sylow_subgroups_path p G P (gset_usym_act G (sylow_gset p G) (w .fst) Q)
            (inverse (Subgroups G) (sylow_point p G (gset_usym_act G (sylow_gset p G) (w .fst) Q)) (P .fst)
              (concat (Subgroups G) (sylow_point p G (gset_usym_act G (sylow_gset p G) (w .fst) Q))
                (subgroup_conjugate G (w .fst) (Q .fst)) (P .fst)
                (sylow_gset_act p G (w .fst) Q) (w .snd)))))
          (sylow_subgroups_conjugate p hp G (Q .fst) (P .fst) (Q .snd) (P .snd))))
      (sylow_exists p hp G hG)

{` Litmus: Σ_3 has a subgroup of order 3 = 3^1 and one of order 2 = 2^1,
   and a 3-Sylow subgroup. `}
def sylow_one_sigma3_three : Mere (SubgroupOfOrder (symmetric_group three) (nat_power (suc. (suc. (suc. zero.))) (suc. zero.)))
  ≔ sylow_one (suc. (suc. (suc. zero.))) nat_prime_three (symmetric_group three) (symmetric_group_finite three) (suc. zero.)
      (transport Nat (NatDivides (suc. (suc. (suc. zero.)))) (factorial three)
        (group_card (symmetric_group three) (symmetric_group_finite three))
        (inverse Nat (group_card (symmetric_group three) (symmetric_group_finite three)) (factorial three)
          (symmetric_group_card three))
        (nat_divides_intro (suc. (suc. (suc. zero.))) (factorial three) (suc. (suc. zero.)) (refl (factorial three))))

def sylow_exists_sigma3_three : Mere (SylowSubgroups (suc. (suc. (suc. zero.))) (symmetric_group three))
  ≔ sylow_exists (suc. (suc. (suc. zero.))) nat_prime_three (symmetric_group three) (symmetric_group_finite three)
