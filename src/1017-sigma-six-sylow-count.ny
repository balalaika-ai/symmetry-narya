export "1016-sigma-six-claims"

{` Chapter 10, the example at fingp.tex 27–33, last sentence, as far as the
   Sylow theorems go: a 3-Sylow subgroup P of Σ_6 has order 3^2 = 9
   (module 1016: 3^2 is the largest power of 3 dividing 6!), and by
   thm:sylow3 the number of 3-Sylow subgroups (= subgroups of order 9)
   divides |Σ_6|/|P| = 80 and is ≡ 1 (mod 3) (sigma6_sylow_count_at, for
   any given 3-Sylow subgroup and any finiteness proof of Syl_3(Σ_6)). That
   such a P exists is thm:sylow1 (sylow_exists, module 1036); 1036 is not
   imported here because 1016 + 1036 together need more than 20 GB of memory
   when compiled from source in this workspace. The book's value 10 is not
   derived (Sylow III alone allows 1, 4, 10, 16, 40). 80 is written as the
   term 2·(5·8) and 6! = (2·(5·8))·9 is proved symbolically (unary numerals
   of this size cannot be normalized, see module 1016). `}

def fingp_eighty_term : Nat ≔ mul two (mul (suc. (suc. (suc. (suc. (suc. zero.))))) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))))

def sigma6_factorial_four : Id Nat (factorial (suc. three)) (mul (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))) three)
  ≔ refl (factorial (suc. three))

{` One unfolding step of factorial (cheap; normalizing 5! is not). `}
def sigma6_factorial_five_unfold
  : Id Nat (factorial (suc. (suc. (suc. (suc. (suc. zero.)))))) (mul (suc. (suc. (suc. (suc. (suc. zero.))))) (factorial (suc. three)))
  ≔ refl (factorial (suc. (suc. (suc. (suc. (suc. zero.))))))

def fingp_three_three_nine : Id Nat (mul three three) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))) ≔ refl (mul three three)

{` 6! = (2·(5·8))·9. `}
def sigma6_factorial_eighty : Id Nat (factorial sigma6_n) (mul fingp_eighty_term (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))))
  ≔ let five : Nat ≔ suc. (suc. (suc. (suc. (suc. zero.)))) in
    let eight : Nat ≔ suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))) in
    calc
      factorial sigma6_n = mul (mul two (factorial (suc. (suc. (suc. (suc. (suc. zero.))))))) three by sigma6_factorial_split
      = mul (mul two (mul five (mul eight three))) three
        by refl ((x ↦ mul (mul two x) three) : Nat → Nat)
          (concat Nat (factorial (suc. (suc. (suc. (suc. (suc. zero.)))))) (mul five (factorial (suc. three))) (mul five (mul eight three))
            sigma6_factorial_five_unfold (refl (mul five) sigma6_factorial_four))
      = mul (mul two (mul (mul five eight) three)) three
        by refl ((x ↦ mul (mul two x) three) : Nat → Nat)
          (inverse Nat (mul (mul five eight) three) (mul five (mul eight three)) (mul_assoc five eight three))
      = mul (mul (mul two (mul five eight)) three) three
        by refl ((x ↦ mul x three) : Nat → Nat)
          (inverse Nat (mul (mul two (mul five eight)) three) (mul two (mul (mul five eight) three))
            (mul_assoc two (mul five eight) three))
      = mul fingp_eighty_term (mul three three) by mul_assoc (mul two (mul five eight)) three three
      = mul fingp_eighty_term (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))))
        by refl (mul fingp_eighty_term) fingp_three_three_nine ∎

def sigma6_sylow_count_at (Q : SylowSubgroups three (symmetric_group sigma6_n))
  (h : IsFinite (SylowSubgroups three (symmetric_group sigma6_n)))
  : Product (NatDivides (cardinality (SylowSubgroups three (symmetric_group sigma6_n)) h) fingp_eighty_term)
      (NatCongruent three (cardinality (SylowSubgroups three (symmetric_group sigma6_n)) h) (suc. zero.))
  ≔ let G ≔ symmetric_group sigma6_n in
    let P ≔ Q .fst in let sP ≔ Q .snd in
    let hG' ≔ sylow_group_finite three G P sP in
    let hP ≔ sylow_subgroup_finite three G P sP in
    let hl2 : IsLargestPrimePower three two (group_card G hG')
      ≔ transport Nat (IsLargestPrimePower three two) (factorial sigma6_n) (group_card G hG')
          (inverse Nat (group_card G hG') (factorial sigma6_n)
            (concat Nat (group_card G hG') (group_card G (symmetric_group_finite sigma6_n)) (factorial sigma6_n)
              (fingp_group_card_irrel G hG' (symmetric_group_finite sigma6_n)) (symmetric_group_card sigma6_n)))
          sigma6_largest_three in
    let e2 : Id Nat (sylow_exponent three G P sP) two
      ≔ largest_prime_power_unique three (group_card G hG') (sylow_exponent three G P sP) two (sP .snd .snd .snd .snd) hl2 in
    let hk : Id Nat (group_card (subgroup_group G P) hP) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))))
      ≔ concat Nat (group_card (subgroup_group G P) hP) (nat_power three (sylow_exponent three G P sP)) (nat_power three two)
          (sylow_subgroup_card three G P sP) (refl (nat_power three) e2) in
    let hn : Id Nat (group_card G (symmetric_group_finite sigma6_n))
          (mul fingp_eighty_term (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))))
      ≔ concat Nat (group_card G (symmetric_group_finite sigma6_n)) (factorial sigma6_n)
          (mul fingp_eighty_term (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))))
          (symmetric_group_card sigma6_n) sigma6_factorial_eighty in
    let h0 ≔ sylow_subgroups_finite three nat_prime_three G P sP in
    let ce : Id Nat (cardinality (SylowSubgroups three G) h0) (cardinality (SylowSubgroups three G) h)
      ≔ fingp_card_irrel (SylowSubgroups three G) h0 h in
    (transport Nat (k ↦ NatDivides k fingp_eighty_term) (cardinality (SylowSubgroups three G) h0)
       (cardinality (SylowSubgroups three G) h) ce
       (sylow_count_divides three nat_prime_three G P sP (symmetric_group_finite sigma6_n) hP fingp_eighty_term
         (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))) hn hk),
     transport Nat (k ↦ NatCongruent three k (suc. zero.)) (cardinality (SylowSubgroups three G) h0)
       (cardinality (SylowSubgroups three G) h) ce
       (sylow_three_congruence three nat_prime_three G P sP))
