export "533-fermat-fixed-sets"
export "1002-prime-numbers-euclid"
import "582-pointed-finite-sets"

{` Chapter 5, Fermat's Little Theorem (the unlabeled theorem after
   lem:burnside): for every prime p and natural number n, p | n^p − n,
   via Burnside's lemma for the C_p-set X(S, t) = (S → Fin n):
   n^p + n(p−1) = Card(Σ_g X^g) = Card(X/C_p) × p. The subtraction is the
   truncated one (n ≤ n^p, fermat_power_ge). `}

{` Splitting a point off a type with decidable equality, as a sum over it:
   Σ_{x : A} P(x) ≃ Σ_{w : A ∖ {a}} P(w) + Σ_{_ : 1} P(a). `}
def fermat_point_split_merge (A : Type) (dA : DecidableEquality A) (a : A) (u : Sum (Without A a) Unit)
  : Id (Sum (Without A a) Unit) (point_split_dec A a (point_merge A a u) (dA (point_merge A a u) a)) u
  ≔ match u [
  | inl. c ↦ point_split_without A a c (dA (c .fst) a)
  | inr. s ↦ match s [ star. ↦ point_split_self A a (dA a a) ] ]

def fermat_point_merge_equiv (A : Type) (dA : DecidableEquality A) (a : A) : Equiv (Sum (Without A a) Unit) A
  ≔ quasi_inverse_equiv (Sum (Without A a) Unit) A (point_merge A a) (x ↦ point_split_dec A a x (dA x a))
      (fermat_point_split_merge A dA a) (x ↦ point_merge_split A a x (dA x a))

def fermat_sigma_sum_to (B C : Type) (Q : Sum B C → Type) (s : Sum B C) (q : Q s)
  : Sum (Σ B (b ↦ Q (inl. b))) (Σ C (c ↦ Q (inr. c)))
  ≔ match s [ inl. b ↦ inl. (b, q) | inr. c ↦ inr. (c, q) ]

def fermat_sigma_sum_from (B C : Type) (Q : Sum B C → Type)
  (u : Sum (Σ B (b ↦ Q (inl. b))) (Σ C (c ↦ Q (inr. c)))) : Σ (Sum B C) Q
  ≔ match u [ inl. v ↦ (inl. (v .fst), v .snd) | inr. v ↦ (inr. (v .fst), v .snd) ]

def fermat_sigma_sum_eta (B C : Type) (Q : Sum B C → Type) (s : Sum B C) (q : Q s)
  : Id (Σ (Sum B C) Q) (fermat_sigma_sum_from B C Q (fermat_sigma_sum_to B C Q s q)) (s, q)
  ≔ match s [ inl. b ↦ refl ((inl. b, q) : Σ (Sum B C) Q) | inr. c ↦ refl ((inr. c, q) : Σ (Sum B C) Q) ]

def fermat_sigma_sum_epsilon (B C : Type) (Q : Sum B C → Type) (u : Sum (Σ B (b ↦ Q (inl. b))) (Σ C (c ↦ Q (inr. c))))
  : Id (Sum (Σ B (b ↦ Q (inl. b))) (Σ C (c ↦ Q (inr. c))))
      (fermat_sigma_sum_to B C Q (fermat_sigma_sum_from B C Q u .fst) (fermat_sigma_sum_from B C Q u .snd)) u
  ≔ match u [
  | inl. v ↦ refl (inl. v : Sum (Σ B (b ↦ Q (inl. b))) (Σ C (c ↦ Q (inr. c))))
  | inr. v ↦ refl (inr. v : Sum (Σ B (b ↦ Q (inl. b))) (Σ C (c ↦ Q (inr. c)))) ]

def fermat_sigma_sum_base_equiv (B C : Type) (Q : Sum B C → Type)
  : Equiv (Σ (Sum B C) Q) (Sum (Σ B (b ↦ Q (inl. b))) (Σ C (c ↦ Q (inr. c))))
  ≔ quasi_inverse_equiv (Σ (Sum B C) Q) (Sum (Σ B (b ↦ Q (inl. b))) (Σ C (c ↦ Q (inr. c))))
      (t ↦ fermat_sigma_sum_to B C Q (t .fst) (t .snd)) (fermat_sigma_sum_from B C Q)
      (t ↦ fermat_sigma_sum_eta B C Q (t .fst) (t .snd)) (fermat_sigma_sum_epsilon B C Q)

def fermat_point_sigma_split (A : Type) (dA : DecidableEquality A) (a : A) (P : A → Type)
  : Equiv (Σ A P) (Sum (Σ (Without A a) (w ↦ P (w .fst))) (Σ Unit (_ ↦ P a)))
  ≔ let S ≔ Sum (Without A a) Unit in
    let e ≔ fermat_point_merge_equiv A dA a in
    compose_equiv (Σ A P) (Σ S (s ↦ P (e .map s))) (Sum (Σ (Without A a) (w ↦ P (w .fst))) (Σ Unit (_ ↦ P a)))
      (canonical_inverse_equiv (Σ S (s ↦ P (e .map s))) (Σ A P) (sigma_pullback_equiv S A e P))
      (fermat_sigma_sum_base_equiv (Without A a) Unit (s ↦ P (e .map s)))

def fermat_unit_sigma_eta (B : Type) (u : Unit) (b : B) : Id (Σ Unit (_ ↦ B)) (star., b) (u, b)
  ≔ match u [ star. ↦ refl ((star., b) : Σ Unit (_ ↦ B)) ]

def fermat_unit_sigma_equiv (B : Type) : Equiv (Σ Unit (_ ↦ B)) B
  ≔ quasi_inverse_equiv (Σ Unit (_ ↦ B)) B (t ↦ t .snd) (b ↦ (star., b))
      (t ↦ fermat_unit_sigma_eta B (t .fst) (t .snd)) (b ↦ refl b)

{` The p − 1 symmetries g ≠ refl of C_p. `}
def fermat_nonidentity_equiv (m : Nat)
  : Equiv (Without (USym (fermat_group m)) (usym_unit (fermat_group m))) (Fin m)
  ≔ let A ≔ USym (fermat_group m) in
    let E ≔ cyclic_group_fin_usym_equiv m in
    compose_equiv (Without A (usym_unit (fermat_group m))) (Without (Fin (suc. m)) (E .map (usym_unit (fermat_group m))))
      (Fin m) (without_equiv A (Fin (suc. m)) E (usym_unit (fermat_group m)))
      (without_fin_equiv m (E .map (usym_unit (fermat_group m))))

{` n^p + n(p−1) = Card(Σ_{g : USym C_p} X^g), p = m+1 prime. `}
def fermat_fixed_points_count (m n : Nat) (hp : NatIsPrime (suc. m))
  : Id Nat (cardinality (BurnsideSum (fermat_group m) (fermat_gset m n))
        (burnside_sum_finite (fermat_group m) (fermat_group_finite m) (fermat_gset m n) (fermat_gset_finite m n)))
      (add (nat_power n (suc. m)) (mul n m))
  ≔ let G ≔ fermat_group m in
    let X ≔ fermat_gset m n in
    let hG ≔ fermat_group_finite m in
    let hX ≔ fermat_gset_finite m n in
    let Xs ≔ Fin (suc. m) → Fin n in
    let A ≔ USym G in
    let e ≔ usym_unit G in
    let P ≔ (g ↦ FixedBy G X g) : A → Type in
    let W ≔ Without A e in
    let B1 ≔ Σ W (w ↦ P (w .fst)) in
    let B2 ≔ Σ Unit (_ ↦ P e) in
    let hS ≔ burnside_sum_finite G hG X hX in
    let hW : IsFinite W ≔ finite_from_equiv W m (fermat_nonidentity_equiv m) in
    let hn ≔ fin_is_finite n in
    let eW ≔ (w ↦ fermat_fixed_by_nonidentity_equiv m n hp (w .fst) (w .snd)) : (w : W) → Equiv (P (w .fst)) (Fin n) in
    let h1 : IsFinite B1
      ≔ finite_of_equiv B1 (Product W (Fin n)) (family_equiv W (w ↦ P (w .fst)) (_ ↦ Fin n) eW)
          (finite_product W (Fin n) hW hn) in
    let e2 : Equiv B2 Xs ≔ compose_equiv B2 (P e) Xs (fermat_unit_sigma_equiv (P e)) (fixed_by_unit_equiv G X) in
    let h2 : IsFinite B2 ≔ finite_of_equiv B2 Xs e2 hX in
    let hSum ≔ finite_sum B1 B2 h1 h2 in
    let c1 : Id Nat (cardinality B1 h1) (mul m n)
      ≔ concat Nat (cardinality B1 h1) (mul (cardinality W hW) (cardinality (Fin n) hn)) (mul m n)
          (cardinality_equinumerous_sum W (Fin n) (w ↦ P (w .fst)) hW hn eW h1)
          (concat Nat (mul (cardinality W hW) (cardinality (Fin n) hn)) (mul m (cardinality (Fin n) hn)) (mul m n)
            (refl ((j ↦ mul j (cardinality (Fin n) hn)) : Nat → Nat)
              (cardinality_from_path W hW m (ua W (Fin m) (fermat_nonidentity_equiv m))))
            (refl (mul m) (cardinality_from_path (Fin n) hn n (refl (Fin n))))) in
    let c2 : Id Nat (cardinality B2 h2) (nat_power n (suc. m))
      ≔ concat Nat (cardinality B2 h2) (cardinality Xs hX) (nat_power n (suc. m))
          (cardinality_equiv B2 Xs e2 h2 hX) (fermat_gset_card m n) in
    calc
      cardinality (BurnsideSum G X) hS
      = cardinality (Sum B1 B2) hSum
        by cardinality_equiv (BurnsideSum G X) (Sum B1 B2) (fermat_point_sigma_split A (finite_decidable_equality A hG) e P) hS hSum
      = add (cardinality B1 h1) (cardinality B2 h2) by cardinality_sum B1 B2 h1 h2 hSum
      = add (mul m n) (cardinality B2 h2) by refl ((j ↦ add j (cardinality B2 h2)) : Nat → Nat) c1
      = add (mul m n) (nat_power n (suc. m)) by refl (add (mul m n)) c2
      = add (nat_power n (suc. m)) (mul m n) by add_comm (mul m n) (nat_power n (suc. m))
      = add (nat_power n (suc. m)) (mul n m) by refl (add (nat_power n (suc. m))) (mul_comm m n) ∎

{` The displayed equation of the proof: n^p + n(p−1) = Card(X/C_p) × p. `}
def fermat_burnside_equation (m n : Nat) (hp : NatIsPrime (suc. m))
  : Id Nat (add (nat_power n (suc. m)) (mul n m))
      (mul (cardinality (Orbits (fermat_group m) (fermat_gset m n))
          (burnside_orbits_finite (fermat_group m) (fermat_group_finite m) (fermat_gset m n) (fermat_gset_finite m n)))
        (suc. m))
  ≔ let G ≔ fermat_group m in
    let X ≔ fermat_gset m n in
    let hG ≔ fermat_group_finite m in
    let hX ≔ fermat_gset_finite m n in
    let c ≔ cardinality (Orbits G X) (burnside_orbits_finite G hG X hX) in
    let hS ≔ burnside_sum_finite G hG X hX in
    calc
      add (nat_power n (suc. m)) (mul n m)
      = cardinality (BurnsideSum G X) hS
        by inverse Nat (cardinality (BurnsideSum G X) hS) (add (nat_power n (suc. m)) (mul n m))
          (fermat_fixed_points_count m n hp)
      = mul c (group_card G hG) by burnside_lemma G hG X hX
      = mul c (suc. m) by refl (mul c) (fermat_group_card m) ∎

def fermat_little_theorem_succ (m n : Nat) (hp : NatIsPrime (suc. m))
  : NatDivides (suc. m) (nat_truncated_sub (nat_power n (suc. m)) n)
  ≔ let c ≔ cardinality (Orbits (fermat_group m) (fermat_gset m n))
              (burnside_orbits_finite (fermat_group m) (fermat_group_finite m) (fermat_gset m n) (fermat_gset_finite m n)) in
    fermat_divides_from_count m n c
      (concat Nat (add (nat_power n (suc. m)) (mul m n)) (add (nat_power n (suc. m)) (mul n m)) (mul c (suc. m))
        (refl (add (nat_power n (suc. m))) (mul_comm m n))
        (fermat_burnside_equation m n hp))

{` Fermat's Little Theorem: p | n^p − n for every prime p and natural n. `}
def fermat_little_theorem (p n : Nat) (hp : NatIsPrime p) : NatDivides p (nat_truncated_sub (nat_power n p) n)
  ≔ match p [
  | zero. ↦ match hp .fst []
  | suc. m ↦ fermat_little_theorem_succ m n hp ]

{` Litmus: 3 | 2^3 − 2 = 6, where 2^3 ∸ 2 computes to 6. `}
def fermat_litmus_six
  : Id Nat (nat_truncated_sub (nat_power (suc. (suc. zero.)) (suc. (suc. (suc. zero.)))) (suc. (suc. zero.)))
      (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))
  ≔ refl (suc. (suc. (suc. (suc. (suc. (suc. zero.))))) : Nat)

def fermat_litmus_three_two
  : NatDivides (suc. (suc. (suc. zero.)))
      (nat_truncated_sub (nat_power (suc. (suc. zero.)) (suc. (suc. (suc. zero.)))) (suc. (suc. zero.)))
  ≔ fermat_little_theorem (suc. (suc. (suc. zero.))) (suc. (suc. zero.)) nat_prime_three
