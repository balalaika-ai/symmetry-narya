export "1001-divisibility-lemmas"

{` Chapter 5, Fermat's Little Theorem: the arithmetic used in the proof.
   Primes (NatIsPrime), powers b^e (nat_power, b^(e+1) = b^e · b) and
   divisibility d | k (NatDivides, ∃ q, k = q·d) are those of modules
   1000/147/1001 (chapter-10 arithmetic vocabulary). Truncated subtraction
   a ∸ b is added here (the repository has none); for b ≤ a it is the
   ordinary difference. `}

{` Truncated subtraction a ∸ b. `}
def nat_truncated_sub (a b : Nat) : Nat
  ≔ match b [
  | zero. ↦ a
  | suc. b ↦ match a [ zero. ↦ zero. | suc. a ↦ nat_truncated_sub a b ] ]

{` (d + b) ∸ b = d. `}
def nat_truncated_sub_add (d b : Nat) : Id Nat (nat_truncated_sub (add d b) b) d
  ≔ match b [ zero. ↦ refl d | suc. b ↦ nat_truncated_sub_add d b ]

def nat_truncated_sub_litmus : Id Nat (nat_truncated_sub (suc. (suc. (suc. zero.))) (suc. zero.)) (suc. (suc. zero.))
  ≔ refl (suc. (suc. zero.) : Nat)

{` n ≤ n^(m+1). `}
def fermat_power_ge (n m : Nat) : Le n (nat_power n (suc. m))
  ≔ match n [
  | zero. ↦ star.
  | suc. k ↦
    le_trans (suc. k) (mul (suc. zero.) (suc. k)) (mul (nat_power (suc. k) m) (suc. k))
      (transport Nat (j ↦ Le (suc. k) j) (suc. k) (mul (suc. zero.) (suc. k))
        (inverse Nat (mul (suc. zero.) (suc. k)) (suc. k) (mul_one_left (suc. k))) (le_refl (suc. k)))
      (le_mul_right (suc. zero.) (nat_power (suc. k) m) (suc. k) (nat_power_positive (suc. k) m star.)) ]

{` (Sum A Unit → B) ≃ (A → B) × B. `}
def fermat_sum_unit_function_equiv (A B : Type) : Equiv (Sum A Unit → B) (Product (A → B) B)
  ≔ compose_equiv (Sum A Unit → B) (Product (A → B) (Unit → B)) (Product (A → B) B)
      (sum_universal_property A Unit B)
      (product_equiv (A → B) (Unit → B) (A → B) B (identity_equiv (A → B))
        (quasi_inverse_equiv (Unit → B) B (h ↦ h star.) (b _ ↦ b)
          (h ↦ funext Unit (_ ↦ B) (_ ↦ h star.) h (u ↦ match u [ star. ↦ refl (h star.) ]))
          (b ↦ refl b)))

{` Functions out of the empty type. `}
def fermat_empty_function_equiv (B : Type) : Equiv (Empty → B) (Fin (suc. zero.))
  ≔ quasi_inverse_equiv (Empty → B) (Fin (suc. zero.)) (_ ↦ inr. star.) (_ e ↦ absurd B e)
      (h ↦ funext Empty (_ ↦ B) (e ↦ absurd B e) h (e ↦ match e []))
      [ inl. e ↦ match e [] | inr. u ↦ match u [ star. ↦ refl (inr. star. : Fin (suc. zero.)) ] ]

{` Fin k → Fin n ≃ Fin (n^k): the set of base-n sequences of length k has n^k elements. `}
def fin_function_equiv (k n : Nat) : Equiv (Fin k → Fin n) (Fin (nat_power n k))
  ≔ match k [
  | zero. ↦ fermat_empty_function_equiv (Fin n)
  | suc. k ↦
    compose_equiv (Fin (suc. k) → Fin n) (Product (Fin k → Fin n) (Fin n)) (Fin (nat_power n (suc. k)))
      (fermat_sum_unit_function_equiv (Fin k) (Fin n))
      (compose_equiv (Product (Fin k → Fin n) (Fin n)) (Product (Fin (nat_power n k)) (Fin n))
        (Fin (mul (nat_power n k) n))
        (product_equiv (Fin k → Fin n) (Fin n) (Fin (nat_power n k)) (Fin n) (fin_function_equiv k n)
          (identity_equiv (Fin n)))
        (fin_product_equiv (nat_power n k) n)) ]

def fin_function_finite (k n : Nat) : IsFinite (Fin k → Fin n)
  ≔ finite_from_equiv (Fin k → Fin n) (nat_power n k) (fin_function_equiv k n)

def fin_function_cardinality (k n : Nat) (h : IsFinite (Fin k → Fin n))
  : Id Nat (cardinality (Fin k → Fin n) h) (nat_power n k)
  ≔ cardinality_from_path (Fin k → Fin n) h (nat_power n k)
      (ua (Fin k → Fin n) (Fin (nat_power n k)) (fin_function_equiv k n))

{` A finite type with cardinality one is a proposition. `}
def fermat_cardinality_one_prop (A : Type) (h : IsFinite A) (q : Id Nat (cardinality A h) (suc. zero.)) : isProp A
  ≔ mere_rec (Id Type A (Fin (cardinality A h))) (isProp A) (isprop_isprop A)
      (r ↦ transport Type isProp (Fin (suc. zero.)) A
        (inverse Type A (Fin (suc. zero.))
          (concat Type A (Fin (cardinality A h)) (Fin (suc. zero.)) r (refl Fin q)))
        (u v ↦ match u [
          | inl. e ↦ match e []
          | inr. s ↦ match v [
            | inl. e ↦ match e []
            | inr. t ↦ match s [ star. ↦ match t [ star. ↦ refl (inr. star. : Fin (suc. zero.)) ] ] ] ]))
      (cardinality_spec A h)

{` If m+1 = (m+1)·b then b = 1. `}
def fermat_mul_cancel_one (m b : Nat) (e : Id Nat (suc. m) (mul (suc. m) b)) : Id Nat b (suc. zero.)
  ≔ match b [
  | zero. ↦ match nat_encode (suc. m) zero. e []
  | suc. zero. ↦ refl (suc. zero. : Nat)
  | suc. (suc. c) ↦
    let y ≔ add (mul (suc. m) c) m in
    match nat_encode zero. (suc. y)
      (add_cancel_right (suc. m) zero. (suc. y)
        (concat Nat (add zero. (suc. m)) (suc. m) (add (suc. y) (suc. m)) (add_zero_left (suc. m))
          (concat Nat (suc. m) (mul (suc. m) (suc. (suc. c))) (add (suc. y) (suc. m)) e
            (refl (add (suc. y) (suc. m))))))
    [] ]

{` The final arithmetic step of the proof: from n^p + n(p−1) = c·p and
   n ≤ n^p (p = m+1) it follows that p | n^p ∸ n. Stated with m·n for n(p−1)
   (commutativity is applied by the caller). `}
def fermat_divides_from_count (m n c : Nat)
  (e : Id Nat (add (nat_power n (suc. m)) (mul m n)) (mul c (suc. m)))
  : NatDivides (suc. m) (nat_truncated_sub (nat_power n (suc. m)) n)
  ≔ let p : Nat ≔ suc. m in
    let P ≔ nat_power n p in
    let bl ≔ le_to_book n P (fermat_power_ge n m) in
    let d ≔ bl .fst in
    let hd : Id Nat (add d n) P ≔ bl .snd in
    let sub_d : Id Nat (nat_truncated_sub P n) d
      ≔ transport Nat (j ↦ Id Nat (nat_truncated_sub j n) d) (add d n) P hd (nat_truncated_sub_add d n) in
    {` d + p·n = c·p `}
    let sum_eq : Id Nat (add d (mul p n)) (mul c p)
      ≔ calc
          add d (mul p n)
          = add d (add (mul m n) n) by refl (add d) (mul_suc_left m n)
          = add d (add n (mul m n)) by refl (add d) (add_comm (mul m n) n)
          = add (add d n) (mul m n) by inverse Nat (add (add d n) (mul m n)) (add d (add n (mul m n))) (add_assoc d n (mul m n))
          = add P (mul m n) by refl ((j ↦ add j (mul m n)) : Nat → Nat) hd
          = mul c p by e ∎ in
    let div_sum : NatDivides p (add d (mul p n))
      ≔ transport Nat (NatDivides p) (mul c p) (add d (mul p n)) (inverse Nat (add d (mul p n)) (mul c p) sum_eq)
          (nat_divides_intro p (mul c p) c (refl (mul c p))) in
    let div_pn : NatDivides p (mul p n) ≔ nat_divides_intro p (mul p n) n (mul_comm p n) in
    transport Nat (NatDivides p) d (nat_truncated_sub P n) (inverse Nat (nat_truncated_sub P n) d sub_d)
      (nat_divides_add_cancel_right p d (mul p n) div_sum div_pn)

{` Litmus: Fin 3 → Fin 2 has 2^3 = 8 elements. `}
def fin_function_litmus_eight
  : Id Nat (cardinality (Fin (suc. (suc. (suc. zero.))) → Fin (suc. (suc. zero.)))
        (fin_function_finite (suc. (suc. (suc. zero.))) (suc. (suc. zero.))))
      (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))
  ≔ fin_function_cardinality (suc. (suc. (suc. zero.))) (suc. (suc. zero.))
      (fin_function_finite (suc. (suc. (suc. zero.))) (suc. (suc. zero.)))
