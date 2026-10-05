export "1002-prime-numbers-euclid"

{` Chapter 10 (fingp.tex), supporting arithmetic for the counting arguments:
   the cardinality of Σ_{a:A} P(a) is the arithmetic sum of the fiber
   cardinalities (the footnote of lem:Lagrangeascounting); divisibility of
   such sums; congruences mod p (NatCongruent of module 1000); the sum of
   numbers each equal to 1 or divisible by p is congruent mod p to the number
   of 1s (core of lem:fixedptsize); the largest power of p dividing m
   (def:sylowsubgroup); and the first example of the chapter (fingp.tex:16):
   positive divisors of 8 adding up to 13 include a 1. `}

{` Footnote of lem:Lagrangeascounting: |Σ_{a:A} P(a)| = Σ_{a:A} |P(a)|. `}
def cardinality_sigma_arithmetic_sum (A : Type) (ha : IsFinite A) (P : A → Type) (hp : (a : A) → IsFinite (P a))
  (hs : IsFinite (Σ A P))
  : Id Nat (cardinality (Σ A P) hs) (arithmetic_sum A ha (a ↦ cardinality (P a) (hp a)))
  ≔ let F : A → Type ≔ a ↦ Fin (cardinality (P a) (hp a)) in
    mere_rec ((a : A) → Id Type (P a) (F a))
      (Id Nat (cardinality (Σ A P) hs) (arithmetic_sum A ha (a ↦ cardinality (P a) (hp a))))
      (nat_set (cardinality (Σ A P) hs) (arithmetic_sum A ha (a ↦ cardinality (P a) (hp a))))
      (q ↦ cardinality_equiv (Σ A P) (Σ A F) (family_equiv A P F (a ↦ id_to_equiv (P a) (F a) (q a))) hs
        (finite_sigma A ha F (a ↦ fin_is_finite (cardinality (P a) (hp a)))))
      (finite_choice A ha (a ↦ Id Type (P a) (F a)) (a ↦ cardinality_spec (P a) (hp a)))

def arithmetic_sum_pointwise (A : Type) (ha : IsFinite A) (f g : A → Nat) (h : (a : A) → Id Nat (f a) (g a))
  : Id Nat (arithmetic_sum A ha f) (arithmetic_sum A ha g)
  ≔ refl (arithmetic_sum A ha) (funext A (_ ↦ Nat) f g h)

{` Footnote of lem:Lagrangeascounting, last clause: constant fiber size m gives |A|·m. `}
def cardinality_sigma_constant (A : Type) (ha : IsFinite A) (P : A → Type) (hp : (a : A) → IsFinite (P a))
  (hs : IsFinite (Σ A P)) (m : Nat) (h : (a : A) → Id Nat (cardinality (P a) (hp a)) m)
  : Id Nat (cardinality (Σ A P) hs) (mul (cardinality A ha) m)
  ≔ calc
      cardinality (Σ A P) hs = arithmetic_sum A ha (a ↦ cardinality (P a) (hp a))
        by cardinality_sigma_arithmetic_sum A ha P hp hs
      = arithmetic_sum A ha (_ ↦ m) by arithmetic_sum_pointwise A ha (a ↦ cardinality (P a) (hp a)) (_ ↦ m) h
      = mul (cardinality A ha) m by arithmetic_sum_constant A ha m ∎

{` Divisibility of finite sums. `}
def fin_arithmetic_sum_divisible (d n : Nat) (f : Fin n → Nat) (h : (i : Fin n) → NatDivides d (f i))
  : NatDivides d (arithmetic_sum (Fin n) (fin_is_finite n) f)
  ≔ match n [
  | zero. ↦ transport Nat (NatDivides d) zero. (arithmetic_sum (Fin zero.) (fin_is_finite zero.) f)
      (inverse Nat (arithmetic_sum (Fin zero.) (fin_is_finite zero.) f) zero. (arithmetic_sum_empty f))
      (nat_divides_zero d)
  | suc. n ↦ transport Nat (NatDivides d)
      (add (arithmetic_sum (Fin n) (fin_is_finite n) (i ↦ f (inl. i))) (f (inr. star.)))
      (arithmetic_sum (Fin (suc. n)) (fin_is_finite (suc. n)) f)
      (inverse Nat (arithmetic_sum (Fin (suc. n)) (fin_is_finite (suc. n)) f)
        (add (arithmetic_sum (Fin n) (fin_is_finite n) (i ↦ f (inl. i))) (f (inr. star.))) (arithmetic_sum_step n f))
      (nat_divides_add d (arithmetic_sum (Fin n) (fin_is_finite n) (i ↦ f (inl. i))) (f (inr. star.))
        (fin_arithmetic_sum_divisible d n (i ↦ f (inl. i)) (i ↦ h (inl. i))) (h (inr. star.))) ]

def arithmetic_sum_divisible (A : Type) (ha : IsFinite A) (f : A → Nat) (d : Nat) (h : (a : A) → NatDivides d (f a))
  : NatDivides d (arithmetic_sum A ha f)
  ≔ mere_rec (Id Type A (Fin (cardinality A ha))) (NatDivides d (arithmetic_sum A ha f))
      (nat_divides_prop d (arithmetic_sum A ha f))
      (q ↦ let e : Equiv (Fin (cardinality A ha)) A
          ≔ id_to_equiv (Fin (cardinality A ha)) A (inverse Type A (Fin (cardinality A ha)) q) in
        transport Nat (NatDivides d)
          (arithmetic_sum (Fin (cardinality A ha)) (fin_is_finite (cardinality A ha)) (i ↦ f (e .map i)))
          (arithmetic_sum A ha f)
          (arithmetic_sum_reindex (Fin (cardinality A ha)) A (fin_is_finite (cardinality A ha)) ha e f)
          (fin_arithmetic_sum_divisible d (cardinality A ha) (i ↦ f (e .map i)) (i ↦ h (e .map i))))
      (cardinality_spec A ha)

def cardinality_sigma_divisible (A : Type) (ha : IsFinite A) (P : A → Type) (hp : (a : A) → IsFinite (P a))
  (hs : IsFinite (Σ A P)) (d : Nat) (h : (a : A) → NatDivides d (cardinality (P a) (hp a)))
  : NatDivides d (cardinality (Σ A P) hs)
  ≔ transport Nat (NatDivides d) (arithmetic_sum A ha (a ↦ cardinality (P a) (hp a))) (cardinality (Σ A P) hs)
      (inverse Nat (cardinality (Σ A P) hs) (arithmetic_sum A ha (a ↦ cardinality (P a) (hp a)))
        (cardinality_sigma_arithmetic_sum A ha P hp hs))
      (arithmetic_sum_divisible A ha (a ↦ cardinality (P a) (hp a)) d h)

{` Congruences mod p. `}
def nat_congruent_intro (p a b k : Nat) (e : Id Nat a (add b (mul k p))) : NatCongruent p a b
  ≔ mere (Σ Nat (j ↦ Sum (Id Nat a (add b (mul j p))) (Id Nat b (add a (mul j p))))) (k, inl. e)

def nat_congruent_refl (p a : Nat) : NatCongruent p a a
  ≔ nat_congruent_intro p a a zero. (inverse Nat (add a (mul zero. p)) a (refl (add a) (mul_zero_left p)))

def nat_congruent_sym (p a b : Nat) (h : NatCongruent p a b) : NatCongruent p b a
  ≔ mere_rec (Σ Nat (j ↦ Sum (Id Nat a (add b (mul j p))) (Id Nat b (add a (mul j p)))))
      (NatCongruent p b a) (nat_congruent_prop p b a)
      (u ↦ mere (Σ Nat (j ↦ Sum (Id Nat b (add a (mul j p))) (Id Nat a (add b (mul j p)))))
        (u .fst, sum_swap (Id Nat a (add b (mul (u .fst) p))) (Id Nat b (add a (mul (u .fst) p))) (u .snd)))
      h

def nat_congruent_divides_at (p a b k : Nat) (s : Sum (Id Nat a (add b (mul k p))) (Id Nat b (add a (mul k p))))
  (hb : NatDivides p b) : NatDivides p a
  ≔ let dk : NatDivides p (mul k p) ≔ nat_divides_mul_left p k p (nat_divides_refl p) in
    match s [
    | inl. e ↦ transport Nat (NatDivides p) (add b (mul k p)) a (inverse Nat a (add b (mul k p)) e)
        (nat_divides_add p b (mul k p) hb dk)
    | inr. e ↦ nat_divides_add_cancel_right p a (mul k p) (transport Nat (NatDivides p) b (add a (mul k p)) e hb) dk ]

{` If a ≡ b (mod p) then p | b implies p | a. `}
def nat_congruent_divides (p a b : Nat) (h : NatCongruent p a b) (hb : NatDivides p b) : NatDivides p a
  ≔ mere_rec (Σ Nat (j ↦ Sum (Id Nat a (add b (mul j p))) (Id Nat b (add a (mul j p)))))
      (NatDivides p a) (nat_divides_prop p a) (u ↦ nat_congruent_divides_at p a b (u .fst) (u .snd) hb) h

def nat_congruent_divides_iff (p a b : Nat) (h : NatCongruent p a b)
  : Product (NatDivides p a → NatDivides p b) (NatDivides p b → NatDivides p a)
  ≔ (nat_congruent_divides p b a (nat_congruent_sym p a b h), nat_congruent_divides p a b h)

{` a ≡ 1 (mod p) with p > 1 implies that p does not divide a. `}
def nat_congruent_one_not_divides (p a : Nat) (hp : Lt (suc. zero.) p) (h : NatCongruent p a (suc. zero.))
  (d : NatDivides p a) : Empty
  ≔ lt_not_equal (suc. zero.) p hp
      (inverse Nat p (suc. zero.) (nat_divides_one p (nat_congruent_divides p (suc. zero.) a (nat_congruent_sym p a (suc. zero.) h) d)))

{` A sum of numbers each 1 or divisible by p is congruent mod p to the
   number of 1s. The indicator of "m = 1": `}
def nat_one_indicator (m : Nat) : Nat
  ≔ match m [ zero. ↦ zero. | suc. m ↦ match m [ zero. ↦ suc. zero. | suc. _ ↦ zero. ] ]

def nat_one_indicator_ne (m : Nat) : (Id Nat m (suc. zero.) → Empty) → Id Nat (nat_one_indicator m) zero.
  ≔ match m [
  | zero. ↦ _ ↦ refl (zero. : Nat)
  | suc. m ↦ match m [
    | zero. ↦ ne ↦ absurd (Id Nat (suc. zero.) zero.) (ne (refl (suc. zero. : Nat)))
    | suc. _ ↦ _ ↦ refl (zero. : Nat) ] ]

def finite_empty_cardinality (P : Type) (h : IsFinite P) (n : P → Empty) : Id Nat (cardinality P h) zero.
  ≔ cardinality_from_path P h zero.
      (ua P (Fin zero.) (quasi_inverse_equiv P Empty n (e ↦ match e []) (x ↦ match n x []) (e ↦ match e [])))

def nat_one_indicator_card (m : Nat) : (h : IsFinite (Id Nat m (suc. zero.)))
  → Id Nat (cardinality (Id Nat m (suc. zero.)) h) (nat_one_indicator m)
  ≔ match m [
  | zero. ↦ h ↦ finite_empty_cardinality (Id Nat zero. (suc. zero.)) h (e ↦ nat_encode zero. (suc. zero.) e)
  | suc. m ↦ match m [
    | zero. ↦ h ↦ inhabited_prop_cardinality (Id Nat (suc. zero.) (suc. zero.)) (nat_set (suc. zero.) (suc. zero.)) h
        (refl (suc. zero. : Nat))
    | suc. m ↦ h ↦ finite_empty_cardinality (Id Nat (suc. (suc. m)) (suc. zero.)) h
        (e ↦ nat_encode (suc. m) zero. (refl nat_pred e)) ] ]

def ones_count_finite (A : Type) (ha : IsFinite A) (f : A → Nat) : IsFinite (Σ A (a ↦ Id Nat (f a) (suc. zero.)))
  ≔ finite_decidable_subset A ha (a ↦ Id Nat (f a) (suc. zero.)) (a ↦ nat_set (f a) (suc. zero.))
      (a ↦ nat_dec_eq (f a) (suc. zero.))

def ones_count_indicator_sum (A : Type) (ha : IsFinite A) (f : A → Nat)
  (hc : IsFinite (Σ A (a ↦ Id Nat (f a) (suc. zero.))))
  : Id Nat (cardinality (Σ A (a ↦ Id Nat (f a) (suc. zero.))) hc) (arithmetic_sum A ha (a ↦ nat_one_indicator (f a)))
  ≔ let hp : (a : A) → IsFinite (Id Nat (f a) (suc. zero.))
      ≔ a ↦ decidable_prop_finite (Id Nat (f a) (suc. zero.)) (nat_set (f a) (suc. zero.)) (nat_dec_eq (f a) (suc. zero.)) in
    concat Nat (cardinality (Σ A (a ↦ Id Nat (f a) (suc. zero.))) hc)
      (arithmetic_sum A ha (a ↦ cardinality (Id Nat (f a) (suc. zero.)) (hp a)))
      (arithmetic_sum A ha (a ↦ nat_one_indicator (f a)))
      (cardinality_sigma_arithmetic_sum A ha (a ↦ Id Nat (f a) (suc. zero.)) hp hc)
      (arithmetic_sum_pointwise A ha (a ↦ cardinality (Id Nat (f a) (suc. zero.)) (hp a)) (a ↦ nat_one_indicator (f a))
        (a ↦ nat_one_indicator_card (f a) (hp a)))

def fin_sum_ones_split (p n : Nat) (f : Fin n → Nat)
  (h : (i : Fin n) → Sum (Id Nat (f i) (suc. zero.)) (NatDivides p (f i)))
  : Mere (Σ Nat (k ↦ Id Nat (arithmetic_sum (Fin n) (fin_is_finite n) f)
      (add (arithmetic_sum (Fin n) (fin_is_finite n) (i ↦ nat_one_indicator (f i))) (mul k p))))
  ≔ match n [
  | zero. ↦
      let S0f : Nat ≔ arithmetic_sum (Fin zero.) (fin_is_finite zero.) f in
      let S0g : Nat ≔ arithmetic_sum (Fin zero.) (fin_is_finite zero.) (i ↦ nat_one_indicator (f i)) in
      mere (Σ Nat (k ↦ Id Nat S0f (add S0g (mul k p))))
        (zero., concat Nat S0f zero. (add S0g (mul zero. p)) (arithmetic_sum_empty f)
          (inverse Nat (add S0g (mul zero. p)) zero.
            (refl add (arithmetic_sum_empty (i ↦ nat_one_indicator (f i))) (mul_zero_left p))))
  | suc. n ↦
      let g : Fin (suc. n) → Nat ≔ i ↦ nat_one_indicator (f i) in
      let Sf : Nat ≔ arithmetic_sum (Fin (suc. n)) (fin_is_finite (suc. n)) f in
      let Sg : Nat ≔ arithmetic_sum (Fin (suc. n)) (fin_is_finite (suc. n)) g in
      let Tf : Nat ≔ arithmetic_sum (Fin n) (fin_is_finite n) (i ↦ f (inl. i)) in
      let Tg : Nat ≔ arithmetic_sum (Fin n) (fin_is_finite n) (i ↦ g (inl. i)) in
      let last : Nat ≔ f (inr. star.) in
      let T : Type ≔ Σ Nat (k ↦ Id Nat Sf (add Sg (mul k p))) in
      mere_rec (Σ Nat (k ↦ Id Nat Tf (add Tg (mul k p)))) (Mere T) (mere_isprop T)
        (u ↦ let k : Nat ≔ u .fst in
          match nat_dec_eq last (suc. zero.) [
          | inl. e ↦ mere T (k, calc
              Sf = add Tf last by arithmetic_sum_step n f
              = add (add Tg (mul k p)) (suc. zero.) by refl add (u .snd) e
              = add (add Tg (suc. zero.)) (mul k p) by add_swap_tail Tg (mul k p) (suc. zero.)
              = add (add Tg (nat_one_indicator last)) (mul k p)
                by refl ((z ↦ add (add Tg z) (mul k p)) : Nat → Nat)
                  (inverse Nat (nat_one_indicator last) (suc. zero.) (refl nat_one_indicator e))
              = add Sg (mul k p)
                by refl ((z ↦ add z (mul k p)) : Nat → Nat)
                  (inverse Nat Sg (add Tg (nat_one_indicator last)) (arithmetic_sum_step n g)) ∎)
          | inr. ne ↦ match h (inr. star.) [
            | inl. e ↦ absurd (Mere T) (ne e)
            | inr. dv ↦ mere_rec (Σ Nat (q ↦ Id Nat last (mul q p))) (Mere T) (mere_isprop T)
                (v ↦ let kq : Nat ≔ add k (v .fst) in
                  mere T (kq, calc
                    Sf = add Tf last by arithmetic_sum_step n f
                    = add (add Tg (mul k p)) (mul (v .fst) p) by refl add (u .snd) (v .snd)
                    = add Tg (add (mul k p) (mul (v .fst) p)) by add_assoc Tg (mul k p) (mul (v .fst) p)
                    = add Tg (mul kq p)
                      by refl (add Tg) (inverse Nat (mul kq p) (add (mul k p) (mul (v .fst) p)) (mul_add_right k (v .fst) p))
                    = add (add Tg (nat_one_indicator last)) (mul kq p)
                      by refl ((z ↦ add (add Tg z) (mul kq p)) : Nat → Nat)
                        (inverse Nat (nat_one_indicator last) zero. (nat_one_indicator_ne last ne))
                    = add Sg (mul kq p)
                      by refl ((z ↦ add z (mul kq p)) : Nat → Nat)
                        (inverse Nat Sg (add Tg (nat_one_indicator last)) (arithmetic_sum_step n g)) ∎))
                dv ] ])
        (fin_sum_ones_split p n (i ↦ f (inl. i)) (i ↦ h (inl. i))) ]

def arithmetic_sum_ones_split (A : Type) (ha : IsFinite A) (f : A → Nat) (p : Nat)
  (h : (a : A) → Sum (Id Nat (f a) (suc. zero.)) (NatDivides p (f a)))
  : Mere (Σ Nat (k ↦ Id Nat (arithmetic_sum A ha f) (add (arithmetic_sum A ha (a ↦ nat_one_indicator (f a))) (mul k p))))
  ≔ let T : Type ≔ Σ Nat (k ↦ Id Nat (arithmetic_sum A ha f) (add (arithmetic_sum A ha (a ↦ nat_one_indicator (f a))) (mul k p))) in
    mere_rec (Id Type A (Fin (cardinality A ha))) (Mere T) (mere_isprop T)
      (q ↦ let e : Equiv (Fin (cardinality A ha)) A
          ≔ id_to_equiv (Fin (cardinality A ha)) A (inverse Type A (Fin (cardinality A ha)) q) in
        let Sf : Nat ≔ arithmetic_sum (Fin (cardinality A ha)) (fin_is_finite (cardinality A ha)) (i ↦ f (e .map i)) in
        let Sg : Nat
          ≔ arithmetic_sum (Fin (cardinality A ha)) (fin_is_finite (cardinality A ha)) (i ↦ nat_one_indicator (f (e .map i))) in
        mere_rec (Σ Nat (k ↦ Id Nat Sf (add Sg (mul k p)))) (Mere T) (mere_isprop T)
          (u ↦ mere T (u .fst, calc
            arithmetic_sum A ha f = Sf
              by inverse Nat Sf (arithmetic_sum A ha f)
                (arithmetic_sum_reindex (Fin (cardinality A ha)) A (fin_is_finite (cardinality A ha)) ha e f)
            = add Sg (mul (u .fst) p) by u .snd
            = add (arithmetic_sum A ha (a ↦ nat_one_indicator (f a))) (mul (u .fst) p)
              by refl ((z ↦ add z (mul (u .fst) p)) : Nat → Nat)
                (arithmetic_sum_reindex (Fin (cardinality A ha)) A (fin_is_finite (cardinality A ha)) ha e
                  (a ↦ nat_one_indicator (f a))) ∎))
          (fin_sum_ones_split p (cardinality A ha) (i ↦ f (e .map i)) (i ↦ h (e .map i))))
      (cardinality_spec A ha)

{` If each f(a) is 1 or divisible by p, then Σ_a f(a) = #{a | f(a) = 1} + k·p. `}
def arithmetic_sum_ones_congruent (A : Type) (ha : IsFinite A) (f : A → Nat) (p : Nat)
  (h : (a : A) → Sum (Id Nat (f a) (suc. zero.)) (NatDivides p (f a)))
  (hc : IsFinite (Σ A (a ↦ Id Nat (f a) (suc. zero.))))
  : Mere (Σ Nat (k ↦ Id Nat (arithmetic_sum A ha f) (add (cardinality (Σ A (a ↦ Id Nat (f a) (suc. zero.))) hc) (mul k p))))
  ≔ let C : Nat ≔ cardinality (Σ A (a ↦ Id Nat (f a) (suc. zero.))) hc in
    let I : Nat ≔ arithmetic_sum A ha (a ↦ nat_one_indicator (f a)) in
    let T : Type ≔ Σ Nat (k ↦ Id Nat (arithmetic_sum A ha f) (add C (mul k p))) in
    mere_rec (Σ Nat (k ↦ Id Nat (arithmetic_sum A ha f) (add I (mul k p)))) (Mere T) (mere_isprop T)
      (u ↦ mere T (u .fst, concat Nat (arithmetic_sum A ha f) (add I (mul (u .fst) p)) (add C (mul (u .fst) p)) (u .snd)
        (refl ((z ↦ add z (mul (u .fst) p)) : Nat → Nat) (inverse Nat C I (ones_count_indicator_sum A ha f hc)))))
      (arithmetic_sum_ones_split A ha f p h)

def arithmetic_sum_ones_mod (A : Type) (ha : IsFinite A) (f : A → Nat) (p : Nat)
  (h : (a : A) → Sum (Id Nat (f a) (suc. zero.)) (NatDivides p (f a)))
  (hc : IsFinite (Σ A (a ↦ Id Nat (f a) (suc. zero.))))
  : NatCongruent p (arithmetic_sum A ha f) (cardinality (Σ A (a ↦ Id Nat (f a) (suc. zero.))) hc)
  ≔ let C : Nat ≔ cardinality (Σ A (a ↦ Id Nat (f a) (suc. zero.))) hc in
    mere_rec (Σ Nat (k ↦ Id Nat (arithmetic_sum A ha f) (add C (mul k p))))
      (NatCongruent p (arithmetic_sum A ha f) C) (nat_congruent_prop p (arithmetic_sum A ha f) C)
      (u ↦ nat_congruent_intro p (arithmetic_sum A ha f) C (u .fst) (u .snd))
      (arithmetic_sum_ones_congruent A ha f p h hc)

{` The same for Σ_{a:A} P(a): if every |P(a)| is 1 or divisible by p, then
   |Σ_a P(a)| ≡ #{a | |P(a)| = 1} (mod p) (the counting step of lem:fixedptsize). `}
def cardinality_sigma_ones_mod (A : Type) (ha : IsFinite A) (P : A → Type) (hp : (a : A) → IsFinite (P a))
  (hs : IsFinite (Σ A P)) (p : Nat)
  (h : (a : A) → Sum (Id Nat (cardinality (P a) (hp a)) (suc. zero.)) (NatDivides p (cardinality (P a) (hp a))))
  (hc : IsFinite (Σ A (a ↦ Id Nat (cardinality (P a) (hp a)) (suc. zero.))))
  : NatCongruent p (cardinality (Σ A P) hs) (cardinality (Σ A (a ↦ Id Nat (cardinality (P a) (hp a)) (suc. zero.))) hc)
  ≔ transport Nat
      (x ↦ NatCongruent p x (cardinality (Σ A (a ↦ Id Nat (cardinality (P a) (hp a)) (suc. zero.))) hc))
      (arithmetic_sum A ha (a ↦ cardinality (P a) (hp a))) (cardinality (Σ A P) hs)
      (inverse Nat (cardinality (Σ A P) hs) (arithmetic_sum A ha (a ↦ cardinality (P a) (hp a)))
        (cardinality_sigma_arithmetic_sum A ha P hp hs))
      (arithmetic_sum_ones_mod A ha (a ↦ cardinality (P a) (hp a)) p h hc)

{` Largest prime powers (def:sylowsubgroup): p^n | m but not p^(n+1) | m. `}
def IsLargestPrimePower (p n m : Nat) : Type
  ≔ Product (NatDivides (nat_power p n) m) (NatDivides (nat_power p (suc. n)) m → Empty)

def is_largest_prime_power_prop (p n m : Nat) : isProp (IsLargestPrimePower p n m)
  ≔ product_prop (NatDivides (nat_power p n) m) (NatDivides (nat_power p (suc. n)) m → Empty)
      (nat_divides_prop (nat_power p n) m) (negation_prop (NatDivides (nat_power p (suc. n)) m))

def largest_prime_power_unique (p m n n' : Nat) (h : IsLargestPrimePower p n m) (h' : IsLargestPrimePower p n' m)
  : Id Nat n n'
  ≔ match nat_dec_eq n n' [
  | inl. e ↦ e
  | inr. ne ↦ match le_total n n' [
    | inl. le ↦ absurd (Id Nat n n') (h .snd (nat_divides_trans (nat_power p (suc. n)) (nat_power p n') m
        (nat_power_le_divides p (suc. n) n' (le_not_equal_lt n n' le ne)) (h' .fst)))
    | inr. ge ↦ absurd (Id Nat n n') (h' .snd (nat_divides_trans (nat_power p (suc. n')) (nat_power p n) m
        (nat_power_le_divides p (suc. n') n (le_not_equal_lt n' n ge (e ↦ ne (inverse Nat n' n e)))) (h .fst))) ] ]

def largest_prime_power_prop (p m : Nat) : isProp (Σ Nat (n ↦ IsLargestPrimePower p n m))
  ≔ u v ↦ subtype_equal Nat (n ↦ IsLargestPrimePower p n m) (n ↦ is_largest_prime_power_prop p n m) u v
      (largest_prime_power_unique p m (u .fst) (v .fst) (u .snd) (v .snd))

def largest_power_from_minimum (p m : Nat) (n : Nat)
  : (NatDivides (nat_power p (suc. n)) m → Empty)
  → ((k : Nat) → (NatDivides (nat_power p (suc. k)) m → Empty) → BookLe n k)
  → NatDivides (nat_power p n) m
  ≔ match n [
  | zero. ↦ _ _ ↦ nat_one_divides m
  | suc. k ↦ _ minimal ↦ match nat_divides_decidable_any (nat_power p (suc. k)) m [
    | inl. d ↦ d
    | inr. nd ↦ absurd (NatDivides (nat_power p (suc. k)) m) (lt_irrefl k (le_from_book (suc. k) k (minimal k nd))) ] ]

{` Existence for p > 1 and m > 0 (the least n with p^(n+1) ∤ m; n = m qualifies). `}
def largest_prime_power_exists (p m : Nat) (hp : Lt (suc. zero.) p) (hm : Lt zero. m)
  : Σ Nat (n ↦ IsLargestPrimePower p n m)
  ≔ let Q : Nat → Type ≔ n ↦ NatDivides (nat_power p (suc. n)) m → Empty in
    let dQ : (n : Nat) → Decidable (Q n)
      ≔ n ↦ match nat_divides_decidable_any (nat_power p (suc. n)) m [
        | inl. d ↦ inr. (nd ↦ nd d)
        | inr. nd ↦ inl. nd ] in
    let qm : Q m ≔ d ↦ lt_irrefl m (lt_le_trans m (nat_power p (suc. m)) m
        (lt_trans m (suc. m) (nat_power p (suc. m)) (le_refl (suc. m)) (nat_power_gt_exponent p hp (suc. m)))
        (nat_divides_le_positive (nat_power p (suc. m)) m hm d)) in
    let w : Σ Nat (IsMinimum Q) ≔ minimum_from_witness Q dQ m qm in
    (w .fst, (largest_power_from_minimum p m (w .fst) (w .snd .fst) (w .snd .snd), w .snd .fst))

{` Cofactor: if m = r·p^n with n largest, then p ∤ r. `}
def largest_prime_power_cofactor (p n m r : Nat) (h : IsLargestPrimePower p n m) (e : Id Nat m (mul r (nat_power p n)))
  (pr : NatDivides p r) : Empty
  ≔ mere_rec (Σ Nat (s ↦ Id Nat r (mul s p))) Empty empty_prop
      (u ↦ h .snd (nat_divides_intro (nat_power p (suc. n)) m (u .fst) (calc
        m = mul r (nat_power p n) by e
        = mul (mul (u .fst) p) (nat_power p n) by refl ((z ↦ mul z (nat_power p n)) : Nat → Nat) (u .snd)
        = mul (u .fst) (mul p (nat_power p n)) by mul_assoc (u .fst) p (nat_power p n)
        = mul (u .fst) (mul (nat_power p n) p) by refl (mul (u .fst)) (mul_comm p (nat_power p n)) ∎)))
      pr

def nat_divides_witness_positive (d k : Nat) : Lt zero. d → NatDivides d k → Σ Nat (q ↦ Id Nat k (mul q d))
  ≔ match d [
  | zero. ↦ hd _ ↦ match hd []
  | suc. c ↦ _ h ↦ nat_divides_witness c k h ]

{` m = r·p^n with p^n the largest power of p dividing m and p ∤ r. `}
def largest_prime_power_decomposition (p m : Nat) (hp : Lt (suc. zero.) p) (hm : Lt zero. m)
  : Σ Nat (n ↦ Σ Nat (r ↦ Product (IsLargestPrimePower p n m)
      (Product (Id Nat m (mul r (nat_power p n))) (NatDivides p r → Empty))))
  ≔ let w : Σ Nat (n ↦ IsLargestPrimePower p n m) ≔ largest_prime_power_exists p m hp hm in
    let q : Σ Nat (r ↦ Id Nat m (mul r (nat_power p (w .fst))))
      ≔ nat_divides_witness_positive (nat_power p (w .fst)) m
          (nat_power_positive p (w .fst) (lt_trans zero. (suc. zero.) p star. hp)) (w .snd .fst) in
    (w .fst, (q .fst, (w .snd, (q .snd, largest_prime_power_cofactor p (w .fst) m (q .fst) (w .snd) (q .snd)))))

{` Litmus: 2^2 is the largest power of 2 dividing 12 (decided), and the
   search computes the exponent 2. `}
def largest_prime_power_litmus_twelve : IsLargestPrimePower (suc. (suc. zero.)) (suc. (suc. zero.)) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))))))
  ≔ (decision_bool_reflect (NatDivides (suc. (suc. (suc. (suc. zero.)))) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))))))) (nat_divides_decidable_any (suc. (suc. (suc. (suc. zero.)))) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))))))) (refl (true. : Bool)),
     nat_decision_false_reflect (NatDivides (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))))))) (nat_divides_decidable_any (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))))))) (refl (false. : Bool)))

def largest_prime_power_litmus_exponent : Id Nat (largest_prime_power_exists (suc. (suc. zero.)) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))))))) star. star. .fst) (suc. (suc. zero.))
  ≔ refl ((suc. (suc. zero.)) : Nat)

{` fingp.tex:16 in general form: if every f(a) divides p^k (p prime) and p
   does not divide Σ_a f(a), then some f(a) is 1. (Positivity of f(a) is not
   needed: a divisor of p^k is automatically positive.) `}
def sum_prime_power_divisors_has_one (A : Type) (ha : IsFinite A) (f : A → Nat) (p k : Nat) (hp : NatIsPrime p)
  (hf : (a : A) → NatDivides (f a) (nat_power p k)) (hs : NatDivides p (arithmetic_sum A ha f) → Empty)
  : Mere (Σ A (a ↦ Id Nat (f a) (suc. zero.)))
  ≔ let P : A → Type ≔ a ↦ Id Nat (f a) (suc. zero.) in
    match finite_quantifiers A ha P (a ↦ nat_set (f a) (suc. zero.)) (a ↦ nat_dec_eq (f a) (suc. zero.)) .snd [
    | inl. t ↦ t
    | inr. no ↦ absurd (Mere (Σ A P)) (hs (arithmetic_sum_divisible A ha f p
        (a ↦ prime_power_divisor_nontrivial p hp k (f a) (hf a) (e ↦ no (mere (Σ A P) (a, e)))))) ]

{` For an explicitly enumerated family the witness can be computed. `}
def fin_sum_prime_power_divisors_has_one (n : Nat) (f : Fin n → Nat) (p k : Nat) (hp : NatIsPrime p)
  (hf : (i : Fin n) → NatDivides (f i) (nat_power p k))
  (hs : NatDivides p (arithmetic_sum (Fin n) (fin_is_finite n) f) → Empty)
  : Σ (Fin n) (i ↦ Id Nat (f i) (suc. zero.))
  ≔ match fin_sigma_decidable n (i ↦ Id Nat (f i) (suc. zero.)) (i ↦ nat_dec_eq (f i) (suc. zero.)) [
    | inl. w ↦ w
    | inr. no ↦ absurd (Σ (Fin n) (i ↦ Id Nat (f i) (suc. zero.)))
        (hs (fin_arithmetic_sum_divisible p n f
          (i ↦ prime_power_divisor_nontrivial p hp k (f i) (hf i) (e ↦ no (i, e))))) ]

{` The orbit form: if every fiber P(a) has cardinality dividing p^k and p
   does not divide |Σ_a P(a)|, then some fiber is a singleton. `}
def cardinality_sigma_prime_power_has_singleton (A : Type) (ha : IsFinite A) (P : A → Type)
  (hp : (a : A) → IsFinite (P a)) (hs : IsFinite (Σ A P)) (p k : Nat) (hpr : NatIsPrime p)
  (hf : (a : A) → NatDivides (cardinality (P a) (hp a)) (nat_power p k))
  (hn : NatDivides p (cardinality (Σ A P) hs) → Empty)
  : Mere (Σ A (a ↦ Id Nat (cardinality (P a) (hp a)) (suc. zero.)))
  ≔ sum_prime_power_divisors_has_one A ha (a ↦ cardinality (P a) (hp a)) p k hpr hf
      (d ↦ hn (transport Nat (NatDivides p) (arithmetic_sum A ha (a ↦ cardinality (P a) (hp a))) (cardinality (Σ A P) hs)
        (inverse Nat (cardinality (Σ A P) hs) (arithmetic_sum A ha (a ↦ cardinality (P a) (hp a)))
          (cardinality_sigma_arithmetic_sum A ha P hp hs)) d))

{` fingp.tex:16, literally: positive integers dividing 8 that add up to 13
   include a 1 (for any number n of summands). `}
def thirteen_sum_divisors_of_eight_has_one (n : Nat) (f : Fin n → Nat) (hf : (i : Fin n) → NatDivides (f i) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))))
  (hs : Id Nat (arithmetic_sum (Fin n) (fin_is_finite n) f) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))))))))
  : Σ (Fin n) (i ↦ Id Nat (f i) (suc. zero.))
  ≔ fin_sum_prime_power_divisors_has_one n f (suc. (suc. zero.)) (suc. (suc. (suc. zero.))) nat_prime_two hf
      (d ↦ nat_divides_litmus_two_thirteen (transport Nat (NatDivides (suc. (suc. zero.))) (arithmetic_sum (Fin n) (fin_is_finite n) f) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))))))) hs d))

{` fingp.tex:16, orbit form: a 13-element set decomposed as Σ_{a:A} P(a)
   with all |P(a)| dividing 8 has a singleton fiber. `}
def fingp_thirteen_eight_has_singleton (A : Type) (ha : IsFinite A) (P : A → Type)
  (hp : (a : A) → IsFinite (P a)) (hs : IsFinite (Σ A P))
  (hf : (a : A) → NatDivides (cardinality (P a) (hp a)) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))) (h13 : Id Nat (cardinality (Σ A P) hs) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))))))))
  : Mere (Σ A (a ↦ Id Nat (cardinality (P a) (hp a)) (suc. zero.)))
  ≔ cardinality_sigma_prime_power_has_singleton A ha P hp hs (suc. (suc. zero.)) (suc. (suc. (suc. zero.))) nat_prime_two hf
      (d ↦ nat_divides_litmus_two_thirteen (transport Nat (NatDivides (suc. (suc. zero.))) (cardinality (Σ A P) hs) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))))))) h13 d))

{` Litmus: 13 = 8 + 4 + 1; the computed witness is the summand 1. `}
def thirteen_sum_litmus_summands : Fin (suc. (suc. (suc. zero.))) → Nat
  ≔ [ inr. _ ↦ (suc. zero.)
    | inl. i ↦ match i [ inr. _ ↦ (suc. (suc. (suc. (suc. zero.)))) | inl. j ↦ match j [ inr. _ ↦ (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))) | inl. e ↦ match e [] ] ] ]

def thirteen_sum_litmus_divisors (i : Fin (suc. (suc. (suc. zero.)))) : NatDivides (thirteen_sum_litmus_summands i) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))
  ≔ match i [
  | inr. _ ↦ nat_one_divides (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))
  | inl. i ↦ match i [
    | inr. _ ↦ nat_divides_intro (suc. (suc. (suc. (suc. zero.)))) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))) (suc. (suc. zero.)) (refl ((suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))) : Nat))
    | inl. j ↦ match j [ inr. _ ↦ nat_divides_refl (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))) | inl. e ↦ match e [] ] ] ]

def thirteen_sum_litmus_total
  : Id Nat (arithmetic_sum (Fin (suc. (suc. (suc. zero.)))) (fin_is_finite (suc. (suc. (suc. zero.)))) thirteen_sum_litmus_summands) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))))))))
  ≔ let f : Fin (suc. (suc. (suc. zero.))) → Nat ≔ thirteen_sum_litmus_summands in
    calc
      arithmetic_sum (Fin (suc. (suc. (suc. zero.)))) (fin_is_finite (suc. (suc. (suc. zero.)))) f
        = add (arithmetic_sum (Fin (suc. (suc. zero.))) (fin_is_finite (suc. (suc. zero.))) (i ↦ f (inl. i))) (suc. zero.) by arithmetic_sum_step (suc. (suc. zero.)) f
      = add (add (arithmetic_sum (Fin (suc. zero.)) (fin_is_finite (suc. zero.)) (i ↦ f (inl. (inl. i)))) (suc. (suc. (suc. (suc. zero.))))) (suc. zero.)
        by refl ((z ↦ add z (suc. zero.)) : Nat → Nat) (arithmetic_sum_step (suc. zero.) (i ↦ f (inl. i)))
      = add (add (add (arithmetic_sum (Fin zero.) (fin_is_finite zero.) (i ↦ f (inl. (inl. (inl. i))))) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))) (suc. (suc. (suc. (suc. zero.))))) (suc. zero.)
        by refl ((z ↦ add (add z (suc. (suc. (suc. (suc. zero.))))) (suc. zero.)) : Nat → Nat) (arithmetic_sum_step zero. (i ↦ f (inl. (inl. i))))
      = add (add (add zero. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))) (suc. (suc. (suc. (suc. zero.))))) (suc. zero.)
        by refl ((z ↦ add (add (add z (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))) (suc. (suc. (suc. (suc. zero.))))) (suc. zero.)) : Nat → Nat) (arithmetic_sum_empty (i ↦ f (inl. (inl. (inl. i))))) ∎

def thirteen_sum_litmus_witness
  : Id (Fin (suc. (suc. (suc. zero.))))
      (thirteen_sum_divisors_of_eight_has_one (suc. (suc. (suc. zero.))) thirteen_sum_litmus_summands thirteen_sum_litmus_divisors
        thirteen_sum_litmus_total .fst)
      (inr. star.)
  ≔ refl (inr. star. : Fin (suc. (suc. (suc. zero.))))
