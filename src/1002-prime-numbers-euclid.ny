export "1001-divisibility-lemmas"

{` Chapter 10 (fingp.tex), supporting arithmetic: prime numbers (NatIsPrime
   of module 1000) and the elementary number theory behind the counting
   arguments: primality is a decidable proposition; Bezout in natural-number
   form for coprime positive a, b (a·x = y·b + 1, by the subtractive Euclidean
   algorithm with fuel); Gauss's lemma (a coprime to b, a | b·c ⇒ a | c);
   Euclid's lemma for primes; the divisors of a prime power p^n are the p^k
   with k ≤ n. Everything is constructive (case splits on decidable
   divisibility and order). `}

def nat_is_prime_prop (p : Nat) : isProp (NatIsPrime p)
  ≔ x y ↦ product_prop (Lt (suc. zero.) p)
      ((d : Nat) → NatDivides d p → Sum (Id Nat d (suc. zero.)) (Id Nat d p))
      (le_prop (suc. (suc. zero.)) p)
      (pi_prop Nat (d ↦ NatDivides d p → Sum (Id Nat d (suc. zero.)) (Id Nat d p))
        (d ↦ pi_prop (NatDivides d p) (_ ↦ Sum (Id Nat d (suc. zero.)) (Id Nat d p))
          (_ ↦ disjoint_sum_prop (Id Nat d (suc. zero.)) (Id Nat d p) (nat_set d (suc. zero.)) (nat_set d p)
            (e1 e2 ↦ lt_not_equal (suc. zero.) p (x .fst)
              (concat Nat (suc. zero.) d p (inverse Nat d (suc. zero.) e1) e2)))))
      x y

def prime_gt_one (p : Nat) (hp : NatIsPrime p) : Lt (suc. zero.) p ≔ hp .fst

def prime_ne_one (p : Nat) (hp : NatIsPrime p) (e : Id Nat p (suc. zero.)) : Empty
  ≔ lt_not_equal (suc. zero.) p (hp .fst) (inverse Nat p (suc. zero.) e)

def prime_positive (p : Nat) (hp : NatIsPrime p) : Lt zero. p
  ≔ lt_trans zero. (suc. zero.) p star. (hp .fst)

def prime_divisors (p : Nat) (hp : NatIsPrime p) (d : Nat) (h : NatDivides d p)
  : Sum (Id Nat d (suc. zero.)) (Id Nat d p)
  ≔ hp .snd d h

{` Decision procedures. `}
def nat_decidable_implies (A B : Type) (da : Decidable A) (db : Decidable B) : Decidable (A → B)
  ≔ match da [
  | inr. na ↦ inl. (a ↦ absurd B (na a))
  | inl. a ↦ match db [ inl. b ↦ inl. (_ ↦ b) | inr. nb ↦ inr. (f ↦ nb (f a)) ] ]

def nat_decidable_sum (A B : Type) (da : Decidable A) (db : Decidable B) : Decidable (Sum A B)
  ≔ match da [
  | inl. a ↦ inl. (inl. a)
  | inr. na ↦ match db [
    | inl. b ↦ inl. (inr. b)
    | inr. nb ↦ inr. (s ↦ match s [ inl. a ↦ na a | inr. b ↦ nb b ]) ] ]

{` A bounded universal quantifier over decidable predicates is decidable. `}
def nat_bounded_forall_decidable (P : Nat → Type) (dP : (k : Nat) → Decidable (P k)) (n : Nat)
  : Decidable ((k : Nat) → Lt k n → P k)
  ≔ match n [
  | zero. ↦ inl. (k h ↦ match h [])
  | suc. n ↦ match nat_bounded_forall_decidable P dP n [
    | inr. no ↦ inr. (f ↦ no (k h ↦ f k (le_step (suc. k) n h)))
    | inl. all ↦ match dP n [
      | inr. npn ↦ inr. (f ↦ npn (f n (le_refl n)))
      | inl. pn ↦ inl. (k h ↦ match le_split k n h [
        | inl. lt ↦ all k lt
        | inr. e ↦ transport Nat P n k (inverse Nat k n e) pn ]) ] ] ]

def nat_divides_le_positive (d k : Nat) : Lt zero. k → NatDivides d k → Le d k
  ≔ match k [
  | zero. ↦ hk _ ↦ match hk []
  | suc. k ↦ _ h ↦ nat_divides_le d k h ]

{` Primality is decidable: only the divisors d ≤ p need to be inspected. `}
def nat_is_prime_decidable (p : Nat) : Decidable (NatIsPrime p)
  ≔ let P : Nat → Type ≔ d ↦ NatDivides d p → Sum (Id Nat d (suc. zero.)) (Id Nat d p) in
    match lt_decidable (suc. zero.) p [
    | inr. n ↦ inr. (h ↦ n (h .fst))
    | inl. gt ↦ match nat_bounded_forall_decidable P
        (d ↦ nat_decidable_implies (NatDivides d p) (Sum (Id Nat d (suc. zero.)) (Id Nat d p))
          (nat_divides_decidable_any d p)
          (nat_decidable_sum (Id Nat d (suc. zero.)) (Id Nat d p) (nat_dec_eq d (suc. zero.)) (nat_dec_eq d p)))
        (suc. p) [
      | inl. all ↦ inl. (gt, d hd ↦ all d (nat_divides_le_positive d p (lt_trans zero. (suc. zero.) p star. gt) hd) hd)
      | inr. no ↦ inr. (h ↦ no (d _ hd ↦ h .snd d hd)) ] ]

{` Litmus: 2, 3, 5 are prime; 0, 1, 4, 6 are not (decided by computation). `}
def nat_prime_two : NatIsPrime (suc. (suc. zero.))
  ≔ decision_bool_reflect (NatIsPrime (suc. (suc. zero.))) (nat_is_prime_decidable (suc. (suc. zero.))) (refl (true. : Bool))

def nat_prime_three : NatIsPrime (suc. (suc. (suc. zero.)))
  ≔ decision_bool_reflect (NatIsPrime (suc. (suc. (suc. zero.)))) (nat_is_prime_decidable (suc. (suc. (suc. zero.)))) (refl (true. : Bool))

def nat_prime_five : NatIsPrime (suc. (suc. (suc. (suc. (suc. zero.)))))
  ≔ decision_bool_reflect (NatIsPrime (suc. (suc. (suc. (suc. (suc. zero.)))))) (nat_is_prime_decidable (suc. (suc. (suc. (suc. (suc. zero.)))))) (refl (true. : Bool))

def nat_not_prime_zero : NatIsPrime zero. → Empty ≔ h ↦ h .fst

def nat_not_prime_one : NatIsPrime (suc. zero.) → Empty ≔ h ↦ h .fst

def nat_not_prime_four : NatIsPrime (suc. (suc. (suc. (suc. zero.)))) → Empty
  ≔ nat_decision_false_reflect (NatIsPrime (suc. (suc. (suc. (suc. zero.))))) (nat_is_prime_decidable (suc. (suc. (suc. (suc. zero.))))) (refl (false. : Bool))

def nat_not_prime_six : NatIsPrime (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))) → Empty
  ≔ nat_decision_false_reflect (NatIsPrime (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))) (nat_is_prime_decidable (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))) (refl (false. : Bool))

{` Coprimality. `}
def nat_coprime_sym (a b : Nat) (h : NatCoprime a b) : NatCoprime b a ≔ d x y ↦ h d y x

def prime_not_divides_coprime (p a : Nat) (hp : NatIsPrime p) (h : NatDivides p a → Empty) : NatCoprime p a
  ≔ d hdp hda ↦ match hp .snd d hdp [
    | inl. e ↦ e
    | inr. e ↦ absurd (Id Nat d (suc. zero.)) (h (transport Nat (x ↦ NatDivides x a) d p e hda)) ]

{` Bezout in natural numbers: a·x = y·b + 1. `}
def NatBezout (a b : Nat) : Type ≔ Σ Nat (x ↦ Σ Nat (y ↦ Id Nat (mul a x) (suc. (mul y b))))

def nat_bezout_one_left (n : Nat) : NatBezout (suc. zero.) n
  ≔ (suc. zero., (zero., suc. (inverse Nat (mul zero. n) zero. (mul_zero_left n))))

{` From a·x = y·c + 1 and c + a = n: a·(x + y) = y·n + 1. `}
def nat_bezout_extend_right (a c n : Nat) (eq : Id Nat (add c a) n) (B : NatBezout a c) : NatBezout a n
  ≔ let x : Nat ≔ B .fst in let y : Nat ≔ B .snd .fst in
    (add x y, (y, calc
      mul a (add x y) = add (mul a x) (mul a y) by mul_add_left a x y
      = add (suc. (mul y c)) (mul a y) by refl ((z ↦ add z (mul a y)) : Nat → Nat) (B .snd .snd)
      = (suc. (add (mul y c) (mul a y)) : Nat) by add_suc_left (mul y c) (mul a y)
      = (suc. (add (mul y c) (mul y a)) : Nat) by suc. (refl (add (mul y c)) (mul_comm a y))
      = (suc. (mul y (add c a)) : Nat)
        by suc. (inverse Nat (mul y (add c a)) (add (mul y c) (mul y a)) (mul_add_left y c a))
      = (suc. (mul y n) : Nat) by suc. (refl (mul y) eq) ∎))

{` From c·x = y·b + 1 and c + b = n: n·x = (y + x)·b + 1. `}
def nat_bezout_extend_left (c b n : Nat) (eq : Id Nat (add c b) n) (B : NatBezout c b) : NatBezout n b
  ≔ let x : Nat ≔ B .fst in let y : Nat ≔ B .snd .fst in
    (x, (add y x, calc
      mul n x = mul (add c b) x by refl ((z ↦ mul z x) : Nat → Nat) (inverse Nat (add c b) n eq)
      = add (mul c x) (mul b x) by mul_add_right c b x
      = add (suc. (mul y b)) (mul b x) by refl ((z ↦ add z (mul b x)) : Nat → Nat) (B .snd .snd)
      = (suc. (add (mul y b) (mul b x)) : Nat) by add_suc_left (mul y b) (mul b x)
      = (suc. (add (mul y b) (mul x b)) : Nat) by suc. (refl (add (mul y b)) (mul_comm b x))
      = (suc. (mul (add y x) b) : Nat)
        by suc. (inverse Nat (mul (add y x) b) (add (mul y b) (mul x b)) (mul_add_right y x b)) ∎))

{` Subtractive Euclidean algorithm; the fuel bounds a + b. `}
def nat_bezout_fuel (f a b : Nat) (bound : Le (add (suc. a) (suc. b)) f) (cop : NatCoprime (suc. a) (suc. b))
  : NatBezout (suc. a) (suc. b)
  ≔ match f [
  | zero. ↦ match bound []
  | suc. f ↦ match nat_dec_eq a b [
    | inl. e ↦
        let ea : Id Nat (suc. a) (suc. zero.)
          ≔ cop (suc. a) (nat_divides_refl (suc. a))
              (transport Nat (x ↦ NatDivides (suc. a) (suc. x)) a b e (nat_divides_refl (suc. a))) in
        transport Nat (x ↦ NatBezout x (suc. b)) (suc. zero.) (suc. a) (inverse Nat (suc. a) (suc. zero.) ea)
          (nat_bezout_one_left (suc. b))
    | inr. ne ↦ match le_total a b [
      | inl. le ↦
          let w : BookLe (suc. a) b ≔ le_to_book (suc. a) b (le_not_equal_lt a b le ne) in
          let c : Nat ≔ w .fst in
          let cb : Id Nat (add (suc. c) a) b
            ≔ concat Nat (add (suc. c) a) (suc. (add c a)) b (add_suc_left c a) (w .snd) in
          let lt : Lt c b ≔ transport Nat (x ↦ Lt c x) (suc. (add c a)) b (w .snd) (le_add_base c a) in
          nat_bezout_extend_right (suc. a) (suc. c) (suc. b) (suc. cb)
            (nat_bezout_fuel f a c
              (lt_le_trans (add (suc. a) c) (add (suc. a) b) f (lt_add_left (suc. a) c b lt) bound)
              (d da dc ↦ cop d da (transport Nat (NatDivides d) (add (suc. c) (suc. a)) (suc. b) (suc. cb)
                 (nat_divides_add d (suc. c) (suc. a) dc da))))
      | inr. ge ↦
          let w : BookLe (suc. b) a ≔ le_to_book (suc. b) a (le_not_equal_lt b a ge (e ↦ ne (inverse Nat b a e))) in
          let c : Nat ≔ w .fst in
          let ca : Id Nat (add (suc. c) b) a
            ≔ concat Nat (add (suc. c) b) (suc. (add c b)) a (add_suc_left c b) (w .snd) in
          let lt : Lt c a ≔ transport Nat (x ↦ Lt c x) (suc. (add c b)) a (w .snd) (le_add_base c b) in
          nat_bezout_extend_left (suc. c) (suc. b) (suc. a) (suc. ca)
            (nat_bezout_fuel f c b
              (lt_le_trans (add (suc. c) b) (add (suc. a) b) f (lt_add_right (suc. c) (suc. a) b lt) bound)
              (d dc db ↦ cop d (transport Nat (NatDivides d) (add (suc. c) (suc. b)) (suc. a) (suc. ca)
                 (nat_divides_add d (suc. c) (suc. b) dc db)) db)) ] ] ]

{` Bezout for coprime positive a, b. (The hypothesis 0 < a cannot be
   dropped: 0 and 1 are coprime but 0·x = y·1 + 1 has no solution.) `}
def coprime_bezout_nat (a b : Nat) : NatCoprime a b → Lt zero. a → Lt zero. b → NatBezout a b
  ≔ match a, b [
  | zero., b ↦ _ ha _ ↦ match ha []
  | suc. a, zero. ↦ _ _ hb ↦ match hb []
  | suc. a, suc. b ↦ cop _ _ ↦
      nat_bezout_fuel (add (suc. a) (suc. b)) a b (le_refl (add (suc. a) (suc. b))) cop ]

{` Gauss's lemma: a coprime to b and a | b·c imply a | c (all a, b, c). `}
def coprime_divides_product (a b c : Nat) : NatCoprime a b → NatDivides a (mul b c) → NatDivides a c
  ≔ match a, b [
  | zero., b ↦ cop h ↦
      let eb : Id Nat b (suc. zero.) ≔ cop b (nat_divides_zero b) (nat_divides_refl b) in
      nat_divides_intro zero. c zero. (calc
        c = mul (suc. zero.) c by inverse Nat (mul (suc. zero.) c) c (mul_one_left c)
        = mul b c by refl ((x ↦ mul x c) : Nat → Nat) (inverse Nat b (suc. zero.) eb)
        = (zero. : Nat) by nat_zero_divides (mul b c) h ∎)
  | suc. a, zero. ↦ cop _ ↦
      let ea : Id Nat (suc. a) (suc. zero.) ≔ cop (suc. a) (nat_divides_refl (suc. a)) (nat_divides_zero (suc. a)) in
      transport Nat (x ↦ NatDivides x c) (suc. zero.) (suc. a) (inverse Nat (suc. a) (suc. zero.) ea) (nat_one_divides c)
  | suc. a, suc. b ↦ cop h ↦
      let B : NatBezout (suc. a) (suc. b) ≔ coprime_bezout_nat (suc. a) (suc. b) cop star. star. in
      let x : Nat ≔ B .fst in let y : Nat ≔ B .snd .fst in
      let key : Id Nat (mul (mul (suc. a) x) c) (add (mul y (mul (suc. b) c)) c) ≔ calc
        mul (mul (suc. a) x) c = mul (suc. (mul y (suc. b))) c by refl ((z ↦ mul z c) : Nat → Nat) (B .snd .snd)
        = add (mul (mul y (suc. b)) c) c by mul_suc_left (mul y (suc. b)) c
        = add (mul y (mul (suc. b) c)) c by refl ((z ↦ add z c) : Nat → Nat) (mul_assoc y (suc. b) c) ∎ in
      nat_divides_add_cancel (suc. a) (mul y (mul (suc. b) c)) c
        (transport Nat (NatDivides (suc. a)) (mul (mul (suc. a) x) c) (add (mul y (mul (suc. b) c)) c) key
          (nat_divides_mul_right (suc. a) (mul (suc. a) x) c
            (nat_divides_mul_right (suc. a) (suc. a) x (nat_divides_refl (suc. a)))))
        (nat_divides_mul_left (suc. a) y (mul (suc. b) c) h) ]

{` Euclid's lemma: a prime dividing a·b divides a or b. `}
def prime_euclid (p a b : Nat) (hp : NatIsPrime p) (h : NatDivides p (mul a b)) : Sum (NatDivides p a) (NatDivides p b)
  ≔ match nat_divides_decidable_any p a [
  | inl. pa ↦ inl. pa
  | inr. npa ↦ inr. (coprime_divides_product p a b (prime_not_divides_coprime p a hp npa) h) ]

def nat_coprime_mul_right (m a b : Nat) (ha : NatCoprime m a) (hb : NatCoprime m b) : NatCoprime m (mul a b)
  ≔ d dm dab ↦ hb d dm (coprime_divides_product d a b (e de da ↦ ha e (nat_divides_trans e d m de dm) da) dab)

{` m coprime to a implies m coprime to every power a^n (requested as
   coprime_prime_power; primality is not needed). `}
def nat_coprime_power (m a n : Nat) (h : NatCoprime m a) : NatCoprime m (nat_power a n)
  ≔ match n [
  | zero. ↦ d _ d1 ↦ nat_divides_one d d1
  | suc. n ↦ nat_coprime_mul_right m (nat_power a n) a (nat_coprime_power m a n h) h ]

{` p^n | m·a with m coprime to p implies p^n | a. `}
def nat_power_divides_coprime_cancel (p m a n : Nat) (hm : NatCoprime m p) (h : NatDivides (nat_power p n) (mul m a))
  : NatDivides (nat_power p n) a
  ≔ coprime_divides_product (nat_power p n) m a (nat_coprime_sym m (nat_power p n) (nat_coprime_power m p n hm)) h

{` A prime dividing a^n divides a. `}
def prime_divides_power (p a : Nat) (hp : NatIsPrime p) (n : Nat) (h : NatDivides p (nat_power a n)) : NatDivides p a
  ≔ match n [
  | zero. ↦ absurd (NatDivides p a) (prime_ne_one p hp (nat_divides_one p h))
  | suc. n ↦ match prime_euclid p (nat_power a n) a hp h [
    | inl. q ↦ prime_divides_power p a hp n q
    | inr. q ↦ q ] ]

{` Divisors of prime powers. `}
def prime_power_divisor_at (c : Nat) (hp : NatIsPrime (suc. c)) (n : Nat)
  : (d : Nat) → NatDivides d (nat_power (suc. c) n) → Σ Nat (k ↦ Product (Le k n) (Id Nat d (nat_power (suc. c) k)))
  ≔ match n [
  | zero. ↦ d h ↦ (zero., (star., nat_divides_one d h))
  | suc. n ↦ d h ↦ match nat_divides_decidable_any (suc. c) d [
    | inl. pd ↦
        let w : Σ Nat (q ↦ Id Nat d (mul q (suc. c))) ≔ nat_divides_witness c d pd in
        let r : Σ Nat (k ↦ Product (Le k n) (Id Nat (w .fst) (nat_power (suc. c) k)))
          ≔ prime_power_divisor_at c hp n (w .fst)
              (nat_divides_mul_cancel_right c (w .fst) (nat_power (suc. c) n)
                (transport Nat (x ↦ NatDivides x (mul (nat_power (suc. c) n) (suc. c))) d (mul (w .fst) (suc. c))
                  (w .snd) h)) in
        (suc. (r .fst), (r .snd .fst,
          concat Nat d (mul (w .fst) (suc. c)) (mul (nat_power (suc. c) (r .fst)) (suc. c)) (w .snd)
            (refl ((x ↦ mul x (suc. c)) : Nat → Nat) (r .snd .snd))))
    | inr. npd ↦
        let r : Σ Nat (k ↦ Product (Le k n) (Id Nat d (nat_power (suc. c) k)))
          ≔ prime_power_divisor_at c hp n d
              (coprime_divides_product d (suc. c) (nat_power (suc. c) n)
                (nat_coprime_sym (suc. c) d (prime_not_divides_coprime (suc. c) d hp npd))
                (transport Nat (NatDivides d) (mul (nat_power (suc. c) n) (suc. c)) (mul (suc. c) (nat_power (suc. c) n))
                  (mul_comm (nat_power (suc. c) n) (suc. c)) h)) in
        (r .fst, (le_step (r .fst) n (r .snd .fst), r .snd .snd)) ] ]

{` Every divisor of p^n is p^k for some k ≤ n. `}
def prime_power_divisor (p : Nat) (hp : NatIsPrime p) (n d : Nat) (h : NatDivides d (nat_power p n))
  : Σ Nat (k ↦ Product (Le k n) (Id Nat d (nat_power p k)))
  ≔ match p [
  | zero. ↦ absurd (Σ Nat (k ↦ Product (Le k n) (Id Nat d (nat_power zero. k)))) (hp .fst)
  | suc. c ↦ prime_power_divisor_at c hp n d h ]

def nat_power_ne_one_divides (p k d : Nat)
  : Id Nat d (nat_power p k) → (Id Nat d (suc. zero.) → Empty) → NatDivides p d
  ≔ match k [
  | zero. ↦ e ne ↦ absurd (NatDivides p d) (ne e)
  | suc. k ↦ e _ ↦ transport Nat (NatDivides p) (mul (nat_power p k) p) d (inverse Nat d (mul (nat_power p k) p) e)
      (nat_divides_mul_left p (nat_power p k) p (nat_divides_refl p)) ]

{` A divisor of p^n other than 1 is divisible by p. `}
def prime_power_divisor_nontrivial (p : Nat) (hp : NatIsPrime p) (n d : Nat) (h : NatDivides d (nat_power p n))
  (ne : Id Nat d (suc. zero.) → Empty) : NatDivides p d
  ≔ let r : Σ Nat (k ↦ Product (Le k n) (Id Nat d (nat_power p k))) ≔ prime_power_divisor p hp n d h in
    nat_power_ne_one_divides p (r .fst) d (r .snd .snd) ne

{` A divisor of p^n is 1 or divisible by p (orbit sizes in a p-group). `}
def prime_power_divisor_one_or_divisible (p : Nat) (hp : NatIsPrime p) (n d : Nat) (h : NatDivides d (nat_power p n))
  : Sum (Id Nat d (suc. zero.)) (NatDivides p d)
  ≔ match nat_dec_eq d (suc. zero.) [
  | inl. e ↦ inl. e
  | inr. ne ↦ inr. (prime_power_divisor_nontrivial p hp n d h ne) ]

{` p^(n+1) | a·p^n implies p | a (for p > 0). `}
def nat_power_succ_divides_cofactor (p n a : Nat) (hp : Lt zero. p)
  (h : NatDivides (nat_power p (suc. n)) (mul a (nat_power p n))) : NatDivides p a
  ≔ nat_divides_mul_cancel_positive (nat_power p n) p a (nat_power_positive p n hp)
      (transport Nat (x ↦ NatDivides x (mul a (nat_power p n))) (mul (nat_power p n) p) (mul p (nat_power p n))
        (mul_comm (nat_power p n) p) h)

{` Growth of powers of p > 1. `}
def nat_lt_double (x : Nat) : Lt (suc. x) (mul (suc. x) (suc. (suc. zero.)))
  ≔ transport Nat (z ↦ Le (suc. x) (add z x)) (suc. x) (add zero. (suc. x))
      (inverse Nat (add zero. (suc. x)) (suc. x) (add_zero_left (suc. x))) (le_add_base (suc. x) x)

def nat_lt_mul_gt_one (x p : Nat) : Lt zero. x → Lt (suc. zero.) p → Lt x (mul x p)
  ≔ match x [
  | zero. ↦ hx _ ↦ match hx []
  | suc. x ↦ _ hp ↦ lt_le_trans (suc. x) (mul (suc. x) (suc. (suc. zero.))) (mul (suc. x) p)
      (nat_lt_double x) (le_mul_left (suc. x) (suc. (suc. zero.)) p hp) ]

def nat_power_lt_succ (p : Nat) (hp : Lt (suc. zero.) p) (i : Nat) : Lt (nat_power p i) (nat_power p (suc. i))
  ≔ nat_lt_mul_gt_one (nat_power p i) p (nat_power_positive p i (lt_trans zero. (suc. zero.) p star. hp)) hp

def nat_power_le (p : Nat) (hp : Lt zero. p) (i j : Nat) (h : Le i j) : Le (nat_power p i) (nat_power p j)
  ≔ nat_divides_le_positive (nat_power p i) (nat_power p j) (nat_power_positive p j hp) (nat_power_le_divides p i j h)

def nat_power_strict (p : Nat) (hp : Lt (suc. zero.) p) (i j : Nat) (h : Lt i j) : Lt (nat_power p i) (nat_power p j)
  ≔ lt_le_trans (nat_power p i) (nat_power p (suc. i)) (nat_power p j) (nat_power_lt_succ p hp i)
      (nat_power_le p (lt_trans zero. (suc. zero.) p star. hp) (suc. i) j h)

def nat_power_injective (p : Nat) (hp : Lt (suc. zero.) p) (i j : Nat) (e : Id Nat (nat_power p i) (nat_power p j))
  : Id Nat i j
  ≔ match nat_dec_eq i j [
  | inl. q ↦ q
  | inr. ne ↦ match le_total i j [
    | inl. le ↦ absurd (Id Nat i j) (lt_not_equal (nat_power p i) (nat_power p j)
        (nat_power_strict p hp i j (le_not_equal_lt i j le ne)) e)
    | inr. ge ↦ absurd (Id Nat i j) (lt_not_equal (nat_power p j) (nat_power p i)
        (nat_power_strict p hp j i (le_not_equal_lt j i ge (q ↦ ne (inverse Nat j i q))))
        (inverse Nat (nat_power p i) (nat_power p j) e)) ] ]

def nat_power_gt_exponent (p : Nat) (hp : Lt (suc. zero.) p) (n : Nat) : Lt n (nat_power p n)
  ≔ match n [
  | zero. ↦ star.
  | suc. n ↦ le_trans (suc. (suc. n)) (suc. (nat_power p n)) (nat_power p (suc. n))
      (nat_power_gt_exponent p hp n) (nat_power_lt_succ p hp n) ]

{` If a·b = p^n then a = p^i, b = p^j with i + j = n. `}
def prime_power_factors (p : Nat) (hp : NatIsPrime p) (n a b : Nat) (h : Id Nat (mul a b) (nat_power p n))
  : Σ Nat (i ↦ Σ Nat (j ↦ Product (Id Nat a (nat_power p i)) (Product (Id Nat b (nat_power p j)) (Id Nat (add i j) n))))
  ≔ let ra : Σ Nat (k ↦ Product (Le k n) (Id Nat a (nat_power p k)))
      ≔ prime_power_divisor p hp n a (nat_divides_intro a (nat_power p n) b
          (concat Nat (nat_power p n) (mul a b) (mul b a) (inverse Nat (mul a b) (nat_power p n) h) (mul_comm a b))) in
    let rb : Σ Nat (k ↦ Product (Le k n) (Id Nat b (nat_power p k)))
      ≔ prime_power_divisor p hp n b (nat_divides_intro b (nat_power p n) a (inverse Nat (mul a b) (nat_power p n) h)) in
    (ra .fst, (rb .fst, (ra .snd .snd, (rb .snd .snd,
      nat_power_injective p (hp .fst) (add (ra .fst) (rb .fst)) n (calc
        nat_power p (add (ra .fst) (rb .fst)) = mul (nat_power p (ra .fst)) (nat_power p (rb .fst))
          by nat_power_add p (ra .fst) (rb .fst)
        = mul a b by refl mul (inverse Nat a (nat_power p (ra .fst)) (ra .snd .snd))
            (inverse Nat b (nat_power p (rb .fst)) (rb .snd .snd))
        = nat_power p n by h ∎)))))

{` Litmus: 8 = 2^3 and 9 = 3^2 are coprime, with the Bezout identity
   3·2 = 1·5 + 1 for 3 and 5; the divisor 4 of 8 is a power of 2. `}
def nat_coprime_litmus_eight_nine : NatCoprime (nat_power (suc. (suc. zero.)) (suc. (suc. (suc. zero.)))) (nat_power (suc. (suc. (suc. zero.))) (suc. (suc. zero.)))
  ≔ let c23 : NatCoprime (suc. (suc. zero.)) (suc. (suc. (suc. zero.)))
      ≔ prime_not_divides_coprime (suc. (suc. zero.)) (suc. (suc. (suc. zero.))) nat_prime_two
          (nat_decision_false_reflect (NatDivides (suc. (suc. zero.)) (suc. (suc. (suc. zero.)))) (nat_divides_decidable_any (suc. (suc. zero.)) (suc. (suc. (suc. zero.)))) (refl (false. : Bool))) in
    nat_coprime_sym (nat_power (suc. (suc. (suc. zero.))) (suc. (suc. zero.))) (nat_power (suc. (suc. zero.)) (suc. (suc. (suc. zero.))))
      (nat_coprime_power (nat_power (suc. (suc. (suc. zero.))) (suc. (suc. zero.))) (suc. (suc. zero.)) (suc. (suc. (suc. zero.)))
        (nat_coprime_sym (suc. (suc. zero.)) (nat_power (suc. (suc. (suc. zero.))) (suc. (suc. zero.))) (nat_coprime_power (suc. (suc. zero.)) (suc. (suc. (suc. zero.))) (suc. (suc. zero.)) c23)))

def nat_bezout_litmus_three_five : NatBezout (suc. (suc. (suc. zero.))) (suc. (suc. (suc. (suc. (suc. zero.))))) ≔ ((suc. (suc. zero.)), ((suc. zero.), refl ((suc. (suc. (suc. (suc. (suc. (suc. zero.)))))) : Nat)))

def nat_power_divisor_litmus_four_eight
  : Σ Nat (k ↦ Product (Le k (suc. (suc. (suc. zero.)))) (Id Nat (suc. (suc. (suc. (suc. zero.)))) (nat_power (suc. (suc. zero.)) k)))
  ≔ prime_power_divisor (suc. (suc. zero.)) nat_prime_two (suc. (suc. (suc. zero.))) (suc. (suc. (suc. (suc. zero.)))) (nat_divides_intro (suc. (suc. (suc. (suc. zero.)))) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))) (suc. (suc. zero.)) (refl ((suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))) : Nat)))
