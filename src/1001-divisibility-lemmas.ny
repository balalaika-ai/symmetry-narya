export "1000-prime-numbers"
export "241-cycle-generators"

{` Chapter 10 (fingp.tex), supporting arithmetic: elementary facts about
   divisibility d | k (NatDivides of module 147, ∃ q, k = q·d, a
   proposition) and about powers b^e (nat_power of module 1000), used by the
   counting arguments of the chapter. Reused: nat_divides_one (module 241),
   mul_one_left / mul_one_right / decision_bool / decision_bool_reflect (module 178),
   Euclidean division and its uniqueness (module 48). Divisibility is
   decided for every d (including d = 0) via Euclidean division. `}

def nat_divides_intro (d k q : Nat) (p : Id Nat k (mul q d)) : NatDivides d k
  ≔ mere (Σ Nat (j ↦ Id Nat k (mul j d))) (q, p)

def nat_divides_refl (d : Nat) : NatDivides d d
  ≔ nat_divides_intro d d (suc. zero.) (inverse Nat (mul (suc. zero.) d) d (mul_one_left d))

def nat_divides_zero (d : Nat) : NatDivides d zero.
  ≔ nat_divides_intro d zero. zero. (inverse Nat (mul zero. d) zero. (mul_zero_left d))

def nat_one_divides (k : Nat) : NatDivides (suc. zero.) k
  ≔ nat_divides_intro (suc. zero.) k k (inverse Nat (mul k (suc. zero.)) k (mul_one_right k))

{` 0 | k forces k = 0. `}
def nat_zero_divides (k : Nat) (h : NatDivides zero. k) : Id Nat k zero.
  ≔ mere_rec (Σ Nat (q ↦ Id Nat k (mul q zero.))) (Id Nat k zero.) (nat_set k zero.) (u ↦ u .snd) h

def nat_divides_trans (a b c : Nat) (h : NatDivides a b) (k : NatDivides b c) : NatDivides a c
  ≔ mere_rec (Σ Nat (q ↦ Id Nat b (mul q a))) (NatDivides a c) (nat_divides_prop a c)
      (u ↦ mere_rec (Σ Nat (q ↦ Id Nat c (mul q b))) (NatDivides a c) (nat_divides_prop a c)
        (v ↦ nat_divides_intro a c (mul (v .fst) (u .fst)) (calc
          c = mul (v .fst) b by v .snd
          = mul (v .fst) (mul (u .fst) a) by refl (mul (v .fst)) (u .snd)
          = mul (mul (v .fst) (u .fst)) a
            by inverse Nat (mul (mul (v .fst) (u .fst)) a) (mul (v .fst) (mul (u .fst) a)) (mul_assoc (v .fst) (u .fst) a) ∎))
        k) h

{` d | a implies d | a·b. `}
def nat_divides_mul_right (d a b : Nat) (h : NatDivides d a) : NatDivides d (mul a b)
  ≔ mere_rec (Σ Nat (q ↦ Id Nat a (mul q d))) (NatDivides d (mul a b)) (nat_divides_prop d (mul a b))
      (u ↦ let q ≔ u .fst in nat_divides_intro d (mul a b) (mul q b) (calc
        mul a b = mul (mul q d) b by refl ((x ↦ mul x b) : Nat → Nat) (u .snd)
        = mul q (mul d b) by mul_assoc q d b
        = mul q (mul b d) by refl (mul q) (mul_comm d b)
        = mul (mul q b) d by inverse Nat (mul (mul q b) d) (mul q (mul b d)) (mul_assoc q b d) ∎)) h

{` d | b implies d | a·b. `}
def nat_divides_mul_left (d a b : Nat) (h : NatDivides d b) : NatDivides d (mul a b)
  ≔ mere_rec (Σ Nat (q ↦ Id Nat b (mul q d))) (NatDivides d (mul a b)) (nat_divides_prop d (mul a b))
      (u ↦ let q ≔ u .fst in nat_divides_intro d (mul a b) (mul a q) (calc
        mul a b = mul a (mul q d) by refl (mul a) (u .snd)
        = mul (mul a q) d by inverse Nat (mul (mul a q) d) (mul a (mul q d)) (mul_assoc a q d) ∎)) h

def nat_divides_add (d a b : Nat) (ha : NatDivides d a) (hb : NatDivides d b) : NatDivides d (add a b)
  ≔ mere_rec (Σ Nat (q ↦ Id Nat a (mul q d))) (NatDivides d (add a b)) (nat_divides_prop d (add a b))
      (u ↦ mere_rec (Σ Nat (q ↦ Id Nat b (mul q d))) (NatDivides d (add a b)) (nat_divides_prop d (add a b))
        (v ↦ nat_divides_intro d (add a b) (add (u .fst) (v .fst)) (calc
          add a b = add (mul (u .fst) d) (mul (v .fst) d) by refl add (u .snd) (v .snd)
          = mul (add (u .fst) (v .fst)) d
            by inverse Nat (mul (add (u .fst) (v .fst)) d) (add (mul (u .fst) d) (mul (v .fst) d))
              (mul_add_right (u .fst) (v .fst) d) ∎))
        hb) ha

{` Euclidean division by a positive number, and cancellation of a positive factor. `}
def nat_positive_book (c : Nat) : BookLt zero. (suc. c) ≔ lt_to_book zero. (suc. c) star.

def nat_mul_cancel_right (c x y : Nat) (p : Id Nat (mul x (suc. c)) (mul y (suc. c))) : Id Nat x y
  ≔ division_quotients_equal (mul x (suc. c)) (suc. c)
      ((x, zero.), (nat_positive_book c, refl (mul x (suc. c))))
      ((y, zero.), (nat_positive_book c, p))

{` If m = suc c divides k and k = q·m + r with r < m, then r = 0. `}
def nat_divides_remainder_zero (c k q r : Nat) (hr : BookLt r (suc. c))
  (p : Id Nat k (add (mul q (suc. c)) r)) (h : NatDivides (suc. c) k) : Id Nat r zero.
  ≔ mere_rec (Σ Nat (j ↦ Id Nat k (mul j (suc. c)))) (Id Nat r zero.) (nat_set r zero.)
      (u ↦ division_remainders_equal k (suc. c) ((q, r), (hr, p)) ((u .fst, zero.), (nat_positive_book c, u .snd))) h

def nat_add_zero_right (a b : Nat) : Id Nat (add a b) zero. → Id Nat b zero.
  ≔ match b [
  | zero. ↦ _ ↦ refl (zero. : Nat)
  | suc. b ↦ p ↦ absurd (Id Nat (suc. b) zero.) (nat_encode (suc. (add a b)) zero. p) ]

{` d | a + b and d | a imply d | b. `}
def nat_divides_add_cancel (d a b : Nat) : NatDivides d (add a b) → NatDivides d a → NatDivides d b
  ≔ match d [
  | zero. ↦ hab _ ↦ nat_divides_intro zero. b zero. (nat_add_zero_right a b (nat_zero_divides (add a b) hab))
  | suc. c ↦ hab ha ↦
      mere_rec (Σ Nat (q ↦ Id Nat a (mul q (suc. c)))) (NatDivides (suc. c) b) (nat_divides_prop (suc. c) b)
        (v ↦ let m : Nat ≔ suc. c in
          let w : DivisionResult b m ≔ euclidean_division b m (nat_positive_book c) in
          let s : Nat ≔ w .fst .fst in let r : Nat ≔ w .fst .snd in
          let eqn : Id Nat (add a b) (add (mul (add (v .fst) s) m) r) ≔ calc
            add a b = add (mul (v .fst) m) (add (mul s m) r) by refl add (v .snd) (w .snd .snd)
            = add (add (mul (v .fst) m) (mul s m)) r
              by inverse Nat (add (add (mul (v .fst) m) (mul s m)) r) (add (mul (v .fst) m) (add (mul s m) r))
                (add_assoc (mul (v .fst) m) (mul s m) r)
            = add (mul (add (v .fst) s) m) r
              by refl ((x ↦ add x r) : Nat → Nat)
                (inverse Nat (mul (add (v .fst) s) m) (add (mul (v .fst) m) (mul s m)) (mul_add_right (v .fst) s m)) ∎ in
          let r0 : Id Nat r zero. ≔ nat_divides_remainder_zero c (add a b) (add (v .fst) s) r (w .snd .fst) eqn hab in
          nat_divides_intro m b s
            (concat Nat b (add (mul s m) r) (mul s m) (w .snd .snd) (refl (add (mul s m)) r0)))
        ha ]

{` Variant: d | a + b and d | b imply d | a. `}
def nat_divides_add_cancel_right (d a b : Nat) (hab : NatDivides d (add a b)) (hb : NatDivides d b) : NatDivides d a
  ≔ nat_divides_add_cancel d b a
      (transport Nat (NatDivides d) (add a b) (add b a) (add_comm a b) hab) hb

def nat_divides_le_at (d k q : Nat) : Id Nat (suc. k) (mul q d) → Le d (suc. k)
  ≔ match q [
  | zero. ↦ p ↦ absurd (Le d (suc. k))
      (nat_encode (suc. k) zero. (concat Nat (suc. k) (mul zero. d) zero. p (mul_zero_left d)))
  | suc. q ↦ p ↦ transport Nat (x ↦ Le d x) (add d (mul q d)) (suc. k)
      (inverse Nat (suc. k) (add d (mul q d)) (calc
        (suc. k : Nat) = mul (suc. q) d by p
        = add (mul q d) d by mul_suc_left q d
        = add d (mul q d) by add_comm (mul q d) d ∎))
      (le_add_base d (mul q d)) ]

{` A divisor of a positive number is at most that number. `}
def nat_divides_le (d k : Nat) (h : NatDivides d (suc. k)) : Le d (suc. k)
  ≔ mere_rec (Σ Nat (q ↦ Id Nat (suc. k) (mul q d))) (Le d (suc. k)) (le_prop d (suc. k))
      (u ↦ nat_divides_le_at d k (u .fst) (u .snd)) h

{` A divisor of a positive number is positive. `}
def nat_divides_positive (d k : Nat) (h : NatDivides d (suc. k)) : Lt zero. d
  ≔ match d [
  | zero. ↦ absurd (Lt zero. zero.) (nat_encode (suc. k) zero. (nat_zero_divides (suc. k) h))
  | suc. d ↦ star. ]

def nat_divides_antisym (d k : Nat) : NatDivides d k → NatDivides k d → Id Nat d k
  ≔ match d, k [
  | zero., zero. ↦ _ _ ↦ refl (zero. : Nat)
  | zero., suc. k ↦ h _ ↦ absurd (Id Nat zero. (suc. k)) (nat_encode (suc. k) zero. (nat_zero_divides (suc. k) h))
  | suc. d, zero. ↦ _ h ↦ absurd (Id Nat (suc. d) zero.) (nat_encode (suc. d) zero. (nat_zero_divides (suc. d) h))
  | suc. d, suc. k ↦ h1 h2 ↦ le_antisym (suc. d) (suc. k) (nat_divides_le (suc. d) k h1) (nat_divides_le (suc. k) d h2) ]

{` Divisibility is decidable for all d and k (d = 0 included). `}
def nat_divides_decidable_any (d k : Nat) : Decidable (NatDivides d k)
  ≔ match d [
  | zero. ↦ match nat_dec_eq k zero. [
    | inl. p ↦ inl. (nat_divides_intro zero. k zero. p)
    | inr. np ↦ inr. (h ↦ np (nat_zero_divides k h)) ]
  | suc. c ↦ let m : Nat ≔ suc. c in
      let w : DivisionResult k m ≔ euclidean_division k m (nat_positive_book c) in
      match nat_dec_eq (w .fst .snd) zero. [
      | inl. r0 ↦ inl. (nat_divides_intro m k (w .fst .fst)
          (concat Nat k (add (mul (w .fst .fst) m) (w .fst .snd)) (mul (w .fst .fst) m) (w .snd .snd)
            (refl (add (mul (w .fst .fst) m)) r0)))
      | inr. nr ↦ inr. (h ↦ nr (nat_divides_remainder_zero c k (w .fst .fst) (w .fst .snd) (w .snd .fst) (w .snd .snd) h)) ] ]

{` For a positive divisor the quotient is unique, so it can be extracted. `}
def nat_quotient_unique_prop (c k : Nat) : isProp (Σ Nat (q ↦ Id Nat k (mul q (suc. c))))
  ≔ u v ↦ subtype_equal Nat (q ↦ Id Nat k (mul q (suc. c))) (q ↦ nat_set k (mul q (suc. c))) u v
      (nat_mul_cancel_right c (u .fst) (v .fst)
        (concat Nat (mul (u .fst) (suc. c)) k (mul (v .fst) (suc. c)) (inverse Nat k (mul (u .fst) (suc. c)) (u .snd)) (v .snd)))

def nat_divides_witness (c k : Nat) (h : NatDivides (suc. c) k) : Σ Nat (q ↦ Id Nat k (mul q (suc. c)))
  ≔ mere_rec (Σ Nat (q ↦ Id Nat k (mul q (suc. c)))) (Σ Nat (q ↦ Id Nat k (mul q (suc. c))))
      (nat_quotient_unique_prop c k) (u ↦ u) h

{` a·m | b·m with m positive implies a | b. `}
def nat_divides_mul_cancel_right (c a b : Nat) (h : NatDivides (mul a (suc. c)) (mul b (suc. c))) : NatDivides a b
  ≔ mere_rec (Σ Nat (q ↦ Id Nat (mul b (suc. c)) (mul q (mul a (suc. c))))) (NatDivides a b) (nat_divides_prop a b)
      (u ↦ nat_divides_intro a b (u .fst)
        (nat_mul_cancel_right c b (mul (u .fst) a)
          (concat Nat (mul b (suc. c)) (mul (u .fst) (mul a (suc. c))) (mul (mul (u .fst) a) (suc. c)) (u .snd)
            (inverse Nat (mul (mul (u .fst) a) (suc. c)) (mul (u .fst) (mul a (suc. c))) (mul_assoc (u .fst) a (suc. c)))))) h

def nat_mul_cancel_positive (c x y : Nat) : Lt zero. c → Id Nat (mul x c) (mul y c) → Id Nat x y
  ≔ match c [
  | zero. ↦ hc _ ↦ match hc []
  | suc. c ↦ _ e ↦ nat_mul_cancel_right c x y e ]

def nat_divides_mul_cancel_positive (m a b : Nat) : Lt zero. m → NatDivides (mul a m) (mul b m) → NatDivides a b
  ≔ match m [
  | zero. ↦ hm _ ↦ match hm []
  | suc. c ↦ _ h ↦ nat_divides_mul_cancel_right c a b h ]

{` Powers. `}
def nat_power_one (b : Nat) : Id Nat (nat_power b (suc. zero.)) b ≔ mul_one_left b

def nat_power_add (b m n : Nat) : Id Nat (nat_power b (add m n)) (mul (nat_power b m) (nat_power b n))
  ≔ match n [
  | zero. ↦ inverse Nat (mul (nat_power b m) (suc. zero.)) (nat_power b m) (mul_one_right (nat_power b m))
  | suc. n ↦ calc
      nat_power b (add m (suc. n)) = mul (mul (nat_power b m) (nat_power b n)) b
        by refl ((x ↦ mul x b) : Nat → Nat) (nat_power_add b m n)
      = mul (nat_power b m) (mul (nat_power b n) b) by mul_assoc (nat_power b m) (nat_power b n) b ∎ ]

def nat_power_mul_divides (b i j : Nat) : NatDivides (nat_power b i) (nat_power b (add i j))
  ≔ nat_divides_intro (nat_power b i) (nat_power b (add i j)) (nat_power b j)
      (concat Nat (nat_power b (add i j)) (mul (nat_power b i) (nat_power b j)) (mul (nat_power b j) (nat_power b i))
        (nat_power_add b i j) (mul_comm (nat_power b i) (nat_power b j)))

def nat_power_le_divides (b i j : Nat) (h : Le i j) : NatDivides (nat_power b i) (nat_power b j)
  ≔ let w : BookLe i j ≔ le_to_book i j h in
    nat_divides_intro (nat_power b i) (nat_power b j) (nat_power b (w .fst))
      (concat Nat (nat_power b j) (nat_power b (add (w .fst) i)) (mul (nat_power b (w .fst)) (nat_power b i))
        (refl (nat_power b) (inverse Nat (add (w .fst) i) j (w .snd))) (nat_power_add b (w .fst) i))

def nat_mul_positive (a b : Nat) : Lt zero. a → Lt zero. b → Lt zero. (mul a b)
  ≔ match a, b [
  | zero., b ↦ ha _ ↦ match ha []
  | suc. a, zero. ↦ _ hb ↦ match hb []
  | suc. a, suc. b ↦ _ _ ↦ star. ]

def nat_power_positive (b e : Nat) (hb : Lt zero. b) : Lt zero. (nat_power b e)
  ≔ match e [
  | zero. ↦ star.
  | suc. e ↦ nat_mul_positive (nat_power b e) b (nat_power_positive b e hb) hb ]

{` Decisions read off as booleans (for litmus checks by computation). `}
def nat_decision_false_reflect (X : Type) (d : Decidable X) (e : Id Bool (decision_bool X d) false.) : X → Empty
  ≔ match d [ inl. _ ↦ absurd (X → Empty) (bool_encode true. false. e) | inr. n ↦ n ]

{` Litmus: 3 | 12, 0 | 0, not 2 | 13, not 0 | 5, all decided by computation. `}
def nat_divides_litmus_three_twelve
  : NatDivides (suc. (suc. (suc. zero.)))
      (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))))))
  ≔ let X : Type ≔ NatDivides (suc. (suc. (suc. zero.)))
      (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))))))) in
    decision_bool_reflect X (nat_divides_decidable_any (suc. (suc. (suc. zero.)))
      (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))))))))
      (refl (true. : Bool))

def nat_divides_litmus_zero_zero : NatDivides zero. zero.
  ≔ decision_bool_reflect (NatDivides zero. zero.) (nat_divides_decidable_any zero. zero.) (refl (true. : Bool))

def nat_divides_litmus_two_thirteen
  : NatDivides (suc. (suc. zero.))
      (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))))))) → Empty
  ≔ let X : Type ≔ NatDivides (suc. (suc. zero.))
      (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))))))) in
    nat_decision_false_reflect X (nat_divides_decidable_any (suc. (suc. zero.))
      (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))))))))
      (refl (false. : Bool))

def nat_divides_litmus_zero_five : NatDivides zero. (suc. (suc. (suc. (suc. (suc. zero.))))) → Empty
  ≔ nat_decision_false_reflect (NatDivides zero. (suc. (suc. (suc. (suc. (suc. zero.))))))
      (nat_divides_decidable_any zero. (suc. (suc. (suc. (suc. (suc. zero.))))))
      (refl (false. : Bool))

{` Litmus: 2^5 = 2^2 · 2^3 = 32 and 2^2 | 2^5. `}
def nat_power_litmus_add
  : Id Nat (mul (nat_power (suc. (suc. zero.)) (suc. (suc. zero.))) (nat_power (suc. (suc. zero.)) (suc. (suc. (suc. zero.)))))
      (nat_power (suc. (suc. zero.)) (suc. (suc. (suc. (suc. (suc. zero.))))))
  ≔ inverse Nat (nat_power (suc. (suc. zero.)) (add (suc. (suc. zero.)) (suc. (suc. (suc. zero.)))))
      (mul (nat_power (suc. (suc. zero.)) (suc. (suc. zero.))) (nat_power (suc. (suc. zero.)) (suc. (suc. (suc. zero.)))))
      (nat_power_add (suc. (suc. zero.)) (suc. (suc. zero.)) (suc. (suc. (suc. zero.))))
