export "147-principal-divisibility"

{` Chapter 10 (fingp.tex): arithmetic vocabulary used throughout the
   chapter. The book does not define primes or powers; these are the
   standard notions. Divisibility is NatDivides of module 147,
   d | k ⇔ ∃ q, k = q·d (a proposition). `}

{` Powers b^e, by recursion on the exponent: b^0 = 1, b^(e+1) = b^e · b. `}
def nat_power (b e : Nat) : Nat
  ≔ match e [ zero. ↦ suc. zero. | suc. e ↦ mul (nat_power b e) b ]

{` p is prime: 1 < p, and every divisor of p is 1 or p. `}
def NatIsPrime (p : Nat) : Type
  ≔ Product (Lt (suc. zero.) p)
      ((d : Nat) → NatDivides d p → Sum (Id Nat d (suc. zero.)) (Id Nat d p))

{` a and b are coprime: their only common divisor is 1. `}
def NatCoprime (a b : Nat) : Type
  ≔ (d : Nat) → NatDivides d a → NatDivides d b → Id Nat d (suc. zero.)

{` a ≡ b (mod p), as a proposition: one of a, b exceeds the other by a
   multiple of p. `}
def NatCongruent (p a b : Nat) : Type
  ≔ Mere (Σ Nat (k ↦ Sum (Id Nat a (add b (mul k p))) (Id Nat b (add a (mul k p)))))

def nat_congruent_prop (p a b : Nat) : isProp (NatCongruent p a b)
  ≔ mere_isprop (Σ Nat (k ↦ Sum (Id Nat a (add b (mul k p))) (Id Nat b (add a (mul k p)))))

def nat_coprime_prop (a b : Nat) : isProp (NatCoprime a b)
  ≔ pi_prop Nat (d ↦ NatDivides d a → NatDivides d b → Id Nat d (suc. zero.))
      (d ↦ pi_prop (NatDivides d a) (_ ↦ NatDivides d b → Id Nat d (suc. zero.))
        (_ ↦ pi_prop (NatDivides d b) (_ ↦ Id Nat d (suc. zero.)) (_ ↦ nat_set d (suc. zero.))))

{` Litmus: 2^3 = 8 and 3^2 = 9 by computation. `}
def nat_power_litmus_eight
  : Id Nat (nat_power (suc. (suc. zero.)) (suc. (suc. (suc. zero.))))
      (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))
  ≔ refl (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))) : Nat)

def nat_power_litmus_nine
  : Id Nat (nat_power (suc. (suc. (suc. zero.))) (suc. (suc. zero.)))
      (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))))
  ≔ refl (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))) : Nat)
