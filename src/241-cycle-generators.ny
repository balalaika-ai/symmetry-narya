export "240-permutation-orbit-decomposition"

def iterate_orbit (A : Type) (e : Equiv A A) (g : A → A) (step : (v : A) → SameOrbit A e v (g v)) (k : Nat) (x : A)
  : SameOrbit A e x (iterate A g k x)
  ≔ match k [
  | zero. ↦ same_orbit_refl A e x
  | suc. k ↦ same_orbit_trans A e x (iterate A g k x) (g (iterate A g k x))
      (iterate_orbit A e g step k x) (step (iterate A g k x)) ]

{` If every f-step stays in an e-orbit, so do all integer powers of f. `}
def orbit_steps_closed (A : Type) (e f : Equiv A A) (step : (v : A) → SameOrbit A e v (f .map v)) (z : Int) (x : A)
  : SameOrbit A e x (permutation_power A f z x)
  ≔ let back ≔ ((v ↦ same_orbit_sym A e (equiv_inverse_map A A f v) v
        (refl (SameOrbit A e (equiv_inverse_map A A f v)) (equiv_counit A A f v)
          .trr (step (equiv_inverse_map A A f v))))
      : (v : A) → SameOrbit A e v (equiv_inverse_map A A f v)) in
    match z [
  | pos. k ↦ iterate_orbit A e (f .map) step k x
  | neg. k ↦ iterate_orbit A e (equiv_inverse_map A A f) back (suc. k) x ]

{` rem:thenonuniquenessofgeneratorsofmodulararithmetic1: generators of a
   cycle (A,e) are automorphisms g commuting with e for which (A,g) is a cycle. `}
def CycleGenerators (A : Type) (e : Equiv A A) : Type
  ≔ Σ (Equiv A A) (g ↦ Product (Commutes A A e e (g .map)) (Cyclic A g))

def cycle_generators_prop (A : Type) (hA : isSet A) (e : Equiv A A) (g : Equiv A A)
  : isProp (Product (Commutes A A e e (g .map)) (Cyclic A g))
  ≔ product_prop (Commutes A A e e (g .map)) (Cyclic A g) (commutes_prop A A hA e e (g .map)) (cyclic_prop A g)

{` "Its inverse would give the same result", for any cycle, including (Z, s). `}
def inverse_cyclic (A : Type) (e : Equiv A A) (c : Cyclic A e) : Cyclic A (canonical_inverse_equiv A A e)
  ≔ let e' ≔ canonical_inverse_equiv A A e in
    let step ≔ ((v ↦ same_orbit_sym A e' (e .map v) v
        (mere (OrbitWitness A e' (e .map v) v) (pos. (suc. zero.),
          inverse A (equiv_inverse_map A A e (e .map v)) v (equiv_retraction A A e v))))
      : (v : A) → SameOrbit A e' v (e .map v)) in
    (c .fst, x y ↦ mere_rec (OrbitWitness A e x y) (SameOrbit A e' x y) (same_orbit_prop A e' x y)
      (w ↦ refl (SameOrbit A e' x) (inverse A y (permutation_power A e (w .fst) x) (w .snd))
        .trr (orbit_steps_closed A e' e step (w .fst) x))
      (c .snd x y))

def inverse_generator (A : Type) (e : Equiv A A) (c : Cyclic A e) : CycleGenerators A e
  ≔ (canonical_inverse_equiv A A e,
     (x ↦ concat A (equiv_inverse_map A A e (e .map x)) x (e .map (equiv_inverse_map A A e x))
        (equiv_retraction A A e x) (inverse A (e .map (equiv_inverse_map A A e x)) x (equiv_counit A A e x)),
      inverse_cyclic A e c))

def integer_inverse_generator : CycleGenerators Int int_succ_equiv
  ≔ inverse_generator Int int_succ_equiv integer_successor_cyclic

{` Arithmetic on natural numbers used below. `}
def nat_add_zero_right_part (a b : Nat) : Id Nat (add a b) zero. → Id Nat a zero.
  ≔ match b [
  | zero. ↦ p ↦ p
  | suc. b ↦ p ↦ absurd (Id Nat a zero.) (nat_encode (suc. (add a b)) zero. p) ]

def nat_mul_suc_zero (q g : Nat) : Id Nat (mul (suc. q) g) zero. → Id Nat g zero.
  ≔ match g [
  | zero. ↦ p ↦ refl (zero. : Nat)
  | suc. g ↦ p ↦ absurd (Id Nat (suc. g) zero.) (nat_encode (suc. (add (mul (suc. q) g) q)) zero. p) ]

def nat_mul_one_factor (q g : Nat) : Id Nat (suc. zero.) (mul q g) → Id Nat g (suc. zero.)
  ≔ match g [
  | zero. ↦ p ↦ absurd (Id Nat zero. (suc. zero.)) (nat_encode (suc. zero.) zero. p)
  | suc. g ↦ match q [
    | zero. ↦ p ↦ absurd (Id Nat (suc. g) (suc. zero.))
        (nat_encode (suc. zero.) zero. (concat Nat (suc. zero.) (mul zero. (suc. g)) zero. p (mul_zero_left (suc. g))))
    | suc. q ↦ p ↦ refl ((k ↦ suc. k) : Nat → Nat)
        (nat_mul_suc_zero q g (nat_add_zero_right_part (mul (suc. q) g) q
          (inverse Nat zero. (add (mul (suc. q) g) q) (refl nat_pred p)))) ] ]

def nat_divides_one (g : Nat) (h : NatDivides g (suc. zero.)) : Id Nat g (suc. zero.)
  ≔ mere_rec (Σ Nat (q ↦ Id Nat (suc. zero.) (mul q g))) (Id Nat g (suc. zero.)) (nat_set g (suc. zero.))
      (v ↦ nat_mul_one_factor (v .fst) g (v .snd)) h

{` For the standard cycle (Z/m, s) with m = suc n: s^r is a cycle iff gcd(r,m) = 1. `}
def coprime_power_cyclic (n r : Nat) (h : Id Nat (nat_gcd r (suc. n)) (suc. zero.))
  : Cyclic (Remainder (suc. n)) (permutation_power_equiv (Remainder (suc. n)) (modular_successor_equiv n) (pos. r))
  ≔ let R ≔ Remainder (suc. n) in let S ≔ modular_successor_equiv n in
    let G ≔ permutation_power_equiv R S (pos. r) in
    let Sum ≔ SubgroupSum (Multiples r) (Multiples (suc. n)) in
    let one_sum ≔ transport (Subtypes Int) (H ↦ H (pos. (suc. zero.)) .fst) (Multiples (nat_gcd r (suc. n))) Sum
      (inverse (Subtypes Int) Sum (Multiples (nat_gcd r (suc. n))) (nat_gcd_sum r (suc. n)))
      (transport Nat (k ↦ Multiples k (pos. (suc. zero.)) .fst) (suc. zero.) (nat_gcd r (suc. n))
        (inverse Nat (nat_gcd r (suc. n)) (suc. zero.) h) (self_multiple (suc. zero.))) in
    (mere R (remainder_at n zero. star.),
     x y ↦ mere_rec (SubgroupSumWitness (Multiples r) (Multiples (suc. n)) (pos. (suc. zero.))) (SameOrbit R G x y)
       (same_orbit_prop R G x y)
       (w ↦ let a ≔ w .fst in let b ≔ w .snd .fst in
         mere_rec (MultipleWitness r a) (SameOrbit R G x y) (same_orbit_prop R G x y)
           (u ↦ mere_rec (MultipleWitness (suc. n) b) (SameOrbit R G x y) (same_orbit_prop R G x y)
             (v ↦
               let E ≔ permutation_power_equiv R G (u .fst) in
               let pointwise ≔ ((t ↦ calc
                   S .map t = permutation_power R S (int_add a b) t
                     by refl ((k ↦ permutation_power R S k t) : Int → R) (w .snd .snd .snd)
                   = permutation_power R S b (permutation_power R S a t) by permutation_power_add R S a b t
                   = permutation_power R S a t
                     by happly R (_ ↦ R) (permutation_power R S b) (identity R)
                       (standard_multiple_period n b v) (permutation_power R S a t)
                   = permutation_power R S (int_mul (u .fst) (pos. r)) t
                     by refl ((k ↦ permutation_power R S k t) : Int → R) (u .snd)
                   = permutation_power R S (int_mul (pos. r) (u .fst)) t
                     by refl ((k ↦ permutation_power R S k t) : Int → R) (int_mul_comm (u .fst) (pos. r))
                   = E .map t by permutation_power_scaled R S r (u .fst) t ∎)
                 : (t : R) → Id R (S .map t) (E .map t)) in
               mere_rec (OrbitWitness R S x y) (SameOrbit R G x y) (same_orbit_prop R G x y)
                 (o ↦ refl (SameOrbit R G x)
                   (inverse R y (permutation_power R E (o .fst) x)
                     (concat R y (permutation_power R S (o .fst) x) (permutation_power R E (o .fst) x) (o .snd)
                       (permutation_power_intertwine R R S E (t ↦ t) pointwise (o .fst) x)))
                   .trr (orbit_steps_closed R G E (t ↦ orbit_power R G t (u .fst)) (o .fst) x))
                 (modular_successor_cyclic n .snd x y))
             (w .snd .snd .fst .snd))
           (w .snd .snd .fst .fst))
       one_sum)

def power_cyclic_coprime (n r : Nat)
  (c : Cyclic (Remainder (suc. n)) (permutation_power_equiv (Remainder (suc. n)) (modular_successor_equiv n) (pos. r)))
  : Id Nat (nat_gcd r (suc. n)) (suc. zero.)
  ≔ let R ≔ Remainder (suc. n) in let S ≔ modular_successor_equiv n in
    let G ≔ permutation_power_equiv R S (pos. r) in
    let x0 ≔ remainder_at n zero. star. in
    let g ≔ nat_gcd r (suc. n) in
    let Sum ≔ SubgroupSum (Multiples r) (Multiples (suc. n)) in
    mere_rec (OrbitWitness R G x0 (S .map x0)) (Id Nat g (suc. zero.)) (nat_set g (suc. zero.))
      (w ↦ let t ≔ w .fst in
        let rt ≔ int_mul (pos. r) t in
        let meet ≔ concat R (permutation_power R S rt x0) (permutation_power R G t x0) (S .map x0)
          (permutation_power_scaled R S r t x0) (inverse R (S .map x0) (permutation_power R G t x0) (w .snd)) in
        let period ≔ cycle_period_from_point R (remainder_set (suc. n)) S (modular_successor_cyclic n) x0
          (int_sub rt (pos. (suc. zero.)))
          (power_equality_difference R S rt (pos. (suc. zero.)) x0 meet) in
        mere_rec (MultipleWitness (suc. n) (int_sub rt (pos. (suc. zero.)))) (Id Nat g (suc. zero.)) (nat_set g (suc. zero.))
          (v ↦ let q ≔ v .fst in let qm ≔ int_mul q (pos. (suc. n)) in
            let rt_eq ≔ calc
              rt = int_add (int_sub rt (pos. (suc. zero.))) (pos. (suc. zero.))
                by inverse Int (int_add (int_sub rt (pos. (suc. zero.))) (pos. (suc. zero.))) rt (int_sub_add rt (pos. (suc. zero.)))
              = int_add qm (pos. (suc. zero.)) by refl ((z ↦ int_add z (pos. (suc. zero.))) : Int → Int) (v .snd) ∎ in
            let one_eq ≔ calc
              (pos. (suc. zero.) : Int) = int_sub (int_add (pos. (suc. zero.)) qm) qm
                by inverse Int (int_sub (int_add (pos. (suc. zero.)) qm) qm) (pos. (suc. zero.)) (int_add_sub (pos. (suc. zero.)) qm)
              = int_sub (int_add qm (pos. (suc. zero.))) qm
                by refl ((z ↦ int_sub z qm) : Int → Int) (int_add_comm (pos. (suc. zero.)) qm)
              = int_sub rt qm by refl ((z ↦ int_sub z qm) : Int → Int) (inverse Int rt (int_add qm (pos. (suc. zero.))) rt_eq)
              = int_add (int_mul t (pos. r)) (int_neg qm)
                by refl ((z ↦ int_add z (int_neg qm)) : Int → Int) (int_mul_comm (pos. r) t)
              = int_add (int_mul t (pos. r)) (int_mul (int_neg q) (pos. (suc. n)))
                by refl (int_add (int_mul t (pos. r)))
                  (inverse Int (int_mul (int_neg q) (pos. (suc. n))) (int_neg qm) (int_mul_neg_left_pos q (suc. n))) ∎ in
            let in_sum : Sum (pos. (suc. zero.)) .fst
              ≔ mere (SubgroupSumWitness (Multiples r) (Multiples (suc. n)) (pos. (suc. zero.)))
                  (int_mul t (pos. r), (int_mul (int_neg q) (pos. (suc. n)),
                    ((multiple_of r t, multiple_of (suc. n) (int_neg q)), one_eq))) in
            nat_divides_one g
              (mere_rec (MultipleWitness g (pos. (suc. zero.))) (NatDivides g (suc. zero.)) (nat_divides_prop g (suc. zero.))
                (multiple_nat_divides g (suc. zero.))
                (transport (Subtypes Int) (H ↦ H (pos. (suc. zero.)) .fst) Sum (Multiples g) (nat_gcd_sum r (suc. n)) in_sum)))
          (standard_period_multiple n (int_sub rt (pos. (suc. zero.))) period))
      (c .snd x0 (S .map x0))

{` The residues r < m with gcd(r, m) = 1. `}
def CoprimeResidues (m : Nat) : Type ≔ Σ (Remainder m) (r ↦ Id Nat (nat_gcd (r .fst) m) (suc. zero.))

def standard_power_value (n : Nat) (r : Remainder (suc. n))
  : Id (Remainder (suc. n)) (permutation_power (Remainder (suc. n)) (modular_successor_equiv n) (pos. (r .fst)) (remainder_at n zero. star.)) r
  ≔ concat (Remainder (suc. n))
      (iterate (Remainder (suc. n)) (modular_successor n) (r .fst) (remainder_at n zero. star.))
      (remainder_at n (r .fst) (lt_from_book (r .fst) (suc. n) (r .snd))) r
      (modular_successor_iterate n (r .fst) (lt_from_book (r .fst) (suc. n) (r .snd)))
      (remainder_equal (suc. n) (remainder_at n (r .fst) (lt_from_book (r .fst) (suc. n) (r .snd))) r (refl (r .fst)))

def standard_power_map (n : Nat) (r : Nat)
  : PermutationMap (Remainder (suc. n)) (Remainder (suc. n)) (modular_successor_equiv n) (modular_successor_equiv n)
  ≔ (permutation_power (Remainder (suc. n)) (modular_successor_equiv n) (pos. r),
     x ↦ permutation_powers_commute (Remainder (suc. n)) (modular_successor_equiv n) (pos. r) (pos. (suc. zero.)) x)

{` A generator commuting with s is the power s^r with r = g(0). `}
def generator_is_power (n : Nat) (g : CycleGenerators (Remainder (suc. n)) (modular_successor_equiv n)) (y : Remainder (suc. n))
  : Id (Remainder (suc. n)) (g .fst .map y)
      (permutation_power (Remainder (suc. n)) (modular_successor_equiv n) (pos. (g .fst .map (remainder_at n zero. star.) .fst)) y)
  ≔ let R ≔ Remainder (suc. n) in let S ≔ modular_successor_equiv n in
    let x0 ≔ remainder_at n zero. star. in
    cycle_map_value_unique R R (remainder_set (suc. n)) S S (modular_successor_cyclic n)
      (g .fst .map, g .snd .fst) (standard_power_map n (g .fst .map x0 .fst)) x0
      (inverse R (permutation_power R S (pos. (g .fst .map x0 .fst)) x0) (g .fst .map x0) (standard_power_value n (g .fst .map x0))) y

def standard_cycle_generators_equiv (n : Nat)
  : Equiv (CycleGenerators (Remainder (suc. n)) (modular_successor_equiv n)) (CoprimeResidues (suc. n))
  ≔ let R ≔ Remainder (suc. n) in let S ≔ modular_successor_equiv n in
    let x0 ≔ remainder_at n zero. star. in
    let to ≔ ((g ↦ (g .fst .map x0,
        power_cyclic_coprime n (g .fst .map x0 .fst)
          (cyclic_transfer R R (g .fst) (permutation_power_equiv R S (pos. (g .fst .map x0 .fst))) (identity_equiv R)
            (generator_is_power n g) (g .snd .snd))))
      : CycleGenerators R S → CoprimeResidues (suc. n)) in
    let from ≔ ((u ↦ (permutation_power_equiv R S (pos. (u .fst .fst)),
        (standard_power_map n (u .fst .fst) .snd, coprime_power_cyclic n (u .fst .fst) (u .snd))))
      : CoprimeResidues (suc. n) → CycleGenerators R S) in
    quasi_inverse_equiv (CycleGenerators R S) (CoprimeResidues (suc. n)) to from
      (g ↦ subtype_equal (Equiv R R) (h ↦ Product (Commutes R R S S (h .map)) (Cyclic R h))
        (cycle_generators_prop R (remainder_set (suc. n)) S) (from (to g)) g
        (equiv_path R R (from (to g) .fst) (g .fst)
          (funext R (_ ↦ R) (from (to g) .fst .map) (g .fst .map)
            (y ↦ inverse R (g .fst .map y) (permutation_power R S (pos. (g .fst .map x0 .fst)) y) (generator_is_power n g y)))))
      (u ↦ subtype_equal R (r ↦ Id Nat (nat_gcd (r .fst) (suc. n)) (suc. zero.))
        (r ↦ nat_set (nat_gcd (r .fst) (suc. n)) (suc. zero.)) (to (from u)) u
        (standard_power_value n (u .fst)))

{` The printed count: for m ≥ 2, as many as positive integers below m coprime to m. `}
def PositiveCoprime (m : Nat) : Type
  ≔ Σ Nat (r ↦ Product (BookLt zero. r) (Product (BookLt r m) (Id Nat (nat_gcd r m) (suc. zero.))))

def coprime_positive (c r : Nat) : Id Nat (nat_gcd r (suc. (suc. c))) (suc. zero.) → BookLt zero. r
  ≔ match r [
  | zero. ↦ p ↦ absurd (BookLt zero. zero.) (nat_encode (suc. c) zero. (refl nat_pred p))
  | suc. r ↦ p ↦ lt_to_book zero. (suc. r) star. ]

def coprime_positive_equiv (c : Nat) : Equiv (CoprimeResidues (suc. (suc. c))) (PositiveCoprime (suc. (suc. c)))
  ≔ let m : Nat ≔ suc. (suc. c) in
    quasi_inverse_equiv (CoprimeResidues m) (PositiveCoprime m)
      (u ↦ (u .fst .fst, (coprime_positive c (u .fst .fst) (u .snd), (u .fst .snd, u .snd))))
      (v ↦ ((v .fst, v .snd .snd .fst), v .snd .snd .snd))
      (u ↦ refl u)
      (v ↦ (refl (v .fst), (book_lt_prop zero. (v .fst) (coprime_positive c (v .fst) (v .snd .snd .snd)) (v .snd .fst),
        (refl (v .snd .snd .fst), refl (v .snd .snd .snd)))))

def standard_generators_positive_coprime (c : Nat)
  : Equiv (CycleGenerators (Remainder (suc. (suc. c))) (modular_successor_equiv (suc. c))) (PositiveCoprime (suc. (suc. c)))
  ≔ compose_equiv (CycleGenerators (Remainder (suc. (suc. c))) (modular_successor_equiv (suc. c)))
      (CoprimeResidues (suc. (suc. c))) (PositiveCoprime (suc. (suc. c)))
      (standard_cycle_generators_equiv (suc. c)) (coprime_positive_equiv c)

{` The printed count fails for m = 1: the identity generates the 1-cycle,
   but there is no positive integer below 1. `}
def positive_below_one_empty (r : Nat) : BookLt zero. r → BookLt r (suc. zero.) → Empty
  ≔ match r [
  | zero. ↦ p q ↦ lt_from_book zero. zero. p
  | suc. r ↦ p q ↦ lt_from_book (suc. r) (suc. zero.) q ]

def positive_coprime_one_empty (v : PositiveCoprime (suc. zero.)) : Empty
  ≔ positive_below_one_empty (v .fst) (v .snd .fst) (v .snd .snd .fst)

def one_cycle_generator : CycleGenerators (Remainder (suc. zero.)) (modular_successor_equiv zero.)
  ≔ equiv_inverse_map (CycleGenerators (Remainder (suc. zero.)) (modular_successor_equiv zero.)) (CoprimeResidues (suc. zero.))
      (standard_cycle_generators_equiv zero.) (remainder_at zero. zero. star., refl (suc. zero. : Nat))
