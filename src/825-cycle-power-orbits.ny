export "148-order-gcd-lcm"
export "140-root-fibers"

{` Chapter 8 (congp.tex), ex:pullbackandgcd (line 355), the arithmetic
   core: for a cycle (Y, m) whose periods are bℤ, an automorphism e of Y
   acting as m^a (e^n = m^{na} pointwise) has exactly gcd(a,b) orbits:
   Y/e ≃ ℤ/gcd(a,b)ℤ, k ↦ [m^k(y0)]. The proof uses
   aℤ + bℤ = gcd(a,b)ℤ (nat_gcd_sum, module 148). `}

def pbg_suc_ne_zero (l : Nat) (p : Id Nat (suc. l) zero.) : Empty
  ≔ transport Nat (n ↦ match n [ zero. ↦ Empty | suc. _ ↦ Unit ]) (suc. l) zero. p star.

def pbg_one_not_zero (p : Id Int (pos. (suc. zero.)) (pos. zero.)) : Empty
  ≔ transport Int (z ↦ match z [ pos. k ↦ match k [ zero. ↦ Empty | suc. _ ↦ Unit ] | neg. _ ↦ Unit ])
      (pos. (suc. zero.)) (pos. zero.) p star.

{` Points of the orbit of y0: m^x(y0) = m^y(y0) iff x − y ∈ bℤ. `}
def cpo_point (Y : Type) (m : Equiv Y Y) (y0 : Y) (k : Int) : Y ≔ permutation_power Y m k y0

def cpo_points_equal_period (Y : Type) (hY : isSet Y) (m : Equiv Y Y) (cyc : Cyclic Y m) (y0 : Y) (b : Nat)
  (per : (n : Int) → PowerPeriod Y m n → Multiples b n .fst) (x y : Int)
  (h : Id Y (cpo_point Y m y0 x) (cpo_point Y m y0 y)) : Multiples b (int_sub x y) .fst
  ≔ per (int_sub x y) (cycle_period_from_point Y hY m cyc y0 (int_sub x y) (calc
      permutation_power Y m (int_sub x y) y0
      = permutation_power Y m (int_neg y) (permutation_power Y m x y0) by permutation_power_add Y m x (int_neg y) y0
      = permutation_power Y m (int_neg y) (permutation_power Y m y y0) by refl (permutation_power Y m (int_neg y)) h
      = y0 by permutation_power_inverse Y m y y0 ∎))

def cpo_period_points_equal (Y : Type) (m : Equiv Y Y) (y0 : Y) (b : Nat)
  (rep : (n : Int) → Multiples b n .fst → PowerPeriod Y m n) (x y : Int)
  (h : Multiples b (int_sub x y) .fst) : Id Y (cpo_point Y m y0 x) (cpo_point Y m y0 y)
  ≔ calc
      permutation_power Y m x y0 = permutation_power Y m (int_add (int_sub x y) y) y0
        by refl ((k ↦ permutation_power Y m k y0) : Int → Y) (inverse Int (int_add (int_sub x y) y) x (int_sub_add x y))
      = permutation_power Y m y (permutation_power Y m (int_sub x y) y0) by permutation_power_add Y m (int_sub x y) y y0
      = permutation_power Y m y y0 by refl (permutation_power Y m y) (rep (int_sub x y) h (refl y0)) ∎

{` e^n(m^k y0) = m^{k + na}(y0). `}
def cpo_e_power_point (Y : Type) (m e : Equiv Y Y) (y0 : Y) (a : Nat)
  (he : (n : Int) (y : Y) → Id Y (permutation_power Y e n y) (permutation_power Y m (int_mul n (pos. a)) y)) (k n : Int)
  : Id Y (permutation_power Y e n (cpo_point Y m y0 k)) (cpo_point Y m y0 (int_add k (int_mul n (pos. a))))
  ≔ concat Y (permutation_power Y e n (cpo_point Y m y0 k))
      (permutation_power Y m (int_mul n (pos. a)) (permutation_power Y m k y0))
      (cpo_point Y m y0 (int_add k (int_mul n (pos. a))))
      (he n (cpo_point Y m y0 k))
      (inverse Y (permutation_power Y m (int_add k (int_mul n (pos. a))) y0)
        (permutation_power Y m (int_mul n (pos. a)) (permutation_power Y m k y0))
        (permutation_power_add Y m k (int_mul n (pos. a)) y0))

{` The arithmetic: k − l ∈ aℤ + bℤ iff (k + na) − l ∈ bℤ for some n. `}
def cpo_sum_to_shift (a b : Nat) (k l : Int) (h : SubgroupSum (Multiples a) (Multiples b) (int_sub k l) .fst)
  : Mere (Σ Int (n ↦ Multiples b (int_sub (int_add k (int_mul n (pos. a))) l) .fst))
  ≔ let T ≔ Σ Int (n ↦ Multiples b (int_sub (int_add k (int_mul n (pos. a))) l) .fst) in
    mere_rec (SubgroupSumWitness (Multiples a) (Multiples b) (int_sub k l)) (Mere T) (mere_isprop T)
      (w ↦ mere_rec (MultipleWitness a (w .fst)) (Mere T) (mere_isprop T)
        (iw ↦
          let u ≔ w .fst in
          let v ≔ w .snd .fst in
          let i ≔ iw .fst in
          mere T (int_neg i,
            transport Int (z ↦ Multiples b z .fst) v (int_sub (int_add k (int_mul (int_neg i) (pos. a))) l)
              (inverse Int (int_sub (int_add k (int_mul (int_neg i) (pos. a))) l) v (calc
                int_add (int_add k (int_mul (int_neg i) (pos. a))) (int_neg l)
                = int_add (int_add k (int_neg l)) (int_mul (int_neg i) (pos. a))
                  by int_add_right_swap k (int_mul (int_neg i) (pos. a)) (int_neg l)
                = int_add (int_add u v) (int_neg u)
                  by refl int_add (w .snd .snd .snd)
                    (concat Int (int_mul (int_neg i) (pos. a)) (int_neg (int_mul i (pos. a))) (int_neg u)
                      (int_mul_neg_left_pos i a)
                      (refl int_neg (inverse Int u (int_mul i (pos. a)) (iw .snd))))
                = int_add (int_add u (int_neg u)) v by int_add_right_swap u v (int_neg u)
                = int_add int_zero v by refl ((z ↦ int_add z v) : Int → Int) (int_add_neg_right u)
                = v by int_add_zero_left v ∎))
              (w .snd .snd .fst .snd)))
        (w .snd .snd .fst .fst))
      h

def cpo_shift_to_sum (a b : Nat) (k l n : Int) (h : Multiples b (int_sub (int_add k (int_mul n (pos. a))) l) .fst)
  : SubgroupSum (Multiples a) (Multiples b) (int_sub k l) .fst
  ≔ let na ≔ int_mul n (pos. a) in
    let v ≔ int_sub (int_add k na) l in
    mere (SubgroupSumWitness (Multiples a) (Multiples b) (int_sub k l))
      (int_neg na, (v,
        ((mere (MultipleWitness a (int_neg na)) (int_neg n, inverse Int (int_mul (int_neg n) (pos. a)) (int_neg na)
            (int_mul_neg_left_pos n a)), h),
         calc
           int_sub k l = int_sub (int_add (int_sub k l) na) na by inverse Int (int_sub (int_add (int_sub k l) na) na) (int_sub k l)
             (int_add_sub (int_sub k l) na)
           = int_add v (int_neg na)
             by refl ((z ↦ int_add z (int_neg na)) : Int → Int)
               (inverse Int (int_add (int_add k na) (int_neg l)) (int_add (int_add k (int_neg l)) na)
                 (int_add_right_swap k na (int_neg l)))
           = int_add (int_neg na) v by int_add_comm v (int_neg na) ∎)))

{` The orbit quotient. `}
def cpo_class (Y : Type) (m e : Equiv Y Y) (y0 : Y) (k : Int) : OrbitQuotient Y e
  ≔ quotient_class Y (orbit_relation Y e) (cpo_point Y m y0 k)

def cpo_gcd_relation (a b : Nat) : EquivalenceRelation Int
  ≔ subgroup_relation (Multiples (nat_gcd a b)) (multiples_laws (nat_gcd a b))

def cpo_gcd_to_sum (a b : Nat) (z : Int) (h : Multiples (nat_gcd a b) z .fst)
  : SubgroupSum (Multiples a) (Multiples b) z .fst
  ≔ transport (Subtypes Int) (H ↦ H z .fst) (Multiples (nat_gcd a b)) (SubgroupSum (Multiples a) (Multiples b))
      (inverse (Subtypes Int) (SubgroupSum (Multiples a) (Multiples b)) (Multiples (nat_gcd a b)) (nat_gcd_sum a b)) h

def cpo_sum_to_gcd (a b : Nat) (z : Int) (h : SubgroupSum (Multiples a) (Multiples b) z .fst)
  : Multiples (nat_gcd a b) z .fst
  ≔ transport (Subtypes Int) (H ↦ H z .fst) (SubgroupSum (Multiples a) (Multiples b)) (Multiples (nat_gcd a b))
      (nat_gcd_sum a b) h

def cpo_class_respects (Y : Type) (m e : Equiv Y Y) (y0 : Y) (a b : Nat)
  (rep : (n : Int) → Multiples b n .fst → PowerPeriod Y m n)
  (he : (n : Int) (y : Y) → Id Y (permutation_power Y e n y) (permutation_power Y m (int_mul n (pos. a)) y))
  : Respects Int (OrbitQuotient Y e) (cpo_gcd_relation a b) (cpo_class Y m e y0)
  ≔ k l r ↦ quotient_encode Y (orbit_relation Y e) (cpo_point Y m y0 k) (cpo_point Y m y0 l)
      (mere_rec (Σ Int (n ↦ Multiples b (int_sub (int_add k (int_mul n (pos. a))) l) .fst))
        (SameOrbit Y e (cpo_point Y m y0 k) (cpo_point Y m y0 l)) (same_orbit_prop Y e (cpo_point Y m y0 k) (cpo_point Y m y0 l))
        (t ↦ mere (OrbitWitness Y e (cpo_point Y m y0 k) (cpo_point Y m y0 l)) (t .fst,
          inverse Y (permutation_power Y e (t .fst) (cpo_point Y m y0 k)) (cpo_point Y m y0 l)
            (concat Y (permutation_power Y e (t .fst) (cpo_point Y m y0 k))
              (cpo_point Y m y0 (int_add k (int_mul (t .fst) (pos. a)))) (cpo_point Y m y0 l)
              (cpo_e_power_point Y m e y0 a he k (t .fst))
              (cpo_period_points_equal Y m y0 b rep (int_add k (int_mul (t .fst) (pos. a))) l (t .snd)))))
        (cpo_sum_to_shift a b k l (cpo_gcd_to_sum a b (int_sub k l) r)))

def cpo_class_reflects (Y : Type) (hY : isSet Y) (m e : Equiv Y Y) (cyc : Cyclic Y m) (y0 : Y) (a b : Nat)
  (per : (n : Int) → PowerPeriod Y m n → Multiples b n .fst)
  (he : (n : Int) (y : Y) → Id Y (permutation_power Y e n y) (permutation_power Y m (int_mul n (pos. a)) y))
  (k l : Int) (p : Id (OrbitQuotient Y e) (cpo_class Y m e y0 k) (cpo_class Y m e y0 l))
  : Rel Int (cpo_gcd_relation a b) k l
  ≔ mere_rec (OrbitWitness Y e (cpo_point Y m y0 k) (cpo_point Y m y0 l))
      (Multiples (nat_gcd a b) (int_sub k l) .fst) (Multiples (nat_gcd a b) (int_sub k l) .snd)
      (w ↦ cpo_sum_to_gcd a b (int_sub k l)
        (cpo_shift_to_sum a b k l (w .fst)
          (cpo_points_equal_period Y hY m cyc y0 b per (int_add k (int_mul (w .fst) (pos. a))) l
            (inverse Y (cpo_point Y m y0 l) (cpo_point Y m y0 (int_add k (int_mul (w .fst) (pos. a))))
              (concat Y (cpo_point Y m y0 l) (permutation_power Y e (w .fst) (cpo_point Y m y0 k))
                (cpo_point Y m y0 (int_add k (int_mul (w .fst) (pos. a))))
                (w .snd) (cpo_e_power_point Y m e y0 a he k (w .fst)))))))
      (quotient_effective Y (orbit_relation Y e) (cpo_point Y m y0 k) (cpo_point Y m y0 l) .map p)

def cpo_class_surjective (Y : Type) (m e : Equiv Y Y) (cyc : Cyclic Y m) (y0 : Y)
  : Surjective Int (OrbitQuotient Y e) (cpo_class Y m e y0)
  ≔ c ↦ mere_rec (BookFiber Y (OrbitQuotient Y e) (quotient_class Y (orbit_relation Y e)) c)
      (Mere (BookFiber Int (OrbitQuotient Y e) (cpo_class Y m e y0) c))
      (mere_isprop (BookFiber Int (OrbitQuotient Y e) (cpo_class Y m e y0) c))
      (u ↦ mere_rec (OrbitWitness Y m y0 (u .fst))
        (Mere (BookFiber Int (OrbitQuotient Y e) (cpo_class Y m e y0) c))
        (mere_isprop (BookFiber Int (OrbitQuotient Y e) (cpo_class Y m e y0) c))
        (w ↦ mere (BookFiber Int (OrbitQuotient Y e) (cpo_class Y m e y0) c)
          (w .fst, concat (OrbitQuotient Y e) c (quotient_class Y (orbit_relation Y e) (u .fst)) (cpo_class Y m e y0 (w .fst))
            (u .snd) (refl (quotient_class Y (orbit_relation Y e)) (w .snd))))
        (cyc .snd y0 (u .fst)))
      (quotient_surjective Y (orbit_relation Y e) c)

{` The orbits of e = "m^a" on a cycle with periods bℤ form ℤ/gcd(a,b)ℤ. `}
def cycle_power_orbits_equiv (Y : Type) (hY : isSet Y) (m : Equiv Y Y) (cyc : Cyclic Y m) (y0 : Y) (a b : Nat)
  (per : (n : Int) → PowerPeriod Y m n → Multiples b n .fst)
  (rep : (n : Int) → Multiples b n .fst → PowerPeriod Y m n)
  (e : Equiv Y Y)
  (he : (n : Int) (y : Y) → Id Y (permutation_power Y e n y) (permutation_power Y m (int_mul n (pos. a)) y))
  : Equiv (SubgroupQuotient (Multiples (nat_gcd a b)) (multiples_laws (nat_gcd a b))) (OrbitQuotient Y e)
  ≔ quotient_presentation_equiv Int (OrbitQuotient Y e) (cpo_gcd_relation a b) (quotient_set Y (orbit_relation Y e))
      (cpo_class Y m e y0) (cpo_class_respects Y m e y0 a b rep he)
      (cpo_class_reflects Y hY m e cyc y0 a b per he) (cpo_class_surjective Y m e cyc y0)
