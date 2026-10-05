export "825-cycle-power-orbits"
export "666-pullbacks"
export "83-degree-cover-monodromy"
export "243-k-cycle-supports"

{` Chapter 8 (congp.tex), ex:pullbackandgcd (line 355): the pullback of the
   a-fold and the b-fold coverings of the circle (the degree maps
   z ↦ z^a, w ↦ w^b of def:dgm-map, circle_degree_map) has exactly
   gcd(a,b) components, for a, b > 0:
     ‖S¹ ×_{S¹} S¹‖₀ ≃ ℤ/gcd(a,b)ℤ ≃ Fin (gcd(a,b)).
   Route: the pullback is the total space over the z-circle of the family
   z ↦ fib_{(-)^b}(z^a); its components are the orbits of its monodromy
   on the fiber over the base (con:cycset-connS1cover, module 60); that
   monodromy is transport along ap_{(-)^a}(loop), identified (along the
   boundary identification of the degree map, a free-loop path) with the
   a-th power of the monodromy of the b-fold covering, which is a cycle with
   periods bℤ (module 83); module 825 counts its orbits. The circle is an
   arbitrary CircleSignature C. `}

def CirclePowerPullback (C : CircleSignature) (a b : Nat) : Type
  ≔ TypePullback (C .carrier) (C .carrier) (C .carrier) (circle_degree_map C a) (circle_degree_map C b)

{` The fibers of the b-fold covering and their pullback along (-)^a. `}
def cpp_fam (C : CircleSignature) (b : Nat) (y : C .carrier) : Type
  ≔ BookFiber (C .carrier) (C .carrier) (circle_degree_map C b) y

def cpp_family (C : CircleSignature) (a b : Nat) (z : C .carrier) : Type
  ≔ cpp_fam C b (circle_degree_map C a z)

def cpp_total_equiv (C : CircleSignature) (a b : Nat)
  : Equiv (CirclePowerPullback C a b) (Σ (C .carrier) (cpp_family C a b))
  ≔ quasi_inverse_equiv (CirclePowerPullback C a b) (Σ (C .carrier) (cpp_family C a b))
      (t ↦ (t .fst .fst, (t .fst .snd, t .snd)))
      (s ↦ ((s .fst, s .snd .fst), s .snd .snd))
      (t ↦ refl t) (s ↦ refl s)

def cpp_set_trunc_equiv (A B : Type) (e : Equiv A B) : Equiv (SetTrunc A) (SetTrunc B)
  ≔ id_to_equiv (SetTrunc A) (SetTrunc B) (refl SetTrunc (ua A B e))

{` Orbits of transport along a free loop (y, ℓ) in the family of fibers. `}
def cpp_free_loop_orbits (C : CircleSignature) (b : Nat) (t : FreeLoop (C .carrier)) : Type
  ≔ OrbitQuotient (cpp_fam C b (t .fst))
      (transport_equiv (cpp_fam C b (t .fst)) (cpp_fam C b (t .fst)) (refl (cpp_fam C b) (t .snd)))

def cpp_power_loop (C : CircleSignature) (a : Nat) : Id (C .carrier) (C .base) (C .base)
  ≔ loop_power_nat (C .carrier) (C .base) (C .loop) a

def cpp_monodromy_power (C : CircleSignature) (a b : Nat) : Equiv (cpp_fam C b (C .base)) (cpp_fam C b (C .base))
  ≔ transport_equiv (cpp_fam C b (C .base)) (cpp_fam C b (C .base)) (refl (cpp_fam C b) (cpp_power_loop C a))

def cpp_orbits_transport (C : CircleSignature) (a b : Nat)
  : Equiv (OrbitQuotient (cpp_family C a b (C .base)) (family_monodromy C (cpp_family C a b)))
      (OrbitQuotient (cpp_fam C b (C .base)) (cpp_monodromy_power C a b))
  ≔ id_to_equiv (cpp_free_loop_orbits C b (circle_eval C (C .carrier) (circle_degree_map C a)))
      (cpp_free_loop_orbits C b (C .base, cpp_power_loop C a))
      (refl (cpp_free_loop_orbits C b) (circle_degree_boundary C a))

{` The b-fold covering as a cycle (module 83): its permutation is the
   monodromy of cpp_fam C b. `}
def cpp_cycle (C : CircleSignature) (b1 : Nat) : Cycles
  ≔ degree_cover_cycle C (suc. b1) (lt_to_book zero. (suc. b1) star.)

def cpp_cycle_monodromy (C : CircleSignature) (b1 : Nat)
  : Id (Equiv (cpp_fam C (suc. b1) (C .base)) (cpp_fam C (suc. b1) (C .base)))
      (family_monodromy C (cpp_fam C (suc. b1))) (cpp_cycle C b1 .fst .snd)
  ≔ equiv_path (cpp_fam C (suc. b1) (C .base)) (cpp_fam C (suc. b1) (C .base))
      (family_monodromy C (cpp_fam C (suc. b1))) (cpp_cycle C b1 .fst .snd)
      (refl (family_monodromy C (cpp_fam C (suc. b1)) .map))

def cpp_cycle_per (C : CircleSignature) (b1 : Nat) (n : Int)
  (h : PowerPeriod (cpp_fam C (suc. b1) (C .base)) (cpp_cycle C b1 .fst .snd) n) : Multiples (suc. b1) n .fst
  ≔ transport (Subtypes Int) (H ↦ H n .fst) (CyclePeriods (cpp_cycle C b1)) (Multiples (suc. b1))
      (degree_cover_periods C (suc. b1) (lt_to_book zero. (suc. b1) star.)) h

def cpp_cycle_rep (C : CircleSignature) (b1 : Nat) (n : Int) (h : Multiples (suc. b1) n .fst)
  : PowerPeriod (cpp_fam C (suc. b1) (C .base)) (cpp_cycle C b1 .fst .snd) n
  ≔ transport (Subtypes Int) (H ↦ H n .fst) (Multiples (suc. b1)) (CyclePeriods (cpp_cycle C b1))
      (inverse (Subtypes Int) (CyclePeriods (cpp_cycle C b1)) (Multiples (suc. b1))
        (degree_cover_periods C (suc. b1) (lt_to_book zero. (suc. b1) star.))) h

{` The monodromy of the pullback family is the a-th power of the cycle. `}
def cpp_power_winding (C : CircleSignature) (a : Nat) (n : Int)
  : Id Int (circle_winding C (loop_power (C .carrier) (C .base) (cpp_power_loop C a) n)) (int_mul n (pos. a))
  ≔ calc
      circle_winding C (loop_power (C .carrier) (C .base) (cpp_power_loop C a) n)
      = int_mul (circle_winding C (cpp_power_loop C a)) n by circle_winding_power_arbitrary C (cpp_power_loop C a) n
      = int_mul (pos. a) n by refl ((k ↦ int_mul k n) : Int → Int) (circle_winding_power C (pos. a))
      = int_mul n (pos. a) by int_mul_comm (pos. a) n ∎

def cpp_monodromy_power_he (C : CircleSignature) (a b1 : Nat) (n : Int) (y : cpp_fam C (suc. b1) (C .base))
  : Id (cpp_fam C (suc. b1) (C .base)) (permutation_power (cpp_fam C (suc. b1) (C .base)) (cpp_monodromy_power C a (suc. b1)) n y)
      (permutation_power (cpp_fam C (suc. b1) (C .base)) (cpp_cycle C b1 .fst .snd) (int_mul n (pos. a)) y)
  ≔ let F ≔ cpp_fam C (suc. b1) in
    let Y ≔ F (C .base) in
    let e ≔ cpp_monodromy_power C a (suc. b1) in
    let l ≔ cpp_power_loop C a in
    calc
      permutation_power Y e n y = transport (C .carrier) F (C .base) (C .base) (loop_power (C .carrier) (C .base) l n) y
        by inverse Y (transport (C .carrier) F (C .base) (C .base) (loop_power (C .carrier) (C .base) l n) y)
          (permutation_power Y e n y)
          (transport_loop_power (C .carrier) F (C .base) l (k ↦ permutation_power Y e k y)
            (k ↦ inverse Y (permutation_power Y e (int_succ k) y) (e .map (permutation_power Y e k y))
              (permutation_power_succ Y e k y)) n)
      = permutation_power Y (family_monodromy C F) (circle_winding C (loop_power (C .carrier) (C .base) l n)) y
        by family_transport_winding C F y (loop_power (C .carrier) (C .base) l n)
      = permutation_power Y (family_monodromy C F) (int_mul n (pos. a)) y
        by refl ((k ↦ permutation_power Y (family_monodromy C F) k y) : Int → Y) (cpp_power_winding C a n)
      = permutation_power Y (cpp_cycle C b1 .fst .snd) (int_mul n (pos. a)) y
        by refl ((mm ↦ permutation_power Y mm (int_mul n (pos. a)) y) : Equiv Y Y → Y) (cpp_cycle_monodromy C b1) ∎

{` ex:pullbackandgcd: ‖S¹ ×_{S¹} S¹‖₀ ≃ ℤ/gcd(a,b)ℤ for a = a1+1, b = b1+1. `}
def circle_power_pullback_components (C : CircleSignature) (a1 b1 : Nat)
  : Equiv (SetTrunc (CirclePowerPullback C (suc. a1) (suc. b1)))
      (SubgroupQuotient (Multiples (nat_gcd (suc. a1) (suc. b1))) (multiples_laws (nat_gcd (suc. a1) (suc. b1))))
  ≔ let a : Nat ≔ suc. a1 in let b : Nat ≔ suc. b1 in
    let R ≔ cpp_family C a b in
    let Y ≔ cpp_fam C b (C .base) in
    let D ≔ SubgroupQuotient (Multiples (nat_gcd a b)) (multiples_laws (nat_gcd a b)) in
    let c ≔ cpp_cycle C b1 in
    compose_equiv (SetTrunc (CirclePowerPullback C a b)) (SetTrunc (Σ (C .carrier) R)) D
      (cpp_set_trunc_equiv (CirclePowerPullback C a b) (Σ (C .carrier) R) (cpp_total_equiv C a b))
      (compose_equiv (SetTrunc (Σ (C .carrier) R)) (OrbitQuotient (R (C .base)) (family_monodromy C R)) D
        (circle_components_orbits_equiv C R)
        (compose_equiv (OrbitQuotient (R (C .base)) (family_monodromy C R)) (OrbitQuotient Y (cpp_monodromy_power C a b)) D
          (cpp_orbits_transport C a b)
          (canonical_inverse_equiv D (OrbitQuotient Y (cpp_monodromy_power C a b))
            (cycle_power_orbits_equiv Y (c .fst .fst .snd) (c .fst .snd) (c .snd)
              (degree_cover_base_point C b (lt_to_book zero. b star.)) a b
              (cpp_cycle_per C b1) (cpp_cycle_rep C b1) (cpp_monodromy_power C a b) (cpp_monodromy_power_he C a b1)))))

{` ℤ/nℤ ≃ Fin n for n > 0 (via the cycle classification: both are cycles
   with periods nℤ). `}
def cpp_multiples_quotient_remainder (n : Nat)
  : Equiv (SubgroupQuotient (Multiples (suc. n)) (multiples_laws (suc. n))) (Remainder (suc. n))
  ≔ let H ≔ Multiples (suc. n) in
    let p ≔ cycle_path_from_periods (subgroup_cycle H (multiples_laws (suc. n))) (finite_standard_cycle n)
      (concat (Subtypes Int) (CyclePeriods (subgroup_cycle H (multiples_laws (suc. n)))) H
        (CyclePeriods (finite_standard_cycle n))
        (subgroup_cycle_periods H (multiples_laws (suc. n)))
        (inverse (Subtypes Int) (CyclePeriods (finite_standard_cycle n)) H (finite_standard_periods n)))
      (subgroup_class H (multiples_laws (suc. n)) int_zero) (remainder_at n zero. star.) in
    id_to_equiv (SubgroupQuotient H (multiples_laws (suc. n))) (Remainder (suc. n))
      (refl ((c ↦ c .fst .fst .fst) : Cycles → Type) p)

def cpp_multiples_quotient_fin (n : Nat)
  : Equiv (SubgroupQuotient (Multiples (suc. n)) (multiples_laws (suc. n))) (Fin (suc. n))
  ≔ compose_equiv (SubgroupQuotient (Multiples (suc. n)) (multiples_laws (suc. n))) (Remainder (suc. n)) (Fin (suc. n))
      (cpp_multiples_quotient_remainder n)
      (canonical_inverse_equiv (Fin (suc. n)) (Remainder (suc. n)) (fin_book_below_equiv (suc. n)))

{` gcd(a,b) > 0 for a > 0. `}
def cpp_divisor_positive (a1 : Nat) : (d : Nat) → NatDivides d (suc. a1) → Σ Nat (n ↦ Id Nat d (suc. n))
  ≔ d ↦ match d [
  | zero. ↦ h ↦ mere_rec (Σ Nat (q ↦ Id Nat (suc. a1) (mul q zero.))) (Σ Nat (n ↦ Id Nat zero. (suc. n)))
      (u v ↦ absurd (Id (Σ Nat (n ↦ Id Nat zero. (suc. n))) u v) (pbg_suc_ne_zero (u .fst)
        (inverse Nat zero. (suc. (u .fst)) (u .snd))))
      (t ↦ absurd (Σ Nat (n ↦ Id Nat zero. (suc. n))) (pbg_suc_ne_zero a1 (t .snd))) h
  | suc. n ↦ _ ↦ (n, refl (suc. n : Nat)) ]

def cpp_gcd_positive (a1 b1 : Nat) : Σ Nat (n ↦ Id Nat (nat_gcd (suc. a1) (suc. b1)) (suc. n))
  ≔ cpp_divisor_positive a1 (nat_gcd (suc. a1) (suc. b1)) (nat_gcd_divides_left (suc. a1) (suc. b1))

def cpp_multiples_quotient_fin_any (d n : Nat) (p : Id Nat d (suc. n))
  : Equiv (SubgroupQuotient (Multiples d) (multiples_laws d)) (Fin d)
  ≔ compose_equiv (SubgroupQuotient (Multiples d) (multiples_laws d))
      (SubgroupQuotient (Multiples (suc. n)) (multiples_laws (suc. n))) (Fin d)
      (id_to_equiv (SubgroupQuotient (Multiples d) (multiples_laws d))
        (SubgroupQuotient (Multiples (suc. n)) (multiples_laws (suc. n)))
        (refl ((k ↦ SubgroupQuotient (Multiples k) (multiples_laws k)) : Nat → Type) p))
      (compose_equiv (SubgroupQuotient (Multiples (suc. n)) (multiples_laws (suc. n))) (Fin (suc. n)) (Fin d)
        (cpp_multiples_quotient_fin n)
        (id_to_equiv (Fin (suc. n)) (Fin d) (refl Fin (inverse Nat d (suc. n) p))))

{` ex:pullbackandgcd, counting form: the pullback has exactly gcd(a,b)
   components. `}
def circle_power_pullback_components_fin (C : CircleSignature) (a1 b1 : Nat)
  : Equiv (SetTrunc (CirclePowerPullback C (suc. a1) (suc. b1))) (Fin (nat_gcd (suc. a1) (suc. b1)))
  ≔ compose_equiv (SetTrunc (CirclePowerPullback C (suc. a1) (suc. b1)))
      (SubgroupQuotient (Multiples (nat_gcd (suc. a1) (suc. b1))) (multiples_laws (nat_gcd (suc. a1) (suc. b1))))
      (Fin (nat_gcd (suc. a1) (suc. b1)))
      (circle_power_pullback_components C a1 b1)
      (cpp_multiples_quotient_fin_any (nat_gcd (suc. a1) (suc. b1)) (cpp_gcd_positive a1 b1 .fst)
        (cpp_gcd_positive a1 b1 .snd))
