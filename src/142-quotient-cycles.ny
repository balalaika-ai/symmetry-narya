export "141-cycle-map-spaces"

def quotient_prop_induction (A : Type) (R : EquivalenceRelation A) (P : Quotient A R → Type)
  (hp : (z : Quotient A R) → isProp (P z)) (b : (a : A) → P (quotient_class A R a)) (z : Quotient A R) : P z
  ≔ mere_rec (BookFiber A (Quotient A R) (quotient_class A R) z) (P z) (hp z)
      (w ↦ transport (Quotient A R) P (quotient_class A R (w .fst)) z
        (inverse (Quotient A R) z (quotient_class A R (w .fst)) (w .snd)) (b (w .fst)))
      (quotient_surjective A R z)

def mod_power_commutes (n : Nat) (X : Type) (t : Equiv X X) (x : X)
  : Id X (t .map (mod_power n X t .map x)) (mod_power n X t .map (t .map x))
  ≔ iterate_commute X (t .map) (suc. zero.) (suc. n) x

{` A map commuting with t^m respects ~_m. `}
def mod_respects_commuting (n : Nat) (X : Type) (t : Equiv X X) (h : X → X)
  (step : (x : X) → Id X (h (mod_power n X t .map x)) (mod_power n X t .map (h x)))
  : Respects X (ModQuotient n X t) (mod_relation n X t) (x ↦ quotient_class X (mod_relation n X t) (h x))
  ≔ let R ≔ mod_relation n X t in let M ≔ mod_power n X t in
    x y o ↦ equiv_inverse_map (Id (ModQuotient n X t) (quotient_class X R (h x)) (quotient_class X R (h y)))
      (Rel X R (h x) (h y)) (quotient_effective X R (h x) (h y))
      (mere_rec (OrbitWitness X M x y) (SameOrbit X M (h x) (h y)) (same_orbit_prop X M (h x) (h y))
        (w ↦ mere (OrbitWitness X M (h x) (h y)) (w .fst,
          concat X (h y) (h (permutation_power X M (w .fst) x)) (permutation_power X M (w .fst) (h x))
            (refl h (w .snd)) (permutation_power_intertwine X X M M h step (w .fst) x))) o)

{` The induced permutation t̄ : X/m → X/m, [x] ↦ [t(x)]. `}
def quotient_successor (n : Nat) (c : Cycles)
  : ModQuotient n (c .fst .fst .fst) (c .fst .snd) → ModQuotient n (c .fst .fst .fst) (c .fst .snd)
  ≔ let X ≔ c .fst .fst .fst in let t ≔ c .fst .snd in let R ≔ mod_relation n X t in
    quotient_rec X (ModQuotient n X t) R (quotient_set X R) (x ↦ quotient_class X R (t .map x))
      (mod_respects_commuting n X t (t .map) (mod_power_commutes n X t))

def quotient_predecessor (n : Nat) (c : Cycles)
  : ModQuotient n (c .fst .fst .fst) (c .fst .snd) → ModQuotient n (c .fst .fst .fst) (c .fst .snd)
  ≔ let X ≔ c .fst .fst .fst in let t ≔ c .fst .snd in let R ≔ mod_relation n X t in
    let g ≔ equiv_inverse_map X X t in
    quotient_rec X (ModQuotient n X t) R (quotient_set X R) (x ↦ quotient_class X R (g x))
      (mod_respects_commuting n X t g (x ↦ inverse X (mod_power n X t .map (g x)) (g (mod_power n X t .map x))
        (inverse_intertwine X X t t (mod_power n X t .map)
          (y ↦ inverse X (t .map (mod_power n X t .map y)) (mod_power n X t .map (t .map y)) (mod_power_commutes n X t y)) x)))

def quotient_successor_equiv (n : Nat) (c : Cycles)
  : Equiv (ModQuotient n (c .fst .fst .fst) (c .fst .snd)) (ModQuotient n (c .fst .fst .fst) (c .fst .snd))
  ≔ let X ≔ c .fst .fst .fst in let t ≔ c .fst .snd in let R ≔ mod_relation n X t in
    let Q ≔ ModQuotient n X t in
    quasi_inverse_equiv Q Q (quotient_successor n c) (quotient_predecessor n c)
      (quotient_prop_induction X R (V ↦ Id Q (quotient_predecessor n c (quotient_successor n c V)) V)
        (V ↦ quotient_set X R (quotient_predecessor n c (quotient_successor n c V)) V)
        (x ↦ refl (quotient_class X R) (equiv_retraction X X t x)))
      (quotient_prop_induction X R (V ↦ Id Q (quotient_successor n c (quotient_predecessor n c V)) V)
        (V ↦ quotient_set X R (quotient_successor n c (quotient_predecessor n c V)) V)
        (x ↦ refl (quotient_class X R) (equiv_counit X X t x)))

def quotient_successor_power (n : Nat) (c : Cycles) (z : Int) (x : c .fst .fst .fst)
  : Id (ModQuotient n (c .fst .fst .fst) (c .fst .snd))
      (permutation_power (ModQuotient n (c .fst .fst .fst) (c .fst .snd)) (quotient_successor_equiv n c) z
        (quotient_class (c .fst .fst .fst) (mod_relation n (c .fst .fst .fst) (c .fst .snd)) x))
      (quotient_class (c .fst .fst .fst) (mod_relation n (c .fst .fst .fst) (c .fst .snd))
        (permutation_power (c .fst .fst .fst) (c .fst .snd) z x))
  ≔ let X ≔ c .fst .fst .fst in let t ≔ c .fst .snd in let R ≔ mod_relation n X t in
    let Q ≔ ModQuotient n X t in
    inverse Q (quotient_class X R (permutation_power X t z x))
      (permutation_power Q (quotient_successor_equiv n c) z (quotient_class X R x))
      (permutation_power_intertwine X Q t (quotient_successor_equiv n c) (quotient_class X R)
        (y ↦ refl (quotient_class X R (t .map y))) z x)

def quotient_successor_cyclic (n : Nat) (c : Cycles)
  : Cyclic (ModQuotient n (c .fst .fst .fst) (c .fst .snd)) (quotient_successor_equiv n c)
  ≔ let X ≔ c .fst .fst .fst in let t ≔ c .fst .snd in let R ≔ mod_relation n X t in
    let Q ≔ ModQuotient n X t in let T ≔ quotient_successor_equiv n c in
    (trunc_map native_truncation X Q (quotient_class X R) (c .snd .fst),
     V W ↦ quotient_prop_induction X R (V ↦ SameOrbit Q T V W) (V ↦ same_orbit_prop Q T V W)
       (a ↦ quotient_prop_induction X R (W ↦ SameOrbit Q T (quotient_class X R a) W)
         (W ↦ same_orbit_prop Q T (quotient_class X R a) W)
         (b ↦ mere_rec (OrbitWitness X t a b) (SameOrbit Q T (quotient_class X R a) (quotient_class X R b))
           (same_orbit_prop Q T (quotient_class X R a) (quotient_class X R b))
           (w ↦ mere (OrbitWitness Q T (quotient_class X R a) (quotient_class X R b)) (w .fst,
             concat Q (quotient_class X R b) (quotient_class X R (permutation_power X t (w .fst) a))
               (permutation_power Q T (w .fst) (quotient_class X R a))
               (refl (quotient_class X R) (w .snd))
               (inverse Q (permutation_power Q T (w .fst) (quotient_class X R a))
                 (quotient_class X R (permutation_power X t (w .fst) a)) (quotient_successor_power n c (w .fst) a))))
           (c .snd .snd a b)) W) V)

{` The cycle (X/m, t̄). `}
def QuotientCycle (n : Nat) (c : Cycles) : Cycles
  ≔ (((ModQuotient n (c .fst .fst .fst) (c .fst .snd),
        quotient_set (c .fst .fst .fst) (mod_relation n (c .fst .fst .fst) (c .fst .snd))),
      quotient_successor_equiv n c), quotient_successor_cyclic n c)

{` A map of cycles X → ℤ/m induces an identification (X/m, t̄) = (ℤ/m, s). `}
def residue_quotient_commutes (n : Nat) (c : Cycles) (rho : CycleResidues n c)
  : Commutes (ModQuotient n (c .fst .fst .fst) (c .fst .snd)) (Remainder (suc. n))
      (quotient_successor_equiv n c) (modular_successor_equiv n) (residue_quotient_map n c rho)
  ≔ let X ≔ c .fst .fst .fst in let R ≔ mod_relation n X (c .fst .snd) in
    let pi ≔ residue_quotient_map n c rho in
    quotient_prop_induction X R
      (V ↦ Id (Remainder (suc. n)) (pi (quotient_successor n c V)) (modular_successor n (pi V)))
      (V ↦ remainder_set (suc. n) (pi (quotient_successor n c V)) (modular_successor n (pi V)))
      (x ↦ rho .snd x)

def quotient_cycle_residue_path (n : Nat) (c : Cycles) (rho : CycleResidues n c)
  : Id Cycles (QuotientCycle n c) (finite_standard_cycle n)
  ≔ equiv_inverse_map (Id Cycles (QuotientCycle n c) (finite_standard_cycle n))
      (PermutationIsomorphisms (QuotientCycle n c .fst) (finite_standard_cycle n .fst))
      (cycle_paths_equiv (QuotientCycle n c) (finite_standard_cycle n))
      (residue_quotient_equiv n c rho, residue_quotient_commutes n c rho)

def quotient_cycle_standard (n : Nat) (c : Cycles) (divides : OrderDivides (principal_order (suc. n)) (cycle_order c))
  : Mere (Id Cycles (finite_standard_cycle n) (QuotientCycle n c))
  ≔ mere_rec (c .fst .fst .fst) (Mere (Id Cycles (finite_standard_cycle n) (QuotientCycle n c)))
      (mere_isprop (Id Cycles (finite_standard_cycle n) (QuotientCycle n c)))
      (x0 ↦ mere (Id Cycles (finite_standard_cycle n) (QuotientCycle n c))
        (inverse Cycles (QuotientCycle n c) (finite_standard_cycle n)
          (quotient_cycle_residue_path n c (cycle_residue n c divides x0 .fst))))
      (c .snd .fst)
