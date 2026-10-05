export "138-pointed-cycles-of-order"

{` The relation ~_m of the m-th root section, m = suc n:
   x ~_m x' iff there merely is r : Int with x' = t^(mr)(x). `}
def ModWitness (n : Nat) (X : Type) (t : Equiv X X) (x y : X) : Type
  ≔ Σ Int (r ↦ Id X y (permutation_power X t (int_mul (pos. (suc. n)) r) x))

def mod_power (n : Nat) (X : Type) (t : Equiv X X) : Equiv X X ≔ permutation_power_equiv X t (pos. (suc. n))
def mod_relation (n : Nat) (X : Type) (t : Equiv X X) : EquivalenceRelation X
  ≔ orbit_relation X (mod_power n X t)

{` X/m, as a set of subsets of X. `}
def ModQuotient (n : Nat) (X : Type) (t : Equiv X X) : Type ≔ Quotient X (mod_relation n X t)

def mod_witness_orbit (n : Nat) (X : Type) (t : Equiv X X) (x y : X) (w : ModWitness n X t x y)
  : OrbitWitness X (mod_power n X t) x y
  ≔ (w .fst, concat X y (permutation_power X t (int_mul (pos. (suc. n)) (w .fst)) x)
      (permutation_power X (mod_power n X t) (w .fst) x) (w .snd) (permutation_power_scaled X t (suc. n) (w .fst) x))

def orbit_mod_witness (n : Nat) (X : Type) (t : Equiv X X) (x y : X) (w : OrbitWitness X (mod_power n X t) x y)
  : ModWitness n X t x y
  ≔ (w .fst, concat X y (permutation_power X (mod_power n X t) (w .fst) x)
      (permutation_power X t (int_mul (pos. (suc. n)) (w .fst)) x) (w .snd)
      (inverse X (permutation_power X t (int_mul (pos. (suc. n)) (w .fst)) x)
        (permutation_power X (mod_power n X t) (w .fst) x) (permutation_power_scaled X t (suc. n) (w .fst) x)))

{` The quotient relation is exactly the printed one. `}
def mod_relation_book (n : Nat) (X : Type) (t : Equiv X X) (x y : X)
  : Equiv (Rel X (mod_relation n X t) x y) (Mere (ModWitness n X t x y))
  ≔ iff_equiv (Rel X (mod_relation n X t) x y) (Mere (ModWitness n X t x y))
      (same_orbit_prop X (mod_power n X t) x y) (mere_isprop (ModWitness n X t x y))
      (trunc_map native_truncation (OrbitWitness X (mod_power n X t) x y) (ModWitness n X t x y)
        (orbit_mod_witness n X t x y))
      (trunc_map native_truncation (ModWitness n X t x y) (OrbitWitness X (mod_power n X t) x y)
        (mod_witness_orbit n X t x y))

def standard_multiple_period (n : Nat) (z : Int) (w : MultipleWitness (suc. n) z)
  : PowerPeriod (Remainder (suc. n)) (modular_successor_equiv n) z
  ≔ transport (Subtypes Int) (H ↦ H z .fst) (Multiples (suc. n)) (CyclePeriods (finite_standard_cycle n))
      (inverse (Subtypes Int) (CyclePeriods (finite_standard_cycle n)) (Multiples (suc. n)) (finite_standard_periods n))
      (mere (MultipleWitness (suc. n) z) w)

def standard_period_multiple (n : Nat) (z : Int) (p : PowerPeriod (Remainder (suc. n)) (modular_successor_equiv n) z)
  : Multiples (suc. n) z .fst
  ≔ transport (Subtypes Int) (H ↦ H z .fst) (CyclePeriods (finite_standard_cycle n)) (Multiples (suc. n))
      (finite_standard_periods n) p

{` Maps of cycles X → ℤ/m into the standard m-cycle.  Such a map
   exists exactly when the order of X is divisible by m (xca:map-of-cycles). `}
def CycleResidues (n : Nat) (c : Cycles) : Type
  ≔ PermutationMap (c .fst .fst .fst) (Remainder (suc. n)) (c .fst .snd) (modular_successor_equiv n)

{` The residue map normalized at a given point x0. `}
def cycle_residue (n : Nat) (c : Cycles) (divides : OrderDivides (principal_order (suc. n)) (cycle_order c))
  (x0 : c .fst .fst .fst)
  : PointedPermutationMaps (c .fst .fst .fst) (Remainder (suc. n)) (c .fst .snd) (modular_successor_equiv n)
      x0 (remainder_at n zero. star.)
  ≔ pointed_cycle_map (c .fst .fst .fst) (Remainder (suc. n)) (c .fst .fst .snd) (remainder_set (suc. n))
      (c .fst .snd) (modular_successor_equiv n) (c .snd) divides x0 (remainder_at n zero. star.)

def residue_power (n : Nat) (c : Cycles) (rho : CycleResidues n c) (z : Int) (a : c .fst .fst .fst)
  : Id (Remainder (suc. n)) (rho .fst (permutation_power (c .fst .fst .fst) (c .fst .snd) z a))
      (permutation_power (Remainder (suc. n)) (modular_successor_equiv n) z (rho .fst a))
  ≔ permutation_power_intertwine (c .fst .fst .fst) (Remainder (suc. n)) (c .fst .snd) (modular_successor_equiv n)
      (rho .fst) (rho .snd) z a

def residue_respects (n : Nat) (c : Cycles) (rho : CycleResidues n c)
  : Respects (c .fst .fst .fst) (Remainder (suc. n)) (mod_relation n (c .fst .fst .fst) (c .fst .snd)) (rho .fst)
  ≔ let X ≔ c .fst .fst .fst in let t ≔ c .fst .snd in
    let pi ≔ rho .fst in
    a b o ↦ mere_rec (OrbitWitness X (mod_power n X t) a b) (Id (Remainder (suc. n)) (pi a) (pi b))
      (remainder_set (suc. n) (pi a) (pi b))
      (w ↦ inverse (Remainder (suc. n)) (pi b) (pi a) (calc
        pi b = pi (permutation_power X (mod_power n X t) (w .fst) a) by refl pi (w .snd)
        = pi (permutation_power X t (int_mul (pos. (suc. n)) (w .fst)) a)
          by refl pi (inverse X (permutation_power X t (int_mul (pos. (suc. n)) (w .fst)) a)
            (permutation_power X (mod_power n X t) (w .fst) a) (permutation_power_scaled X t (suc. n) (w .fst) a))
        = permutation_power (Remainder (suc. n)) (modular_successor_equiv n) (int_mul (pos. (suc. n)) (w .fst)) (pi a)
          by residue_power n c rho (int_mul (pos. (suc. n)) (w .fst)) a
        = pi a by happly (Remainder (suc. n)) (_ ↦ Remainder (suc. n))
          (permutation_power (Remainder (suc. n)) (modular_successor_equiv n) (int_mul (pos. (suc. n)) (w .fst)))
          (identity (Remainder (suc. n)))
          (standard_multiple_period n (int_mul (pos. (suc. n)) (w .fst)) (w .fst, int_mul_comm (pos. (suc. n)) (w .fst)))
          (pi a) ∎)) o

def residue_reflects (n : Nat) (c : Cycles) (rho : CycleResidues n c) (a b : c .fst .fst .fst)
  (p : Id (Remainder (suc. n)) (rho .fst a) (rho .fst b))
  : Rel (c .fst .fst .fst) (mod_relation n (c .fst .fst .fst) (c .fst .snd)) a b
  ≔ let X ≔ c .fst .fst .fst in let t ≔ c .fst .snd in
    let pi ≔ rho .fst in
    let goal ≔ SameOrbit X (mod_power n X t) a b in
    mere_rec (OrbitWitness X t a b) goal (same_orbit_prop X (mod_power n X t) a b)
      (w ↦ let fixed ≔ calc
          permutation_power (Remainder (suc. n)) (modular_successor_equiv n) (w .fst) (pi a)
          = pi (permutation_power X t (w .fst) a)
            by inverse (Remainder (suc. n)) (pi (permutation_power X t (w .fst) a))
              (permutation_power (Remainder (suc. n)) (modular_successor_equiv n) (w .fst) (pi a))
              (residue_power n c rho (w .fst) a)
          = pi b by refl pi (inverse X b (permutation_power X t (w .fst) a) (w .snd))
          = pi a by inverse (Remainder (suc. n)) (pi a) (pi b) p ∎ in
        let period ≔ cycle_period_from_point (Remainder (suc. n)) (remainder_set (suc. n)) (modular_successor_equiv n)
          (modular_successor_cyclic n) (pi a) (w .fst) fixed in
        mere_rec (MultipleWitness (suc. n) (w .fst)) goal (same_orbit_prop X (mod_power n X t) a b)
          (v ↦ mere (OrbitWitness X (mod_power n X t) a b) (v .fst, calc
            b = permutation_power X t (w .fst) a by w .snd
            = permutation_power X t (int_mul (v .fst) (pos. (suc. n))) a
              by refl ((z ↦ permutation_power X t z a) : Int → X) (v .snd)
            = permutation_power X t (int_mul (pos. (suc. n)) (v .fst)) a
              by refl ((z ↦ permutation_power X t z a) : Int → X) (int_mul_comm (v .fst) (pos. (suc. n)))
            = permutation_power X (mod_power n X t) (v .fst) a by permutation_power_scaled X t (suc. n) (v .fst) a ∎))
          (standard_period_multiple n (w .fst) period))
      (c .snd .snd a b)

def residue_quotient_map (n : Nat) (c : Cycles) (rho : CycleResidues n c)
  : ModQuotient n (c .fst .fst .fst) (c .fst .snd) → Remainder (suc. n)
  ≔ quotient_rec (c .fst .fst .fst) (Remainder (suc. n)) (mod_relation n (c .fst .fst .fst) (c .fst .snd))
      (remainder_set (suc. n)) (rho .fst) (residue_respects n c rho)

def residue_quotient_injective (n : Nat) (c : Cycles) (rho : CycleResidues n c)
  : PathReflecting (ModQuotient n (c .fst .fst .fst) (c .fst .snd)) (Remainder (suc. n)) (residue_quotient_map n c rho)
  ≔ let X ≔ c .fst .fst .fst in let R ≔ mod_relation n X (c .fst .snd) in
    let Q ≔ ModQuotient n X (c .fst .snd) in let pi ≔ residue_quotient_map n c rho in
    V W p ↦ mere_rec (BookFiber X Q (quotient_class X R) V) (Id Q V W) (quotient_set X R V W)
      (a ↦ mere_rec (BookFiber X Q (quotient_class X R) W) (Id Q V W) (quotient_set X R V W)
        (b ↦ calc
          V = quotient_class X R (a .fst) by a .snd
          = quotient_class X R (b .fst)
            by equiv_inverse_map (Id Q (quotient_class X R (a .fst)) (quotient_class X R (b .fst)))
              (Rel X R (a .fst) (b .fst)) (quotient_effective X R (a .fst) (b .fst))
              (residue_reflects n c rho (a .fst) (b .fst) (calc
                pi (quotient_class X R (a .fst)) = pi V by refl pi (inverse Q V (quotient_class X R (a .fst)) (a .snd))
                = pi W by p
                = pi (quotient_class X R (b .fst)) by refl pi (b .snd) ∎))
          = W by inverse Q W (quotient_class X R (b .fst)) (b .snd) ∎)
        (quotient_surjective X R W))
      (quotient_surjective X R V)

def residue_quotient_surjective (n : Nat) (c : Cycles) (rho : CycleResidues n c)
  : Surjective (ModQuotient n (c .fst .fst .fst) (c .fst .snd)) (Remainder (suc. n)) (residue_quotient_map n c rho)
  ≔ let X ≔ c .fst .fst .fst in let R ≔ mod_relation n X (c .fst .snd) in
    let Q ≔ ModQuotient n X (c .fst .snd) in
    r ↦ mere_rec (BookFiber X (Remainder (suc. n)) (rho .fst) r)
      (Mere (BookFiber Q (Remainder (suc. n)) (residue_quotient_map n c rho) r))
      (mere_isprop (BookFiber Q (Remainder (suc. n)) (residue_quotient_map n c rho) r))
      (w ↦ mere (BookFiber Q (Remainder (suc. n)) (residue_quotient_map n c rho) r) (quotient_class X R (w .fst), w .snd))
      (cycle_map_surjective X (Remainder (suc. n)) (c .fst .snd) (modular_successor_equiv n) (c .snd)
        (modular_successor_cyclic n) rho r)

{` Every map of cycles X → ℤ/m identifies X/m with ℤ/m. `}
def residue_quotient_equiv (n : Nat) (c : Cycles) (rho : CycleResidues n c)
  : Equiv (ModQuotient n (c .fst .fst .fst) (c .fst .snd)) (Remainder (suc. n))
  ≔ set_bijection_equiv (ModQuotient n (c .fst .fst .fst) (c .fst .snd)) (Remainder (suc. n)) (remainder_set (suc. n))
      (residue_quotient_map n c rho) (residue_quotient_injective n c rho) (residue_quotient_surjective n c rho)

{` The map f(k) = [t^k(x0)] of lem:X-mod-m-chosen. `}
def residue_class (n : Nat) (c : Cycles) (x0 : c .fst .fst .fst) (k : Fin (suc. n))
  : ModQuotient n (c .fst .fst .fst) (c .fst .snd)
  ≔ quotient_class (c .fst .fst .fst) (mod_relation n (c .fst .fst .fst) (c .fst .snd))
      (iterate (c .fst .fst .fst) (c .fst .snd .map) (fin_book_below_equiv (suc. n) .map k .fst) x0)

def residue_class_position (n : Nat) (c : Cycles) (rho : CycleResidues n c) (x0 : c .fst .fst .fst)
  (base : Id (Remainder (suc. n)) (rho .fst x0) (remainder_at n zero. star.)) (k : Fin (suc. n))
  : Id (Remainder (suc. n)) (residue_quotient_map n c rho (residue_class n c x0 k)) (fin_book_below_equiv (suc. n) .map k)
  ≔ let X ≔ c .fst .fst .fst in
    let r ≔ fin_book_below_equiv (suc. n) .map k in
    let h ≔ lt_from_book (r .fst) (suc. n) (r .snd) in
    calc
      rho .fst (iterate X (c .fst .snd .map) (r .fst) x0)
      = iterate (Remainder (suc. n)) (modular_successor n) (r .fst) (rho .fst x0)
        by iterate_intertwine X (Remainder (suc. n)) (c .fst .snd .map) (modular_successor n) (rho .fst) (rho .snd) (r .fst) x0
      = iterate (Remainder (suc. n)) (modular_successor n) (r .fst) (remainder_at n zero. star.)
        by refl (iterate (Remainder (suc. n)) (modular_successor n) (r .fst)) base
      = remainder_at n (r .fst) h by modular_successor_iterate n (r .fst) h
      = r by remainder_equal (suc. n) (remainder_at n (r .fst) h) r (refl (r .fst)) ∎

def residue_class_injective (n : Nat) (c : Cycles) (divides : OrderDivides (principal_order (suc. n)) (cycle_order c))
  (x0 : c .fst .fst .fst) : PathReflecting (Fin (suc. n)) (ModQuotient n (c .fst .fst .fst) (c .fst .snd)) (residue_class n c x0)
  ≔ let rho ≔ cycle_residue n c divides x0 in
    let pi ≔ residue_quotient_map n c (rho .fst) in
    k l p ↦ equivalence_injective (Fin (suc. n)) (Remainder (suc. n)) (fin_book_below_equiv (suc. n)) k l (calc
      fin_book_below_equiv (suc. n) .map k = pi (residue_class n c x0 k)
        by inverse (Remainder (suc. n)) (pi (residue_class n c x0 k)) (fin_book_below_equiv (suc. n) .map k)
          (residue_class_position n c (rho .fst) x0 (rho .snd) k)
      = pi (residue_class n c x0 l) by refl pi p
      = fin_book_below_equiv (suc. n) .map l by residue_class_position n c (rho .fst) x0 (rho .snd) l ∎)

def residue_class_surjective (n : Nat) (c : Cycles) (divides : OrderDivides (principal_order (suc. n)) (cycle_order c))
  (x0 : c .fst .fst .fst) : Surjective (Fin (suc. n)) (ModQuotient n (c .fst .fst .fst) (c .fst .snd)) (residue_class n c x0)
  ≔ let Q ≔ ModQuotient n (c .fst .fst .fst) (c .fst .snd) in
    let rho ≔ cycle_residue n c divides x0 in
    let pi ≔ residue_quotient_map n c (rho .fst) in
    let e ≔ fin_book_below_equiv (suc. n) in
    V ↦ let k ≔ equiv_inverse_map (Fin (suc. n)) (Remainder (suc. n)) e (pi V) in
      mere (BookFiber (Fin (suc. n)) Q (residue_class n c x0) V)
        (k, residue_quotient_injective n c (rho .fst) V (residue_class n c x0 k) (calc
          pi V = e .map k by inverse (Remainder (suc. n)) (e .map k) (pi V) (equiv_counit (Fin (suc. n)) (Remainder (suc. n)) e (pi V))
          = pi (residue_class n c x0 k)
            by inverse (Remainder (suc. n)) (pi (residue_class n c x0 k)) (e .map k)
              (residue_class_position n c (rho .fst) x0 (rho .snd) k) ∎))

{` lem:X-mod-m-chosen: for a cycle of order divisible by m and any x0,
   k ↦ [t^k(x0)] is an equivalence Fin m ≃ X/m. `}
def residue_class_equiv (n : Nat) (c : Cycles) (divides : OrderDivides (principal_order (suc. n)) (cycle_order c))
  (x0 : c .fst .fst .fst) : Equiv (Fin (suc. n)) (ModQuotient n (c .fst .fst .fst) (c .fst .snd))
  ≔ set_bijection_equiv (Fin (suc. n)) (ModQuotient n (c .fst .fst .fst) (c .fst .snd))
      (quotient_set (c .fst .fst .fst) (mod_relation n (c .fst .fst .fst) (c .fst .snd)))
      (residue_class n c x0) (residue_class_injective n c divides x0) (residue_class_surjective n c divides x0)
