export "135-formal-roots"

def int_add_successor_right (x y : Int)
  : Id Int (int_add x (int_succ y)) (int_succ (int_add x y))
  ≔ permutation_power_succ Int int_succ_equiv y x

def int_add_successor_left (x y : Int)
  : Id Int (int_add (int_succ x) y) (int_succ (int_add x y))
  ≔ calc
      int_add (int_succ x) y = int_add y (int_succ x) by int_add_comm (int_succ x) y
      = int_succ (int_add y x) by int_add_successor_right y x
      = int_succ (int_add x y) by refl int_succ (int_add_comm y x) ∎

def integer_scaling_successor (q : Int) (m : Nat)
  : Id Int (int_mul (int_succ q) (pos. m)) (iterate Int int_succ m (int_mul q (pos. m)))
  ≔ match m [
  | zero. ↦ refl int_zero
  | suc. m ↦ calc
      int_mul (int_succ q) (pos. (suc. m)) = int_succ (int_add q (int_mul (int_succ q) (pos. m)))
        by int_add_successor_left q (int_mul (int_succ q) (pos. m))
      = int_succ (int_add q (iterate Int int_succ m (int_mul q (pos. m))))
        by refl ((v ↦ int_succ (int_add q v)) : Int → Int) (integer_scaling_successor q m)
      = iterate Int int_succ (suc. m) (int_mul q (pos. (suc. m)))
        by refl int_succ (iterate_intertwine Int Int int_succ int_succ (int_add q)
          (int_add_successor_right q) m (int_mul q (pos. m))) ∎ ]

def root_integer_digits_step (n : Nat) (u : IntegerDigits (suc. n))
  : Id Int (integer_digits_value (suc. n) (root_remainder n Int int_succ u))
      (int_succ (integer_digits_value (suc. n) u))
  ≔ match le_split (u .fst .fst) n (lt_from_book (u .fst .fst) (suc. n) (u .fst .snd)) [
  | inl. small ↦ calc
      integer_digits_value (suc. n) (root_remainder n Int int_succ u)
      = integer_digits_value (suc. n) (remainder_at n (suc. (u .fst .fst)) small, u .snd)
        by refl (integer_digits_value (suc. n)) (root_remainder_small n Int int_succ (u .fst) small (u .snd))
      = int_succ (integer_digits_value (suc. n) u) by refl (int_succ (integer_digits_value (suc. n) u)) ∎
  | inr. last ↦ calc
      integer_digits_value (suc. n) (root_remainder n Int int_succ u)
      = int_mul (int_succ (u .snd)) (pos. (suc. n))
        by refl (integer_digits_value (suc. n)) (root_remainder_last_at n Int int_succ (u .fst) last (u .snd))
      = iterate Int int_succ (suc. n) (int_mul (u .snd) (pos. (suc. n)))
        by integer_scaling_successor (u .snd) (suc. n)
      = int_succ (integer_digits_value (suc. n) u)
        by refl ((r ↦ iterate Int int_succ (suc. r) (int_mul (u .snd) (pos. (suc. n)))) : Nat → Int) last ∎ ]

{` The displayed phi(k,z)=k+mz intertwines the actual root successor
   and integer successor, including the wrap branch and negative z. `}
def integer_root_radix_commutes (n : Nat)
  : Commutes (Product (Fin (suc. n)) Int) Int (root_finite_equiv n Int int_succ_equiv) int_succ_equiv
      (integer_radix_value (suc. n))
  ≔ u ↦ calc
      integer_radix_value (suc. n) (root_finite n Int int_succ u)
      = integer_digits_value (suc. n) (root_finite_encode n Int (root_finite n Int int_succ u))
        by integer_radix_value_compare (suc. n) (root_finite n Int int_succ u)
      = integer_digits_value (suc. n) (root_remainder n Int int_succ (root_finite_encode n Int u))
        by refl (integer_digits_value (suc. n))
          (root_finite_encode_decode n Int (root_remainder n Int int_succ (root_finite_encode n Int u)))
      = int_succ (integer_digits_value (suc. n) (root_finite_encode n Int u))
        by root_integer_digits_step n (root_finite_encode n Int u)
      = int_succ (integer_radix_value (suc. n) u) by refl int_succ (integer_radix_value_compare (suc. n) u) ∎

def root_infinite_cycle_path (n : Nat) : Id Cycles (cycle_root n infinite_cycle) infinite_cycle
  ≔ equiv_inverse_map (Id Cycles (cycle_root n infinite_cycle) infinite_cycle)
      (PermutationIsomorphisms (cycle_root n infinite_cycle .fst) (infinite_cycle .fst))
      (cycle_paths_equiv (cycle_root n infinite_cycle) infinite_cycle)
      (native_equivalence (Product (Fin (suc. n)) Int) Int
        (integer_radix_equiv (suc. n) (lt_to_book zero. (suc. n) star.)), integer_root_radix_commutes n)

def formal_root_integer_path (n : Nat) : Id Endomorphisms (formal_root n integer_endomorphism) integer_endomorphism
  ≔ refl cycle_endomorphism (root_infinite_cycle_path n)

{` lem:deg-m-on-Cyc, infinite restriction in the literal endomorphism
   component. The finite restrictions are separate remaining obligations. `}
def formal_root_infinite_component (n : Nat) (u : InfiniteCycles) : InfiniteCycles
  ≔ (formal_root n (u .fst), trunc_map native_truncation (Id Endomorphisms integer_endomorphism (u .fst))
      (Id Endomorphisms integer_endomorphism (formal_root n (u .fst)))
      (p ↦ concat Endomorphisms integer_endomorphism (formal_root n integer_endomorphism) (formal_root n (u .fst))
        (inverse Endomorphisms (formal_root n integer_endomorphism) integer_endomorphism (formal_root_integer_path n))
        (refl (formal_root n) p)) (u .snd))

def formal_root_infinite_pointed (n : Nat)
  : BookPointedMap (InfiniteCycles, infinite_endomorphism_point) (InfiniteCycles, infinite_endomorphism_point)
  ≔ (formal_root_infinite_component n,
      subtype_equal Endomorphisms (u ↦ Mere (Id Endomorphisms integer_endomorphism u))
        (u ↦ mere_isprop (Id Endomorphisms integer_endomorphism u))
        infinite_endomorphism_point (formal_root_infinite_component n infinite_endomorphism_point)
        (inverse Endomorphisms (formal_root n integer_endomorphism) integer_endomorphism (formal_root_integer_path n)))
