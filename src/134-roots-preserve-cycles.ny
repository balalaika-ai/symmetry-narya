export "133-root-iteration"

def same_orbit_iterate_steps (A B : Type) (t : A → A) (e : Equiv B B) (h : A → B)
  (step : (x : A) → SameOrbit B e (h x) (h (t x))) (n : Nat) (x : A)
  : SameOrbit B e (h x) (h (iterate A t n x))
  ≔ match n [
  | zero. ↦ same_orbit_refl B e (h x)
  | suc. n ↦ same_orbit_trans B e (h x) (h (iterate A t n x)) (h (t (iterate A t n x)))
      (same_orbit_iterate_steps A B t e h step n x) (step (iterate A t n x)) ]

def same_orbit_inverse_step (A B : Type) (e : Equiv A A) (f : Equiv B B) (h : A → B)
  (step : (x : A) → SameOrbit B f (h x) (h (e .map x))) (x : A)
  : SameOrbit B f (h x) (h (equiv_inverse_map A A e x))
  ≔ transport B (y ↦ SameOrbit B f y (h (equiv_inverse_map A A e x)))
      (h (e .map (equiv_inverse_map A A e x))) (h x) (refl h (equiv_counit A A e x))
      (same_orbit_sym B f (h (equiv_inverse_map A A e x)) (h (e .map (equiv_inverse_map A A e x)))
        (step (equiv_inverse_map A A e x)))

def same_orbit_power_steps (A B : Type) (e : Equiv A A) (f : Equiv B B) (h : A → B)
  (step : (x : A) → SameOrbit B f (h x) (h (e .map x))) (z : Int) (x : A)
  : SameOrbit B f (h x) (h (permutation_power A e z x))
  ≔ match z [
  | pos. n ↦ same_orbit_iterate_steps A B (e .map) f h step n x
  | neg. n ↦ same_orbit_iterate_steps A B (equiv_inverse_map A A e) f h
      (same_orbit_inverse_step A B e f h step) (suc. n) x ]

def same_orbit_map_steps (A B : Type) (e : Equiv A A) (f : Equiv B B) (h : A → B)
  (step : (x : A) → SameOrbit B f (h x) (h (e .map x))) (x y : A)
  : SameOrbit A e x y → SameOrbit B f (h x) (h y)
  ≔ mere_rec (OrbitWitness A e x y) (SameOrbit B f (h x) (h y)) (same_orbit_prop B f (h x) (h y))
      (w ↦ transport B (SameOrbit B f (h x)) (h (permutation_power A e (w .fst) x)) (h y)
        (inverse B (h y) (h (permutation_power A e (w .fst) x)) (refl h (w .snd)))
        (same_orbit_power_steps A B e f h step (w .fst) x))

def root_remainder_zero_step (n : Nat) (X : Type) (e : Equiv X X) (x : X)
  : SameOrbit (Product (Remainder (suc. n)) X) (root_remainder_equiv n X e)
      (remainder_at n zero. star., x) (remainder_at n zero. star., e .map x)
  ≔ mere (OrbitWitness (Product (Remainder (suc. n)) X) (root_remainder_equiv n X e)
      (remainder_at n zero. star., x) (remainder_at n zero. star., e .map x))
      (pos. (suc. n), inverse (Product (Remainder (suc. n)) X)
        (iterate (Product (Remainder (suc. n)) X) (root_remainder n X (e .map)) (suc. n) (remainder_at n zero. star., x))
        (remainder_at n zero. star., e .map x) (root_remainder_turn_zero n X (e .map) x))

def root_remainder_position_orbit (n : Nat) (X : Type) (e : Equiv X X) (r : Remainder (suc. n)) (x : X)
  : SameOrbit (Product (Remainder (suc. n)) X) (root_remainder_equiv n X e)
      (remainder_at n zero. star., x) (r, x)
  ≔ mere (OrbitWitness (Product (Remainder (suc. n)) X) (root_remainder_equiv n X e)
      (remainder_at n zero. star., x) (r, x))
      (pos. (r .fst), calc
        ((r, x) : Product (Remainder (suc. n)) X)
        = (remainder_at n (r .fst) (lt_from_book (r .fst) (suc. n) (r .snd)), x)
          by (remainder_equal (suc. n) r
            (remainder_at n (r .fst) (lt_from_book (r .fst) (suc. n) (r .snd))) (refl (r .fst)), refl x)
        = iterate (Product (Remainder (suc. n)) X) (root_remainder n X (e .map)) (r .fst) (remainder_at n zero. star., x)
          by root_remainder_iterate_small n (r .fst) (lt_from_book (r .fst) (suc. n) (r .snd)) X (e .map) x ∎)

{` The lemma after lem:root-pres-equiv. Signed orbit witnesses in X are
   transferred using actual iterates; no choice of a generator is made. `}
def root_remainder_cyclic (n : Nat) (X : Type) (e : Equiv X X) (c : Cyclic X e)
  : Cyclic (Product (Remainder (suc. n)) X) (root_remainder_equiv n X e)
  ≔ (trunc_map native_truncation X (Product (Remainder (suc. n)) X)
        (x ↦ (remainder_at n zero. star., x)) (c .fst),
      u v ↦ let R ≔ Product (Remainder (suc. n)) X in let f ≔ root_remainder_equiv n X e in
        same_orbit_trans R f u (remainder_at n zero. star., u .snd) v
          (same_orbit_sym R f (remainder_at n zero. star., u .snd) u (root_remainder_position_orbit n X e (u .fst) (u .snd)))
          (same_orbit_trans R f (remainder_at n zero. star., u .snd) (remainder_at n zero. star., v .snd) v
            (same_orbit_map_steps X R e f (x ↦ (remainder_at n zero. star., x))
              (root_remainder_zero_step n X e) (u .snd) (v .snd) (c .snd (u .snd) (v .snd)))
            (root_remainder_position_orbit n X e (v .fst) (v .snd))))
