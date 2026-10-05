export "141-cycle-map-spaces"

{` Generic lemmas for prop:ump-cycn-into-groupoids. `}
def loop_concat_equiv (A : Type) (a z : A) (l : Id A a a) : Equiv (Id A a z) (Id A a z)
  ≔ quasi_inverse_equiv (Id A a z) (Id A a z) (t ↦ concat A a a z l t) (t ↦ concat A a a z (inverse A a a l) t)
      (t ↦ calc
        concat A a a z (inverse A a a l) (concat A a a z l t)
        = concat A a a z (concat A a a a (inverse A a a l) l) t
          by inverse (Id A a z) (concat A a a z (concat A a a a (inverse A a a l) l) t)
            (concat A a a z (inverse A a a l) (concat A a a z l t)) (concat_assoc A a a a z (inverse A a a l) l t)
        = concat A a a z (refl a) t
          by refl ((q ↦ concat A a a z q t) : Id A a a → Id A a z) (concat_inverse_left A a a l)
        = t by concat_1p A a z t ∎)
      (t ↦ calc
        concat A a a z l (concat A a a z (inverse A a a l) t)
        = concat A a a z (concat A a a a l (inverse A a a l)) t
          by inverse (Id A a z) (concat A a a z (concat A a a a l (inverse A a a l)) t)
            (concat A a a z l (concat A a a z (inverse A a a l) t)) (concat_assoc A a a a z l (inverse A a a l) t)
        = concat A a a z (refl a) t
          by refl ((q ↦ concat A a a z q t) : Id A a a → Id A a z) (concat_inverse_right A a a l)
        = t by concat_1p A a z t ∎)

def iterate_cancel (A : Type) (f g : A → A) (h : (x : A) → Id A (g (f x)) x) (k : Nat) (x : A)
  : Id A (iterate A g k (iterate A f k x)) x
  ≔ match k [
  | zero. ↦ refl x
  | suc. k ↦ calc
      iterate A g (suc. k) (f (iterate A f k x))
      = iterate A g k (g (f (iterate A f k x)))
        by inverse A (iterate A g k (g (f (iterate A f k x)))) (iterate A g (suc. k) (f (iterate A f k x)))
          (iterate_commute A g k (suc. zero.) (f (iterate A f k x)))
      = iterate A g k (iterate A f k x) by refl (iterate A g k) (h (iterate A f k x))
      = x by iterate_cancel A f g h k x ∎ ]

def iterate_loop_concat (A : Type) (a z : A) (l : Id A a a) (k : Nat) (t : Id A a z)
  : Id (Id A a z) (iterate (Id A a z) (t' ↦ concat A a a z l t') k t) (concat A a a z (loop_power_nat A a l k) t)
  ≔ match k [
  | zero. ↦ inverse (Id A a z) (concat A a a z (refl a) t) t (concat_1p A a z t)
  | suc. k ↦ let g ≔ ((t' ↦ concat A a a z l t') : Id A a z → Id A a z) in
    calc
      iterate (Id A a z) g (suc. k) t = iterate (Id A a z) g k (g t)
        by inverse (Id A a z) (iterate (Id A a z) g k (g t)) (iterate (Id A a z) g (suc. k) t)
          (iterate_commute (Id A a z) g k (suc. zero.) t)
      = concat A a a z (loop_power_nat A a l k) (concat A a a z l t) by iterate_loop_concat A a z l k (g t)
      = concat A a a z (concat A a a a (loop_power_nat A a l k) l) t
        by inverse (Id A a z) (concat A a a z (concat A a a a (loop_power_nat A a l k) l) t)
          (concat A a a z (loop_power_nat A a l k) (concat A a a z l t))
          (concat_assoc A a a a z (loop_power_nat A a l k) l t) ∎ ]

def map_path_loop_power_nat (C A : Type) (f : C → A) (x : C) (l : Id C x x) (k : Nat)
  : Id (Id A (f x) (f x)) (refl f (loop_power_nat C x l k)) (loop_power_nat A (f x) (refl f l) k)
  ≔ match k [
  | zero. ↦ refl (refl (f x))
  | suc. k ↦ calc
      refl f (concat C x x x (loop_power_nat C x l k) l)
      = concat A (f x) (f x) (f x) (refl f (loop_power_nat C x l k)) (refl f l)
        by map_path_concat C A f x x x (loop_power_nat C x l k) l
      = concat A (f x) (f x) (f x) (loop_power_nat A (f x) (refl f l) k) (refl f l)
        by refl ((q ↦ concat A (f x) (f x) (f x) q (refl f l)) : Id A (f x) (f x) → Id A (f x) (f x))
          (map_path_loop_power_nat C A f x l k) ∎ ]

def transport_loop_family (A : Type) (x y : A) (p : Id A x y) (l : Id A x x)
  : Id (Id A y y) (transport A ((z ↦ Id A z z) : A → Type) x y p l)
      (concat A y x y (concat A y x x (inverse A x y p) l) p)
  ≔ J A x (y p ↦ Id (Id A y y) (transport A ((z ↦ Id A z z) : A → Type) x y p l)
        (concat A y x y (concat A y x x (inverse A x y p) l) p))
      (calc
        transport A ((z ↦ Id A z z) : A → Type) x x (refl x) l = l
          by transport_refl A ((z ↦ Id A z z) : A → Type) x l
        = concat A x x x (refl x) l by inverse (Id A x x) (concat A x x x (refl x) l) l (concat_1p A x x l)
        = concat A x x x (inverse A x x (refl x)) l
          by refl ((q ↦ concat A x x x q l) : Id A x x → Id A x x)
            (inverse (Id A x x) (inverse A x x (refl x)) (refl x) (inverse_refl A x))
        = concat A x x x (concat A x x x (inverse A x x (refl x)) l) (refl x)
          by inverse (Id A x x) (concat A x x x (concat A x x x (inverse A x x (refl x)) l) (refl x))
            (concat A x x x (inverse A x x (refl x)) l) (concat_p1 A x x (concat A x x x (inverse A x x (refl x)) l)) ∎)
      y p

def based_paths_from_contractible (A : Type) (a : A) : isContr (Σ A (y ↦ Id A a y))
  ≔ ((a, refl a), u ↦ J A a (y p ↦ Id (Σ A (z ↦ Id A a z)) (y, p) (a, refl a))
      (refl ((a, refl a) : Σ A (z ↦ Id A a z))) (u .fst) (u .snd))

{` Powers of a left inverse are powers with negated exponent. `}
def permutation_power_left_inverse (A : Type) (e e' : Equiv A A) (inv : (x : A) → Id A (e' .map (e .map x)) x)
  (z : Int) (x : A) : Id A (permutation_power A e' z x) (permutation_power A e (int_neg z) x)
  ≔ match z [
  | pos. zero. ↦ refl x
  | pos. (suc. j) ↦ iterate_pointwise A (e' .map) (equiv_inverse_map A A e)
      (y ↦ concat A (e' .map y) (e' .map (e .map (equiv_inverse_map A A e y))) (equiv_inverse_map A A e y)
        (refl (e' .map) (inverse A (e .map (equiv_inverse_map A A e y)) y (equiv_counit A A e y)))
        (inv (equiv_inverse_map A A e y))) (suc. j) x
  | neg. j ↦ iterate_pointwise A (equiv_inverse_map A A e') (e .map)
      (y ↦ inverse_at_known_point A A e' (e .map y) y (inv y)) (suc. j) x ]

def cyclic_left_inverse (A : Type) (e e' : Equiv A A) (inv : (x : A) → Id A (e' .map (e .map x)) x)
  (c : Cyclic A e) : Cyclic A e'
  ≔ (c .fst, x y ↦ trunc_map native_truncation (OrbitWitness A e x y) (OrbitWitness A e' x y)
      (w ↦ (int_neg (w .fst), calc
        y = permutation_power A e (w .fst) x by w .snd
        = permutation_power A e (int_neg (int_neg (w .fst))) x
          by refl ((z ↦ permutation_power A e z x) : Int → A)
            (inverse Int (int_neg (int_neg (w .fst))) (w .fst) (int_neg_neg (w .fst)))
        = permutation_power A e' (int_neg (w .fst)) x
          by inverse A (permutation_power A e' (int_neg (w .fst)) x) (permutation_power A e (int_neg (int_neg (w .fst))) x)
            (permutation_power_left_inverse A e e' inv (int_neg (w .fst)) x) ∎))
      (c .snd x y))

def permutation_period_laws (A : Type) (hs : isSet A) (e : Equiv A A) : IntegerSubgroupLaws (cycle_periods A hs e)
  ≔ (power_period_zero A e, (power_period_add A e, power_period_neg A e))

{` The loops of the standard n-cycle, n = suc b, in the component Cyc_n. `}
def modular_predecessor_equiv (b : Nat) : Equiv (Remainder (suc. b)) (Remainder (suc. b))
  ≔ quasi_inverse_equiv (Remainder (suc. b)) (Remainder (suc. b)) (modular_predecessor b) (modular_successor b)
      (modular_successor_predecessor b) (modular_predecessor_successor b)

def modular_predecessor_cyclic (b : Nat) : Cyclic (Remainder (suc. b)) (modular_predecessor_equiv b)
  ≔ cyclic_left_inverse (Remainder (suc. b)) (modular_successor_equiv b) (modular_predecessor_equiv b)
      (modular_predecessor_successor b) (modular_successor_cyclic b)

def standard_predecessor_iso (b : Nat)
  : PermutationIsomorphisms (finite_standard_cycle b .fst) (finite_standard_cycle b .fst)
  ≔ (modular_predecessor_equiv b, x ↦ concat (Remainder (suc. b)) (modular_predecessor b (modular_successor b x)) x
      (modular_successor b (modular_predecessor b x)) (modular_predecessor_successor b x)
      (inverse (Remainder (suc. b)) (modular_successor b (modular_predecessor b x)) x (modular_successor_predecessor b x)))

{` The symmetry (s^-1, !) of the standard n-cycle in Cycles. `}
def standard_predecessor_loop (b : Nat) : Id Cycles (finite_standard_cycle b) (finite_standard_cycle b)
  ≔ equiv_inverse_map (Id Cycles (finite_standard_cycle b) (finite_standard_cycle b))
      (PermutationIsomorphisms (finite_standard_cycle b .fst) (finite_standard_cycle b .fst))
      (cycle_paths_equiv (finite_standard_cycle b) (finite_standard_cycle b)) (standard_predecessor_iso b)

def standard_predecessor_loop_action (b : Nat) (x : Remainder (suc. b))
  : Id (Remainder (suc. b)) (cycle_path_evaluate (finite_standard_cycle b) (finite_standard_cycle b)
      (standard_predecessor_loop b) x) (modular_predecessor b x)
  ≔ evaluation_of_inverse_beta (Id Cycles (finite_standard_cycle b) (finite_standard_cycle b))
      (PermutationIsomorphisms (finite_standard_cycle b .fst) (finite_standard_cycle b .fst)) (Remainder (suc. b))
      (cycle_paths_equiv (finite_standard_cycle b) (finite_standard_cycle b))
      (h ↦ h .fst .map x) (standard_predecessor_iso b)

def cyc_component_prop (b : Nat) (c : Cycles) : isProp (Mere (Id Cycles (finite_standard_cycle b) c))
  ≔ mere_isprop (Id Cycles (finite_standard_cycle b) c)

{` sigma_n : pt_n = pt_n in Cyc_n. `}
def cyc_generator (b : Nat)
  : Id (CycleComponent (suc. b)) (principal_component_point (suc. b)) (principal_component_point (suc. b))
  ≔ subtype_equal Cycles (c ↦ Mere (Id Cycles (finite_standard_cycle b) c)) (cyc_component_prop b)
      (principal_component_point (suc. b)) (principal_component_point (suc. b)) (standard_predecessor_loop b)

def cyc_generator_underlying (b : Nat)
  : Id (Id Cycles (finite_standard_cycle b) (finite_standard_cycle b)) (cyc_generator b .fst) (standard_predecessor_loop b)
  ≔ equiv_counit (Id (CycleComponent (suc. b)) (principal_component_point (suc. b)) (principal_component_point (suc. b)))
      (Id Cycles (finite_standard_cycle b) (finite_standard_cycle b))
      (subtype_path_equiv Cycles (c ↦ Mere (Id Cycles (finite_standard_cycle b) c)) (cyc_component_prop b)
        (principal_component_point (suc. b)) (principal_component_point (suc. b)))
      (standard_predecessor_loop b)

def cyc_loop_equiv (b : Nat)
  : Equiv (Id (CycleComponent (suc. b)) (principal_component_point (suc. b)) (principal_component_point (suc. b)))
      (Remainder (suc. b))
  ≔ compose_equiv (Id (CycleComponent (suc. b)) (principal_component_point (suc. b)) (principal_component_point (suc. b)))
      (Id Cycles (finite_standard_cycle b) (finite_standard_cycle b)) (Remainder (suc. b))
      (subtype_path_equiv Cycles (c ↦ Mere (Id Cycles (finite_standard_cycle b) c)) (cyc_component_prop b)
        (principal_component_point (suc. b)) (principal_component_point (suc. b)))
      (native_equivalence (Id Cycles (finite_standard_cycle b) (finite_standard_cycle b)) (Remainder (suc. b))
        (cycle_automorphisms_evaluation (finite_standard_cycle b) (remainder_at b zero. star.)))

def cyc_loop_eval (b : Nat)
  (t : Id (CycleComponent (suc. b)) (principal_component_point (suc. b)) (principal_component_point (suc. b)))
  : Id (Remainder (suc. b)) (cyc_loop_equiv b .map t)
      (cycle_path_evaluate (finite_standard_cycle b) (finite_standard_cycle b) (t .fst) (remainder_at b zero. star.))
  ≔ refl (cyc_loop_equiv b .map t)
