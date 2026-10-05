export "136-roots-of-infinite-cycles"

def iterate_pointwise (A : Type) (f g : A → A) (h : (x : A) → Id A (f x) (g x)) (n : Nat) (x : A)
  : Id A (iterate A f n x) (iterate A g n x)
  ≔ iterate_intertwine A A f g (y ↦ y) h n x

def permutation_power_step_iterate (A : Type) (e : Equiv A A) (s : Int) (j : Nat) (x : A)
  : Id A (permutation_power A e (iterate Int (int_add s) j int_zero) x) (iterate A (permutation_power A e s) j x)
  ≔ match j [
  | zero. ↦ refl x
  | suc. j ↦ calc
      permutation_power A e (int_add s (iterate Int (int_add s) j int_zero)) x
      = permutation_power A e (iterate Int (int_add s) j int_zero) (permutation_power A e s x)
        by permutation_power_add A e s (iterate Int (int_add s) j int_zero) x
      = iterate A (permutation_power A e s) j (permutation_power A e s x)
        by permutation_power_step_iterate A e s j (permutation_power A e s x)
      = iterate A (permutation_power A e s) (suc. j) x
        by iterate_commute A (permutation_power A e s) j (suc. zero.) x ∎ ]

{` A power of a power: e^(m·q) = (e^m)^q for natural m and integer q. `}
def permutation_power_scaled (A : Type) (e : Equiv A A) (m : Nat) (q : Int) (x : A)
  : Id A (permutation_power A e (int_mul (pos. m) q) x)
      (permutation_power A (permutation_power_equiv A e (pos. m)) q x)
  ≔ match q [
  | pos. j ↦ permutation_power_step_iterate A e (pos. m) j x
  | neg. j ↦ let E ≔ permutation_power_equiv A e (pos. m) in
    let g ≔ permutation_power A e (int_neg (pos. m)) in
    calc
      permutation_power A e (int_mul (pos. m) (neg. j)) x = iterate A g (suc. j) x
        by permutation_power_step_iterate A e (int_neg (pos. m)) (suc. j) x
      = iterate A (equiv_inverse_map A A E) (suc. j) x
        by iterate_pointwise A g (equiv_inverse_map A A E)
          (y ↦ inverse A (equiv_inverse_map A A E y) (g y)
            (inverse_at_known_point A A E (g y) y (permutation_power_inverse_other A e (pos. m) y))) (suc. j) x ∎ ]

def int_mul_pos_add (x : Int) (c d : Nat)
  : Id Int (int_mul x (pos. (add c d))) (int_add (int_mul x (pos. c)) (int_mul x (pos. d)))
  ≔ match d [
  | zero. ↦ refl (int_mul x (pos. c))
  | suc. d ↦ calc
      int_add x (int_mul x (pos. (add c d))) = int_add x (int_add (int_mul x (pos. c)) (int_mul x (pos. d)))
        by refl (int_add x) (int_mul_pos_add x c d)
      = int_add (int_add x (int_mul x (pos. c))) (int_mul x (pos. d))
        by inverse Int (int_add (int_add x (int_mul x (pos. c))) (int_mul x (pos. d)))
          (int_add x (int_add (int_mul x (pos. c)) (int_mul x (pos. d))))
          (int_add_assoc x (int_mul x (pos. c)) (int_mul x (pos. d)))
      = int_add (int_add (int_mul x (pos. c)) x) (int_mul x (pos. d))
        by refl ((v ↦ int_add v (int_mul x (pos. d))) : Int → Int) (int_add_comm x (int_mul x (pos. c)))
      = int_add (int_mul x (pos. c)) (int_add x (int_mul x (pos. d)))
        by int_add_assoc (int_mul x (pos. c)) x (int_mul x (pos. d)) ∎ ]

def int_mul_pos_mul (x : Int) (a b : Nat)
  : Id Int (int_mul x (pos. (mul a b))) (int_mul (int_mul x (pos. a)) (pos. b))
  ≔ match b [
  | zero. ↦ refl int_zero
  | suc. b ↦ calc
      int_mul x (pos. (add (mul a b) a)) = int_add (int_mul x (pos. (mul a b))) (int_mul x (pos. a))
        by int_mul_pos_add x (mul a b) a
      = int_add (int_mul (int_mul x (pos. a)) (pos. b)) (int_mul x (pos. a))
        by refl ((v ↦ int_add v (int_mul x (pos. a))) : Int → Int) (int_mul_pos_mul x a b)
      = int_add (int_mul x (pos. a)) (int_mul (int_mul x (pos. a)) (pos. b))
        by int_add_comm (int_mul (int_mul x (pos. a)) (pos. b)) (int_mul x (pos. a)) ∎ ]

{` The first coordinate of the root is the modular successor. `}
def root_remainder_first (n : Nat) (X : Type) (t : X → X) (u : Product (Remainder (suc. n)) X)
  : Id (Remainder (suc. n)) (root_remainder n X t u .fst) (modular_successor n (u .fst))
  ≔ let R ≔ Product (Remainder (suc. n)) X in
    let first ≔ ((v ↦ v .fst) : R → Remainder (suc. n)) in
    match le_split (u .fst .fst) n (lt_from_book (u .fst .fst) (suc. n) (u .fst .snd)) [
  | inl. small ↦ calc
      root_remainder n X t u .fst = remainder_at n (suc. (u .fst .fst)) small
        by refl first (root_remainder_small n X t (u .fst) small (u .snd))
      = modular_successor n (u .fst)
        by inverse (Remainder (suc. n)) (modular_successor n (u .fst)) (remainder_at n (suc. (u .fst .fst)) small)
          (modular_successor_remainder_small n (u .fst) small) ∎
  | inr. last ↦ calc
      root_remainder n X t u .fst = remainder_at n zero. star.
        by refl first (root_remainder_last_at n X t (u .fst) last (u .snd))
      = modular_successor n (remainder_at n n (le_refl n))
        by inverse (Remainder (suc. n)) (modular_successor n (remainder_at n n (le_refl n))) (remainder_at n zero. star.)
          (modular_successor_last n)
      = modular_successor n (u .fst)
        by refl (modular_successor n) (remainder_equal (suc. n) (remainder_at n n (le_refl n)) (u .fst)
          (inverse Nat (u .fst .fst) n last)) ∎ ]

def root_finite_remainder_first (n : Nat) (X : Type) (e : Equiv X X)
  : Commutes (Product (Fin (suc. n)) X) (Remainder (suc. n)) (root_finite_equiv n X e) (modular_successor_equiv n)
      (u ↦ fin_book_below_equiv (suc. n) .map (u .fst))
  ≔ u ↦ calc
      fin_book_below_equiv (suc. n) .map (root_finite n X (e .map) u .fst)
      = root_remainder n X (e .map) (root_finite_encode n X u) .fst
        by equiv_counit (Fin (suc. n)) (Remainder (suc. n)) (fin_book_below_equiv (suc. n))
          (root_remainder n X (e .map) (root_finite_encode n X u) .fst)
      = modular_successor n (fin_book_below_equiv (suc. n) .map (u .fst))
        by root_remainder_first n X (e .map) (root_finite_encode n X u) ∎

{` lem:m-root-id, first clause: a period of the root is a period of the
   standard m-cycle.  A point of X is used only to prove a proposition. `}
def root_period_standard (n : Nat) (X : Type) (e : Equiv X X) (x : X) (z : Int)
  (p : PowerPeriod (Product (Fin (suc. n)) X) (root_finite_equiv n X e) z)
  : CyclePeriods (finite_standard_cycle n) z .fst
  ≔ let F ≔ Product (Fin (suc. n)) X in let u : F ≔ (inr. star., x) in
    let h ≔ ((v ↦ fin_book_below_equiv (suc. n) .map (v .fst)) : F → Remainder (suc. n)) in
    cycle_period_from_point (Remainder (suc. n)) (remainder_set (suc. n)) (modular_successor_equiv n)
      (modular_successor_cyclic n) (h u) z (calc
        permutation_power (Remainder (suc. n)) (modular_successor_equiv n) z (h u)
        = h (permutation_power F (root_finite_equiv n X e) z u)
          by inverse (Remainder (suc. n)) (h (permutation_power F (root_finite_equiv n X e) z u))
            (permutation_power (Remainder (suc. n)) (modular_successor_equiv n) z (h u))
            (permutation_power_intertwine F (Remainder (suc. n)) (root_finite_equiv n X e) (modular_successor_equiv n)
              h (root_finite_remainder_first n X e) z u)
        = h u by refl h (happly F (_ ↦ F) (permutation_power F (root_finite_equiv n X e) z) (identity F) p u) ∎)

def root_periods_standard (n : Nat) (c : Cycles)
  : Inclusion Int (CyclePeriods (cycle_root n c)) (CyclePeriods (finite_standard_cycle n))
  ≔ z p ↦ mere_rec (c .fst .fst .fst) (CyclePeriods (finite_standard_cycle n) z .fst)
      (CyclePeriods (finite_standard_cycle n) z .snd)
      (x ↦ root_period_standard n (c .fst .fst .fst) (c .fst .snd) x z p) (c .snd .fst)

{` "In other words, m divides the order of the root", with divisibility
   of orders as reverse inclusion of period subgroups (def:Order). `}
def root_order_divisible (n : Nat) (c : Cycles)
  : OrderDivides (principal_order (suc. n)) (cycle_order (cycle_root n c))
  ≔ root_periods_standard n c

def root_period_multiple (n : Nat) (c : Cycles) (z : Int) (p : CyclePeriods (cycle_root n c) z .fst)
  : Multiples (suc. n) z .fst
  ≔ transport (Subtypes Int) (H ↦ H z .fst) (CyclePeriods (finite_standard_cycle n)) (Multiples (suc. n))
      (finite_standard_periods n) (root_periods_standard n c z p)

{` The root iterated m·q times is id × t^q, for every integer q. `}
def root_scaled_power (n : Nat) (X : Type) (e : Equiv X X) (q : Int) (u : Product (Fin (suc. n)) X)
  : Id (Product (Fin (suc. n)) X)
      (permutation_power (Product (Fin (suc. n)) X) (root_finite_equiv n X e) (int_mul (pos. (suc. n)) q) u)
      (u .fst, permutation_power X e q (u .snd))
  ≔ let F ≔ Product (Fin (suc. n)) X in let R ≔ root_finite_equiv n X e in
    let M ≔ permutation_power_equiv F R (pos. (suc. n)) in
    calc
      permutation_power F R (int_mul (pos. (suc. n)) q) u = permutation_power F M q u
        by permutation_power_scaled F R (suc. n) q u
      = (u .fst, permutation_power X e q (u .snd))
        by inverse F (u .fst, permutation_power X e q (u .snd)) (permutation_power F M q u)
          (permutation_power_intertwine X F e M (x ↦ (u .fst, x))
            (x ↦ inverse F (iterate F (root_finite n X (e .map)) (suc. n) (u .fst, x)) (u .fst, e .map x)
              (root_finite_full_turn n X (e .map) (u .fst, x))) q (u .snd)) ∎

{` lem:m-root-id, second clause: if the root has period z = q·m, then t^q = id. `}
def root_period_quotient (n : Nat) (X : Type) (e : Equiv X X) (z : Int)
  (p : PowerPeriod (Product (Fin (suc. n)) X) (root_finite_equiv n X e) z)
  (w : MultipleWitness (suc. n) z) : PowerPeriod X e (w .fst)
  ≔ let F ≔ Product (Fin (suc. n)) X in let R ≔ root_finite_equiv n X e in
    let q ≔ w .fst in
    funext X (_ ↦ X) (permutation_power X e q) (identity X) (x ↦
      refl ((v ↦ v .snd) : F → X) (calc
        ((inr. star., permutation_power X e q x) : F)
        = permutation_power F R (int_mul (pos. (suc. n)) q) (inr. star., x)
          by inverse F (permutation_power F R (int_mul (pos. (suc. n)) q) (inr. star., x))
            (inr. star., permutation_power X e q x) (root_scaled_power n X e q (inr. star., x))
        = permutation_power F R z (inr. star., x)
          by refl ((y ↦ permutation_power F R y (inr. star., x)) : Int → F)
            (concat Int (int_mul (pos. (suc. n)) q) (int_mul q (pos. (suc. n))) z
              (int_mul_comm (pos. (suc. n)) q) (inverse Int z (int_mul q (pos. (suc. n))) (w .snd)))
        = (inr. star., x) by happly F (_ ↦ F) (permutation_power F R z) (identity F) p (inr. star., x) ∎))

{` The converse used in thm:fiber-cdg: a period q of t gives the period q·m of the root. `}
def root_period_from_scaled (n : Nat) (X : Type) (e : Equiv X X) (q : Int) (p : PowerPeriod X e q)
  : PowerPeriod (Product (Fin (suc. n)) X) (root_finite_equiv n X e) (int_mul q (pos. (suc. n)))
  ≔ let F ≔ Product (Fin (suc. n)) X in let R ≔ root_finite_equiv n X e in
    funext F (_ ↦ F) (permutation_power F R (int_mul q (pos. (suc. n)))) (identity F) (u ↦ calc
      permutation_power F R (int_mul q (pos. (suc. n))) u = permutation_power F R (int_mul (pos. (suc. n)) q) u
        by refl ((y ↦ permutation_power F R y u) : Int → F) (int_mul_comm q (pos. (suc. n)))
      = (u .fst, permutation_power X e q (u .snd)) by root_scaled_power n X e q u
      = u by (refl (u .fst), happly X (_ ↦ X) (permutation_power X e q) (identity X) p (u .snd)) ∎)

{` The subgroup m·H = {q·m | q ∈ H}. `}
def ScaledWitness (m : Nat) (H : Subtypes Int) (z : Int) : Type
  ≔ Σ (MultipleWitness m z) (w ↦ H (w .fst) .fst)
def ScaledSubtype (m : Nat) (H : Subtypes Int) : Subtypes Int
  ≔ z ↦ (Mere (ScaledWitness m H z), mere_isprop (ScaledWitness m H z))

{` Periods of the m-th root are exactly m times the periods of the cycle. `}
def root_cycle_periods (n : Nat) (c : Cycles)
  : Id (Subtypes Int) (CyclePeriods (cycle_root n c)) (ScaledSubtype (suc. n) (CyclePeriods c))
  ≔ let X ≔ c .fst .fst .fst in let e ≔ c .fst .snd in
    let S ≔ ScaledSubtype (suc. n) (CyclePeriods c) in
    inclusion_antisym Int (CyclePeriods (cycle_root n c)) S
      (z p ↦ mere_rec (MultipleWitness (suc. n) z) (S z .fst) (S z .snd)
        (w ↦ mere (ScaledWitness (suc. n) (CyclePeriods c) z) (w, root_period_quotient n X e z p w))
        (root_period_multiple n c z p))
      (z s ↦ mere_rec (ScaledWitness (suc. n) (CyclePeriods c) z) (CyclePeriods (cycle_root n c) z .fst)
        (CyclePeriods (cycle_root n c) z .snd)
        (v ↦ transport Int (PowerPeriod (Product (Fin (suc. n)) X) (root_finite_equiv n X e))
          (int_mul (v .fst .fst) (pos. (suc. n))) z (inverse Int z (int_mul (v .fst .fst) (pos. (suc. n))) (v .fst .snd))
          (root_period_from_scaled n X e (v .fst .fst) (v .snd))) s)

def scaled_multiples (m k : Nat)
  : Id (Subtypes Int) (ScaledSubtype m (Multiples k)) (Multiples (mul m k))
  ≔ inclusion_antisym Int (ScaledSubtype m (Multiples k)) (Multiples (mul m k))
      (z s ↦ mere_rec (ScaledWitness m (Multiples k) z) (Multiples (mul m k) z .fst) (Multiples (mul m k) z .snd)
        (v ↦ mere_rec (MultipleWitness k (v .fst .fst)) (Multiples (mul m k) z .fst) (Multiples (mul m k) z .snd)
          (u ↦ mere (MultipleWitness (mul m k) z) (u .fst, calc
            z = int_mul (v .fst .fst) (pos. m) by v .fst .snd
            = int_mul (int_mul (u .fst) (pos. k)) (pos. m)
              by refl ((y ↦ int_mul y (pos. m)) : Int → Int) (u .snd)
            = int_mul (u .fst) (pos. (mul k m))
              by inverse Int (int_mul (u .fst) (pos. (mul k m))) (int_mul (int_mul (u .fst) (pos. k)) (pos. m))
                (int_mul_pos_mul (u .fst) k m)
            = int_mul (u .fst) (pos. (mul m k))
              by refl ((y ↦ int_mul (u .fst) (pos. y)) : Nat → Int) (mul_comm k m) ∎)) (v .snd)) s)
      (z s ↦ mere_rec (MultipleWitness (mul m k) z) (ScaledSubtype m (Multiples k) z .fst)
        (ScaledSubtype m (Multiples k) z .snd)
        (u ↦ mere (ScaledWitness m (Multiples k) z)
          ((int_mul (u .fst) (pos. k), calc
            z = int_mul (u .fst) (pos. (mul m k)) by u .snd
            = int_mul (u .fst) (pos. (mul k m)) by refl ((y ↦ int_mul (u .fst) (pos. y)) : Nat → Int) (mul_comm m k)
            = int_mul (int_mul (u .fst) (pos. k)) (pos. m) by int_mul_pos_mul (u .fst) k m ∎),
           mere (MultipleWitness k (int_mul (u .fst) (pos. k))) (u .fst, refl (int_mul (u .fst) (pos. k))))) s)

def root_finite_standard_periods (n b : Nat)
  : Id (Subtypes Int) (CyclePeriods (finite_standard_cycle (add (mul (suc. n) b) n)))
      (CyclePeriods (cycle_root n (finite_standard_cycle b)))
  ≔ let N ≔ add (mul (suc. n) b) n in
    let c ≔ finite_standard_cycle b in
    calc
      CyclePeriods (finite_standard_cycle N) = Multiples (mul (suc. n) (suc. b)) by finite_standard_periods N
      = ScaledSubtype (suc. n) (Multiples (suc. b))
        by inverse (Subtypes Int) (ScaledSubtype (suc. n) (Multiples (suc. b))) (Multiples (mul (suc. n) (suc. b)))
          (scaled_multiples (suc. n) (suc. b))
      = ScaledSubtype (suc. n) (CyclePeriods c)
        by refl (ScaledSubtype (suc. n)) (inverse (Subtypes Int) (CyclePeriods c) (Multiples (suc. b)) (finite_standard_periods b))
      = CyclePeriods (cycle_root n c)
        by inverse (Subtypes Int) (CyclePeriods (cycle_root n c)) (ScaledSubtype (suc. n) (CyclePeriods c))
          (root_cycle_periods n c) ∎

{` lem:deg-m-on-Cyc: the identification pt_{mk} = root(pt_k), for the
   infinite index 0 and every positive index; m = suc n. `}
def root_principal_path (n k : Nat)
  : Id Cycles (principal_cycle (mul (suc. n) k)) (cycle_root n (principal_cycle k))
  ≔ match k [
  | zero. ↦ inverse Cycles (cycle_root n infinite_cycle) infinite_cycle (root_infinite_cycle_path n)
  | suc. b ↦ cycle_path_from_periods (finite_standard_cycle (add (mul (suc. n) b) n))
      (cycle_root n (finite_standard_cycle b)) (root_finite_standard_periods n b)
      (remainder_at (add (mul (suc. n) b) n) zero. star.) (inr. star., remainder_at b zero. star.) ]

def principal_component_point (k : Nat) : CycleComponent k
  ≔ (principal_cycle k, mere (Id Cycles (principal_cycle k) (principal_cycle k)) (refl (principal_cycle k)))

def cycle_root_component (n k : Nat) (u : CycleComponent k) : CycleComponent (mul (suc. n) k)
  ≔ (cycle_root n (u .fst), trunc_map native_truncation (Id Cycles (principal_cycle k) (u .fst))
      (Id Cycles (principal_cycle (mul (suc. n) k)) (cycle_root n (u .fst)))
      (p ↦ concat Cycles (principal_cycle (mul (suc. n) k)) (cycle_root n (principal_cycle k)) (cycle_root n (u .fst))
        (root_principal_path n k) (refl (cycle_root n) p)) (u .snd))

{` lem:deg-m-on-Cyc: the pointed maps Cyc_k → Cyc_{mk}; index 0 is Cyc_0. `}
def cycle_root_pointed (n k : Nat)
  : BookPointedMap (CycleComponent k, principal_component_point k)
      (CycleComponent (mul (suc. n) k), principal_component_point (mul (suc. n) k))
  ≔ (cycle_root_component n k,
      subtype_equal Cycles (c ↦ Mere (Id Cycles (principal_cycle (mul (suc. n) k)) c))
        (c ↦ mere_isprop (Id Cycles (principal_cycle (mul (suc. n) k)) c))
        (principal_component_point (mul (suc. n) k)) (cycle_root_component n k (principal_component_point k))
        (root_principal_path n k))
