export "56-integer-radix"

def permutation_power (A : Type) (e : Equiv A A) (z : Int) (x : A) : A
  ≔ int_iterate A (e .map) (equiv_inverse_map A A e) z x

def permutation_power_succ (A : Type) (e : Equiv A A) (z : Int) (x : A)
  : Id A (permutation_power A e (int_succ z) x) (e .map (permutation_power A e z x))
  ≔ match z [
  | pos. n ↦ refl (e .map (iterate A (e .map) n x))
  | neg. zero. ↦ inverse A (e .map (equiv_inverse_map A A e x)) x (equiv_counit A A e x)
  | neg. (suc. n) ↦ inverse A
      (e .map (equiv_inverse_map A A e (iterate A (equiv_inverse_map A A e) (suc. n) x)))
      (iterate A (equiv_inverse_map A A e) (suc. n) x)
      (equiv_counit A A e (iterate A (equiv_inverse_map A A e) (suc. n) x)) ]

def permutation_power_pred (A : Type) (e : Equiv A A) (z : Int) (x : A)
  : Id A (permutation_power A e (int_pred z) x) (equiv_inverse_map A A e (permutation_power A e z x))
  ≔ match z [
  | pos. zero. ↦ refl (equiv_inverse_map A A e x)
  | pos. (suc. n) ↦ equiv_unit A A e (iterate A (e .map) n x)
  | neg. n ↦ refl (equiv_inverse_map A A e (iterate A (equiv_inverse_map A A e) (suc. n) x)) ]

def permutation_power_positive_shift (A : Type) (e : Equiv A A) (z : Int) (n : Nat) (x : A)
  : Id A (permutation_power A e (iterate Int int_succ n z) x) (iterate A (e .map) n (permutation_power A e z x))
  ≔ match n [
  | zero. ↦ refl (permutation_power A e z x)
  | suc. n ↦ calc
      permutation_power A e (int_succ (iterate Int int_succ n z)) x
      = e .map (permutation_power A e (iterate Int int_succ n z) x)
        by permutation_power_succ A e (iterate Int int_succ n z) x
      = e .map (iterate A (e .map) n (permutation_power A e z x))
        by refl (e .map) (permutation_power_positive_shift A e z n x) ∎ ]

def permutation_power_negative_shift (A : Type) (e : Equiv A A) (z : Int) (n : Nat) (x : A)
  : Id A (permutation_power A e (iterate Int int_pred n z) x)
      (iterate A (equiv_inverse_map A A e) n (permutation_power A e z x))
  ≔ match n [
  | zero. ↦ refl (permutation_power A e z x)
  | suc. n ↦ calc
      permutation_power A e (int_pred (iterate Int int_pred n z)) x
      = equiv_inverse_map A A e (permutation_power A e (iterate Int int_pred n z) x)
        by permutation_power_pred A e (iterate Int int_pred n z) x
      = equiv_inverse_map A A e (iterate A (equiv_inverse_map A A e) n (permutation_power A e z x))
        by refl (equiv_inverse_map A A e) (permutation_power_negative_shift A e z n x) ∎ ]

def permutation_power_add (A : Type) (e : Equiv A A) (z w : Int) (x : A)
  : Id A (permutation_power A e (int_add z w) x) (permutation_power A e w (permutation_power A e z x))
  ≔ match w [
  | pos. n ↦ permutation_power_positive_shift A e z n x
  | neg. n ↦ permutation_power_negative_shift A e z (suc. n) x ]

def permutation_power_inverse (A : Type) (e : Equiv A A) (z : Int) (x : A)
  : Id A (permutation_power A e (int_neg z) (permutation_power A e z x)) x
  ≔ calc
      permutation_power A e (int_neg z) (permutation_power A e z x)
      = permutation_power A e (int_add z (int_neg z)) x by permutation_power_add A e z (int_neg z) x
      = x by refl ((n ↦ permutation_power A e n x) : Int → A) (int_add_neg_right z) ∎

def permutation_power_inverse_other (A : Type) (e : Equiv A A) (z : Int) (x : A)
  : Id A (permutation_power A e z (permutation_power A e (int_neg z) x)) x
  ≔ calc
      permutation_power A e z (permutation_power A e (int_neg z) x)
      = permutation_power A e (int_add (int_neg z) z) x by permutation_power_add A e (int_neg z) z x
      = x by refl ((n ↦ permutation_power A e n x) : Int → A) (int_add_neg_left z) ∎

def permutation_power_equiv (A : Type) (e : Equiv A A) (z : Int) : Equiv A A
  ≔ quasi_inverse_equiv A A (permutation_power A e z) (permutation_power A e (int_neg z))
      (permutation_power_inverse A e z) (permutation_power_inverse_other A e z)

def iterate_intertwine (A B : Type) (f : A → A) (g : B → B) (h : A → B)
  (step : (x : A) → Id B (h (f x)) (g (h x))) (n : Nat) (x : A)
  : Id B (h (iterate A f n x)) (iterate B g n (h x))
  ≔ match n [
  | zero. ↦ refl (h x)
  | suc. n ↦ concat B (h (f (iterate A f n x))) (g (h (iterate A f n x))) (g (iterate B g n (h x)))
      (step (iterate A f n x)) (refl g (iterate_intertwine A B f g h step n x)) ]

def inverse_intertwine (A B : Type) (e : Equiv A A) (f : Equiv B B) (h : A → B)
  (step : (x : A) → Id B (h (e .map x)) (f .map (h x))) (x : A)
  : Id B (h (equiv_inverse_map A A e x)) (equiv_inverse_map B B f (h x))
  ≔ calc
      h (equiv_inverse_map A A e x)
      = equiv_inverse_map B B f (f .map (h (equiv_inverse_map A A e x)))
        by equiv_unit B B f (h (equiv_inverse_map A A e x))
      = equiv_inverse_map B B f (h (e .map (equiv_inverse_map A A e x)))
        by refl (equiv_inverse_map B B f) (step (equiv_inverse_map A A e x))
      = equiv_inverse_map B B f (h x)
        by refl ((a ↦ equiv_inverse_map B B f (h a)) : A → B) (equiv_counit A A e x) ∎

def permutation_power_intertwine (A B : Type) (e : Equiv A A) (f : Equiv B B) (h : A → B)
  (step : (x : A) → Id B (h (e .map x)) (f .map (h x))) (z : Int) (x : A)
  : Id B (h (permutation_power A e z x)) (permutation_power B f z (h x))
  ≔ match z [
  | pos. n ↦ iterate_intertwine A B (e .map) (f .map) h step n x
  | neg. n ↦ iterate_intertwine A B (equiv_inverse_map A A e) (equiv_inverse_map B B f) h
      (inverse_intertwine A B e f h step) (suc. n) x ]
