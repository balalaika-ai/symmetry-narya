export "25-coverings"

def loop_power_nat (A : Type) (a : A) (l : Id A a a) (n : Nat) : Id A a a
  ≔ match n [ zero. ↦ refl a | suc. n ↦ concat A a a a (loop_power_nat A a l n) l ]

def loop_power (A : Type) (a : A) (l : Id A a a) (z : Int) : Id A a a
  ≔ match z [
  | pos. n ↦ loop_power_nat A a l n
  | neg. n ↦ loop_power_nat A a (inverse A a a l) (suc. n) ]

def concat_cancel_final_inverse (A : Type) (a : A) (p l : Id A a a)
  : Id (Id A a a) (concat A a a a (concat A a a a p (inverse A a a l)) l) p
  ≔ calc
      concat A a a a (concat A a a a p (inverse A a a l)) l
      = concat A a a a p (concat A a a a (inverse A a a l) l)
        by concat_assoc A a a a a p (inverse A a a l) l
      = concat A a a a p (refl a)
        by refl (concat A a a a p) (concat_inverse_left A a a l)
      = p by concat_p1 A a a p ∎

def loop_power_succ (A : Type) (a : A) (l : Id A a a) (z : Int)
  : Id (Id A a a) (concat A a a a (loop_power A a l z) l) (loop_power A a l (int_succ z))
  ≔ match z [
  | pos. n ↦ refl (loop_power_nat A a l (suc. n))
  | neg. zero. ↦ concat_cancel_final_inverse A a (refl a) l
  | neg. (suc. n) ↦ concat_cancel_final_inverse A a (loop_power_nat A a (inverse A a a l) (suc. n)) l ]

def transport_inverse_step (A : Type) (R : A → Type) (a : A) (l : Id A a a)
  (e : Int → R a)
  (step : (n : Int) → Id (R a) (transport A R a a l (e n)) (e (int_succ n)))
  (n : Int)
  : Id (R a) (transport A R a a (inverse A a a l) (e n)) (e (int_pred n))
  ≔ calc
      transport A R a a (inverse A a a l) (e n)
      = transport A R a a (inverse A a a l) (e (int_succ (int_pred n)))
        by refl ((m ↦ transport A R a a (inverse A a a l) (e m)) : Int → R a) (int_succ_pred n)
      = transport A R a a (inverse A a a l) (transport A R a a l (e (int_pred n)))
        by refl (transport A R a a (inverse A a a l)) (step (int_pred n))
      = e (int_pred n) by transport_inverse_roundtrip A R a a l (e (int_pred n)) ∎

def transport_positive_power (A : Type) (R : A → Type) (a : A) (l : Id A a a)
  (e : Int → R a)
  (step : (n : Int) → Id (R a) (transport A R a a l (e n)) (e (int_succ n)))
  (n : Nat)
  : Id (R a) (transport A R a a (loop_power_nat A a l n) (e int_zero)) (e (pos. n))
  ≔ match n [
  | zero. ↦ transport_refl A R a (e int_zero)
  | suc. n ↦ calc
      transport A R a a (loop_power_nat A a l (suc. n)) (e int_zero)
      = transport A R a a l (transport A R a a (loop_power_nat A a l n) (e int_zero))
        by transport_concat A R a a a (loop_power_nat A a l n) l (e int_zero)
      = transport A R a a l (e (pos. n))
        by refl (transport A R a a l) (transport_positive_power A R a l e step n)
      = e (pos. (suc. n)) by step (pos. n) ∎ ]

def transport_negative_power (A : Type) (R : A → Type) (a : A) (l : Id A a a)
  (e : Int → R a)
  (step : (n : Int) → Id (R a) (transport A R a a l (e n)) (e (int_succ n)))
  (n : Nat)
  : Id (R a) (transport A R a a (loop_power_nat A a (inverse A a a l) (suc. n)) (e int_zero)) (e (neg. n))
  ≔ match n [
  | zero. ↦ calc
      transport A R a a (loop_power_nat A a (inverse A a a l) (suc. zero.)) (e int_zero)
      = transport A R a a (inverse A a a l) (transport A R a a (refl a) (e int_zero))
        by transport_concat A R a a a (refl a) (inverse A a a l) (e int_zero)
      = transport A R a a (inverse A a a l) (e int_zero)
        by refl (transport A R a a (inverse A a a l)) (transport_refl A R a (e int_zero))
      = e (neg. zero.) by transport_inverse_step A R a l e step int_zero ∎
  | suc. n ↦ calc
      transport A R a a (loop_power_nat A a (inverse A a a l) (suc. (suc. n))) (e int_zero)
      = transport A R a a (inverse A a a l)
          (transport A R a a (loop_power_nat A a (inverse A a a l) (suc. n)) (e int_zero))
        by transport_concat A R a a a (loop_power_nat A a (inverse A a a l) (suc. n)) (inverse A a a l) (e int_zero)
      = transport A R a a (inverse A a a l) (e (neg. n))
        by refl (transport A R a a (inverse A a a l)) (transport_negative_power A R a l e step n)
      = e (neg. (suc. n)) by transport_inverse_step A R a l e step (neg. n) ∎ ]

def transport_loop_power (A : Type) (R : A → Type) (a : A) (l : Id A a a)
  (e : Int → R a)
  (step : (n : Int) → Id (R a) (transport A R a a l (e n)) (e (int_succ n)))
  (n : Int)
  : Id (R a) (transport A R a a (loop_power A a l n) (e int_zero)) (e n)
  ≔ match n [
  | pos. n ↦ transport_positive_power A R a l e step n
  | neg. n ↦ transport_negative_power A R a l e step n ]

def transport_iterated_action (A : Type) (R : A → Type) (a : A) (l : Id A a a)
  (X : Type) (f : X → X) (e : X → R a)
  (h : (x : X) → Id (R a) (transport A R a a l (e x)) (e (f x))) (n : Nat) (x : X)
  : Id (R a) (transport A R a a (loop_power_nat A a l n) (e x)) (e (iterate X f n x))
  ≔ match n [
  | zero. ↦ transport_refl A R a (e x)
  | suc. n ↦ calc
      transport A R a a (loop_power_nat A a l (suc. n)) (e x)
      = transport A R a a l (transport A R a a (loop_power_nat A a l n) (e x))
        by transport_concat A R a a a (loop_power_nat A a l n) l (e x)
      = transport A R a a l (e (iterate X f n x))
        by refl (transport A R a a l) (transport_iterated_action A R a l X f e h n x)
      = e (iterate X f (suc. n) x) by h (iterate X f n x) ∎ ]

def transport_power_at (A : Type) (R : A → Type) (a : A) (l : Id A a a)
  (e : Int → R a)
  (step : (n : Int) → Id (R a) (transport A R a a l (e n)) (e (int_succ n))) (k n : Int)
  : Id (R a) (transport A R a a (loop_power A a l n) (e k)) (e (int_add k n))
  ≔ match n [
  | pos. n ↦ transport_iterated_action A R a l Int int_succ e step n k
  | neg. n ↦ transport_iterated_action A R a (inverse A a a l) Int int_pred e
      (transport_inverse_step A R a l e step) (suc. n) k ]
