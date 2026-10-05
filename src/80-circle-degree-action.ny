export "79-decidable-covering-components"

def map_loop_power_nat (A B : Type) (f : A → B) (a : A) (l : Id A a a) (n : Nat)
  : Id (Id B (f a) (f a)) (refl f (loop_power_nat A a l n)) (loop_power_nat B (f a) (refl f l) n)
  ≔ match n [
  | zero. ↦ refl (refl (f a))
  | suc. n ↦ concat (Id B (f a) (f a))
      (refl f (loop_power_nat A a l (suc. n)))
      (concat B (f a) (f a) (f a) (refl f (loop_power_nat A a l n)) (refl f l))
      (loop_power_nat B (f a) (refl f l) (suc. n))
      (map_path_concat A B f a a a (loop_power_nat A a l n) l)
      (refl ((p ↦ concat B (f a) (f a) (f a) p (refl f l)) : Id B (f a) (f a) → Id B (f a) (f a))
        (map_loop_power_nat A B f a l n)) ]

def map_loop_power (A B : Type) (f : A → B) (a : A) (l : Id A a a) (z : Int)
  : Id (Id B (f a) (f a)) (refl f (loop_power A a l z)) (loop_power B (f a) (refl f l) z)
  ≔ match z [
  | pos. n ↦ map_loop_power_nat A B f a l n
  | neg. n ↦ concat (Id B (f a) (f a))
      (refl f (loop_power_nat A a (inverse A a a l) (suc. n)))
      (loop_power_nat B (f a) (refl f (inverse A a a l)) (suc. n))
      (loop_power_nat B (f a) (inverse B (f a) (f a) (refl f l)) (suc. n))
      (map_loop_power_nat A B f a (inverse A a a l) (suc. n))
      (refl ((p ↦ loop_power_nat B (f a) p (suc. n)) : Id B (f a) (f a) → Id B (f a) (f a))
        (map_path_inverse A B f a a l)) ]

def circle_winding_inverse (C : CircleSignature) (p : Id (C .carrier) (C .base) (C .base))
  : Id Int (circle_winding C (inverse (C .carrier) (C .base) (C .base) p)) (int_neg (circle_winding C p))
  ≔ int_neg_unique (circle_winding C p) (circle_winding C (inverse (C .carrier) (C .base) (C .base) p))
      (calc
        int_add (circle_winding C p) (circle_winding C (inverse (C .carrier) (C .base) (C .base) p))
        = circle_winding C (concat (C .carrier) (C .base) (C .base) (C .base) p (inverse (C .carrier) (C .base) (C .base) p))
          by circle_winding_composition C p (inverse (C .carrier) (C .base) (C .base) p)
        = circle_winding C (refl (C .base))
          by refl (circle_winding C) (concat_inverse_right (C .carrier) (C .base) (C .base) p)
        = int_zero by circle_winding_refl C ∎)

def circle_winding_iterate (C : CircleSignature) (p : Id (C .carrier) (C .base) (C .base)) (n : Nat)
  : Id Int (circle_winding C (loop_power_nat (C .carrier) (C .base) p n))
      (iterate Int (int_add (circle_winding C p)) n int_zero)
  ≔ match n [
  | zero. ↦ circle_winding_refl C
  | suc. n ↦ calc
      circle_winding C (loop_power_nat (C .carrier) (C .base) p (suc. n))
      = int_add (circle_winding C (loop_power_nat (C .carrier) (C .base) p n)) (circle_winding C p)
        by circle_winding_composition C (loop_power_nat (C .carrier) (C .base) p n) p
      = int_add (circle_winding C p) (circle_winding C (loop_power_nat (C .carrier) (C .base) p n))
        by int_add_comm (circle_winding C (loop_power_nat (C .carrier) (C .base) p n)) (circle_winding C p)
      = iterate Int (int_add (circle_winding C p)) (suc. n) int_zero
        by refl (int_add (circle_winding C p)) (circle_winding_iterate C p n) ∎ ]

def circle_winding_power_arbitrary (C : CircleSignature) (p : Id (C .carrier) (C .base) (C .base)) (z : Int)
  : Id Int (circle_winding C (loop_power (C .carrier) (C .base) p z)) (int_mul (circle_winding C p) z)
  ≔ match z [
  | pos. n ↦ circle_winding_iterate C p n
  | neg. n ↦ concat Int
      (circle_winding C (loop_power_nat (C .carrier) (C .base) (inverse (C .carrier) (C .base) (C .base) p) (suc. n)))
      (iterate Int (int_add (circle_winding C (inverse (C .carrier) (C .base) (C .base) p))) (suc. n) int_zero)
      (int_mul (circle_winding C p) (neg. n))
      (circle_winding_iterate C (inverse (C .carrier) (C .base) (C .base) p) (suc. n))
      (refl ((k ↦ iterate Int (int_add k) (suc. n) int_zero) : Int → Int) (circle_winding_inverse C p)) ]

def free_loop_power (A : Type) (z : Int) (t : FreeLoop A) : FreeLoop A
  ≔ (t .fst, loop_power A (t .fst) (t .snd) z)

{` def:dgm-map. Defined also at zero; the covering theorem requires m>0. `}
def circle_degree_map (C : CircleSignature) (m : Nat) : C .carrier → C .carrier
  ≔ circle_rec C (C .carrier) (C .base, loop_power_nat (C .carrier) (C .base) (C .loop) m)

def circle_degree_boundary (C : CircleSignature) (m : Nat)
  : Id (FreeLoop (C .carrier)) (circle_eval C (C .carrier) (circle_degree_map C m))
      (C .base, loop_power_nat (C .carrier) (C .base) (C .loop) m)
  ≔ circle_rec_beta C (C .carrier) (C .base, loop_power_nat (C .carrier) (C .base) (C .loop) m)

def circle_degree_based_action (C : CircleSignature) (m : Nat) (p : Id (C .carrier) (C .base) (C .base))
  : Id (C .carrier) (C .base) (C .base)
  ≔ transport (C .carrier) (x ↦ Id (C .carrier) x x)
      (circle_degree_map C m (C .base)) (C .base) (circle_degree_boundary C m .fst) (refl (circle_degree_map C m) p)

def circle_degree_action_power (C : CircleSignature) (m : Nat) (z : Int)
  : Id (Id (C .carrier) (C .base) (C .base))
      (circle_degree_based_action C m (loop_power (C .carrier) (C .base) (C .loop) z))
      (loop_power (C .carrier) (C .base) (loop_power_nat (C .carrier) (C .base) (C .loop) m) z)
  ≔ let f ≔ circle_degree_map C m in
    let q ≔ circle_degree_boundary C m in
    let tr ≔ transport (C .carrier) (x ↦ Id (C .carrier) x x) (f (C .base)) (C .base) (q .fst) in
    concat (Id (C .carrier) (C .base) (C .base))
      (circle_degree_based_action C m (loop_power (C .carrier) (C .base) (C .loop) z))
      (tr (loop_power (C .carrier) (f (C .base)) (refl f (C .loop)) z))
      (loop_power (C .carrier) (C .base) (loop_power_nat (C .carrier) (C .base) (C .loop) m) z)
      (refl tr (map_loop_power (C .carrier) (C .carrier) f (C .base) (C .loop) z))
      (pathover_transport_equiv (C .carrier) (x ↦ Id (C .carrier) x x) (f (C .base)) (C .base) (q .fst)
        (loop_power (C .carrier) (f (C .base)) (refl f (C .loop)) z)
        (loop_power (C .carrier) (C .base) (loop_power_nat (C .carrier) (C .base) (C .loop) m) z)
        .map (refl (free_loop_power (C .carrier) z) q .snd))

def circle_degree_winding (C : CircleSignature) (m : Nat) (p : Id (C .carrier) (C .base) (C .base))
  : Id Int (circle_winding C (circle_degree_based_action C m p)) (int_mul (pos. m) (circle_winding C p))
  ≔ calc
      circle_winding C (circle_degree_based_action C m p)
      = circle_winding C (circle_degree_based_action C m (loop_power (C .carrier) (C .base) (C .loop) (circle_winding C p)))
        by refl ((r ↦ circle_winding C (circle_degree_based_action C m r)) : Id (C .carrier) (C .base) (C .base) → Int)
          (circle_power_winding C p)
      = circle_winding C (loop_power (C .carrier) (C .base) (loop_power_nat (C .carrier) (C .base) (C .loop) m) (circle_winding C p))
        by refl (circle_winding C) (circle_degree_action_power C m (circle_winding C p))
      = int_mul (circle_winding C (loop_power_nat (C .carrier) (C .base) (C .loop) m)) (circle_winding C p)
        by circle_winding_power_arbitrary C (loop_power_nat (C .carrier) (C .base) (C .loop) m) (circle_winding C p)
      = int_mul (pos. m) (circle_winding C p)
        by refl ((k ↦ int_mul k (circle_winding C p)) : Int → Int) (circle_winding_power C (pos. m)) ∎

def circle_degree_action_is_power (C : CircleSignature) (m : Nat) (p : Id (C .carrier) (C .base) (C .base))
  : Id (Id (C .carrier) (C .base) (C .base))
      (circle_degree_based_action C m p) (loop_power_nat (C .carrier) (C .base) p m)
  ≔ equivalence_injective (Id (C .carrier) (C .base) (C .base)) Int
      (native_equivalence (Id (C .carrier) (C .base) (C .base)) Int (circle_loop_integer_equiv C))
      (circle_degree_based_action C m p) (loop_power_nat (C .carrier) (C .base) p m) (calc
        circle_winding C (circle_degree_based_action C m p) = int_mul (pos. m) (circle_winding C p)
          by circle_degree_winding C m p
        = int_mul (circle_winding C p) (pos. m) by int_mul_comm (pos. m) (circle_winding C p)
        = circle_winding C (loop_power_nat (C .carrier) (C .base) p m) by circle_winding_power_arbitrary C p (pos. m) ∎)
