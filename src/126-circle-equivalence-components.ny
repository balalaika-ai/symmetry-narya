export "125-integer-units"

def circle_general_winding_power (C : CircleSignature) (x : C .carrier)
  (p : Id (C .carrier) x x) (z : Int)
  : Id Int (circle_general_winding C x (loop_power (C .carrier) x p z))
      (int_mul (circle_general_winding C x p) z)
  ≔ circle_ind_prop C
      (x ↦ (p : Id (C .carrier) x x) → (z : Int) →
        Id Int (circle_general_winding C x (loop_power (C .carrier) x p z))
          (int_mul (circle_general_winding C x p) z))
      (x ↦ pi_prop (Id (C .carrier) x x)
        (p ↦ (z : Int) → Id Int (circle_general_winding C x (loop_power (C .carrier) x p z))
          (int_mul (circle_general_winding C x p) z))
        (p ↦ pi_prop Int
          (z ↦ Id Int (circle_general_winding C x (loop_power (C .carrier) x p z))
            (int_mul (circle_general_winding C x p) z))
          (z ↦ int_set (circle_general_winding C x (loop_power (C .carrier) x p z))
            (int_mul (circle_general_winding C x p) z))))
      (p z ↦ calc
        circle_general_winding C (C .base) (loop_power (C .carrier) (C .base) p z)
        = circle_winding C (loop_power (C .carrier) (C .base) p z)
          by circle_general_winding_base_value C (loop_power (C .carrier) (C .base) p z)
        = int_mul (circle_winding C p) z by circle_winding_power_arbitrary C p z
        = int_mul (circle_general_winding C (C .base) p) z
          by refl ((k ↦ int_mul k z) : Int → Int) (circle_general_winding_base_value C p) ∎) x p z

def circle_map_winding_power (C : CircleSignature) (f : C .carrier → C .carrier) (z : Int)
  : Id Int (circle_general_winding C (f (C .base))
      (refl f (loop_power (C .carrier) (C .base) (C .loop) z))) (int_mul (circle_map_degree C f) z)
  ≔ calc
      circle_general_winding C (f (C .base)) (refl f (loop_power (C .carrier) (C .base) (C .loop) z))
      = circle_general_winding C (f (C .base)) (loop_power (C .carrier) (f (C .base)) (refl f (C .loop)) z)
        by refl (circle_general_winding C (f (C .base)))
          (map_loop_power (C .carrier) (C .carrier) f (C .base) (C .loop) z)
      = int_mul (circle_map_degree C f) z
        by circle_general_winding_power C (f (C .base)) (refl f (C .loop)) z ∎

def circle_equivalence_integer_action (C : CircleSignature) (e : Equiv (C .carrier) (C .carrier))
  : Equiv Int Int
  ≔ compose_equiv Int (Id (C .carrier) (e .map (C .base)) (e .map (C .base))) Int
      (compose_equiv Int (Id (C .carrier) (C .base) (C .base))
        (Id (C .carrier) (e .map (C .base)) (e .map (C .base)))
        (native_equivalence Int (Id (C .carrier) (C .base) (C .base)) (circle_integer_loop_equiv C))
        (equivalence_on_paths (C .carrier) (C .carrier) e (C .base) (C .base)))
      (circle_general_winding_equiv C (e .map (C .base)))

def integer_multiplication_equiv_sign (x : Int) (action : Equiv Int Int)
  (h : (z : Int) → Id Int (action .map z) (int_mul x z)) : IntegerUnitSign x
  ≔
    let y ≔ equiv_inverse_map Int Int action (pos. (suc. zero.)) in
    integer_unit_sign x y (calc
      int_mul x y = action .map y by h y
      = (pos. (suc. zero.) : Int) by equiv_counit Int Int action (pos. (suc. zero.)) ∎)

def circle_equivalence_degree_sign (C : CircleSignature) (e : Equiv (C .carrier) (C .carrier))
  : IntegerUnitSign (circle_map_degree C (e .map))
  ≔ integer_multiplication_equiv_sign (circle_map_degree C (e .map))
      (circle_equivalence_integer_action C e) (circle_map_winding_power C (e .map))

{` The displayed product in xca:S1=S1-components. The equalities are
   equalities of functions, as in the preceding component statement. `}
def circle_equivalence_two_components (C : CircleSignature) (e : Equiv (C .carrier) (C .carrier))
  : Sum (Mere (Id (C .carrier → C .carrier) (identity (C .carrier)) (e .map)))
      (Mere (Id (C .carrier → C .carrier) (circle_reflection C) (e .map)))
  ≔ match circle_equivalence_degree_sign C e [
  | inl. p ↦ inl. (circle_equal_degree_component C (identity (C .carrier)) (e .map) (calc
      circle_map_degree C (identity (C .carrier)) = (pos. (suc. zero.) : Int) by circle_degree_identity C
      = circle_map_degree C (e .map) by p ∎))
  | inr. p ↦ inr. (circle_equal_degree_component C (circle_reflection C) (e .map) (calc
      circle_map_degree C (circle_reflection C) = (neg. zero. : Int) by circle_degree_reflection C
      = circle_map_degree C (e .map) by p ∎)) ]

def book_circle_equivalence_two_components (C : CircleSignature) (e : BookEquiv (C .carrier) (C .carrier))
  : Sum (Mere (Id (C .carrier → C .carrier) (identity (C .carrier)) (e .map)))
      (Mere (Id (C .carrier → C .carrier) (circle_reflection C) (e .map)))
  ≔ circle_equivalence_two_components C (native_equivalence (C .carrier) (C .carrier) e)
