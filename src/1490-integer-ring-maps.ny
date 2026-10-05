export "1413-dimension-invariance"
export "1310-integer-ring"

{` Chapter 14 (transfer of the ℤ[φ] computation, module 1492):
   the canonical map ℤ → R into any ring, n ↦ n·1 and -(n+1) ↦ -((n+1)·1),
   and its compatibility with successor, predecessor, addition, negation
   and multiplication of the integers of chapter 3 (int_add and int_mul are
   iterated successor/predecessor and iterated addition). `}

def int_to_ring (R : AbstractRing) (x : Int) : R .carrier
  ≔ match x [ pos. n ↦ ring_of_nat R n | neg. n ↦ R .neg (ring_of_nat R (suc. n)) ]

def ring_neg_add (R : AbstractRing) (a b : R .carrier)
  : Id (R .carrier) (R .neg (R .add a b)) (R .add (R .neg a) (R .neg b))
  ≔ concat (R .carrier) (R .neg (R .add a b)) (R .add (R .neg b) (R .neg a)) (R .add (R .neg a) (R .neg b))
      (ag_inv_mul (ring_additive_group R) a b) (ring_add_comm R (R .neg b) (R .neg a))

def int_to_ring_succ (R : AbstractRing) (x : Int)
  : Id (R .carrier) (int_to_ring R (int_succ x)) (R .add (int_to_ring R x) (R .one))
  ≔ let S ≔ R .carrier in let a ≔ R .add in let ng ≔ R .neg in let z ≔ R .zero in let o ≔ R .one in
    let G ≔ ring_additive_group R in
    match x [
    | pos. n ↦ refl (a (ring_of_nat R n) o)
    | neg. zero. ↦
      calc
        z = a (ng o) o by inverse S (a (ng o) o) z (ag_inv_left G o)
        = a (ng (a z o)) o by refl ((y ↦ a (ng y) o) : S → S) (inverse S (a z o) o (R .add_laws .unit_left o)) ∎
    | neg. (suc. n) ↦
      let t ≔ ring_of_nat R (suc. n) in
      calc
        ng t = a (ng t) z by inverse S (a (ng t) z) (ng t) (R .add_laws .unit_right (ng t))
        = a (ng t) (a (ng o) o) by refl (a (ng t)) (inverse S (a (ng o) o) z (ag_inv_left G o))
        = a (a (ng t) (ng o)) o by ring_add_assoc R (ng t) (ng o) o
        = a (ng (a t o)) o by refl ((y ↦ a y o) : S → S) (inverse S (ng (a t o)) (a (ng t) (ng o)) (ring_neg_add R t o)) ∎ ]

def int_to_ring_pred (R : AbstractRing) (x : Int)
  : Id (R .carrier) (int_to_ring R (int_pred x)) (R .add (int_to_ring R x) (R .neg (R .one)))
  ≔ let S ≔ R .carrier in let a ≔ R .add in let ng ≔ R .neg in let z ≔ R .zero in let o ≔ R .one in
    match x [
    | pos. zero. ↦
      calc
        ng (a z o) = ng o by refl ng (R .add_laws .unit_left o)
        = a z (ng o) by inverse S (a z (ng o)) (ng o) (R .add_laws .unit_left (ng o)) ∎
    | pos. (suc. n) ↦
      let t ≔ ring_of_nat R n in
      calc
        t = a t z by inverse S (a t z) t (R .add_laws .unit_right t)
        = a t (a o (ng o)) by refl (a t) (inverse S (a o (ng o)) z (R .add_laws .inv_right o))
        = a (a t o) (ng o) by ring_add_assoc R t o (ng o) ∎
    | neg. n ↦ ring_neg_add R (ring_of_nat R (suc. n)) o ]

def int_to_ring_iterate_succ (R : AbstractRing) (x : Int) (n : Nat)
  : Id (R .carrier) (int_to_ring R (iterate Int int_succ n x)) (R .add (int_to_ring R x) (ring_of_nat R n))
  ≔ let S ≔ R .carrier in let a ≔ R .add in let f ≔ int_to_ring R in
    match n [
    | zero. ↦ inverse S (a (f x) (R .zero)) (f x) (R .add_laws .unit_right (f x))
    | suc. n ↦
      calc
        f (int_succ (iterate Int int_succ n x)) = a (f (iterate Int int_succ n x)) (R .one)
          by int_to_ring_succ R (iterate Int int_succ n x)
        = a (a (f x) (ring_of_nat R n)) (R .one) by refl ((y ↦ a y (R .one)) : S → S) (int_to_ring_iterate_succ R x n)
        = a (f x) (a (ring_of_nat R n) (R .one))
          by inverse S (a (f x) (a (ring_of_nat R n) (R .one))) (a (a (f x) (ring_of_nat R n)) (R .one))
               (ring_add_assoc R (f x) (ring_of_nat R n) (R .one)) ∎ ]

def int_to_ring_iterate_pred (R : AbstractRing) (x : Int) (m : Nat)
  : Id (R .carrier) (int_to_ring R (iterate Int int_pred m x)) (R .add (int_to_ring R x) (R .neg (ring_of_nat R m)))
  ≔ let S ≔ R .carrier in let a ≔ R .add in let ng ≔ R .neg in let f ≔ int_to_ring R in
    match m [
    | zero. ↦
      calc
        f x = a (f x) (R .zero) by inverse S (a (f x) (R .zero)) (f x) (R .add_laws .unit_right (f x))
        = a (f x) (ng (R .zero)) by refl (a (f x)) (inverse S (ng (R .zero)) (R .zero) (ag_inv_unit (ring_additive_group R))) ∎
    | suc. m ↦
      let t ≔ ring_of_nat R m in
      calc
        f (int_pred (iterate Int int_pred m x)) = a (f (iterate Int int_pred m x)) (ng (R .one))
          by int_to_ring_pred R (iterate Int int_pred m x)
        = a (a (f x) (ng t)) (ng (R .one)) by refl ((y ↦ a y (ng (R .one))) : S → S) (int_to_ring_iterate_pred R x m)
        = a (f x) (a (ng t) (ng (R .one)))
          by inverse S (a (f x) (a (ng t) (ng (R .one)))) (a (a (f x) (ng t)) (ng (R .one))) (ring_add_assoc R (f x) (ng t) (ng (R .one)))
        = a (f x) (ng (a t (R .one)))
          by refl (a (f x)) (inverse S (ng (a t (R .one))) (a (ng t) (ng (R .one))) (ring_neg_add R t (R .one))) ∎ ]

def int_to_ring_add (R : AbstractRing) (x y : Int)
  : Id (R .carrier) (int_to_ring R (int_add x y)) (R .add (int_to_ring R x) (int_to_ring R y))
  ≔ match y [
    | pos. n ↦ int_to_ring_iterate_succ R x n
    | neg. n ↦ int_to_ring_iterate_pred R x (suc. n) ]

def int_to_ring_neg (R : AbstractRing) (x : Int)
  : Id (R .carrier) (int_to_ring R (int_neg x)) (R .neg (int_to_ring R x))
  ≔ let S ≔ R .carrier in let G ≔ ring_additive_group R in
    match x [
    | pos. zero. ↦ inverse S (R .neg (R .zero)) (R .zero) (ag_inv_unit G)
    | pos. (suc. n) ↦ refl (R .neg (ring_of_nat R (suc. n)))
    | neg. n ↦ inverse S (R .neg (R .neg (ring_of_nat R (suc. n)))) (ring_of_nat R (suc. n)) (ag_inv_inv G (ring_of_nat R (suc. n))) ]

def int_to_ring_iterate_add (R : AbstractRing) (y : Int) (n : Nat)
  : Id (R .carrier) (int_to_ring R (iterate Int (int_add y) n int_zero)) (R .mul (int_to_ring R y) (ring_of_nat R n))
  ≔ let S ≔ R .carrier in let a ≔ R .add in let m ≔ R .mul in let f ≔ int_to_ring R in
    match n [
    | zero. ↦ inverse S (m (f y) (R .zero)) (R .zero) (ring_mul_zero_right R (f y))
    | suc. n ↦
      let t ≔ ring_of_nat R n in
      let it ≔ iterate Int (int_add y) n int_zero in
      calc
        f (int_add y it) = a (f y) (f it) by int_to_ring_add R y it
        = a (f y) (m (f y) t) by refl (a (f y)) (int_to_ring_iterate_add R y n)
        = a (m (f y) t) (f y) by ring_add_comm R (f y) (m (f y) t)
        = a (m (f y) t) (m (f y) (R .one)) by refl (a (m (f y) t)) (inverse S (m (f y) (R .one)) (f y) (ring_mul_one_right R (f y)))
        = m (f y) (a t (R .one)) by inverse S (m (f y) (a t (R .one))) (a (m (f y) t) (m (f y) (R .one))) (ring_ldistr R (f y) t (R .one)) ∎ ]

def int_to_ring_mul (R : AbstractRing) (x y : Int)
  : Id (R .carrier) (int_to_ring R (int_mul x y)) (R .mul (int_to_ring R x) (int_to_ring R y))
  ≔ let S ≔ R .carrier in let m ≔ R .mul in let f ≔ int_to_ring R in
    match y [
    | pos. n ↦ int_to_ring_iterate_add R x n
    | neg. n ↦
      let t ≔ ring_of_nat R (suc. n) in
      calc
        f (iterate Int (int_add (int_neg x)) (suc. n) int_zero) = m (f (int_neg x)) t by int_to_ring_iterate_add R (int_neg x) (suc. n)
        = m (R .neg (f x)) t by refl ((u ↦ m u t) : S → S) (int_to_ring_neg R x)
        = R .neg (m (f x) t) by ring_mul_neg_left R (f x) t
        = m (f x) (R .neg t) by inverse S (m (f x) (R .neg t)) (R .neg (m (f x) t)) (ring_mul_neg_right R (f x) t) ∎ ]
