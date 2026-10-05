export "93-infinite-cycle-loop-coordinates"

def inverse_evaluation_agreement (A B X : Type) (e : Equiv A B) (f : A → X) (g : B → X)
  (agreement : (a : A) → Id X (f a) (g (e .map a))) (b : B)
  : Id X (f (equiv_inverse_map A B e b)) (g b)
  ≔ concat X (f (equiv_inverse_map A B e b)) (g (e .map (equiv_inverse_map A B e b))) (g b)
      (agreement (equiv_inverse_map A B e b)) (refl g (equiv_counit A B e b))

def integer_cycle_power_isomorphism (z : Int) : PermutationIsomorphisms (infinite_cycle .fst) (infinite_cycle .fst)
  ≔ (permutation_power_equiv Int int_succ_equiv z,
      x ↦ permutation_powers_commute Int int_succ_equiv z (pos. (suc. zero.)) x)

def integer_cycle_power_path (z : Int) : Id Cycles infinite_cycle infinite_cycle
  ≔ equiv_inverse_map (Id Cycles infinite_cycle infinite_cycle)
      (PermutationIsomorphisms (infinite_cycle .fst) (infinite_cycle .fst))
      (cycle_paths_equiv infinite_cycle infinite_cycle) (integer_cycle_power_isomorphism z)

def integer_cycle_power_evaluation (z : Int)
  : Id Int (cycle_path_evaluate infinite_cycle infinite_cycle (integer_cycle_power_path z) int_zero) z
  ≔ concat Int (cycle_path_evaluate infinite_cycle infinite_cycle (integer_cycle_power_path z) int_zero)
      (int_add int_zero z) z
      (inverse_evaluation_agreement (Id Cycles infinite_cycle infinite_cycle)
        (PermutationIsomorphisms (infinite_cycle .fst) (infinite_cycle .fst)) Int
        (cycle_paths_equiv infinite_cycle infinite_cycle)
        (p ↦ cycle_path_evaluate infinite_cycle infinite_cycle p int_zero) (h ↦ h .fst .map int_zero)
        (p ↦ refl (cycle_path_evaluate infinite_cycle infinite_cycle p int_zero)) (integer_cycle_power_isomorphism z))
      (int_add_zero_left z)

def integer_endomorphism_power_path (z : Int) : Id Endomorphisms integer_endomorphism integer_endomorphism
  ≔ cycle_endomorphism_paths infinite_cycle infinite_cycle .map (integer_cycle_power_path z)

def integer_endomorphism_power_evaluation (z : Int)
  : Id Int (endomorphism_path_evaluate integer_endomorphism integer_endomorphism
      (integer_endomorphism_power_path z) int_zero) z
  ≔ integer_cycle_power_evaluation z

def int_predecessor_equiv : Equiv Int Int
  ≔ set_iso_equiv Int Int int_set int_pred int_succ int_succ_pred int_pred_succ

def integer_predecessor_commutes : Commutes Int Int int_succ_equiv int_succ_equiv int_pred
  ≔ z ↦ concat Int (int_pred (int_succ z)) z (int_succ (int_pred z))
      (int_pred_succ z) (inverse Int (int_succ (int_pred z)) z (int_succ_pred z))

def integer_predecessor_isomorphism : PermutationIsomorphisms (infinite_cycle .fst) (infinite_cycle .fst)
  ≔ (int_predecessor_equiv, integer_predecessor_commutes)

def integer_predecessor_cycle_path : Id Cycles infinite_cycle infinite_cycle
  ≔ equiv_inverse_map (Id Cycles infinite_cycle infinite_cycle)
      (PermutationIsomorphisms (infinite_cycle .fst) (infinite_cycle .fst))
      (cycle_paths_equiv infinite_cycle infinite_cycle) integer_predecessor_isomorphism

def integer_predecessor_cycle_evaluation (z : Int)
  : Id Int (cycle_path_evaluate infinite_cycle infinite_cycle integer_predecessor_cycle_path z) (int_pred z)
  ≔ inverse_evaluation_agreement (Id Cycles infinite_cycle infinite_cycle)
      (PermutationIsomorphisms (infinite_cycle .fst) (infinite_cycle .fst)) Int
      (cycle_paths_equiv infinite_cycle infinite_cycle)
      (p ↦ cycle_path_evaluate infinite_cycle infinite_cycle p z) (h ↦ h .fst .map z)
      (p ↦ refl (cycle_path_evaluate infinite_cycle infinite_cycle p z)) integer_predecessor_isomorphism

def integer_predecessor_endomorphism_path : Id Endomorphisms integer_endomorphism integer_endomorphism
  ≔ cycle_endomorphism_paths infinite_cycle infinite_cycle .map integer_predecessor_cycle_path

def infinite_predecessor_loop : Id InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point
  ≔ equiv_inverse_map (Id InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point)
      (Id Endomorphisms integer_endomorphism integer_endomorphism)
      (subtype_path_equiv Endomorphisms (t ↦ Mere (Id Endomorphisms integer_endomorphism t))
        (t ↦ mere_isprop (Id Endomorphisms integer_endomorphism t))
        infinite_endomorphism_point infinite_endomorphism_point) integer_predecessor_endomorphism_path

def infinite_predecessor_loop_coordinate : Id Int (infinite_cycle_loop_coordinate infinite_predecessor_loop) (neg. zero.)
  ≔ concat Int (infinite_cycle_loop_coordinate infinite_predecessor_loop)
      (endomorphism_path_evaluate integer_endomorphism integer_endomorphism integer_predecessor_endomorphism_path int_zero)
      (neg. zero.)
      (inverse_evaluation_agreement (Id InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point)
        (Id Endomorphisms integer_endomorphism integer_endomorphism) Int
        (subtype_path_equiv Endomorphisms (t ↦ Mere (Id Endomorphisms integer_endomorphism t))
          (t ↦ mere_isprop (Id Endomorphisms integer_endomorphism t))
          infinite_endomorphism_point infinite_endomorphism_point)
        infinite_cycle_loop_coordinate
        (p ↦ endomorphism_path_evaluate integer_endomorphism integer_endomorphism p int_zero)
        (p ↦ refl (infinite_cycle_loop_coordinate p)) integer_predecessor_endomorphism_path)
      (integer_predecessor_cycle_evaluation int_zero)

def circle_negative_winding_equiv (C : CircleSignature)
  : Equiv (Id (C .carrier) (C .base) (C .base)) Int
  ≔ compose_equiv (Id (C .carrier) (C .base) (C .base)) Int Int
      (native_equivalence (Id (C .carrier) (C .base) (C .base)) Int (circle_loop_integer_equiv C)) int_neg_equiv

def circle_negative_winding_refl (C : CircleSignature)
  : Id Int (circle_negative_winding_equiv C .map (refl (C .base))) int_zero
  ≔ refl int_neg (circle_winding_refl C)

def circle_negative_winding_composition (C : CircleSignature)
  (p q : Id (C .carrier) (C .base) (C .base))
  : Id Int (circle_negative_winding_equiv C .map (concat (C .carrier) (C .base) (C .base) (C .base) p q))
      (int_add (circle_negative_winding_equiv C .map p) (circle_negative_winding_equiv C .map q))
  ≔ concat Int (int_neg (circle_winding C (concat (C .carrier) (C .base) (C .base) (C .base) p q)))
      (int_neg (int_add (circle_winding C p) (circle_winding C q)))
      (int_add (int_neg (circle_winding C p)) (int_neg (circle_winding C q)))
      (refl int_neg (circle_winding_composition C p q)) (int_neg_additive (circle_winding C p) (circle_winding C q))

def circle_infinite_loop_equiv (C : CircleSignature)
  : Equiv (Id (C .carrier) (C .base) (C .base))
      (Id InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point)
  ≔ compose_equiv (Id (C .carrier) (C .base) (C .base)) Int
      (Id InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point) (circle_negative_winding_equiv C)
      (canonical_inverse_equiv (Id InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point) Int
        infinite_cycle_loop_coordinate_equiv)

def circle_infinite_loop_coordinate (C : CircleSignature) (p : Id (C .carrier) (C .base) (C .base))
  : Id Int (infinite_cycle_loop_coordinate (circle_infinite_loop_equiv C .map p)) (int_neg (circle_winding C p))
  ≔ equiv_counit (Id InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point) Int
      infinite_cycle_loop_coordinate_equiv (int_neg (circle_winding C p))

def circle_infinite_loop_unit (C : CircleSignature)
  : LoopMapUnit (C .carrier) InfiniteCycles (C .base) infinite_endomorphism_point (circle_infinite_loop_equiv C .map)
  ≔ loop_coordinate_unit (C .carrier) InfiniteCycles (C .base) infinite_endomorphism_point (circle_infinite_loop_equiv C)
      (circle_negative_winding_equiv C) infinite_cycle_loop_coordinate_equiv (circle_infinite_loop_coordinate C)
      (circle_negative_winding_refl C) infinite_cycle_loop_coordinate_refl

def circle_infinite_loop_composition (C : CircleSignature)
  : LoopMapComposition (C .carrier) InfiniteCycles (C .base) infinite_endomorphism_point (circle_infinite_loop_equiv C .map)
  ≔ loop_coordinate_composition (C .carrier) InfiniteCycles (C .base) infinite_endomorphism_point (circle_infinite_loop_equiv C)
      (circle_negative_winding_equiv C) infinite_cycle_loop_coordinate_equiv (circle_infinite_loop_coordinate C)
      (circle_negative_winding_composition C) infinite_cycle_loop_coordinate_composition

def coordinate_generator_equal (A B X : Type) (e : Equiv A B) (u : A → X) (v : Equiv B X)
  (agreement : (a : A) → Id X (v .map (e .map a)) (u a)) (a : A) (b : B)
  (value : Id X (u a) (v .map b)) : Id B (e .map a) b
  ≔ equivalence_injective B X v (e .map a) b
      (concat X (v .map (e .map a)) (u a) (v .map b) (agreement a) value)

def circle_infinite_loop_generator (C : CircleSignature)
  : Id (Id InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point)
      (circle_infinite_loop_equiv C .map (C .loop)) infinite_predecessor_loop
  ≔ coordinate_generator_equal (Id (C .carrier) (C .base) (C .base))
      (Id InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point) Int
      (circle_infinite_loop_equiv C) (p ↦ int_neg (circle_winding C p)) infinite_cycle_loop_coordinate_equiv
      (circle_infinite_loop_coordinate C) (C .loop) infinite_predecessor_loop
      (concat Int (int_neg (circle_winding C (C .loop))) (neg. zero.)
        (infinite_cycle_loop_coordinate infinite_predecessor_loop)
        (refl int_neg (circle_winding_loop C))
        (inverse Int (infinite_cycle_loop_coordinate infinite_predecessor_loop) (neg. zero.) infinite_predecessor_loop_coordinate))

{` def:S1toC: the generator is the predecessor symmetry, with the book's
   sign convention.  The complete recursor boundary has propositional beta. `}
def circle_infinite_cycle_map (C : CircleSignature) : C .carrier → InfiniteCycles
  ≔ circle_rec C InfiniteCycles (infinite_endomorphism_point, infinite_predecessor_loop)

def circle_infinite_cycle_boundary (C : CircleSignature)
  : Id (FreeLoop InfiniteCycles) (circle_eval C InfiniteCycles (circle_infinite_cycle_map C))
      (infinite_endomorphism_point, infinite_predecessor_loop)
  ≔ circle_rec_beta C InfiniteCycles (infinite_endomorphism_point, infinite_predecessor_loop)

def circle_infinite_cycle_based_action (C : CircleSignature) (p : Id (C .carrier) (C .base) (C .base))
  : Id InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point
  ≔ circle_rec_based_action C InfiniteCycles infinite_endomorphism_point infinite_predecessor_loop p

def circle_infinite_cycle_action_comparison (C : CircleSignature) (p : Id (C .carrier) (C .base) (C .base))
  : Id (Id InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point)
      (circle_infinite_cycle_based_action C p) (circle_infinite_loop_equiv C .map p)
  ≔ concat (Id InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point)
      (circle_infinite_cycle_based_action C p)
      (circle_rec_based_action C InfiniteCycles infinite_endomorphism_point (circle_infinite_loop_equiv C .map (C .loop)) p)
      (circle_infinite_loop_equiv C .map p)
      (inverse (Id InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point)
        (circle_rec_based_action C InfiniteCycles infinite_endomorphism_point (circle_infinite_loop_equiv C .map (C .loop)) p)
        (circle_infinite_cycle_based_action C p)
        (refl ((l ↦ circle_rec_based_action C InfiniteCycles infinite_endomorphism_point l p)
          : Id InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point
            → Id InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point)
          (circle_infinite_loop_generator C)))
      (circle_delooping_action C InfiniteCycles infinite_endomorphism_point (circle_infinite_loop_equiv C)
        (circle_infinite_loop_unit C) (circle_infinite_loop_composition C) p)

def circle_infinite_cycle_action_coordinate (C : CircleSignature) (p : Id (C .carrier) (C .base) (C .base))
  : Id Int (infinite_cycle_loop_coordinate (circle_infinite_cycle_based_action C p)) (int_neg (circle_winding C p))
  ≔ concat Int (infinite_cycle_loop_coordinate (circle_infinite_cycle_based_action C p))
      (infinite_cycle_loop_coordinate (circle_infinite_loop_equiv C .map p)) (int_neg (circle_winding C p))
      (refl infinite_cycle_loop_coordinate (circle_infinite_cycle_action_comparison C p)) (circle_infinite_loop_coordinate C p)

def circle_infinite_cycle_power_coordinate (C : CircleSignature) (z : Int)
  : Id Int (infinite_cycle_loop_coordinate
      (circle_infinite_cycle_based_action C (loop_power (C .carrier) (C .base) (C .loop) z))) (int_neg z)
  ≔ concat Int (infinite_cycle_loop_coordinate
      (circle_infinite_cycle_based_action C (loop_power (C .carrier) (C .base) (C .loop) z)))
      (int_neg (circle_winding C (loop_power (C .carrier) (C .base) (C .loop) z))) (int_neg z)
      (circle_infinite_cycle_action_coordinate C (loop_power (C .carrier) (C .base) (C .loop) z))
      (refl int_neg (circle_winding_power C z))

{` thm:S1bysymmetries.  The resulting map is the specified map c, rather
   than an unspecified equivalence with the infinite-cycle component. `}
def circle_infinite_cycles_equiv (C : CircleSignature) : BookEquiv (C .carrier) InfiniteCycles
  ≔ let e ≔ circle_delooping_equiv C InfiniteCycles
      (native_component_connected Endomorphisms integer_endomorphism) infinite_endomorphism_point
      (circle_infinite_loop_equiv C) (circle_infinite_loop_unit C) (circle_infinite_loop_composition C) in
    let p ≔ refl ((l ↦ circle_rec C InfiniteCycles (infinite_endomorphism_point, l))
      : Id InfiniteCycles infinite_endomorphism_point infinite_endomorphism_point → (C .carrier → InfiniteCycles))
      (circle_infinite_loop_generator C) in
    book_equivalence (C .carrier) InfiniteCycles
      (equiv_change_map (C .carrier) InfiniteCycles (native_equivalence (C .carrier) InfiniteCycles e)
        (circle_infinite_cycle_map C) (x ↦ p (refl x)))
