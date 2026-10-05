export "223-constructed-circle"

{` Sanity checks: circle-conditional theorems instantiated at the
   constructed circle. `}
def constructed_circle_connected : Connected (CycleComponent zero.) ≔ native_circle_connected constructed_circle

def constructed_circle_groupoid : isGroupoid (CycleComponent zero.) ≔ circle_groupoid constructed_circle

def constructed_circle_loops_integers
  : BookEquiv (Id (CycleComponent zero.) (principal_component_point zero.) (principal_component_point zero.)) Int
  ≔ circle_loop_integer_equiv constructed_circle

def constructed_circle_universal_property (A : Type) : BookEquiv (CycleComponent zero. → A) (FreeLoop A)
  ≔ book_circle_universal_property constructed_circle A

def constructed_circle_coverings_permutations : Equiv (Coverings (CycleComponent zero.)) Permutations
  ≔ circle_coverings_permutations constructed_circle

def constructed_circle_infinite_cycles : BookEquiv (CycleComponent zero.) InfiniteCycles
  ≔ circle_infinite_cycles_equiv constructed_circle

{` The base of the constructed circle and its generator: evaluation of
   the loop at 0 is 1. `}
def constructed_circle_loop_coordinate
  : Id Int (circle_loop_equiv .map circle_loop) (int_succ int_zero)
  ≔ concat Int (circle_loop_equiv .map circle_loop)
      (cycle_path_evaluate infinite_cycle infinite_cycle infinite_successor_loop_cycles int_zero) (int_succ int_zero)
      (refl ((p ↦ cycle_path_evaluate infinite_cycle infinite_cycle p int_zero) : Id Cycles infinite_cycle infinite_cycle → Int)
        circle_loop_underlying)
      (infinite_successor_loop_action int_zero)
