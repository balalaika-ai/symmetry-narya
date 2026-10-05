export "250-circle-instantiations"
export "262-root-path-action"
export "272-quotient-fiber-equivalence"

{` The comparisons of cdg_m with dg_m and of the flip with inversion,
   instantiated at the constructed circle, with the generic types written
   out at C := constructed_circle (see module 250). `}
def S1_root_degree_pointed (n : Nat)
  : Id (BookPointedMap (circle_pointed constructed_circle) infinite_pointed)
      (root_after_circle constructed_circle n) (circle_after_degree constructed_circle n)
  ≔ root_degree_pointed constructed_circle n

def S1_root_degree_maps (n : Nat)
  : Id (constructed_circle .carrier → InfiniteCycles)
      (x ↦ formal_root_infinite_component n (circle_infinite_cycle_map constructed_circle x))
      (x ↦ circle_infinite_cycle_map constructed_circle (circle_degree_map constructed_circle (suc. n) x))
  ≔ root_degree_maps constructed_circle n

def S1_circle_flip_pointed
  : Id (BookPointedMap (circle_pointed constructed_circle) infinite_pointed)
      (inverse_after_circle constructed_circle) (circle_after_reflection constructed_circle)
  ≔ circle_flip_pointed constructed_circle

def S1_circle_flip_maps
  : Id (constructed_circle .carrier → InfiniteCycles)
      (x ↦ infinite_inverse (circle_infinite_cycle_map constructed_circle x))
      (x ↦ circle_infinite_cycle_map constructed_circle (circle_reflection constructed_circle x))
  ≔ circle_flip_maps constructed_circle

def S1_circle_flip_conjugation
  : Id (InfiniteCycles → InfiniteCycles)
      (y ↦ circle_infinite_cycle_map constructed_circle (circle_reflection constructed_circle
        (equiv_inverse_map (constructed_circle .carrier) InfiniteCycles
          (native_equivalence (constructed_circle .carrier) InfiniteCycles
            (circle_infinite_cycles_equiv constructed_circle)) y)))
      infinite_inverse
  ≔ circle_flip_conjugation constructed_circle
