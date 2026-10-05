export "404-group-examples"
export "224-constructed-circle-checks"

{` ex:circlegroup at the constructed circle (modules 220-224): the group of
   integers Z ≔ mkgroup (S¹, base), with S¹ = Cyc_0 based at (Z, succ).
   This module is the explicitly typed interface to the constructed circle;
   downstream modules that only need some circle should use circle_group C
   for a CircleSignature C instead (module 404), which is much lighter. `}
def integer_group : Group ≔ circle_group constructed_circle

def integer_group_classifying_type : Id Type (BG integer_group .carrier) (CycleComponent zero.)
  ≔ refl (CycleComponent zero.)

def integer_group_shape : Id (CycleComponent zero.) (shape integer_group) (principal_component_point zero.)
  ≔ refl (principal_component_point zero.)

{` The generating symmetry loop : USym Z. `}
def integer_group_generator : USym integer_group ≔ circle_loop

{` cor:S1groupoid: n ↦ loopⁿ is an equivalence Z ≃ USym Z. `}
def integer_group_usym_equiv : BookEquiv Int (USym integer_group)
  ≔ circle_group_usym_integers constructed_circle
