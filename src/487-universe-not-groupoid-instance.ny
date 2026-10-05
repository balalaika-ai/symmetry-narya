export "486-universe-not-groupoid"
export "224-constructed-circle-checks"

{` The universe is not a groupoid (unconditionally, using the constructed
   circle of modules 220-224), while its component at a set is
   (universe_set_component_groupoid): the example of rem:autinfgp. `}
def universe_not_groupoid (hT : isGroupoid Type) : Empty ≔ universe_not_groupoid_of_circle constructed_circle hT

def universe_component_groupoid_not_universe (S : Type) (hS : isSet S)
  : Product (isGroupoid (NativeComponent Type S)) (isGroupoid Type → Empty)
  ≔ (universe_set_component_groupoid S hS, universe_not_groupoid)

{` xca:defgroup, unconditional reading refuted: (Type, Empty) has a set of
   loops but Type is not a groupoid. `}
def loops_set_not_groupoid : Product (isSet (Id Type Empty Empty)) (isGroupoid Type → Empty)
  ≔ loops_set_not_groupoid_of_circle constructed_circle
