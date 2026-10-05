export "1740-condition-l"
export "223-constructed-circle"

{` The xca "S¹-AC(2) is false" at the constructed circle of module 223. `}
def constructed_circle_local_choice_two_false
  (lac : LocalChoiceOfSize (constructed_circle .carrier) two) : Empty
  ≔ circle_local_choice_two_false constructed_circle lac

{` Hence 2-element choice over arbitrary index types (not only sets) fails. `}
def choice_of_size_two_over_all_types_false
  (h : (X : Type) → LocalChoiceOfSize X two) : Empty
  ≔ constructed_circle_local_choice_two_false (h (constructed_circle .carrier))
