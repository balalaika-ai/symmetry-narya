export "210-truncation-smallness"
export "186-chapter-two-remarks"

{` rem:expforreal: the preimage of any point of the circle under the
   exponential covering exp : Tot(R) → S¹ is merely a copy of the integers. `}
def exponential_base_fiber (C : CircleSignature) : Equiv (circle_integer_family C (C .base)) Int
  ≔ id_to_equiv (circle_integer_family C (C .base)) Int (circle_integer_family_beta C .fst)

def exponential_family_integers (C : CircleSignature) (z : C .carrier)
  : Mere (Equiv (circle_integer_family C z) Int)
  ≔ circle_ind_prop C (z ↦ Mere (Equiv (circle_integer_family C z) Int))
      (z ↦ mere_isprop (Equiv (circle_integer_family C z) Int))
      (mere (Equiv (circle_integer_family C (C .base)) Int) (exponential_base_fiber C)) z

def exponential_fibers_integers (C : CircleSignature) (z : C .carrier)
  : Mere (Equiv (BookFiber (Σ (C .carrier) (circle_integer_family C)) (C .carrier) (t ↦ t .fst) z) Int)
  ≔ let F ≔ BookFiber (Σ (C .carrier) (circle_integer_family C)) (C .carrier) (t ↦ t .fst) z in
    trunc_map native_truncation (Equiv (circle_integer_family C z) Int) (Equiv F Int)
      (e ↦ compose_equiv F (circle_integer_family C z) Int
        (projection_book_fiber_equiv (C .carrier) (circle_integer_family C) z) e)
      (exponential_family_integers C z)
