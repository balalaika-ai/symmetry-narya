export "410-pointed-connected-groupoids"
export "487-universe-not-groupoid-instance"

{` xca:defgroup, unconditional reading. "A is a groupoid iff a = a is a set"
   fails without connectedness: for A = U (Narya's Type) and a = ∅, the loop
   type ∅ = ∅ is a set (universe_empty_loops_set), but U is not a groupoid
   (universe_not_groupoid, module 487). Only the forward implication
   groupoid_loops_set holds for arbitrary A. `}
def defgroup_unconditional_fails
  (h : (A : Type) (a : A) → isSet (Id A a a) → isGroupoid A) : Empty
  ≔ universe_not_groupoid (h Type Empty universe_empty_loops_set)
