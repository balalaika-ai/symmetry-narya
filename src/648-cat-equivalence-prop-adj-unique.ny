export "643-ff-eso-equivalences"
export "624-adjunctions-via-representability"

{` Chapter 6, section 6.7: lem:cat-equiv-is-prop by the book's route.
   "From cor:adj-unique we immediately see": for F out of a category the
   right adjoint data form a proposition
   (right_adjoint_data_prop), and the unit and counit conditions are
   propositions in any wild precategory. The same statement is proved in
   module 643 (is_cat_equivalence_prop) via lem:equiv-precat-is-ff-split-eso
   and lem:ff-eso; both are checked to agree in type. `}
def is_cat_equivalence_prop_via_adj_unique (C : Category) (D : WildPrecat) (F : WildFunctor (C .wild) D)
  : isProp (IsCatEquivalence (C .wild) D F)
  ≔ sigma_prop (RightAdjointData (C .wild) D F) (CatEquivalenceIsoConditions (C .wild) D F)
      (right_adjoint_data_prop C D F) (cat_equivalence_iso_conditions_prop (C .wild) D F)

{` The two proofs give the same identification (both live in a
   proposition's identity type, which is contractible). `}
def is_cat_equivalence_prop_routes_agree (C : Category) (D : WildPrecat) (F : WildFunctor (C .wild) D)
  (E E' : IsCatEquivalence (C .wild) D F)
  : Id (Id (IsCatEquivalence (C .wild) D F) E E')
      (is_cat_equivalence_prop_via_adj_unique C D F E E') (is_cat_equivalence_prop C D F E E')
  ≔ prop_is_set (IsCatEquivalence (C .wild) D F) (is_cat_equivalence_prop C D F) E E'
      (is_cat_equivalence_prop_via_adj_unique C D F E E') (is_cat_equivalence_prop C D F E E')
