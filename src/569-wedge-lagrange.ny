import "566-wedge-circle-gsets"
import "526-lagrange-construction"

{` Chapter 5, xca:lagrange-if-subgr-not-normal, conclusion: Lagrange's
   construction (con:lagrange) applies to the subgroup (X, 0) of
   G = mkgroup(S¹ ∨ S¹) with the choice map of module 566. `}

def wedge_lagrange_equiv (W : CircleWedgeSignature) (hW : isGroupoid (W .carrier))
  : Equiv (USym (circle_wedge_group W hW))
      (Product (wedge_family W (W .base) .fst) (USym (subgroup_group (circle_wedge_group W hW) (wedge_subgroup W hW))))
  ≔ lagrange_construction (circle_wedge_group W hW) (wedge_subgroup W hW) (wedge_choice_map W hW)

{` Composed with E : X(sh) ≃ Fin 3: USym G ≃ Fin 3 × USym H. `}
def wedge_lagrange_fin3_equiv (W : CircleWedgeSignature) (hW : isGroupoid (W .carrier))
  : Equiv (USym (circle_wedge_group W hW))
      (Product (Fin three) (USym (subgroup_group (circle_wedge_group W hW) (wedge_subgroup W hW))))
  ≔ let H ≔ USym (subgroup_group (circle_wedge_group W hW) (wedge_subgroup W hW)) in
    compose_equiv (USym (circle_wedge_group W hW)) (Product (wedge_family W (W .base) .fst) H) (Product (Fin three) H)
      (wedge_lagrange_equiv W hW)
      (product_equiv (wedge_family W (W .base) .fst) H (Fin three) H (wedge_identify W) (identity_equiv H))

{` The first component of L(f)(g) is g · 0. `}
def wedge_lagrange_equiv_fst (W : CircleWedgeSignature) (hW : isGroupoid (W .carrier)) (g : USym (circle_wedge_group W hW))
  : Id (wedge_family W (W .base) .fst) (wedge_lagrange_equiv W hW .map g .fst)
      (gset_usym_act (circle_wedge_group W hW) (wedge_gset W hW) g (wedge_gset_point W fin3_zero))
  ≔ refl (gset_usym_act (circle_wedge_group W hW) (wedge_gset W hW) g (wedge_gset_point W fin3_zero))
