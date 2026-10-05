export "1200-abelian-group-basics"
export "810-wreath-products"
export "802-semidirect-symmetries"

{` Chapter 12, sec:direct-sums (abelian.tex 938-952), example (Lamplighter
   group) C₂ ≀ Z, first part. The section is a sketch. With chapter 8's
   wreath product (congp.tex sec:wreath: H ≀_X G ≔ G ⋉ H^X with
   H^X(z) ≔ Aut_{X(z) → BH}(const sh_H), module 810), C₂ ≀ Z for the
   principal Z-set X(z) ≔ (sh = z) is the UNRESTRICTED wreath product: its
   symmetries are Z × (Z → C₂), all functions, not only finitely supported
   ones (lamplighter_unrestricted_usym_equiv). The lamplighter group proper is
   the reduced (restricted) wreath product ⊕_Z C₂ ⋊ Z of the section title;
   it is constructed in module 1220 (reduced_wreath_product, lamplighter_group),
   which answers the book's \wip question for finitely supported sums. `}

{` The symmetries of H ≀_X G are pairs (g, c) with c : X(sh_G) → USym H
   (lem:pathpairsection, then the symmetries of a constant function). `}
def wreath_usym_functions_equiv (H G : Group) (X : GSet G)
  : Equiv (USym (wreath_product H G X)) (Product (USym G) (X (shape G) .fst → USym H))
  ≔ let S ≔ X (shape G) .fst in
    compose_equiv (USym (wreath_product H G X)) (Product (USym G) (USym (wreath_power_action H G X (shape G))))
      (Product (USym G) (S → USym H))
      (semidirect_usym_equiv G (wreath_power_action H G X))
      (product_equiv (USym G) (USym (wreath_power_action H G X (shape G))) (USym G) (S → USym H)
        (identity_equiv (USym G))
        (compose_equiv (USym (wreath_power_action H G X (shape G)))
          (Id (S → BG H .carrier) (wreath_constant_shape H S) (wreath_constant_shape H S)) (S → USym H)
          (automorphism_group_usym_equiv (S → BG H .carrier) (wreath_power_groupoid H S) (wreath_constant_shape H S))
          (function_extensionality S (_ ↦ BG H .carrier) (wreath_constant_shape H S) (wreath_constant_shape H S))))

{` C₂ ≀ Z with chapter 8's (unrestricted) wreath product: Z = circle_group C
   acting on its principal Z-set, C₂ = cyclic_group_fin 1. `}
def lamplighter_unrestricted_group (C : CircleSignature) : Group
  ≔ wreath_product (cyclic_group_fin (suc. zero.)) (circle_group C) (principal_gset (circle_group C))

{` Litmus: the symmetries of the unrestricted C₂ ≀ Z are pairs (n, c) of an
   integer and an arbitrary function Z → C₂ (Fin 2). `}
def lamplighter_unrestricted_usym_equiv (C : CircleSignature)
  : Equiv (USym (lamplighter_unrestricted_group C)) (Product Int (Int → Fin (suc. (suc. zero.))))
  ≔ let Z ≔ circle_group C in let C2 ≔ cyclic_group_fin (suc. zero.) in
    let eZ ≔ native_equivalence Int (USym Z) (circle_group_usym_integers C) in
    compose_equiv (USym (lamplighter_unrestricted_group C)) (Product (USym Z) (USym Z → USym C2))
      (Product Int (Int → Fin (suc. (suc. zero.))))
      (wreath_usym_functions_equiv C2 Z (principal_gset Z))
      (product_equiv (USym Z) (USym Z → USym C2) Int (Int → Fin (suc. (suc. zero.)))
        (canonical_inverse_equiv Int (USym Z) eZ)
        (compose_equiv (USym Z → USym C2) (Int → USym C2) (Int → Fin (suc. (suc. zero.)))
          (precompose_equiv Int (USym Z) (USym C2) eZ)
          (pi_family_equiv Int (_ ↦ USym C2) (_ ↦ Fin (suc. (suc. zero.)))
            (_ ↦ cyclic_group_fin_usym_equiv (suc. zero.)))))
