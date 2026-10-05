export "800-semidirect-products"
export "407-group-family-products"
export "410-pointed-connected-groupoids"
export "500-gsets"

{` Chapter 8 (congp.tex), section "Wreath products" (sec:wreath, lines 309–352).
   A G-set is X : BG → Set (def:Gset), chapter 5's GSet G ≔ BG G .carrier → SetTypes.
   H^X(z) ≔ Aut_{X(z) → BH}(_ ↦ sh_H), the symmetries of the constant function,
   and H ≀_X G ≔ G ⋉ H^X (def. at congp.tex:328).  The three examples that
   follow (hypercubes, Sudoku, trees, lines 340–350) have empty bodies. `}

def wreath_power_groupoid (H : Group) (S : Type) : isGroupoid (S → BG H .carrier)
  ≔ groupoid_pi S (_ ↦ BG H .carrier) (_ ↦ bg_groupoid H)

def wreath_constant_shape (H : Group) (S : Type) : S → BG H .carrier ≔ _ ↦ shape H

{` H^X : BG → Group, H^X(z) ≔ Aut_{X(z) → BH}(_ ↦ sh_H). `}
def wreath_power_action (H G : Group) (X : GSet G) (z : BG G .carrier) : Group
  ≔ automorphism_group (X z .fst → BG H .carrier) (wreath_power_groupoid H (X z .fst))
      (wreath_constant_shape H (X z .fst))

{` H ≀_X G ≔ G ⋉ H^X. `}
def wreath_product (H G : Group) (X : GSet G) : Group
  ≔ semidirect_product G (wreath_power_action H G X)

def wreath_product_classifying (H G : Group) (X : GSet G)
  : Id Type (BG (wreath_product H G X) .carrier)
      (Σ (BG G .carrier) (z ↦ NativeComponent (X z .fst → BG H .carrier) (wreath_constant_shape H (X z .fst))))
  ≔ refl (BG (wreath_product H G X) .carrier)

{` "G acts on the power H^{X(sh_G)}": the acted-on group H^X(sh_G) is the
   group of symmetries of the constant function in X(sh_G) → BH; for finite
   X(sh_G) it is the power group of module 407 (xca:bigproductfunext (i)). `}
def wreath_power_component_equiv (H : Group) (S : Type) (hS : IsFinite S)
  : BookPointedEquiv (BG (automorphism_group (S → BG H .carrier) (wreath_power_groupoid H S) (wreath_constant_shape H S)))
      (BG (power_group S hS H))
  ≔ connected_component_pointed_equiv (S → BG H .carrier)
      (connected_pi_finite S hS (_ ↦ BG H .carrier) (_ ↦ bg_connected H)) (wreath_constant_shape H S)

def wreath_power_is_power_group (H : Group) (S : Type) (hS : IsFinite S)
  : Id Group (automorphism_group (S → BG H .carrier) (wreath_power_groupoid H S) (wreath_constant_shape H S))
      (power_group S hS H)
  ≔ group_path_from_pointed_equiv
      (automorphism_group (S → BG H .carrier) (wreath_power_groupoid H S) (wreath_constant_shape H S))
      (power_group S hS H) (wreath_power_component_equiv H S hS)

def wreath_acted_on_group (H G : Group) (X : GSet G) (hX : IsFinite (X (shape G) .fst))
  : Id Group (wreath_power_action H G X (shape G)) (power_group (X (shape G) .fst) hX H)
  ≔ wreath_power_is_power_group H (X (shape G) .fst) hX

{` Finiteness of X(sh_G) propagates to every X(z) (BG is connected). `}
def wreath_fibers_finite (G : Group) (X : GSet G) (hX : IsFinite (X (shape G) .fst))
  (z : BG G .carrier) : IsFinite (X z .fst)
  ≔ mere_rec (Id (BG G .carrier) (shape G) z) (IsFinite (X z .fst)) (isfinite_prop (X z .fst))
      (p ↦ transport (BG G .carrier) (y ↦ IsFinite (X y .fst)) (shape G) z p hX)
      (bg_connected G .snd (shape G) z)

{` "If the underlying set of X is finite, then the classifying space of
   H^X(z) can be identified with the whole function type X(z) → BH". `}
def wreath_power_classifying_equiv (H G : Group) (X : GSet G)
  (hX : IsFinite (X (shape G) .fst)) (z : BG G .carrier)
  : BookIsEquiv (BG (wreath_power_action H G X z) .carrier) (X z .fst → BG H .carrier) (u ↦ u .fst)
  ≔ connected_component_fst_equiv (X z .fst → BG H .carrier)
      (connected_pi_finite (X z .fst) (wreath_fibers_finite G X hX z) (_ ↦ BG H .carrier) (_ ↦ bg_connected H))
      (wreath_constant_shape H (X z .fst))

{` "When X(sh_G) is finite, B(H ≀_X G) ≃ Σ_{z:BG} X(z) → BH", by
   (z, u) ↦ (z, u .fst); it sends the shape to (sh_G, _ ↦ sh_H). `}
def wreath_classifying_equiv (H G : Group) (X : GSet G) (hX : IsFinite (X (shape G) .fst))
  : Equiv (BG (wreath_product H G X) .carrier) (Σ (BG G .carrier) (z ↦ X z .fst → BG H .carrier))
  ≔ family_equiv (BG G .carrier) (z ↦ BG (wreath_power_action H G X z) .carrier) (z ↦ X z .fst → BG H .carrier)
      (z ↦ native_equivalence (BG (wreath_power_action H G X z) .carrier) (X z .fst → BG H .carrier)
        (u ↦ u .fst, wreath_power_classifying_equiv H G X hX z))

def wreath_classifying_equiv_map (H G : Group) (X : GSet G) (hX : IsFinite (X (shape G) .fst))
  (w : BG (wreath_product H G X) .carrier)
  : Id (Σ (BG G .carrier) (z ↦ X z .fst → BG H .carrier)) (wreath_classifying_equiv H G X hX .map w)
      (w .fst, w .snd .fst)
  ≔ refl (w .fst, w .snd .fst)

def wreath_classifying_equiv_shape (H G : Group) (X : GSet G) (hX : IsFinite (X (shape G) .fst))
  : Id (Σ (BG G .carrier) (z ↦ X z .fst → BG H .carrier))
      (wreath_classifying_equiv H G X hX .map (shape (wreath_product H G X)))
      (shape G, wreath_constant_shape H (X (shape G) .fst))
  ≔ refl (shape G, wreath_constant_shape H (X (shape G) .fst))

{` Litmus: the wreath product by the one-point G-set is the product G × H. `}
def wreath_unit_gset (G : Group) : GSet G ≔ _ ↦ (Unit, unit_set)

def wreath_unit_finite : IsFinite Unit
  ≔ mere (Σ Nat (n ↦ Id Type Unit (Fin n)))
      (suc. zero., ua Unit (Fin (suc. zero.)) (canonical_inverse_equiv (Fin (suc. zero.)) Unit fin_one_equiv))

def wreath_unit_function_equiv (T : Type) : Equiv (Unit → T) T
  ≔ quasi_inverse_equiv (Unit → T) T (f ↦ f star.) (t ↦ _ ↦ t)
      (f ↦ funext Unit (_ ↦ T) (_ ↦ f star.) f (u ↦ match u [ star. ↦ refl (f star.) ]))
      (t ↦ refl t)

def wreath_unit_classifying_equiv (H G : Group)
  : Equiv (BG (wreath_product H G (wreath_unit_gset G)) .carrier) (Product (BG G .carrier) (BG H .carrier))
  ≔ compose_equiv (BG (wreath_product H G (wreath_unit_gset G)) .carrier)
      (Σ (BG G .carrier) (_ ↦ Unit → BG H .carrier)) (Product (BG G .carrier) (BG H .carrier))
      (wreath_classifying_equiv H G (wreath_unit_gset G) wreath_unit_finite)
      (family_equiv (BG G .carrier) (_ ↦ Unit → BG H .carrier) (_ ↦ BG H .carrier)
        (_ ↦ wreath_unit_function_equiv (BG H .carrier)))

def wreath_unit_pointed_equiv (H G : Group)
  : BookPointedEquiv (BG (wreath_product H G (wreath_unit_gset G))) (BG (product_group G H))
  ≔ ((wreath_unit_classifying_equiv H G .map, refl (shape (product_group G H))),
     book_equivalence (BG (wreath_product H G (wreath_unit_gset G)) .carrier) (Product (BG G .carrier) (BG H .carrier))
       (wreath_unit_classifying_equiv H G) .equiv)

def wreath_unit_product_path (H G : Group) : Id Group (wreath_product H G (wreath_unit_gset G)) (product_group G H)
  ≔ group_path_from_pointed_equiv (wreath_product H G (wreath_unit_gset G)) (product_group G H)
      (wreath_unit_pointed_equiv H G)

def wreath_unit_classifying_map_check (H G : Group) (w : BG (wreath_product H G (wreath_unit_gset G)) .carrier)
  : Id (Product (BG G .carrier) (BG H .carrier)) (wreath_unit_classifying_equiv H G .map w) (w .fst, w .snd .fst star.)
  ≔ refl (w .fst, w .snd .fst star.)
