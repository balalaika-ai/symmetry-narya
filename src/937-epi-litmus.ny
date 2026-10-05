export "936-epi-mono-iso"

{` Litmus checks for lem:epi-surj (line 161) and lem:epimonoiso (line 238):
   the projection G × H → G and Σ_3 → 1 are epimorphisms (via (2') ⇒ (1')),
   while the inclusion 1 → Σ_3 of the trivial subgroup is not an
   epimorphism (via the hard direction (1') ⇒ (2'): its USym map is not
   surjective, the transposition τ is not in its image); consequently
   1 → Σ_3 is a monomorphism that is not an isomorphism, and Σ_3 → 1 is an
   epimorphism that is not a monomorphism. `}

def gepi_product_proj1_usym_surjective (G H : Group)
  : Surjective (USym (product_group G H)) (USym G) (usym_hom (product_group G H) G (product_group_proj1 G H))
  ≔ g ↦ mere (BookFiber (USym (product_group G H)) (USym G) (usym_hom (product_group G H) G (product_group_proj1 G H)) g)
      ((g, refl (shape H)),
       inverse (USym G) (usym_hom (product_group G H) G (product_group_proj1 G H) (g, refl (shape H))) g
         (product_group_proj1_usym G H (g, refl (shape H))))

def gepi_product_proj1_epi (G H : Group) : IsEpi (GroupCat .wild) (product_group G H) G (product_group_proj1 G H)
  ≔ gepi_usym_surjective_epi (product_group G H) G (product_group_proj1 G H) (gepi_product_proj1_usym_surjective G H)

def gepi_unit_usym_prop : isProp (USym unit_group)
  ≔ contractible_prop (USym unit_group) (native_contraction (USym unit_group) unit_group_usym_contractible)

def gepi_to_unit_epi (G : Group) : IsEpi (GroupCat .wild) G unit_group (group_hom_to_unit G)
  ≔ gepi_usym_surjective_epi G unit_group (group_hom_to_unit G)
      (h ↦ mere (BookFiber (USym G) (USym unit_group) (usym_hom G unit_group (group_hom_to_unit G)) h)
        (usym_unit G, gepi_unit_usym_prop h (usym_hom G unit_group (group_hom_to_unit G) (usym_unit G))))

def gepi_sigma3_to_unit_epi : IsEpi (GroupCat .wild) (symmetric_group three) unit_group (group_hom_to_unit (symmetric_group three))
  ≔ gepi_to_unit_epi (symmetric_group three)

def gepi_fin3_one_not_zero (p : Id (Fin three) fin3_one fin3_zero) : Empty
  ≔ transport (Fin three) ([ inl. _ ↦ Unit | inr. _ ↦ Empty ] : Fin three → Type) fin3_one fin3_zero p star.

{` τ is not the unit symmetry: τ(0) = 1, e(0) = 0. `}
def gepi_sigma3_tau_not_unit (p : Id (USym (symmetric_group three)) sigma3_tau (usym_unit (symmetric_group three))) : Empty
  ≔ gepi_fin3_one_not_zero
      (concat (Fin three) fin3_one
         (permutation_action (standard_set three) (usym_unit (symmetric_group three)) fin3_zero) fin3_zero
         (refl ((u ↦ permutation_action (standard_set three) u fin3_zero) : USym (symmetric_group three) → Fin three) p)
         (permutation_action_unit (standard_set three) fin3_zero))

{` The inclusion of the trivial subgroup 1 → Σ_3 is not an epimorphism. `}
def gepi_unit_to_sigma3_not_epi
  (e : IsEpi (GroupCat .wild) unit_group (symmetric_group three) (group_hom_from_unit (symmetric_group three))) : Empty
  ≔ let S3 ≔ symmetric_group three in
    let i ≔ group_hom_from_unit S3 in
    mere_rec (BookFiber (USym unit_group) (USym S3) (usym_hom unit_group S3 i) sigma3_tau) Empty empty_prop
      (w ↦ gepi_sigma3_tau_not_unit
        (calc
          sigma3_tau
          = usym_hom unit_group S3 i (w .fst) by w .snd
          = usym_hom unit_group S3 i (usym_unit unit_group)
            by refl (usym_hom unit_group S3 i) (gepi_unit_usym_prop (w .fst) (usym_unit unit_group))
          = usym_unit S3 by usym_hom_unit unit_group S3 i ∎))
      (gepi_epi_usym_surjective unit_group S3 i e sigma3_tau)

{` 1 → Σ_3 is a monomorphism (USym 1 is a proposition) but not an
   isomorphism; Σ_3 → 1 is an epimorphism but not an isomorphism. `}
def gepi_unit_to_sigma3_mono : IsMono (GroupCat .wild) unit_group (symmetric_group three) (group_hom_from_unit (symmetric_group three))
  ≔ usym_injective_group_mono unit_group (symmetric_group three) (group_hom_from_unit (symmetric_group three))
      (path_reflecting_set_embedding (USym unit_group) (USym (symmetric_group three)) (usym_set (symmetric_group three))
        (usym_hom unit_group (symmetric_group three) (group_hom_from_unit (symmetric_group three)))
        (g g' _ ↦ gepi_unit_usym_prop g g'))

def gepi_unit_to_sigma3_not_iso
  (h : IsGroupIso unit_group (symmetric_group three) (group_hom_from_unit (symmetric_group three))) : Empty
  ≔ gepi_unit_to_sigma3_not_epi (gepi_iso_mono_epi_equiv unit_group (symmetric_group three)
      (group_hom_from_unit (symmetric_group three)) .map h .snd)

def gepi_sigma3_to_unit_not_iso
  (h : IsGroupIso (symmetric_group three) unit_group (group_hom_to_unit (symmetric_group three))) : Empty
  ≔ sigma3_to_unit_not_mono (gepi_iso_mono_epi_equiv (symmetric_group three) unit_group
      (group_hom_to_unit (symmetric_group three)) .map h .fst)
