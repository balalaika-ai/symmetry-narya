export "941-image-consequences"
export "937-epi-litmus"

{` Litmus checks for modules 938-941 (chapter 9: kernels, cokernels,
   images, image factorization). `}

{` The kernel of the identity is trivial; the kernel of Σ_3 → 1 is not. `}
def chlit_identity_kernel_trivial (G : Group) : IsTrivialMono G (kernel G G (group_hom_id G))
  ≔ eqmc_mono_kernel_trivial G G (group_hom_id G)
      (usym_injective_group_mono G G (group_hom_id G) (group_identity_usym_injective G))

def chlit_sigma3_kernel_identity_trivial
  : IsTrivialGroup (kernel_group (symmetric_group three) (symmetric_group three) (group_hom_id (symmetric_group three)))
  ≔ chlit_identity_kernel_trivial (symmetric_group three)

def chlit_sigma3_to_unit_kernel_nontrivial
  (t : IsTrivialMono (symmetric_group three) (kernel (symmetric_group three) unit_group (group_hom_to_unit (symmetric_group three))))
  : Empty
  ≔ sigma3_to_unit_not_mono (eqmc_kernel_trivial_mono (symmetric_group three) unit_group (group_hom_to_unit (symmetric_group three)) t)

{` The cokernel of 1 → Σ_3 is not contractible (the inclusion is not an
   epimorphism); the cokernel of Σ_3 → 1 is. `}
def chlit_unit_to_sigma3_cokernel_not_contractible
  (c : EqmcCokernelContractible unit_group (symmetric_group three) (group_hom_from_unit (symmetric_group three)))
  : Empty
  ≔ gepi_unit_to_sigma3_not_epi
      (equiv_inverse_map (IsGroupEpi unit_group (symmetric_group three) (group_hom_from_unit (symmetric_group three)))
        (EqmcCokernelContractible unit_group (symmetric_group three) (group_hom_from_unit (symmetric_group three)))
        (eqmc_epi_cokernel_contractible_equiv unit_group (symmetric_group three) (group_hom_from_unit (symmetric_group three))) c)

def chlit_sigma3_to_unit_cokernel_contractible
  : EqmcCokernelContractible (symmetric_group three) unit_group (group_hom_to_unit (symmetric_group three))
  ≔ eqmc_epi_cokernel_contractible_equiv (symmetric_group three) unit_group (group_hom_to_unit (symmetric_group three)) .map
      gepi_sigma3_to_unit_epi

{` The image of Σ_3 → 1 is trivial: its inclusion into 1 is an
   isomorphism (ex:charsurinj), so BImg ≃ B1 is contractible. `}
def chlit_sigma3_to_unit_image_trivial
  : IsTrivialGroup (image_group (symmetric_group three) unit_group (group_hom_to_unit (symmetric_group three)))
  ≔ let S ≔ symmetric_group three in
    let f ≔ group_hom_to_unit S in
    let I ≔ image_group S unit_group f in
    let e ≔ native_equivalence (BG I .carrier) Unit
        (hom_function I unit_group (image_inclusion S unit_group f),
         chim_epi_image_inclusion_iso S unit_group f gepi_sigma3_to_unit_epi) in
    book_contractibility_equiv Unit (BG I .carrier) (canonical_inverse_equiv (BG I .carrier) Unit e) .map unit_contraction

{` The image of a monomorphism: prj_img of the identity of Σ_3 is an
   isomorphism, and the identity is identified with its image inclusion
   in Mono(Σ_3). `}
def chlit_sigma3_identity_projection_iso
  : IsGroupIso (symmetric_group three) (image_group (symmetric_group three) (symmetric_group three) (group_hom_id (symmetric_group three)))
      (image_projection (symmetric_group three) (symmetric_group three) (group_hom_id (symmetric_group three)))
  ≔ chim_mono_image_projection_iso (symmetric_group three) (symmetric_group three) (group_hom_id (symmetric_group three))
      sigma3_identity_group_mono

def chlit_sigma3_identity_image_path
  : Id (GroupMonomorphismsInto (symmetric_group three))
      (symmetric_group three, (group_hom_id (symmetric_group three), sigma3_identity_group_mono))
      (image_mono_categorical (symmetric_group three) (symmetric_group three) (group_hom_id (symmetric_group three)))
  ≔ chim_mono_image_path (symmetric_group three) (symmetric_group three) (group_hom_id (symmetric_group three))
      sigma3_identity_group_mono

{` The image factorization of Σ_3 → 1 composes back to Σ_3 → 1, and the
   inclusion 1 → Σ_3 does not have a surjective image inclusion. `}
def chlit_sigma3_to_unit_factorization_section
  : Id (GroupHom (symmetric_group three) unit_group)
      (imfact_compose (symmetric_group three) unit_group
         (image_factorization_map (symmetric_group three) unit_group (group_hom_to_unit (symmetric_group three))))
      (group_hom_to_unit (symmetric_group three))
  ≔ imfact_compose_section (symmetric_group three) unit_group (group_hom_to_unit (symmetric_group three))

def chlit_unit_to_sigma3_image_inclusion_not_iso
  (h : IsGroupIso (image_group unit_group (symmetric_group three) (group_hom_from_unit (symmetric_group three)))
         (symmetric_group three) (image_inclusion unit_group (symmetric_group three) (group_hom_from_unit (symmetric_group three))))
  : Empty
  ≔ gepi_unit_to_sigma3_not_epi
      (chim_image_inclusion_iso_epi unit_group (symmetric_group three) (group_hom_from_unit (symmetric_group three)) h)
