export "06-normal"
export "../../../src/907-normal-epis"

{` Bridges for chapter 9: definition bridges shared by the other bridge files. `}

{` def:monomorphism / def:epimorphism: the blind predicates are ours (categorical monos/epis of GroupCat). `}
def bridge_def_is_mono (G H : Group) (f : GroupHom G H) : Id Type (BlindIsMono G H f) (IsGroupMonomorphism G H f)
  ≔ refl (BlindIsMono G H f)

def bridge_def_is_epi (G H : Group) (f : GroupHom G H) : Id Type (BlindIsEpi G H f) (IsGroupEpi G H f)
  ≔ refl (BlindIsEpi G H f)

def bridge_def_epi (G : Group) : Id Type (BlindEpi G) (GroupEpis G) ≔ refl (BlindEpi G)

def bridge_def_mono_type (H : Group) : Id Type (BlindMonoType H) (GroupMonomorphismsInto H) ≔ refl (BlindMonoType H)

{` def:kernel. `}
def bridge_def_ker_group (G H : Group) (f : GroupHom G H) : Id Group (BlindKer G H f) (kernel_group G H f)
  ≔ refl (BlindKer G H f)

def bridge_def_kermap (G H : Group) (f : GroupHom G H)
  : Id (GroupHom (kernel_group G H f) G) (blind_kermap G H f) (kernel_inclusion G H f)
  ≔ refl (blind_kermap G H f)

def bridge_def_ker (G H : Group) (f : GroupHom G H) : Id (GroupMonos G) (blind_ker G H f) (kernel G H f)
  ≔ refl (blind_ker G H f)

{` def:cokernel. `}
def bridge_def_coker (G H : Group) (f : GroupHom G H) : Id (GSet H) (blind_coker G H f) (cokernel G H f)
  ≔ refl (blind_coker G H f)

def bridge_def_coker_point (G H : Group) (f : GroupHom G H)
  : Id (gset_underlying H (cokernel G H f)) (blind_coker_point G H f) (cokernel_point G H f)
  ≔ refl (blind_coker_point G H f)

{` def:image: the explicit automorphism-group form. `}
def bridge_def_image (G H : Group) (f : GroupHom G H) : Id Group (BlindImage G H f) (image_group_aut G H f)
  ≔ refl (BlindImage G H f)

{` def:normalsubgroup. `}
def bridge_def_nor (G : Group) : Id Type (BlindNor G) (NormalSubgroups G) ≔ refl (BlindNor G)

def bridge_def_nor_incl (G : Group) (N : BlindNor G) : Id (Subgroups G) (blind_nor_incl G N) (normal_to_subgroup G N)
  ≔ refl (blind_nor_incl G N)

def bridge_def_kernels (G : Group) : Id Type (BlindKernels G) (KernelsOf G) ≔ refl (BlindKernels G)

def bridge_def_quotient_group (G : Group) (N : BlindNor G)
  : Id Group (BlindQuotientGroup G N) (normal_quotient_group G N) ≔ refl (BlindQuotientGroup G N)

def bridge_def_mono_gset (G : Group) : Id (GSet G) (BlindMonoGSet G) (monos_gset G) ≔ refl (BlindMonoGSet G)

def bridge_def_sub_gset (G : Group) : Id (GSet G) (BlindSubGSet G) (subgroups_gset G) ≔ refl (BlindSubGSet G)

def bridge_quotient_point_fst (G : Group) (N : BlindNor G)
  : Id (Id (GSet G) (N (shape G) .gset) (N (shape G) .gset)) (normal_quotient_point G N .fst) (refl (N (shape G) .gset))
  ≔ refl (refl (N (shape G) .gset))
