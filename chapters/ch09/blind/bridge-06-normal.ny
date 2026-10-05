export "bridge-00-core"
export "../../../src/909-quotient-torsors"
export "../../../src/941-image-consequences"

{` Bridges for subgroups.tex, sec:normal and sec:assker (blind file 06-normal). The blind statements with
   proof parameters (transitivity proofs ht of nor, epi proofs hq of q_N, kernel proofs hk of ass) are derived for
   every choice of the parameters. `}

{` Remark at line 1330. `}
def bridge_nor_incl_injective : blind_nor_incl_injective ≔ G ↦ normal_to_subgroup_injective G

def bridge_def_is_normal_subgroup (G : Group) (S : Subgroups G)
  : Id Type (BlindIsNormalSubgroup G S) (IsNormalSubgroup G S) ≔ refl (BlindIsNormalSubgroup G S)

def bridge_is_normal_subgroup_prop : blind_is_normal_subgroup_prop ≔ G S ↦ is_normal_subgroup_prop G S

{` def:setofkernels. `}
def bridge_def_ker_corestrict (G : Group)
  : Id (BlindEpi G → BlindKernels G) (blind_ker_corestrict G) (epis_to_kernels G) ≔ refl (blind_ker_corestrict G)

def bridge_def_kernels_incl (G : Group)
  : Id (BlindKernels G → GroupMonos G) (blind_kernels_incl G) (kernels_include G) ≔ refl (blind_kernels_incl G)

def bridge_kernels_factorization : blind_kernels_factorization
  ≔ G ↦ (epis_to_kernels_surjective G, kernels_include_injective G)

{` def:ker2. The blind G-sets are ours; our transitivity proofs give the parameter; for every parameter the
   blind nor is ours. `}
def bridge_def_nor_gset (G : Group) (e : BlindEpi G) (y : BG G .carrier)
  : Id (GSet G) (blind_nor_gset G e y) (nor_gset G (e .fst) (e .snd .fst) y) ≔ refl (blind_nor_gset G e y)

def bridge_nor_transitive : blind_nor_transitive ≔ G e y ↦ nor G e y .transitive

def bridge_def_nor_map (G : Group) (ht : BlindNorTransitivity G) (e : BlindEpi G)
  : Id (NormalSubgroups G) (blind_nor G ht e) (nor G e)
  ≔ funext (BG G .carrier) (y ↦ Subgroups (group_at G y)) (blind_nor G ht e) (nor G e)
      (y ↦ (refl (nor_gset G (e .fst) (e .snd .fst) y), refl (refl (hom_function G (e .fst) (e .snd .fst) y)),
            is_transitive_prop (group_at G y) (nor_gset G (e .fst) (e .snd .fst) y) (ht e y) (nor G e y .transitive)))

{` Remark at line 1408. `}
def bridge_nor_gset_torsor_iff_iso : blind_nor_gset_torsor_iff_iso
  ≔ G e y ↦ nor_gset_torsor_iff_iso G (e .fst) (e .snd .fst) y

{` lem:diagfornormal. `}
def bridge_diagfornormal : blind_diagfornormal
  ≔ G ht e ↦
    let c ≔ epis_to_connected G e .snd .snd in
    concat (Subgroups G) (mono_to_subgroup G (kernel G (e .fst) (e .snd .fst))) (normal_to_subgroup G (nor G e))
      (normal_to_subgroup G (blind_nor G ht e))
      (inverse (Subgroups G) (normal_to_subgroup G (nor_conn G (e .fst, (e .snd .fst, c)))) (mono_to_subgroup G (kernel G (e .fst) (e .snd .fst)))
        (diag_for_normal G (e .fst) (e .snd .fst) c))
      (refl (normal_to_subgroup G) (inverse (NormalSubgroups G) (blind_nor G ht e) (nor G e) (bridge_def_nor_map G ht e)))

{` lem:evaliseqwhennormal. `}
def bridge_evaliseqwhennormal : blind_evaliseqwhennormal ≔ G N y z ↦ normal_evaluation_is_equiv G N y z

def bridge_normal_ap_surjective : blind_normal_ap_surjective ≔ G N y z ↦ normal_family_map_surjective G N y z

{` def:normalquotient: the blind q_N (strictly pointed component lift) equals ours. `}
def bridge_def_quotient_hom (G : Group) (N : BlindNor G)
  : Id (GroupHom G (normal_quotient_group G N)) (blind_quotient_hom G N) (normal_quotient_hom G N)
  ≔ refl (mkhom G (normal_quotient_group G N))
      (component_lift_project (BG G) (bg_connected G) (GSet G) (N (shape G) .gset)
        (hom_B G (normal_quotient_group G N) (normal_quotient_hom G N)))

def bridge_quotient_hom_epi : blind_quotient_hom_epi
  ≔ G N ↦ transport (GroupHom G (normal_quotient_group G N)) (IsGroupEpi G (normal_quotient_group G N))
      (normal_quotient_hom G N) (blind_quotient_hom G N)
      (inverse (GroupHom G (normal_quotient_group G N)) (blind_quotient_hom G N) (normal_quotient_hom G N) (bridge_def_quotient_hom G N))
      (normal_quotient_epi G N)

def bridge_def_q (G : Group) (hq : BlindQuotientEpi G) (N : BlindNor G)
  : Id (GroupEpis G) (blind_q G hq N) (normal_quotient_epis G N)
  ≔ chim_epis_path G (blind_q G hq N) (normal_quotient_epis G N)
      (refl (normal_quotient_group G N), bridge_def_quotient_hom G N)

{` Remark at line 1466. `}
def bridge_def_type_quotient (G : Group) (N : BlindNor G) (Y : BG G .carrier → Type) (y : BG G .carrier)
  : Id Type (BlindTypeQuotient G N Y y) (normal_quotient_family G N Y y) ≔ refl (BlindTypeQuotient G N Y y)

def bridge_principal_quotient : blind_principal_quotient
  ≔ G N y ↦ book_equivalence (normal_quotient_family G N (z ↦ Id (BG G .carrier) (shape G) z) y) (normal_family G N (shape G) y .fst)
      (normal_quotient_paths_equiv G N (shape G) y)

def bridge_torsor_quotient_component : blind_torsor_quotient_component
  ≔ G N Y ↦
    let F ≔ BG G .carrier → Type in
    let a ≔ normal_quotient_family G N (z ↦ Y .fst z .fst) in
    let b ≔ (w ↦ normal_family G N (shape G) w .fst) : F in
    mere_rec (Id F a b) (Mere (Id F b a)) (mere_isprop (Id F b a)) (r ↦ mere (Id F b a) (inverse F a b r))
      (torsor_quotient_component G N Y)

def bridge_quotient_hom_via_torsors : blind_quotient_hom_via_torsors
  ≔ G N z ↦ inverse (BG G .carrier → Type) (normal_quotient_family G N (w ↦ Id (BG G .carrier) z w)) (w ↦ normal_family G N z w .fst)
      (normal_quotient_paths_path G N z)

{` lem:qeq, for every ht and hq. `}
def bridge_qeq : blind_qeq
  ≔ G ht hq ↦
    let E ≔ GroupEpis G in let Nr ≔ NormalSubgroups G in
    (book_equivalence E Nr
       (equiv_change_map E Nr (nor_equiv G) (blind_nor G ht) (e ↦ inverse Nr (blind_nor G ht e) (nor G e) (bridge_def_nor_map G ht e))) .equiv,
     (N ↦ concat Nr (blind_nor G ht (blind_q G hq N)) (nor G (blind_q G hq N)) N
            (bridge_def_nor_map G ht (blind_q G hq N))
            (concat Nr (nor G (blind_q G hq N)) (nor G (normal_quotient_epis G N)) N
              (refl (nor G) (bridge_def_q G hq N)) (nor_q_epi_path G N)),
      e ↦ concat E (blind_q G hq (blind_nor G ht e)) (normal_quotient_epis G (blind_nor G ht e)) e
            (bridge_def_q G hq (blind_nor G ht e))
            (concat E (normal_quotient_epis G (blind_nor G ht e)) (normal_quotient_epis G (nor G e)) e
              (refl (normal_quotient_epis G) (bridge_def_nor_map G ht e)) (q_nor_epi_path G e))))

{` cor:normalisnormal. `}
def bridge_normalisnormal : blind_normalisnormal
  ≔ G ↦
    let e ≔ native_equivalence (GroupEpis G) (KernelsOf G) (kernels_equiv G) in
    (hlevel_two_to_set (GroupEpis G)
       (hlevel_equiv (suc. (suc. zero.)) (KernelsOf G) (GroupEpis G) (canonical_inverse_equiv (GroupEpis G) (KernelsOf G) e)
         (set_to_hlevel_two (KernelsOf G) (kernels_set G))),
     kernels_equiv G .equiv)

{` def:associatednormal. The blind Ass(N) (the stabilizer form) is our ass(N) (the subgroup form) in Mono(G). `}
def bridge_def_ass (G : Group) (N : BlindNor G) : Id (GroupMonos G) (blind_ass G N) (associated_kernel_mono G N)
  ≔ inverse (GroupMonos G) (associated_kernel_mono G N) (blind_ass G N) (subgroup_stabilizer_mono_path G (N (shape G)))

def bridge_ass_E : blind_ass_E
  ≔ G N ↦ transitive_stabilizer_subgroup_path G (N (shape G) .gset) (N (shape G) .point) (N (shape G) .transitive)

def bridge_ass_is_ker_q : blind_ass_is_ker_q
  ≔ G N ↦
    let Q ≔ normal_quotient_group G N in
    let M ≔ GroupMonos G in
    concat M (kernel G Q (blind_quotient_hom G N)) (kernel G Q (normal_quotient_hom G N)) (blind_ass G N)
      (refl (kernel G Q) (bridge_def_quotient_hom G N))
      (concat M (kernel G Q (normal_quotient_hom G N)) (associated_kernel_mono G N) (blind_ass G N)
        (kernel_quotient_associated_path G N)
        (inverse M (blind_ass G N) (associated_kernel_mono G N) (bridge_def_ass G N)))

def bridge_ass_is_kernel : blind_ass_is_kernel
  ≔ G N ↦ transport (GroupMonos G) (m ↦ Mere (BookFiber (GroupEpis G) (GroupMonos G) (epi_kernel G) m))
      (associated_kernel_mono G N) (blind_ass G N)
      (inverse (GroupMonos G) (blind_ass G N) (associated_kernel_mono G N) (bridge_def_ass G N))
      (associated_kernel G N .snd)

def bridge_def_ass_kernel (G : Group) (hk : BlindAssKernelProofs G) (N : BlindNor G)
  : Id (KernelsOf G) (blind_ass_kernel G hk N) (associated_kernel G N)
  ≔ subtype_equal (GroupMonos G) (m ↦ Mere (BookFiber (GroupEpis G) (GroupMonos G) (epi_kernel G) m))
      (m ↦ mere_isprop (BookFiber (GroupEpis G) (GroupMonos G) (epi_kernel G) m))
      (blind_ass_kernel G hk N) (associated_kernel G N) (bridge_def_ass G N)

{` lem:normalsarekernels, for every ht and hk. `}
def bridge_normalsarekernels : blind_normalsarekernels
  ≔ G ht hk ↦
    let K ≔ KernelsOf G in let Nr ≔ NormalSubgroups G in
    (book_equivalence Nr K
       (equiv_change_map Nr K (associated_kernel_equiv G) (blind_ass_kernel G hk)
         (N ↦ inverse K (blind_ass_kernel G hk N) (associated_kernel G N) (bridge_def_ass_kernel G hk N))) .equiv,
     e ↦ concat K (blind_ass_kernel G hk (blind_nor G ht e)) (associated_kernel G (blind_nor G ht e)) (epis_to_kernels G e)
           (bridge_def_ass_kernel G hk (blind_nor G ht e))
           (concat K (associated_kernel G (blind_nor G ht e)) (associated_kernel G (nor G e)) (epis_to_kernels G e)
             (refl (associated_kernel G) (bridge_def_nor_map G ht e)) (associated_kernel_nor_epi G e)))

{` lem:characterizations of normal, first three equivalences (the fourth, with the abstract monomorphisms, is in
   bridge-06b). `}
def bridge_characterizations_of_normal_123 (G : Group)
  : Product (Equiv (BlindEpi G) (BlindKernels G)) (Product (Equiv (BlindKernels G) (BlindNor G)) (Equiv (BlindNor G) (BlindFixMono G)))
  ≔ (native_equivalence (GroupEpis G) (KernelsOf G) (kernels_equiv G),
     (canonical_inverse_equiv (NormalSubgroups G) (KernelsOf G) (associated_kernel_equiv G),
      canonical_inverse_equiv (InvariantMaps G (monos_gset G)) (NormalSubgroups G) (monos_fixed_points_equiv G)))
