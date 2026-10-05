export "905-normal-quotient-equivalence"

{` Chapter 9 (subgroups.tex), sec:normal and sec:assker: the remark after
   def:ker2, the injectivity part of cor:normalisnormal, def:associatednormal
   and the commutativity part of lem:normalsarekernels. The statements on the
   book's Epi(G) that need the hard direction of lem:epi-surj are in
   module 907. `}

{` The remark after def:ker2: the G-set P_{f(y)} ∘ f is a G-torsor exactly
   when f is an isomorphism. Its action type is (judgmentally) the fiber of
   Bf at Bf(y); a G-set is a torsor iff its action type is contractible. `}
def torsor_action_type_contractible (G : Group) (X : GSet G) (t : Mere (Id (GSet G) (principal_gset G) X))
  : BookIsContr (ActionType G X)
  ≔ mere_transport native_truncation (GSet G) (Y ↦ BookIsContr (ActionType G Y))
      (Y ↦ book_iscontr_isprop (ActionType G Y)) (principal_gset G) X t
      (gset_paths_action_type_contractible G (shape G))

def contractible_action_type_torsor (G : Group) (X : GSet G) (h : BookIsContr (ActionType G X))
  : Mere (Id (GSet G) (principal_gset G) X)
  ≔ free_transitive_torsor G X
      (x ↦ gset_contractible_component (ActionType G X) h (shape G, x))
      (connected_action_type_transitive G X (contractible_connected (ActionType G X) h))

def nor_gset_torsor_iff_iso (G H : Group) (f : GroupHom G H) (y : BG G .carrier)
  : Product (Mere (Id (GSet G) (principal_gset G) (nor_gset G H f y)) → IsGroupIso G H f)
      (IsGroupIso G H f → Mere (Id (GSet G) (principal_gset G) (nor_gset G H f y)))
  ≔ (t ↦ connected_based_elim native_truncation (BG H .carrier) (bg_connected H) (hom_function G H f y)
          (w ↦ BookIsContr (HomFiber G H f w)) (w ↦ book_iscontr_isprop (HomFiber G H f w))
          (torsor_action_type_contractible G (nor_gset G H f y) t),
     h ↦ contractible_action_type_torsor G (nor_gset G H f y) (h (hom_function G H f y)))

{` E⁻¹ ∘ i ∘ nor = ker on homomorphisms with connected fibers (the
   lem:diagfornormal square read in Mono(G)). `}
def kernel_from_nor_path (G : Group) (e : ConnectedEpis G)
  : Id (GroupMonos G) (subgroup_to_mono G (normal_to_subgroup G (nor_conn G e))) (connected_epi_kernel G e)
  ≔ let H ≔ e .fst in let f ≔ e .snd .fst in let c ≔ e .snd .snd in
    concat (GroupMonos G) (subgroup_to_mono G (normal_to_subgroup G (nor_conn G e)))
      (subgroup_to_mono G (mono_to_subgroup G (kernel G H f))) (kernel G H f)
      (map_path (Subgroups G) (GroupMonos G) (subgroup_to_mono G)
        (normal_to_subgroup G (nor_conn G e)) (mono_to_subgroup G (kernel G H f)) (diag_for_normal G H f c))
      (mono_subgroup_roundtrip G (kernel G H f))

{` cor:normalisnormal, injectivity: on homomorphisms with connected fibers
   the kernel determines the homomorphism (ker e = ker e' ⇒ i(nor e) =
   i(nor e') ⇒ nor e = nor e' ⇒ e = e' by lem:qeq). `}
def connected_kernel_injective (G : Group) (e e' : ConnectedEpis G)
  (p : Id (GroupMonos G) (connected_epi_kernel G e) (connected_epi_kernel G e')) : Id (ConnectedEpis G) e e'
  ≔ let S ≔ Subgroups G in
    let iN : ConnectedEpis G → S ≔ u ↦ normal_to_subgroup G (nor_conn G u) in
    let sub_eq : Id S (iN e) (iN e')
      ≔ calc
          iN e
          = mono_to_subgroup G (connected_epi_kernel G e)
            by diag_for_normal G (e .fst) (e .snd .fst) (e .snd .snd)
          = mono_to_subgroup G (connected_epi_kernel G e')
            by map_path (GroupMonos G) S (mono_to_subgroup G) (connected_epi_kernel G e) (connected_epi_kernel G e') p
          = iN e'
            by inverse S (iN e') (mono_to_subgroup G (connected_epi_kernel G e'))
                 (diag_for_normal G (e' .fst) (e' .snd .fst) (e' .snd .snd)) ∎ in
    let nor_eq : Id (NormalSubgroups G) (nor_conn G e) (nor_conn G e')
      ≔ refl ((t ↦ t .fst) : BookFiber (NormalSubgroups G) S (normal_to_subgroup G) (iN e) → NormalSubgroups G)
          (normal_to_subgroup_injective G (iN e) (nor_conn G e, refl (iN e)) (nor_conn G e', sub_eq)) in
    equivalence_injective (ConnectedEpis G) (NormalSubgroups G) (nor_conn_equiv G) e e' nor_eq

{` def:associatednormal. ass(N) ≔ E⁻¹ i(N) : Mono(G), with group
   Ass(N) = Aut_{Σ_x X_{sh_G}(x)}(sh_G, pt_{sh_G}) (subgroup_group) and the
   first projection; it is the kernel of q(N): ker q(N) = ass(N) in Mono(G)
   (the identification goes through lem:diagfornormal, lem:qeq and
   lem:SubG=MonoG; the book's explicit form is ev_{x sh_G}). `}
def associated_kernel_mono (G : Group) (N : NormalSubgroups G) : GroupMonos G
  ≔ subgroup_to_mono G (normal_to_subgroup G N)

def associated_kernel_group (G : Group) (N : NormalSubgroups G)
  : Id Group (associated_kernel_mono G N .fst) (subgroup_group G (N (shape G)))
  ≔ refl (subgroup_group G (N (shape G)))

def kernel_quotient_associated_path (G : Group) (N : NormalSubgroups G)
  : Id (GroupMonos G) (connected_epi_kernel G (normal_quotient_connected_epis G N)) (associated_kernel_mono G N)
  ≔ let M ≔ GroupMonos G in
    let e ≔ normal_quotient_connected_epis G N in
    concat M (connected_epi_kernel G e) (subgroup_to_mono G (normal_to_subgroup G (nor_conn G e)))
      (associated_kernel_mono G N)
      (inverse M (subgroup_to_mono G (normal_to_subgroup G (nor_conn G e))) (connected_epi_kernel G e)
        (kernel_from_nor_path G e))
      (map_path (NormalSubgroups G) M (associated_kernel_mono G) (nor_conn G e) N (nor_q_path G N))

def associated_kernel (G : Group) (N : NormalSubgroups G) : KernelsOf G
  ≔ (associated_kernel_mono G N,
     mere (BookFiber (GroupEpis G) (GroupMonos G) (epi_kernel G) (associated_kernel_mono G N))
       (normal_quotient_epis G N,
        inverse (GroupMonos G) (connected_epi_kernel G (normal_quotient_connected_epis G N)) (associated_kernel_mono G N)
          (kernel_quotient_associated_path G N)))

{` lem:normalsarekernels, commutativity. (1) i ∘ ass = E⁻¹ ∘ i (by
   definition); (2) E ∘ i ∘ ass = i (lem:SubG=MonoG); (3) ass ∘ nor = ker on
   homomorphisms with connected fibers (as elements of the set of kernels). `}
def associated_kernel_include (G : Group) (N : NormalSubgroups G)
  : Id (GroupMonos G) (kernels_include G (associated_kernel G N)) (subgroup_to_mono G (normal_to_subgroup G N))
  ≔ refl (subgroup_to_mono G (normal_to_subgroup G N))

def associated_kernel_subgroup (G : Group) (N : NormalSubgroups G)
  : Id (Subgroups G) (mono_to_subgroup G (kernels_include G (associated_kernel G N))) (normal_to_subgroup G N)
  ≔ subgroup_mono_roundtrip G (normal_to_subgroup G N)

def connected_epi_as_epi (G : Group) (e : ConnectedEpis G) : GroupEpis G
  ≔ (e .fst, (e .snd .fst, gepi_connected_fibers_epi G (e .fst) (e .snd .fst) (e .snd .snd)))

def associated_kernel_nor (G : Group) (e : ConnectedEpis G)
  : Id (KernelsOf G) (associated_kernel G (nor_conn G e)) (epis_to_kernels G (connected_epi_as_epi G e))
  ≔ subtype_equal (GroupMonos G) (m ↦ Mere (BookFiber (GroupEpis G) (GroupMonos G) (epi_kernel G) m))
      (m ↦ mere_isprop (BookFiber (GroupEpis G) (GroupMonos G) (epi_kernel G) m))
      (associated_kernel G (nor_conn G e)) (epis_to_kernels G (connected_epi_as_epi G e))
      (kernel_from_nor_path G e)
