export "906-associated-kernels"
export "934-epi-connected-fibers"

{` Chapter 9 (subgroups.tex), sec:normal and sec:assker, on the book's
   Epi(G): lem:qeq (nor : Epi(G) ≃ Nor(G) with inverse q),
   cor:normalisnormal, lem:normalsarekernels (ass is an equivalence) and
   items (1)-(4) of lem:characterizations of normal. Epimorphisms and
   homomorphisms with connected fibers are identified by lem:epi-surj
   (module 934). `}

def epis_to_connected (G : Group) (e : GroupEpis G) : ConnectedEpis G
  ≔ (e .fst, (e .snd .fst, gepi_epi_connected_fibers G (e .fst) (e .snd .fst) (e .snd .snd)))

def epis_connected_equiv (G : Group) : Equiv (GroupEpis G) (ConnectedEpis G)
  ≔ quasi_inverse_equiv (GroupEpis G) (ConnectedEpis G) (epis_to_connected G) (connected_epi_as_epi G)
      (e ↦ map_path (IsGroupEpi G (e .fst) (e .snd .fst)) (GroupEpis G) (x ↦ (e .fst, (e .snd .fst, x)))
        (connected_epi_as_epi G (epis_to_connected G e) .snd .snd) (e .snd .snd)
        (is_group_epi_prop G (e .fst) (e .snd .fst) (connected_epi_as_epi G (epis_to_connected G e) .snd .snd) (e .snd .snd)))
      (c ↦ map_path (IsConnectedHom G (c .fst) (c .snd .fst)) (ConnectedEpis G) (x ↦ (c .fst, (c .snd .fst, x)))
        (epis_to_connected G (connected_epi_as_epi G c) .snd .snd) (c .snd .snd)
        (is_connected_hom_prop G (c .fst) (c .snd .fst) (epis_to_connected G (connected_epi_as_epi G c) .snd .snd) (c .snd .snd)))

{` def:ker2 on Epi(G): nor(G', f, !)(y) ≔ (P_{f(y)} ∘ f, refl_{f(y)}, !). `}
def nor (G : Group) (e : GroupEpis G) : NormalSubgroups G ≔ nor_conn G (epis_to_connected G e)

{` lem:qeq: nor : Epi(G) → Nor(G) is an equivalence with inverse q. `}
def nor_equiv (G : Group) : Equiv (GroupEpis G) (NormalSubgroups G)
  ≔ compose_equiv (GroupEpis G) (ConnectedEpis G) (NormalSubgroups G) (epis_connected_equiv G) (nor_conn_equiv G)

def nor_q_epi_path (G : Group) (N : NormalSubgroups G) : Id (NormalSubgroups G) (nor G (normal_quotient_epis G N)) N
  ≔ concat (NormalSubgroups G) (nor G (normal_quotient_epis G N)) (nor_conn G (normal_quotient_connected_epis G N)) N
      (map_path (IsConnectedHom G (normal_quotient_group G N) (normal_quotient_hom G N)) (NormalSubgroups G)
        (x ↦ nor_conn G (normal_quotient_group G N, (normal_quotient_hom G N, x)))
        (epis_to_connected G (normal_quotient_epis G N) .snd .snd) (normal_quotient_connected G N)
        (is_connected_hom_prop G (normal_quotient_group G N) (normal_quotient_hom G N)
          (epis_to_connected G (normal_quotient_epis G N) .snd .snd) (normal_quotient_connected G N)))
      (nor_q_path G N)

def q_nor_epi_path (G : Group) (e : GroupEpis G) : Id (GroupEpis G) (normal_quotient_epis G (nor G e)) e
  ≔ equivalence_injective (GroupEpis G) (NormalSubgroups G) (nor_equiv G) (normal_quotient_epis G (nor G e)) e
      (nor_q_epi_path G (nor G e))

{` cor:normalisnormal: ker : Epi(G) → Ker_G is an equivalence of sets. `}
def epis_to_kernels_injective (G : Group) : IsEmbedding (GroupEpis G) (KernelsOf G) (epis_to_kernels G)
  ≔ path_reflecting_set_embedding (GroupEpis G) (KernelsOf G) (kernels_set G) (epis_to_kernels G)
      (e e' p ↦ equivalence_injective (GroupEpis G) (ConnectedEpis G) (epis_connected_equiv G) e e'
        (connected_kernel_injective G (epis_to_connected G e) (epis_to_connected G e')
          (map_path (KernelsOf G) (GroupMonos G) (kernels_include G) (epis_to_kernels G e) (epis_to_kernels G e') p)))

def kernels_equiv (G : Group) : BookEquiv (GroupEpis G) (KernelsOf G)
  ≔ embedding_surjection_equiv native_truncation (GroupEpis G) (KernelsOf G) (epis_to_kernels G)
      (epis_to_kernels_injective G) (epis_to_kernels_surjective G)

{` lem:normalsarekernels: ass ∘ nor = ker, hence ass : Nor(G) → Ker_G is an
   equivalence (the remaining commutativity statements are in module 906). `}
def associated_kernel_nor_epi (G : Group) (e : GroupEpis G)
  : Id (KernelsOf G) (associated_kernel G (nor G e)) (epis_to_kernels G e)
  ≔ concat (KernelsOf G) (associated_kernel G (nor G e)) (epis_to_kernels G (connected_epi_as_epi G (epis_to_connected G e)))
      (epis_to_kernels G e)
      (associated_kernel_nor G (epis_to_connected G e))
      (map_path (GroupEpis G) (KernelsOf G) (epis_to_kernels G) (connected_epi_as_epi G (epis_to_connected G e)) e
        (equiv_retraction (GroupEpis G) (ConnectedEpis G) (epis_connected_equiv G) e))

def associated_kernel_equiv (G : Group) : Equiv (NormalSubgroups G) (KernelsOf G)
  ≔ equiv_change_map (NormalSubgroups G) (KernelsOf G)
      (compose_equiv (NormalSubgroups G) (GroupEpis G) (KernelsOf G)
        (canonical_inverse_equiv (GroupEpis G) (NormalSubgroups G) (nor_equiv G))
        (native_equivalence (GroupEpis G) (KernelsOf G) (kernels_equiv G)))
      (associated_kernel G)
      (N ↦ let e ≔ equiv_inverse_map (GroupEpis G) (NormalSubgroups G) (nor_equiv G) N in
        concat (KernelsOf G) (epis_to_kernels G e) (associated_kernel G (nor G e)) (associated_kernel G N)
          (inverse (KernelsOf G) (associated_kernel G (nor G e)) (epis_to_kernels G e) (associated_kernel_nor_epi G e))
          (map_path (NormalSubgroups G) (KernelsOf G) (associated_kernel G) (nor G e) N
            (equiv_counit (GroupEpis G) (NormalSubgroups G) (nor_equiv G) N)))

{` lem:characterizations of normal, items (1)-(4): Epi(G) ≃ Ker_G ≃ Nor(G)
   ≃ fixed points of the G-set Mono(G). Item (5) (abstract subgroups) is
   in module 916. `}
def monos_fixed_points_equiv (G : Group) : Equiv (InvariantMaps G (monos_gset G)) (NormalSubgroups G)
  ≔ id_to_equiv (InvariantMaps G (monos_gset G)) (NormalSubgroups G)
      (map_path (GSet G) Type (InvariantMaps G) (monos_gset G) (subgroups_gset G) (monos_subgroups_gset_path G))

def characterizations_of_normal (G : Group)
  : Product (Product (BookEquiv (GroupEpis G) (KernelsOf G)) (Equiv (GroupEpis G) (NormalSubgroups G)))
      (Product (Equiv (KernelsOf G) (NormalSubgroups G)) (Equiv (InvariantMaps G (monos_gset G)) (NormalSubgroups G)))
  ≔ ((kernels_equiv G, nor_equiv G),
     (canonical_inverse_equiv (NormalSubgroups G) (KernelsOf G) (associated_kernel_equiv G), monos_fixed_points_equiv G))
