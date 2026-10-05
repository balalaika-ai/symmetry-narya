export "915-what-sylow-needs"
export "822-pullback-group-symmetries"

{` Chapter 9 (subgroups.tex), the exercise at line 1825: lem:whatSylow2needs
   (modules 914/915) written out with subgroups S : Sub(G) instead of
   monomorphisms (H, i) : Mono(G).

   For subgroups N, S of G, N ∩ S is the subgroup of S given by the
   pullback of the inclusions of N and S (projection to S, a monomorphism
   since N's inclusion is one), transported to Sub(S) by E
   (subgroup_intersection_sub). Let f : Hom(G, G') have connected fibers
   (an epimorphism, lem:epi-surj) and N ≔ E(ker f) : Sub(G). Then
   (1) N ∩ S = E(ker(f ∘ i_S)) in Sub(S), and
   (2) the homomorphism S/(N ∩ S) → G' induced by f ∘ i_S is a
   monomorphism with k ∘ q = f ∘ i_S, where S is the underlying group
   subgroup_group G S and i_S its inclusion. `}

def intersection_into_mono (G : Group) (S : Subgroups G) (m : GroupMonos G) : GroupMonos (subgroup_group G S)
  ≔ (pullback_group G (m .fst) (subgroup_group G S) (m .snd .fst) (subgroup_inclusion G S),
     (pullback_group_proj_right G (m .fst) (subgroup_group G S) (m .snd .fst) (subgroup_inclusion G S),
      pullback_group_proj_right_mono G (m .fst) (subgroup_group G S) (m .snd .fst) (subgroup_inclusion G S) (m .snd .snd)))

{` N ∩ S as a monomorphism into S and as a subgroup of S. `}
def subgroup_intersection_mono (G : Group) (N S : Subgroups G) : GroupMonos (subgroup_group G S)
  ≔ intersection_into_mono G S (subgroup_to_mono G N)

def subgroup_intersection_sub (G : Group) (N S : Subgroups G) : Subgroups (subgroup_group G S)
  ≔ mono_to_subgroup (subgroup_group G S) (subgroup_intersection_mono G N S)

{` (1) in Sub(S): E(ker f) ∩ S = E(ker(f ∘ i_S)). `}
def sub_what_sylow_needs_kernel (G G' : Group) (f : GroupHom G G') (c : IsConnectedHom G G' f) (S : Subgroups G)
  : Id (Subgroups (subgroup_group G S))
      (subgroup_intersection_sub G (mono_to_subgroup G (kernel G G' f)) S)
      (mono_to_subgroup (subgroup_group G S)
        (kernel (subgroup_group G S) G' (group_hom_compose (subgroup_group G S) G G' (subgroup_inclusion G S) f)))
  ≔ let H ≔ subgroup_group G S in
    let i ≔ subgroup_inclusion G S in
    let K ≔ kernel G G' f in
    let MH ≔ GroupMonos H in
    map_path MH (Subgroups H) (mono_to_subgroup H)
      (intersection_into_mono G S (subgroup_to_mono G (mono_to_subgroup G K)))
      (kernel H G' (group_hom_compose H G G' i f))
      (calc
        intersection_into_mono G S (subgroup_to_mono G (mono_to_subgroup G K))
        = intersection_into_mono G S K
          by map_path (GroupMonos G) MH (intersection_into_mono G S) (subgroup_to_mono G (mono_to_subgroup G K)) K
               (mono_subgroup_roundtrip G K)
        = wsn_intersection_as_mono G G' H f i c
          by group_monos_path_same H (intersection_into_mono G S K .fst) (intersection_into_mono G S K .snd .fst)
               (wsn_intersection_as_mono G G' H f i c .snd .fst) (intersection_into_mono G S K .snd .snd)
               (wsn_intersection_as_mono G G' H f i c .snd .snd)
               (refl (intersection_into_mono G S K .snd .fst))
        = kernel H G' (group_hom_compose H G G' i f) by what_sylow_needs_kernel G G' H f i c ∎)

{` (2) for S : Sub(G): the induced S/(N ∩ S) ≡ kernel_quotient_group of
   f ∘ i_S → G' is a monomorphism and k ∘ q = f ∘ i_S. `}
def sub_what_sylow_needs_induced (G G' : Group) (f : GroupHom G G') (S : Subgroups G)
  : Σ (GroupHom (kernel_quotient_group (subgroup_group G S) G' (group_hom_compose (subgroup_group G S) G G' (subgroup_inclusion G S) f)) G')
      (k ↦ Product
        (IsGroupMono (kernel_quotient_group (subgroup_group G S) G' (group_hom_compose (subgroup_group G S) G G' (subgroup_inclusion G S) f)) G' k)
        (Id (GroupHom (subgroup_group G S) G')
          (group_hom_compose (subgroup_group G S)
            (kernel_quotient_group (subgroup_group G S) G' (group_hom_compose (subgroup_group G S) G G' (subgroup_inclusion G S) f)) G'
            (normal_quotient_hom (subgroup_group G S)
              (kernel_normal_subgroup (subgroup_group G S) G' (group_hom_compose (subgroup_group G S) G G' (subgroup_inclusion G S) f)))
            k)
          (group_hom_compose (subgroup_group G S) G G' (subgroup_inclusion G S) f)))
  ≔ what_sylow_needs_induced G G' (subgroup_group G S) f (subgroup_inclusion G S)
