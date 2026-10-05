export "902-subgroup-gsets"
export "508-stabilizer-subgroups"

{` Chapter 9 (subgroups.tex), sec:normal, part 1: def:normalsubgroup and the
   remark after it, def:setofkernels, def:ker2 and lem:diagfornormal.

   def:ker2 needs that the epimorphism f has connected fibers (so that the
   G-set P_{f(y)} ∘ f is transitive). It is defined here on the type
   ConnectedEpis G of homomorphisms out of G whose classifying map has
   connected fibers (condition (3') of lem:epi-surj); the book's version on
   Epi(G) is obtained by composing with lem:epi-surj (module 934, see
   module 907). `}

{` def:normalsubgroup. Nor(G) ≔ Π_{y:BG} Sub(G)(y), the fixed points of the
   G-set Sub(G), with i(N) ≔ N(sh_G). `}
def NormalSubgroups (G : Group) : Type ≔ InvariantMaps G (subgroups_gset G)

def normal_subgroups_set (G : Group) : isSet (NormalSubgroups G) ≔ invariant_maps_set G (subgroups_gset G)

def normal_to_subgroup (G : Group) (N : NormalSubgroups G) : Subgroups G ≔ N (shape G)

{` The remark after def:normalsubgroup: i is an injection (two sections of
   the set family Sub(G) over the connected BG agreeing at sh_G agree). `}
def normal_to_subgroup_injective (G : Group)
  : IsEmbedding (NormalSubgroups G) (Subgroups G) (normal_to_subgroup G)
  ≔ path_reflecting_set_embedding (NormalSubgroups G) (Subgroups G) (subgroups_set G) (normal_to_subgroup G)
      (N N' e ↦ invariant_maps_eq_at_shape G (subgroups_gset G) N N' e)

{` "A subgroup H of G is said to be normal whenever the fiber i⁻¹(H) has a
   (necessarily propositionally unique) element." `}
def IsNormalSubgroup (G : Group) (S : Subgroups G) : Type
  ≔ BookFiber (NormalSubgroups G) (Subgroups G) (normal_to_subgroup G) S

def is_normal_subgroup_prop (G : Group) (S : Subgroups G) : isProp (IsNormalSubgroup G S)
  ≔ normal_to_subgroup_injective G S

{` A subgroup is normal iff it is a fixed point of the action of G on
   Sub(G): g · (X, x) ≔ (X, g ·_X x) = (X, x) for all g : USym G. `}
def SubgroupFixedByAll (G : Group) (S : Subgroups G) : Type
  ≔ (g : USym G) → Id (Subgroups G) (subgroups_move G (shape G) (shape G) g S) S

def subgroup_fixed_by_all_prop (G : Group) (S : Subgroups G) : isProp (SubgroupFixedByAll G S)
  ≔ pi_prop (USym G) (g ↦ Id (Subgroups G) (subgroups_move G (shape G) (shape G) g S) S)
      (g ↦ subgroups_set G (subgroups_move G (shape G) (shape G) g S) S)

def normal_subgroup_fixed (G : Group) (S : Subgroups G) (h : IsNormalSubgroup G S) : SubgroupFixedByAll G S
  ≔ g ↦
    let N ≔ h .fst in
    let e : Id (Subgroups G) S (N (shape G)) ≔ h .snd in
    let X ≔ subgroups_gset G in
    calc
      subgroups_move G (shape G) (shape G) g S
      = subgroups_move G (shape G) (shape G) g (N (shape G))
        by refl (subgroups_move G (shape G) (shape G) g) e
      = gset_usym_act G X g (N (shape G))
        by inverse (Subgroups G) (gset_usym_act G X g (N (shape G))) (subgroups_move G (shape G) (shape G) g (N (shape G)))
             (subgroups_gset_usym_act G g (N (shape G)))
      = N (shape G) by invariant_map_fixed G X N .snd g
      = S by inverse (Subgroups G) S (N (shape G)) e ∎

def fixed_normal_subgroup (G : Group) (S : Subgroups G) (fix : SubgroupFixedByAll G S) : IsNormalSubgroup G S
  ≔ let X ≔ subgroups_gset G in
    let fix' : (g : USym G) → Id (Subgroups G) (gset_usym_act G X g S) S
      ≔ g ↦ concat (Subgroups G) (gset_usym_act G X g S) (subgroups_move G (shape G) (shape G) g S) S
          (subgroups_gset_usym_act G g S) (fix g) in
    (gset_fixed_point_extension G X S fix',
     inverse (Subgroups G) (gset_fixed_point_extension G X S fix' (shape G)) S
       (gset_fixed_point_extension_beta G X S fix'))

def normal_iff_fixed (G : Group) (S : Subgroups G)
  : Product (IsNormalSubgroup G S → SubgroupFixedByAll G S) (SubgroupFixedByAll G S → IsNormalSubgroup G S)
  ≔ (normal_subgroup_fixed G S, fixed_normal_subgroup G S)

{` In terms of pointed G-sets: (X, x) is normal iff for every g there is an
   identification of pointed G-sets (X, g ·_X x) = (X, x), i.e. a G-set
   automorphism of X carrying g · x to x. `}
def fixed_from_pointed_paths (G : Group) (S : Subgroups G)
  (h : (g : USym G) → Id (PointedGSet G) (S .gset, gset_usym_act G (S .gset) g (S .point)) (S .gset, S .point))
  : SubgroupFixedByAll G S
  ≔ g ↦ subgroup_path G (subgroups_move G (shape G) (shape G) g S) S (h g)

def pointed_paths_from_fixed (G : Group) (S : Subgroups G) (fix : SubgroupFixedByAll G S) (g : USym G)
  : Id (PointedGSet G) (S .gset, gset_usym_act G (S .gset) g (S .point)) (S .gset, S .point)
  ≔ refl ((T ↦ (T .gset, T .point)) : Subgroups G → PointedGSet G) (fix g)

{` def:setofkernels. ker : Epi(G) → Mono(G) and its surjection/injection
   factorization through the propositional image, the set of kernels. `}
def epi_kernel (G : Group) (e : GroupEpis G) : GroupMonos G ≔ kernel G (e .fst) (e .snd .fst)

def KernelsOf (G : Group) : Type ≔ Image (GroupEpis G) (GroupMonos G) (epi_kernel G)

def kernels_include (G : Group) : KernelsOf G → GroupMonos G ≔ image_include (GroupEpis G) (GroupMonos G) (epi_kernel G)

def kernels_include_injective (G : Group) : IsEmbedding (KernelsOf G) (GroupMonos G) (kernels_include G)
  ≔ image_include_embedding (GroupEpis G) (GroupMonos G) (epi_kernel G)

def epis_to_kernels (G : Group) : GroupEpis G → KernelsOf G ≔ image_factor (GroupEpis G) (GroupMonos G) (epi_kernel G)

def epis_to_kernels_surjective (G : Group) : Surjective (GroupEpis G) (KernelsOf G) (epis_to_kernels G)
  ≔ image_factor_surjective (GroupEpis G) (GroupMonos G) (epi_kernel G)

def kernels_set (G : Group) : isSet (KernelsOf G)
  ≔ image_set (GroupEpis G) (GroupMonos G) (epi_kernel G) (group_monos_set G)

{` Homomorphisms whose classifying map has connected fibers (lem:epi-surj
   (3')), and the type of such homomorphisms out of G. `}
def IsConnectedHom (G H : Group) (f : GroupHom G H) : Type
  ≔ ConnectedFibers (BG G .carrier) (BG H .carrier) (hom_function G H f)

def is_connected_hom_prop (G H : Group) (f : GroupHom G H) : isProp (IsConnectedHom G H f)
  ≔ pi_prop (BG H .carrier) (w ↦ Connected (HomFiber G H f w)) (w ↦ connected_isprop (HomFiber G H f w))

def ConnectedEpis (G : Group) : Type ≔ Σ Group (H ↦ Σ (GroupHom G H) (f ↦ IsConnectedHom G H f))

def connected_epi_kernel (G : Group) (e : ConnectedEpis G) : GroupMonos G ≔ kernel G (e .fst) (e .snd .fst)

{` def:ker2. nor(H, f, !)(y) ≔ (P_{f(y)} ∘ f, refl_{f(y)}, !) : Sub(G)(y). `}
def nor_gset (G H : Group) (f : GroupHom G H) (y : BG G .carrier) : GSet G
  ≔ gset_restrict G H f (gset_paths H (hom_function G H f y))

def nor_gset_value (G H : Group) (f : GroupHom G H) (y z : BG G .carrier)
  : Id Type (nor_gset G H f y z .fst) (Id (BG H .carrier) (hom_function G H f y) (hom_function G H f z))
  ≔ refl (Id (BG H .carrier) (hom_function G H f y) (hom_function G H f z))

def nor_subgroup (G H : Group) (f : GroupHom G H) (c : IsConnectedHom G H f) (y : BG G .carrier)
  : Subgroups (group_at G y)
  ≔ (nor_gset G H f y, refl (hom_function G H f y),
     connected_action_type_transitive (group_at G y) (nor_gset G H f y) (c (hom_function G H f y)))

def nor_conn (G : Group) (e : ConnectedEpis G) : NormalSubgroups G
  ≔ y ↦ nor_subgroup G (e .fst) (e .snd .fst) (e .snd .snd) y

{` lem:diagfornormal. For an epimorphism f (connected fibers), going around
   the top, E(ker f), is the G-set z ↦ (sh_H = f(z)) pointed at Bf_pt;
   around the bottom, i(nor f), it is z ↦ (f(sh_G) = f(z)) pointed at refl;
   pre-composition with Bf_pt⁻¹ identifies them. First: E(ker f) is the
   pointed G-set f^*P_H at Bf_pt (ker f is the stabilizer monomorphism, and
   f^*P_H is transitive since the fiber of Bf is connected). `}
def kernel_gset_transitive (G H : Group) (f : GroupHom G H) (c : IsConnectedHom G H f)
  : IsTransitive G (kernel_gset G H f)
  ≔ connected_action_type_transitive G (kernel_gset G H f) (c (shape H))

def kernel_subgroup_path (G H : Group) (f : GroupHom G H) (c : IsConnectedHom G H f)
  : Id (Subgroups G) (mono_to_subgroup G (kernel G H f)) (kernel_gset G H f, hom_point G H f, kernel_gset_transitive G H f c)
  ≔ transitive_stabilizer_subgroup_path G (kernel_gset G H f) (hom_point G H f) (kernel_gset_transitive G H f c)

def kernel_nor_subgroup_path (G H : Group) (f : GroupHom G H) (c : IsConnectedHom G H f)
  : Id (Subgroups G) (kernel_gset G H f, hom_point G H f, kernel_gset_transitive G H f c) (nor_subgroup G H f c (shape G))
  ≔ let B ≔ BG H .carrier in let Bf ≔ hom_function G H f in let p ≔ hom_point G H f in
    subgroup_path G (kernel_gset G H f, p, kernel_gset_transitive G H f c) (nor_subgroup G H f c (shape G))
      (pointed_gset_path G (kernel_gset G H f) (nor_gset G H f (shape G)) p (refl (Bf (shape G)))
        (z ↦ concat_left_equiv B (Bf (shape G)) (shape H) (Bf z) (inverse B (shape H) (Bf (shape G)) p))
        (concat_inverse_left B (shape H) (Bf (shape G)) p))

def diag_for_normal (G H : Group) (f : GroupHom G H) (c : IsConnectedHom G H f)
  : Id (Subgroups G) (normal_to_subgroup G (nor_conn G (H, (f, c)))) (mono_to_subgroup G (kernel G H f))
  ≔ inverse (Subgroups G) (mono_to_subgroup G (kernel G H f)) (nor_subgroup G H f c (shape G))
      (concat (Subgroups G) (mono_to_subgroup G (kernel G H f))
        (kernel_gset G H f, hom_point G H f, kernel_gset_transitive G H f c) (nor_subgroup G H f c (shape G))
        (kernel_subgroup_path G H f c) (kernel_nor_subgroup_path G H f c))

{` Kernels of epimorphisms are normal subgroups. `}
def kernel_normal (G H : Group) (f : GroupHom G H) (c : IsConnectedHom G H f)
  : IsNormalSubgroup G (mono_to_subgroup G (kernel G H f))
  ≔ (nor_conn G (H, (f, c)), inverse (Subgroups G) (normal_to_subgroup G (nor_conn G (H, (f, c))))
      (mono_to_subgroup G (kernel G H f)) (diag_for_normal G H f c))
