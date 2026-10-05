export "906-associated-kernels"

{` symmetry.tex, thm:fund-thm-homs (Fundamental Theorem of Homomorphisms):
   for f : Hom(G, G'), G/ker f ≃ im f. The book's map is "TODO"; we use the
   isomorphism Q of lem:qeq for the projection p(f) : G → Img(f) onto the
   image (an epimorphism with connected fibers). The normal subgroup
   "ker f" is nor(p(f)), whose underlying subgroup is E(ker p(f))
   (lem:diagfornormal); ker p(f) = ker f is lem:kerandcoker. `}

def image_projection_connected_epi (G H : Group) (f : GroupHom G H) : ConnectedEpis G
  ≔ (image_group G H f, (image_projection G H f, image_projection_connected_fibers G H f))

{` ker f as a normal subgroup of G. `}
def kernel_normal_subgroup (G H : Group) (f : GroupHom G H) : NormalSubgroups G
  ≔ nor_conn G (image_projection_connected_epi G H f)

def kernel_normal_subgroup_underlying (G H : Group) (f : GroupHom G H)
  : Id (Subgroups G) (normal_to_subgroup G (kernel_normal_subgroup G H f))
      (mono_to_subgroup G (kernel G (image_group G H f) (image_projection G H f)))
  ≔ diag_for_normal G (image_group G H f) (image_projection G H f) (image_projection_connected_fibers G H f)

{` The quotient G/ker f and the isomorphism Img(f) ≅ G/ker f. `}
def kernel_quotient_group (G H : Group) (f : GroupHom G H) : Group
  ≔ normal_quotient_group G (kernel_normal_subgroup G H f)

def fundamental_theorem_homs (G H : Group) (f : GroupHom G H)
  : GroupIso (image_group G H f) (kernel_quotient_group G H f)
  ≔ (qeq_Q G (image_group G H f) (image_projection G H f) (image_projection_connected_fibers G H f),
     qeq_Q_iso G (image_group G H f) (image_projection G H f) (image_projection_connected_fibers G H f))

def fundamental_theorem_homs_path (G H : Group) (f : GroupHom G H)
  : Id Group (kernel_quotient_group G H f) (image_group G H f)
  ≔ inverse Group (image_group G H f) (kernel_quotient_group G H f)
      (group_path_from_iso (image_group G H f) (kernel_quotient_group G H f) (fundamental_theorem_homs G H f))

{` The isomorphism is compatible with the projections: Q ∘ p(f) = q_{ker f},
   so f = i(f) ∘ Q⁻¹ ∘ q_{ker f} (with image_factorization_path). `}
def fundamental_theorem_homs_compat (G H : Group) (f : GroupHom G H)
  : Id (GroupHom G (kernel_quotient_group G H f))
      (group_hom_compose G (image_group G H f) (kernel_quotient_group G H f) (image_projection G H f)
        (fundamental_theorem_homs G H f .fst))
      (normal_quotient_hom G (kernel_normal_subgroup G H f))
  ≔ qeq_Q_compose_path G (image_group G H f) (image_projection G H f) (image_projection_connected_fibers G H f)

{` Litmus: for the identity of Σ_3, the quotient by the kernel is
   isomorphic to the image. (The point of the litmus is that the
   statement instantiates at a concrete non-abelian group.) `}
def fundamental_theorem_homs_sigma3
  : GroupIso (image_group (symmetric_group three) (symmetric_group three) (group_hom_id (symmetric_group three)))
      (kernel_quotient_group (symmetric_group three) (symmetric_group three) (group_hom_id (symmetric_group three)))
  ≔ fundamental_theorem_homs (symmetric_group three) (symmetric_group three) (group_hom_id (symmetric_group three))
