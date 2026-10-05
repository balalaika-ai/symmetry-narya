export "702-abstract-group-identity"
export "406-symmetric-group-three"

{` Chapter 7 (absgroup.tex), xca:op-abs-group. For G = (S, e, μ, ι) the
   opposite group G^op = (S, e, μ^op, ι) with μ^op(a, b) = μ(b, a). The
   inverse operation ι is an isomorphism G ≅ G^op (rem:abs-iso: an
   equivalence of the underlying sets preserving multiplication); the
   printed hint equations are ι(e) = e (ag_inv_unit) and
   (a·b)⁻¹ = b⁻¹·a⁻¹ (ag_inv_mul), both of module 700. By univalence
   (module 702) ι gives an identification G = G^op. `}

def abstract_op_mul (G : AbstractGroup) : G .carrier → G .carrier → G .carrier ≔ a b ↦ G .mul b a

def abstract_op_laws (G : AbstractGroup) : AbstractGroupLaws (G .carrier) (G .unit) (abstract_op_mul G) (G .inv)
  ≔ let S ≔ G .carrier in let m ≔ G .mul in let L ≔ G .laws in
    (L .carrier_set,
     g ↦ L .unit_left g,
     g ↦ L .unit_right g,
     g1 g2 g3 ↦ inverse S (m g3 (m g2 g1)) (m (m g3 g2) g1) (L .assoc g3 g2 g1),
     g ↦ ag_inv_left G g)

def abstract_op_group (G : AbstractGroup) : AbstractGroup
  ≔ (G .carrier, G .unit, abstract_op_mul G, G .inv, abstract_op_laws G)

{` ι is an equivalence (it is its own inverse). `}
def abstract_inv_equiv (G : AbstractGroup) : Equiv (G .carrier) (G .carrier)
  ≔ quasi_inverse_equiv (G .carrier) (G .carrier) (G .inv) (G .inv) (ag_inv_inv G) (ag_inv_inv G)

{` ι : G ≅ G^op. The multiplication condition ι(a·b) = μ^op(ι a, ι b) is
   literally (a·b)⁻¹ = b⁻¹·a⁻¹. `}
def abstract_op_iso (G : AbstractGroup) : AbstractIso G (abstract_op_group G)
  ≔ (abstract_inv_equiv G, a b ↦ ag_inv_mul G a b)

{` The hint equations in the printed form of an isomorphism
   (AbstractIsoEquations: e' = f(e) and μ'(f s, f t) = f(μ(s, t))). `}
def abstract_op_iso_equations (G : AbstractGroup) : AbstractIsoEquations G (abstract_op_group G)
  ≔ abstract_iso_equations_equiv G (abstract_op_group G) .map (abstract_op_iso G)

def abstract_op_iso_unit (G : AbstractGroup) : Id (G .carrier) (G .inv (G .unit)) (G .unit) ≔ ag_inv_unit G

{` The identification G = G^op induced by ι. `}
def abstract_op_path (G : AbstractGroup) : Id AbstractGroup G (abstract_op_group G)
  ≔ abstract_group_path_from_iso G (abstract_op_group G) (abstract_op_iso G)

{` Litmus: μ^op swaps the arguments and transport along G = G^op is ι,
   both by computation; (G^op)^op = G with the same data. `}
def abstract_op_mul_litmus (G : AbstractGroup) (a b : G .carrier)
  : Id (G .carrier) (abstract_op_group G .mul a b) (G .mul b a)
  ≔ refl (G .mul b a)

def abstract_op_path_transport (G : AbstractGroup) (s : G .carrier)
  : Id (G .carrier) (abstract_op_path G .carrier .trr s) (G .inv s)
  ≔ refl (G .inv s)

def abstract_op_op_path (G : AbstractGroup) : Id AbstractGroup (abstract_op_group (abstract_op_group G)) G
  ≔ abstract_group_path_of_data (abstract_op_group (abstract_op_group G)) G (refl (abstract_group_data G))

{` Litmus: for G = abstr Σ_3 the identity function is not an isomorphism
   G ≅ G^op (σ·τ ≠ τ·σ), so the inverse in abstract_op_iso is needed. `}
def abstract_op_identity_not_hom
  (h : IsAbstractHom (abstr (symmetric_group three)) (abstract_op_group (abstr (symmetric_group three))) (x ↦ x))
  : Empty
  ≔ sigma3_tau_sigma_noncommuting (h sigma3_sigma sigma3_tau)
