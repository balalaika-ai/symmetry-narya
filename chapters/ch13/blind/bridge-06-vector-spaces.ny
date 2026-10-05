export "06-vector-spaces"
export "bridge-05-fields"
export "../../../src/1302-vector-spaces"

{` Bridges for the vector-space definitions (fields.tex 1287, 1291, 1295, 1299). The blind vector space
   has an uncurried scalar multiplication K × V → V and an IsAbstractAbelian field; ours (RingModule) is curried
   with add_comm. Currying is inverse to uncurrying by η, so the conversion is an equivalence with refl round trips,
   and linear maps, freeness and n-dimensional spaces agree along it (by refl / by the identity term). Ours is
   stated for modules over any ring; VectorSpace K is the special case. `}

def b06_space (K : BlindField) (V : BlindVectorSpace K) : VectorSpace (b05_to_field K)
  ≔ (V .vec .carrier, V .vec .unit, V .vec .mul, V .vec .inv, V .vec .laws, V .abelian,
     a v ↦ V .smul (a, v), V .smul_one, V .smul_mul, V .bilinear .fst, V .bilinear .snd)

def b06_blind_space (K : BlindField) (W : VectorSpace (b05_to_field K)) : BlindVectorSpace K
  ≔ (module_group (b01_ring (K .fst)) W, module_group_abelian (b01_ring (K .fst)) W,
     p ↦ W .smul (p .fst) (p .snd), (W .smul_add_scalar, W .smul_add_vector), W .smul_one, W .smul_mul)

{` def vector space (1287). `}
def bridge_def_vector_space (K : BlindField) : Equiv (BlindVectorSpace K) (VectorSpace (b05_to_field K))
  ≔ quasi_inverse_equiv (BlindVectorSpace K) (VectorSpace (b05_to_field K)) (b06_space K) (b06_blind_space K)
      (V ↦ refl V) (W ↦ refl W)

{` def linear map (1291). `}
def bridge_def_linear_map (K : BlindField) (V W : BlindVectorSpace K)
  : Id Type (BlindLinearMap K V W) (LinearMap (b01_ring (K .fst)) (b06_space K V) (b06_space K W))
  ≔ refl (BlindLinearMap K V W)

{` def free vector space (1295): the two freeness predicates imply each other along the conversion (both are
   propositions, so they are equivalent). `}
def bridge_def_is_free_to (K : BlindField) (S : SetTypes) (V : BlindVectorSpace K) (i : S .fst → V .vec .carrier)
  (h : BlindIsFreeVectorSpace K S V i) : IsFreeVectorSpace (b05_to_field K) S (b06_space K V) i
  ≔ W j ↦ h (b06_blind_space K W) j

def bridge_def_is_free_from (K : BlindField) (S : SetTypes) (V : BlindVectorSpace K) (i : S .fst → V .vec .carrier)
  (h : IsFreeVectorSpace (b05_to_field K) S (b06_space K V) i) : BlindIsFreeVectorSpace K S V i
  ≔ W j ↦ h (b06_space K W) j

def bridge_def_free_vector_space (K : BlindField) (S : SetTypes)
  : Equiv (BlindFreeVectorSpace K S) (FreeVectorSpace (b05_to_field K) S)
  ≔ quasi_inverse_equiv (BlindFreeVectorSpace K S) (FreeVectorSpace (b05_to_field K) S)
      (t ↦ (b06_space K (t .fst), (t .snd .fst, bridge_def_is_free_to K S (t .fst) (t .snd .fst) (t .snd .snd))))
      (t ↦ (b06_blind_space K (t .fst),
            (t .snd .fst, bridge_def_is_free_from K S (b06_blind_space K (t .fst)) (t .snd .fst) (t .snd .snd))))
      (t ↦ refl t) (t ↦ refl t)

{` def n-dimensional vector space (1299). `}
def bridge_def_n_dim_vector_space (K : BlindField) (n : Nat)
  : Equiv (BlindNDimVectorSpace K n) (NDimensionalVectorSpace (b05_to_field K) n)
  ≔ bridge_def_free_vector_space K (standard_set n)
