export "01-inner-product-spaces"
export "../../../src/707-abstract-torsors"
export "../../../src/800-semidirect-products"

{` Blind statements, chapter 14 (geometry.tex), section "Euclidean spaces".
   RR is the parameter K : BlindEuclideanField (see 01-inner-product-spaces). `}

{` The additive (abstract) group underlying an inner product space. `}
def blind_vectors_group (K : BlindEuclideanField) (V : BlindInnerProductSpace K) : AbstractGroup
  ≔ module_group (K .field .fst) (V .space)

{` def:EuclideanSpace. A Euclidean space: an inner product space V together
   with a torsor (def:abstrGtorsors, abstract torsors of chapter 7) for the
   additive group underlying V. ES is the type of all of them. `}
def BlindEuclideanSpace (K : BlindEuclideanField) : Type
  ≔ Σ (BlindInnerProductSpace K) (V ↦ AbstractTorsors (blind_vectors_group K V))

{` Vectors E (the inner product space) and Points E (the torsor's set). `}
def blind_es_vectors (K : BlindEuclideanField) (E : BlindEuclideanSpace K) : BlindInnerProductSpace K ≔ E .fst

def blind_es_points (K : BlindEuclideanField) (E : BlindEuclideanSpace K) : Type
  ≔ agset_carrier (blind_vectors_group K (E .fst)) (E .snd .fst)

{` Definition (geometry.tex 127). ES_n ≔ Σ_{V : OS_n} Torsor_V. `}
def BlindEuclideanSpaceDim (K : BlindEuclideanField) (n : Nat) : Type
  ≔ Σ (BlindInnerProductSpaceDim K n) (V ↦ AbstractTorsors (blind_vectors_group K (V .fst)))

def blind_es_dim_forget (K : BlindEuclideanField) (n : Nat) (E : BlindEuclideanSpaceDim K n) : BlindEuclideanSpace K
  ≔ (E .fst .fst, E .snd)

{` Claim in the definition (geometry.tex 127): ES ≃ Σ_{n : N} ES_n, via
   the map forgetting the dimension. `}
def blind_euclidean_spaces_sum (K : BlindEuclideanField) : Type
  ≔ BookIsEquiv (Σ Nat (n ↦ BlindEuclideanSpaceDim K n)) (BlindEuclideanSpace K)
      (u ↦ blind_es_dim_forget K (u .fst) (u .snd))

{` The standard Euclidean space E^n : ES_n: vectors V^n, points the
   principal torsor of RR^n. `}
def blind_std_euclidean_space (K : BlindEuclideanField) (n : Nat) : BlindEuclideanSpaceDim K n
  ≔ (blind_std_inner_product_space_dim K n,
     abstract_principal_torsor (blind_vectors_group K (blind_std_inner_product_space K n)))

{` thm:EuclideanNormalization. Any Euclidean space E is merely equal to
   E^n, n = dim E (read: for every n with dim(Vectors E) = n). `}
def blind_euclidean_normalization (K : BlindEuclideanField) : Type
  ≔ (E : BlindEuclideanSpace K) (n : Nat) → HasDimension (K .field) n (E .fst .space)
    → Mere (Id (BlindEuclideanSpace K) E (blind_es_dim_forget K n (blind_std_euclidean_space K n)))

{` lem:EuclideanSpace1Type. ES_n is a 1-type (for every n). `}
def blind_euclidean_space_one_type (K : BlindEuclideanField) : Type
  ≔ (n : Nat) → isGroupoid (BlindEuclideanSpaceDim K n)

{` def:EuclideanGroup, the facts it relies on: ES_n is a connected groupoid. `}
def blind_euclidean_group_data (K : BlindEuclideanField) : Type
  ≔ (n : Nat) → Product (Connected (BlindEuclideanSpaceDim K n)) (isGroupoid (BlindEuclideanSpaceDim K n))

{` def:EuclideanGroup. E(n) ≔ mkgroup ES_n, pointed at E^n; the
   connectedness and groupoid proofs (propositions) are arguments. `}
def BlindEuclideanGroup (K : BlindEuclideanField) (n : Nat)
  (conn : Connected (BlindEuclideanSpaceDim K n)) (grpd : isGroupoid (BlindEuclideanSpaceDim K n)) : Group
  ≔ mkgroup (BlindEuclideanSpaceDim K n, blind_std_euclidean_space K n, conn, grpd)

{` The standard action of O(n) on the additive group underlying RR^n,
   as an action in groups BO(n) → Group: V ↦ (the group of the additive
   group of V). At the shape V^n it is the additive group of RR^n. `}
def blind_orthogonal_vectors_action (K : BlindEuclideanField) (n : Nat)
  (conn : Connected (BlindInnerProductSpaceDim K n)) (grpd : isGroupoid (BlindInnerProductSpaceDim K n))
  : BG (BlindOrthogonalGroup K n conn grpd) .carrier → Group
  ≔ V ↦ concr (blind_vectors_group K (V .fst))

{` thm:EuclideanGroupSemidirect. E(n) is isomorphic (equivalent as a
   group) to the semidirect product O(n) ⋉ RR^n. `}
def blind_euclidean_group_semidirect (K : BlindEuclideanField) : Type
  ≔ (n : Nat)
    (connO : Connected (BlindInnerProductSpaceDim K n)) (grpdO : isGroupoid (BlindInnerProductSpaceDim K n))
    (connE : Connected (BlindEuclideanSpaceDim K n)) (grpdE : isGroupoid (BlindEuclideanSpaceDim K n))
    → GroupIso (BlindEuclideanGroup K n connE grpdE)
        (semidirect_product (BlindOrthogonalGroup K n connO grpdO) (blind_orthogonal_vectors_action K n connO grpdO))
