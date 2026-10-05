export "bridge-01-inner-product-spaces"

{` Bridges for geometry.tex, section "Euclidean spaces" (blind file
   02-euclidean-spaces): blocks 113, 127, 148, 158, 168, 178. `}

{` def:EuclideanSpace (113): bridge_def_es (bridge-00-core); Points and the
   vector group are ours by refl. `}
def bridge_def_vectors_group (K : BlindEuclideanField) (V : BlindInnerProductSpace K)
  : Id AbstractGroup (blind_vectors_group K V) (ip_additive_group (bridge_ef14 K) (bridge_os K V))
  ≔ refl (blind_vectors_group K V)

{` Definition at 127: ES_n (bridge_def_esn, bridge_std_esn) and
   ES ≃ Σ_n ES_n via the forgetful map. The inverse is ours (dimension of
   the vector space, vector_space_dimension_data), the round trip uses our
   finite_dimension_prop (uniqueness of dimension). `}
def bridge_es_back (K : BlindEuclideanField) (E : BlindEuclideanSpace K) : Σ Nat (n ↦ BlindEuclideanSpaceDim K n)
  ≔ let d ≔ vector_space_dimension_data (bridge_ef14 K) (E .fst .space) (E .fst .finite_dim) in
    (d .fst, ((E .fst, d .snd), E .snd))

def bridge_euclidean_spaces_sum (K : BlindEuclideanField) : blind_euclidean_spaces_sum K
  ≔ let A ≔ Σ Nat (n ↦ BlindEuclideanSpaceDim K n) in
    let ES ≔ BlindEuclideanSpace K in
    book_quasi_inverse_equiv A ES (u ↦ blind_es_dim_forget K (u .fst) (u .snd)) (bridge_es_back K)
      (x ↦
        let V ≔ x .snd .fst .fst in let T ≔ x .snd .snd in
        let D ≔ Σ Nat (n ↦ HasDimension (K .field) n (V .space)) in
        refl ((e ↦ (e .fst, ((V, e .snd), T))) : D → A)
          (finite_dimension_prop (bridge_ef14 K) (V .space)
            (vector_space_dimension_data (bridge_ef14 K) (V .space) (V .finite_dim)) (x .fst, x .snd .fst .snd)))
      (E ↦ refl E)
      .equiv

{` thm:EuclideanNormalization (148). `}
def bridge_euclidean_normalization (K : BlindEuclideanField) : blind_euclidean_normalization K
  ≔ E n h ↦
    let L ≔ bridge_ef14 K in
    let ES ≔ EuclideanSpace L in let B ≔ BlindEuclideanSpace K in
    let std ≔ euclidean_space_dim_forget L n (euclidean_standard L n) in
    let bstd ≔ blind_es_dim_forget K n (blind_std_euclidean_space K n) in
    mere_rec (Id ES (bridge_es K E) std) (Mere (Id B E bstd)) (mere_isprop (Id B E bstd))
      (p ↦ mere (Id B E bstd)
        (concat B E (bridge_es_inv K std) bstd (refl (bridge_es_inv K) p) (bridge_std_es_blind K n)))
      (euclidean_normalization_es L n (bridge_es K E) h)

{` lem:EuclideanSpace1Type (158). `}
def bridge_euclidean_space_one_type (K : BlindEuclideanField) : blind_euclidean_space_one_type K
  ≔ n ↦ hlevel_to_groupoid (BlindEuclideanSpaceDim K n)
      (hlevel_equiv (suc. (suc. (suc. zero.))) (EuclideanSpaceDim (bridge_ef14 K) n) (BlindEuclideanSpaceDim K n)
        (canonical_inverse_equiv (BlindEuclideanSpaceDim K n) (EuclideanSpaceDim (bridge_ef14 K) n) (bridge_def_esn K n))
        (groupoid_to_hlevel (EuclideanSpaceDim (bridge_ef14 K) n) (euclidean_space_dim_groupoid (bridge_ef14 K) n)))

def bridge_esn_connected (K : BlindEuclideanField) (n : Nat) : Connected (BlindEuclideanSpaceDim K n)
  ≔ connected_equiv (EuclideanSpaceDim (bridge_ef14 K) n) (BlindEuclideanSpaceDim K n)
      (canonical_inverse_equiv (BlindEuclideanSpaceDim K n) (EuclideanSpaceDim (bridge_ef14 K) n) (bridge_def_esn K n))
      .map (euclidean_group_connected (bridge_ef14 K) n)

{` def:EuclideanGroup (168): the facts it relies on; the group itself is
   bridge_def_euclidean_group (bridge-00-core). `}
def bridge_euclidean_group_data (K : BlindEuclideanField) : blind_euclidean_group_data K
  ≔ n ↦ (bridge_esn_connected K n, bridge_euclidean_space_one_type K n)

def bridge_euclidean_group_iso (K : BlindEuclideanField) (n : Nat)
  (conn : Connected (BlindEuclideanSpaceDim K n)) (grpd : isGroupoid (BlindEuclideanSpaceDim K n))
  : GroupIso (BlindEuclideanGroup K n conn grpd) (euclidean_group (bridge_ef14 K) n)
  ≔ bridge_group_iso_of_path (BlindEuclideanGroup K n conn grpd) (euclidean_group (bridge_ef14 K) n)
      (bridge_def_euclidean_group K n conn grpd)

{` thm:EuclideanGroupSemidirect (178). The blind semidirect product is ours
   (the blind action is ours on the bridged classifying type), and ours is
   identified with E(n) by euclidean_group_semidirect. `}
def bridge_semidirect_carrier_equiv (K : BlindEuclideanField) (n : Nat)
  (connO : Connected (BlindInnerProductSpaceDim K n)) (grpdO : isGroupoid (BlindInnerProductSpaceDim K n))
  : Equiv (semidirect_classifying_type (BlindOrthogonalGroup K n connO grpdO) (blind_orthogonal_vectors_action K n connO grpdO))
      (semidirect_classifying_type (orthogonal_group (bridge_ef14 K) n) (euclidean_semidirect_action (bridge_ef14 K) n))
  ≔ quasi_inverse_equiv
      (semidirect_classifying_type (BlindOrthogonalGroup K n connO grpdO) (blind_orthogonal_vectors_action K n connO grpdO))
      (semidirect_classifying_type (orthogonal_group (bridge_ef14 K) n) (euclidean_semidirect_action (bridge_ef14 K) n))
      (u ↦ (bridge_osn K n (u .fst), u .snd)) (u ↦ (bridge_osn_inv K n (u .fst), u .snd)) (u ↦ refl u) (u ↦ refl u)

def bridge_semidirect_path (K : BlindEuclideanField) (n : Nat)
  (connO : Connected (BlindInnerProductSpaceDim K n)) (grpdO : isGroupoid (BlindInnerProductSpaceDim K n))
  : Id Group (semidirect_product (BlindOrthogonalGroup K n connO grpdO) (blind_orthogonal_vectors_action K n connO grpdO))
      (semidirect_product (orthogonal_group (bridge_ef14 K) n) (euclidean_semidirect_action (bridge_ef14 K) n))
  ≔ let G ≔ BlindOrthogonalGroup K n connO grpdO in let H ≔ blind_orthogonal_vectors_action K n connO grpdO in
    let G' ≔ orthogonal_group (bridge_ef14 K) n in let H' ≔ euclidean_semidirect_action (bridge_ef14 K) n in
    bridge_mkgroup_path
      (semidirect_classifying_type G H, semidirect_shape G H, semidirect_classifying_connected G H,
       semidirect_classifying_groupoid G H)
      (semidirect_classifying_type G' H', semidirect_shape G' H', semidirect_classifying_connected G' H',
       semidirect_classifying_groupoid G' H')
      (bridge_semidirect_carrier_equiv K n connO grpdO)
      (bridge_std_osn K n, refl (shape (H (shape G))))

def bridge_euclidean_group_semidirect (K : BlindEuclideanField) : blind_euclidean_group_semidirect K
  ≔ n connO grpdO connE grpdE ↦
    let L ≔ bridge_ef14 K in
    let E ≔ BlindEuclideanGroup K n connE grpdE in
    let S ≔ semidirect_product (BlindOrthogonalGroup K n connO grpdO) (blind_orthogonal_vectors_action K n connO grpdO) in
    let S' ≔ semidirect_product (orthogonal_group L n) (euclidean_semidirect_action L n) in
    bridge_group_iso_of_path E S
      (concat Group E (euclidean_group L n) S (bridge_def_euclidean_group K n connE grpdE)
        (concat Group (euclidean_group L n) S' S (euclidean_group_semidirect L n)
          (inverse Group S S' (bridge_semidirect_path K n connO grpdO))))
