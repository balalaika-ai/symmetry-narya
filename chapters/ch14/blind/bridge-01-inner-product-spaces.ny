export "bridge-00-core"

{` Bridges for geometry.tex, section "Inner product spaces" (blind
   file 01-inner-product-spaces): blocks 17, 34, 46, 57. Every statement is
   derived from ours at bridge_ef14 K by transport along the equivalences
   of bridge-00-core. `}

{` def:InnerProductSpace (17): bridge_def_inner_product_space,
   bridge_def_ip_laws, bridge_def_dot, bridge_def_osn, and the standard
   spaces agree (bridge_std_os, bridge_std_osn). `}

{` thm:GramSchmidt (34). `}
def bridge_gram_schmidt (K : BlindEuclideanField) : blind_gram_schmidt K
  ≔ V n h ↦
    let OS ≔ InnerProductSpace (bridge_ef14 K) in
    let B ≔ BlindInnerProductSpace K in
    let std ≔ standard_inner_product_space (bridge_ef14 K) n in
    let bstd ≔ blind_std_inner_product_space K n in
    mere_rec (Id OS (bridge_os K V) std) (Mere (Id B V bstd)) (mere_isprop (Id B V bstd))
      (p ↦ mere (Id B V bstd)
        (concat B V (bridge_os_inv K std) bstd (refl (bridge_os_inv K) p) (bridge_std_os_blind K n)))
      (gram_schmidt_theorem_os (bridge_ef14 K) n (bridge_os K V) h)

{` lem:InnerProductSpace1Type (46). `}
def bridge_inner_product_space_one_type (K : BlindEuclideanField) : blind_inner_product_space_one_type K
  ≔ hlevel_to_groupoid (BlindInnerProductSpace K)
      (hlevel_equiv (suc. (suc. (suc. zero.))) (InnerProductSpace (bridge_ef14 K)) (BlindInnerProductSpace K)
        (canonical_inverse_equiv (BlindInnerProductSpace K) (InnerProductSpace (bridge_ef14 K)) (bridge_def_inner_product_space K))
        (groupoid_to_hlevel (InnerProductSpace (bridge_ef14 K)) (inner_product_space_groupoid (bridge_ef14 K))))

{` Converse direction for 46 at the blind level: OS_n is a 1-type too. `}
def bridge_osn_groupoid (K : BlindEuclideanField) (n : Nat) : isGroupoid (BlindInnerProductSpaceDim K n)
  ≔ hlevel_to_groupoid (BlindInnerProductSpaceDim K n)
      (hlevel_equiv (suc. (suc. (suc. zero.))) (InnerProductSpaceDim (bridge_ef14 K) n) (BlindInnerProductSpaceDim K n)
        (canonical_inverse_equiv (BlindInnerProductSpaceDim K n) (InnerProductSpaceDim (bridge_ef14 K) n) (bridge_def_osn K n))
        (groupoid_to_hlevel (InnerProductSpaceDim (bridge_ef14 K) n) (inner_product_space_dim_groupoid (bridge_ef14 K) n)))

def bridge_osn_connected (K : BlindEuclideanField) (n : Nat) : Connected (BlindInnerProductSpaceDim K n)
  ≔ connected_equiv (InnerProductSpaceDim (bridge_ef14 K) n) (BlindInnerProductSpaceDim K n)
      (canonical_inverse_equiv (BlindInnerProductSpaceDim K n) (InnerProductSpaceDim (bridge_ef14 K) n) (bridge_def_osn K n))
      .map (orthogonal_group_connected (bridge_ef14 K) n)

{` def:OrthogonalGroup (57): the facts it relies on, and the group itself
   (bridge_def_orthogonal_group in bridge-00-core: for all proofs conn,
   grpd, the blind O(n) is our O(n)); also as a group isomorphism. `}
def bridge_orthogonal_group_data (K : BlindEuclideanField) : blind_orthogonal_group_data K
  ≔ n ↦ (bridge_osn_connected K n, bridge_osn_groupoid K n)

def bridge_orthogonal_group_iso (K : BlindEuclideanField) (n : Nat)
  (conn : Connected (BlindInnerProductSpaceDim K n)) (grpd : isGroupoid (BlindInnerProductSpaceDim K n))
  : GroupIso (BlindOrthogonalGroup K n conn grpd) (orthogonal_group (bridge_ef14 K) n)
  ≔ bridge_group_iso_of_path (BlindOrthogonalGroup K n conn grpd) (orthogonal_group (bridge_ef14 K) n)
      (bridge_def_orthogonal_group K n conn grpd)

{` Litmus through the bridge: the blind O(2) is not abelian. `}
def bridge_blind_orthogonal_two_not_abelian (K : BlindEuclideanField)
  (conn : Connected (BlindInnerProductSpaceDim K 2)) (grpd : isGroupoid (BlindInnerProductSpaceDim K 2))
  (h : IsAbelian (BlindOrthogonalGroup K 2 conn grpd)) : Empty
  ≔ orthogonal_two_not_abelian (bridge_ef14 K)
      (transport Group IsAbelian (BlindOrthogonalGroup K 2 conn grpd) (orthogonal_group (bridge_ef14 K) 2)
        (bridge_def_orthogonal_group K 2 conn grpd) h)
