export "03-geometric-objects"
export "../../../src/1436-point-symmetries"
export "../../../src/410-pointed-connected-groupoids"

{` Bridges for geometry.tex: definition bridges shared by all bridge
   files.

   The parameter records. BlindEuclideanField has every field of our
   EuclideanField (module 1400) except that the square root is one
   Σ-valued field instead of three fields, plus one more axiom,
   nonneg_total (x ≥ 0 or -x ≥ 0, merely). So bridge_ef14 builds our
   field record from a blind one (forgetting totality, splitting sqrt);
   every blind statement is "for all K : BlindEuclideanField", and we
   derive it from our statement at bridge_ef14 K. The converse map does
   not exist: totality is not among our axioms (none of our proofs needs
   it), so our results are stated for a larger class of fields.

   Over bridge_ef14 K the carrier, the vector spaces and all operations
   are those of K by definition. BlindInnerProductSpace and our
   InnerProductSpace have the same components (the laws in another order
   and with other field names), so bridge_os is an equivalence with refl
   round trips, and so are the maps on OS_n, ES, ES_n, EucObj_M,
   configurations and arrangements. The blind standard spaces 𝕍ⁿ, 𝔼ⁿ use
   other proof terms (finite dimensionality, the laws of the dot product)
   than ours: they are identified with ours by paths whose vector-space,
   form and torsor components are refl. O(n), E(n) and the symmetry
   groups are identified by pointed equivalences of classifying types. `}

def bridge_ef14 (K : BlindEuclideanField) : EuclideanField
  ≔ (field ≔ K .field,
     nonneg ≔ K .nonneg,
     nonneg_prop ≔ K .nonneg_prop,
     nonneg_add ≔ K .nonneg_add,
     nonneg_mul ≔ K .nonneg_mul,
     nonneg_square ≔ K .nonneg_square,
     nonneg_antisym ≔ K .nonneg_antisym,
     nonzero_invertible ≔ K .nonzero_invertible,
     sqrt ≔ a h ↦ K .sqrt a h .fst,
     sqrt_nonneg ≔ a h ↦ K .sqrt a h .snd .fst,
     sqrt_square ≔ a h ↦ K .sqrt a h .snd .snd)

{` Inner product laws: the same five fields. `}
def bridge_ip_laws (K : BlindEuclideanField) (V : VectorSpace (K .field))
  (H : V .carrier → V .carrier → K .field .fst .carrier) (l : BlindInnerProductLaws K V H)
  : IsInnerProduct (bridge_ef14 K) V H
  ≔ (add_left ≔ l .add_left, smul_left ≔ l .smul_left, symmetric ≔ l .symm, nonneg ≔ l .pos, definite ≔ l .definite)

def bridge_ip_laws_inv (K : BlindEuclideanField) (V : VectorSpace (K .field))
  (H : V .carrier → V .carrier → K .field .fst .carrier) (l : IsInnerProduct (bridge_ef14 K) V H)
  : BlindInnerProductLaws K V H
  ≔ (symm ≔ l .symmetric, add_left ≔ l .add_left, smul_left ≔ l .smul_left, pos ≔ l .nonneg, definite ≔ l .definite)

def bridge_def_ip_laws (K : BlindEuclideanField) (V : VectorSpace (K .field))
  (H : V .carrier → V .carrier → K .field .fst .carrier)
  : Equiv (BlindInnerProductLaws K V H) (IsInnerProduct (bridge_ef14 K) V H)
  ≔ quasi_inverse_equiv (BlindInnerProductLaws K V H) (IsInnerProduct (bridge_ef14 K) V H)
      (bridge_ip_laws K V H) (bridge_ip_laws_inv K V H) (l ↦ refl l) (l ↦ refl l)

def bridge_ip_laws_prop (K : BlindEuclideanField) (V : VectorSpace (K .field))
  (H : V .carrier → V .carrier → K .field .fst .carrier) : isProp (BlindInnerProductLaws K V H)
  ≔ x y ↦ refl (bridge_ip_laws_inv K V H)
      (is_inner_product_prop (bridge_ef14 K) V H (bridge_ip_laws K V H x) (bridge_ip_laws K V H y))

{` The dot product is ours by definition. `}
def bridge_def_dot (K : BlindEuclideanField) (n : Nat)
  : Id ((Fin n → K .field .fst .carrier) → (Fin n → K .field .fst .carrier) → K .field .fst .carrier)
      (blind_dot K n) (dot_product (bridge_ef14 K) n)
  ≔ refl (dot_product (bridge_ef14 K) n)

{` def:InnerProductSpace: OS. `}
def bridge_os (K : BlindEuclideanField) (V : BlindInnerProductSpace K) : InnerProductSpace (bridge_ef14 K)
  ≔ (space ≔ V .space, finite ≔ V .finite_dim, form ≔ V .inner, inner ≔ bridge_ip_laws K (V .space) (V .inner) (V .laws))

def bridge_os_inv (K : BlindEuclideanField) (V : InnerProductSpace (bridge_ef14 K)) : BlindInnerProductSpace K
  ≔ (space ≔ V .space, finite_dim ≔ V .finite, inner ≔ V .form, laws ≔ bridge_ip_laws_inv K (V .space) (V .form) (V .inner))

def bridge_def_inner_product_space (K : BlindEuclideanField)
  : Equiv (BlindInnerProductSpace K) (InnerProductSpace (bridge_ef14 K))
  ≔ quasi_inverse_equiv (BlindInnerProductSpace K) (InnerProductSpace (bridge_ef14 K))
      (bridge_os K) (bridge_os_inv K) (V ↦ refl V) (V ↦ refl V)

{` The standard space 𝕍ⁿ: same space and form, other proofs. `}
def bridge_std_os (K : BlindEuclideanField) (n : Nat)
  : Id (InnerProductSpace (bridge_ef14 K)) (bridge_os K (blind_std_inner_product_space K n))
      (standard_inner_product_space (bridge_ef14 K) n)
  ≔ let L ≔ bridge_ef14 K in
    let X ≔ standard_vector_space (K .field) n in
    (refl X,
     mere_isprop (Σ Nat (m ↦ HasDimension (K .field) m X))
       (bridge_os K (blind_std_inner_product_space K n) .finite) (standard_inner_product_space L n .finite),
     refl (dot_product L n),
     is_inner_product_prop L X (dot_product L n)
       (bridge_os K (blind_std_inner_product_space K n) .inner) (dot_product_inner L n))

def bridge_std_os_blind (K : BlindEuclideanField) (n : Nat)
  : Id (BlindInnerProductSpace K) (bridge_os_inv K (standard_inner_product_space (bridge_ef14 K) n))
      (blind_std_inner_product_space K n)
  ≔ refl (bridge_os_inv K)
      (inverse (InnerProductSpace (bridge_ef14 K)) (bridge_os K (blind_std_inner_product_space K n))
        (standard_inner_product_space (bridge_ef14 K) n) (bridge_std_os K n))

{` OS_n. `}
def bridge_osn (K : BlindEuclideanField) (n : Nat) (V : BlindInnerProductSpaceDim K n)
  : InnerProductSpaceDim (bridge_ef14 K) n
  ≔ (bridge_os K (V .fst), V .snd)

def bridge_osn_inv (K : BlindEuclideanField) (n : Nat) (V : InnerProductSpaceDim (bridge_ef14 K) n)
  : BlindInnerProductSpaceDim K n
  ≔ (bridge_os_inv K (V .fst), V .snd)

def bridge_def_osn (K : BlindEuclideanField) (n : Nat)
  : Equiv (BlindInnerProductSpaceDim K n) (InnerProductSpaceDim (bridge_ef14 K) n)
  ≔ quasi_inverse_equiv (BlindInnerProductSpaceDim K n) (InnerProductSpaceDim (bridge_ef14 K) n)
      (bridge_osn K n) (bridge_osn_inv K n) (V ↦ refl V) (V ↦ refl V)

def bridge_std_osn (K : BlindEuclideanField) (n : Nat)
  : Id (InnerProductSpaceDim (bridge_ef14 K) n) (bridge_osn K n (blind_std_inner_product_space_dim K n))
      (standard_inner_product_space_dim (bridge_ef14 K) n)
  ≔ let L ≔ bridge_ef14 K in
    (bridge_std_os K n,
     prop_family_pathover (InnerProductSpace L) (X ↦ HasDimension (K .field) n (X .space))
       (X ↦ mere_isprop (Σ (Fin n → X .space .carrier) (i ↦ IsFreeVectorSpace (K .field) (standard_set n) (X .space) i)))
       (bridge_os K (blind_std_inner_product_space K n)) (standard_inner_product_space L n) (bridge_std_os K n)
       (blind_std_basis_free K n) (standard_has_dimension L n))

{` ES and ES_n: the torsor component is unchanged (the additive group of
   bridge_os V is that of V by definition). `}
def bridge_es (K : BlindEuclideanField) (E : BlindEuclideanSpace K) : EuclideanSpace (bridge_ef14 K)
  ≔ (bridge_os K (E .fst), E .snd)

def bridge_es_inv (K : BlindEuclideanField) (E : EuclideanSpace (bridge_ef14 K)) : BlindEuclideanSpace K
  ≔ (bridge_os_inv K (E .fst), E .snd)

def bridge_def_es (K : BlindEuclideanField) : Equiv (BlindEuclideanSpace K) (EuclideanSpace (bridge_ef14 K))
  ≔ quasi_inverse_equiv (BlindEuclideanSpace K) (EuclideanSpace (bridge_ef14 K))
      (bridge_es K) (bridge_es_inv K) (E ↦ refl E) (E ↦ refl E)

def bridge_es_points (K : BlindEuclideanField) (E : BlindEuclideanSpace K)
  : Id Type (blind_es_points K E) (euclidean_points (bridge_ef14 K) (bridge_es K E))
  ≔ refl (blind_es_points K E)

def bridge_esn (K : BlindEuclideanField) (n : Nat) (E : BlindEuclideanSpaceDim K n)
  : EuclideanSpaceDim (bridge_ef14 K) n
  ≔ (bridge_osn K n (E .fst), E .snd)

def bridge_esn_inv (K : BlindEuclideanField) (n : Nat) (E : EuclideanSpaceDim (bridge_ef14 K) n)
  : BlindEuclideanSpaceDim K n
  ≔ (bridge_osn_inv K n (E .fst), E .snd)

def bridge_def_esn (K : BlindEuclideanField) (n : Nat)
  : Equiv (BlindEuclideanSpaceDim K n) (EuclideanSpaceDim (bridge_ef14 K) n)
  ≔ quasi_inverse_equiv (BlindEuclideanSpaceDim K n) (EuclideanSpaceDim (bridge_ef14 K) n)
      (bridge_esn K n) (bridge_esn_inv K n) (E ↦ refl E) (E ↦ refl E)

def bridge_std_esn (K : BlindEuclideanField) (n : Nat)
  : Id (EuclideanSpaceDim (bridge_ef14 K) n) (bridge_esn K n (blind_std_euclidean_space K n))
      (euclidean_standard (bridge_ef14 K) n)
  ≔ (bridge_std_osn K n,
     refl (abstract_principal_torsor (module_group (K .field .fst) (standard_vector_space (K .field) n))))

def bridge_std_es (K : BlindEuclideanField) (n : Nat)
  : Id (EuclideanSpace (bridge_ef14 K)) (bridge_es K (blind_es_dim_forget K n (blind_std_euclidean_space K n)))
      (euclidean_space_dim_forget (bridge_ef14 K) n (euclidean_standard (bridge_ef14 K) n))
  ≔ refl ((E ↦ euclidean_space_dim_forget (bridge_ef14 K) n E) : EuclideanSpaceDim (bridge_ef14 K) n → EuclideanSpace (bridge_ef14 K))
      (bridge_std_esn K n)

def bridge_std_es_blind (K : BlindEuclideanField) (n : Nat)
  : Id (BlindEuclideanSpace K) (bridge_es_inv K (euclidean_space_dim_forget (bridge_ef14 K) n (euclidean_standard (bridge_ef14 K) n)))
      (blind_es_dim_forget K n (blind_std_euclidean_space K n))
  ≔ refl (bridge_es_inv K)
      (inverse (EuclideanSpace (bridge_ef14 K)) (bridge_es K (blind_es_dim_forget K n (blind_std_euclidean_space K n)))
        (euclidean_space_dim_forget (bridge_ef14 K) n (euclidean_standard (bridge_ef14 K) n)) (bridge_std_es K n))

{` Groups given by mkgroup on equivalent pointed classifying types. `}
def bridge_mkgroup_path (X Y : PointedConnectedGroupoid) (e : Equiv (X .carrier) (Y .carrier))
  (p : Id (Y .carrier) (e .map (X .point)) (Y .point))
  : Id Group (mkgroup X) (mkgroup Y)
  ≔ group_path_from_pointed_equiv (mkgroup X) (mkgroup Y)
      ((e .map, inverse (Y .carrier) (e .map (X .point)) (Y .point) p),
       book_equivalence (X .carrier) (Y .carrier) e .equiv)

def bridge_group_iso_of_path (G H : Group) (p : Id Group G H) : GroupIso G H
  ≔ group_path_iso_equiv G H .map p

{` def:OrthogonalGroup: the blind O(n), for any proofs of connectedness and
   of the groupoid property, is our O(n). `}
def bridge_def_orthogonal_group (K : BlindEuclideanField) (n : Nat)
  (conn : Connected (BlindInnerProductSpaceDim K n)) (grpd : isGroupoid (BlindInnerProductSpaceDim K n))
  : Id Group (BlindOrthogonalGroup K n conn grpd) (orthogonal_group (bridge_ef14 K) n)
  ≔ bridge_mkgroup_path
      (BlindInnerProductSpaceDim K n, blind_std_inner_product_space_dim K n, conn, grpd)
      (orthogonal_group_classifying (bridge_ef14 K) n)
      (bridge_def_osn K n) (bridge_std_osn K n)

{` def:EuclideanGroup. `}
def bridge_def_euclidean_group (K : BlindEuclideanField) (n : Nat)
  (conn : Connected (BlindEuclideanSpaceDim K n)) (grpd : isGroupoid (BlindEuclideanSpaceDim K n))
  : Id Group (BlindEuclideanGroup K n conn grpd) (euclidean_group (bridge_ef14 K) n)
  ≔ bridge_mkgroup_path
      (BlindEuclideanSpaceDim K n, blind_std_euclidean_space K n, conn, grpd)
      (euclidean_group_classifying (bridge_ef14 K) n)
      (bridge_def_esn K n) (bridge_std_esn K n)

{` Geometric objects EucObj_M. `}
def bridge_obj (K : BlindEuclideanField) (M : SetTypes) (X : BlindEucObj K M) : EuclideanObject (bridge_ef14 K) M
  ≔ (bridge_es K (X .fst), X .snd)

def bridge_obj_inv (K : BlindEuclideanField) (M : SetTypes) (X : EuclideanObject (bridge_ef14 K) M) : BlindEucObj K M
  ≔ (bridge_es_inv K (X .fst), X .snd)

def bridge_def_euc_obj (K : BlindEuclideanField) (M : SetTypes)
  : Equiv (BlindEucObj K M) (EuclideanObject (bridge_ef14 K) M)
  ≔ quasi_inverse_equiv (BlindEucObj K M) (EuclideanObject (bridge_ef14 K) M)
      (bridge_obj K M) (bridge_obj_inv K M) (X ↦ refl X) (X ↦ refl X)

def bridge_def_prop_set : Id SetTypes blind_prop_set propositions_settype ≔ refl propositions_settype

{` Symmetry groups: Aut(X) in the blind EucObj is Aut(bridge_obj X) in ours. `}
def bridge_symmetry_group (K : BlindEuclideanField) (M : SetTypes) (grpd : isGroupoid (BlindEucObj K M))
  (X : BlindEucObj K M) (Y : EuclideanObject (bridge_ef14 K) M) (p : Id (EuclideanObject (bridge_ef14 K) M) (bridge_obj K M X) Y)
  : Id Group (blind_symmetry_group K M grpd X) (geometric_object_symmetry_group (bridge_ef14 K) M Y)
  ≔ automorphism_group_equiv_path_at (BlindEucObj K M) (EuclideanObject (bridge_ef14 K) M) grpd
      (euclidean_object_groupoid (bridge_ef14 K) M) (bridge_def_euc_obj K M) X Y p
