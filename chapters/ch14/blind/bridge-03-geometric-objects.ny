export "bridge-02-euclidean-spaces"
export "../../../src/1435-configurations"

{` Bridges for geometry.tex, section "Geometric objects" (blind file
   03-geometric-objects): blocks 229, 241, 247, 251, 262, 272, 286. `}

{` Definition at 229: bridge_def_euc_obj and bridge_def_prop_set
   (bridge-00-core). Exercise at 241: EucObj_M is a groupoid. `}
def bridge_euc_obj_groupoid (K : BlindEuclideanField) : blind_euc_obj_groupoid K
  ≔ M ↦ hlevel_to_groupoid (BlindEucObj K M)
      (hlevel_equiv (suc. (suc. (suc. zero.))) (EuclideanObject (bridge_ef14 K) M) (BlindEucObj K M)
        (canonical_inverse_equiv (BlindEucObj K M) (EuclideanObject (bridge_ef14 K) M) (bridge_def_euc_obj K M))
        (groupoid_to_hlevel (EuclideanObject (bridge_ef14 K) M) (euclidean_object_groupoid (bridge_ef14 K) M)))

{` A blind object in the blind 𝔼ⁿ is our object in our 𝔼ⁿ. `}
def bridge_standard_object (K : BlindEuclideanField) (M : SetTypes) (n : Nat)
  (g : blind_es_points K (blind_es_dim_forget K n (blind_std_euclidean_space K n)) → M .fst)
  : Id (EuclideanObject (bridge_ef14 K) M)
      (bridge_obj K M (blind_es_dim_forget K n (blind_std_euclidean_space K n), g))
      (standard_object (bridge_ef14 K) M n g)
  ≔ (bridge_std_es K n, refl g)

{` Exercise at 247: a monomorphism Sym(𝔼ⁿ, g) → E(n), from our subgroup
   (geometric_object_subgroup, its inclusion is a monomorphism) and the
   identification of its underlying group with Sym(𝔼ⁿ, g)
   (geometric_object_subgroup_path), transported along the group bridges. `}
def bridge_mono_family (H G : Group) : Type ≔ Σ (GroupHom H G) (i ↦ IsGroupMono H G i)

def bridge_euc_obj_symmetry_subgroup (K : BlindEuclideanField) : blind_euc_obj_symmetry_subgroup K
  ≔ M grpd n conn grpdE g ↦
    let L ≔ bridge_ef14 K in
    let X : BlindEucObj K M ≔ (blind_es_dim_forget K n (blind_std_euclidean_space K n), g) in
    let o ≔ standard_object L M n g in
    let Sb ≔ blind_symmetry_group K M grpd X in
    let So ≔ geometric_object_symmetry_group L M o in
    let Eb ≔ BlindEuclideanGroup K n conn grpdE in
    let S ≔ geometric_object_subgroup L M n g in
    let Sub ≔ subgroup_group (euclidean_group L n) S in
    let pH : Id Group Sb Sub
      ≔ concat Group Sb So Sub (bridge_symmetry_group K M grpd X o (bridge_standard_object K M n g))
          (inverse Group Sub So (geometric_object_subgroup_path L M n g)) in
    let pG : Id Group Eb (euclidean_group L n) ≔ bridge_def_euclidean_group K n conn grpdE in
    (refl bridge_mono_family pH pG) .trl
      (subgroup_inclusion (euclidean_group L n) S, subgroup_inclusion_mono (euclidean_group L n) S)

{` Exercise at 251. The blind statement asks for an isomorphism (data) for
   every E of dimension n and every point P; we prove its mere version
   from ours (point_symmetry_group), and the data version at (𝔼ⁿ, {0})
   from origin_symmetry_iso. The literal blind statement is refuted for
   n = 2 in bridge-03b-point-symmetry-refutation. `}
def blind_point_symmetry_orthogonal_corrected (K : BlindEuclideanField) : Type
  ≔ (grpd : isGroupoid (BlindEucObj K blind_prop_set)) (n : Nat)
    (connO : Connected (BlindInnerProductSpaceDim K n)) (grpdO : isGroupoid (BlindInnerProductSpaceDim K n))
    (E : BlindEuclideanSpace K) → HasDimension (K .field) n (E .fst .space) → (P : blind_es_points K E)
    → Mere (GroupIso (blind_symmetry_group K blind_prop_set grpd (blind_point_object K E P))
              (BlindOrthogonalGroup K n connO grpdO))

def bridge_point_symmetry_orthogonal_corrected (K : BlindEuclideanField) : blind_point_symmetry_orthogonal_corrected K
  ≔ grpd n connO grpdO E h P ↦
    let L ≔ bridge_ef14 K in
    let Sb ≔ blind_symmetry_group K blind_prop_set grpd (blind_point_object K E P) in
    let So ≔ geometric_object_symmetry_group L propositions_settype (bridge_es K E, single_pred L (bridge_es K E) P) in
    let Ob ≔ BlindOrthogonalGroup K n connO grpdO in
    let O ≔ orthogonal_group L n in
    let q : Id Group Sb So
      ≔ bridge_symmetry_group K blind_prop_set grpd (blind_point_object K E P)
          (bridge_es K E, single_pred L (bridge_es K E) P)
          (refl (bridge_es K E, single_pred L (bridge_es K E) P)) in
    mere_rec (Id Group So O) (Mere (GroupIso Sb Ob)) (mere_isprop (GroupIso Sb Ob))
      (r ↦ mere (GroupIso Sb Ob)
        (bridge_group_iso_of_path Sb Ob
          (concat Group Sb So Ob q (concat Group So O Ob r (inverse Group Ob O (bridge_def_orthogonal_group K n connO grpdO))))))
      (point_symmetry_group L n (bridge_es K E) h P)

{` The data version at the origin of the blind 𝔼ⁿ. `}
def bridge_point_symmetry_origin (K : BlindEuclideanField) (grpd : isGroupoid (BlindEucObj K blind_prop_set)) (n : Nat)
  (connO : Connected (BlindInnerProductSpaceDim K n)) (grpdO : isGroupoid (BlindInnerProductSpaceDim K n))
  : GroupIso (blind_symmetry_group K blind_prop_set grpd
               (blind_point_object K (blind_es_dim_forget K n (blind_std_euclidean_space K n)) (standard_vector_space (K .field) n .zero)))
      (BlindOrthogonalGroup K n connO grpdO)
  ≔ let L ≔ bridge_ef14 K in
    let X ≔ blind_point_object K (blind_es_dim_forget K n (blind_std_euclidean_space K n)) (standard_vector_space (K .field) n .zero) in
    let Sb ≔ blind_symmetry_group K blind_prop_set grpd X in
    let So ≔ geometric_object_symmetry_group L propositions_settype (origin_object L n) in
    let Ob ≔ BlindOrthogonalGroup K n connO grpdO in
    let O ≔ orthogonal_group L n in
    bridge_group_iso_of_path Sb Ob
      (concat Group Sb So Ob
        (bridge_symmetry_group K blind_prop_set grpd X (origin_object L n) (bridge_std_es K n, refl (origin_pred L n)))
        (concat Group So O Ob (inverse Group O So (origin_symmetry_path L n))
          (inverse Group Ob O (bridge_def_orthogonal_group K n connO grpdO))))

{` Definition at 262: configurations, constituents, configurations of n
   objects. `}
def bridge_config (K : BlindEuclideanField) (I : Type) (M : I → SetTypes) (c : BlindConfiguration K I M)
  : Configuration (bridge_ef14 K) I M
  ≔ (bridge_es K (c .fst), c .snd)

def bridge_def_configuration (K : BlindEuclideanField) (I : Type) (M : I → SetTypes)
  : Equiv (BlindConfiguration K I M) (Configuration (bridge_ef14 K) I M)
  ≔ quasi_inverse_equiv (BlindConfiguration K I M) (Configuration (bridge_ef14 K) I M)
      (bridge_config K I M) (c ↦ (bridge_es_inv K (c .fst), c .snd)) (c ↦ refl c) (c ↦ refl c)

def bridge_def_constituent (K : BlindEuclideanField) (I : Type) (M : I → SetTypes) (c : BlindConfiguration K I M) (i : I)
  : Id (EuclideanObject (bridge_ef14 K) (M i)) (bridge_obj K (M i) (blind_constituent K I M c i))
      (configuration_constituent (bridge_ef14 K) I M (bridge_config K I M c) i)
  ≔ refl (configuration_constituent (bridge_ef14 K) I M (bridge_config K I M c) i)

def bridge_def_configuration_of_n (K : BlindEuclideanField) (n : Nat) (M : Fin n → SetTypes)
  : Equiv (BlindConfigurationOfN K n M) (ConfigurationOfObjects (bridge_ef14 K) n M)
  ≔ bridge_def_configuration K (Fin n) M

{` Definition at 272: arrangements of T and of the bridged objects. `}
def bridge_arrangement (K : BlindEuclideanField) (I : Type) (M : I → SetTypes) (T : (i : I) → BlindEucObj K (M i))
  (a : BlindArrangement K I M T) : Arrangement (bridge_ef14 K) I M (i ↦ bridge_obj K (M i) (T i))
  ≔ let L ≔ bridge_ef14 K in
    (bridge_config K I M (a .fst),
     i ↦
       let C ≔ blind_constituent K I M (a .fst) i in
       mere_rec (Id (BlindEucObj K (M i)) C (T i))
         (Mere (Id (EuclideanObject L (M i)) (bridge_obj K (M i) C) (bridge_obj K (M i) (T i))))
         (mere_isprop (Id (EuclideanObject L (M i)) (bridge_obj K (M i) C) (bridge_obj K (M i) (T i))))
         (p ↦ mere (Id (EuclideanObject L (M i)) (bridge_obj K (M i) C) (bridge_obj K (M i) (T i)))
           (refl (bridge_obj K (M i)) p))
         (a .snd i))

def bridge_arrangement_inv (K : BlindEuclideanField) (I : Type) (M : I → SetTypes) (T : (i : I) → BlindEucObj K (M i))
  (a : Arrangement (bridge_ef14 K) I M (i ↦ bridge_obj K (M i) (T i))) : BlindArrangement K I M T
  ≔ let L ≔ bridge_ef14 K in
    let c : BlindConfiguration K I M ≔ (bridge_es_inv K (a .fst .fst), a .fst .snd) in
    (c,
     i ↦
       let C ≔ configuration_constituent L I M (a .fst) i in
       mere_rec (Id (EuclideanObject L (M i)) C (bridge_obj K (M i) (T i)))
         (Mere (Id (BlindEucObj K (M i)) (blind_constituent K I M c i) (T i)))
         (mere_isprop (Id (BlindEucObj K (M i)) (blind_constituent K I M c i) (T i)))
         (p ↦ mere (Id (BlindEucObj K (M i)) (blind_constituent K I M c i) (T i))
           (refl (bridge_obj_inv K (M i)) p))
         (a .snd i))

def bridge_def_arrangement (K : BlindEuclideanField) (I : Type) (M : I → SetTypes) (T : (i : I) → BlindEucObj K (M i))
  : Equiv (BlindArrangement K I M T) (Arrangement (bridge_ef14 K) I M (i ↦ bridge_obj K (M i) (T i)))
  ≔ let L ≔ bridge_ef14 K in
    let T' ≔ (i : I) ↦ bridge_obj K (M i) (T i) in
    quasi_inverse_equiv (BlindArrangement K I M T) (Arrangement L I M T')
      (bridge_arrangement K I M T) (bridge_arrangement_inv K I M T)
      (a ↦ (refl (a .fst),
            pi_prop I (i ↦ Mere (Id (BlindEucObj K (M i)) (blind_constituent K I M (a .fst) i) (T i)))
              (i ↦ mere_isprop (Id (BlindEucObj K (M i)) (blind_constituent K I M (a .fst) i) (T i)))
              (bridge_arrangement_inv K I M T (bridge_arrangement K I M T a) .snd) (a .snd)))
      (a ↦ (refl (a .fst),
            pi_prop I (i ↦ Mere (Id (EuclideanObject L (M i)) (configuration_constituent L I M (a .fst) i) (T' i)))
              (i ↦ mere_isprop (Id (EuclideanObject L (M i)) (configuration_constituent L I M (a .fst) i) (T' i)))
              (bridge_arrangement K I M T (bridge_arrangement_inv K I M T a) .snd) (a .snd)))

{` Definition at 286: incidence types (components of equivalent types). `}
def bridge_def_incidence_type (K : BlindEuclideanField) (I : Type) (M : I → SetTypes) (T : (i : I) → BlindEucObj K (M i))
  (a : BlindArrangement K I M T)
  : Equiv (BlindIncidenceType K I M T a)
      (IncidenceType (bridge_ef14 K) I M (i ↦ bridge_obj K (M i) (T i)) (bridge_arrangement K I M T a))
  ≔ component_equiv (BlindArrangement K I M T) (Arrangement (bridge_ef14 K) I M (i ↦ bridge_obj K (M i) (T i)))
      (bridge_def_arrangement K I M T) a
