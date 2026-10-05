export "02-euclidean-spaces"
export "../../../src/502-subgroups"

{` Blind statements, chapter 14 (geometry.tex), section "Geometric objects". `}

{` Definition (geometry.tex 229). Geometric objects with materials drawn
   from a set M: EucObj ≔ Σ_{E : ES} (Points E → M). `}
def BlindEucObj (K : BlindEuclideanField) (M : SetTypes) : Type
  ≔ Σ (BlindEuclideanSpace K) (E ↦ blind_es_points K E → M .fst)

{` M = Prop (a set by univalence): objects as subsets of Points E. `}
def blind_prop_set : SetTypes ≔ (PropTypes, propositions_set)

{` Exercise (geometry.tex 241). EucObj is a groupoid (for every set M). `}
def blind_euc_obj_groupoid (K : BlindEuclideanField) : Type
  ≔ (M : SetTypes) → isGroupoid (BlindEucObj K M)

{` The symmetry group of a geometric object X: Aut_{EucObj}(X). The
   groupoid proof is an argument. `}
def blind_symmetry_group (K : BlindEuclideanField) (M : SetTypes) (grpd : isGroupoid (BlindEucObj K M))
  (X : BlindEucObj K M) : Group
  ≔ automorphism_group (BlindEucObj K M) grpd X

{` Exercise (geometry.tex 247). The symmetry group of a geometric object
   (E^n, g) in E^n is a subgroup of E(n): there is a monomorphism
   Sym(E^n, g) → E(n). `}
def blind_euc_obj_symmetry_subgroup (K : BlindEuclideanField) : Type
  ≔ (M : SetTypes) (grpd : isGroupoid (BlindEucObj K M)) (n : Nat)
    (conn : Connected (BlindEuclideanSpaceDim K n)) (grpdE : isGroupoid (BlindEuclideanSpaceDim K n))
    (g : blind_es_points K (blind_es_dim_forget K n (blind_std_euclidean_space K n)) → M .fst)
    → Σ (GroupHom (blind_symmetry_group K M grpd (blind_es_dim_forget K n (blind_std_euclidean_space K n), g))
           (BlindEuclideanGroup K n conn grpdE))
        (i ↦ IsGroupMono (blind_symmetry_group K M grpd (blind_es_dim_forget K n (blind_std_euclidean_space K n), g))
               (BlindEuclideanGroup K n conn grpdE) i)

{` The one-point subset {P} of Points E, Q ↦ (Q = P). `}
def blind_point_object (K : BlindEuclideanField) (E : BlindEuclideanSpace K) (P : blind_es_points K E)
  : BlindEucObj K blind_prop_set
  ≔ (E, Q ↦ (Id (blind_es_points K E) Q P, agset_carrier_set (blind_vectors_group K (E .fst)) (E .snd .fst) Q P))

{` Exercise (geometry.tex 251). For E of dimension n and P : Points E, the
   symmetry group of {P} is isomorphic to O(n). `}
def blind_point_symmetry_orthogonal (K : BlindEuclideanField) : Type
  ≔ (grpd : isGroupoid (BlindEucObj K blind_prop_set)) (n : Nat)
    (connO : Connected (BlindInnerProductSpaceDim K n)) (grpdO : isGroupoid (BlindInnerProductSpaceDim K n))
    (E : BlindEuclideanSpace K) → HasDimension (K .field) n (E .fst .space) → (P : blind_es_points K E)
    → GroupIso (blind_symmetry_group K blind_prop_set grpd (blind_point_object K E P))
        (BlindOrthogonalGroup K n connO grpdO)

{` Definition (geometry.tex 262). A configuration for a parameter type I
   and sets M_i: a Euclidean space E with p_i : Points E → M_i for each i. `}
def BlindConfiguration (K : BlindEuclideanField) (I : Type) (M : I → SetTypes) : Type
  ≔ Σ (BlindEuclideanSpace K) (E ↦ (i : I) → blind_es_points K E → M i .fst)

{` Its constituents (E, p_i). `}
def blind_constituent (K : BlindEuclideanField) (I : Type) (M : I → SetTypes) (c : BlindConfiguration K I M) (i : I)
  : BlindEucObj K (M i)
  ≔ (c .fst, c .snd i)

{` A configuration of n objects: I = Fin n. `}
def BlindConfigurationOfN (K : BlindEuclideanField) (n : Nat) (M : Fin n → SetTypes) : Type
  ≔ BlindConfiguration K (Fin n) M

{` Definition (geometry.tex 272). An arrangement of a family T_i of
   geometric objects: a configuration whose i-th constituent is merely
   equal to T_i. `}
def BlindArrangement (K : BlindEuclideanField) (I : Type) (M : I → SetTypes) (T : (i : I) → BlindEucObj K (M i)) : Type
  ≔ Σ (BlindConfiguration K I M)
      (c ↦ (i : I) → Mere (Id (BlindEucObj K (M i)) (blind_constituent K I M c i) (T i)))

{` Definition (geometry.tex 286). An incidence type: a connected component
   of the type of arrangements, i.e. the component of some arrangement a. `}
def BlindIncidenceType (K : BlindEuclideanField) (I : Type) (M : I → SetTypes) (T : (i : I) → BlindEucObj K (M i))
  (a : BlindArrangement K I M T) : Type
  ≔ NativeComponent (BlindArrangement K I M T) a
