export "1434-point-objects"

{` Chapter 14, exercise (geometry.tex 251-256), conclusion: O(n) is the
   symmetry group of (𝔼ⁿ, {0}) (explicit isomorphism) and, merely, of (E, {P})
   for any Euclidean space E of dimension n and point P (see module 1434). `}

def point_object_component_equiv (K : EuclideanField) (n : Nat)
  : BookEquiv (InnerProductSpaceDim K n) (NativeComponent (EuclideanObject K propositions_settype) (origin_object K n))
  ≔ let Obj ≔ EuclideanObject K propositions_settype in let o0 ≔ origin_object K n in
    let C ≔ NativeComponent Obj o0 in let OSn ≔ InnerProductSpaceDim K n in
    book_quasi_inverse_equiv OSn C (point_object_component K n) (point_object_component_inverse K n)
      (V ↦
        let Hd ≔ HasDimension (K .field) n (V .fst .space) in
        refl ((h ↦ (V .fst, h)) : Hd → OSn)
          (mere_isprop (Σ (Fin n → V .fst .space .carrier) (i ↦ IsFreeVectorSpace (K .field) (standard_set n) (V .fst .space) i))
            (object_component_dimension K propositions_settype n (origin_pred K n) (point_object_component K n V)) (V .snd)))
      (c ↦
        let V ≔ c .fst .fst .fst in let T ≔ c .fst .fst .snd in
        let G ≔ ip_additive_group K V in
        let sg ≔ origin_component_singleton K n c in
        let Fm : Σ (AbstractTorsors G) (T ↦ agset_carrier G (T .fst)) → Obj
          ≔ u ↦ ((V, u .fst), single_pred K (V, u .fst) (u .snd)) in
        let p1 ≔ refl Fm (pointed_torsors_contractible G .contract (T, sg .fst)) in
        let p2 : Id Obj ((V, T), single_pred K (V, T) (sg .fst)) (c .fst)
          ≔ refl ((h ↦ ((V, T), h)) : (agset_carrier G (T .fst) → PropTypes) → Obj)
              (inverse (agset_carrier G (T .fst) → PropTypes) (c .fst .snd) (single_pred K (V, T) (sg .fst)) (sg .snd)) in
        component_path Obj o0 (point_object_component K n (point_object_component_inverse K n c)) c
          (concat Obj (point_object_map K n (point_object_component_inverse K n c))
             ((V, T), single_pred K (V, T) (sg .fst)) (c .fst) p1 p2))

{` O(n) ≅ symmetry group of (𝔼ⁿ, {0}). `}
def origin_symmetry_iso (K : EuclideanField) (n : Nat)
  : GroupIso (orthogonal_group K n) (geometric_object_symmetry_group K propositions_settype (origin_object K n))
  ≔ let Obj ≔ EuclideanObject K propositions_settype in let o0 ≔ origin_object K n in
    let O ≔ orthogonal_group K n in let Sym ≔ geometric_object_symmetry_group K propositions_settype o0 in
    let e ≔ point_object_component_equiv K n in
    (mkhom O Sym (e .map, component_path Obj o0 (shape Sym) (e .map (shape O)) (refl o0)), e .equiv)

def origin_symmetry_path (K : EuclideanField) (n : Nat)
  : Id Group (orthogonal_group K n) (geometric_object_symmetry_group K propositions_settype (origin_object K n))
  ≔ group_path_from_iso (orthogonal_group K n) (geometric_object_symmetry_group K propositions_settype (origin_object K n))
      (origin_symmetry_iso K n)

{` The exercise for an arbitrary Euclidean space E of dimension n and a
   point P: the symmetry group of {P} is (merely) O(n). `}
def point_object_merely_origin (K : EuclideanField) (n : Nat) (E : EuclideanSpace K)
  (h : HasDimension (K .field) n (E .fst .space)) (P : euclidean_points K E)
  : Mere (Id (EuclideanObject K propositions_settype) (E, single_pred K E P) (origin_object K n))
  ≔ let Obj ≔ EuclideanObject K propositions_settype in let o0 ≔ origin_object K n in
    let ES ≔ EuclideanSpace K in let E0 ≔ euclidean_space_dim_forget K n (euclidean_standard K n) in
    let G0 ≔ ip_additive_group K (standard_inner_product_space K n) in
    mere_rec (Id ES E E0) (Mere (Id Obj (E, single_pred K E P) o0)) (mere_isprop (Id Obj (E, single_pred K E P) o0))
      (pE ↦
        let P' ≔ transport ES (euclidean_points K) E E0 pE P in
        let a : Id Obj (E, single_pred K E P) (E0, single_pred K E0 P')
          ≔ refl ((x ↦ (x .fst, single_pred K (x .fst) (x .snd))) : Σ ES (euclidean_points K) → Obj)
              ((pE, pathover_of_eq ES (euclidean_points K) E E0 pE P P' (refl P')) : Id (Σ ES (euclidean_points K)) (E, P) (E0, P')) in
        let Fm : Σ (AbstractTorsors G0) (T ↦ agset_carrier G0 (T .fst)) → Obj
          ≔ u ↦ ((standard_inner_product_space K n, u .fst), single_pred K (standard_inner_product_space K n, u .fst) (u .snd)) in
        let c ≔ pointed_torsors_contractible G0 in
        let b : Id Obj (E0, single_pred K E0 P') o0
          ≔ refl Fm (inverse (Σ (AbstractTorsors G0) (T ↦ agset_carrier G0 (T .fst))) (c .center) (E0 .snd, P')
               (c .contract (E0 .snd, P'))) in
        mere (Id Obj (E, single_pred K E P) o0) (concat Obj (E, single_pred K E P) (E0, single_pred K E0 P') o0 a b))
      (euclidean_normalization_es K n E h)

def point_symmetry_group (K : EuclideanField) (n : Nat) (E : EuclideanSpace K)
  (h : HasDimension (K .field) n (E .fst .space)) (P : euclidean_points K E)
  : Mere (Id Group (geometric_object_symmetry_group K propositions_settype (E, single_pred K E P)) (orthogonal_group K n))
  ≔ let Obj ≔ EuclideanObject K propositions_settype in let o0 ≔ origin_object K n in
    let Sym ≔ geometric_object_symmetry_group K propositions_settype in
    let goal ≔ Id Group (Sym (E, single_pred K E P)) (orthogonal_group K n) in
    mere_rec (Id Obj (E, single_pred K E P) o0) (Mere goal) (mere_isprop goal)
      (q ↦ mere goal
        (concat Group (Sym (E, single_pred K E P)) (Sym o0) (orthogonal_group K n)
          (refl Sym q) (inverse Group (orthogonal_group K n) (Sym o0) (origin_symmetry_path K n))))
      (point_object_merely_origin K n E h P)
