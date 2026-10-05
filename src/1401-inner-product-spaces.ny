export "1400-euclidean-fields"

{` Chapter 14, section "Inner product spaces" (geometry.tex 15-55).

   def:InnerProductSpace: an inner product space is a finite dimensional
   K-vector space V with an inner product H; the book takes H : V × V → ℝ,
   here it is curried, H : V → V → K (as smul in chapter 13), and K is a
   EuclideanField (module 1400) standing for ℝ. The book does not spell out
   "inner product"; we use the standard axioms: H is linear in the first
   argument, symmetric (hence bilinear), and positive definite
   (H(v,v) ≥ 0, and H(v,v) = 0 only for v = 0).

   OS (InnerProductSpace K) is the type of such pairs (V, H) together with
   the proof of finite dimensionality; OS_n (InnerProductSpaceDim K n) is
   the subtype of those of dimension n (HasDimension, module 1302: V merely
   is free on Fin n). The standard space 𝕍ⁿ is Kⁿ (module 1315) with the dot
   product x·y = Σ_i x_i y_i.

   lem:InnerProductSpace1Type: the proof in the book is the structure
   identity principle, which is formalized: (V = W) ≃ linear isomorphisms
   compatible with the inner products (ip_space_path_isometry_equiv), and
   those form a set. `}

def IsInnerProduct (K : EuclideanField) (V : VectorSpace (K .field)) (H : V .carrier → V .carrier → ef_carrier K)
  : Type
  ≔ sig (
    add_left : (u v w : V .carrier) → Id (ef_carrier K) (H (V .add u v) w) (K .field .fst .add (H u w) (H v w)),
    smul_left : (a : ef_carrier K) (u w : V .carrier) → Id (ef_carrier K) (H (V .smul a u) w) (K .field .fst .mul a (H u w)),
    symmetric : (u w : V .carrier) → Id (ef_carrier K) (H u w) (H w u),
    nonneg : (v : V .carrier) → K .nonneg (H v v),
    definite : (v : V .carrier) → Id (ef_carrier K) (H v v) (K .field .fst .zero) → Id (V .carrier) v (V .zero))

def is_inner_product_prop (K : EuclideanField) (V : VectorSpace (K .field)) (H : V .carrier → V .carrier → ef_carrier K)
  : isProp (IsInnerProduct K V H)
  ≔ x y ↦
    let R ≔ K .field .fst in let S ≔ R .carrier in let T ≔ V .carrier in
    let hS ≔ ring_set R in let hT ≔ module_set R V in
    (pi_prop T (u ↦ (v w : T) → Id S (H (V .add u v) w) (R .add (H u w) (H v w)))
       (u ↦ pi_prop T (v ↦ (w : T) → Id S (H (V .add u v) w) (R .add (H u w) (H v w)))
         (v ↦ pi_prop T (w ↦ Id S (H (V .add u v) w) (R .add (H u w) (H v w)))
           (w ↦ hS (H (V .add u v) w) (R .add (H u w) (H v w)))))
       (x .add_left) (y .add_left),
     pi_prop S (a ↦ (u w : T) → Id S (H (V .smul a u) w) (R .mul a (H u w)))
       (a ↦ pi_prop T (u ↦ (w : T) → Id S (H (V .smul a u) w) (R .mul a (H u w)))
         (u ↦ pi_prop T (w ↦ Id S (H (V .smul a u) w) (R .mul a (H u w)))
           (w ↦ hS (H (V .smul a u) w) (R .mul a (H u w)))))
       (x .smul_left) (y .smul_left),
     pi_prop T (u ↦ (w : T) → Id S (H u w) (H w u))
       (u ↦ pi_prop T (w ↦ Id S (H u w) (H w u)) (w ↦ hS (H u w) (H w u)))
       (x .symmetric) (y .symmetric),
     pi_prop T (v ↦ K .nonneg (H v v)) (v ↦ K .nonneg_prop (H v v)) (x .nonneg) (y .nonneg),
     pi_prop T (v ↦ Id S (H v v) (R .zero) → Id T v (V .zero))
       (v ↦ pi_prop (Id S (H v v) (R .zero)) (_ ↦ Id T v (V .zero)) (_ ↦ hT v (V .zero)))
       (x .definite) (y .definite))

{` def:InnerProductSpace. OS, the type of inner product spaces. `}
def InnerProductSpace (K : EuclideanField) : Type ≔ sig (
  space : VectorSpace (K .field),
  finite : IsFiniteDimensional (K .field) space,
  form : space .carrier → space .carrier → ef_carrier K,
  inner : IsInnerProduct K space form)

def ip_carrier (K : EuclideanField) (V : InnerProductSpace K) : Type ≔ V .space .carrier

{` OS_n, inner product spaces of dimension n. `}
def InnerProductSpaceDim (K : EuclideanField) (n : Nat) : Type
  ≔ Σ (InnerProductSpace K) (V ↦ HasDimension (K .field) n (V .space))

{` The inner product as a linear map in either argument. `}
def ip_left_linear (K : EuclideanField) (V : InnerProductSpace K) (w : ip_carrier K V)
  : LinearMap (K .field .fst) (V .space) (ring_self_module (K .field .fst))
  ≔ ((u ↦ V .form u w, u v ↦ V .inner .add_left u v w), a u ↦ V .inner .smul_left a u w)

def ip_add_right (K : EuclideanField) (V : InnerProductSpace K) (u v w : ip_carrier K V)
  : Id (ef_carrier K) (V .form u (V .space .add v w)) (K .field .fst .add (V .form u v) (V .form u w))
  ≔ let S ≔ ef_carrier K in let H ≔ V .form in let R ≔ K .field .fst in
    calc
      H u (V .space .add v w) = H (V .space .add v w) u by V .inner .symmetric u (V .space .add v w)
      = R .add (H v u) (H w u) by V .inner .add_left v w u
      = R .add (H u v) (H u w) by refl (R .add) (V .inner .symmetric v u) (V .inner .symmetric w u) ∎

def ip_smul_right (K : EuclideanField) (V : InnerProductSpace K) (a : ef_carrier K) (u w : ip_carrier K V)
  : Id (ef_carrier K) (V .form u (V .space .smul a w)) (K .field .fst .mul a (V .form u w))
  ≔ let S ≔ ef_carrier K in let H ≔ V .form in let R ≔ K .field .fst in
    calc
      H u (V .space .smul a w) = H (V .space .smul a w) u by V .inner .symmetric u (V .space .smul a w)
      = R .mul a (H w u) by V .inner .smul_left a w u
      = R .mul a (H u w) by refl (R .mul a) (V .inner .symmetric w u) ∎

def ip_right_linear (K : EuclideanField) (V : InnerProductSpace K) (u : ip_carrier K V)
  : LinearMap (K .field .fst) (V .space) (ring_self_module (K .field .fst))
  ≔ ((w ↦ V .form u w, v w ↦ ip_add_right K V u v w), a w ↦ ip_smul_right K V a u w)

{` Linear isometries: linear isomorphisms f with H'(f u, f v) = H(u, v). `}
def IsIsometry (K : EuclideanField) (V W : InnerProductSpace K) (f : ip_carrier K V → ip_carrier K W) : Type
  ≔ (u v : ip_carrier K V) → Id (ef_carrier K) (V .form u v) (W .form (f u) (f v))

def is_isometry_prop (K : EuclideanField) (V W : InnerProductSpace K) (f : ip_carrier K V → ip_carrier K W)
  : isProp (IsIsometry K V W f)
  ≔ let S ≔ ef_carrier K in let T ≔ ip_carrier K V in
    pi_prop T (u ↦ (v : T) → Id S (V .form u v) (W .form (f u) (f v)))
      (u ↦ pi_prop T (v ↦ Id S (V .form u v) (W .form (f u) (f v)))
        (v ↦ ring_set (K .field .fst) (V .form u v) (W .form (f u) (f v))))

def LinearIsometry (K : EuclideanField) (V W : InnerProductSpace K) : Type
  ≔ Σ (LinearIso (K .field .fst) (V .space) (W .space)) (φ ↦ IsIsometry K V W (φ .fst .map))

def linear_isometry_map (K : EuclideanField) (V W : InnerProductSpace K) (φ : LinearIsometry K V W)
  : ip_carrier K V → ip_carrier K W
  ≔ φ .fst .fst .map

def linear_isometry_path (K : EuclideanField) (V W : InnerProductSpace K) (φ ψ : LinearIsometry K V W)
  (h : Id (ip_carrier K V → ip_carrier K W) (φ .fst .fst .map) (ψ .fst .fst .map)) : Id (LinearIsometry K V W) φ ψ
  ≔ subtype_equal (LinearIso (K .field .fst) (V .space) (W .space)) (θ ↦ IsIsometry K V W (θ .fst .map))
      (θ ↦ is_isometry_prop K V W (θ .fst .map)) φ ψ
      (linear_iso_path (K .field .fst) (V .space) (W .space) (φ .fst) (ψ .fst) h)

def linear_isometry_set (K : EuclideanField) (V W : InnerProductSpace K) : isSet (LinearIsometry K V W)
  ≔ sigma_set (LinearIso (K .field .fst) (V .space) (W .space)) (θ ↦ IsIsometry K V W (θ .fst .map))
      (linear_iso_set (K .field .fst) (V .space) (W .space))
      (θ ↦ prop_is_set (IsIsometry K V W (θ .fst .map)) (is_isometry_prop K V W (θ .fst .map)))

{` Structure identity principle. The identification given by a linear
   isometry φ: its carrier component is ua(φ) (module 1304), so transport
   along it is φ by computation. `}
def IpSpaceData (K : EuclideanField) : Type
  ≔ Σ (VectorSpace (K .field)) (X ↦ X .carrier → X .carrier → ef_carrier K)

def ip_space_path_from_isometry (K : EuclideanField) (V W : InnerProductSpace K) (φ : LinearIsometry K V W)
  : Id (InnerProductSpace K) V W
  ≔ let R ≔ K .field .fst in let S ≔ ef_carrier K in
    let f ≔ φ .fst .fst in
    let p ≔ module_path_from_iso R (V .space) (W .space) (φ .fst) in
    let q : Id (VectorSpace (K .field) → Type) (X ↦ X .carrier → X .carrier → S) (X ↦ X .carrier → X .carrier → S)
      ≔ refl ((X ↦ X .carrier → X .carrier → S) : VectorSpace (K .field) → Type) in
    let hform : Id (X ↦ X .carrier → X .carrier → S) p (V .form) (W .form)
      ≔ x y ⤇ concat S (V .form x.0 y.0) (W .form (f .map x.0) (f .map y.0)) (W .form x.1 y.1)
            (φ .snd x.0 y.0) (refl (W .form) (x.2 .unglue) (y.2 .unglue)) in
    let d : Id (IpSpaceData K) (V .space, V .form) (W .space, W .form) ≔ (p, hform) in
    (p,
     prop_family_pathover (VectorSpace (K .field)) (X ↦ IsFiniteDimensional (K .field) X)
       (X ↦ mere_isprop (Σ Nat (n ↦ HasDimension (K .field) n X))) (V .space) (W .space) p (V .finite) (W .finite),
     hform,
     prop_family_pathover (IpSpaceData K) (e ↦ IsInnerProduct K (e .fst) (e .snd))
       (e ↦ is_inner_product_prop K (e .fst) (e .snd)) (V .space, V .form) (W .space, W .form) d (V .inner) (W .inner))

{` Transport along the space component of an identification is a linear
   isometry. `}
def ip_space_path_to_isometry (K : EuclideanField) (V W : InnerProductSpace K) (p : Id (InnerProductSpace K) V W)
  : LinearIsometry K V W
  ≔ let P ≔ p .space .carrier in
    (module_path_to_iso (K .field .fst) (V .space) (W .space) (p .space),
     u v ↦ p .form (P .liftr u) (P .liftr v))

def ip_space_isometry_path_section (K : EuclideanField) (V W : InnerProductSpace K) (φ : LinearIsometry K V W)
  : Id (LinearIsometry K V W) (ip_space_path_to_isometry K V W (ip_space_path_from_isometry K V W φ)) φ
  ≔ linear_isometry_path K V W (ip_space_path_to_isometry K V W (ip_space_path_from_isometry K V W φ)) φ
      (refl (φ .fst .fst .map))

def ip_space_isometry_total_contractible (K : EuclideanField) (V : InnerProductSpace K)
  : isContr (Σ (InnerProductSpace K) (LinearIsometry K V))
  ≔ let OS ≔ InnerProductSpace K in
    contractible_retract (Σ OS (W ↦ Id OS V W)) (Σ OS (LinearIsometry K V))
      (iscontr_idfrom OS V)
      (totalize OS (W ↦ Id OS V W) (LinearIsometry K V) (ip_space_path_to_isometry K V))
      (totalize OS (LinearIsometry K V) (W ↦ Id OS V W) (ip_space_path_from_isometry K V))
      (u ↦ (refl (u .fst), ip_space_isometry_path_section K V (u .fst) (u .snd)))

def ip_space_path_to_isometry_is_equiv (K : EuclideanField) (V W : InnerProductSpace K)
  : isEquiv (Id (InnerProductSpace K) V W) (LinearIsometry K V W) (ip_space_path_to_isometry K V W)
  ≔ let OS ≔ InnerProductSpace K in
    fiberwise_from_total OS (W ↦ Id OS V W) (LinearIsometry K V) (ip_space_path_to_isometry K V)
      (cat_contractible_map_is_equiv (Σ OS (W ↦ Id OS V W)) (Σ OS (LinearIsometry K V))
        (totalize OS (W ↦ Id OS V W) (LinearIsometry K V) (ip_space_path_to_isometry K V))
        (iscontr_idfrom OS V) (ip_space_isometry_total_contractible K V)) W

{` (V = W) ≃ linear isometries V ≅ W ("by univalence, its elements
   correspond to the linear isomorphisms compatible with the inner
   products"). `}
def ip_space_path_isometry_equiv (K : EuclideanField) (V W : InnerProductSpace K)
  : Equiv (Id (InnerProductSpace K) V W) (LinearIsometry K V W)
  ≔ (ip_space_path_to_isometry K V W, ip_space_path_to_isometry_is_equiv K V W)

def ip_space_paths_set (K : EuclideanField) (V W : InnerProductSpace K) : isSet (Id (InnerProductSpace K) V W)
  ≔ hlevel_two_to_set (Id (InnerProductSpace K) V W)
      (hlevel_equiv (suc. (suc. zero.)) (LinearIsometry K V W) (Id (InnerProductSpace K) V W)
        (canonical_inverse_equiv (Id (InnerProductSpace K) V W) (LinearIsometry K V W) (ip_space_path_isometry_equiv K V W))
        (set_to_hlevel_two (LinearIsometry K V W) (linear_isometry_set K V W)))

{` lem:InnerProductSpace1Type: OS is a 1-type. `}
def inner_product_space_groupoid (K : EuclideanField) : isGroupoid (InnerProductSpace K)
  ≔ V W ↦ ip_space_paths_set K V W

def ip_space_dim_path_equiv (K : EuclideanField) (n : Nat) (V W : InnerProductSpaceDim K n)
  : Equiv (Id (InnerProductSpaceDim K n) V W) (Id (InnerProductSpace K) (V .fst) (W .fst))
  ≔ subtype_path_equiv (InnerProductSpace K) (X ↦ HasDimension (K .field) n (X .space))
      (X ↦ mere_isprop (Σ (Fin n → X .space .carrier) (i ↦ IsFreeVectorSpace (K .field) (standard_set n) (X .space) i)))
      V W

def ip_space_dim_path_from_isometry (K : EuclideanField) (n : Nat) (V W : InnerProductSpaceDim K n)
  (φ : LinearIsometry K (V .fst) (W .fst)) : Id (InnerProductSpaceDim K n) V W
  ≔ let p ≔ ip_space_path_from_isometry K (V .fst) (W .fst) φ in
    (p,
     prop_family_pathover (InnerProductSpace K) (X ↦ HasDimension (K .field) n (X .space))
       (X ↦ mere_isprop (Σ (Fin n → X .space .carrier) (i ↦ IsFreeVectorSpace (K .field) (standard_set n) (X .space) i)))
       (V .fst) (W .fst) p (V .snd) (W .snd))

{` OS_n is a 1-type as well. `}
def inner_product_space_dim_groupoid (K : EuclideanField) (n : Nat) : isGroupoid (InnerProductSpaceDim K n)
  ≔ hlevel_to_groupoid (InnerProductSpaceDim K n)
      (subtype_hlevel (suc. (suc. zero.)) (InnerProductSpace K) (X ↦ HasDimension (K .field) n (X .space))
        (groupoid_to_hlevel (InnerProductSpace K) (inner_product_space_groupoid K))
        (X ↦ mere_isprop (Σ (Fin n → X .space .carrier) (i ↦ IsFreeVectorSpace (K .field) (standard_set n) (X .space) i))))

{` The standard inner product space 𝕍ⁿ = (Kⁿ, dot product). `}
def dot_product (K : EuclideanField) (n : Nat) (x y : Fin n → ef_carrier K) : ef_carrier K
  ≔ fin_module_sum (K .field .fst) (ring_self_module (K .field .fst)) n (i ↦ K .field .fst .mul (x i) (y i))

def dot_product_inner (K : EuclideanField) (n : Nat)
  : IsInnerProduct K (standard_vector_space (K .field) n) (dot_product K n)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let M ≔ ring_self_module R in
    let sum ≔ fin_module_sum R M n in
    (u v w ↦ concat S (dot_product K n (standard_vector_space (K .field) n .add u v) w)
        (sum (i ↦ R .add (R .mul (u i) (w i)) (R .mul (v i) (w i))))
        (R .add (dot_product K n u w) (dot_product K n v w))
        (refl sum (funext (Fin n) (_ ↦ S) (i ↦ R .mul (R .add (u i) (v i)) (w i))
          (i ↦ R .add (R .mul (u i) (w i)) (R .mul (v i) (w i))) (i ↦ ring_rdistr R (u i) (v i) (w i))))
        (fin_module_sum_add R M n (i ↦ R .mul (u i) (w i)) (i ↦ R .mul (v i) (w i))),
     a u w ↦ concat S (dot_product K n (standard_vector_space (K .field) n .smul a u) w)
        (sum (i ↦ R .mul a (R .mul (u i) (w i))))
        (R .mul a (dot_product K n u w))
        (refl sum (funext (Fin n) (_ ↦ S) (i ↦ R .mul (R .mul a (u i)) (w i)) (i ↦ R .mul a (R .mul (u i) (w i)))
          (i ↦ inverse S (R .mul a (R .mul (u i) (w i))) (R .mul (R .mul a (u i)) (w i)) (ring_mul_assoc R a (u i) (w i)))))
        (fin_module_sum_smul R M n a (i ↦ R .mul (u i) (w i))),
     u w ↦ refl sum (funext (Fin n) (_ ↦ S) (i ↦ R .mul (u i) (w i)) (i ↦ R .mul (w i) (u i))
        (i ↦ ef_commutative K (u i) (w i))),
     v ↦ ef_sum_squares_nonneg K n v,
     v p ↦ funext (Fin n) (_ ↦ S) v (_ ↦ R .zero) (i ↦ ef_sum_squares_zero K n v p i))

def standard_has_dimension (K : EuclideanField) (n : Nat)
  : HasDimension (K .field) n (standard_vector_space (K .field) n)
  ≔ mere (Σ (Fin n → Fin n → ef_carrier K)
            (i ↦ IsFreeVectorSpace (K .field) (standard_set n) (standard_vector_space (K .field) n) i))
      (standard_basis (K .field .fst) n, standard_module_free (K .field .fst) n)

def standard_inner_product_space (K : EuclideanField) (n : Nat) : InnerProductSpace K
  ≔ (standard_vector_space (K .field) n,
     mere (Σ Nat (m ↦ HasDimension (K .field) m (standard_vector_space (K .field) n))) (n, standard_has_dimension K n),
     dot_product K n,
     dot_product_inner K n)

{` 𝕍ⁿ as an element of OS_n. `}
def standard_inner_product_space_dim (K : EuclideanField) (n : Nat) : InnerProductSpaceDim K n
  ≔ (standard_inner_product_space K n, standard_has_dimension K n)
