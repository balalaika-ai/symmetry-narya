export "1435-configurations"
export "1436-point-symmetries"

{` Chapter 14 (geometry.tex 80, "an isosceles non-equilateral
   triangle has a total of 2 symmetries"), part 1: tools for the
   symmetries of geometric objects in the standard plane 𝔼².

   For an identification ℓ : 𝔼² = 𝔼² in ES, transport of points τ and of
   vectors λ along ℓ are compatible with everything defined uniformly in E
   (by applying refl to that definition): λ preserves the inner product,
   and τ(v + P) = λ(v) + τ(P). So τ is an affine map with isometric linear
   part. Loops of the point object (𝔼², {0}) (origin_object) all come from
   loops of O(2) (origin_loop_lift: point_object_component_equiv is an
   equivalence, and an equivalence is surjective on loops), and for such a
   loop the transport of points is the linear isometry of the O(2)
   symmetry. `}

{` Transport in the family a ↦ (b = f a) is post-composition with ap f. `}
def transport_ap_path_family (A B : Type) (f : A → B) (b : B) (x y : A) (r : Id A x y) (u : Id B b (f x))
  : Id (Id B b (f y)) (transport A ((a ↦ Id B b (f a)) : A → Type) x y r u) (concat B b (f x) (f y) u (refl f r))
  ≔ J A x (y r ↦ Id (Id B b (f y)) (transport A ((a ↦ Id B b (f a)) : A → Type) x y r u) (concat B b (f x) (f y) u (refl f r)))
      (concat (Id B b (f x)) (transport A ((a ↦ Id B b (f a)) : A → Type) x x (refl x) u) u
         (concat B b (f x) (f x) u (refl (f x)))
         (transport_refl A ((a ↦ Id B b (f a)) : A → Type) x u)
         (inverse (Id B b (f x)) (concat B b (f x) (f x) u (refl (f x))) u (concat_p1 B b (f x) u)))
      y r

{` A (book) equivalence is surjective on loops: every loop at f x is ap f
   of a loop at x (from the contractible fiber over f x). `}
def book_equiv_loop_lift (A B : Type) (f : A → B) (h : BookIsEquiv A B f) (x : A) (q : Id B (f x) (f x))
  : Σ (Id A x x) (r ↦ Id (Id B (f x) (f x)) (refl f r) q)
  ≔ let b ≔ f x in
    let Fb ≔ BookFiber A B f b in
    let c ≔ h b in
    let u : Fb ≔ (x, refl b) in let v : Fb ≔ (x, q) in
    let p : Id Fb u v ≔ concat Fb u (c .center) v (inverse Fb (c .center) u (c .contract u)) (c .contract v) in
    let t : Id (Id B b b) (transport A ((a ↦ Id B b (f a)) : A → Type) x x (p .fst) (refl b)) q
      ≔ pathover_transport_equiv A ((a ↦ Id B b (f a)) : A → Type) x x (p .fst) (refl b) q .map (p .snd) in
    (p .fst,
     calc
       refl f (p .fst) = concat B b b b (refl b) (refl f (p .fst))
         by inverse (Id B b b) (concat B b b b (refl b) (refl f (p .fst))) (refl f (p .fst)) (concat_1p B b b (refl f (p .fst)))
       = transport A ((a ↦ Id B b (f a)) : A → Type) x x (p .fst) (refl b)
         by inverse (Id B b b) (transport A ((a ↦ Id B b (f a)) : A → Type) x x (p .fst) (refl b))
              (concat B b b b (refl b) (refl f (p .fst))) (transport_ap_path_family A B f b x x (p .fst) (refl b))
       = q by t ∎)

{` Paths between identifications in Σ A B, B set-valued, are paths
   between their first components. `}
def sigma_set_path_of_fst (A : Type) (B : A → Type) (hB : (a : A) → isSet (B a)) (x y : Σ A B)
  (u v : Id (Σ A B) x y) (e : Id (Id A (x .fst) (y .fst)) (u .fst) (v .fst))
  : Id (Id (Σ A B) x y) u v
  ≔ let P ≔ Id A (x .fst) (y .fst) in
    let Q ≔ (p : P) ↦ refl B p (x .snd) (y .snd) in
    let hQ : (p : P) → isProp (Q p)
      ≔ p ↦ hlevel_one_to_prop (Q p)
          (pathover_hlevel (suc. zero.) A B (a ↦ set_to_hlevel_two (B a) (hB a)) (x .fst) (y .fst) p (x .snd) (y .snd)) in
    refl ((w ↦ (w .fst, w .snd)) : Σ P Q → Id (Σ A B) x y)
      (subtype_equal P Q hQ (u .fst, u .snd) (v .fst, v .snd) e)

{` Points and vectors of the standard plane, and transport along a loop. `}
def plane_point_transport (K : EuclideanField) (ℓ : Id (EuclideanSpace K) (standard_plane K) (standard_plane K))
  (P : Fin 2 → ef_carrier K) : Fin 2 → ef_carrier K
  ≔ refl (euclidean_points K) ℓ .trr P

def plane_vector_transport (K : EuclideanField) (ℓ : Id (EuclideanSpace K) (standard_plane K) (standard_plane K))
  (v : Fin 2 → ef_carrier K) : Fin 2 → ef_carrier K
  ≔ refl (euclidean_vectors K) ℓ .trr v

def plane_transport_form (K : EuclideanField) (ℓ : Id (EuclideanSpace K) (standard_plane K) (standard_plane K))
  (u w : Fin 2 → ef_carrier K)
  : Id (ef_carrier K) (dot_product K 2 u w) (dot_product K 2 (plane_vector_transport K ℓ u) (plane_vector_transport K ℓ w))
  ≔ let V ≔ refl (euclidean_vectors K) ℓ in
    refl ((E ↦ E .fst .form) : (E : EuclideanSpace K) → euclidean_vectors K E → euclidean_vectors K E → ef_carrier K)
      ℓ (V .liftr u) (V .liftr w)

def plane_transport_translate (K : EuclideanField) (ℓ : Id (EuclideanSpace K) (standard_plane K) (standard_plane K))
  (v P : Fin 2 → ef_carrier K)
  : Id (Fin 2 → ef_carrier K) (plane_point_transport K ℓ (euclidean_translate K (standard_plane K) v P))
      (euclidean_translate K (standard_plane K) (plane_vector_transport K ℓ v) (plane_point_transport K ℓ P))
  ≔ let F ≔ Fin 2 → ef_carrier K in
    let Pt ≔ refl (euclidean_points K) ℓ in let V ≔ refl (euclidean_vectors K) ℓ in
    type_pathover_transport F F Pt (euclidean_translate K (standard_plane K) v P)
      (euclidean_translate K (standard_plane K) (V .trr v) (Pt .trr P))
      (refl (euclidean_translate K) ℓ (V .liftr v) (Pt .liftr P))

def plane_point_transport_injective (K : EuclideanField) (ℓ : Id (EuclideanSpace K) (standard_plane K) (standard_plane K))
  (X Y : Fin 2 → ef_carrier K) (e : Id (Fin 2 → ef_carrier K) (plane_point_transport K ℓ X) (plane_point_transport K ℓ Y))
  : Id (Fin 2 → ef_carrier K) X Y
  ≔ let F ≔ Fin 2 → ef_carrier K in
    let T ≔ transport_equiv F F (refl (euclidean_points K) ℓ) in
    let g ≔ equiv_inverse_map F F T in
    calc
      X = g (T .map X) by equiv_unit F F T X
      = g (T .map Y) by refl g e
      = Y by inverse F Y (g (T .map Y)) (equiv_unit F F T Y) ∎

{` The origin 0 of 𝔼², and the affine form of τ: τ(Q) = λ(Q) + τ(0). `}
def plane_origin (K : EuclideanField) : Fin 2 → ef_carrier K ≔ standard_vector_space (K .field) 2 .zero

def plane_transport_affine (K : EuclideanField) (ℓ : Id (EuclideanSpace K) (standard_plane K) (standard_plane K))
  (Q : Fin 2 → ef_carrier K)
  : Id (Fin 2 → ef_carrier K) (plane_point_transport K ℓ Q)
      (euclidean_translate K (standard_plane K) (plane_vector_transport K ℓ Q) (plane_point_transport K ℓ (plane_origin K)))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let F ≔ Fin 2 → S in
    let c : Id F Q (euclidean_translate K (standard_plane K) Q (plane_origin K))
      ≔ funext (Fin 2) (_ ↦ S) Q (euclidean_translate K (standard_plane K) Q (plane_origin K))
          (i ↦ inverse S (R .add (Q i) (R .zero)) (Q i) (R .add_laws .unit_right (Q i))) in
    concat F (plane_point_transport K ℓ Q) (plane_point_transport K ℓ (euclidean_translate K (standard_plane K) Q (plane_origin K)))
      (euclidean_translate K (standard_plane K) (plane_vector_transport K ℓ Q) (plane_point_transport K ℓ (plane_origin K)))
      (refl (plane_point_transport K ℓ) c) (plane_transport_translate K ℓ Q (plane_origin K))

{` If τ(0) = W and τ(X) = Y then λ(X) = Y - W. `}
def plane_vector_transport_solve (K : EuclideanField) (ℓ : Id (EuclideanSpace K) (standard_plane K) (standard_plane K))
  (X Y W : Fin 2 → ef_carrier K)
  (hW : Id (Fin 2 → ef_carrier K) (plane_point_transport K ℓ (plane_origin K)) W)
  (hY : Id (Fin 2 → ef_carrier K) (plane_point_transport K ℓ X) Y)
  : Id (Fin 2 → ef_carrier K) (plane_vector_transport K ℓ X) (i ↦ K .field .fst .add (Y i) (K .field .fst .neg (W i)))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let F ≔ Fin 2 → S in let G ≔ ring_additive_group R in
    let lx ≔ plane_vector_transport K ℓ X in
    let aff : Id F Y (euclidean_translate K (standard_plane K) lx W)
      ≔ calc
          Y = plane_point_transport K ℓ X by inverse F (plane_point_transport K ℓ X) Y hY
          = euclidean_translate K (standard_plane K) lx (plane_point_transport K ℓ (plane_origin K)) by plane_transport_affine K ℓ X
          = euclidean_translate K (standard_plane K) lx W by refl (euclidean_translate K (standard_plane K) lx) hW ∎ in
    funext (Fin 2) (_ ↦ S) lx (i ↦ R .add (Y i) (R .neg (W i)))
      (i ↦
        calc
          lx i = R .add (R .add (lx i) (W i)) (R .neg (W i)) by inverse S (R .add (R .add (lx i) (W i)) (R .neg (W i))) (lx i) (ag_mul_inv_cancel_right G (lx i) (W i))
          = R .add (Y i) (R .neg (W i))
            by refl ((y ↦ R .add y (R .neg (W i))) : S → S)
                 (inverse S (Y i) (R .add (lx i) (W i)) (refl ((f ↦ f i) : F → S) aff)) ∎)

{` Loops in Obj at the base of a component, for an equivalence onto the
   component, come from loops of the domain (stated for variables, so that
   the equivalence proof is never unfolded). `}
def component_equiv_loop_lift (A Obj : Type) (o : Obj) (f : A → NativeComponent Obj o)
  (h : BookIsEquiv A (NativeComponent Obj o) f) (x : A) (z : Id Obj (f x .fst) (f x .fst))
  : Σ (Id A x x) (r ↦ Id (Id Obj (f x .fst) (f x .fst)) (refl ((y ↦ f y .fst) : A → Obj) r) z)
  ≔ let Comp ≔ NativeComponent Obj o in
    let PC ≔ Id Comp (f x) (f x) in let PO ≔ Id Obj (f x .fst) (f x .fst) in
    let Ec ≔ component_path_equiv Obj o (f x) (f x) in
    let zz ≔ equiv_inverse_map PC PO Ec z in
    let w ≔ book_equiv_loop_lift A Comp f h x zz in
    (w .fst,
     concat PO (refl ((y ↦ f y .fst) : A → Obj) (w .fst)) (Ec .map zz) z
       (refl (Ec .map) (w .snd)) (equiv_counit PC PO Ec z))

{` Loops of the point object (𝔼², {0}) come from loops of O(2). `}
def origin_loop_lift (K : EuclideanField)
  (z : Id (EuclideanObject K propositions_settype) (origin_object K 2) (origin_object K 2))
  : Σ (USym (orthogonal_group K 2))
      (r ↦ Id (Id (EuclideanObject K propositions_settype) (origin_object K 2) (origin_object K 2))
              (refl (point_object_map K 2) r) z)
  ≔ component_equiv_loop_lift (InnerProductSpaceDim K 2) (EuclideanObject K propositions_settype) (origin_object K 2)
      (point_object_component K 2) (point_object_component_equiv K 2 .equiv) (standard_inner_product_space_dim K 2) z

{` For a loop coming from r : USym O(2), transport of points is the linear
   isometry of r. `}
def origin_loop_transport (K : EuclideanField) (r : USym (orthogonal_group K 2)) (X : Fin 2 → ef_carrier K)
  : Id (Fin 2 → ef_carrier K)
      (plane_point_transport K (refl (point_object_map K 2) r .fst) X)
      (orthogonal_usym_isometry_equiv K 2 .map r .fst .fst .map X)
  ≔ refl (orthogonal_usym_isometry_equiv K 2 .map r .fst .fst .map X)
