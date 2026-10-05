export "210-truncation-smallness"
export "186-chapter-two-remarks"

{` Higher images for every level n = k - 1 >= -1, with k : Nat indexing the
   n-truncations Trunc k of modules 200-202; an n-type has HLevel index k + 1,
   so n-truncated maps are TruncatedMap (suc. k).  The level n = -2, whose
   truncation is Unit, is treated separately in module 108. `}

{` Paths between maps out of a truncation, with the computation of their
   components at units, and dependent elimination with its computation rule. `}
def trunc_maps_path (k : Nat) (A : Type) (R : TruncStructure k A) (B : Type) (hB : HLevel (suc. k) B)
  (h h' : R .carrier → B) (p : (a : A) → Id B (h (R .unit_map a)) (h' (R .unit_map a)))
  : Id (R .carrier → B) h h'
  ≔ let E ≔ trunc_precompose_equiv k A R B hB in
    equiv_inverse_map (Id (R .carrier → B) h h') (Id (A → B) (E .map h) (E .map h'))
      (equivalence_on_paths (R .carrier → B) (A → B) E h h')
      (funext A (_ ↦ B) (E .map h) (E .map h') p)

def trunc_maps_path_beta (k : Nat) (A : Type) (R : TruncStructure k A) (B : Type) (hB : HLevel (suc. k) B)
  (h h' : R .carrier → B) (p : (a : A) → Id B (h (R .unit_map a)) (h' (R .unit_map a))) (a : A)
  : Id (Id B (h (R .unit_map a)) (h' (R .unit_map a)))
      (happly (R .carrier) (_ ↦ B) h h' (trunc_maps_path k A R B hB h h' p) (R .unit_map a)) (p a)
  ≔ let E ≔ trunc_precompose_equiv k A R B hB in
    let F ≔ funext A (_ ↦ B) (E .map h) (E .map h') p in
    let e ≔ equivalence_on_paths (R .carrier → B) (A → B) E h h' in
    calc
      happly (R .carrier) (_ ↦ B) h h' (trunc_maps_path k A R B hB h h' p) (R .unit_map a)
      = happly A (_ ↦ B) (E .map h) (E .map h') (e .map (trunc_maps_path k A R B hB h h' p)) a
        by refl (happly (R .carrier) (_ ↦ B) h h' (trunc_maps_path k A R B hB h h' p) (R .unit_map a))
      = happly A (_ ↦ B) (E .map h) (E .map h') F a
        by refl ((r ↦ happly A (_ ↦ B) (E .map h) (E .map h') r a) : Id (A → B) (E .map h) (E .map h') → Id B (h (R .unit_map a)) (h' (R .unit_map a)))
          (equiv_counit (Id (R .carrier → B) h h') (Id (A → B) (E .map h) (E .map h')) e F)
      = p a by inverse (Id B (h (R .unit_map a)) (h' (R .unit_map a))) (p a)
          (happly A (_ ↦ B) (E .map h) (E .map h') F a) (funext_beta A (_ ↦ B) (E .map h) (E .map h') p a) ∎

def trunc_ind (k : Nat) (A : Type) (R : TruncStructure k A) (P : R .carrier → Type)
  (hP : (c : R .carrier) → HLevel (suc. k) (P c)) (f : (a : A) → P (R .unit_map a)) (c : R .carrier) : P c
  ≔ let C ≔ R .carrier in let S ≔ Σ C P in
    let hS ≔ hlevel_sigma (suc. k) C P (R .level) hP in
    let g ≔ ((a ↦ (R .unit_map a, f a)) : A → S) in
    let s ≔ trunc_extend k A R S hS g in
    let fs ≔ trunc_maps_path k A R C (R .level) (x ↦ s x .fst) (identity C)
      (a ↦ inverse C (R .unit_map a) (s (R .unit_map a) .fst) (trunc_extend_beta k A R S hS g a .fst)) in
    transport C P (s c .fst) c (happly C (_ ↦ C) (x ↦ s x .fst) (identity C) fs c) (s c .snd)

def pathover_inverse_transport (A : Type) (B : A → Type) (x y : A) (p : Id A x y) (u : B x) (v : B y)
  (q : Id B p u v) : Id (B x) (transport A B y x (inverse A x y p) v) u
  ≔ pathover_transport_equiv A B y x (inverse A x y p) v u .map (pathover_inverse A B x y p u v q)

def trunc_ind_beta (k : Nat) (A : Type) (R : TruncStructure k A) (P : R .carrier → Type)
  (hP : (c : R .carrier) → HLevel (suc. k) (P c)) (f : (a : A) → P (R .unit_map a)) (a : A)
  : Id (P (R .unit_map a)) (trunc_ind k A R P hP f (R .unit_map a)) (f a)
  ≔ let C ≔ R .carrier in let S ≔ Σ C P in
    let hS ≔ hlevel_sigma (suc. k) C P (R .level) hP in
    let g ≔ ((b ↦ (R .unit_map b, f b)) : A → S) in
    let s ≔ trunc_extend k A R S hS g in
    let beta ≔ trunc_extend_beta k A R S hS g a in
    let pts ≔ ((b ↦ inverse C (R .unit_map b) (s (R .unit_map b) .fst) (trunc_extend_beta k A R S hS g b .fst))
      : (b : A) → Id C (s (R .unit_map b) .fst) (R .unit_map b)) in
    let fs ≔ trunc_maps_path k A R C (R .level) (x ↦ s x .fst) (identity C) pts in
    calc
      transport C P (s (R .unit_map a) .fst) (R .unit_map a)
        (happly C (_ ↦ C) (x ↦ s x .fst) (identity C) fs (R .unit_map a)) (s (R .unit_map a) .snd)
      = transport C P (s (R .unit_map a) .fst) (R .unit_map a) (pts a) (s (R .unit_map a) .snd)
        by refl ((r ↦ transport C P (s (R .unit_map a) .fst) (R .unit_map a) r (s (R .unit_map a) .snd))
          : Id C (s (R .unit_map a) .fst) (R .unit_map a) → P (R .unit_map a))
          (trunc_maps_path_beta k A R C (R .level) (x ↦ s x .fst) (identity C) pts a)
      = f a by pathover_inverse_transport C P (R .unit_map a) (s (R .unit_map a) .fst) (beta .fst)
          (f a) (s (R .unit_map a) .snd) (beta .snd) ∎

{` def:n-image: im_n(f) = Σ_{b:B} ||f⁻¹(b)||_n, with the factorization p, i. `}
def NImage (k : Nat) (A B : Type) (f : A → B) : Type ≔ Σ B (b ↦ Trunc k (BookFiber A B f b))

def n_image_factor (k : Nat) (A B : Type) (f : A → B) : A → NImage k A B f
  ≔ a ↦ (f a, trunc_unit k (BookFiber A B f (f a)) (a, refl (f a)))

def n_image_include (k : Nat) (A B : Type) (f : A → B) : NImage k A B f → B ≔ z ↦ z .fst

def n_image_triangle (k : Nat) (A B : Type) (f : A → B)
  : Id (A → B) f (compose A (NImage k A B f) B (n_image_include k A B f) (n_image_factor k A B f))
  ≔ refl f

{` "Observe that im_{-1}(f) ≡ im(f)": judgmentally. `}
def n_image_minus_one (A B : Type) (f : A → B) : Id Type (NImage zero. A B f) (Image A B f)
  ≔ refl (Image A B f)

def n_image_zero_equiv (A B : Type) (f : A → B) : Equiv (NImage (suc. zero.) A B f) (ZeroImage A B f)
  ≔ family_equiv B (b ↦ Trunc (suc. zero.) (BookFiber A B f b)) (b ↦ SetTrunc (BookFiber A B f b))
      (b ↦ trunc_one_set_trunc_equiv (BookFiber A B f b))

{` def:n-connected. `}
def NConnectedType (k : Nat) (A : Type) : Type ≔ BookIsContr (Trunc k A)
def NConnectedMap (k : Nat) (A B : Type) (f : A → B) : Type ≔ (b : B) → NConnectedType k (BookFiber A B f b)

def n_connected_type_prop (k : Nat) (A : Type) : isProp (NConnectedType k A) ≔ book_iscontr_isprop (Trunc k A)
def n_connected_map_prop (k : Nat) (A B : Type) (f : A → B) : isProp (NConnectedMap k A B f)
  ≔ pi_prop B (b ↦ NConnectedType k (BookFiber A B f b)) (b ↦ n_connected_type_prop k (BookFiber A B f b))

def n_connected_type_equiv (k : Nat) (X Y : Type) (e : Equiv X Y) (h : NConnectedType k X) : NConnectedType k Y
  ≔ transport Type (T ↦ NConnectedType k T) X Y (ua X Y e) h

{` The (-1)-connected types are the nonempty ones and the 0-connected types
   are the connected ones; the (-1)-connected maps are the surjections. `}
def minus_one_connected_nonempty (A : Type) : Equiv (NConnectedType zero. A) (Mere A)
  ≔ iff_equiv (NConnectedType zero. A) (Mere A) (n_connected_type_prop zero. A) (mere_isprop A)
      (h ↦ h .center) (m ↦ (m, mere_isprop A m))

def zero_connected_connected (A : Type) : Equiv (NConnectedType (suc. zero.) A) (Connected A)
  ≔ compose_equiv (NConnectedType (suc. zero.) A) (BookIsContr (SetTrunc A)) (Connected A)
      (book_contractibility_equiv (Trunc (suc. zero.) A) (SetTrunc A) (trunc_one_set_trunc_equiv A))
      (canonical_inverse_equiv (Connected A) (BookIsContr (SetTrunc A)) (connected_set_trunc_equiv A))

def minus_one_connected_map_surjective (A B : Type) (f : A → B)
  : Equiv (NConnectedMap zero. A B f) (Surjective A B f)
  ≔ minus_one_connected_map_equiv A B f

def zero_connected_map_compare (A B : Type) (f : A → B)
  : Equiv (NConnectedMap (suc. zero.) A B f) (ZeroConnectedMap A B f)
  ≔ pi_family_equiv B (b ↦ NConnectedType (suc. zero.) (BookFiber A B f b)) (b ↦ BookIsContr (SetTrunc (BookFiber A B f b)))
      (b ↦ book_contractibility_equiv (Trunc (suc. zero.) (BookFiber A B f b)) (SetTrunc (BookFiber A B f b))
        (trunc_one_set_trunc_equiv (BookFiber A B f b)))

{` lem:trunc-n-connected: the constructor |_|_n : A → ||A||_n is n-connected. `}
def trunc_unit_fiber_center (k : Nat) (A : Type) (x : Trunc k A)
  : Trunc k (BookFiber A (Trunc k A) (trunc_unit k A) x)
  ≔ trunc_ind k A (truncation k A) (y ↦ Trunc k (BookFiber A (Trunc k A) (trunc_unit k A) y))
      (y ↦ trunc_level k (BookFiber A (Trunc k A) (trunc_unit k A) y))
      (a ↦ trunc_unit k (BookFiber A (Trunc k A) (trunc_unit k A) (trunc_unit k A a)) (a, refl (trunc_unit k A a))) x

def trunc_unit_fiber_center_beta (k : Nat) (A : Type) (a : A)
  : Id (Trunc k (BookFiber A (Trunc k A) (trunc_unit k A) (trunc_unit k A a)))
      (trunc_unit_fiber_center k A (trunc_unit k A a))
      (trunc_unit k (BookFiber A (Trunc k A) (trunc_unit k A) (trunc_unit k A a)) (a, refl (trunc_unit k A a)))
  ≔ trunc_ind_beta k A (truncation k A) (y ↦ Trunc k (BookFiber A (Trunc k A) (trunc_unit k A) y))
      (y ↦ trunc_level k (BookFiber A (Trunc k A) (trunc_unit k A) y))
      (a ↦ trunc_unit k (BookFiber A (Trunc k A) (trunc_unit k A) (trunc_unit k A a)) (a, refl (trunc_unit k A a))) a

def trunc_unit_fiber_contract_point (k : Nat) (A : Type) (a : A) (x : Trunc k A)
  (q : Id (Trunc k A) (trunc_unit k A a) x)
  : Id (Trunc k (BookFiber A (Trunc k A) (trunc_unit k A) x)) (trunc_unit_fiber_center k A x)
      (trunc_unit k (BookFiber A (Trunc k A) (trunc_unit k A) x) (a, inverse (Trunc k A) (trunc_unit k A a) x q))
  ≔ J (Trunc k A) (trunc_unit k A a)
      (x q ↦ Id (Trunc k (BookFiber A (Trunc k A) (trunc_unit k A) x)) (trunc_unit_fiber_center k A x)
        (trunc_unit k (BookFiber A (Trunc k A) (trunc_unit k A) x) (a, inverse (Trunc k A) (trunc_unit k A a) x q)))
      (concat (Trunc k (BookFiber A (Trunc k A) (trunc_unit k A) (trunc_unit k A a)))
        (trunc_unit_fiber_center k A (trunc_unit k A a))
        (trunc_unit k (BookFiber A (Trunc k A) (trunc_unit k A) (trunc_unit k A a)) (a, refl (trunc_unit k A a)))
        (trunc_unit k (BookFiber A (Trunc k A) (trunc_unit k A) (trunc_unit k A a))
          (a, inverse (Trunc k A) (trunc_unit k A a) (trunc_unit k A a) (refl (trunc_unit k A a))))
        (trunc_unit_fiber_center_beta k A a)
        (refl ((r ↦ trunc_unit k (BookFiber A (Trunc k A) (trunc_unit k A) (trunc_unit k A a)) (a, r))
            : Id (Trunc k A) (trunc_unit k A a) (trunc_unit k A a)
              → Trunc k (BookFiber A (Trunc k A) (trunc_unit k A) (trunc_unit k A a)))
          (inverse (Id (Trunc k A) (trunc_unit k A a) (trunc_unit k A a))
            (inverse (Trunc k A) (trunc_unit k A a) (trunc_unit k A a) (refl (trunc_unit k A a)))
            (refl (trunc_unit k A a)) (inverse_refl (Trunc k A) (trunc_unit k A a)))))
      x q

def trunc_unit_fiber_contract (k : Nat) (A : Type) (x : Trunc k A)
  (y : Trunc k (BookFiber A (Trunc k A) (trunc_unit k A) x))
  : Id (Trunc k (BookFiber A (Trunc k A) (trunc_unit k A) x)) (trunc_unit_fiber_center k A x) y
  ≔ let F ≔ BookFiber A (Trunc k A) (trunc_unit k A) x in
    trunc_ind k F (truncation k F) (w ↦ Id (Trunc k F) (trunc_unit_fiber_center k A x) w)
      (w ↦ hlevel_raise k (Id (Trunc k F) (trunc_unit_fiber_center k A x) w)
        (trunc_level k F (trunc_unit_fiber_center k A x) w))
      (z ↦ concat (Trunc k F) (trunc_unit_fiber_center k A x)
        (trunc_unit k F (z .fst, inverse (Trunc k A) (trunc_unit k A (z .fst)) x
          (inverse (Trunc k A) x (trunc_unit k A (z .fst)) (z .snd))))
        (trunc_unit k F z)
        (trunc_unit_fiber_contract_point k A (z .fst) x (inverse (Trunc k A) x (trunc_unit k A (z .fst)) (z .snd)))
        (refl ((r ↦ trunc_unit k F (z .fst, r)) : Id (Trunc k A) x (trunc_unit k A (z .fst)) → Trunc k F)
          (inverse_inverse (Trunc k A) x (trunc_unit k A (z .fst)) (z .snd)))) y

def trunc_unit_connected (k : Nat) (A : Type) : NConnectedMap k A (Trunc k A) (trunc_unit k A)
  ≔ x ↦ (trunc_unit_fiber_center k A x, trunc_unit_fiber_contract k A x)

{` The factorization through the n-image: i is n-truncated and p is n-connected. `}
def n_image_include_fiber_equiv (k : Nat) (A B : Type) (f : A → B) (b : B)
  : Equiv (BookFiber (NImage k A B f) B (n_image_include k A B f) b) (Trunc k (BookFiber A B f b))
  ≔ native_equivalence (BookFiber (NImage k A B f) B (n_image_include k A B f) b)
      (Trunc k (BookFiber A B f b)) (book_projection_fiber_equiv B (b ↦ Trunc k (BookFiber A B f b)) b)

def n_image_include_truncated (k : Nat) (A B : Type) (f : A → B)
  : TruncatedMap (suc. k) (NImage k A B f) B (n_image_include k A B f)
  ≔ b ↦ hlevel_equiv (suc. k) (Trunc k (BookFiber A B f b)) (BookFiber (NImage k A B f) B (n_image_include k A B f) b)
      (canonical_inverse_equiv (BookFiber (NImage k A B f) B (n_image_include k A B f) b)
        (Trunc k (BookFiber A B f b)) (n_image_include_fiber_equiv k A B f b))
      (trunc_level k (BookFiber A B f b))

def n_image_factor_fiber_equiv (k : Nat) (A B : Type) (f : A → B) (z : NImage k A B f)
  : Equiv (BookFiber A (NImage k A B f) (n_image_factor k A B f) z)
      (BookFiber (BookFiber A B f (z .fst)) (Trunc k (BookFiber A B f (z .fst)))
        (trunc_unit k (BookFiber A B f (z .fst))) (z .snd))
  ≔ let D ≔ Σ B (BookFiber A B f) in
    let G ≔ totalize B (BookFiber A B f) (b ↦ Trunc k (BookFiber A B f b))
      (b ↦ trunc_unit k (BookFiber A B f b)) in
    compose_equiv (BookFiber A (NImage k A B f) (n_image_factor k A B f) z)
      (BookFiber D (NImage k A B f) G z)
      (BookFiber (BookFiber A B f (z .fst)) (Trunc k (BookFiber A B f (z .fst)))
        (trunc_unit k (BookFiber A B f (z .fst))) (z .snd))
      (preequivalence_fiber_equiv A D (NImage k A B f) (fiber_decomposition_equiv A B f) G z)
      (total_fiber_equiv B (BookFiber A B f) (b ↦ Trunc k (BookFiber A B f b))
        (b ↦ trunc_unit k (BookFiber A B f b)) (z .fst) (z .snd))

def n_image_factor_connected (k : Nat) (A B : Type) (f : A → B)
  : NConnectedMap k A (NImage k A B f) (n_image_factor k A B f)
  ≔ z ↦ n_connected_type_equiv k
      (BookFiber (BookFiber A B f (z .fst)) (Trunc k (BookFiber A B f (z .fst)))
        (trunc_unit k (BookFiber A B f (z .fst))) (z .snd))
      (BookFiber A (NImage k A B f) (n_image_factor k A B f) z)
      (canonical_inverse_equiv (BookFiber A (NImage k A B f) (n_image_factor k A B f) z)
        (BookFiber (BookFiber A B f (z .fst)) (Trunc k (BookFiber A B f (z .fst)))
          (trunc_unit k (BookFiber A B f (z .fst))) (z .snd)) (n_image_factor_fiber_equiv k A B f z))
      (trunc_unit_connected k (BookFiber A B f (z .fst)) (z .snd))

{` xca:im_preserves_conn: every n-image (n >= -1) of a map out of a connected
   type is connected. `}
def n_image_connected (k : Nat) (A B : Type) (f : A → B) (hA : Connected A) : Connected (NImage k A B f)
  ≔ reflected_images_preserve_connectedness (Trunc k) (trunc_unit k) (trunc_unit_surjective k) A B f hA
