export "231-truncated-sums-and-reflections"

{` The type in thm:n-im-univ-prop for n = k - 1 >= -1: factorizations of f
   with an n-connected first map and an n-truncated second map. `}
def NImageFactorizations (k : Nat) (A B : Type) (f : A → B) : Type
  ≔ Σ Type (C ↦ Σ (A → C) (g ↦ Σ (C → B) (h ↦ Product (Id (A → B) f (compose A C B h g))
      (Product (NConnectedMap k A C g) (TruncatedMap (suc. k) C B h)))))

def n_image_factorization (k : Nat) (A B : Type) (f : A → B) : NImageFactorizations k A B f
  ≔ (NImage k A B f, (n_image_factor k A B f, (n_image_include k A B f,
      (n_image_triangle k A B f, (n_image_factor_connected k A B f, n_image_include_truncated k A B f)))))

def NFactorizationProperties (k : Nat) (A B : Type) (f : A → B) (t : Factorizations A B f) : Type
  ≔ Product (NConnectedMap k A (t .fst) (t .snd .fst)) (TruncatedMap (suc. k) (t .fst) B (t .snd .snd .fst))

def n_factorization_properties_prop (k : Nat) (A B : Type) (f : A → B) (t : Factorizations A B f)
  : isProp (NFactorizationProperties k A B f t)
  ≔ product_prop (NConnectedMap k A (t .fst) (t .snd .fst)) (TruncatedMap (suc. k) (t .fst) B (t .snd .snd .fst))
      (n_connected_map_prop k A (t .fst) (t .snd .fst)) (truncated_map_prop (suc. k) (t .fst) B (t .snd .snd .fst))

def n_factorization_regroup (k : Nat) (A B : Type) (f : A → B)
  : Equiv (NImageFactorizations k A B f) (Σ (Factorizations A B f) (NFactorizationProperties k A B f))
  ≔ quasi_inverse_equiv (NImageFactorizations k A B f) (Σ (Factorizations A B f) (NFactorizationProperties k A B f))
      (t ↦ ((t .fst, (t .snd .fst, (t .snd .snd .fst, t .snd .snd .snd .fst))), t .snd .snd .snd .snd))
      (t ↦ (t .fst .fst, (t .fst .snd .fst, (t .fst .snd .snd .fst, (t .fst .snd .snd .snd, t .snd)))))
      (t ↦ refl t) (t ↦ refl t)

{` Comparison of the n-image of hg with X, for g n-connected and h n-truncated. `}
def n_composite_section (k : Nat) (A X B : Type) (g : A → X) (hg : NConnectedMap k A X g)
  (h : X → B) (hh : TruncatedMap (suc. k) X B h) (z : NImage k A B (compose A X B h g))
  : BookFiber X B h (z .fst)
  ≔ n_composite_truncated_fiber_equiv k A X B g hg h hh (z .fst) .map (z .snd)

def n_composite_lift (k : Nat) (A X B : Type) (g : A → X) (hg : NConnectedMap k A X g)
  (h : X → B) (hh : TruncatedMap (suc. k) X B h) : NImage k A B (compose A X B h g) → X
  ≔ z ↦ n_composite_section k A X B g hg h hh z .fst

def n_composite_carrier_equiv (k : Nat) (A X B : Type) (g : A → X) (hg : NConnectedMap k A X g)
  (h : X → B) (hh : TruncatedMap (suc. k) X B h) : Equiv (NImage k A B (compose A X B h g)) X
  ≔ (n_composite_lift k A X B g hg h hh,
      compose_equiv (NImage k A B (compose A X B h g)) (Σ B (BookFiber X B h)) X
        (family_equiv B (b ↦ Trunc k (BookFiber A B (compose A X B h g) b)) (BookFiber X B h)
          (n_composite_truncated_fiber_equiv k A X B g hg h hh)) (sum_of_fibers_equiv X B h) .equiv)

def n_composite_right_triangle (k : Nat) (A X B : Type) (g : A → X) (hg : NConnectedMap k A X g)
  (h : X → B) (hh : TruncatedMap (suc. k) X B h)
  : Id (NImage k A B (compose A X B h g) → B) (n_image_include k A B (compose A X B h g))
      (compose (NImage k A B (compose A X B h g)) X B h (n_composite_lift k A X B g hg h hh))
  ≔ funext (NImage k A B (compose A X B h g)) (_ ↦ B) (n_image_include k A B (compose A X B h g))
      (compose (NImage k A B (compose A X B h g)) X B h (n_composite_lift k A X B g hg h hh))
      (z ↦ n_composite_section k A X B g hg h hh z .snd)

{` The computation of the comparison at the units: (g a, refl) is carried to
   the section value by the computation rule of the truncation. `}
def n_composite_unit_path (k : Nat) (A X B : Type) (g : A → X) (hg : NConnectedMap k A X g)
  (h : X → B) (hh : TruncatedMap (suc. k) X B h) (a : A)
  : Id (BookFiber X B h (h (g a))) (g a, refl (h (g a)))
      (n_composite_section k A X B g hg h hh (n_image_factor k A B (compose A X B h g) a))
  ≔ let F ≔ compose A X B h g in let Fib ≔ BookFiber A B F (F a) in
    trunc_extend_beta k Fib (truncation k Fib) (BookFiber X B h (F a)) (hh (F a))
      (composite_fiber_map A X B g h (F a)) (a, refl (F a))

def n_composite_pointwise (k : Nat) (A X B : Type) (g : A → X) (hg : NConnectedMap k A X g)
  (h : X → B) (hh : TruncatedMap (suc. k) X B h) (a : A)
  : Id (Id B (h (g a)) (h (n_composite_lift k A X B g hg h hh (n_image_factor k A B (compose A X B h g) a))))
      (map_path X B h (g a) (n_composite_lift k A X B g hg h hh (n_image_factor k A B (compose A X B h g) a))
        (n_composite_unit_path k A X B g hg h hh a .fst))
      (n_composite_section k A X B g hg h hh (n_image_factor k A B (compose A X B h g) a) .snd)
  ≔ let F ≔ compose A X B h g in
    let z ≔ n_image_factor k A B F a in
    let l ≔ n_composite_lift k A X B g hg h hh z in
    let s ≔ n_composite_section k A X B g hg h hh z in
    let gam ≔ n_composite_unit_path k A X B g hg h hh a in
    concat (Id B (F a) (h l)) (map_path X B h (g a) l (gam .fst))
      (concat B (F a) (F a) (h l) (refl (F a)) (map_path X B h (g a) l (gam .fst))) (s .snd)
      (inverse (Id B (F a) (h l)) (concat B (F a) (F a) (h l) (refl (F a)) (map_path X B h (g a) l (gam .fst)))
        (map_path X B h (g a) l (gam .fst)) (concat_1p B (F a) (h l) (map_path X B h (g a) l (gam .fst))))
      (id_to_equiv (Id (x ↦ Id B (F a) (h x)) (gam .fst) (refl (F a)) (s .snd))
        (Id (Id B (F a) (h l)) (concat B (F a) (F a) (h l) (refl (F a)) (map_path X B h (g a) l (gam .fst))) (s .snd))
        (pathover_mapped_paths_type X B h (F a) (g a) l (gam .fst) (refl (F a)) (s .snd)) .map (gam .snd))

def n_composite_factor_path (k : Nat) (A X B : Type) (g : A → X) (hg : NConnectedMap k A X g)
  (h : X → B) (hh : TruncatedMap (suc. k) X B h)
  : Id (A → X) g (compose A (NImage k A B (compose A X B h g)) X (n_composite_lift k A X B g hg h hh)
      (n_image_factor k A B (compose A X B h g)))
  ≔ funext A (_ ↦ X) g (compose A (NImage k A B (compose A X B h g)) X (n_composite_lift k A X B g hg h hh)
      (n_image_factor k A B (compose A X B h g))) (a ↦ n_composite_unit_path k A X B g hg h hh a .fst)

def n_composite_two_path (k : Nat) (A X B : Type) (g : A → X) (hg : NConnectedMap k A X g)
  (h : X → B) (hh : TruncatedMap (suc. k) X B h)
  : Id (Id (A → B) (compose A X B h g)
        (compose A X B h (compose A (NImage k A B (compose A X B h g)) X (n_composite_lift k A X B g hg h hh)
          (n_image_factor k A B (compose A X B h g)))))
      (map_path (A → X) (A → B) (compose A X B h) g
        (compose A (NImage k A B (compose A X B h g)) X (n_composite_lift k A X B g hg h hh)
          (n_image_factor k A B (compose A X B h g))) (n_composite_factor_path k A X B g hg h hh))
      (refl (precompose A (NImage k A B (compose A X B h g)) B (n_image_factor k A B (compose A X B h g)))
        (n_composite_right_triangle k A X B g hg h hh))
  ≔ let F ≔ compose A X B h g in
    let NI ≔ NImage k A B F in
    let lift ≔ n_composite_lift k A X B g hg h hh in
    let fac ≔ n_image_factor k A B F in
    let G ≔ compose A X B h (compose A NI X lift fac) in
    let P ≔ n_composite_factor_path k A X B g hg h hh in
    let RT ≔ n_composite_right_triangle k A X B g hg h hh in
    let a1 ≔ map_path (A → X) (A → B) (compose A X B h) g (compose A NI X lift fac) P in
    let a2 ≔ refl (precompose A NI B fac) RT in
    equivalence_injective (Id (A → B) F G) (Homotopy A (_ ↦ B) F G) (function_extensionality A (_ ↦ B) F G) a1 a2
      (funext A (a ↦ Id B (F a) (G a)) (happly A (_ ↦ B) F G a1) (happly A (_ ↦ B) F G a2)
        (a ↦ calc
          happly A (_ ↦ B) F G a1 a = map_path X B h (g a) (lift (fac a)) (happly A (_ ↦ X) g (compose A NI X lift fac) P a)
            by refl (happly A (_ ↦ B) F G a1 a)
          = map_path X B h (g a) (lift (fac a)) (n_composite_unit_path k A X B g hg h hh a .fst)
            by refl (map_path X B h (g a) (lift (fac a)))
              (inverse (Id X (g a) (lift (fac a))) (n_composite_unit_path k A X B g hg h hh a .fst)
                (happly A (_ ↦ X) g (compose A NI X lift fac) P a)
                (funext_beta A (_ ↦ X) g (compose A NI X lift fac) (b ↦ n_composite_unit_path k A X B g hg h hh b .fst) a))
          = n_composite_section k A X B g hg h hh (fac a) .snd by n_composite_pointwise k A X B g hg h hh a
          = happly NI (_ ↦ B) (n_image_include k A B F) (compose NI X B h lift) RT (fac a)
            by funext_beta NI (_ ↦ B) (n_image_include k A B F) (compose NI X B h lift)
              (z ↦ n_composite_section k A X B g hg h hh z .snd) (fac a)
          = happly A (_ ↦ B) F G a2 a by refl (happly A (_ ↦ B) F G a2 a) ∎))

def n_composite_comparison_coherence (k : Nat) (A X B : Type) (g : A → X) (hg : NConnectedMap k A X g)
  (h : X → B) (hh : TruncatedMap (suc. k) X B h)
  : Id (RightDiagonals A X B h (compose A X B h g)) (g, refl (compose A X B h g))
      (factorization_compare_map A (NImage k A B (compose A X B h g)) X B (compose A X B h g)
        (n_image_factor k A B (compose A X B h g)) (n_image_include k A B (compose A X B h g))
        (n_image_triangle k A B (compose A X B h g)) h
        (n_composite_lift k A X B g hg h hh, n_composite_right_triangle k A X B g hg h hh))
  ≔ let F ≔ compose A X B h g in
    let NI ≔ NImage k A B F in
    let lift ≔ n_composite_lift k A X B g hg h hh in
    let fac ≔ n_image_factor k A B F in
    let K ≔ compose A NI X lift fac in
    let P ≔ n_composite_factor_path k A X B g hg h hh in
    let RT ≔ n_composite_right_triangle k A X B g hg h hh in
    let T2 ≔ concat (A → B) F F (compose A X B h K) (refl F) (refl (precompose A NI B fac) RT) in
    (P, id_to_equiv
      (Id (Id (A → B) F (compose A X B h K))
        (concat (A → B) F F (compose A X B h K) (refl F) (map_path (A → X) (A → B) (compose A X B h) g K P)) T2)
      (Id (u ↦ Id (A → B) F (compose A X B h u)) P (refl F) T2)
      (inverse Type (Id (u ↦ Id (A → B) F (compose A X B h u)) P (refl F) T2)
        (Id (Id (A → B) F (compose A X B h K))
          (concat (A → B) F F (compose A X B h K) (refl F) (map_path (A → X) (A → B) (compose A X B h) g K P)) T2)
        (pathover_mapped_paths_type (A → X) (A → B) (compose A X B h) F g K P (refl F) T2))
      .map (refl (concat (A → B) F F (compose A X B h K) (refl F)) (n_composite_two_path k A X B g hg h hh)))

def n_image_triangular_factorization (k : Nat) (A B : Type) (f : A → B) : Factorizations A B f
  ≔ (NImage k A B f, (n_image_factor k A B f, (n_image_include k A B f, n_image_triangle k A B f)))

def n_composite_factorization_path (k : Nat) (A X B : Type) (g : A → X) (hg : NConnectedMap k A X g)
  (h : X → B) (hh : TruncatedMap (suc. k) X B h)
  : Id (Factorizations A B (compose A X B h g))
      (n_image_triangular_factorization k A B (compose A X B h g)) (X, (g, (h, refl (compose A X B h g))))
  ≔ factorization_equivalence_comparison A (NImage k A B (compose A X B h g)) X B (compose A X B h g)
      (n_image_factor k A B (compose A X B h g)) (n_image_include k A B (compose A X B h g))
      (n_image_triangle k A B (compose A X B h g)) g h (refl (compose A X B h g))
      (n_composite_carrier_equiv k A X B g hg h hh) (n_composite_right_triangle k A X B g hg h hh)
      (n_composite_comparison_coherence k A X B g hg h hh)

def n_image_triangle_path_from_reverse (k : Nat) (A C B : Type) (g : A → C) (hg : NConnectedMap k A C g)
  (h : C → B) (hh : TruncatedMap (suc. k) C B h) (f : A → B) (q : Id (A → B) (compose A C B h g) f)
  : Id (Factorizations A B f) (n_image_triangular_factorization k A B f)
      (C, (g, (h, inverse (A → B) (compose A C B h g) f q)))
  ≔ let F ≔ compose A C B h g in
    J (A → B) F
      (f q ↦ Id (Factorizations A B f) (n_image_triangular_factorization k A B f)
        (C, (g, (h, inverse (A → B) F f q))))
      (concat (Factorizations A B F) (n_image_triangular_factorization k A B F)
        (C, (g, (h, refl F))) (C, (g, (h, inverse (A → B) F F (refl F))))
        (n_composite_factorization_path k A C B g hg h hh)
        (refl ((r ↦ (C, (g, (h, r)))) : Id (A → B) F F → Factorizations A B F)
          (inverse (Id (A → B) F F) (inverse (A → B) F F (refl F)) (refl F)
            (inverse_refl (A → B) F)))) f q

def n_image_triangular_contraction (k : Nat) (A C B : Type) (g : A → C) (hg : NConnectedMap k A C g)
  (h : C → B) (hh : TruncatedMap (suc. k) C B h) (f : A → B) (r : Id (A → B) f (compose A C B h g))
  : Id (Factorizations A B f) (n_image_triangular_factorization k A B f) (C, (g, (h, r)))
  ≔ let F ≔ compose A C B h g in
    concat (Factorizations A B f) (n_image_triangular_factorization k A B f)
      (C, (g, (h, inverse (A → B) F f (inverse (A → B) f F r)))) (C, (g, (h, r)))
      (n_image_triangle_path_from_reverse k A C B g hg h hh f (inverse (A → B) f F r))
      (refl ((s ↦ (C, (g, (h, s)))) : Id (A → B) f F → Factorizations A B f)
        (inverse_inverse (A → B) f F r))

def n_image_factorization_contraction (k : Nat) (A B : Type) (f : A → B) (u : NImageFactorizations k A B f)
  : Id (NImageFactorizations k A B f) (n_image_factorization k A B f) u
  ≔ equivalence_injective (NImageFactorizations k A B f)
      (Σ (Factorizations A B f) (NFactorizationProperties k A B f)) (n_factorization_regroup k A B f)
      (n_image_factorization k A B f) u
      (subtype_equal (Factorizations A B f) (NFactorizationProperties k A B f) (n_factorization_properties_prop k A B f)
        (n_factorization_regroup k A B f .map (n_image_factorization k A B f)) (n_factorization_regroup k A B f .map u)
        (n_image_triangular_contraction k A (u .fst) B (u .snd .fst) (u .snd .snd .snd .snd .fst)
          (u .snd .snd .fst) (u .snd .snd .snd .snd .snd) f (u .snd .snd .snd .fst)))

{` thm:n-im-univ-prop for every n >= -1 (n = k - 1): the full six-component
   type of factorizations through the n-image is contractible, with the
   canonical n-image factorization as center.  For n = -2 see
   minus_two_image_universal_property (module 108). `}
def n_image_universal_property (k : Nat) (A B : Type) (f : A → B) : BookIsContr (NImageFactorizations k A B f)
  ≔ (n_image_factorization k A B f, n_image_factorization_contraction k A B f)

def n_image_book_universal_property (k : Nat) (A B : Type) (f : A → B)
  : BookIsContr (Σ (Factorizations A B f) (NFactorizationProperties k A B f))
  ≔ book_contractibility_equiv (NImageFactorizations k A B f)
      (Σ (Factorizations A B f) (NFactorizationProperties k A B f)) (n_factorization_regroup k A B f) .map
      (n_image_universal_property k A B f)
