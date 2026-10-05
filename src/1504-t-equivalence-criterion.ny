export "1502-restriction-bundle"
export "1503-algebraic-elements"

{` Chapter 15 (galois.tex), rem:algebraic-endomorphisms-are-automorphisms,
   the parts that do not need algebraicity.

   (1) t : USym Gal(K, i) → fiber of restr_i over (K, i) is an equivalence
   as soon as every k-endomorphism of K is an equivalence
   (galois_t_is_equiv_of_endos): by galois_t_identification, t is the
   inclusion Aut_k(K) → End_k(K) up to equivalences, and that inclusion is
   an equivalence when every k-endomorphism is invertible. The first claim
   of the remark (algebraic ⇒ t equivalence) combines this with the theorem
   of the modules 1520–1539 that k-endomorphisms of algebraic
   extensions are equivalences (module 1510).

   (2) The ℚ → ℝ argument. ℝ and ℚ are not constructed in this project, so
   the argument is proved for any extension (K, i) of k with the property
   used by the book: with x < y meaning that y − x is the square of an
   invertible element (for ℝ: positive numbers are squares of nonzero
   numbers), "two elements lying in the same rational intervals are equal"
   (RationalSeparation, true for ℚ → ℝ). Then every k-endomorphism φ of K is
   the identity (real_like_endo_identity): φ is k-linear and sends squares
   of invertible elements to squares of invertible elements, hence
   preserves <, fixes i(p) and i(q), so i(p) < α < i(q) implies
   i(p) < φ(α) < i(q). The book phrases this with non-strict monotonicity
   and an irrational α; the strict order of squares of invertibles needs no
   injectivity argument and no case split on rationality. Consequently t is
   an equivalence (real_like_galois_t_equiv); with the non-algebraicity of
   ℚ → ℝ as a further hypothesis (not provable without ℝ) this is the
   counterexample to the converse (algebraic_converse_fails). As printed
   (defn:algebraic-element allowing the zero polynomial) no extension is
   non-algebraic (printed_non_algebraic_impossible). `}

def ring_hom_preserves_invertible (R S : AbstractRing) (φ : RingHom R S) (x : R .carrier) (h : IsInvertible R x)
  : IsInvertible S (φ .fst .fst x)
  ≔ let f ≔ φ .fst .fst in let B ≔ S .carrier in
    mere_rec (InverseWitness R x) (IsInvertible S (f x)) (is_invertible_prop S (f x))
      (w ↦ invertible_intro S (f x) (f (w .fst))
         (concat B (S .mul (f x) (f (w .fst))) (f (R .mul x (w .fst))) (S .one)
            (inverse B (f (R .mul x (w .fst))) (S .mul (f x) (f (w .fst))) (φ .snd .snd x (w .fst)))
            (concat B (f (R .mul x (w .fst))) (f (R .one)) (S .one) (refl f (w .snd .fst)) (φ .snd .fst)))
         (concat B (S .mul (f (w .fst)) (f x)) (f (R .mul (w .fst) x)) (S .one)
            (inverse B (f (R .mul (w .fst) x)) (S .mul (f (w .fst)) (f x)) (φ .snd .snd (w .fst) x))
            (concat B (f (R .mul (w .fst) x)) (f (R .one)) (S .one) (refl f (w .snd .snd)) (φ .snd .fst))))
      h

{` x < y: y − x is the square of an invertible element. `}
def SquareLess (R : AbstractRing) (x y : R .carrier) : Type
  ≔ Mere (Σ (R .carrier) (s ↦ Product (IsInvertible R s) (Id (R .carrier) (R .add y (R .neg x)) (R .mul s s))))

def ring_hom_preserves_difference (R S : AbstractRing) (φ : RingHom R S) (x y : R .carrier)
  : Id (S .carrier) (φ .fst .fst (R .add y (R .neg x))) (S .add (φ .fst .fst y) (S .neg (φ .fst .fst x)))
  ≔ let f ≔ φ .fst .fst in
    concat (S .carrier) (f (R .add y (R .neg x))) (S .add (f y) (f (R .neg x))) (S .add (f y) (S .neg (f x)))
      (φ .fst .snd y (R .neg x))
      (refl (S .add (f y)) (abstract_hom_preserves_inv (ring_additive_group R) (ring_additive_group S) f (φ .fst .snd) x))

def ring_hom_preserves_square_less (R S : AbstractRing) (φ : RingHom R S) (x y : R .carrier) (h : SquareLess R x y)
  : SquareLess S (φ .fst .fst x) (φ .fst .fst y)
  ≔ let f ≔ φ .fst .fst in let B ≔ S .carrier in
    let T ≔ Σ B (s ↦ Product (IsInvertible S s) (Id B (S .add (f y) (S .neg (f x))) (S .mul s s))) in
    mere_rec (Σ (R .carrier) (s ↦ Product (IsInvertible R s) (Id (R .carrier) (R .add y (R .neg x)) (R .mul s s))))
      (SquareLess S (f x) (f y)) (mere_isprop T)
      (w ↦ mere T (f (w .fst),
         (ring_hom_preserves_invertible R S φ (w .fst) (w .snd .fst),
          concat B (S .add (f y) (S .neg (f x))) (f (R .add y (R .neg x))) (S .mul (f (w .fst)) (f (w .fst)))
            (inverse B (f (R .add y (R .neg x))) (S .add (f y) (S .neg (f x))) (ring_hom_preserves_difference R S φ x y))
            (concat B (f (R .add y (R .neg x))) (f (R .mul (w .fst) (w .fst))) (S .mul (f (w .fst)) (f (w .fst)))
              (refl f (w .snd .snd)) (φ .snd .snd (w .fst) (w .fst))))))
      h

{` A k-endomorphism fixes the image of k. `}
def kalg_endo_fixes_base (k : Field) (E : FieldExt k) (φ : KAlgHom k E E) (p : k .fst .carrier)
  : Id (ext_carrier k E) (φ .fst .fst .fst (ext_map k E p)) (ext_map k E p)
  ≔ inverse (ext_carrier k E) (ext_map k E p) (φ .fst .fst .fst (ext_map k E p))
      (refl ((χ ↦ χ .fst .fst p) : RingHom (k .fst) (E .fst .fst) → ext_carrier k E) (φ .snd))

{` Two elements lying in the same "rational" intervals (i(p), i(q)) are equal. `}
def RationalSeparation (k : Field) (E : FieldExt k) : Type
  ≔ let K ≔ E .fst .fst in
    (α β : ext_carrier k E)
    → ((p q : k .fst .carrier) → SquareLess K (ext_map k E p) α → SquareLess K α (ext_map k E q)
         → Product (SquareLess K (ext_map k E p) β) (SquareLess K β (ext_map k E q)))
    → Id (ext_carrier k E) α β

{` rem:algebraic-endomorphisms-are-automorphisms, the ℚ → ℝ argument: every
   k-endomorphism is the identity. `}
def real_like_endo_identity (k : Field) (E : FieldExt k) (sep : RationalSeparation k E) (φ : KAlgHom k E E)
  (α : ext_carrier k E) : Id (ext_carrier k E) (φ .fst .fst .fst α) α
  ≔ let K ≔ E .fst .fst in let A ≔ K .carrier in let f ≔ φ .fst .fst .fst in
    inverse A α (f α)
      (sep α (f α) (p q hp hq ↦
         (transport A (x ↦ SquareLess K x (f α)) (f (ext_map k E p)) (ext_map k E p) (kalg_endo_fixes_base k E φ p)
            (ring_hom_preserves_square_less K K (φ .fst) (ext_map k E p) α hp),
          transport A (x ↦ SquareLess K (f α) x) (f (ext_map k E q)) (ext_map k E q) (kalg_endo_fixes_base k E φ q)
            (ring_hom_preserves_square_less K K (φ .fst) α (ext_map k E q) hq))))

{` A k-homomorphism whose map is an equivalence is a k-isomorphism. `}
def kalg_endo_to_kaut (k : Field) (E F : FieldExt k) (φ : KAlgHom k E F)
  (h : isEquiv (E .fst .fst .carrier) (F .fst .fst .carrier) (φ .fst .fst .fst)) : FieldExtIso k E F
  ≔ let j' ≔ φ .fst in
    (((j' .fst .fst, h),
      (j' .fst .snd, (j' .snd .snd,
        (abstract_hom_preserves_unit (ring_additive_group (E .fst .fst)) (ring_additive_group (F .fst .fst)) (j' .fst .fst) (j' .fst .snd),
         j' .snd .fst)))),
     inverse (RingHom (k .fst) (F .fst .fst)) (F .snd)
       (ring_hom_compose (k .fst) (E .fst .fst) (F .fst .fst) (E .snd) j') (φ .snd))

{` If every k-homomorphism E → F is an equivalence, the inclusion
   Iso_k(E, F) → hom_k(E, F) is an equivalence. `}
def kaut_kalg_equiv_of_endos (k : Field) (E F : FieldExt k)
  (H : (φ : KAlgHom k E F) → isEquiv (E .fst .fst .carrier) (F .fst .fst .carrier) (φ .fst .fst .fst))
  : Equiv (FieldExtIso k E F) (KAlgHom k E F)
  ≔ let P ≔ (σ ↦ Id (RingHom (k .fst) (F .fst .fst)) (field_iso_after k (E .fst) (F .fst) (E .snd) σ) (F .snd))
           : FieldIso (E .fst) (F .fst) → Type in
    quasi_inverse_equiv (FieldExtIso k E F) (KAlgHom k E F) (kaut_to_kalg k E F)
      (φ ↦ kalg_endo_to_kaut k E F φ (H φ))
      (σ ↦ subtype_equal (FieldIso (E .fst) (F .fst)) P
         (τ ↦ ring_hom_set (k .fst) (F .fst .fst) (field_iso_after k (E .fst) (F .fst) (E .snd) τ) (F .snd))
         (kalg_endo_to_kaut k E F (kaut_to_kalg k E F σ) (H (kaut_to_kalg k E F σ))) σ
         (ring_iso_path (E .fst .fst) (F .fst .fst)
           (kalg_endo_to_kaut k E F (kaut_to_kalg k E F σ) (H (kaut_to_kalg k E F σ)) .fst) (σ .fst)
           (refl (σ .fst .fst .map))))
      (φ ↦ kalg_hom_path k E F (kaut_to_kalg k E F (kalg_endo_to_kaut k E F φ (H φ))) φ
         (x ↦ refl (φ .fst .fst .fst x)))

{` t is an equivalence when every k-endomorphism of K is an equivalence. `}
def galois_t_is_equiv_of_endos (k : Field) (E : FieldExt k)
  (H : (φ : KAlgHom k E E) → isEquiv (E .fst .fst .carrier) (E .fst .fst .carrier) (φ .fst .fst .fst))
  : isEquiv (USym (galois_group k E)) (restriction_fiber_over k E E) (galois_t k E)
  ≔ let U ≔ USym (galois_group k E) in let Fb ≔ restriction_fiber_over k E E in
    let Φ ≔ restriction_fiber_kalg_equiv k E E in
    let e ≔ compose_equiv U (FieldExtIso k E E) Fb (galois_usym_kaut_equiv k E)
              (compose_equiv (FieldExtIso k E E) (KAlgHom k E E) Fb (kaut_kalg_equiv_of_endos k E E H)
                (canonical_inverse_equiv Fb (KAlgHom k E E) Φ)) in
    equiv_change_map U Fb e (galois_t k E)
      (g ↦ concat Fb (equiv_inverse_map Fb (KAlgHom k E E) Φ (kaut_to_kalg k E E (galois_usym_kaut_equiv k E .map g)))
             (equiv_inverse_map Fb (KAlgHom k E E) Φ (Φ .map (galois_t k E g))) (galois_t k E g)
             (refl (equiv_inverse_map Fb (KAlgHom k E E) Φ)
               (inverse (KAlgHom k E E) (Φ .map (galois_t k E g)) (kaut_to_kalg k E E (galois_usym_kaut_equiv k E .map g))
                 (galois_t_identification k E g)))
             (equiv_retraction Fb (KAlgHom k E E) Φ (galois_t k E g)))
      .equiv

def pointwise_identity_is_equiv (A : Type) (f : A → A) (h : (x : A) → Id A (f x) x) : isEquiv A A f
  ≔ equiv_change_map A A (identity_equiv A) f (x ↦ inverse A (f x) x (h x)) .equiv

{` For a "real-like" extension (ℚ → ℝ), t is an equivalence. `}
def real_like_galois_t_equiv (k : Field) (E : FieldExt k) (sep : RationalSeparation k E)
  : isEquiv (USym (galois_group k E)) (restriction_fiber_over k E E) (galois_t k E)
  ≔ galois_t_is_equiv_of_endos k E
      (φ ↦ pointwise_identity_is_equiv (E .fst .fst .carrier) (φ .fst .fst .fst) (real_like_endo_identity k E sep φ))

{` The converse of "algebraic ⇒ t equivalence" fails for any real-like
   extension that is not algebraic (ℚ → ℝ; non-algebraicity is a hypothesis). `}
def algebraic_converse_fails (k : Field) (E : FieldExt k) (sep : RationalSeparation k E)
  (na : Not (IsAlgebraicExtension k E))
  : Product (isEquiv (USym (galois_group k E)) (restriction_fiber_over k E E) (galois_t k E))
      (Not (IsAlgebraicExtension k E))
  ≔ (real_like_galois_t_equiv k E sep, na)

{` With the printed definition no extension is non-algebraic. `}
def printed_non_algebraic_impossible (k : Field) (E : FieldExt k) : Not (Not (IsAlgebraicExtensionAsPrinted k E))
  ≔ n ↦ n (every_extension_algebraic_as_printed k E)

{` Litmus: the identity extension satisfies the criterion (its only
   k-endomorphism fixes everything), so its t is an equivalence. `}
def identity_ext_endo_identity (K : Field) (φ : KAlgHom K (identity_extension K) (identity_extension K))
  (x : K .fst .carrier) : Id (K .fst .carrier) (φ .fst .fst .fst x) x
  ≔ kalg_endo_fixes_base K (identity_extension K) φ x

def identity_ext_galois_t_equiv (K : Field)
  : isEquiv (USym (galois_group K (identity_extension K))) (restriction_fiber_over K (identity_extension K) (identity_extension K))
      (galois_t K (identity_extension K))
  ≔ galois_t_is_equiv_of_endos K (identity_extension K)
      (φ ↦ pointwise_identity_is_equiv (K .fst .carrier) (φ .fst .fst .fst) (identity_ext_endo_identity K φ))
