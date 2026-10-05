export "bridge-02a-poly"
export "../../../src/1509-field-dimension-invariance"

{` Bridges for galois.tex: the restriction map, t, algebraic
   elements and extensions, rem:algebraic-endomorphisms-are-automorphisms,
   finite extensions and degree.

   blind_restr, BlindRestrFiber, the point id_K of the fiber, blind_t and
   blind_ext_vector_space are ours definitionally (blind_t up to the
   identification of the two USym types, bridge-01). The printed (blind
   literal) notion of algebraic element is the trivially true proposition,
   like ours as printed. The rem's first claim with the printed notion is
   refuted by our 𝔽₂(X), X ↦ X² (module 1532); the corrected first claim
   follows from ours given decidable equality of K (in particular under
   excluded middle). The second claim as printed is refuted (every
   extension is algebraic); the corrected one follows from ours for any
   extension with RationalSeparation that is not algebraic (ℚ → ℝ is not
   constructed). `}

def bridge_def_restr (k : Field) (E : FieldExt k)
  : Id (FieldExt (E .fst) → FieldExt k) (blind_restr k E) (field_ext_restriction k E)
  ≔ refl (field_ext_restriction k E)

{` lem:field-ext-restriction-set-bundle. `}
def bridge_field_ext_restriction_set_bundle : blind_field_ext_restriction_set_bundle
  ≔ k E ↦ field_ext_restriction_set_bundle k E

def bridge_def_restr_fiber (k : Field) (E y : FieldExt k)
  : Id Type (BlindRestrFiber k E y) (restriction_fiber_over k E y)
  ≔ refl (restriction_fiber_over k E y)

def bridge_def_restr_fiber_id (k : Field) (E : FieldExt k)
  : Id (restriction_fiber_over k E E) (blind_restr_fiber_id k E) (restriction_identity_point k E)
  ≔ refl (restriction_identity_point k E)

{` blind_t is our galois_t. `}
def bridge_def_t (k : Field) (E : FieldExt k) (g : ComponentLoop k E)
  : Id (restriction_fiber_over k E E) (blind_t k E (bridge_usym_blind_in k E g)) (galois_t k E (bridge_usym_ours_in k E g))
  ≔ refl (galois_t k E (bridge_usym_ours_in k E g))

def bridge_t_equiv_to_blind (k : Field) (E : FieldExt k)
  (h : isEquiv (USym (galois_group k E)) (restriction_fiber_over k E E) (galois_t k E))
  : BookIsEquiv (USym (BlindGaloisGroup k E)) (BlindRestrFiber k E E) (blind_t k E)
  ≔ let Fb ≔ restriction_fiber_over k E E in
    let e ≔ compose_equiv (USym (BlindGaloisGroup k E)) (USym (galois_group k E)) Fb
              (bridge_def_galois_usym k E) (galois_t k E, h) in
    book_equivalence (USym (BlindGaloisGroup k E)) Fb
      (equiv_change_map (USym (BlindGaloisGroup k E)) Fb e (blind_t k E) (g ↦ refl (blind_t k E g))) .equiv

def bridge_t_equiv_from_blind (k : Field) (E : FieldExt k)
  (h : BookIsEquiv (USym (BlindGaloisGroup k E)) (BlindRestrFiber k E E) (blind_t k E))
  : isEquiv (USym (galois_group k E)) (restriction_fiber_over k E E) (galois_t k E)
  ≔ let Fb ≔ restriction_fiber_over k E E in
    let e ≔ native_equivalence (USym (BlindGaloisGroup k E)) Fb (blind_t k E, h) in
    let e2 ≔ compose_equiv (USym (galois_group k E)) (USym (BlindGaloisGroup k E)) Fb
               (quasi_inverse_equiv (USym (galois_group k E)) (USym (BlindGaloisGroup k E))
                  (bridge_usym_to_blind k E) (bridge_usym_to_ours k E) (g ↦ refl g) (g ↦ refl g))
               e in
    equiv_change_map (USym (galois_group k E)) Fb e2 (galois_t k E) (g ↦ refl (galois_t k E g)) .equiv

{` ---- defn:algebraic-element / defn:algebraic-extension ---- `}

{` The literal blind notion holds for every element (zero polynomial). `}
def bridge_blind_algebraic_trivial (k : Field) (E : FieldExt k) (α : ext_carrier k E) : BlindIsAlgebraicElement k E α
  ≔ let K ≔ E .fst .fst in let kc ≔ k .fst .carrier in
    let T ≔ Σ Nat (n ↦ Σ (Fin (suc. n) → kc) (a ↦ Id (K .carrier) (blind_poly_eval k E n a α) (K .zero))) in
    mere T (zero., (_ ↦ k .fst .zero,
      calc
        K .add (K .zero) (K .mul (ext_map k E (k .fst .zero)) (K .one)) = K .mul (ext_map k E (k .fst .zero)) (K .one)
          by K .add_laws .unit_left (K .mul (ext_map k E (k .fst .zero)) (K .one))
        = ext_map k E (k .fst .zero) by ring_mul_one_right K (ext_map k E (k .fst .zero))
        = K .zero by ext_map_zero k E ∎))

{` Literal blind ≃ our printed notion: both are the trivially true proposition. `}
def bridge_def_algebraic_element (k : Field) (E : FieldExt k) (α : ext_carrier k E)
  : Equiv (BlindIsAlgebraicElement k E α) (IsAlgebraicElementAsPrinted k E α)
  ≔ let K ≔ E .fst .fst in let kc ≔ k .fst .carrier in
    iff_equiv (BlindIsAlgebraicElement k E α) (IsAlgebraicElementAsPrinted k E α)
      (mere_isprop (Σ Nat (n ↦ Σ (Fin (suc. n) → kc) (a ↦ Id (K .carrier) (blind_poly_eval k E n a α) (K .zero)))))
      (mere_isprop (Σ Nat (n ↦ Σ (Fin (suc. n) → kc) (a ↦ Id (K .carrier) (ext_poly_value k E α n a) (K .zero)))))
      (_ ↦ every_element_algebraic_as_printed k E α) (_ ↦ bridge_blind_algebraic_trivial k E α)

{` The blind vacuity claim, derived from ours. `}
def bridge_algebraic_element_as_printed_vacuous : blind_algebraic_element_as_printed_vacuous
  ≔ k E α ↦ equiv_inverse_map (BlindIsAlgebraicElement k E α) (IsAlgebraicElementAsPrinted k E α)
      (bridge_def_algebraic_element k E α) (every_element_algebraic_as_printed k E α)

{` Corrected notions: ours ⇒ blind always, blind ⇒ ours with decidable equality of k (bridge-02a). `}
def bridge_def_algebraic_ext_corrected_to (k : Field) (E : FieldExt k) (h : IsAlgebraicExtension k E)
  : BlindIsAlgebraicExtCorrected k E
  ≔ α ↦ bridge_algebraic_element_to_blind k E α (h α)

def bridge_def_algebraic_ext_corrected_from (k : Field) (E : FieldExt k) (dec : DecidableEquality (k .fst .carrier))
  (h : BlindIsAlgebraicExtCorrected k E) : IsAlgebraicExtension k E
  ≔ α ↦ bridge_algebraic_element_from_blind k E dec α (h α)

def bridge_def_algebraic_ext (k : Field) (E : FieldExt k)
  : Product (BlindIsAlgebraicExt k E → IsAlgebraicExtensionAsPrinted k E) (IsAlgebraicExtensionAsPrinted k E → BlindIsAlgebraicExt k E)
  ≔ (_ ↦ every_extension_algebraic_as_printed k E, _ ↦ α ↦ bridge_blind_algebraic_trivial k E α)

{` ---- rem:algebraic-endomorphisms-are-automorphisms ---- `}

{` First claim, literal: refuted by 𝔽₂(X)/𝔽₂ (module 1532). `}
def bridge_algebraic_t_equiv_refuted : Not blind_algebraic_t_equiv
  ≔ H ↦ f2_rational_t_not_equiv
      (bridge_t_equiv_from_blind f2_field f2_rational_ext
        (H f2_field f2_rational_ext (α ↦ bridge_blind_algebraic_trivial f2_field f2_rational_ext α)))

{` First claim, corrected: from ours, given decidable equality of K, or excluded middle. `}
def bridge_algebraic_t_equiv_corrected_dec (k : Field) (E : FieldExt k) (dec : DecidableEquality (ext_carrier k E))
  (h : BlindIsAlgebraicExtCorrected k E)
  : BookIsEquiv (USym (BlindGaloisGroup k E)) (BlindRestrFiber k E E) (blind_t k E)
  ≔ bridge_t_equiv_to_blind k E
      (algebraic_galois_t_equiv_dec k E dec (bridge_def_algebraic_ext_corrected_from k E (bridge_dec_base k E dec) h))

def bridge_algebraic_t_equiv_corrected_lem (lem : ExcludedMiddle) : blind_algebraic_t_equiv_corrected
  ≔ k E h ↦ bridge_algebraic_t_equiv_corrected_dec k E (lem_set_decidable_equality lem (ext_carrier k E) (ring_set (E .fst .fst))) h

{` Converse: the blind corrected claim gives ours (without decidability). `}
def bridge_algebraic_t_equiv_corrected_converse (H : blind_algebraic_t_equiv_corrected) (k : Field) (E : FieldExt k)
  (h : IsAlgebraicExtension k E) : isEquiv (USym (galois_group k E)) (restriction_fiber_over k E E) (galois_t k E)
  ≔ bridge_t_equiv_from_blind k E (H k E (bridge_def_algebraic_ext_corrected_to k E h))

{` Second claim, literal: refuted (no extension is non-algebraic as printed). `}
def bridge_t_equiv_not_algebraic_refuted : Not blind_t_equiv_not_algebraic
  ≔ w ↦ w .snd .snd .snd (α ↦ bridge_blind_algebraic_trivial (w .fst) (w .snd .fst) α)

{` Second claim, corrected: from ours for any non-algebraic extension with RationalSeparation. `}
def bridge_t_equiv_not_algebraic_corrected_cond (k : Field) (E : FieldExt k) (sep : RationalSeparation k E)
  (na : Not (BlindIsAlgebraicExtCorrected k E)) : blind_t_equiv_not_algebraic_corrected
  ≔ (k, (E, (bridge_t_equiv_to_blind k E (real_like_galois_t_equiv k E sep), na)))

{` ---- defn:degree-field-extension ---- `}

def bridge_def_ext_vector_space (k : Field) (E : FieldExt k)
  : Id (VectorSpace k) (blind_ext_vector_space k E) (field_ext_vector_space k E)
  ≔ refl (field_ext_vector_space k E)

def bridge_finite_to_ours (k : Field) (E : FieldExt k) (h : BlindIsFiniteExt k E) : IsFiniteExtension k E
  ≔ mere (Σ Nat (n ↦ ExtensionHasDegree k E n)) h

def bridge_finite_to_blind (k : Field) (E : FieldExt k) (h : IsFiniteExtension k E) : BlindIsFiniteExt k E
  ≔ mere_rec (Σ Nat (n ↦ ExtensionHasDegree k E n)) (Σ Nat (n ↦ ExtensionHasDegree k E n))
      (extension_degree_data_prop k E (field_dimension_invariance k)) (u ↦ u) h

{` BlindIsFiniteExt (Σ n, merely free on n generators) is a proposition by
   invariance of dimension (module 1509), hence equivalent to ours. `}
def bridge_def_finite_ext (k : Field) (E : FieldExt k) : Equiv (BlindIsFiniteExt k E) (IsFiniteExtension k E)
  ≔ iff_equiv (BlindIsFiniteExt k E) (IsFiniteExtension k E)
      (extension_degree_data_prop k E (field_dimension_invariance k))
      (mere_isprop (Σ Nat (n ↦ ExtensionHasDegree k E n)))
      (bridge_finite_to_ours k E) (bridge_finite_to_blind k E)

def bridge_def_ext_degree (k : Field) (E : FieldExt k) (h : BlindIsFiniteExt k E)
  : Id Nat (blind_ext_degree k E h) (field_extension_degree k E (bridge_finite_to_ours k E h))
  ≔ refl (h .fst)

def bridge_def_ext_degree_converse (k : Field) (E : FieldExt k) (h : IsFiniteExtension k E)
  : Id Nat (field_extension_degree k E h) (blind_ext_degree k E (bridge_finite_to_blind k E h))
  ≔ refl (field_extension_degree k E h)
