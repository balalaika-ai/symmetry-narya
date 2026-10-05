export "1504-t-equivalence-criterion"
export "1523-algebraic-endomorphisms"

{` Chapter 15 (galois.tex), rem:algebraic-endomorphisms-are-automorphisms,
   first claim: when the extension (K, i) is algebraic, t is an
   equivalence. "Algebraic" is the corrected notion of module 1503 (as
   printed every extension is algebraic, and t is not an equivalence for
   every extension: module 1532 formalizes the counterexample 𝔽₂(X) with
   X ↦ X²). The proof needs decidable equality of K (explicit hypothesis of
   algebraic_galois_t_equiv_dec; excluded middle in algebraic_galois_t_equiv
   implies it) through algebraic_kalg_endo_is_equiv_dec (modules
   1520–1523: k-endomorphisms of algebraic extensions are equivalences) and
   galois_t_is_equiv_of_endos (module 1504). `}

def algebraic_galois_t_equiv_dec (k : Field) (E : FieldExt k) (dec : DecidableEquality (ext_carrier k E))
  (h : IsAlgebraicExtension k E)
  : isEquiv (USym (galois_group k E)) (restriction_fiber_over k E E) (galois_t k E)
  ≔ galois_t_is_equiv_of_endos k E (φ ↦ algebraic_kalg_endo_is_equiv_dec k E dec h φ)

def algebraic_galois_t_equiv (lem : ExcludedMiddle) (k : Field) (E : FieldExt k) (h : IsAlgebraicExtension k E)
  : isEquiv (USym (galois_group k E)) (restriction_fiber_over k E E) (galois_t k E)
  ≔ galois_t_is_equiv_of_endos k E (φ ↦ algebraic_kalg_endo_is_equiv lem k E h φ)

{` Litmus: the identity extension is algebraic, so its t is an equivalence. `}
def identity_extension_algebraic_t_equiv (lem : ExcludedMiddle) (K : Field)
  : isEquiv (USym (galois_group K (identity_extension K)))
      (restriction_fiber_over K (identity_extension K) (identity_extension K)) (galois_t K (identity_extension K))
  ≔ algebraic_galois_t_equiv lem K (identity_extension K) (identity_extension_algebraic K)
