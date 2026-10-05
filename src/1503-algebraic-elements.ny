export "1501-field-extensions"

{` Chapter 15 (galois.tex), defn:algebraic-element, defn:algebraic-extension
   and defn:degree-field-extension.

   defn:algebraic-element as printed: α : K is algebraic over i : k → K if
     ‖Σ_{n : ℕ} Σ_{a : ⟦n+1⟧ → k} i(a(0)) + i(a(1))α + ⋯ + i(a(n))αⁿ = 0‖.
   As printed the polynomial may be zero (n = 0, a(0) = 0), so every element
   of every extension is algebraic (every_element_algebraic_as_printed) and
   the converse claim of rem:algebraic-endomorphisms-are-automorphisms
   (ℚ → ℝ is not algebraic) fails. The intended definition (a root of a
   nonzero polynomial) is IsAlgebraicElement: the leading coefficient a(n)
   is nonzero. The index m : ⟦n+1⟧ = Fin(n+1) is the m-th element in the
   standard order (Fin (suc n) = Fin n + 1, inr ★ the last, of index n);
   poly_value computes a(0) + a(1)x + ⋯ + a(n)xⁿ with x^m = (⋯(1·x)⋯)·x.

   defn:degree-field-extension: K is a k-vector space with scalar
   multiplication a·v ≔ i(a)v (field_ext_vector_space); (K, i) is finite
   when it is finite dimensional (IsFiniteDimensional of module 1302) and its
   degree is that dimension. "The dimension" presupposes invariance of
   dimension, which is not proved for arbitrary fields in this project
   (module 1413 proves it for euclidean fields); the degree is therefore
   the proposition ExtensionHasDegree k E n ([K : k] = n), and the number
   extension_degree is defined under the explicit hypothesis
   DimensionInvariance k. `}

def ring_power (R : AbstractRing) (x : R .carrier) (n : Nat) : R .carrier
  ≔ match n [ zero. ↦ R .one | suc. n ↦ R .mul (ring_power R x n) x ]

{` a(0) + a(1)x + ⋯ + a(n)xⁿ. `}
def poly_value (R : AbstractRing) (x : R .carrier) (n : Nat) (a : Fin (suc. n) → R .carrier) : R .carrier
  ≔ match n [
  | zero. ↦ a (inr. star.)
  | suc. n ↦ R .add (poly_value R x n (s ↦ a (inl. s))) (R .mul (a (inr. star.)) (ring_power R x (suc. n))) ]

def ext_carrier (k : Field) (E : FieldExt k) : Type ≔ E .fst .fst .carrier

def ext_map (k : Field) (E : FieldExt k) : k .fst .carrier → E .fst .fst .carrier ≔ E .snd .fst .fst

{` The value at α of the polynomial with coefficients i ∘ a. `}
def ext_poly_value (k : Field) (E : FieldExt k) (α : ext_carrier k E) (n : Nat) (a : Fin (suc. n) → k .fst .carrier)
  : ext_carrier k E
  ≔ poly_value (E .fst .fst) α n (m ↦ ext_map k E (a m))

{` defn:algebraic-element, literally as printed. `}
def IsAlgebraicElementAsPrinted (k : Field) (E : FieldExt k) (α : ext_carrier k E) : Type
  ≔ Mere (Σ Nat (n ↦ Σ (Fin (suc. n) → k .fst .carrier) (a ↦
      Id (ext_carrier k E) (ext_poly_value k E α n a) (E .fst .fst .zero))))

def ext_map_zero (k : Field) (E : FieldExt k) : Id (ext_carrier k E) (ext_map k E (k .fst .zero)) (E .fst .fst .zero)
  ≔ abstract_hom_preserves_unit (ring_additive_group (k .fst)) (ring_additive_group (E .fst .fst))
      (E .snd .fst .fst) (E .snd .fst .snd)

{` As printed, the zero polynomial makes every element algebraic. `}
def every_element_algebraic_as_printed (k : Field) (E : FieldExt k) (α : ext_carrier k E)
  : IsAlgebraicElementAsPrinted k E α
  ≔ mere (Σ Nat (n ↦ Σ (Fin (suc. n) → k .fst .carrier) (a ↦
            Id (ext_carrier k E) (ext_poly_value k E α n a) (E .fst .fst .zero))))
      (zero., (_ ↦ k .fst .zero, ext_map_zero k E))

{` defn:algebraic-element, corrected: α is merely a root of a polynomial
   a(0) + a(1)X + ⋯ + a(n)Xⁿ over k with a(n) ≠ 0. `}
def IsAlgebraicElement (k : Field) (E : FieldExt k) (α : ext_carrier k E) : Type
  ≔ Mere (Σ Nat (n ↦ Σ (Fin (suc. n) → k .fst .carrier) (a ↦
      Product (Not (Id (k .fst .carrier) (a (inr. star.)) (k .fst .zero)))
        (Id (ext_carrier k E) (ext_poly_value k E α n a) (E .fst .fst .zero)))))

def is_algebraic_element_prop (k : Field) (E : FieldExt k) (α : ext_carrier k E) : isProp (IsAlgebraicElement k E α)
  ≔ mere_isprop (Σ Nat (n ↦ Σ (Fin (suc. n) → k .fst .carrier) (a ↦
      Product (Not (Id (k .fst .carrier) (a (inr. star.)) (k .fst .zero)))
        (Id (ext_carrier k E) (ext_poly_value k E α n a) (E .fst .fst .zero)))))

def algebraic_element_as_printed (k : Field) (E : FieldExt k) (α : ext_carrier k E) (h : IsAlgebraicElement k E α)
  : IsAlgebraicElementAsPrinted k E α
  ≔ every_element_algebraic_as_printed k E α

{` defn:algebraic-extension (as printed, and with the corrected notion). `}
def IsAlgebraicExtensionAsPrinted (k : Field) (E : FieldExt k) : Type
  ≔ (α : ext_carrier k E) → IsAlgebraicElementAsPrinted k E α

def every_extension_algebraic_as_printed (k : Field) (E : FieldExt k) : IsAlgebraicExtensionAsPrinted k E
  ≔ α ↦ every_element_algebraic_as_printed k E α

def IsAlgebraicExtension (k : Field) (E : FieldExt k) : Type ≔ (α : ext_carrier k E) → IsAlgebraicElement k E α

{` Litmus: in the identity extension (K, id) every α is a root of
   X - α = (-α) + 1·X, whose leading coefficient 1 is nonzero. `}
def linear_coefficients (R : AbstractRing) (α : R .carrier) : Fin (suc. (suc. zero.)) → R .carrier
  ≔ [ inl. _ ↦ R .neg α | inr. _ ↦ R .one ]

def linear_poly_root (R : AbstractRing) (α : R .carrier)
  : Id (R .carrier) (poly_value R α (suc. zero.) (linear_coefficients R α)) (R .zero)
  ≔ let A ≔ R .carrier in
    calc
      R .add (R .neg α) (R .mul (R .one) (R .mul (R .one) α))
      = R .add (R .neg α) (R .mul (R .one) α)
        by refl (R .add (R .neg α)) (ring_mul_one_left R (R .mul (R .one) α))
      = R .add (R .neg α) α by refl (R .add (R .neg α)) (ring_mul_one_left R α)
      = R .add α (R .neg α) by ring_add_comm R (R .neg α) α
      = R .zero by R .add_laws .inv_right α ∎

def identity_extension_algebraic (K : Field) : IsAlgebraicExtension K (identity_extension K)
  ≔ α ↦ mere (Σ Nat (n ↦ Σ (Fin (suc. n) → K .fst .carrier) (a ↦
            Product (Not (Id (K .fst .carrier) (a (inr. star.)) (K .fst .zero)))
              (Id (K .fst .carrier) (ext_poly_value K (identity_extension K) α n a) (K .fst .zero)))))
      (suc. zero., (linear_coefficients (K .fst) α,
        (e ↦ K .snd .fst .snd (inverse (K .fst .carrier) (K .fst .one) (K .fst .zero) e),
         linear_poly_root (K .fst) α)))

{` Litmus: poly_value computes 1 + x + x² at x = 1 in 𝔽₂ to 1 + 1 + 1 = 1. `}
def f2_poly_litmus : Id Bool (poly_value f2_ring true. (suc. (suc. zero.)) (_ ↦ true.)) true. ≔ refl true.

{` K as a k-vector space through i: a·v ≔ i(a)v. `}
def field_ext_vector_space (k : Field) (E : FieldExt k) : VectorSpace k
  ≔ let K ≔ E .fst .fst in let i ≔ E .snd .fst .fst in let A ≔ K .carrier in
    (A, K .zero, K .add, K .neg, K .add_laws, ring_add_comm K, (a v ↦ K .mul (i a) v),
     v ↦ concat A (K .mul (i (k .fst .one)) v) (K .mul (K .one) v) v
           (refl ((x ↦ K .mul x v) : A → A) (E .snd .snd .fst)) (ring_mul_one_left K v),
     a b v ↦ concat A (K .mul (i (k .fst .mul a b)) v) (K .mul (K .mul (i a) (i b)) v) (K .mul (i a) (K .mul (i b) v))
           (refl ((x ↦ K .mul x v) : A → A) (E .snd .snd .snd a b))
           (inverse A (K .mul (i a) (K .mul (i b) v)) (K .mul (K .mul (i a) (i b)) v) (ring_mul_assoc K (i a) (i b) v)),
     a b v ↦ concat A (K .mul (i (k .fst .add a b)) v) (K .mul (K .add (i a) (i b)) v) (K .add (K .mul (i a) v) (K .mul (i b) v))
           (refl ((x ↦ K .mul x v) : A → A) (E .snd .fst .snd a b))
           (ring_rdistr K (i a) (i b) v),
     a v w ↦ ring_ldistr K (i a) v w)

{` defn:degree-field-extension. `}
def IsFiniteExtension (k : Field) (E : FieldExt k) : Type ≔ IsFiniteDimensional k (field_ext_vector_space k E)

{` [K : k] = n. `}
def ExtensionHasDegree (k : Field) (E : FieldExt k) (n : Nat) : Type ≔ HasDimension k n (field_ext_vector_space k E)

{` Invariance of dimension for k-vector spaces (explicit hypothesis). `}
def DimensionInvariance (k : Field) : Type
  ≔ (V : VectorSpace k) (n m : Nat) → HasDimension k n V → HasDimension k m V → Id Nat n m

def extension_degree_data_prop (k : Field) (E : FieldExt k) (inv : DimensionInvariance k)
  : isProp (Σ Nat (n ↦ ExtensionHasDegree k E n))
  ≔ u v ↦ subtype_equal Nat (n ↦ ExtensionHasDegree k E n)
      (n ↦ mere_isprop (Σ (Fin n → ext_carrier k E) (b ↦ IsFreeVectorSpace k (standard_set n) (field_ext_vector_space k E) b)))
      u v (inv (field_ext_vector_space k E) (u .fst) (v .fst) (u .snd) (v .snd))

{` The degree [(K, i)] of a finite extension, given invariance of dimension. `}
def extension_degree (k : Field) (E : FieldExt k) (inv : DimensionInvariance k) (h : IsFiniteExtension k E) : Nat
  ≔ mere_rec (Σ Nat (n ↦ ExtensionHasDegree k E n)) (Σ Nat (n ↦ ExtensionHasDegree k E n))
      (extension_degree_data_prop k E inv) (u ↦ u) h .fst

def extension_degree_spec (k : Field) (E : FieldExt k) (inv : DimensionInvariance k) (h : IsFiniteExtension k E)
  : ExtensionHasDegree k E (extension_degree k E inv h)
  ≔ mere_rec (Σ Nat (n ↦ ExtensionHasDegree k E n)) (Σ Nat (n ↦ ExtensionHasDegree k E n))
      (extension_degree_data_prop k E inv) (u ↦ u) h .snd

{` Litmus: [K : K] = 1 for the identity extension. `}
def identity_extension_degree_one (K : Field) : ExtensionHasDegree K (identity_extension K) (suc. zero.)
  ≔ mere (Σ (Fin (suc. zero.) → K .fst .carrier)
            (b ↦ IsFreeVectorSpace K (standard_set (suc. zero.)) (field_ext_vector_space K (identity_extension K)) b))
      (ring_self_generator (K .fst), ring_self_module_free (K .fst))

def identity_extension_finite (K : Field) : IsFiniteExtension K (identity_extension K)
  ≔ mere (Σ Nat (n ↦ ExtensionHasDegree K (identity_extension K) n)) (suc. zero., identity_extension_degree_one K)
