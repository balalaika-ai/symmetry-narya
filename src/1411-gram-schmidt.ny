export "1410-linear-spans"

{` Chapter 14, thm:GramSchmidt (geometry.tex 34-44): any inner product
   space V of dimension n is merely equal to 𝕍ⁿ. As in the book's proof we
   may assume a basis b of V (HasDimension is a mere proposition) and apply
   Gram–Schmidt orthonormalization: by recursion on m, an independent
   family c : Fin m → V yields an orthonormal family u with c_j ∈ span(u)
   and u_j ∈ span(c); the new vector is u_m = s⁻¹ w with
   w = c_m − Σ_j H(c_m, u_j) u_j ≠ 0 and s = √H(w,w) (square root and
   inverse from the EuclideanField hypotheses). For a basis b the map
   ψ : Kⁿ → V, a ↦ Σ_i a_i u_i is a linear isometry with inverse
   v ↦ (H(v, u_j))_j, and the structure identity principle (module 1401)
   turns it into an identification. `}

def GramSchmidtData (K : EuclideanField) (V : InnerProductSpace K) (m : Nat) (c : Fin m → ip_carrier K V) : Type
  ≔ Σ (Fin m → ip_carrier K V) (u ↦
      Product (IsOrthonormal K V m u)
        (Product ((j : Fin m) → InLinearSpan (K .field .fst) (V .space) m u (c j))
          ((j : Fin m) → InLinearSpan (K .field .fst) (V .space) m c (u j))))

{` p = Σ_j H(c_m, u_j) u_j and w = c_m − p. `}
def gs_coefficients (K : EuclideanField) (V : InnerProductSpace K) (m : Nat) (c : Fin (suc. m) → ip_carrier K V)
  (u : Fin m → ip_carrier K V) : Fin m → ef_carrier K
  ≔ j ↦ V .form (c (inr. star.)) (u j)

def gs_projection (K : EuclideanField) (V : InnerProductSpace K) (m : Nat) (c : Fin (suc. m) → ip_carrier K V)
  (u : Fin m → ip_carrier K V) : ip_carrier K V
  ≔ fin_linear_combination (K .field .fst) (V .space) m (gs_coefficients K V m c u) u

def gs_residual (K : EuclideanField) (V : InnerProductSpace K) (m : Nat) (c : Fin (suc. m) → ip_carrier K V)
  (u : Fin m → ip_carrier K V) : ip_carrier K V
  ≔ V .space .add (c (inr. star.)) (V .space .neg (gs_projection K V m c u))

def gs_residual_orthogonal (K : EuclideanField) (V : InnerProductSpace K) (m : Nat) (c : Fin (suc. m) → ip_carrier K V)
  (u : Fin m → ip_carrier K V) (on : IsOrthonormal K V m u) (j : Fin m)
  : Id (ef_carrier K) (V .form (gs_residual K V m c u) (u j)) (K .field .fst .zero)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let W ≔ V .space in
    let p ≔ gs_projection K V m c u in let α ≔ gs_coefficients K V m c u in
    let cl ≔ c (inr. star.) in
    calc
      V .form (W .add cl (W .neg p)) (u j) = R .add (α j) (V .form (W .neg p) (u j))
        by V .inner .add_left cl (W .neg p) (u j)
      = R .add (α j) (R .neg (V .form p (u j)))
        by refl (R .add (α j))
          (abstract_hom_preserves_inv (module_group R W) (ring_additive_group R) (v ↦ V .form v (u j))
            (ip_left_linear K V (u j) .fst .snd) p)
      = R .add (α j) (R .neg (α j))
        by refl ((x ↦ R .add (α j) (R .neg x)) : S → S) (ip_lc_orthonormal K V m u on α j)
      = R .zero by R .add_laws .inv_right (α j) ∎

{` w ≠ 0: otherwise c_m = p ∈ span(u) ⊆ span(c_0, …, c_{m-1}). `}
def gs_residual_nonzero (K : EuclideanField) (V : InnerProductSpace K) (m : Nat) (c : Fin (suc. m) → ip_carrier K V)
  (ind : LinearlyIndependent (K .field .fst) (V .space) (suc. m) c) (u : Fin m → ip_carrier K V)
  (uc : (j : Fin m) → InLinearSpan (K .field .fst) (V .space) m (i ↦ c (inl. i)) (u j))
  : Not (Id (ip_carrier K V) (gs_residual K V m c u) (V .space .zero))
  ≔ q ↦
    let R ≔ K .field .fst in let W ≔ V .space in let T ≔ W .carrier in
    let p ≔ gs_projection K V m c u in let cl ≔ c (inr. star.) in
    let G ≔ module_group R W in
    let e : Id T cl p
      ≔ concat T cl (W .neg (W .neg p)) p (ag_inv_unique_left G (W .neg p) cl q) (ag_inv_inv G p) in
    let hp ≔ span_combination R W m (i ↦ c (inl. i)) m u uc (gs_coefficients K V m c u) in
    independent_last_not_in_span R W (ef_non_trivial K) m c ind
      (hp .fst, concat T cl p (fin_linear_combination R W m (hp .fst) (i ↦ c (inl. i))) e (hp .snd))

def gs_norm (K : EuclideanField) (V : InnerProductSpace K) (m : Nat) (c : Fin (suc. m) → ip_carrier K V)
  (u : Fin m → ip_carrier K V) : ef_carrier K
  ≔ K .sqrt (V .form (gs_residual K V m c u) (gs_residual K V m c u)) (V .inner .nonneg (gs_residual K V m c u))

def gs_norm_nonzero (K : EuclideanField) (V : InnerProductSpace K) (m : Nat) (c : Fin (suc. m) → ip_carrier K V)
  (ind : LinearlyIndependent (K .field .fst) (V .space) (suc. m) c) (u : Fin m → ip_carrier K V)
  (uc : (j : Fin m) → InLinearSpan (K .field .fst) (V .space) m (i ↦ c (inl. i)) (u j))
  : Not (Id (ef_carrier K) (gs_norm K V m c u) (K .field .fst .zero))
  ≔ q ↦
    let R ≔ K .field .fst in let S ≔ R .carrier in
    let w ≔ gs_residual K V m c u in let s ≔ gs_norm K V m c u in
    gs_residual_nonzero K V m c ind u uc
      (V .inner .definite w
        (calc
           V .form w w = R .mul s s
             by inverse S (R .mul s s) (V .form w w) (K .sqrt_square (V .form w w) (V .inner .nonneg w))
           = R .mul (R .zero) (R .zero) by refl (R .mul) q q
           = R .zero by ring_mul_zero_left R (R .zero) ∎))

def gs_norm_inverse (K : EuclideanField) (V : InnerProductSpace K) (m : Nat) (c : Fin (suc. m) → ip_carrier K V)
  (ind : LinearlyIndependent (K .field .fst) (V .space) (suc. m) c) (u : Fin m → ip_carrier K V)
  (uc : (j : Fin m) → InLinearSpan (K .field .fst) (V .space) m (i ↦ c (inl. i)) (u j))
  : InverseWitness (K .field .fst) (gs_norm K V m c u)
  ≔ ef_inv K (gs_norm K V m c u) (gs_norm_nonzero K V m c ind u uc)

{` The new vector u_m = s⁻¹ w. `}
def gs_new_vector (K : EuclideanField) (V : InnerProductSpace K) (m : Nat) (c : Fin (suc. m) → ip_carrier K V)
  (ind : LinearlyIndependent (K .field .fst) (V .space) (suc. m) c) (u : Fin m → ip_carrier K V)
  (uc : (j : Fin m) → InLinearSpan (K .field .fst) (V .space) m (i ↦ c (inl. i)) (u j)) : ip_carrier K V
  ≔ V .space .smul (gs_norm_inverse K V m c ind u uc .fst) (gs_residual K V m c u)

def gs_new_orthogonal (K : EuclideanField) (V : InnerProductSpace K) (m : Nat) (c : Fin (suc. m) → ip_carrier K V)
  (ind : LinearlyIndependent (K .field .fst) (V .space) (suc. m) c) (u : Fin m → ip_carrier K V)
  (on : IsOrthonormal K V m u)
  (uc : (j : Fin m) → InLinearSpan (K .field .fst) (V .space) m (i ↦ c (inl. i)) (u j)) (j : Fin m)
  : Id (ef_carrier K) (V .form (gs_new_vector K V m c ind u uc) (u j)) (K .field .fst .zero)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in
    let t ≔ gs_norm_inverse K V m c ind u uc .fst in let w ≔ gs_residual K V m c u in
    calc
      V .form (V .space .smul t w) (u j) = R .mul t (V .form w (u j)) by V .inner .smul_left t w (u j)
      = R .mul t (R .zero) by refl (R .mul t) (gs_residual_orthogonal K V m c u on j)
      = R .zero by ring_mul_zero_right R t ∎

def gs_new_unit (K : EuclideanField) (V : InnerProductSpace K) (m : Nat) (c : Fin (suc. m) → ip_carrier K V)
  (ind : LinearlyIndependent (K .field .fst) (V .space) (suc. m) c) (u : Fin m → ip_carrier K V)
  (uc : (j : Fin m) → InLinearSpan (K .field .fst) (V .space) m (i ↦ c (inl. i)) (u j))
  : Id (ef_carrier K) (V .form (gs_new_vector K V m c ind u uc) (gs_new_vector K V m c ind u uc)) (K .field .fst .one)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in
    let inv ≔ gs_norm_inverse K V m c ind u uc in
    let t ≔ inv .fst in let w ≔ gs_residual K V m c u in let s ≔ gs_norm K V m c u in
    let W ≔ V .space in
    calc
      V .form (W .smul t w) (W .smul t w) = R .mul t (V .form w (W .smul t w)) by V .inner .smul_left t w (W .smul t w)
      = R .mul t (R .mul t (V .form w w)) by refl (R .mul t) (ip_smul_right K V t w w)
      = R .mul t (R .mul t (R .mul s s))
        by refl ((x ↦ R .mul t (R .mul t x)) : S → S)
          (inverse S (R .mul s s) (V .form w w) (K .sqrt_square (V .form w w) (V .inner .nonneg w)))
      = R .mul t (R .mul (R .mul t s) s) by refl (R .mul t) (ring_mul_assoc R t s s)
      = R .mul t (R .mul (R .one) s) by refl ((x ↦ R .mul t (R .mul x s)) : S → S) (inv .snd .snd)
      = R .mul t s by refl (R .mul t) (ring_mul_one_left R s)
      = R .one by inv .snd .snd ∎

{` The extended family u' = (u, u_m). `}
def gs_extended (K : EuclideanField) (V : InnerProductSpace K) (m : Nat) (c : Fin (suc. m) → ip_carrier K V)
  (ind : LinearlyIndependent (K .field .fst) (V .space) (suc. m) c) (u : Fin m → ip_carrier K V)
  (uc : (j : Fin m) → InLinearSpan (K .field .fst) (V .space) m (i ↦ c (inl. i)) (u j))
  : Fin (suc. m) → ip_carrier K V
  ≔ [ inl. j ↦ u j | inr. _ ↦ gs_new_vector K V m c ind u uc ]

def gs_extended_orthonormal (K : EuclideanField) (V : InnerProductSpace K) (m : Nat) (c : Fin (suc. m) → ip_carrier K V)
  (ind : LinearlyIndependent (K .field .fst) (V .space) (suc. m) c) (u : Fin m → ip_carrier K V)
  (on : IsOrthonormal K V m u)
  (uc : (j : Fin m) → InLinearSpan (K .field .fst) (V .space) m (i ↦ c (inl. i)) (u j))
  : IsOrthonormal K V (suc. m) (gs_extended K V m c ind u uc)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in
    let um ≔ gs_new_vector K V m c ind u uc in
    i j ↦ match i, j [
    | inl. i, inl. j ↦ on i j
    | inl. i, inr. _ ↦
      concat S (V .form (u i) um) (V .form um (u i)) (R .zero) (V .inner .symmetric (u i) um)
        (gs_new_orthogonal K V m c ind u on uc i)
    | inr. _, inl. j ↦ gs_new_orthogonal K V m c ind u on uc j
    | inr. _, inr. _ ↦ gs_new_unit K V m c ind u uc ]

{` c_m = p + w = Σ_j H(c_m, u_j) u_j + s u_m. `}
def gs_last_in_span (K : EuclideanField) (V : InnerProductSpace K) (m : Nat) (c : Fin (suc. m) → ip_carrier K V)
  (ind : LinearlyIndependent (K .field .fst) (V .space) (suc. m) c) (u : Fin m → ip_carrier K V)
  (uc : (j : Fin m) → InLinearSpan (K .field .fst) (V .space) m (i ↦ c (inl. i)) (u j))
  : InLinearSpan (K .field .fst) (V .space) (suc. m) (gs_extended K V m c ind u uc) (c (inr. star.))
  ≔ let R ≔ K .field .fst in let W ≔ V .space in let T ≔ W .carrier in
    let inv ≔ gs_norm_inverse K V m c ind u uc in
    let t ≔ inv .fst in let w ≔ gs_residual K V m c u in let s ≔ gs_norm K V m c u in
    let p ≔ gs_projection K V m c u in let cl ≔ c (inr. star.) in
    let α ≔ gs_coefficients K V m c u in
    let ws : Id T (W .smul s (W .smul t w)) w
      ≔ calc
          W .smul s (W .smul t w) = W .smul (R .mul s t) w
            by inverse T (W .smul (R .mul s t) w) (W .smul s (W .smul t w)) (W .smul_mul s t w)
          = W .smul (R .one) w by refl ((x ↦ W .smul x w) : R .carrier → T) (inv .snd .fst)
          = w by W .smul_one w ∎ in
    let coeffs : Fin (suc. m) → R .carrier ≔ [ inl. j ↦ α j | inr. _ ↦ s ] in
    (coeffs,
     calc
       cl = W .add w p by inverse T (W .add w p) cl (ag_mul_cancel_inv_right (module_group R W) cl p)
       = W .add p w by W .add_comm w p
       = W .add p (W .smul s (W .smul t w)) by refl (W .add p) (inverse T (W .smul s (W .smul t w)) w ws) ∎)

def gs_new_in_span (K : EuclideanField) (V : InnerProductSpace K) (m : Nat) (c : Fin (suc. m) → ip_carrier K V)
  (ind : LinearlyIndependent (K .field .fst) (V .space) (suc. m) c) (u : Fin m → ip_carrier K V)
  (uc : (j : Fin m) → InLinearSpan (K .field .fst) (V .space) m (i ↦ c (inl. i)) (u j))
  : InLinearSpan (K .field .fst) (V .space) (suc. m) c (gs_new_vector K V m c ind u uc)
  ≔ let R ≔ K .field .fst in let W ≔ V .space in
    let p ≔ gs_projection K V m c u in let cl ≔ c (inr. star.) in
    span_smul R W (suc. m) c (gs_norm_inverse K V m c ind u uc .fst) (gs_residual K V m c u)
      (span_add R W (suc. m) c cl (W .neg p) (span_member R W (suc. m) c (inr. star.))
        (span_neg R W (suc. m) c p
          (span_extend R W m c p (span_combination R W m (i ↦ c (inl. i)) m u uc (gs_coefficients K V m c u)))))

def gs_step (K : EuclideanField) (V : InnerProductSpace K) (m : Nat) (c : Fin (suc. m) → ip_carrier K V)
  (ind : LinearlyIndependent (K .field .fst) (V .space) (suc. m) c)
  (ih : GramSchmidtData K V m (i ↦ c (inl. i))) : GramSchmidtData K V (suc. m) c
  ≔ let R ≔ K .field .fst in let W ≔ V .space in
    let u ≔ ih .fst in let on ≔ ih .snd .fst in let cu ≔ ih .snd .snd .fst in let uc ≔ ih .snd .snd .snd in
    let ue ≔ gs_extended K V m c ind u uc in
    (ue,
     (gs_extended_orthonormal K V m c ind u on uc,
      (j ↦ match j [
       | inl. j ↦ span_extend R W m ue (c (inl. j)) (cu j)
       | inr. star. ↦ gs_last_in_span K V m c ind u uc ],
       j ↦ match j [
       | inl. j ↦ span_extend R W m c (u j) (uc j)
       | inr. star. ↦ gs_new_in_span K V m c ind u uc ])))

{` Gram–Schmidt orthonormalization of an independent family. `}
def gram_schmidt_family (K : EuclideanField) (V : InnerProductSpace K) (m : Nat) (c : Fin m → ip_carrier K V)
  (ind : LinearlyIndependent (K .field .fst) (V .space) m c) : GramSchmidtData K V m c
  ≔ match m [
  | zero. ↦ ((j ↦ match j [ ]), ((i j ↦ match i [ ]), ((j ↦ match j [ ]), (j ↦ match j [ ]))))
  | suc. m ↦ gs_step K V m c ind
      (gram_schmidt_family K V m (i ↦ c (inl. i)) (independent_restrict (K .field .fst) (V .space) m c ind)) ]
