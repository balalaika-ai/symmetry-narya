export "1401-inner-product-spaces"

{` Chapter 14, proof of thm:GramSchmidt (geometry.tex 40-44), part 1:
   finite linear combinations Σ_i a_i c_i in a module, membership in the
   span of a finite family, closure of spans, linear independence, and the
   inner product of a linear combination with a vector. `}

def fin_linear_combination (R : AbstractRing) (W : RingModule R) (m : Nat) (a : Fin m → R .carrier)
  (c : Fin m → W .carrier) : W .carrier
  ≔ fin_module_sum R W m (i ↦ W .smul (a i) (c i))

def InLinearSpan (R : AbstractRing) (W : RingModule R) (m : Nat) (c : Fin m → W .carrier) (v : W .carrier) : Type
  ≔ Σ (Fin m → R .carrier) (a ↦ Id (W .carrier) v (fin_linear_combination R W m a c))

def span_zero (R : AbstractRing) (W : RingModule R) (m : Nat) (c : Fin m → W .carrier)
  : InLinearSpan R W m c (W .zero)
  ≔ (_ ↦ R .zero,
     inverse (W .carrier) (fin_linear_combination R W m (_ ↦ R .zero) c) (W .zero)
       (fin_module_sum_zero R W m (i ↦ W .smul (R .zero) (c i)) (i ↦ smul_zero_scalar R W (c i))))

def span_add (R : AbstractRing) (W : RingModule R) (m : Nat) (c : Fin m → W .carrier) (v w : W .carrier)
  (hv : InLinearSpan R W m c v) (hw : InLinearSpan R W m c w) : InLinearSpan R W m c (W .add v w)
  ≔ let a ≔ hv .fst in let b ≔ hw .fst in
    let E ≔ standard_module_extension R m W c in
    (i ↦ R .add (a i) (b i),
     concat (W .carrier) (W .add v w) (W .add (fin_linear_combination R W m a c) (fin_linear_combination R W m b c))
       (fin_linear_combination R W m (i ↦ R .add (a i) (b i)) c)
       (refl (W .add) (hv .snd) (hw .snd))
       (inverse (W .carrier) (fin_linear_combination R W m (i ↦ R .add (a i) (b i)) c)
         (W .add (fin_linear_combination R W m a c) (fin_linear_combination R W m b c)) (E .fst .snd a b)))

def span_smul (R : AbstractRing) (W : RingModule R) (m : Nat) (c : Fin m → W .carrier) (d : R .carrier)
  (v : W .carrier) (hv : InLinearSpan R W m c v) : InLinearSpan R W m c (W .smul d v)
  ≔ let a ≔ hv .fst in
    let E ≔ standard_module_extension R m W c in
    (i ↦ R .mul d (a i),
     concat (W .carrier) (W .smul d v) (W .smul d (fin_linear_combination R W m a c))
       (fin_linear_combination R W m (i ↦ R .mul d (a i)) c)
       (refl (W .smul d) (hv .snd))
       (inverse (W .carrier) (fin_linear_combination R W m (i ↦ R .mul d (a i)) c)
         (W .smul d (fin_linear_combination R W m a c)) (E .snd d a)))

def lc_neg (R : AbstractRing) (W : RingModule R) (m : Nat) (a : Fin m → R .carrier) (c : Fin m → W .carrier)
  : Id (W .carrier) (fin_linear_combination R W m (i ↦ R .neg (a i)) c) (W .neg (fin_linear_combination R W m a c))
  ≔ let E ≔ standard_module_extension R m W c in
    abstract_hom_preserves_inv (module_group R (standard_module R m)) (module_group R W) (E .fst .fst) (E .fst .snd) a

def span_neg (R : AbstractRing) (W : RingModule R) (m : Nat) (c : Fin m → W .carrier) (v : W .carrier)
  (hv : InLinearSpan R W m c v) : InLinearSpan R W m c (W .neg v)
  ≔ let a ≔ hv .fst in
    (i ↦ R .neg (a i),
     concat (W .carrier) (W .neg v) (W .neg (fin_linear_combination R W m a c))
       (fin_linear_combination R W m (i ↦ R .neg (a i)) c)
       (refl (W .neg) (hv .snd))
       (inverse (W .carrier) (fin_linear_combination R W m (i ↦ R .neg (a i)) c)
         (W .neg (fin_linear_combination R W m a c)) (lc_neg R W m a c)))

{` c_j is in the span of c (coefficients e_j). `}
def span_member (R : AbstractRing) (W : RingModule R) (m : Nat) (c : Fin m → W .carrier) (j : Fin m)
  : InLinearSpan R W m c (c j)
  ≔ (standard_basis R m j,
     inverse (W .carrier) (fin_linear_combination R W m (standard_basis R m j) c) (c j) (fin_delta_sum_right R W m c j))

{` A linear combination of elements of span(c) is in span(c). `}
def span_combination (R : AbstractRing) (W : RingModule R) (m : Nat) (c : Fin m → W .carrier) (k : Nat)
  (u : Fin k → W .carrier) (hu : (j : Fin k) → InLinearSpan R W m c (u j)) (d : Fin k → R .carrier)
  : InLinearSpan R W m c (fin_linear_combination R W k d u)
  ≔ match k [
  | zero. ↦ span_zero R W m c
  | suc. k ↦
    span_add R W m c (fin_linear_combination R W k (j ↦ d (inl. j)) (j ↦ u (inl. j)))
      (W .smul (d (inr. star.)) (u (inr. star.)))
      (span_combination R W m c k (j ↦ u (inl. j)) (j ↦ hu (inl. j)) (j ↦ d (inl. j)))
      (span_smul R W m c (d (inr. star.)) (u (inr. star.)) (hu (inr. star.))) ]

{` Extension of coefficients by 0 at the new (last) index. `}
def coefficients_extend_zero (R : AbstractRing) (m : Nat) (a : Fin m → R .carrier) : Fin (suc. m) → R .carrier
  ≔ [ inl. i ↦ a i | inr. _ ↦ R .zero ]

def lc_extend_zero (R : AbstractRing) (W : RingModule R) (m : Nat) (a : Fin m → R .carrier)
  (c : Fin (suc. m) → W .carrier)
  : Id (W .carrier) (fin_linear_combination R W (suc. m) (coefficients_extend_zero R m a) c)
      (fin_linear_combination R W m a (i ↦ c (inl. i)))
  ≔ let x ≔ fin_linear_combination R W m a (i ↦ c (inl. i)) in
    concat (W .carrier) (W .add x (W .smul (R .zero) (c (inr. star.)))) (W .add x (W .zero)) x
      (refl (W .add x) (smul_zero_scalar R W (c (inr. star.))))
      (W .add_laws .unit_right x)

def span_extend (R : AbstractRing) (W : RingModule R) (m : Nat) (c : Fin (suc. m) → W .carrier) (v : W .carrier)
  (h : InLinearSpan R W m (i ↦ c (inl. i)) v) : InLinearSpan R W (suc. m) c v
  ≔ (coefficients_extend_zero R m (h .fst),
     concat (W .carrier) v (fin_linear_combination R W m (h .fst) (i ↦ c (inl. i)))
       (fin_linear_combination R W (suc. m) (coefficients_extend_zero R m (h .fst)) c)
       (h .snd)
       (inverse (W .carrier) (fin_linear_combination R W (suc. m) (coefficients_extend_zero R m (h .fst)) c)
         (fin_linear_combination R W m (h .fst) (i ↦ c (inl. i))) (lc_extend_zero R W m (h .fst) c)))

{` Linear independence: Σ_i a_i c_i = 0 only for a = 0. `}
def LinearlyIndependent (R : AbstractRing) (W : RingModule R) (m : Nat) (c : Fin m → W .carrier) : Type
  ≔ (a : Fin m → R .carrier) → Id (W .carrier) (fin_linear_combination R W m a c) (W .zero)
    → (i : Fin m) → Id (R .carrier) (a i) (R .zero)

def independent_restrict (R : AbstractRing) (W : RingModule R) (m : Nat) (c : Fin (suc. m) → W .carrier)
  (h : LinearlyIndependent R W (suc. m) c) : LinearlyIndependent R W m (i ↦ c (inl. i))
  ≔ a p i ↦
    h (coefficients_extend_zero R m a)
      (concat (W .carrier) (fin_linear_combination R W (suc. m) (coefficients_extend_zero R m a) c)
         (fin_linear_combination R W m a (j ↦ c (inl. j))) (W .zero) (lc_extend_zero R W m a c) p)
      (inl. i)

{` The last member of an independent family is not in the span of the
   others: c_m = Σ a_i c_i gives the relation Σ (-a_i) c_i + 1·c_m = 0. `}
def independent_last_not_in_span (R : AbstractRing) (W : RingModule R) (ht : IsNonTrivialRing R) (m : Nat)
  (c : Fin (suc. m) → W .carrier) (h : LinearlyIndependent R W (suc. m) c)
  (hs : InLinearSpan R W m (i ↦ c (inl. i)) (c (inr. star.))) : Empty
  ≔ let a ≔ hs .fst in let T ≔ W .carrier in
    let l ≔ c (inr. star.) in
    let b : Fin (suc. m) → R .carrier ≔ [ inl. i ↦ R .neg (a i) | inr. _ ↦ R .one ] in
    let x ≔ fin_linear_combination R W m a (i ↦ c (inl. i)) in
    let rel : Id T (fin_linear_combination R W (suc. m) b c) (W .zero)
      ≔ calc
          W .add (fin_linear_combination R W m (i ↦ R .neg (a i)) (i ↦ c (inl. i))) (W .smul (R .one) l)
          = W .add (W .neg x) l
            by refl (W .add) (lc_neg R W m a (i ↦ c (inl. i))) (W .smul_one l)
          = W .add (W .neg l) l
            by refl ((y ↦ W .add (W .neg y) l) : T → T) (inverse T l x (hs .snd))
          = W .zero by ag_inv_left (module_group R W) l ∎ in
    ring_one_ne_zero R ht (h b rel (inr. star.))

{` Free modules on Fin n (used for thm:GramSchmidt and dimension
   invariance): for a basis b (W free on Fin n via b) the coordinate map
   δ : W → Rⁿ with δ(b_i) = e_i satisfies δ(Σ_i a_i b_i) = a, so b is
   linearly independent, and every v equals Σ_i δ(v)_i b_i. `}
def basis_coordinates (R : AbstractRing) (n : Nat) (W : RingModule R) (b : Fin n → W .carrier)
  (hb : IsFreeModuleOn R (standard_set n) W b)
  : LinearExtensions R (standard_set n) W b (standard_module R n) (standard_basis R n)
  ≔ hb (standard_module R n) (standard_basis R n) .center

def basis_coordinates_lc (R : AbstractRing) (n : Nat) (W : RingModule R) (b : Fin n → W .carrier)
  (hb : IsFreeModuleOn R (standard_set n) W b) (a : Fin n → R .carrier)
  : Id (Fin n → R .carrier) (basis_coordinates R n W b hb .fst .fst .fst (fin_linear_combination R W n a b)) a
  ≔ let Kn ≔ standard_module R n in
    let d ≔ basis_coordinates R n W b hb in let δ ≔ d .fst in let df ≔ δ .fst .fst in
    calc
      df (fin_linear_combination R W n a b) = fin_module_sum R Kn n (i ↦ df (W .smul (a i) (b i)))
        by linear_map_fin_sum R W Kn δ n (i ↦ W .smul (a i) (b i))
      = fin_module_sum R Kn n (i ↦ Kn .smul (a i) (standard_basis R n i))
        by refl (fin_module_sum R Kn n)
          (funext (Fin n) (_ ↦ Fin n → R .carrier) (i ↦ df (W .smul (a i) (b i)))
            (i ↦ Kn .smul (a i) (standard_basis R n i))
            (i ↦ concat (Fin n → R .carrier) (df (W .smul (a i) (b i))) (Kn .smul (a i) (df (b i)))
                   (Kn .smul (a i) (standard_basis R n i)) (δ .snd (a i) (b i)) (refl (Kn .smul (a i)) (d .snd i))))
      = a by standard_decomposition R n a ∎

def basis_independent (R : AbstractRing) (n : Nat) (W : RingModule R) (b : Fin n → W .carrier)
  (hb : IsFreeModuleOn R (standard_set n) W b)
  : LinearlyIndependent R W n b
  ≔ a p i ↦
    let Kn ≔ standard_module R n in
    let δ ≔ basis_coordinates R n W b hb .fst in let df ≔ δ .fst .fst in
    let q : Id (Fin n → R .carrier) a (_ ↦ R .zero)
      ≔ calc
          a = df (fin_linear_combination R W n a b)
            by inverse (Fin n → R .carrier) (df (fin_linear_combination R W n a b)) a (basis_coordinates_lc R n W b hb a)
          = df (W .zero) by refl df p
          = Kn .zero by abstract_hom_preserves_unit (module_group R W) (module_group R Kn) df (δ .fst .snd) ∎ in
    happly (Fin n) (_ ↦ R .carrier) a (_ ↦ R .zero) q i

{` v = Σ_i δ(v)_i b_i: ε ∘ δ and id are both linear extensions of b. `}
def basis_expansion (R : AbstractRing) (n : Nat) (W : RingModule R) (b : Fin n → W .carrier)
  (hb : IsFreeModuleOn R (standard_set n) W b) (v : W .carrier)
  : Id (W .carrier) v (fin_linear_combination R W n (basis_coordinates R n W b hb .fst .fst .fst v) b)
  ≔ let T ≔ W .carrier in let Kn ≔ standard_module R n in
    let d ≔ basis_coordinates R n W b hb in let δ ≔ d .fst in
    let ε ≔ standard_module_extension R n W b in
    let E ≔ LinearExtensions R (standard_set n) W b W b in
    let c ≔ hb W b in
    let e1 : E ≔ (linear_compose R W Kn W δ ε,
                  s ↦ concat T (ε .fst .fst (δ .fst .fst (b s))) (ε .fst .fst (standard_basis R n s)) (b s)
                        (refl (ε .fst .fst) (d .snd s)) (fin_delta_sum_right R W n b s)) in
    let e2 : E ≔ (linear_id R W, s ↦ refl (b s)) in
    let q : Id E e1 e2 ≔ concat E e1 (c .center) e2 (inverse E (c .center) e1 (c .contract e1)) (c .contract e2) in
    inverse T (ε .fst .fst (δ .fst .fst v)) v (refl ((x ↦ x .fst .fst .fst v) : E → T) q)

def basis_spans (R : AbstractRing) (n : Nat) (W : RingModule R) (b : Fin n → W .carrier)
  (hb : IsFreeModuleOn R (standard_set n) W b) (v : W .carrier) : InLinearSpan R W n b v
  ≔ (basis_coordinates R n W b hb .fst .fst .fst v, basis_expansion R n W b hb v)

{` Inner products of linear combinations. `}
def ip_lc_left (K : EuclideanField) (V : InnerProductSpace K) (m : Nat) (a : Fin m → ef_carrier K)
  (u : Fin m → ip_carrier K V) (w : ip_carrier K V)
  : Id (ef_carrier K) (V .form (fin_linear_combination (K .field .fst) (V .space) m a u) w)
      (fin_module_sum (K .field .fst) (ring_self_module (K .field .fst)) m (i ↦ K .field .fst .mul (a i) (V .form (u i) w)))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let M ≔ ring_self_module R in
    concat S (V .form (fin_linear_combination R (V .space) m a u) w)
      (fin_module_sum R M m (i ↦ V .form (V .space .smul (a i) (u i)) w))
      (fin_module_sum R M m (i ↦ R .mul (a i) (V .form (u i) w)))
      (linear_map_fin_sum R (V .space) M (ip_left_linear K V w) m (i ↦ V .space .smul (a i) (u i)))
      (refl (fin_module_sum R M m)
        (funext (Fin m) (_ ↦ S) (i ↦ V .form (V .space .smul (a i) (u i)) w) (i ↦ R .mul (a i) (V .form (u i) w))
          (i ↦ V .inner .smul_left (a i) (u i) w)))

{` Orthonormal families: H(u_i, u_j) = δ(i, j). `}
def IsOrthonormal (K : EuclideanField) (V : InnerProductSpace K) (m : Nat) (u : Fin m → ip_carrier K V) : Type
  ≔ (i j : Fin m) → Id (ef_carrier K) (V .form (u i) (u j)) (fin_delta (K .field .fst) m i j)

{` For an orthonormal u: H(Σ_i a_i u_i, u_j) = a_j. `}
def ip_lc_orthonormal (K : EuclideanField) (V : InnerProductSpace K) (m : Nat) (u : Fin m → ip_carrier K V)
  (on : IsOrthonormal K V m u) (a : Fin m → ef_carrier K) (j : Fin m)
  : Id (ef_carrier K) (V .form (fin_linear_combination (K .field .fst) (V .space) m a u) (u j)) (a j)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let M ≔ ring_self_module R in
    calc
      V .form (fin_linear_combination R (V .space) m a u) (u j)
      = fin_module_sum R M m (i ↦ R .mul (a i) (V .form (u i) (u j))) by ip_lc_left K V m a u (u j)
      = fin_module_sum R M m (i ↦ R .mul (a i) (fin_delta R m i j))
        by refl (fin_module_sum R M m)
          (funext (Fin m) (_ ↦ S) (i ↦ R .mul (a i) (V .form (u i) (u j))) (i ↦ R .mul (a i) (fin_delta R m i j))
            (i ↦ refl (R .mul (a i)) (on i j)))
      = a j by fin_delta_sum_left R m a j ∎
