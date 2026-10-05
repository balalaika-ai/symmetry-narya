export "1520-field-hom-injective"
export "1410-linear-spans"

{` Chapter 15 (galois.tex), defn:degree-field-extension: invariance of
   dimension over an arbitrary field, so that "the dimension" of a finite
   extension is well defined without hypotheses. Module 1413 (chapter 14)
   proves dimension_unique only for euclidean fields: its trace argument
   gives n·1 = m·1, which yields n = m only in characteristic 0. Here the
   statement is proved for every field (in the book's sense: non-invertible
   elements are zero) by elimination:

   an injective linear map f : Kᵐ → Kⁿ forces m ≤ n
   (field_injective_linear_le). Induction on n. For n = 0, e_m ↦ 0 forces
   1 = 0. For n + 1 and m + 1, suppose m ≰ n (the goal m ≤ n is
   decidable). Let v = f(e_last). Each coordinate v_j is zero: v_j is not
   invertible, since with c v_j = 1 the map
     y ↦ (f(y, 0) − f(y, 0)_j c v) with coordinate j deleted : Kᵐ → Kⁿ
   is linear and injective, so m ≤ n by induction. Hence v = 0 and
   e_last = 0 by injectivity, i.e. 1 = 0. No decidable equality or
   excluded middle on K is used: the field axiom turns "not invertible"
   into "zero", and the only case distinction is on m ≤ n in ℕ.

   field_dimension_unique repeats the reduction of dimension_unique
   (module 1413: two bases give mutually inverse linear maps Kⁿ ⇄ Kᵐ) with
   this lemma in place of the trace argument. Consequently
   DimensionInvariance k holds for every field k (field_dimension_invariance)
   and the degree [K : k] of a finite extension is defined without
   hypotheses (field_extension_degree). `}

{` fin_skip n j : Fin n → Fin (n + 1), the increasing injection missing j. `}
def fin_skip (n : Nat) (j : Fin (suc. n)) (k : Fin n) : Fin (suc. n)
  ≔ match n [
  | zero. ↦ match k [ ]
  | suc. n ↦ match j [
    | inr. _ ↦ inl. k
    | inl. j ↦ match k [ inl. k ↦ inl. (fin_skip n j k) | inr. _ ↦ inr. star. ] ] ]

{` A function on Fin (n + 1) vanishing at j and at every fin_skip n j k vanishes. `}
def fin_skip_cover (S : Type) (z : S) (n : Nat) (j : Fin (suc. n)) (w : Fin (suc. n) → S)
  (hj : Id S (w j) z) (hk : (k : Fin n) → Id S (w (fin_skip n j k)) z) (x : Fin (suc. n)) : Id S (w x) z
  ≔ match n [
  | zero. ↦ match x [
    | inl. e ↦ match e [ ]
    | inr. u ↦ match j [ inl. e ↦ match e [ ] | inr. v ↦ match u, v [ star., star. ↦ hj ] ] ]
  | suc. n ↦ match j [
    | inr. v ↦ match x [ inl. x ↦ hk x | inr. u ↦ match u, v [ star., star. ↦ hj ] ]
    | inl. j ↦ match x [
      | inr. u ↦ match u [ star. ↦ hk (inr. star.) ]
      | inl. x ↦ fin_skip_cover S z n j (y ↦ w (inl. y)) hj (k ↦ hk (inl. k)) x ] ] ]

{` −(a + b) = −a + −b. `}
def ring_neg_add_split (R : AbstractRing) (a b : R .carrier)
  : Id (R .carrier) (R .neg (R .add a b)) (R .add (R .neg a) (R .neg b))
  ≔ concat (R .carrier) (R .neg (R .add a b)) (R .add (R .neg b) (R .neg a)) (R .add (R .neg a) (R .neg b))
      (ag_inv_mul (ring_additive_group R) a b) (ring_add_comm R (R .neg b) (R .neg a))

{` Linear maps Kᵐ → Kⁿ on coordinate vectors, and trivial kernel. `}
def LinearFinMap (R : AbstractRing) (m n : Nat) (f : (Fin m → R .carrier) → Fin n → R .carrier) : Type
  ≔ (a : R .carrier) (x y : Fin m → R .carrier) (t : Fin n)
    → Id (R .carrier) (f (s ↦ R .add (x s) (R .mul a (y s))) t) (R .add (f x t) (R .mul a (f y t)))

def TrivialKernel (R : AbstractRing) (m n : Nat) (f : (Fin m → R .carrier) → Fin n → R .carrier) : Type
  ≔ (x : Fin m → R .carrier) → ((t : Fin n) → Id (R .carrier) (f x t) (R .zero))
    → (s : Fin m) → Id (R .carrier) (x s) (R .zero)

{` (y, 0) and the last standard basis vector of Kᵐ⁺¹. `}
def vec_extend_zero (R : AbstractRing) (m : Nat) (y : Fin m → R .carrier) : Fin (suc. m) → R .carrier
  ≔ [ inl. s ↦ y s | inr. _ ↦ R .zero ]

def vec_last_unit (R : AbstractRing) (m : Nat) : Fin (suc. m) → R .carrier ≔ [ inl. _ ↦ R .zero | inr. _ ↦ R .one ]

def ring_zero_add_mul_zero (R : AbstractRing) (a : R .carrier)
  : Id (R .carrier) (R .zero) (R .add (R .zero) (R .mul a (R .zero)))
  ≔ inverse (R .carrier) (R .add (R .zero) (R .mul a (R .zero))) (R .zero)
      (concat (R .carrier) (R .add (R .zero) (R .mul a (R .zero))) (R .add (R .zero) (R .zero)) (R .zero)
        (refl (R .add (R .zero)) (ring_mul_zero_right R a)) (R .add_laws .unit_right (R .zero)))

def vec_extend_zero_lin (R : AbstractRing) (m : Nat) (a : R .carrier) (x y : Fin m → R .carrier)
  : Id (Fin (suc. m) → R .carrier) (vec_extend_zero R m (s ↦ R .add (x s) (R .mul a (y s))))
      (s ↦ R .add (vec_extend_zero R m x s) (R .mul a (vec_extend_zero R m y s)))
  ≔ funext (Fin (suc. m)) (_ ↦ R .carrier) (vec_extend_zero R m (s ↦ R .add (x s) (R .mul a (y s))))
      (s ↦ R .add (vec_extend_zero R m x s) (R .mul a (vec_extend_zero R m y s)))
      [ inl. s ↦ refl (R .add (x s) (R .mul a (y s))) | inr. _ ↦ ring_zero_add_mul_zero R a ]

{` The reduced map Kᵐ → Kⁿ: y ↦ f(y, 0) − (f(y, 0)_j c) v with coordinate j
   deleted, where v = f(e_last) and c is an inverse of v_j. `}
def linear_le_reduce (R : AbstractRing) (m n : Nat) (f : (Fin (suc. m) → R .carrier) → Fin (suc. n) → R .carrier)
  (j : Fin (suc. n)) (c : R .carrier) (y : Fin m → R .carrier) (k : Fin n) : R .carrier
  ≔ let F ≔ f (vec_extend_zero R m y) in let v ≔ f (vec_last_unit R m) in
    R .add (F (fin_skip n j k)) (R .neg (R .mul (R .mul (F j) c) (v (fin_skip n j k))))

{` (p + a q) − ((P + a Q) c) w = (p − (P c) w) + a (q − (Q c) w). `}
def linear_le_algebra (R : AbstractRing) (a c p q P Q w : R .carrier)
  : Id (R .carrier)
      (R .add (R .add p (R .mul a q)) (R .neg (R .mul (R .mul (R .add P (R .mul a Q)) c) w)))
      (R .add (R .add p (R .neg (R .mul (R .mul P c) w))) (R .mul a (R .add q (R .neg (R .mul (R .mul Q c) w)))))
  ≔ let S ≔ R .carrier in let ad ≔ R .add in let mu ≔ R .mul in let ng ≔ R .neg in
    let X ≔ mu (mu P c) w in let Y ≔ mu (mu Q c) w in
    let aY ≔ mu (mu (mu a Q) c) w in
    let e1 : Id S (mu (mu (ad P (mu a Q)) c) w) (ad X aY)
      ≔ concat S (mu (mu (ad P (mu a Q)) c) w) (mu (ad (mu P c) (mu (mu a Q) c)) w) (ad X aY)
          (refl ((u ↦ mu u w) : S → S) (ring_rdistr R P (mu a Q) c))
          (ring_rdistr R (mu P c) (mu (mu a Q) c) w) in
    let e2 : Id S aY (mu a Y)
      ≔ concat S aY (mu (mu a (mu Q c)) w) (mu a Y)
          (refl ((u ↦ mu u w) : S → S) (inverse S (mu a (mu Q c)) (mu (mu a Q) c) (ring_mul_assoc R a Q c)))
          (inverse S (mu a Y) (mu (mu a (mu Q c)) w) (ring_mul_assoc R a (mu Q c) w)) in
    calc
      ad (ad p (mu a q)) (ng (mu (mu (ad P (mu a Q)) c) w)) = ad (ad p (mu a q)) (ng (ad X aY))
        by refl ((u ↦ ad (ad p (mu a q)) (ng u)) : S → S) e1
      = ad (ad p (mu a q)) (ad (ng X) (ng aY)) by refl (ad (ad p (mu a q))) (ring_neg_add_split R X aY)
      = ad (ad p (ng X)) (ad (mu a q) (ng aY)) by ring_add_interchange R p (mu a q) (ng X) (ng aY)
      = ad (ad p (ng X)) (ad (mu a q) (mu a (ng Y)))
        by refl ((u ↦ ad (ad p (ng X)) (ad (mu a q) u)) : S → S)
          (concat S (ng aY) (ng (mu a Y)) (mu a (ng Y)) (refl ng e2)
            (inverse S (mu a (ng Y)) (ng (mu a Y)) (ring_mul_neg_right R a Y)))
      = ad (ad p (ng X)) (mu a (ad q (ng Y)))
        by refl (ad (ad p (ng X))) (inverse S (mu a (ad q (ng Y))) (ad (mu a q) (mu a (ng Y))) (ring_ldistr R a q (ng Y))) ∎

def linear_le_reduce_lin (R : AbstractRing) (m n : Nat) (f : (Fin (suc. m) → R .carrier) → Fin (suc. n) → R .carrier)
  (lin : LinearFinMap R (suc. m) (suc. n) f) (j : Fin (suc. n)) (c : R .carrier)
  : LinearFinMap R m n (linear_le_reduce R m n f j c)
  ≔ a x y k ↦
    let S ≔ R .carrier in
    let ext ≔ vec_extend_zero R m in
    let v ≔ f (vec_last_unit R m) in
    let u ≔ fin_skip n j k in
    let el : (t : Fin (suc. n)) → Id S (f (ext (s ↦ R .add (x s) (R .mul a (y s)))) t)
                                        (R .add (f (ext x) t) (R .mul a (f (ext y) t)))
      ≔ t ↦ concat S (f (ext (s ↦ R .add (x s) (R .mul a (y s)))) t)
              (f (s ↦ R .add (ext x s) (R .mul a (ext y s))) t)
              (R .add (f (ext x) t) (R .mul a (f (ext y) t)))
              (refl ((w ↦ f w t) : (Fin (suc. m) → S) → S) (vec_extend_zero_lin R m a x y))
              (lin a (ext x) (ext y) t) in
    concat S (linear_le_reduce R m n f j c (s ↦ R .add (x s) (R .mul a (y s))) k)
      (R .add (R .add (f (ext x) u) (R .mul a (f (ext y) u)))
        (R .neg (R .mul (R .mul (R .add (f (ext x) j) (R .mul a (f (ext y) j))) c) (v u))))
      (R .add (linear_le_reduce R m n f j c x k) (R .mul a (linear_le_reduce R m n f j c y k)))
      (refl ((p P ↦ R .add p (R .neg (R .mul (R .mul P c) (v u)))) : S → S → S) (el u) (el j))
      (linear_le_algebra R a c (f (ext x) u) (f (ext y) u) (f (ext x) j) (f (ext y) j) (v u))

def linear_le_reduce_ker (R : AbstractRing) (m n : Nat) (f : (Fin (suc. m) → R .carrier) → Fin (suc. n) → R .carrier)
  (lin : LinearFinMap R (suc. m) (suc. n) f) (ker : TrivialKernel R (suc. m) (suc. n) f)
  (j : Fin (suc. n)) (c : R .carrier) (hc : Id (R .carrier) (R .mul c (f (vec_last_unit R m) j)) (R .one))
  : TrivialKernel R m n (linear_le_reduce R m n f j c)
  ≔ y hy s ↦
    let S ≔ R .carrier in let ad ≔ R .add in let mu ≔ R .mul in let ng ≔ R .neg in
    let F ≔ f (vec_extend_zero R m y) in
    let v ≔ f (vec_last_unit R m) in
    let μ ≔ mu (F j) c in
    let x : Fin (suc. m) → S ≔ t ↦ ad (vec_extend_zero R m y t) (mu (ng μ) (vec_last_unit R m t)) in
    let fx : (u : Fin (suc. n)) → Id S (f x u) (ad (F u) (ng (mu μ (v u))))
      ≔ u ↦ concat S (f x u) (ad (F u) (mu (ng μ) (v u))) (ad (F u) (ng (mu μ (v u))))
              (lin (ng μ) (vec_extend_zero R m y) (vec_last_unit R m) u)
              (refl (ad (F u)) (ring_mul_neg_left R μ (v u))) in
    let μv : Id S (mu μ (v j)) (F j)
      ≔ calc
          mu μ (v j) = mu (F j) (mu c (v j)) by inverse S (mu (F j) (mu c (v j))) (mu μ (v j)) (ring_mul_assoc R (F j) c (v j))
          = mu (F j) (R .one) by refl (mu (F j)) hc
          = F j by ring_mul_one_right R (F j) ∎ in
    let atj : Id S (f x j) (R .zero)
      ≔ calc
          f x j = ad (F j) (ng (mu μ (v j))) by fx j
          = ad (F j) (ng (F j)) by refl ((u ↦ ad (F j) (ng u)) : S → S) μv
          = R .zero by R .add_laws .inv_right (F j) ∎ in
    let all : (u : Fin (suc. n)) → Id S (f x u) (R .zero)
      ≔ fin_skip_cover S (R .zero) n j (f x) atj
          (k ↦ concat S (f x (fin_skip n j k)) (linear_le_reduce R m n f j c y k) (R .zero) (fx (fin_skip n j k)) (hy k)) in
    calc
      y s = ad (y s) (R .zero) by inverse S (ad (y s) (R .zero)) (y s) (R .add_laws .unit_right (y s))
      = ad (y s) (mu (ng μ) (R .zero))
        by refl (ad (y s)) (inverse S (mu (ng μ) (R .zero)) (R .zero) (ring_mul_zero_right R (ng μ)))
      = R .zero by ker x all (inl. s) ∎

{` The inductive step: if m ≰ n, every coordinate of f(e_last) is zero, so
   e_last = 0, i.e. 1 = 0. `}
def linear_le_contra (K : Field) (n m : Nat) (f : (Fin (suc. m) → K .fst .carrier) → Fin (suc. n) → K .fst .carrier)
  (lin : LinearFinMap (K .fst) (suc. m) (suc. n) f) (ker : TrivialKernel (K .fst) (suc. m) (suc. n) f)
  (ih : (g : (Fin m → K .fst .carrier) → Fin n → K .fst .carrier)
        → LinearFinMap (K .fst) m n g → TrivialKernel (K .fst) m n g → Le m n)
  (no : Not (Le m n)) : Empty
  ≔ let R ≔ K .fst in
    let v ≔ f (vec_last_unit R m) in
    ring_one_ne_zero R (K .snd .fst .snd)
      (ker (vec_last_unit R m)
        (t ↦ field_non_invertible_zero R (K .snd) (v t)
           (inv ↦ mere_rec (InverseWitness R (v t)) Empty empty_prop
              (w ↦ no (ih (linear_le_reduce R m n f t (w .fst))
                         (linear_le_reduce_lin R m n f lin t (w .fst))
                         (linear_le_reduce_ker R m n f lin ker t (w .fst) (w .snd .snd))))
              inv))
        (inr. star.))

{` An injective (trivial-kernel) linear map Kᵐ → Kⁿ over a field forces m ≤ n. `}
def field_injective_linear_le (K : Field) (n m : Nat) (f : (Fin m → K .fst .carrier) → Fin n → K .fst .carrier)
  (lin : LinearFinMap (K .fst) m n f) (ker : TrivialKernel (K .fst) m n f) : Le m n
  ≔ match m [
  | zero. ↦ star.
  | suc. m ↦ match n [
    | zero. ↦ match ring_one_ne_zero (K .fst) (K .snd .fst .snd) (ker (vec_last_unit (K .fst) m) (t ↦ match t [ ]) (inr. star.)) [ ]
    | suc. n ↦ match le_decidable m n [
      | inl. yes ↦ yes
      | inr. no ↦ match linear_le_contra K n m f lin ker (field_injective_linear_le K n m) no [ ] ] ] ]

{` Linear maps of standard modules are LinearFinMaps; a map with a linear
   left inverse has trivial kernel. `}
def linear_map_fin_lin (R : AbstractRing) (p q : Nat) (h : LinearMap R (standard_module R p) (standard_module R q))
  : LinearFinMap R p q (h .fst .fst)
  ≔ a x y t ↦
    let Kp ≔ standard_module R p in let Kq ≔ standard_module R q in let hf ≔ h .fst .fst in
    refl ((w ↦ w t) : (Fin q → R .carrier) → R .carrier)
      (concat (Fin q → R .carrier) (hf (Kp .add x (Kp .smul a y))) (Kq .add (hf x) (hf (Kp .smul a y)))
        (Kq .add (hf x) (Kq .smul a (hf y)))
        (h .fst .snd x (Kp .smul a y)) (refl (Kq .add (hf x)) (h .snd a y)))

def linear_left_inverse_ker (R : AbstractRing) (p q : Nat)
  (h : LinearMap R (standard_module R p) (standard_module R q)) (g : LinearMap R (standard_module R q) (standard_module R p))
  (gh : (a : Fin p → R .carrier) → Id (Fin p → R .carrier) (g .fst .fst (h .fst .fst a)) a)
  : TrivialKernel R p q (h .fst .fst)
  ≔ x hx s ↦
    let S ≔ R .carrier in let Kp ≔ standard_module R p in let Kq ≔ standard_module R q in
    let z : Id (Fin q → S) (h .fst .fst x) (_ ↦ R .zero) ≔ funext (Fin q) (_ ↦ S) (h .fst .fst x) (_ ↦ R .zero) hx in
    let e : Id (Fin p → S) x (_ ↦ R .zero)
      ≔ calc
          x = g .fst .fst (h .fst .fst x) by inverse (Fin p → S) (g .fst .fst (h .fst .fst x)) x (gh x)
          = g .fst .fst (_ ↦ R .zero) by refl (g .fst .fst) z
          = (_ ↦ R .zero) by abstract_hom_preserves_unit (module_group R Kq) (module_group R Kp) (g .fst .fst) (g .fst .snd) ∎ in
    refl ((w ↦ w s) : (Fin p → S) → S) e

{` Uniqueness of dimension over any field (dimension_unique of module 1413
   with field_injective_linear_le in place of the trace argument). `}
def field_dimension_unique (K : Field) (V : VectorSpace K) (n m : Nat)
  (hn : HasDimension K n V) (hm : HasDimension K m V) : Id Nat n m
  ≔ let R ≔ K .fst in
    let Kn ≔ standard_module R n in let Km ≔ standard_module R m in
    mere_rec (Σ (Fin n → V .carrier) (i ↦ IsFreeVectorSpace K (standard_set n) V i)) (Id Nat n m) (nat_set n m)
      (bb ↦
        mere_rec (Σ (Fin m → V .carrier) (i ↦ IsFreeVectorSpace K (standard_set m) V i)) (Id Nat n m)
          (nat_set n m)
          (cc ↦
            let b ≔ bb .fst in let hb ≔ bb .snd in let c ≔ cc .fst in let hc ≔ cc .snd in
            let δb ≔ basis_coordinates R n V b hb .fst in
            let δc ≔ basis_coordinates R m V c hc .fst in
            let f ≔ linear_compose R Kn V Km (standard_module_extension R n V b) δc in
            let g ≔ linear_compose R Km V Kn (standard_module_extension R m V c) δb in
            let gf : (a : Fin n → R .carrier) → Id (Fin n → R .carrier) (g .fst .fst (f .fst .fst a)) a
              ≔ a ↦ concat (Fin n → R .carrier) (g .fst .fst (f .fst .fst a))
                  (δb .fst .fst (fin_linear_combination R V n a b)) a
                  (refl (δb .fst .fst)
                    (inverse (V .carrier) (fin_linear_combination R V n a b)
                      (fin_linear_combination R V m (δc .fst .fst (fin_linear_combination R V n a b)) c)
                      (basis_expansion R m V c hc (fin_linear_combination R V n a b))))
                  (basis_coordinates_lc R n V b hb a) in
            let fg : (a : Fin m → R .carrier) → Id (Fin m → R .carrier) (f .fst .fst (g .fst .fst a)) a
              ≔ a ↦ concat (Fin m → R .carrier) (f .fst .fst (g .fst .fst a))
                  (δc .fst .fst (fin_linear_combination R V m a c)) a
                  (refl (δc .fst .fst)
                    (inverse (V .carrier) (fin_linear_combination R V m a c)
                      (fin_linear_combination R V n (δb .fst .fst (fin_linear_combination R V m a c)) b)
                      (basis_expansion R n V b hb (fin_linear_combination R V m a c))))
                  (basis_coordinates_lc R m V c hc a) in
            le_antisym n m
              (field_injective_linear_le K m n (f .fst .fst) (linear_map_fin_lin R n m f) (linear_left_inverse_ker R n m f g gf))
              (field_injective_linear_le K n m (g .fst .fst) (linear_map_fin_lin R m n g) (linear_left_inverse_ker R m n g f fg)))
          hm)
      hn

{` The hypothesis of extension_degree (module 1503) holds for every field. `}
def field_dimension_invariance (k : Field) : DimensionInvariance k
  ≔ V n m hn hm ↦ field_dimension_unique k V n m hn hm

{` defn:degree-field-extension: [K : k] of a finite extension, no hypotheses. `}
def field_extension_degree (k : Field) (E : FieldExt k) (h : IsFiniteExtension k E) : Nat
  ≔ extension_degree k E (field_dimension_invariance k) h

def field_extension_degree_spec (k : Field) (E : FieldExt k) (h : IsFiniteExtension k E)
  : ExtensionHasDegree k E (field_extension_degree k E h)
  ≔ extension_degree_spec k E (field_dimension_invariance k) h

{` The degree is the unique n with [K : k] = n. `}
def field_extension_degree_unique (k : Field) (E : FieldExt k) (h : IsFiniteExtension k E) (n : Nat)
  (d : ExtensionHasDegree k E n) : Id Nat (field_extension_degree k E h) n
  ≔ field_dimension_unique k (field_ext_vector_space k E) (field_extension_degree k E h) n
      (field_extension_degree_spec k E h) d

{` Litmus in characteristic 2, where the trace argument of module 1413 gives
   nothing: [𝔽₂ : 𝔽₂] = 1 by computation, and 𝔽₂ is not 2-dimensional over itself. `}
def f2_identity_extension_degree : Id Nat (field_extension_degree f2_field (identity_extension f2_field)
    (identity_extension_finite f2_field)) 1
  ≔ refl (1 : Nat)

def f2_not_two_dimensional (h : ExtensionHasDegree f2_field (identity_extension f2_field) 2) : Empty
  ≔ nat_encode 2 1 (field_dimension_unique f2_field (field_ext_vector_space f2_field (identity_extension f2_field)) 2 1
      h (identity_extension_degree_one f2_field))
