export "1410-linear-spans"

{` Chapter 14 uses "dim V" (thm:GramSchmidt, thm:EuclideanNormalization)
   and the equivalence ES ≃ Σ_n ES_n (geometry.tex 132-133), which need
   that the dimension of a finite dimensional vector space is unique. Proof
   by the trace: linear maps f : Kⁿ → Kᵐ, g : Kᵐ → Kⁿ inverse to each
   other give n·1 = Σ_i (g f e_i)_i = Σ_i Σ_j f(e_i)_j g(e_j)_i
   = Σ_j Σ_i g(e_j)_i f(e_i)_j = Σ_j (f g e_j)_j = m·1 in any commutative
   ring; in a EuclideanField (ordered, so of characteristic 0) this gives
   n = m. Consequently OS ≃ Σ_n OS_n. `}

def fin_delta_diagonal (R : AbstractRing) (n : Nat) (i : Fin n) : Id (R .carrier) (fin_delta R n i i) (R .one)
  ≔ match n [
  | zero. ↦ match i [ ]
  | suc. n ↦ match i [ inl. i ↦ fin_delta_diagonal R n i | inr. _ ↦ refl (R .one) ] ]

{` n·1 = Σ_{i < n} 1. `}
def ring_of_nat (R : AbstractRing) (n : Nat) : R .carrier
  ≔ fin_module_sum R (ring_self_module R) n (_ ↦ R .one)

{` Interchange of finite double sums. `}
def fin_sum_swap (R : AbstractRing) (W : RingModule R) (n m : Nat) (x : Fin n → Fin m → W .carrier)
  : Id (W .carrier) (fin_module_sum R W n (i ↦ fin_module_sum R W m (j ↦ x i j)))
      (fin_module_sum R W m (j ↦ fin_module_sum R W n (i ↦ x i j)))
  ≔ match n [
  | zero. ↦ inverse (W .carrier) (fin_module_sum R W m (_ ↦ W .zero)) (W .zero)
      (fin_module_sum_zero R W m (_ ↦ W .zero) (_ ↦ refl (W .zero)))
  | suc. n ↦
    let T ≔ W .carrier in
    let last ≔ fin_module_sum R W m (j ↦ x (inr. star.) j) in
    concat T (W .add (fin_module_sum R W n (i ↦ fin_module_sum R W m (j ↦ x (inl. i) j))) last)
      (W .add (fin_module_sum R W m (j ↦ fin_module_sum R W n (i ↦ x (inl. i) j))) last)
      (fin_module_sum R W m (j ↦ W .add (fin_module_sum R W n (i ↦ x (inl. i) j)) (x (inr. star.) j)))
      (refl ((y ↦ W .add y last) : T → T) (fin_sum_swap R W n m (i ↦ x (inl. i))))
      (inverse T (fin_module_sum R W m (j ↦ W .add (fin_module_sum R W n (i ↦ x (inl. i) j)) (x (inr. star.) j)))
        (W .add (fin_module_sum R W m (j ↦ fin_module_sum R W n (i ↦ x (inl. i) j))) last)
        (fin_module_sum_add R W m (j ↦ fin_module_sum R W n (i ↦ x (inl. i) j)) (j ↦ x (inr. star.) j))) ]

{` A linear map h : Rᵖ → R^q is given by its matrix: (h a)_k = Σ_j a_j h(e_j)_k. `}
def linear_map_matrix (R : AbstractRing) (p q : Nat) (h : LinearMap R (standard_module R p) (standard_module R q))
  (a : Fin p → R .carrier) (k : Fin q)
  : Id (R .carrier) (h .fst .fst a k)
      (fin_module_sum R (ring_self_module R) p (j ↦ R .mul (a j) (h .fst .fst (standard_basis R p j) k)))
  ≔ let Kp ≔ standard_module R p in let Kq ≔ standard_module R q in let hf ≔ h .fst .fst in
    let F ≔ Fin q → R .carrier in
    let e : Id F (hf a) (fin_module_sum R Kq p (j ↦ Kq .smul (a j) (hf (standard_basis R p j))))
      ≔ calc
          hf a = hf (fin_module_sum R Kp p (j ↦ Kp .smul (a j) (standard_basis R p j)))
            by refl hf (inverse (Fin p → R .carrier)
                 (fin_module_sum R Kp p (j ↦ Kp .smul (a j) (standard_basis R p j))) a (standard_decomposition R p a))
          = fin_module_sum R Kq p (j ↦ hf (Kp .smul (a j) (standard_basis R p j)))
            by linear_map_fin_sum R Kp Kq h p (j ↦ Kp .smul (a j) (standard_basis R p j))
          = fin_module_sum R Kq p (j ↦ Kq .smul (a j) (hf (standard_basis R p j)))
            by refl (fin_module_sum R Kq p)
              (funext (Fin p) (_ ↦ F) (j ↦ hf (Kp .smul (a j) (standard_basis R p j)))
                (j ↦ Kq .smul (a j) (hf (standard_basis R p j))) (j ↦ h .snd (a j) (standard_basis R p j))) ∎ in
    concat (R .carrier) (hf a k) (fin_module_sum R Kq p (j ↦ Kq .smul (a j) (hf (standard_basis R p j))) k)
      (fin_module_sum R (ring_self_module R) p (j ↦ R .mul (a j) (hf (standard_basis R p j) k)))
      (refl ((y ↦ y k) : F → R .carrier) e)
      (standard_module_sum_eval R q p (j ↦ Kq .smul (a j) (hf (standard_basis R p j))) k)

{` The trace argument: n·1 = m·1. `}
def trace_count_equal (R : AbstractRing) (hc : IsCommutativeRing R) (n m : Nat)
  (f : LinearMap R (standard_module R n) (standard_module R m)) (g : LinearMap R (standard_module R m) (standard_module R n))
  (gf : (a : Fin n → R .carrier) → Id (Fin n → R .carrier) (g .fst .fst (f .fst .fst a)) a)
  (fg : (a : Fin m → R .carrier) → Id (Fin m → R .carrier) (f .fst .fst (g .fst .fst a)) a)
  : Id (R .carrier) (ring_of_nat R n) (ring_of_nat R m)
  ≔ let S ≔ R .carrier in let M ≔ ring_self_module R in
    let ff ≔ f .fst .fst in let gg ≔ g .fst .fst in
    let en ≔ standard_basis R n in let em ≔ standard_basis R m in
    calc
      ring_of_nat R n = fin_module_sum R M n (i ↦ gg (ff (en i)) i)
        by refl (fin_module_sum R M n)
          (funext (Fin n) (_ ↦ S) (_ ↦ R .one) (i ↦ gg (ff (en i)) i)
            (i ↦ inverse S (gg (ff (en i)) i) (R .one)
              (concat S (gg (ff (en i)) i) (en i i) (R .one)
                (refl ((y ↦ y i) : (Fin n → S) → S) (gf (en i))) (fin_delta_diagonal R n i))))
      = fin_module_sum R M n (i ↦ fin_module_sum R M m (j ↦ R .mul (ff (en i) j) (gg (em j) i)))
        by refl (fin_module_sum R M n)
          (funext (Fin n) (_ ↦ S) (i ↦ gg (ff (en i)) i)
            (i ↦ fin_module_sum R M m (j ↦ R .mul (ff (en i) j) (gg (em j) i)))
            (i ↦ linear_map_matrix R m n g (ff (en i)) i))
      = fin_module_sum R M m (j ↦ fin_module_sum R M n (i ↦ R .mul (ff (en i) j) (gg (em j) i)))
        by fin_sum_swap R M n m (i j ↦ R .mul (ff (en i) j) (gg (em j) i))
      = fin_module_sum R M m (j ↦ fin_module_sum R M n (i ↦ R .mul (gg (em j) i) (ff (en i) j)))
        by refl (fin_module_sum R M m)
          (funext (Fin m) (_ ↦ S) (j ↦ fin_module_sum R M n (i ↦ R .mul (ff (en i) j) (gg (em j) i)))
            (j ↦ fin_module_sum R M n (i ↦ R .mul (gg (em j) i) (ff (en i) j)))
            (j ↦ refl (fin_module_sum R M n)
              (funext (Fin n) (_ ↦ S) (i ↦ R .mul (ff (en i) j) (gg (em j) i)) (i ↦ R .mul (gg (em j) i) (ff (en i) j))
                (i ↦ hc (ff (en i) j) (gg (em j) i)))))
      = fin_module_sum R M m (j ↦ ff (gg (em j)) j)
        by refl (fin_module_sum R M m)
          (funext (Fin m) (_ ↦ S) (j ↦ fin_module_sum R M n (i ↦ R .mul (gg (em j) i) (ff (en i) j)))
            (j ↦ ff (gg (em j)) j)
            (j ↦ inverse S (ff (gg (em j)) j) (fin_module_sum R M n (i ↦ R .mul (gg (em j) i) (ff (en i) j)))
              (linear_map_matrix R n m f (gg (em j)) j)))
      = ring_of_nat R m
        by refl (fin_module_sum R M m)
          (funext (Fin m) (_ ↦ S) (j ↦ ff (gg (em j)) j) (_ ↦ R .one)
            (j ↦ concat S (ff (gg (em j)) j) (em j j) (R .one)
              (refl ((y ↦ y j) : (Fin m → S) → S) (fg (em j))) (fin_delta_diagonal R m j))) ∎

{` Characteristic 0 of an ordered field: n·1 ≥ 0, (n+1)·1 ≠ 0, and n·1 = m·1
   implies n = m. `}
def ef_nat_nonneg (K : EuclideanField) (n : Nat) : K .nonneg (ring_of_nat (K .field .fst) n)
  ≔ match n [
  | zero. ↦ ef_zero_nonneg K
  | suc. n ↦ K .nonneg_add (ring_of_nat (K .field .fst) n) (K .field .fst .one) (ef_nat_nonneg K n) (ef_one_nonneg K) ]

def ef_nat_succ_nonzero (K : EuclideanField) (n : Nat)
  (p : Id (ef_carrier K) (ring_of_nat (K .field .fst) (suc. n)) (K .field .fst .zero)) : Empty
  ≔ let R ≔ K .field .fst in
    ring_one_ne_zero R (ef_non_trivial K)
      (ef_sum_zero_right K (ring_of_nat R n) (R .one) (ef_nat_nonneg K n) (ef_one_nonneg K) p)

def ef_nat_injective (K : EuclideanField) (n m : Nat)
  (p : Id (ef_carrier K) (ring_of_nat (K .field .fst) n) (ring_of_nat (K .field .fst) m)) : Id Nat n m
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in
    match n, m [
    | zero., zero. ↦ refl (zero. : Nat)
    | zero., suc. m ↦ match ef_nat_succ_nonzero K m (inverse S (R .zero) (ring_of_nat R (suc. m)) p) [ ]
    | suc. n, zero. ↦ match ef_nat_succ_nonzero K n p [ ]
    | suc. n, suc. m ↦
      refl ((k ↦ suc. k) : Nat → Nat)
        (ef_nat_injective K n m (ag_cancel_right (ring_additive_group R) (R .one) (ring_of_nat R n) (ring_of_nat R m) p)) ]

{` Uniqueness of dimension. `}
def dimension_unique (K : EuclideanField) (V : VectorSpace (K .field)) (n m : Nat)
  (hn : HasDimension (K .field) n V) (hm : HasDimension (K .field) m V) : Id Nat n m
  ≔ let R ≔ K .field .fst in
    let Kn ≔ standard_module R n in let Km ≔ standard_module R m in
    mere_rec (Σ (Fin n → V .carrier) (i ↦ IsFreeVectorSpace (K .field) (standard_set n) V i)) (Id Nat n m) (nat_set n m)
      (bb ↦
        mere_rec (Σ (Fin m → V .carrier) (i ↦ IsFreeVectorSpace (K .field) (standard_set m) V i)) (Id Nat n m)
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
            ef_nat_injective K n m (trace_count_equal R (ef_commutative K) n m f g gf fg))
          hm)
      hn

def finite_dimension_prop (K : EuclideanField) (V : VectorSpace (K .field))
  : isProp (Σ Nat (n ↦ HasDimension (K .field) n V))
  ≔ x y ↦
    subtype_equal Nat (n ↦ HasDimension (K .field) n V)
      (n ↦ mere_isprop (Σ (Fin n → V .carrier) (i ↦ IsFreeVectorSpace (K .field) (standard_set n) V i)))
      x y (dimension_unique K V (x .fst) (y .fst) (x .snd) (y .snd))

{` dim V for a finite dimensional V. `}
def vector_space_dimension_data (K : EuclideanField) (V : VectorSpace (K .field)) (h : IsFiniteDimensional (K .field) V)
  : Σ Nat (n ↦ HasDimension (K .field) n V)
  ≔ mere_rec (Σ Nat (n ↦ HasDimension (K .field) n V)) (Σ Nat (n ↦ HasDimension (K .field) n V))
      (finite_dimension_prop K V) (x ↦ x) h

def ip_space_dimension (K : EuclideanField) (V : InnerProductSpace K) : Nat
  ≔ vector_space_dimension_data K (V .space) (V .finite) .fst

{` OS ≃ Σ_n OS_n (map: forget n). `}
def inner_product_space_dim_sum_equiv (K : EuclideanField)
  : Equiv (Σ Nat (n ↦ InnerProductSpaceDim K n)) (InnerProductSpace K)
  ≔ let OS ≔ InnerProductSpace K in
    let A ≔ Σ Nat (n ↦ InnerProductSpaceDim K n) in
    let back : OS → A
      ≔ V ↦ let d ≔ vector_space_dimension_data K (V .space) (V .finite) in (d .fst, (V, d .snd)) in
    quasi_inverse_equiv A OS (x ↦ x .snd .fst) back
      (x ↦
        let V ≔ x .snd .fst in
        let D ≔ Σ Nat (n ↦ HasDimension (K .field) n (V .space)) in
        refl ((e ↦ (e .fst, (V, e .snd))) : D → A)
          (finite_dimension_prop K (V .space) (vector_space_dimension_data K (V .space) (V .finite)) (x .fst, x .snd .snd)))
      (V ↦ refl V)

{` Litmus: dim 𝕍ⁿ = n. `}
def standard_ip_space_dimension (K : EuclideanField) (n : Nat)
  : Id Nat (ip_space_dimension K (standard_inner_product_space K n)) n
  ≔ dimension_unique K (standard_vector_space (K .field) n) (ip_space_dimension K (standard_inner_product_space K n)) n
      (vector_space_dimension_data K (standard_vector_space (K .field) n) (standard_inner_product_space K n .finite) .snd)
      (standard_has_dimension K n)
