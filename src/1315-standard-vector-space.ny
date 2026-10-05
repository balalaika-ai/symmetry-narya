export "1302-vector-spaces"
export "1310-integer-ring"
export "430-pointwise-abstract-groups"

{` Chapter 13 (fields.tex 1295-1301), litmus for the definitions of free
   and n-dimensional vector spaces: the standard vector space Kⁿ (functions
   Fin n → K with pointwise operations) is free on Fin n with the standard
   basis e_s(t) = δ(s, t), hence an n-dimensional K-vector space. The proof
   works for modules over any abstract ring R. The extension of
   j : Fin n → W is v ↦ Σ_s v(s) j(s); uniqueness uses the decomposition
   v = Σ_s v(s) e_s. Finite sums Σ_(s : Fin n) in a module are defined by
   recursion on n (Fin (n+1) = Fin n + 1, the new element last). `}

def fin_module_sum (R : AbstractRing) (W : RingModule R) (n : Nat) (f : Fin n → W .carrier) : W .carrier
  ≔ match n [
  | zero. ↦ W .zero
  | suc. n ↦ W .add (fin_module_sum R W n (s ↦ f (inl. s))) (f (inr. star.)) ]

def fin_module_sum_zero (R : AbstractRing) (W : RingModule R) (n : Nat) (f : Fin n → W .carrier)
  (h : (s : Fin n) → Id (W .carrier) (f s) (W .zero))
  : Id (W .carrier) (fin_module_sum R W n f) (W .zero)
  ≔ match n [
  | zero. ↦ refl (W .zero)
  | suc. n ↦ calc
      W .add (fin_module_sum R W n (s ↦ f (inl. s))) (f (inr. star.)) = W .add (W .zero) (W .zero)
        by refl (W .add) (fin_module_sum_zero R W n (s ↦ f (inl. s)) (s ↦ h (inl. s))) (h (inr. star.))
      = W .zero by W .add_laws .unit_right (W .zero) ∎ ]

def fin_module_sum_add (R : AbstractRing) (W : RingModule R) (n : Nat) (f g : Fin n → W .carrier)
  : Id (W .carrier) (fin_module_sum R W n (s ↦ W .add (f s) (g s)))
      (W .add (fin_module_sum R W n f) (fin_module_sum R W n g))
  ≔ match n [
  | zero. ↦ inverse (W .carrier) (W .add (W .zero) (W .zero)) (W .zero) (W .add_laws .unit_right (W .zero))
  | suc. n ↦
    let F ≔ fin_module_sum R W n (s ↦ f (inl. s)) in
    let G ≔ fin_module_sum R W n (s ↦ g (inl. s)) in
    calc
      W .add (fin_module_sum R W n (s ↦ W .add (f (inl. s)) (g (inl. s)))) (W .add (f (inr. star.)) (g (inr. star.)))
      = W .add (W .add F G) (W .add (f (inr. star.)) (g (inr. star.)))
        by refl ((x ↦ W .add x (W .add (f (inr. star.)) (g (inr. star.)))) : W .carrier → W .carrier)
          (fin_module_sum_add R W n (s ↦ f (inl. s)) (s ↦ g (inl. s)))
      = W .add (W .add F (f (inr. star.))) (W .add G (g (inr. star.)))
        by abstract_abelian_interchange (module_group R W) (module_group_abelian R W)
          F G (f (inr. star.)) (g (inr. star.)) ∎ ]

def fin_module_sum_smul (R : AbstractRing) (W : RingModule R) (n : Nat) (a : R .carrier) (f : Fin n → W .carrier)
  : Id (W .carrier) (fin_module_sum R W n (s ↦ W .smul a (f s))) (W .smul a (fin_module_sum R W n f))
  ≔ match n [
  | zero. ↦ inverse (W .carrier) (W .smul a (W .zero)) (W .zero) (smul_zero_vector R W a)
  | suc. n ↦ calc
      W .add (fin_module_sum R W n (s ↦ W .smul a (f (inl. s)))) (W .smul a (f (inr. star.)))
      = W .add (W .smul a (fin_module_sum R W n (s ↦ f (inl. s)))) (W .smul a (f (inr. star.)))
        by refl ((x ↦ W .add x (W .smul a (f (inr. star.)))) : W .carrier → W .carrier)
          (fin_module_sum_smul R W n a (s ↦ f (inl. s)))
      = W .smul a (W .add (fin_module_sum R W n (s ↦ f (inl. s))) (f (inr. star.)))
        by inverse (W .carrier) (W .smul a (W .add (fin_module_sum R W n (s ↦ f (inl. s))) (f (inr. star.))))
          (W .add (W .smul a (fin_module_sum R W n (s ↦ f (inl. s)))) (W .smul a (f (inr. star.))))
          (W .smul_add_vector a (fin_module_sum R W n (s ↦ f (inl. s))) (f (inr. star.))) ∎ ]

{` Linear (indeed additive) maps commute with finite sums. `}
def linear_map_fin_sum (R : AbstractRing) (V W : RingModule R) (h : LinearMap R V W) (n : Nat) (f : Fin n → V .carrier)
  : Id (W .carrier) (h .fst .fst (fin_module_sum R V n f)) (fin_module_sum R W n (s ↦ h .fst .fst (f s)))
  ≔ match n [
  | zero. ↦ abstract_hom_preserves_unit (module_group R V) (module_group R W) (h .fst .fst) (h .fst .snd)
  | suc. n ↦ calc
      h .fst .fst (V .add (fin_module_sum R V n (s ↦ f (inl. s))) (f (inr. star.)))
      = W .add (h .fst .fst (fin_module_sum R V n (s ↦ f (inl. s)))) (h .fst .fst (f (inr. star.)))
        by h .fst .snd (fin_module_sum R V n (s ↦ f (inl. s))) (f (inr. star.))
      = W .add (fin_module_sum R W n (s ↦ h .fst .fst (f (inl. s)))) (h .fst .fst (f (inr. star.)))
        by refl ((x ↦ W .add x (h .fst .fst (f (inr. star.)))) : W .carrier → W .carrier)
          (linear_map_fin_sum R V W h n (s ↦ f (inl. s))) ∎ ]

{` Rⁿ: functions Fin n → R, pointwise addition and a · v = (t ↦ a · v(t)). `}
def standard_module (R : AbstractRing) (n : Nat) : RingModule R
  ≔ let G ≔ pointwise_abstract_group (ring_additive_group R) (Fin n) in
    let S ≔ R .carrier in
    (Fin n → S, G .unit, G .mul, G .inv, G .laws,
     pointwise_abelian (ring_additive_group R) (Fin n) (ring_additive_abelian R),
     a v t ↦ R .mul a (v t),
     v ↦ funext (Fin n) (_ ↦ S) (t ↦ R .mul (R .one) (v t)) v (t ↦ ring_mul_one_left R (v t)),
     a b v ↦ funext (Fin n) (_ ↦ S) (t ↦ R .mul (R .mul a b) (v t)) (t ↦ R .mul a (R .mul b (v t)))
       (t ↦ inverse S (R .mul a (R .mul b (v t))) (R .mul (R .mul a b) (v t)) (ring_mul_assoc R a b (v t))),
     a b v ↦ funext (Fin n) (_ ↦ S) (t ↦ R .mul (R .add a b) (v t)) (t ↦ R .add (R .mul a (v t)) (R .mul b (v t)))
       (t ↦ ring_rdistr R a b (v t)),
     a v w ↦ funext (Fin n) (_ ↦ S) (t ↦ R .mul a (R .add (v t) (w t))) (t ↦ R .add (R .mul a (v t)) (R .mul a (w t)))
       (t ↦ ring_ldistr R a (v t) (w t)))

{` Kronecker delta on Fin n. `}
def fin_delta (R : AbstractRing) (n : Nat) (s t : Fin n) : R .carrier
  ≔ match n [
  | zero. ↦ match s [ ]
  | suc. n ↦ match s, t [
    | inl. s, inl. t ↦ fin_delta R n s t
    | inl. _, inr. _ ↦ R .zero
    | inr. _, inl. _ ↦ R .zero
    | inr. _, inr. _ ↦ R .one ] ]

{` The standard basis e_s = (t ↦ δ(s, t)). `}
def standard_basis (R : AbstractRing) (n : Nat) (s : Fin n) : Fin n → R .carrier ≔ t ↦ fin_delta R n s t

{` Σ_t δ(s, t) j(t) = j(s) in any module. `}
def fin_delta_sum_right (R : AbstractRing) (W : RingModule R) (n : Nat) (j : Fin n → W .carrier) (s : Fin n)
  : Id (W .carrier) (fin_module_sum R W n (t ↦ W .smul (fin_delta R n s t) (j t))) (j s)
  ≔ match n [
  | zero. ↦ match s [ ]
  | suc. n ↦ match s [
    | inl. s ↦ calc
        W .add (fin_module_sum R W n (t ↦ W .smul (fin_delta R n s t) (j (inl. t)))) (W .smul (R .zero) (j (inr. star.)))
        = W .add (j (inl. s)) (W .zero)
          by refl (W .add) (fin_delta_sum_right R W n (t ↦ j (inl. t)) s) (smul_zero_scalar R W (j (inr. star.)))
        = j (inl. s) by W .add_laws .unit_right (j (inl. s)) ∎
    | inr. star. ↦ calc
        W .add (fin_module_sum R W n (t ↦ W .smul (R .zero) (j (inl. t)))) (W .smul (R .one) (j (inr. star.)))
        = W .add (W .zero) (j (inr. star.))
          by refl (W .add)
            (fin_module_sum_zero R W n (t ↦ W .smul (R .zero) (j (inl. t))) (t ↦ smul_zero_scalar R W (j (inl. t))))
            (W .smul_one (j (inr. star.)))
        = j (inr. star.) by W .add_laws .unit_left (j (inr. star.)) ∎ ] ]

{` Σ_s v(s) δ(s, t) = v(t) in R. `}
def fin_delta_sum_left (R : AbstractRing) (n : Nat) (v : Fin n → R .carrier) (t : Fin n)
  : Id (R .carrier) (fin_module_sum R (ring_self_module R) n (s ↦ R .mul (v s) (fin_delta R n s t))) (v t)
  ≔ match n [
  | zero. ↦ match t [ ]
  | suc. n ↦ match t [
    | inl. t ↦ calc
        R .add (fin_module_sum R (ring_self_module R) n (s ↦ R .mul (v (inl. s)) (fin_delta R n s t)))
          (R .mul (v (inr. star.)) (R .zero))
        = R .add (v (inl. t)) (R .zero)
          by refl (R .add) (fin_delta_sum_left R n (s ↦ v (inl. s)) t) (ring_mul_zero_right R (v (inr. star.)))
        = v (inl. t) by R .add_laws .unit_right (v (inl. t)) ∎
    | inr. star. ↦ calc
        R .add (fin_module_sum R (ring_self_module R) n (s ↦ R .mul (v (inl. s)) (R .zero)))
          (R .mul (v (inr. star.)) (R .one))
        = R .add (R .zero) (v (inr. star.))
          by refl (R .add)
            (fin_module_sum_zero R (ring_self_module R) n (s ↦ R .mul (v (inl. s)) (R .zero))
              (s ↦ ring_mul_zero_right R (v (inl. s))))
            (ring_mul_one_right R (v (inr. star.)))
        = v (inr. star.) by R .add_laws .unit_left (v (inr. star.)) ∎ ] ]

{` Sums in Rⁿ are computed coordinatewise. `}
def standard_module_sum_eval (R : AbstractRing) (n m : Nat) (u : Fin m → Fin n → R .carrier) (t : Fin n)
  : Id (R .carrier) (fin_module_sum R (standard_module R n) m u t) (fin_module_sum R (ring_self_module R) m (s ↦ u s t))
  ≔ match m [
  | zero. ↦ refl (R .zero)
  | suc. m ↦ refl ((x ↦ R .add x (u (inr. star.) t)) : R .carrier → R .carrier)
      (standard_module_sum_eval R n m (s ↦ u (inl. s)) t) ]

{` v = Σ_s v(s) e_s. `}
def standard_decomposition (R : AbstractRing) (n : Nat) (v : Fin n → R .carrier)
  : Id (Fin n → R .carrier)
      (fin_module_sum R (standard_module R n) n (s ↦ standard_module R n .smul (v s) (standard_basis R n s))) v
  ≔ funext (Fin n) (_ ↦ R .carrier)
      (fin_module_sum R (standard_module R n) n (s ↦ standard_module R n .smul (v s) (standard_basis R n s))) v
      (t ↦ concat (R .carrier)
        (fin_module_sum R (standard_module R n) n (s ↦ standard_module R n .smul (v s) (standard_basis R n s)) t)
        (fin_module_sum R (ring_self_module R) n (s ↦ R .mul (v s) (fin_delta R n s t))) (v t)
        (standard_module_sum_eval R n n (s ↦ standard_module R n .smul (v s) (standard_basis R n s)) t)
        (fin_delta_sum_left R n v t))

{` The linear extension v ↦ Σ_s v(s) j(s) of j : Fin n → W. `}
def standard_module_extension (R : AbstractRing) (n : Nat) (W : RingModule R) (j : Fin n → W .carrier)
  : LinearMap R (standard_module R n) W
  ≔ let T ≔ W .carrier in
    let E : (Fin n → R .carrier) → T ≔ v ↦ fin_module_sum R W n (s ↦ W .smul (v s) (j s)) in
    ((E,
      v w ↦ concat T (E (standard_module R n .add v w))
        (fin_module_sum R W n (s ↦ W .add (W .smul (v s) (j s)) (W .smul (w s) (j s))))
        (W .add (E v) (E w))
        (refl (fin_module_sum R W n)
          (funext (Fin n) (_ ↦ T) (s ↦ W .smul (R .add (v s) (w s)) (j s))
            (s ↦ W .add (W .smul (v s) (j s)) (W .smul (w s) (j s)))
            (s ↦ W .smul_add_scalar (v s) (w s) (j s))))
        (fin_module_sum_add R W n (s ↦ W .smul (v s) (j s)) (s ↦ W .smul (w s) (j s)))),
     a v ↦ concat T (E (standard_module R n .smul a v))
       (fin_module_sum R W n (s ↦ W .smul a (W .smul (v s) (j s))))
       (W .smul a (E v))
       (refl (fin_module_sum R W n)
         (funext (Fin n) (_ ↦ T) (s ↦ W .smul (R .mul a (v s)) (j s)) (s ↦ W .smul a (W .smul (v s) (j s)))
           (s ↦ W .smul_mul a (v s) (j s))))
       (fin_module_sum_smul R W n a (s ↦ W .smul (v s) (j s))))

{` Rⁿ is free on Fin n with basis e: the extension of j is the unique
   linear map sending e_s to j(s). `}
def standard_module_free (R : AbstractRing) (n : Nat)
  : IsFreeModuleOn R (standard_set n) (standard_module R n) (standard_basis R n)
  ≔ W j ↦
    let T ≔ W .carrier in
    let V ≔ standard_module R n in
    let E ≔ LinearExtensions R (standard_set n) V (standard_basis R n) W j in
    let c : E ≔ (standard_module_extension R n W j, s ↦ fin_delta_sum_right R W n j s) in
    (center ≔ c,
     contract ≔ u ↦
       let h ≔ u .fst .fst .fst in
       subtype_equal (LinearMap R V W)
         (k ↦ (s : Fin n) → Id T (k .fst .fst (standard_basis R n s)) (j s))
         (k ↦ pi_prop (Fin n) (s ↦ Id T (k .fst .fst (standard_basis R n s)) (j s))
           (s ↦ module_set R W (k .fst .fst (standard_basis R n s)) (j s)))
         c u
         (linear_map_ext R V W (c .fst) (u .fst)
           (v ↦ calc
              fin_module_sum R W n (s ↦ W .smul (v s) (j s))
              = fin_module_sum R W n (s ↦ W .smul (v s) (h (standard_basis R n s)))
                by refl (fin_module_sum R W n)
                  (funext (Fin n) (_ ↦ T) (s ↦ W .smul (v s) (j s)) (s ↦ W .smul (v s) (h (standard_basis R n s)))
                    (s ↦ refl (W .smul (v s)) (inverse T (h (standard_basis R n s)) (j s) (u .snd s))))
              = fin_module_sum R W n (s ↦ h (V .smul (v s) (standard_basis R n s)))
                by refl (fin_module_sum R W n)
                  (funext (Fin n) (_ ↦ T) (s ↦ W .smul (v s) (h (standard_basis R n s)))
                    (s ↦ h (V .smul (v s) (standard_basis R n s)))
                    (s ↦ inverse T (h (V .smul (v s) (standard_basis R n s))) (W .smul (v s) (h (standard_basis R n s)))
                      (u .fst .snd (v s) (standard_basis R n s))))
              = h (fin_module_sum R V n (s ↦ V .smul (v s) (standard_basis R n s)))
                by inverse T (h (fin_module_sum R V n (s ↦ V .smul (v s) (standard_basis R n s))))
                  (fin_module_sum R W n (s ↦ h (V .smul (v s) (standard_basis R n s))))
                  (linear_map_fin_sum R V W (u .fst) n (s ↦ V .smul (v s) (standard_basis R n s)))
              = h v by refl h (standard_decomposition R n v) ∎)))

{` Kⁿ is an n-dimensional K-vector space. `}
def standard_vector_space (K : Field) (n : Nat) : VectorSpace K ≔ standard_module (K .fst) n

def standard_vector_space_free (K : Field) (n : Nat)
  : IsFreeVectorSpace K (standard_set n) (standard_vector_space K n) (standard_basis (K .fst) n)
  ≔ standard_module_free (K .fst) n

def standard_n_dimensional (K : Field) (n : Nat) : NDimensionalVectorSpace K n
  ≔ (standard_vector_space K n, (standard_basis (K .fst) n, standard_module_free (K .fst) n))

{` Litmus over ℤ (n = 2): e_0 = (1, 0), e_1 = (0, 1); the extension of
   j = (5, 7) to ℤ sends v = (2, 3) to 2·5 + 3·7 = 31. `}
def fin_two_first : Fin 2 ≔ inl. (inr. star.)

def fin_two_second : Fin 2 ≔ inr. star.

def standard_basis_litmus
  : Id (Product (Product Int Int) (Product Int Int))
      ((standard_basis integer_ring 2 fin_two_first fin_two_first, standard_basis integer_ring 2 fin_two_first fin_two_second),
       (standard_basis integer_ring 2 fin_two_second fin_two_first, standard_basis integer_ring 2 fin_two_second fin_two_second))
      ((int_one, int_zero), (int_zero, int_one))
  ≔ refl (((int_one, int_zero), (int_zero, int_one)) : Product (Product Int Int) (Product Int Int))

def litmus_pair (a b : Int) : Fin 2 → Int ≔ [ inl. _ ↦ a | inr. _ ↦ b ]

def standard_extension_litmus
  : Id Int
      (standard_module_extension integer_ring 2 (ring_self_module integer_ring) (litmus_pair (pos. 5) (pos. 7))
        .fst .fst (litmus_pair (pos. 2) (pos. 3)))
      (pos. 31)
  ≔ refl (pos. 31 : Int)
