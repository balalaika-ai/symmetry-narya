export "1520-field-hom-injective"

{` Chapter 15 (galois.tex), rem:algebraic-endomorphisms-are-automorphisms,
   preliminaries: synthetic division in a commutative ring for the
   polynomials p_a(x) = a(0) + a(1)x + ⋯ + a(n)xⁿ of module 1503
   (poly_value). For a of degree n + 1 and c, poly_div gives coefficients q
   of degree n with the same leading coefficient (poly_div_lead) and
   p_a(x) = (x − c) · p_q(x) + p_a(c) for all x (poly_div_spec).
   Construction: the top term a_N xᴺ = a_N x^(N−1) (x − c) + a_N c x^(N−1),
   so q is obtained by dividing the polynomial with the top coefficient
   folded down (poly_fold_top) and appending a_N. `}

{` Coefficients of p_a(X) − a_N Xᴺ + a_N c X^(N−1) (N = n + 2). `}
def poly_fold_top (R : AbstractRing) (n : Nat) (a : Fin (suc. (suc. (suc. n))) → R .carrier) (c : R .carrier)
  : Fin (suc. (suc. n)) → R .carrier
  ≔ [ inl. j ↦ a (inl. (inl. j)) | inr. _ ↦ R .add (a (inl. (inr. star.))) (R .mul (a (inr. star.)) c) ]

{` The quotient of p_a by X − c. `}
def poly_div (R : AbstractRing) (n : Nat) (a : Fin (suc. (suc. n)) → R .carrier) (c : R .carrier)
  : Fin (suc. n) → R .carrier
  ≔ match n [
  | zero. ↦ _ ↦ a (inr. star.)
  | suc. n ↦ [ inl. j ↦ poly_div R n (poly_fold_top R n a c) c j | inr. _ ↦ a (inr. star.) ] ]

def poly_div_lead (R : AbstractRing) (n : Nat) (a : Fin (suc. (suc. n)) → R .carrier) (c : R .carrier)
  : Id (R .carrier) (poly_div R n a c (inr. star.)) (a (inr. star.))
  ≔ match n [ zero. ↦ refl (a (inr. star.)) | suc. n ↦ refl (a (inr. star.)) ]

{` (Q + (t + a c) Y) + (y − c)(a Y) = (Q + t Y) + a (Y y). `}
def poly_fold_step_alg (R : AbstractRing) (hc : IsCommutativeRing R) (Q t a c y Y : R .carrier)
  : Id (R .carrier)
      (R .add (R .add Q (R .mul (R .add t (R .mul a c)) Y)) (R .mul (R .add y (R .neg c)) (R .mul a Y)))
      (R .add (R .add Q (R .mul t Y)) (R .mul a (R .mul Y y)))
  ≔ let A ≔ R .carrier in let p ≔ R .add in let m ≔ R .mul in
    let tY ≔ m t Y in let acY ≔ m (m a c) Y in let yaY ≔ m y (m a Y) in
    calc
      p (p Q (m (p t (m a c)) Y)) (m (p y (R .neg c)) (m a Y))
      = p (p Q (p tY acY)) (m (p y (R .neg c)) (m a Y))
        by refl ((v ↦ p (p Q v) (m (p y (R .neg c)) (m a Y))) : A → A) (ring_rdistr R t (m a c) Y)
      = p (p Q (p tY acY)) (p yaY (R .neg (m c (m a Y))))
        by refl (p (p Q (p tY acY))) (ring_sub_rdistr R y c (m a Y))
      = p (p Q (p tY acY)) (p yaY (R .neg (m (m c a) Y)))
        by refl ((v ↦ p (p Q (p tY acY)) (p yaY (R .neg v))) : A → A) (ring_mul_assoc R c a Y)
      = p (p Q (p tY acY)) (p yaY (R .neg acY))
        by refl ((v ↦ p (p Q (p tY acY)) (p yaY (R .neg (m v Y)))) : A → A) (hc c a)
      = p (p (p Q tY) acY) (p yaY (R .neg acY))
        by refl ((v ↦ p v (p yaY (R .neg acY))) : A → A) (R .add_laws .assoc Q tY acY)
      = p (p Q tY) (p acY (p yaY (R .neg acY)))
        by inverse A (p (p Q tY) (p acY (p yaY (R .neg acY)))) (p (p (p Q tY) acY) (p yaY (R .neg acY)))
             (R .add_laws .assoc (p Q tY) acY (p yaY (R .neg acY)))
      = p (p Q tY) yaY by refl (p (p Q tY)) (ring_add_cancel_mid R acY yaY)
      = p (p Q tY) (m (m a Y) y) by refl (p (p Q tY)) (hc y (m a Y))
      = p (p Q tY) (m a (m Y y)) by refl (p (p Q tY)) (inverse A (m a (m Y y)) (m (m a Y) y) (ring_mul_assoc R a Y y)) ∎

{` (u D + P) + u E = u (D + E) + P. `}
def poly_div_step_alg (R : AbstractRing) (u D E P : R .carrier)
  : Id (R .carrier) (R .add (R .add (R .mul u D) P) (R .mul u E)) (R .add (R .mul u (R .add D E)) P)
  ≔ let A ≔ R .carrier in let p ≔ R .add in let m ≔ R .mul in
    calc
      p (p (m u D) P) (m u E) = p (m u D) (p P (m u E))
        by inverse A (p (m u D) (p P (m u E))) (p (p (m u D) P) (m u E)) (R .add_laws .assoc (m u D) P (m u E))
      = p (m u D) (p (m u E) P) by refl (p (m u D)) (ring_add_comm R P (m u E))
      = p (p (m u D) (m u E)) P by R .add_laws .assoc (m u D) (m u E) P
      = p (m u (p D E)) P
        by refl ((v ↦ p v P) : A → A) (inverse A (m u (p D E)) (p (m u D) (m u E)) (ring_ldistr R u D E)) ∎

{` a₀ + a₁(1 x) = (x − c) a₁ + (a₀ + a₁(1 c)). `}
def poly_div_base_alg (R : AbstractRing) (hc : IsCommutativeRing R) (a0 a1 x c : R .carrier)
  : Id (R .carrier) (R .add a0 (R .mul a1 (R .mul (R .one) x)))
      (R .add (R .mul (R .add x (R .neg c)) a1) (R .add a0 (R .mul a1 (R .mul (R .one) c))))
  ≔ let A ≔ R .carrier in let p ≔ R .add in let m ≔ R .mul in
    inverse A (p (m (p x (R .neg c)) a1) (p a0 (m a1 (m (R .one) c)))) (p a0 (m a1 (m (R .one) x)))
      (calc
         p (m (p x (R .neg c)) a1) (p a0 (m a1 (m (R .one) c)))
         = p (p (m x a1) (R .neg (m c a1))) (p a0 (m a1 (m (R .one) c)))
           by refl ((v ↦ p v (p a0 (m a1 (m (R .one) c)))) : A → A) (ring_sub_rdistr R x c a1)
         = p (p (m x a1) (R .neg (m c a1))) (p a0 (m a1 c))
           by refl ((v ↦ p (p (m x a1) (R .neg (m c a1))) (p a0 (m a1 v))) : A → A) (ring_mul_one_left R c)
         = p (p (m x a1) (R .neg (m c a1))) (p a0 (m c a1))
           by refl ((v ↦ p (p (m x a1) (R .neg (m c a1))) (p a0 v)) : A → A) (hc a1 c)
         = p (p (m x a1) a0) (p (R .neg (m c a1)) (m c a1))
           by ring_add_interchange R (m x a1) (R .neg (m c a1)) a0 (m c a1)
         = p (p (m x a1) a0) (R .zero) by refl (p (p (m x a1) a0)) (ag_inv_left (ring_additive_group R) (m c a1))
         = p (m x a1) a0 by R .add_laws .unit_right (p (m x a1) a0)
         = p a0 (m x a1) by ring_add_comm R (m x a1) a0
         = p a0 (m a1 x) by refl (p a0) (hc x a1)
         = p a0 (m a1 (m (R .one) x))
           by refl ((v ↦ p a0 (m a1 v)) : A → A) (inverse A (m (R .one) x) x (ring_mul_one_left R x)) ∎)

{` Synthetic division: p_a(x) = (x − c) · p_{poly_div a c}(x) + p_a(c). `}
def poly_div_spec (R : AbstractRing) (hc : IsCommutativeRing R) (n : Nat) (a : Fin (suc. (suc. n)) → R .carrier)
  (c x : R .carrier)
  : Id (R .carrier) (poly_value R x (suc. n) a)
      (R .add (R .mul (R .add x (R .neg c)) (poly_value R x n (poly_div R n a c))) (poly_value R c (suc. n) a))
  ≔ match n [
  | zero. ↦ poly_div_base_alg R hc (a (inl. (inr. star.))) (a (inr. star.)) x c
  | suc. n ↦
    let A ≔ R .carrier in let p ≔ R .add in let m ≔ R .mul in
    let b ≔ poly_fold_top R n a c in
    let aN ≔ a (inr. star.) in let t ≔ a (inl. (inr. star.)) in
    let u ≔ p x (R .neg c) in
    let Xx ≔ ring_power R x (suc. n) in let Xc ≔ ring_power R c (suc. n) in
    let D ≔ poly_value R x n (poly_div R n b c) in
    let pa_x ≔ poly_value R x (suc. (suc. n)) a in let pa_c ≔ poly_value R c (suc. (suc. n)) a in
    let pb_x ≔ poly_value R x (suc. n) b in let pb_c ≔ poly_value R c (suc. n) b in
    let step_x : Id A (p pb_x (m u (m aN Xx))) pa_x
      ≔ poly_fold_step_alg R hc (poly_value R x n (s ↦ a (inl. (inl. s)))) t aN c x Xx in
    let step_c : Id A (p pb_c (m (p c (R .neg c)) (m aN Xc))) pa_c
      ≔ poly_fold_step_alg R hc (poly_value R c n (s ↦ a (inl. (inl. s)))) t aN c c Xc in
    let eq_c : Id A pb_c pa_c
      ≔ concat A pb_c (p pb_c (m (p c (R .neg c)) (m aN Xc))) pa_c
          (inverse A (p pb_c (m (p c (R .neg c)) (m aN Xc))) pb_c
            (concat A (p pb_c (m (p c (R .neg c)) (m aN Xc))) (p pb_c (R .zero)) pb_c
              (refl (p pb_c) (ring_sub_self_mul R c (m aN Xc))) (R .add_laws .unit_right pb_c)))
          step_c in
    calc
      pa_x = p pb_x (m u (m aN Xx)) by inverse A (p pb_x (m u (m aN Xx))) pa_x step_x
      = p (p (m u D) pb_c) (m u (m aN Xx))
        by refl ((v ↦ p v (m u (m aN Xx))) : A → A) (poly_div_spec R hc n b c x)
      = p (m u (p D (m aN Xx))) pb_c by poly_div_step_alg R u D (m aN Xx) pb_c
      = p (m u (p D (m aN Xx))) pa_c by refl (p (m u (p D (m aN Xx)))) eq_c ∎ ]

{` Litmus over 𝔽₂: 1 + X + X² = (X − 1)·X + 1, so dividing by X − 1 gives the
   quotient X, with coefficients (0, 1). `}
def f2_poly_div_litmus
  : Product (Id Bool (poly_div f2_ring (suc. zero.) (_ ↦ true.) true. (inl. (inr. star.))) false.)
      (Id Bool (poly_div f2_ring (suc. zero.) (_ ↦ true.) true. (inr. star.)) true.)
  ≔ (refl false., refl true.)
