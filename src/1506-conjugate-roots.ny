export "1503-algebraic-elements"

{` Chapter 15 (galois.tex), introduction: "for any polynomial Q : ℝ[X, Y],
   Q(i, −i) = 0 iff Q(−i, i) = 0, because there is an automorphism σ of ℂ
   fixing ℝ with σ(i) = −i and σ(−i) = i". ℂ and ℝ are not constructed in
   this project; the statement is proved for any extension (K, i) of k and
   any k-automorphism σ (an element of FieldExtIso k E E, i.e. a symmetry
   of Gal(K, i)) exchanging α and β (conjugate_roots_iff). Polynomials in
   two variables are given by coefficients a : Fin(n+1) → Fin(m+1) → k and
   evaluated as Σ_q (Σ_p i(a_pq) x^p) y^q (poly2_value). The key lemma is
   that ring homomorphisms commute with polynomial evaluation
   (ring_hom_poly_value). The 𝔽₄ instance (ω, ω² and the Frobenius) is in
   module 1505. `}

def ring_hom_power (R S : AbstractRing) (φ : RingHom R S) (x : R .carrier) (n : Nat)
  : Id (S .carrier) (φ .fst .fst (ring_power R x n)) (ring_power S (φ .fst .fst x) n)
  ≔ match n [
  | zero. ↦ φ .snd .fst
  | suc. n ↦ concat (S .carrier) (φ .fst .fst (R .mul (ring_power R x n) x))
      (S .mul (φ .fst .fst (ring_power R x n)) (φ .fst .fst x)) (S .mul (ring_power S (φ .fst .fst x) n) (φ .fst .fst x))
      (φ .snd .snd (ring_power R x n) x)
      (refl ((y ↦ S .mul y (φ .fst .fst x)) : S .carrier → S .carrier) (ring_hom_power R S φ x n)) ]

{` φ(a(0) + a(1)x + ⋯ + a(n)xⁿ) = φ(a(0)) + φ(a(1))φ(x) + ⋯ + φ(a(n))φ(x)ⁿ. `}
def ring_hom_poly_value (R S : AbstractRing) (φ : RingHom R S) (x : R .carrier) (n : Nat) (a : Fin (suc. n) → R .carrier)
  : Id (S .carrier) (φ .fst .fst (poly_value R x n a)) (poly_value S (φ .fst .fst x) n (m ↦ φ .fst .fst (a m)))
  ≔ let f ≔ φ .fst .fst in
    match n [
  | zero. ↦ refl (f (a (inr. star.)))
  | suc. n ↦
    concat (S .carrier)
      (f (R .add (poly_value R x n (s ↦ a (inl. s))) (R .mul (a (inr. star.)) (ring_power R x (suc. n)))))
      (S .add (f (poly_value R x n (s ↦ a (inl. s)))) (f (R .mul (a (inr. star.)) (ring_power R x (suc. n)))))
      (S .add (poly_value S (f x) n (s ↦ f (a (inl. s)))) (S .mul (f (a (inr. star.))) (ring_power S (f x) (suc. n))))
      (φ .fst .snd (poly_value R x n (s ↦ a (inl. s))) (R .mul (a (inr. star.)) (ring_power R x (suc. n))))
      (refl (S .add) (ring_hom_poly_value R S φ x n (s ↦ a (inl. s)))
        (concat (S .carrier) (f (R .mul (a (inr. star.)) (ring_power R x (suc. n))))
           (S .mul (f (a (inr. star.))) (f (ring_power R x (suc. n))))
           (S .mul (f (a (inr. star.))) (ring_power S (f x) (suc. n)))
           (φ .snd .snd (a (inr. star.)) (ring_power R x (suc. n)))
           (refl (S .mul (f (a (inr. star.)))) (ring_hom_power R S φ x (suc. n))))) ]

{` poly_value respects pointwise equal coefficients. `}
def poly_value_coefficients (R : AbstractRing) (x : R .carrier) (n : Nat) (a b : Fin (suc. n) → R .carrier)
  (h : (m : Fin (suc. n)) → Id (R .carrier) (a m) (b m))
  : Id (R .carrier) (poly_value R x n a) (poly_value R x n b)
  ≔ refl ((c ↦ poly_value R x n c) : (Fin (suc. n) → R .carrier) → R .carrier)
      (funext (Fin (suc. n)) (_ ↦ R .carrier) a b h)

{` Q(x, y) = Σ_q (Σ_p i(a_pq) x^p) y^q. `}
def poly2_value (k : Field) (E : FieldExt k) (n m : Nat) (a : Fin (suc. n) → Fin (suc. m) → k .fst .carrier)
  (x y : ext_carrier k E) : ext_carrier k E
  ≔ poly_value (E .fst .fst) y m (q ↦ poly_value (E .fst .fst) x n (p ↦ ext_map k E (a p q)))

{` A k-automorphism σ commutes with evaluation of polynomials over k. `}
def kaut_poly2_value (k : Field) (E : FieldExt k) (σ : FieldExtIso k E E)
  (n m : Nat) (a : Fin (suc. n) → Fin (suc. m) → k .fst .carrier) (x y : ext_carrier k E)
  : Id (ext_carrier k E) (σ .fst .fst .map (poly2_value k E n m a x y))
      (poly2_value k E n m a (σ .fst .fst .map x) (σ .fst .fst .map y))
  ≔ let K ≔ E .fst .fst in let A ≔ K .carrier in
    let φ ≔ ring_iso_hom K K (σ .fst) in let f ≔ σ .fst .fst .map in
    let fix ≔ (c ↦ refl ((χ ↦ χ .fst .fst c) : RingHom (k .fst) K → A) (σ .snd))
              : (c : k .fst .carrier) → Id A (f (ext_map k E c)) (ext_map k E c) in
    concat A (f (poly2_value k E n m a x y))
      (poly_value K (f y) m (q ↦ f (poly_value K x n (p ↦ ext_map k E (a p q)))))
      (poly2_value k E n m a (f x) (f y))
      (ring_hom_poly_value K K φ y m (q ↦ poly_value K x n (p ↦ ext_map k E (a p q))))
      (poly_value_coefficients K (f y) m
         (q ↦ f (poly_value K x n (p ↦ ext_map k E (a p q))))
         (q ↦ poly_value K (f x) n (p ↦ ext_map k E (a p q)))
         (q ↦ concat A (f (poly_value K x n (p ↦ ext_map k E (a p q))))
                (poly_value K (f x) n (p ↦ f (ext_map k E (a p q))))
                (poly_value K (f x) n (p ↦ ext_map k E (a p q)))
                (ring_hom_poly_value K K φ x n (p ↦ ext_map k E (a p q)))
                (poly_value_coefficients K (f x) n (p ↦ f (ext_map k E (a p q))) (p ↦ ext_map k E (a p q))
                   (p ↦ fix (a p q)))))

{` Introduction of the chapter: if a k-automorphism σ exchanges α and β,
   then Q(α, β) = 0 iff Q(β, α) = 0 for every polynomial Q over k. `}
def conjugate_roots_forward (k : Field) (E : FieldExt k) (σ : FieldExtIso k E E) (α β : ext_carrier k E)
  (hα : Id (ext_carrier k E) (σ .fst .fst .map α) β) (hβ : Id (ext_carrier k E) (σ .fst .fst .map β) α)
  (n m : Nat) (a : Fin (suc. n) → Fin (suc. m) → k .fst .carrier)
  (h : Id (ext_carrier k E) (poly2_value k E n m a α β) (E .fst .fst .zero))
  : Id (ext_carrier k E) (poly2_value k E n m a β α) (E .fst .fst .zero)
  ≔ let K ≔ E .fst .fst in let A ≔ K .carrier in let f ≔ σ .fst .fst .map in
    calc
      poly2_value k E n m a β α
      = poly2_value k E n m a (f α) (f β)
        by refl ((u ↦ poly2_value k E n m a (u .fst) (u .snd)) : Product A A → A)
             ((inverse A (f α) β hα, inverse A (f β) α hβ) : Id (Product A A) (β, α) (f α, f β))
      = f (poly2_value k E n m a α β)
        by inverse A (f (poly2_value k E n m a α β)) (poly2_value k E n m a (f α) (f β)) (kaut_poly2_value k E σ n m a α β)
      = f (K .zero) by refl f h
      = K .zero by σ .fst .snd .snd .snd .fst ∎

def conjugate_roots_iff (k : Field) (E : FieldExt k) (σ : FieldExtIso k E E) (α β : ext_carrier k E)
  (hα : Id (ext_carrier k E) (σ .fst .fst .map α) β) (hβ : Id (ext_carrier k E) (σ .fst .fst .map β) α)
  (n m : Nat) (a : Fin (suc. n) → Fin (suc. m) → k .fst .carrier)
  : Product
      (Id (ext_carrier k E) (poly2_value k E n m a α β) (E .fst .fst .zero)
        → Id (ext_carrier k E) (poly2_value k E n m a β α) (E .fst .fst .zero))
      (Id (ext_carrier k E) (poly2_value k E n m a β α) (E .fst .fst .zero)
        → Id (ext_carrier k E) (poly2_value k E n m a α β) (E .fst .fst .zero))
  ≔ (conjugate_roots_forward k E σ α β hα hβ n m a, conjugate_roots_forward k E σ β α hβ hα n m a)
