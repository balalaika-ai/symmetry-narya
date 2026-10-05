export "1531-f2-polynomial-domain"
export "1508-algebraic-t-equivalence"

{` Chapter 15 (galois.tex), rem:algebraic-endomorphisms-are-automorphisms:
   the counterexample k(X), X ↦ X², for k = 𝔽₂.

   K = 𝔽₂(X) is the field of fractions of 𝔽₂[X] (modules 1530, 1531), an
   extension of 𝔽₂ by the unique ring homomorphism (char_two_bool_hom: K has
   characteristic 2). The Frobenius x ↦ x² is a ring endomorphism of every
   commutative ring of characteristic 2 (char_two_frobenius); it fixes 𝔽₂,
   so it is an 𝔽₂-endomorphism of K, and it sends X to X². It is not
   surjective: X = (p/q)² gives p² = X q² in 𝔽₂[X], impossible for q ≠ 0
   (f2_poly_square_ratio_zero). On the other hand t : USym Gal(K, i) → fiber
   is an equivalence only if every k-endomorphism is an equivalence
   (galois_t_equiv_endo_is_equiv, the converse of galois_t_is_equiv_of_endos
   of module 1504). Hence t is not an equivalence for 𝔽₂(X)/𝔽₂
   (f2_rational_t_not_equiv).

   Consequences. (1) The first claim of the remark is false with the
   printed definition of algebraic elements, under which every extension is
   algebraic (printed_algebraic_t_equiv_fails). (2) With the corrected
   definition, 𝔽₂(X) is not algebraic over 𝔽₂ (f2_rational_not_algebraic,
   from algebraic_galois_t_equiv_dec, since K has decidable equality),
   a litmus for the corrected notion. `}

{` The unique ring homomorphism 𝔽₂ → R into a ring of characteristic 2. `}
def char_two_bool_map (R : AbstractRing) (b : Bool) : R .carrier ≔ match b [ false. ↦ R .zero | true. ↦ R .one ]

def char_two_bool_hom (R : AbstractRing) (h2 : Id (R .carrier) (R .add (R .one) (R .one)) (R .zero)) : RingHom f2_ring R
  ≔ let S ≔ R .carrier in let f ≔ char_two_bool_map R in
    ((f,
      a b ↦ match a, b [
      | false., false. ↦ inverse S (R .add (R .zero) (R .zero)) (R .zero) (R .add_laws .unit_right (R .zero))
      | false., true. ↦ inverse S (R .add (R .zero) (R .one)) (R .one) (R .add_laws .unit_left (R .one))
      | true., false. ↦ inverse S (R .add (R .one) (R .zero)) (R .one) (R .add_laws .unit_right (R .one))
      | true., true. ↦ inverse S (R .add (R .one) (R .one)) (R .zero) h2 ]),
     (refl (R .one),
      a b ↦ match a, b [
      | false., false. ↦ inverse S (R .mul (R .zero) (R .zero)) (R .zero) (ring_mul_zero_left R (R .zero))
      | false., true. ↦ inverse S (R .mul (R .zero) (R .one)) (R .zero) (ring_mul_zero_left R (R .one))
      | true., false. ↦ inverse S (R .mul (R .one) (R .zero)) (R .zero) (ring_mul_one_left R (R .zero))
      | true., true. ↦ inverse S (R .mul (R .one) (R .one)) (R .one) (ring_mul_one_left R (R .one)) ]))

{` z + z = 0 in characteristic 2. `}
def char_two_double (R : AbstractRing) (h2 : Id (R .carrier) (R .add (R .one) (R .one)) (R .zero)) (z : R .carrier)
  : Id (R .carrier) (R .add z z) (R .zero)
  ≔ let S ≔ R .carrier in
    calc
      R .add z z = R .add (R .mul (R .one) z) (R .mul (R .one) z)
        by inverse S (R .add (R .mul (R .one) z) (R .mul (R .one) z)) (R .add z z)
          (refl (R .add) (ring_mul_one_left R z) (ring_mul_one_left R z))
      = R .mul (R .add (R .one) (R .one)) z
        by inverse S (R .mul (R .add (R .one) (R .one)) z) (R .add (R .mul (R .one) z) (R .mul (R .one) z))
          (ring_rdistr R (R .one) (R .one) z)
      = R .mul (R .zero) z by refl ((u ↦ R .mul u z) : S → S) h2
      = R .zero by ring_mul_zero_left R z ∎

{` The Frobenius x ↦ x² of a commutative ring of characteristic 2. `}
def char_two_frobenius (R : AbstractRing) (hc : IsCommutativeRing R) (h2 : Id (R .carrier) (R .add (R .one) (R .one)) (R .zero))
  : RingHom R R
  ≔ let S ≔ R .carrier in let m ≔ R .mul in let ad ≔ R .add in
    ((x ↦ m x x,
      x y ↦
        calc
          m (ad x y) (ad x y) = ad (m x (ad x y)) (m y (ad x y)) by ring_rdistr R x y (ad x y)
          = ad (ad (m x x) (m x y)) (ad (m y x) (m y y)) by refl ad (ring_ldistr R x x y) (ring_ldistr R y x y)
          = ad (ad (m x x) (m x y)) (ad (m x y) (m y y))
            by refl ((u ↦ ad (ad (m x x) (m x y)) (ad u (m y y))) : S → S) (hc y x)
          = ad (m x x) (ad (m x y) (ad (m x y) (m y y)))
            by inverse S (ad (m x x) (ad (m x y) (ad (m x y) (m y y)))) (ad (ad (m x x) (m x y)) (ad (m x y) (m y y)))
              (R .add_laws .assoc (m x x) (m x y) (ad (m x y) (m y y)))
          = ad (m x x) (ad (ad (m x y) (m x y)) (m y y)) by refl (ad (m x x)) (R .add_laws .assoc (m x y) (m x y) (m y y))
          = ad (m x x) (ad (R .zero) (m y y))
            by refl ((u ↦ ad (m x x) (ad u (m y y))) : S → S) (char_two_double R h2 (m x y))
          = ad (m x x) (m y y) by refl (ad (m x x)) (R .add_laws .unit_left (m y y)) ∎),
     (ring_mul_one_left R (R .one),
      x y ↦ cring_mul_interchange4 R hc x y x y))

{` ---- 𝔽₂(X) ---- `}

def f2_rational_field : Field ≔ frac_field f2_poly_domain

def f2_rational_char_two
  : Id (FracQ f2_poly_domain) (frac_add f2_poly_domain (frac_one f2_poly_domain) (frac_one f2_poly_domain))
      (frac_zero f2_poly_domain)
  ≔ let D ≔ f2_poly_domain in let R ≔ D .ring in let S ≔ R .carrier in let m ≔ R .mul in let o ≔ R .one in
    frac_encode D (frac_pair_add D (frac_pair_one D) (frac_pair_one D)) (frac_pair_zero D)
      (calc
         m (R .add (m o o) (m o o)) o = R .add (m o o) (m o o) by ring_mul_one_right R (R .add (m o o) (m o o))
         = R .add o o by refl (R .add) (ring_mul_one_right R o) (ring_mul_one_right R o)
         = R .zero by f2_poly_char_two
         = m (R .zero) (m o o) by inverse S (m (R .zero) (m o o)) (R .zero) (ring_mul_zero_left R (m o o)) ∎)

{` 𝔽₂(X) as an extension of 𝔽₂. `}
def f2_rational_ext : FieldExt f2_field
  ≔ (f2_rational_field, char_two_bool_hom (frac_ring f2_poly_domain) f2_rational_char_two)

def f2_rational_frobenius_hom : RingHom (frac_ring f2_poly_domain) (frac_ring f2_poly_domain)
  ≔ char_two_frobenius (frac_ring f2_poly_domain) (frac_mul_comm f2_poly_domain) f2_rational_char_two

{` The Frobenius is an 𝔽₂-endomorphism of 𝔽₂(X). `}
def f2_rational_frobenius : KAlgHom f2_field f2_rational_ext f2_rational_ext
  ≔ let R ≔ frac_ring f2_poly_domain in let S ≔ R .carrier in
    (f2_rational_frobenius_hom,
     ring_hom_ext f2_ring R (f2_rational_ext .snd)
       (ring_hom_compose f2_ring R R (f2_rational_ext .snd) f2_rational_frobenius_hom)
       [ false. ↦ inverse S (R .mul (R .zero) (R .zero)) (R .zero) (ring_mul_zero_left R (R .zero))
       | true. ↦ inverse S (R .mul (R .one) (R .one)) (R .one) (ring_mul_one_left R (R .one)) ])

def f2_rational_x : FracQ f2_poly_domain ≔ frac_class f2_poly_domain (frac_pair_of f2_poly_domain f2_poly_x)

{` Litmus: the Frobenius sends X to X², by computation. `}
def f2_rational_frobenius_x
  : Id (FracQ f2_poly_domain) (f2_rational_frobenius .fst .fst .fst f2_rational_x)
      (frac_mul f2_poly_domain f2_rational_x f2_rational_x)
  ≔ refl (frac_mul f2_poly_domain f2_rational_x f2_rational_x)

{` X is not a square in 𝔽₂(X). `}
def f2_rational_x_not_square (z : FracQ f2_poly_domain)
  (e : Id (FracQ f2_poly_domain) (frac_mul f2_poly_domain z z) f2_rational_x) : Empty
  ≔ let D ≔ f2_poly_domain in let Q ≔ FracQ D in let R ≔ D .ring in
    frac_ind D (z ↦ Id Q (frac_mul D z z) f2_rational_x → Empty)
      (z ↦ pi_prop (Id Q (frac_mul D z z) f2_rational_x) (_ ↦ Empty) (_ ↦ empty_prop))
      (a e' ↦
        let p ≔ a .fst in let q ≔ a .snd .fst in
        f2_poly_square_ratio_zero p q (a .snd .snd)
          (concat (R .carrier) (R .mul p p) (R .mul (R .mul p p) (R .one)) (R .mul f2_poly_x (R .mul q q))
            (inverse (R .carrier) (R .mul (R .mul p p) (R .one)) (R .mul p p) (ring_mul_one_right R (R .mul p p)))
            (frac_effective D (frac_pair_mul D a a) (frac_pair_of D f2_poly_x) e')))
      z e

def f2_rational_frobenius_not_equiv
  : Not (isEquiv (FracQ f2_poly_domain) (FracQ f2_poly_domain) (f2_rational_frobenius .fst .fst .fst))
  ≔ h ↦ f2_rational_x_not_square (h f2_rational_x .center .fst) (h f2_rational_x .center .snd)

{` Converse of galois_t_is_equiv_of_endos (module 1504): if t is an
   equivalence, every k-endomorphism of K is an equivalence. `}
def galois_t_equiv_endo_is_equiv (k : Field) (E : FieldExt k)
  (h : isEquiv (USym (galois_group k E)) (restriction_fiber_over k E E) (galois_t k E)) (φ : KAlgHom k E E)
  : isEquiv (ext_carrier k E) (ext_carrier k E) (φ .fst .fst .fst)
  ≔ let A ≔ ext_carrier k E in
    let Fb ≔ restriction_fiber_over k E E in let H ≔ KAlgHom k E E in
    let Φ ≔ restriction_fiber_kalg_equiv k E E in
    let u ≔ equiv_inverse_map Fb H Φ φ in
    let w ≔ h u .center in
    let g ≔ w .fst in
    let σ ≔ galois_usym_kaut_equiv k E .map g in
    let P1 : Id H (kaut_to_kalg k E E σ) φ
      ≔ calc
          kaut_to_kalg k E E σ = restriction_fiber_to_kalg k E E (galois_t k E g)
            by inverse H (restriction_fiber_to_kalg k E E (galois_t k E g)) (kaut_to_kalg k E E σ) (galois_t_identification k E g)
          = Φ .map u by refl (Φ .map) (w .snd)
          = φ by equiv_counit Fb H Φ φ ∎ in
    transport (A → A) (f ↦ isEquiv A A f) (σ .fst .fst .map) (φ .fst .fst .fst)
      (refl ((ψ ↦ ψ .fst .fst .fst) : H → (A → A)) P1) (σ .fst .fst .equiv)

{` t is not an equivalence for 𝔽₂(X)/𝔽₂. `}
def f2_rational_t_not_equiv
  : Not (isEquiv (USym (galois_group f2_field f2_rational_ext)) (restriction_fiber_over f2_field f2_rational_ext f2_rational_ext)
      (galois_t f2_field f2_rational_ext))
  ≔ h ↦ f2_rational_frobenius_not_equiv (galois_t_equiv_endo_is_equiv f2_field f2_rational_ext h f2_rational_frobenius)

{` rem:algebraic-endomorphisms-are-automorphisms, first claim, as printed
   (with the printed definition of algebraic, under which every extension
   is algebraic): refuted. `}
def printed_algebraic_t_equiv_fails
  : Not ((k : Field) (E : FieldExt k) → IsAlgebraicExtensionAsPrinted k E
         → isEquiv (USym (galois_group k E)) (restriction_fiber_over k E E) (galois_t k E))
  ≔ H ↦ f2_rational_t_not_equiv (H f2_field f2_rational_ext (every_extension_algebraic_as_printed f2_field f2_rational_ext))

{` Decidable equality of a field of fractions. `}
def frac_decidable_equality (D : DecidableDomain) : DecidableEquality (FracQ D)
  ≔ z w ↦
    let Q ≔ FracQ D in let m ≔ D .ring .mul in
    frac_ind D (z ↦ Decidable (Id Q z w)) (z ↦ f2_decidable_prop (Id Q z w) (frac_set D z w))
      (a ↦ frac_ind D (w ↦ Decidable (Id Q (frac_class D a) w))
         (w ↦ f2_decidable_prop (Id Q (frac_class D a) w) (frac_set D (frac_class D a) w))
         (b ↦ match D .dec (m (a .fst) (b .snd .fst)) (m (b .fst) (a .snd .fst)) [
           | inl. r ↦ inl. (frac_encode D a b r)
           | inr. nr ↦ inr. (e ↦ nr (frac_effective D a b e)) ])
         w)
      z

{` Litmus for the corrected definition: 𝔽₂(X) is not algebraic over 𝔽₂. `}
def f2_rational_not_algebraic : Not (IsAlgebraicExtension f2_field f2_rational_ext)
  ≔ h ↦ f2_rational_t_not_equiv
      (algebraic_galois_t_equiv_dec f2_field f2_rational_ext (frac_decidable_equality f2_poly_domain) h)
