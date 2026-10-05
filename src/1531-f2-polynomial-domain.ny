export "1530-domain-fractions"
export "1313-polynomial-ring"
export "46-natural-arithmetic"

{` Chapter 15 (galois.tex), rem:algebraic-endomorphisms-are-automorphisms:
   preliminaries for the counterexample 𝔽₂(X), X ↦ X² (module 1532). The
   polynomial ring 𝔽₂[X] = polynomial_ring f2_ring of module 1313 is a
   DecidableDomain (f2_poly_domain), and X·q² = p² forces q = 0
   (f2_poly_square_ratio_zero).

   The tool is the valuation (index of the lowest nonzero coefficient), which
   fits the recursion (f g)_(n+1) = f_0 g_(n+1) + ((shift f) g)_n of the
   Cauchy product (module 1312): if the coefficients of f below a and those
   of g below b vanish, then those of f g below b + a vanish and
   (f g)_(b+a) = f_a g_b (series_mul_low_zero, series_mul_low_value; any
   ring). A nonzero polynomial over 𝔽₂ has a valuation (found by search up
   to a vanishing bound), so products of nonzero polynomials are nonzero.
   p² has even valuation, X q² odd valuation; hence X q² = p² is impossible
   for q ≠ 0. Equality of polynomials is decidable by comparing the
   coefficients below a common vanishing bound. `}

{` ---- Natural numbers ---- `}

def lt_suc_split (i N : Nat) (h : Le i N) : Sum (Lt i N) (Id Nat i N)
  ≔ match i, N [
  | zero., zero. ↦ inr. (refl (zero. : Nat))
  | zero., suc. N ↦ inl. star.
  | suc. i, zero. ↦ match h [ ]
  | suc. i, suc. N ↦ match lt_suc_split i N h [ inl. x ↦ inl. x | inr. e ↦ inr. (suc. e) ] ]

def nat_split_below (N i : Nat) : Sum (Lt i N) (Σ Nat (k ↦ Id Nat i (add k N)))
  ≔ match N [
  | zero. ↦ inr. (i, refl i)
  | suc. N ↦ match i [
    | zero. ↦ inl. star.
    | suc. i ↦ match nat_split_below N i [ inl. h ↦ inl. h | inr. w ↦ inr. (w .fst, suc. (w .snd)) ] ] ]

def nat_le_of_not_lt (m n : Nat) (h : Not (Lt n m)) : Le m n
  ≔ match m, n [
  | zero., n ↦ star.
  | suc. m, zero. ↦ match h star. [ ]
  | suc. m, suc. n ↦ nat_le_of_not_lt m n h ]

def nat_double_ne_odd (c b : Nat) (e : Id Nat (add c c) (suc. (add b b))) : Empty
  ≔ match c [
  | zero. ↦ nat_zero_ne_suc (add b b) e
  | suc. c ↦
    let e2 : Id Nat (suc. (add c c)) (add b b)
      ≔ concat Nat (suc. (add c c)) (add (suc. c) c) (add b b)
          (inverse Nat (add (suc. c) c) (suc. (add c c)) (add_suc_left c c)) (refl nat_pred e) in
    match b [
    | zero. ↦ nat_zero_ne_suc (add c c) (inverse Nat (suc. (add c c)) zero. e2)
    | suc. b ↦ nat_double_ne_odd c b
        (refl nat_pred (concat Nat (suc. (add c c)) (suc. (add (suc. b) b)) (suc. (suc. (add b b))) e2 (suc. (add_suc_left b b)))) ] ]

{` ---- Valuations in R[[x]] ---- `}

def SeriesLowZero (R : AbstractRing) (f : Nat → R .carrier) (a : Nat) : Type
  ≔ (i : Nat) → Lt i a → Id (R .carrier) (f i) (R .zero)

def lt_suc_drop (j b : Nat) (h : Lt (suc. j) b) : Lt j b
  ≔ match b [ zero. ↦ match h [ ] | suc. b ↦ lt_le j b h ]

def series_mul_low_right (R : AbstractRing) (h g : Nat → R .carrier) (b : Nat) (hg : SeriesLowZero R g b)
  (j : Nat) (hj : Lt j b) : Id (R .carrier) (series_mul R h g j) (R .zero)
  ≔ let S ≔ R .carrier in
    match j [
  | zero. ↦ concat S (R .mul (h zero.) (g zero.)) (R .mul (h zero.) (R .zero)) (R .zero)
      (refl (R .mul (h zero.)) (hg zero. hj)) (ring_mul_zero_right R (h zero.))
  | suc. j ↦ concat S (R .add (R .mul (h zero.) (g (suc. j))) (series_mul R (series_shift R h) g j))
      (R .add (R .zero) (R .zero)) (R .zero)
      (refl (R .add)
        (concat S (R .mul (h zero.) (g (suc. j))) (R .mul (h zero.) (R .zero)) (R .zero)
          (refl (R .mul (h zero.)) (hg (suc. j) hj)) (ring_mul_zero_right R (h zero.)))
        (series_mul_low_right R (series_shift R h) g b hg j (lt_suc_drop j b hj)))
      (R .add_laws .unit_right (R .zero)) ]

def series_mul_low_zero (R : AbstractRing) (f g : Nat → R .carrier) (b : Nat) (hg : SeriesLowZero R g b)
  (a : Nat) (hf : SeriesLowZero R f a) (n : Nat) (hn : Lt n (add b a)) : Id (R .carrier) (series_mul R f g n) (R .zero)
  ≔ let S ≔ R .carrier in
    match a [
  | zero. ↦ series_mul_low_right R f g b hg n hn
  | suc. a ↦ match n [
    | zero. ↦ concat S (R .mul (f zero.) (g zero.)) (R .mul (R .zero) (g zero.)) (R .zero)
        (refl ((u ↦ R .mul u (g zero.)) : S → S) (hf zero. star.)) (ring_mul_zero_left R (g zero.))
    | suc. n ↦ concat S (R .add (R .mul (f zero.) (g (suc. n))) (series_mul R (series_shift R f) g n))
        (R .add (R .zero) (R .zero)) (R .zero)
        (refl (R .add)
          (concat S (R .mul (f zero.) (g (suc. n))) (R .mul (R .zero) (g (suc. n))) (R .zero)
            (refl ((u ↦ R .mul u (g (suc. n))) : S → S) (hf zero. star.)) (ring_mul_zero_left R (g (suc. n))))
          (series_mul_low_zero R (series_shift R f) g b hg a (i hi ↦ hf (suc. i) hi) n hn))
        (R .add_laws .unit_right (R .zero)) ] ]

def le_refl_lt_suc (b : Nat) : Lt b (suc. b) ≔ le_refl b

def series_mul_low_value (R : AbstractRing) (f g : Nat → R .carrier) (b : Nat) (hg : SeriesLowZero R g b)
  (a : Nat) (hf : SeriesLowZero R f a) : Id (R .carrier) (series_mul R f g (add b a)) (R .mul (f a) (g b))
  ≔ let S ≔ R .carrier in
    match a [
  | zero. ↦ match b [
    | zero. ↦ refl (R .mul (f zero.) (g zero.))
    | suc. b ↦ concat S (R .add (R .mul (f zero.) (g (suc. b))) (series_mul R (series_shift R f) g b))
        (R .add (R .mul (f zero.) (g (suc. b))) (R .zero)) (R .mul (f zero.) (g (suc. b)))
        (refl (R .add (R .mul (f zero.) (g (suc. b))))
          (series_mul_low_right R (series_shift R f) g (suc. b) hg b (le_refl_lt_suc b)))
        (R .add_laws .unit_right (R .mul (f zero.) (g (suc. b)))) ]
  | suc. a ↦ concat S (R .add (R .mul (f zero.) (g (suc. (add b a)))) (series_mul R (series_shift R f) g (add b a)))
      (R .add (R .zero) (R .mul (f (suc. a)) (g b))) (R .mul (f (suc. a)) (g b))
      (refl (R .add)
        (concat S (R .mul (f zero.) (g (suc. (add b a)))) (R .mul (R .zero) (g (suc. (add b a)))) (R .zero)
          (refl ((u ↦ R .mul u (g (suc. (add b a)))) : S → S) (hf zero. star.)) (ring_mul_zero_left R (g (suc. (add b a)))))
        (series_mul_low_value R (series_shift R f) g b hg a (i hi ↦ hf (suc. i) hi)))
      (R .add_laws .unit_left (R .mul (f (suc. a)) (g b))) ]

{` ---- 𝔽₂[X] ---- `}

def f2_poly : AbstractRing ≔ polynomial_ring f2_ring

def f2_poly_carrier : Type ≔ f2_poly .carrier

def f2_bool_cases (b : Bool) : Sum (Id Bool b true.) (Id Bool b false.)
  ≔ match b [ true. ↦ inl. (refl (true. : Bool)) | false. ↦ inr. (refl (false. : Bool)) ]

def f2_bool_dec (a b : Bool) : Decidable (Id Bool a b)
  ≔ match a, b [
  | false., false. ↦ inl. (refl (false. : Bool))
  | false., true. ↦ inr. (p ↦ bool_encode false. true. p)
  | true., false. ↦ inr. (p ↦ bool_encode true. false. p)
  | true., true. ↦ inl. (refl (true. : Bool)) ]

def f2_true_ne_false (p : Id Bool true. false.) : Empty ≔ bool_encode true. false. p

def f2_poly_ext (u v : f2_poly_carrier) (h : (i : Nat) → Id Bool (u .fst i) (v .fst i)) : Id f2_poly_carrier u v
  ≔ subtype_equal (Nat → Bool) (IsPolynomialSeries f2_ring) (is_polynomial_series_prop f2_ring) u v
      (funext Nat (_ ↦ Bool) (u .fst) (v .fst) h)

def f2_poly_coeff (u v : f2_poly_carrier) (e : Id f2_poly_carrier u v) (i : Nat) : Id Bool (u .fst i) (v .fst i)
  ≔ refl ((w ↦ w .fst i) : f2_poly_carrier → Bool) e

{` A sequence vanishing below N and from N is zero. `}
def f2_seq_zero (f : Nat → Bool) (N : Nat) (low : SeriesLowZero f2_ring f N) (high : SeriesVanishesFrom f2_ring f N)
  (i : Nat) : Id Bool (f i) false.
  ≔ match nat_split_below N i [
  | inl. h ↦ low i h
  | inr. w ↦ concat Bool (f i) (f (add (w .fst) N)) false. (refl f (w .snd)) (high (w .fst)) ]

{` Lowest true coefficient below N, or none. `}
def f2_first_true (f : Nat → Bool) (N : Nat)
  : Sum (SeriesLowZero f2_ring f N) (Σ Nat (a ↦ Product (Id Bool (f a) true.) (SeriesLowZero f2_ring f a)))
  ≔ match N [
  | zero. ↦ inl. (i h ↦ match h [ ])
  | suc. N ↦ match f2_first_true f N [
    | inr. w ↦ inr. w
    | inl. low ↦ match f2_bool_cases (f N) [
      | inl. e ↦ inr. (N, (e, low))
      | inr. e ↦ inl. (i h ↦ match lt_suc_split i N h [
          | inl. h' ↦ low i h'
          | inr. q ↦ concat Bool (f i) (f N) false. (refl f q) e ]) ] ] ]

def F2Valuation (u : f2_poly_carrier) : Type
  ≔ Σ Nat (a ↦ Product (Id Bool (u .fst a) true.) (SeriesLowZero f2_ring (u .fst) a))

def f2_poly_valuation (u : f2_poly_carrier) (nu : Not (Id f2_poly_carrier u (f2_poly .zero))) : Mere (F2Valuation u)
  ≔ mere_rec (Σ Nat (N ↦ SeriesVanishesFrom f2_ring (u .fst) N)) (Mere (F2Valuation u)) (mere_isprop (F2Valuation u))
      (w ↦ match f2_first_true (u .fst) (w .fst) [
        | inr. v ↦ mere (F2Valuation u) v
        | inl. low ↦ match nu (f2_poly_ext u (f2_poly .zero) (f2_seq_zero (u .fst) (w .fst) low (w .snd))) [ ] ])
      (u .snd)

{` The valuation of a product of polynomials with valuations a and b is b + a. `}
def f2_poly_mul_value (u v : f2_poly_carrier) (ha : F2Valuation u) (hb : F2Valuation v)
  : Id Bool (f2_poly .mul u v .fst (add (hb .fst) (ha .fst))) true.
  ≔ concat Bool (series_mul f2_ring (u .fst) (v .fst) (add (hb .fst) (ha .fst))) (f2_mul (u .fst (ha .fst)) (v .fst (hb .fst))) true.
      (series_mul_low_value f2_ring (u .fst) (v .fst) (hb .fst) (hb .snd .snd) (ha .fst) (ha .snd .snd))
      (refl f2_mul (ha .snd .fst) (hb .snd .fst))

def f2_poly_mul_valuation (u v : f2_poly_carrier) (ha : F2Valuation u) (hb : F2Valuation v) : F2Valuation (f2_poly .mul u v)
  ≔ (add (hb .fst) (ha .fst),
     (f2_poly_mul_value u v ha hb,
      series_mul_low_zero f2_ring (u .fst) (v .fst) (hb .fst) (hb .snd .snd) (ha .fst) (ha .snd .snd)))

def f2_poly_no_zero_divisors (u v : f2_poly_carrier) (nu : Not (Id f2_poly_carrier u (f2_poly .zero)))
  (nv : Not (Id f2_poly_carrier v (f2_poly .zero))) : Not (Id f2_poly_carrier (f2_poly .mul u v) (f2_poly .zero))
  ≔ e ↦ mere_rec (F2Valuation u) Empty empty_prop
      (ha ↦ mere_rec (F2Valuation v) Empty empty_prop
         (hb ↦ f2_true_ne_false
            (concat Bool true. (f2_poly .mul u v .fst (add (hb .fst) (ha .fst))) false.
              (inverse Bool (f2_poly .mul u v .fst (add (hb .fst) (ha .fst))) true. (f2_poly_mul_value u v ha hb))
              (f2_poly_coeff (f2_poly .mul u v) (f2_poly .zero) e (add (hb .fst) (ha .fst)))))
         (f2_poly_valuation v nv))
      (f2_poly_valuation u nu)

{` Decidable equality of 𝔽₂[X]. `}
def f2_decidable_prop (P : Type) (hP : isProp P) : isProp (Decidable P)
  ≔ x y ↦ match x, y [
  | inl. p, inl. q ↦ refl ((t ↦ inl. t) : P → Decidable P) (hP p q)
  | inl. p, inr. n ↦ match n p [ ]
  | inr. n, inl. q ↦ match n q [ ]
  | inr. n, inr. n' ↦ refl ((t ↦ inr. t) : Not P → Decidable P) (negation_prop P n n') ]

def f2_seq_agree_below (f g : Nat → Bool) (N : Nat) : Decidable ((i : Nat) → Lt i N → Id Bool (f i) (g i))
  ≔ match N [
  | zero. ↦ inl. (i h ↦ match h [ ])
  | suc. N ↦ match f2_seq_agree_below f g N [
    | inr. no ↦ inr. (h ↦ no (i hi ↦ h i (lt_le i N hi)))
    | inl. yes ↦ match f2_bool_dec (f N) (g N) [
      | inr. ne ↦ inr. (h ↦ ne (h N (le_refl N)))
      | inl. e ↦ inl. (i h ↦ match lt_suc_split i N h [
          | inl. h' ↦ yes i h'
          | inr. q ↦ concat Bool (f i) (f N) (g i) (refl f q) (concat Bool (f N) (g N) (g i) e (refl g (inverse Nat i N q))) ]) ] ] ]

def f2_poly_dec_bounded (u v : f2_poly_carrier) (N : Nat)
  (hu : SeriesVanishesFrom f2_ring (u .fst) N) (hv : SeriesVanishesFrom f2_ring (v .fst) N) : Decidable (Id f2_poly_carrier u v)
  ≔ match f2_seq_agree_below (u .fst) (v .fst) N [
  | inr. no ↦ inr. (e ↦ no (i _ ↦ f2_poly_coeff u v e i))
  | inl. yes ↦ inl. (f2_poly_ext u v (i ↦ match nat_split_below N i [
      | inl. h ↦ yes i h
      | inr. w ↦ concat Bool (u .fst i) false. (v .fst i)
          (concat Bool (u .fst i) (u .fst (add (w .fst) N)) false. (refl (u .fst) (w .snd)) (hu (w .fst)))
          (inverse Bool (v .fst i) false.
            (concat Bool (v .fst i) (v .fst (add (w .fst) N)) false. (refl (v .fst) (w .snd)) (hv (w .fst)))) ])) ]

def f2_poly_dec (u v : f2_poly_carrier) : Decidable (Id f2_poly_carrier u v)
  ≔ let T ≔ Decidable (Id f2_poly_carrier u v) in
    let hT ≔ f2_decidable_prop (Id f2_poly_carrier u v) (ring_set f2_poly u v) in
    mere_rec (Σ Nat (N ↦ SeriesVanishesFrom f2_ring (u .fst) N)) T hT
      (wu ↦ mere_rec (Σ Nat (N ↦ SeriesVanishesFrom f2_ring (v .fst) N)) T hT
        (wv ↦ f2_poly_dec_bounded u v (add (wu .fst) (wv .fst))
           (vanishes_from_add_right f2_ring (u .fst) (wu .fst) (wu .snd) (wv .fst))
           (vanishes_from_add_left f2_ring (v .fst) (wv .fst) (wv .snd) (wu .fst)))
        (v .snd))
      (u .snd)

def f2_poly_non_trivial : IsNonTrivialRing f2_poly
  ≔ e ↦ bool_encode false. true. (f2_poly_coeff (f2_poly .zero) (f2_poly .one) e zero.)

{` 𝔽₂[X] as a decidable domain. `}
def f2_poly_domain : DecidableDomain
  ≔ (f2_poly, polynomial_ring_commutative f2_ring f2_commutative, f2_poly_non_trivial,
     f2_poly_no_zero_divisors, f2_poly_dec)

{` Characteristic 2: 1 + 1 = 0 in 𝔽₂[X]. `}
def f2_poly_char_two : Id f2_poly_carrier (f2_poly .add (f2_poly .one) (f2_poly .one)) (f2_poly .zero)
  ≔ f2_poly_ext (f2_poly .add (f2_poly .one) (f2_poly .one)) (f2_poly .zero)
      [ zero. ↦ refl (false. : Bool) | suc. _ ↦ refl (false. : Bool) ]

{` The variable X. `}
def f2_poly_x : f2_poly_carrier
  ≔ (series_variable f2_ring,
     mere (Σ Nat (N ↦ SeriesVanishesFrom f2_ring (series_variable f2_ring) N)) (2, _ ↦ refl (false. : Bool)))

def f2_poly_x_valuation : F2Valuation f2_poly_x
  ≔ (1, (refl (true. : Bool), i h ↦ match i [ zero. ↦ refl (false. : Bool) | suc. _ ↦ match h [ ] ]))

{` X q² = p² is impossible for q ≠ 0 (parity of valuations). `}
def f2_poly_square_ratio_zero (p q : f2_poly_carrier) (nq : Not (Id f2_poly_carrier q (f2_poly .zero)))
  (e : Id f2_poly_carrier (f2_poly .mul p p) (f2_poly .mul f2_poly_x (f2_poly .mul q q))) : Empty
  ≔ let P ≔ f2_poly_carrier in
    let xqq ≔ f2_poly .mul f2_poly_x (f2_poly .mul q q) in
    let pp ≔ f2_poly .mul p p in
    mere_rec (F2Valuation q) Empty empty_prop
      (hq ↦
        let vr ≔ f2_poly_mul_valuation f2_poly_x (f2_poly .mul q q) f2_poly_x_valuation (f2_poly_mul_valuation q q hq hq) in
        let t ≔ vr .fst in
        match f2_poly_dec p (f2_poly .zero) [
        | inl. ep ↦ f2_true_ne_false
            (calc
               (true. : Bool) = xqq .fst t by inverse Bool (xqq .fst t) true. (vr .snd .fst)
               = pp .fst t by inverse Bool (pp .fst t) (xqq .fst t) (f2_poly_coeff pp xqq e t)
               = false. by series_mul_zero_left f2_ring (p .fst) (p .fst) (k ↦ f2_poly_coeff p (f2_poly .zero) ep k) t ∎)
        | inr. np ↦ mere_rec (F2Valuation p) Empty empty_prop
            (hp ↦
              let vl ≔ f2_poly_mul_valuation p p hp hp in
              let c2 ≔ vl .fst in
              match lt_decidable c2 t [
              | inl. lt ↦ f2_true_ne_false
                  (calc
                     (true. : Bool) = pp .fst c2 by inverse Bool (pp .fst c2) true. (vl .snd .fst)
                     = xqq .fst c2 by f2_poly_coeff pp xqq e c2
                     = false. by vr .snd .snd c2 lt ∎)
              | inr. nlt ↦ match lt_decidable t c2 [
                | inl. lt2 ↦ f2_true_ne_false
                    (calc
                       (true. : Bool) = xqq .fst t by inverse Bool (xqq .fst t) true. (vr .snd .fst)
                       = pp .fst t by inverse Bool (pp .fst t) (xqq .fst t) (f2_poly_coeff pp xqq e t)
                       = false. by vl .snd .snd t lt2 ∎)
                | inr. nlt2 ↦ nat_double_ne_odd (hp .fst) (hq .fst)
                    (le_antisym c2 t (nat_le_of_not_lt c2 t nlt2) (nat_le_of_not_lt t c2 nlt)) ] ])
            (f2_poly_valuation p np) ])
      (f2_poly_valuation q nq)
