export "1312-power-series"

{` Chapter 13 (fields.tex), exa:ring-Z-polynomials (line 89; the printed
   body is the stub "We elaborate the abstract ring of polynomials with
   integer coefficients. TBD"). R[x] is the subring of R[[x]] (module 1312)
   of the series that merely vanish from some index on:
     IsPolynomialSeries R f = ‖Σ (N : Nat), Π (k : Nat), f(k + N) = 0‖.
   The predicate is a proposition, so the carrier Σ (Nat → R) IsPolynomial
   is a set, and two polynomials are equal when their coefficient
   sequences are. The subring is built by the general closed_subring (a
   predicate closed under 0, 1, +, -, ·). If f vanishes from N and g from
   M, then f + g vanishes from N + M and f g from M + N. The book's ℤ[x] is
   integer_polynomial_ring, commutative and non-trivial; litmus
   (1 + x)² = 1 + 2x + x², and the geometric series is not a polynomial. `}

{` A subset closed under the ring operations is a ring (the operations are
   those of R on the first components; all laws hold since equality in
   the subtype is equality of first components). `}
def closed_subring (R : AbstractRing) (P : R .carrier → Type) (hP : (a : R .carrier) → isProp (P a))
  (hz : P (R .zero)) (ho : P (R .one))
  (ha : (a b : R .carrier) → P a → P b → P (R .add a b))
  (hn : (a : R .carrier) → P a → P (R .neg a))
  (hm : (a b : R .carrier) → P a → P b → P (R .mul a b))
  : AbstractRing
  ≔ let S ≔ R .carrier in
    let T ≔ Σ S P in
    let eq : (u v : T) → Id S (u .fst) (v .fst) → Id T u v ≔ subtype_equal S P hP in
    let add : T → T → T ≔ u v ↦ (R .add (u .fst) (v .fst), ha (u .fst) (v .fst) (u .snd) (v .snd)) in
    let neg : T → T ≔ u ↦ (R .neg (u .fst), hn (u .fst) (u .snd)) in
    let mul : T → T → T ≔ u v ↦ (R .mul (u .fst) (v .fst), hm (u .fst) (v .fst) (u .snd) (v .snd)) in
    let zero : T ≔ (R .zero, hz) in
    let one : T ≔ (R .one, ho) in
    let tset : isSet T ≔ sigma_set S P (ring_set R) (a ↦ prop_is_set (P a) (hP a)) in
    (T, zero, add, neg,
     (tset,
      u ↦ eq (add u zero) u (R .add_laws .unit_right (u .fst)),
      u ↦ eq (add zero u) u (R .add_laws .unit_left (u .fst)),
      u v w ↦ eq (add u (add v w)) (add (add u v) w) (R .add_laws .assoc (u .fst) (v .fst) (w .fst)),
      u ↦ eq (add u (neg u)) zero (R .add_laws .inv_right (u .fst))),
     one, mul,
     (tset,
      (u ↦ (eq (mul u one) u (ring_mul_one_right R (u .fst)), eq (mul one u) u (ring_mul_one_left R (u .fst))),
       u v w ↦ eq (mul u (mul v w)) (mul (mul u v) w) (ring_mul_assoc R (u .fst) (v .fst) (w .fst)))),
     (u v w ↦ eq (mul u (add v w)) (add (mul u v) (mul u w)) (ring_ldistr R (u .fst) (v .fst) (w .fst)),
      u v w ↦ eq (mul (add u v) w) (add (mul u w) (mul v w)) (ring_rdistr R (u .fst) (v .fst) (w .fst))))

{` The inclusion of a closed subring is a ring homomorphism. `}
def closed_subring_inclusion (R : AbstractRing) (P : R .carrier → Type) (hP : (a : R .carrier) → isProp (P a))
  (hz : P (R .zero)) (ho : P (R .one))
  (ha : (a b : R .carrier) → P a → P b → P (R .add a b))
  (hn : (a : R .carrier) → P a → P (R .neg a))
  (hm : (a b : R .carrier) → P a → P b → P (R .mul a b))
  : RingHom (closed_subring R P hP hz ho ha hn hm) R
  ≔ ((u ↦ u .fst, u v ↦ refl (R .add (u .fst) (v .fst))), (refl (R .one), u v ↦ refl (R .mul (u .fst) (v .fst))))

def SeriesVanishesFrom (R : AbstractRing) (f : Nat → R .carrier) (N : Nat) : Type
  ≔ (k : Nat) → Id (R .carrier) (f (add k N)) (R .zero)

def IsPolynomialSeries (R : AbstractRing) (f : Nat → R .carrier) : Type
  ≔ Mere (Σ Nat (N ↦ SeriesVanishesFrom R f N))

def is_polynomial_series_prop (R : AbstractRing) (f : Nat → R .carrier) : isProp (IsPolynomialSeries R f)
  ≔ mere_isprop (Σ Nat (N ↦ SeriesVanishesFrom R f N))

def vanishes_from_add_left (R : AbstractRing) (f : Nat → R .carrier) (N : Nat) (h : SeriesVanishesFrom R f N)
  (K : Nat) : SeriesVanishesFrom R f (add K N)
  ≔ k ↦ concat (R .carrier) (f (add k (add K N))) (f (add (add k K) N)) (R .zero)
      (refl f (inverse Nat (add (add k K) N) (add k (add K N)) (add_assoc k K N))) (h (add k K))

def vanishes_from_add_right (R : AbstractRing) (f : Nat → R .carrier) (N : Nat) (h : SeriesVanishesFrom R f N)
  (K : Nat) : SeriesVanishesFrom R f (add N K)
  ≔ k ↦ concat (R .carrier) (f (add k (add N K))) (f (add k (add K N))) (R .zero)
      (refl ((j ↦ f (add k j)) : Nat → R .carrier) (add_comm N K)) (vanishes_from_add_left R f N h K k)

def series_add_vanishes (R : AbstractRing) (f g : Nat → R .carrier) (N M : Nat)
  (hf : SeriesVanishesFrom R f N) (hg : SeriesVanishesFrom R g M)
  : SeriesVanishesFrom R (series_add R f g) (add N M)
  ≔ k ↦ concat (R .carrier) (R .add (f (add k (add N M))) (g (add k (add N M)))) (R .add (R .zero) (R .zero)) (R .zero)
      (refl (R .add) (vanishes_from_add_right R f N hf M k) (vanishes_from_add_left R g M hg N k))
      (R .add_laws .unit_right (R .zero))

def series_neg_vanishes (R : AbstractRing) (f : Nat → R .carrier) (N : Nat) (hf : SeriesVanishesFrom R f N)
  : SeriesVanishesFrom R (k ↦ R .neg (f k)) N
  ≔ k ↦ concat (R .carrier) (R .neg (f (add k N))) (R .neg (R .zero)) (R .zero)
      (refl (R .neg) (hf k)) (ag_inv_unit (ring_additive_group R))

{` If g vanishes from M and f from N, then f g vanishes from M + N (by
   induction on N: for N = 0 f is zero; otherwise (f g)_(j+1) =
   f_0 g_(j+1) + ((shift f) g)_j, where g_(j+1) = 0 and shift f vanishes
   from N - 1). `}
def series_mul_vanishes (R : AbstractRing) (f g : Nat → R .carrier) (M : Nat) (hg : SeriesVanishesFrom R g M)
  (N : Nat) (hf : SeriesVanishesFrom R f N)
  : SeriesVanishesFrom R (series_mul R f g) (add M N)
  ≔ let S ≔ R .carrier in let z ≔ R .zero in
    match N [
  | zero. ↦ k ↦ series_mul_zero_left R f g hf (add k M)
  | suc. N ↦ k ↦
    let j ≔ add k (add M N) in
    let e : Id Nat (suc. j) (add (suc. (add k N)) M)
      ≔ calc
          (suc. j : Nat) = suc. (add k (add N M)) by refl ((i ↦ suc. (add k i)) : Nat → Nat) (add_comm M N)
          = suc. (add (add k N) M) by suc. (inverse Nat (add (add k N) M) (add k (add N M)) (add_assoc k N M))
          = add (suc. (add k N)) M
            by inverse Nat (add (suc. (add k N)) M) (suc. (add (add k N) M)) (add_suc_left (add k N) M) ∎ in
    calc
      R .add (R .mul (f zero.) (g (suc. j))) (series_mul R (series_shift R f) g j) = R .add z z
        by refl (R .add)
          (concat S (R .mul (f zero.) (g (suc. j))) (R .mul (f zero.) z) z
            (refl (R .mul (f zero.)) (concat S (g (suc. j)) (g (add (suc. (add k N)) M)) z (refl g e) (hg (suc. (add k N)))))
            (ring_mul_zero_right R (f zero.)))
          (series_mul_vanishes R (series_shift R f) g M hg N hf k)
      = z by R .add_laws .unit_right z ∎ ]

def polynomial_zero_closed (R : AbstractRing) : IsPolynomialSeries R (_ ↦ R .zero)
  ≔ mere (Σ Nat (N ↦ SeriesVanishesFrom R (_ ↦ R .zero) N)) (zero., _ ↦ refl (R .zero))

def polynomial_one_closed (R : AbstractRing) : IsPolynomialSeries R (series_one R)
  ≔ mere (Σ Nat (N ↦ SeriesVanishesFrom R (series_one R) N)) (1, _ ↦ refl (R .zero))

def polynomial_add_closed (R : AbstractRing) (f g : Nat → R .carrier)
  (pf : IsPolynomialSeries R f) (pg : IsPolynomialSeries R g) : IsPolynomialSeries R (series_add R f g)
  ≔ let B ≔ Σ Nat (N ↦ SeriesVanishesFrom R (series_add R f g) N) in
    mere_rec (Σ Nat (N ↦ SeriesVanishesFrom R f N)) (Mere B) (mere_isprop B)
      (u ↦ mere_rec (Σ Nat (M ↦ SeriesVanishesFrom R g M)) (Mere B) (mere_isprop B)
        (v ↦ mere B (add (u .fst) (v .fst), series_add_vanishes R f g (u .fst) (v .fst) (u .snd) (v .snd))) pg) pf

def polynomial_neg_closed (R : AbstractRing) (f : Nat → R .carrier) (pf : IsPolynomialSeries R f)
  : IsPolynomialSeries R (k ↦ R .neg (f k))
  ≔ let B ≔ Σ Nat (N ↦ SeriesVanishesFrom R (k ↦ R .neg (f k)) N) in
    mere_rec (Σ Nat (N ↦ SeriesVanishesFrom R f N)) (Mere B) (mere_isprop B)
      (u ↦ mere B (u .fst, series_neg_vanishes R f (u .fst) (u .snd))) pf

def polynomial_mul_closed (R : AbstractRing) (f g : Nat → R .carrier)
  (pf : IsPolynomialSeries R f) (pg : IsPolynomialSeries R g) : IsPolynomialSeries R (series_mul R f g)
  ≔ let B ≔ Σ Nat (N ↦ SeriesVanishesFrom R (series_mul R f g) N) in
    mere_rec (Σ Nat (N ↦ SeriesVanishesFrom R f N)) (Mere B) (mere_isprop B)
      (u ↦ mere_rec (Σ Nat (M ↦ SeriesVanishesFrom R g M)) (Mere B) (mere_isprop B)
        (v ↦ mere B (add (v .fst) (u .fst), series_mul_vanishes R f g (v .fst) (v .snd) (u .fst) (u .snd))) pg) pf

{` R[x]: polynomials with coefficients in R. `}
def polynomial_ring (R : AbstractRing) : AbstractRing
  ≔ closed_subring (power_series_ring R) (IsPolynomialSeries R) (is_polynomial_series_prop R)
      (polynomial_zero_closed R) (polynomial_one_closed R) (polynomial_add_closed R)
      (polynomial_neg_closed R) (polynomial_mul_closed R)

def polynomial_series_inclusion (R : AbstractRing) : RingHom (polynomial_ring R) (power_series_ring R)
  ≔ closed_subring_inclusion (power_series_ring R) (IsPolynomialSeries R) (is_polynomial_series_prop R)
      (polynomial_zero_closed R) (polynomial_one_closed R) (polynomial_add_closed R)
      (polynomial_neg_closed R) (polynomial_mul_closed R)

def polynomial_ring_commutative (R : AbstractRing) (hc : IsCommutativeRing R)
  : IsCommutativeRing (polynomial_ring R)
  ≔ u v ↦ subtype_equal (Nat → R .carrier) (IsPolynomialSeries R) (is_polynomial_series_prop R)
      (polynomial_ring R .mul u v) (polynomial_ring R .mul v u)
      (power_series_ring_commutative R hc (u .fst) (v .fst))

{` exa:ring-Z-polynomials: ℤ[x]. `}
def integer_polynomial_ring : AbstractRing ≔ polynomial_ring integer_ring

def integer_polynomial_ring_commutative : IsCommutativeRing integer_polynomial_ring
  ≔ polynomial_ring_commutative integer_ring integer_ring_commutative

def integer_polynomial_ring_non_trivial : IsNonTrivialRing integer_polynomial_ring
  ≔ p ↦ int_encode int_zero int_one (refl ((u ↦ u .fst 0) : integer_polynomial_ring .carrier → Int) p)

{` Litmus: x and 1 + x are polynomials; (1 + x)² has coefficients
   1, 2, 1, 0 and x · x = x², by computation. `}
def integer_polynomial_variable : integer_polynomial_ring .carrier
  ≔ (series_variable integer_ring,
     mere (Σ Nat (N ↦ SeriesVanishesFrom integer_ring (series_variable integer_ring) N)) (2, _ ↦ refl int_zero))

def int_one_plus_x : Nat → Int ≔ [ zero. ↦ int_one | suc. zero. ↦ int_one | suc. (suc. _) ↦ int_zero ]

def integer_polynomial_one_plus_x : integer_polynomial_ring .carrier
  ≔ (int_one_plus_x, mere (Σ Nat (N ↦ SeriesVanishesFrom integer_ring int_one_plus_x N)) (2, _ ↦ refl int_zero))

def integer_polynomial_litmus_square
  : Id (Product Int (Product Int (Product Int Int)))
      (integer_polynomial_ring .mul integer_polynomial_one_plus_x integer_polynomial_one_plus_x .fst 0,
       (integer_polynomial_ring .mul integer_polynomial_one_plus_x integer_polynomial_one_plus_x .fst 1,
        (integer_polynomial_ring .mul integer_polynomial_one_plus_x integer_polynomial_one_plus_x .fst 2,
         integer_polynomial_ring .mul integer_polynomial_one_plus_x integer_polynomial_one_plus_x .fst 3)))
      (int_one, (pos. 2, (int_one, int_zero)))
  ≔ refl ((int_one, (pos. 2, (int_one, int_zero))) : Product Int (Product Int (Product Int Int)))

def integer_polynomial_litmus_one_plus_x
  : Id (integer_polynomial_ring .carrier) integer_polynomial_one_plus_x
      (integer_polynomial_ring .add (integer_polynomial_ring .one) integer_polynomial_variable)
  ≔ subtype_equal (Nat → Int) (IsPolynomialSeries integer_ring) (is_polynomial_series_prop integer_ring)
      integer_polynomial_one_plus_x
      (integer_polynomial_ring .add (integer_polynomial_ring .one) integer_polynomial_variable)
      (funext Nat (_ ↦ Int) int_one_plus_x
        (integer_polynomial_ring .add (integer_polynomial_ring .one) integer_polynomial_variable .fst)
        [ zero. ↦ refl int_one | suc. zero. ↦ refl int_one | suc. (suc. _) ↦ refl int_zero ])

{` The geometric series 1 + x + x² + … (module 1312) is not a polynomial:
   it vanishes from no index. `}
def geometric_series_not_polynomial : Not (IsPolynomialSeries integer_ring int_geometric_series)
  ≔ mere_rec (Σ Nat (N ↦ SeriesVanishesFrom integer_ring int_geometric_series N)) Empty empty_prop
      (u ↦ int_encode int_one int_zero (u .snd zero.))
