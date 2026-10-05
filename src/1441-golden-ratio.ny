export "1413-dimension-invariance"

{` Chapter 14, the golden ratio φ = (1 + √5)/2 in a Euclidean field K
   (geometry.tex 298), with φ² = φ + 1 and φ ≥ 0, and the uniqueness of
   non-negative square roots (used to evaluate lengths such as √4 = 2).
   2 = 1 + 1 is invertible because K is ordered (characteristic 0). `}

def ef_two (K : EuclideanField) : ef_carrier K ≔ K .field .fst .add (K .field .fst .one) (K .field .fst .one)

def ef_two_nonzero (K : EuclideanField) : Not (Id (ef_carrier K) (ef_two K) (K .field .fst .zero))
  ≔ p ↦
    let R ≔ K .field .fst in let S ≔ R .carrier in let o ≔ R .one in
    ef_nat_succ_nonzero K 1
      (concat S (R .add (R .add (R .zero) o) o) (R .add o o) (R .zero)
        (refl ((y ↦ R .add y o) : S → S) (R .add_laws .unit_left o)) p)

def ef_two_nonneg (K : EuclideanField) : K .nonneg (ef_two K)
  ≔ K .nonneg_add (K .field .fst .one) (K .field .fst .one) (ef_one_nonneg K) (ef_one_nonneg K)

def ef_half_witness (K : EuclideanField) : InverseWitness (K .field .fst) (ef_two K) ≔ ef_inv K (ef_two K) (ef_two_nonzero K)

def ef_half (K : EuclideanField) : ef_carrier K ≔ ef_half_witness K .fst

{` Commutative ring rearrangements. `}
def cring_mul_interchange (R : AbstractRing) (hc : IsCommutativeRing R) (c d x y : R .carrier)
  : Id (R .carrier) (R .mul c (R .mul d (R .mul x y))) (R .mul (R .mul c x) (R .mul d y))
  ≔ let S ≔ R .carrier in let m ≔ R .mul in
    calc
      m c (m d (m x y)) = m c (m (m d x) y) by refl (m c) (ring_mul_assoc R d x y)
      = m c (m (m x d) y) by refl ((t ↦ m c (m t y)) : S → S) (hc d x)
      = m c (m x (m d y)) by refl (m c) (inverse S (m x (m d y)) (m (m x d) y) (ring_mul_assoc R x d y))
      = m (m c x) (m d y) by ring_mul_assoc R c x (m d y) ∎

{` Cancellation of an invertible factor. `}
def ring_cancel_invertible (R : AbstractRing) (c : R .carrier) (w : InverseWitness R c) (x y : R .carrier)
  (p : Id (R .carrier) (R .mul c x) (R .mul c y)) : Id (R .carrier) x y
  ≔ let S ≔ R .carrier in let m ≔ R .mul in let h ≔ w .fst in
    calc
      x = m (R .one) x by inverse S (m (R .one) x) x (ring_mul_one_left R x)
      = m (m h c) x by refl ((t ↦ m t x) : S → S) (inverse S (m h c) (R .one) (w .snd .snd))
      = m h (m c x) by inverse S (m h (m c x)) (m (m h c) x) (ring_mul_assoc R h c x)
      = m h (m c y) by refl (m h) p
      = m (m h c) y by ring_mul_assoc R h c y
      = m (R .one) y by refl ((t ↦ m t y) : S → S) (w .snd .snd)
      = y by ring_mul_one_left R y ∎

{` (1 + 1) x = x + x. `}
def ring_two_mul (R : AbstractRing) (x : R .carrier)
  : Id (R .carrier) (R .mul (R .add (R .one) (R .one)) x) (R .add x x)
  ≔ concat (R .carrier) (R .mul (R .add (R .one) (R .one)) x) (R .add (R .mul (R .one) x) (R .mul (R .one) x)) (R .add x x)
      (ring_rdistr R (R .one) (R .one) x) (refl (R .add) (ring_mul_one_left R x) (ring_mul_one_left R x))

{` n·1 for n + 2 is (n·1) + 2. `}
def ring_of_nat_add_two (R : AbstractRing) (k : Nat)
  : Id (R .carrier) (ring_of_nat R (suc. (suc. k))) (R .add (ring_of_nat R k) (R .add (R .one) (R .one)))
  ≔ inverse (R .carrier) (R .add (ring_of_nat R k) (R .add (R .one) (R .one))) (R .add (R .add (ring_of_nat R k) (R .one)) (R .one))
      (ring_add_assoc R (ring_of_nat R k) (R .one) (R .one))

{` 2·2 = 4. `}
def ef_two_square (K : EuclideanField)
  : Id (ef_carrier K) (K .field .fst .mul (ef_two K) (ef_two K)) (ring_of_nat (K .field .fst) 4)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let o ≔ R .one in let t ≔ ef_two K in
    calc
      R .mul t t = R .add t t by ring_two_mul R t
      = R .add (R .add t o) o by ring_add_assoc R t o o
      = ring_of_nat R 4 by refl ((y ↦ R .add (R .add (R .add y o) o) o) : S → S)
          (inverse S (R .add (R .zero) o) o (R .add_laws .unit_left o)) ∎

{` The golden ratio φ = (1 + √5) · 2⁻¹. `}
def ef_sqrt_five (K : EuclideanField) : ef_carrier K
  ≔ K .sqrt (ring_of_nat (K .field .fst) 5) (ef_nat_nonneg K 5)

def golden_ratio (K : EuclideanField) : ef_carrier K
  ≔ K .field .fst .mul (K .field .fst .add (K .field .fst .one) (ef_sqrt_five K)) (ef_half K)

{` 2φ = 1 + √5. `}
def golden_ratio_double (K : EuclideanField)
  : Id (ef_carrier K) (K .field .fst .mul (ef_two K) (golden_ratio K)) (K .field .fst .add (K .field .fst .one) (ef_sqrt_five K))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let m ≔ R .mul in
    let t ≔ ef_two K in let h ≔ ef_half K in let w ≔ R .add (R .one) (ef_sqrt_five K) in
    calc
      m t (m w h) = m (m t w) h by ring_mul_assoc R t w h
      = m (m w t) h by refl ((x ↦ m x h) : S → S) (ef_commutative K t w)
      = m w (m t h) by inverse S (m w (m t h)) (m (m w t) h) (ring_mul_assoc R w t h)
      = m w (R .one) by refl (m w) (ef_half_witness K .snd .fst)
      = w by ring_mul_one_right R w ∎

{` (1 + s)(1 + s) = 2(1 + s) + 2·2 when s² = 5. `}
def golden_core_identity (K : EuclideanField)
  : Id (ef_carrier K)
      (K .field .fst .mul (K .field .fst .add (K .field .fst .one) (ef_sqrt_five K)) (K .field .fst .add (K .field .fst .one) (ef_sqrt_five K)))
      (K .field .fst .add (K .field .fst .mul (ef_two K) (K .field .fst .add (K .field .fst .one) (ef_sqrt_five K)))
        (K .field .fst .mul (ef_two K) (ef_two K)))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let m ≔ R .mul in let a ≔ R .add in
    let o ≔ R .one in let s ≔ ef_sqrt_five K in let w ≔ a o s in let t ≔ ef_two K in
    let G ≔ ring_additive_group R in let hab ≔ ring_additive_abelian R in
    let five ≔ ring_of_nat R 5 in
    let six ≔ ring_of_nat R 6 in
    let lhs : Id S (m w w) (a six (a s s))
      ≔ calc
          m w w = a (m o w) (m s w) by ring_rdistr R o s w
          = a w (a (m s o) (m s s)) by refl (a) (ring_mul_one_left R w) (ring_ldistr R s o s)
          = a w (a s five) by refl ((y ↦ a w y) : S → S)
              (refl (a) (ring_mul_one_right R s) (K .sqrt_square five (ef_nat_nonneg K 5)))
          = a w (a five s) by refl (a w) (ring_add_comm R s five)
          = a (a o five) (a s s) by abstract_abelian_interchange G hab o s five s
          = a six (a s s) by refl ((y ↦ a y (a s s)) : S → S) (ring_add_comm R o five) ∎ in
    let rhs : Id S (a (m t w) (m t t)) (a six (a s s))
      ≔ calc
          a (m t w) (m t t) = a (a w w) (a t t) by refl (a) (ring_two_mul R w) (ring_two_mul R t)
          = a (a (a o o) (a s s)) (a t t) by refl ((y ↦ a y (a t t)) : S → S) (abstract_abelian_interchange G hab o s o s)
          = a (a t (a s s)) (a t t) by refl (a (a t (a s s))) (refl (a t t))
          = a t (a (a s s) (a t t)) by inverse S (a t (a (a s s) (a t t))) (a (a t (a s s)) (a t t)) (ring_add_assoc R t (a s s) (a t t))
          = a t (a (a t t) (a s s)) by refl (a t) (ring_add_comm R (a s s) (a t t))
          = a (a t (a t t)) (a s s) by ring_add_assoc R t (a t t) (a s s)
          = a (a (a t t) t) (a s s) by refl ((y ↦ a y (a s s)) : S → S) (ring_add_comm R t (a t t))
          = a six (a s s) by refl ((y ↦ a y (a s s)) : S → S)
              (calc
                 a (a t t) t = a (a (ring_of_nat R 2) t) t
                   by refl ((y ↦ a (a y t) t) : S → S)
                     (inverse S (ring_of_nat R 2) t
                       (concat S (ring_of_nat R 2) (a (R .zero) t) t (ring_of_nat_add_two R 0) (R .add_laws .unit_left t)))
                 = a (ring_of_nat R 4) t
                   by refl ((y ↦ a y t) : S → S) (inverse S (ring_of_nat R 4) (a (ring_of_nat R 2) t) (ring_of_nat_add_two R 2))
                 = six by inverse S six (a (ring_of_nat R 4) t) (ring_of_nat_add_two R 4) ∎) ∎ in
    concat S (m w w) (a six (a s s)) (a (m t w) (m t t)) lhs (inverse S (a (m t w) (m t t)) (a six (a s s)) rhs)

{` φ² = φ + 1. `}
def golden_ratio_square (K : EuclideanField)
  : Id (ef_carrier K) (K .field .fst .mul (golden_ratio K) (golden_ratio K)) (K .field .fst .add (golden_ratio K) (K .field .fst .one))
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let m ≔ R .mul in let a ≔ R .add in
    let o ≔ R .one in let t ≔ ef_two K in let φ ≔ golden_ratio K in
    let w ≔ a o (ef_sqrt_five K) in
    let tw ≔ ef_half_witness K in
    ring_cancel_invertible R t tw (m φ φ) (a φ o)
      (ring_cancel_invertible R t tw (m t (m φ φ)) (m t (a φ o))
        (calc
           m t (m t (m φ φ)) = m (m t φ) (m t φ) by cring_mul_interchange R (ef_commutative K) t t φ φ
           = m w w by refl (m) (golden_ratio_double K) (golden_ratio_double K)
           = a (m t w) (m t t) by golden_core_identity K
           = a (m t (m t φ)) (m t t) by refl ((y ↦ a (m t y) (m t t)) : S → S) (inverse S (m t φ) w (golden_ratio_double K))
           = m t (a (m t φ) t) by inverse S (m t (a (m t φ) t)) (a (m t (m t φ)) (m t t)) (ring_ldistr R t (m t φ) t)
           = m t (a (m t φ) (m t o)) by refl ((y ↦ m t (a (m t φ) y)) : S → S) (inverse S (m t o) t (ring_mul_one_right R t))
           = m t (m t (a φ o)) by refl (m t) (inverse S (m t (a φ o)) (a (m t φ) (m t o)) (ring_ldistr R t φ o)) ∎))

{` φ ≥ 0: 2⁻¹ = 2·(2⁻¹)² ≥ 0 and 1 + √5 ≥ 0. `}
def ef_half_nonneg (K : EuclideanField) : K .nonneg (ef_half K)
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let h ≔ ef_half K in let t ≔ ef_two K in
    ef_transport_nonneg K (R .mul t (R .mul h h)) h
      (calc
         R .mul t (R .mul h h) = R .mul (R .mul t h) h by ring_mul_assoc R t h h
         = R .mul (R .one) h by refl ((x ↦ R .mul x h) : S → S) (ef_half_witness K .snd .fst)
         = h by ring_mul_one_left R h ∎)
      (K .nonneg_mul t (R .mul h h) (ef_two_nonneg K) (K .nonneg_square h))

def golden_ratio_nonneg (K : EuclideanField) : K .nonneg (golden_ratio K)
  ≔ let R ≔ K .field .fst in
    K .nonneg_mul (R .add (R .one) (ef_sqrt_five K)) (ef_half K)
      (K .nonneg_add (R .one) (ef_sqrt_five K) (ef_one_nonneg K) (K .sqrt_nonneg (ring_of_nat R 5) (ef_nat_nonneg K 5)))
      (ef_half_nonneg K)

{` Non-negative square roots are unique: if t ≥ 0 and t² = a then √a = t.
   (r - t)(r + t) = 0 for r = √a; if r - t were invertible then r + t = 0,
   so r = t = 0 by antisymmetry, contradicting invertibility; hence r - t is
   not invertible, so it is 0 (K is a field). `}
def ring_diff_sum_product (R : AbstractRing) (hc : IsCommutativeRing R) (r t : R .carrier)
  : Id (R .carrier) (R .mul (R .add r (R .neg t)) (R .add r t))
      (R .add (R .add (R .mul r r) (R .mul r t)) (R .neg (R .add (R .mul r t) (R .mul t t))))
  ≔ let S ≔ R .carrier in let m ≔ R .mul in let a ≔ R .add in let G ≔ ring_additive_group R in
    calc
      m (a r (R .neg t)) (a r t) = a (m r (a r t)) (m (R .neg t) (a r t)) by ring_rdistr R r (R .neg t) (a r t)
      = a (a (m r r) (m r t)) (R .neg (m t (a r t)))
        by refl (a) (ring_ldistr R r r t) (ring_mul_neg_left R t (a r t))
      = a (a (m r r) (m r t)) (R .neg (a (m t r) (m t t))) by refl ((y ↦ a (a (m r r) (m r t)) (R .neg y)) : S → S) (ring_ldistr R t r t)
      = a (a (m r r) (m r t)) (R .neg (a (m r t) (m t t)))
        by refl ((y ↦ a (a (m r r) (m r t)) (R .neg (a y (m t t)))) : S → S) (hc t r) ∎

def ef_sqrt_unique (K : EuclideanField) (x : ef_carrier K) (hx : K .nonneg x) (t : ef_carrier K) (ht : K .nonneg t)
  (p : Id (ef_carrier K) (K .field .fst .mul t t) x)
  : Id (ef_carrier K) (K .sqrt x hx) t
  ≔ let R ≔ K .field .fst in let S ≔ R .carrier in let m ≔ R .mul in let a ≔ R .add in
    let G ≔ ring_additive_group R in
    let r ≔ K .sqrt x hx in let hr ≔ K .sqrt_nonneg x hx in
    let rr : Id S (m r r) (m t t) ≔ concat S (m r r) x (m t t) (K .sqrt_square x hx) (inverse S (m t t) x p) in
    let prod0 : Id S (m (a r (R .neg t)) (a r t)) (R .zero)
      ≔ calc
          m (a r (R .neg t)) (a r t) = a (a (m r r) (m r t)) (R .neg (a (m r t) (m t t))) by ring_diff_sum_product R (ef_commutative K) r t
          = a (a (m r r) (m r t)) (R .neg (a (m r t) (m r r)))
            by refl ((y ↦ a (a (m r r) (m r t)) (R .neg (a (m r t) y))) : S → S) (inverse S (m r r) (m t t) rr)
          = a (a (m r r) (m r t)) (R .neg (a (m r r) (m r t)))
            by refl ((y ↦ a (a (m r r) (m r t)) (R .neg y)) : S → S) (ring_add_comm R (m r t) (m r r))
          = R .zero by R .add_laws .inv_right (a (m r r) (m r t)) ∎ in
    let d ≔ a r (R .neg t) in
    let notinv : Not (IsInvertible R d)
      ≔ hinv ↦
        let w ≔ invertible_witness R d hinv in let y ≔ w .fst in
        let sum0 : Id S (a r t) (R .zero)
          ≔ calc
              a r t = m (R .one) (a r t) by inverse S (m (R .one) (a r t)) (a r t) (ring_mul_one_left R (a r t))
              = m (m y d) (a r t) by refl ((z ↦ m z (a r t)) : S → S) (inverse S (m y d) (R .one) (w .snd .snd))
              = m y (m d (a r t)) by inverse S (m y (m d (a r t))) (m (m y d) (a r t)) (ring_mul_assoc R y d (a r t))
              = m y (R .zero) by refl (m y) prod0
              = R .zero by ring_mul_zero_right R y ∎ in
        let r0 ≔ ef_sum_zero_left K r t hr ht sum0 in
        let t0 ≔ ef_sum_zero_right K r t hr ht sum0 in
        let d0 : Id S d (R .zero)
          ≔ calc
              d = a (R .zero) (R .neg (R .zero)) by refl (a) r0 (refl (R .neg) t0)
              = R .zero by R .add_laws .inv_right (R .zero) ∎ in
        ef_non_trivial K
          (calc
             R .zero = m (R .zero) y by inverse S (m (R .zero) y) (R .zero) (ring_mul_zero_left R y)
             = m d y by refl ((z ↦ m z y) : S → S) (inverse S d (R .zero) d0)
             = R .one by w .snd .fst ∎) in
    let dz ≔ field_non_invertible_zero R (K .field .snd) d notinv in
    concat S r (R .neg (R .neg t)) t (ag_inv_unique_left G (R .neg t) r dz) (ag_inv_inv G t)
