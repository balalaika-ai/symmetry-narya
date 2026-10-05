export "02-restriction-algebraic"
export "bridge-01-galois-group"
export "../../../src/1532-rational-function-counterexample"

{` Bridges helpers for defn:algebraic-element: comparison of the blind
   polynomial evaluation with ours.

   blind_poly_eval sums i(a s)·α^{fin_index s} over s : Fin(n+1), and
   fin_index enumerates Fin(n+1) in the reverse of our order (fin_index
   (inr ★) = 0, fin_index (inl s) = fin_index s + 1), while our poly_value
   gives inr ★ the top index n. Both are compared with the coefficient-
   sequence form Σ_{k ≤ n} c(k) α^k (bpoly_series_sum): the blind sum
   equals it for the coefficient sequence bpoly_blind_coeffs n b
   (bpoly_blind_sum), and poly_value with the family j ↦ c(our index of j)
   equals it (bpoly_our_sum). bpoly_our_coeffs and bpoly_blind_coeffs
   recover the coefficient sequences of a family in either order. The
   corrected blind notion ("not all coefficients zero") then implies ours
   ("top coefficient nonzero") given decidable equality of k (the top
   nonzero coefficient is found by search, bpoly_top_nonzero), and ours
   implies the blind one unconditionally. `}

def bridge_ring_pow (R : AbstractRing) (x : R .carrier) (n : Nat)
  : Id (R .carrier) (blind_ring_pow R x n) (ring_power R x n)
  ≔ match n [
  | zero. ↦ refl (R .one)
  | suc. n ↦ refl ((y ↦ R .mul y x) : R .carrier → R .carrier) (bridge_ring_pow R x n) ]

def le_n_suc (n : Nat) : Le n (suc. n) ≔ match n [ zero. ↦ star. | suc. n ↦ le_n_suc n ]

{` Σ_{k<N} c(k) x^k. `}
def bpoly_series_sum (R : AbstractRing) (x : R .carrier) (c : Nat → R .carrier) (N : Nat) : R .carrier
  ≔ match N [
  | zero. ↦ R .zero
  | suc. N ↦ R .add (bpoly_series_sum R x c N) (R .mul (c N) (ring_power R x N)) ]

def bpoly_series_sum_ext (R : AbstractRing) (x : R .carrier) (c d : Nat → R .carrier) (N : Nat)
  (h : (k : Nat) → Lt k N → Id (R .carrier) (c k) (d k))
  : Id (R .carrier) (bpoly_series_sum R x c N) (bpoly_series_sum R x d N)
  ≔ match N [
  | zero. ↦ refl (R .zero)
  | suc. N ↦ refl (R .add) (bpoly_series_sum_ext R x c d N (k hk ↦ h k (lt_le k N hk)))
      (refl ((y ↦ R .mul y (ring_power R x N)) : R .carrier → R .carrier) (h N (le_refl N))) ]

def bpoly_series_shift (R : AbstractRing) (x : R .carrier) (c : Nat → R .carrier) (N : Nat)
  : Id (R .carrier) (bpoly_series_sum R x c (suc. N))
      (R .add (R .mul (bpoly_series_sum R x (k ↦ c (suc. k)) N) x) (R .mul (c zero.) (R .one)))
  ≔ let S ≔ R .carrier in let ad ≔ R .add in let m ≔ R .mul in
    match N [
  | zero. ↦ refl ((u ↦ ad u (m (c zero.) (R .one))) : S → S) (inverse S (m (R .zero) x) (R .zero) (ring_mul_zero_left R x))
  | suc. N ↦
    let A ≔ m (bpoly_series_sum R x (k ↦ c (suc. k)) N) x in
    let C ≔ m (c zero.) (R .one) in
    let Bm ≔ m (c (suc. N)) (m (ring_power R x N) x) in
    let B' ≔ m (m (c (suc. N)) (ring_power R x N)) x in
    calc
      ad (bpoly_series_sum R x c (suc. N)) Bm = ad (ad A C) Bm
        by refl ((u ↦ ad u Bm) : S → S) (bpoly_series_shift R x c N)
      = ad A (ad C Bm) by inverse S (ad A (ad C Bm)) (ad (ad A C) Bm) (R .add_laws .assoc A C Bm)
      = ad A (ad Bm C) by refl (ad A) (ring_add_comm R C Bm)
      = ad (ad A Bm) C by R .add_laws .assoc A Bm C
      = ad (ad A B') C by refl ((u ↦ ad (ad A u) C) : S → S) (ring_mul_assoc R (c (suc. N)) (ring_power R x N) x)
      = ad (m (ad (bpoly_series_sum R x (k ↦ c (suc. k)) N) (m (c (suc. N)) (ring_power R x N))) x) C
        by refl ((u ↦ ad u C) : S → S)
          (inverse S (m (ad (bpoly_series_sum R x (k ↦ c (suc. k)) N) (m (c (suc. N)) (ring_power R x N))) x) (ad A B')
            (ring_rdistr R (bpoly_series_sum R x (k ↦ c (suc. k)) N) (m (c (suc. N)) (ring_power R x N)) x)) ∎ ]

{` Coefficient sequence of a family read in the blind order. `}
def bpoly_blind_coeffs (A : Type) (z : A) (n : Nat) (b : Fin (suc. n) → A) (k : Nat) : A
  ≔ match k [
  | zero. ↦ b (inr. star.)
  | suc. k ↦ match n [ zero. ↦ z | suc. n ↦ bpoly_blind_coeffs A z n (s ↦ b (inl. s)) k ] ]

def bpoly_fin_sum_mul_right (R : AbstractRing) (x : R .carrier) (m : Nat) (u v : Fin m → R .carrier)
  : Id (R .carrier) (blind_fin_sum R m (s ↦ R .mul (u s) (R .mul (v s) x))) (R .mul (blind_fin_sum R m (s ↦ R .mul (u s) (v s))) x)
  ≔ let S ≔ R .carrier in
    match m [
  | zero. ↦ inverse S (R .mul (R .zero) x) (R .zero) (ring_mul_zero_left R x)
  | suc. m ↦ concat S (R .add (blind_fin_sum R m (s ↦ R .mul (u (inl. s)) (R .mul (v (inl. s)) x))) (R .mul (u (inr. star.)) (R .mul (v (inr. star.)) x)))
      (R .add (R .mul (blind_fin_sum R m (s ↦ R .mul (u (inl. s)) (v (inl. s)))) x) (R .mul (R .mul (u (inr. star.)) (v (inr. star.))) x))
      (R .mul (R .add (blind_fin_sum R m (s ↦ R .mul (u (inl. s)) (v (inl. s)))) (R .mul (u (inr. star.)) (v (inr. star.)))) x)
      (refl (R .add) (bpoly_fin_sum_mul_right R x m (s ↦ u (inl. s)) (s ↦ v (inl. s)))
        (ring_mul_assoc R (u (inr. star.)) (v (inr. star.)) x))
      (inverse S (R .mul (R .add (blind_fin_sum R m (s ↦ R .mul (u (inl. s)) (v (inl. s)))) (R .mul (u (inr. star.)) (v (inr. star.)))) x)
        (R .add (R .mul (blind_fin_sum R m (s ↦ R .mul (u (inl. s)) (v (inl. s)))) x) (R .mul (R .mul (u (inr. star.)) (v (inr. star.))) x))
        (ring_rdistr R (blind_fin_sum R m (s ↦ R .mul (u (inl. s)) (v (inl. s)))) (R .mul (u (inr. star.)) (v (inr. star.))) x)) ]

{` The blind sum is the series sum of the blind coefficient sequence. `}
def bpoly_blind_sum (R : AbstractRing) (x : R .carrier) (n : Nat) (b : Fin (suc. n) → R .carrier)
  : Id (R .carrier) (blind_fin_sum R (suc. n) (s ↦ R .mul (b s) (blind_ring_pow R x (fin_index (suc. n) s))))
      (bpoly_series_sum R x (bpoly_blind_coeffs (R .carrier) (R .zero) n b) (suc. n))
  ≔ let S ≔ R .carrier in
    match n [
  | zero. ↦ refl (R .add (R .zero) (R .mul (b (inr. star.)) (R .one)))
  | suc. n ↦
    let C ≔ R .mul (b (inr. star.)) (R .one) in
    let inner ≔ blind_fin_sum R (suc. n) (s ↦ R .mul (b (inl. s)) (blind_ring_pow R x (fin_index (suc. n) s))) in
    calc
      R .add (blind_fin_sum R (suc. n) (s ↦ R .mul (b (inl. s)) (R .mul (blind_ring_pow R x (fin_index (suc. n) s)) x))) C
      = R .add (R .mul inner x) C
        by refl ((u ↦ R .add u C) : S → S)
          (bpoly_fin_sum_mul_right R x (suc. n) (s ↦ b (inl. s)) (s ↦ blind_ring_pow R x (fin_index (suc. n) s)))
      = R .add (R .mul (bpoly_series_sum R x (bpoly_blind_coeffs S (R .zero) n (s ↦ b (inl. s))) (suc. n)) x) C
        by refl ((u ↦ R .add (R .mul u x) C) : S → S) (bpoly_blind_sum R x n (s ↦ b (inl. s)))
      = bpoly_series_sum R x (bpoly_blind_coeffs S (R .zero) (suc. n) b) (suc. (suc. n))
        by inverse S (bpoly_series_sum R x (bpoly_blind_coeffs S (R .zero) (suc. n) b) (suc. (suc. n)))
          (R .add (R .mul (bpoly_series_sum R x (bpoly_blind_coeffs S (R .zero) n (s ↦ b (inl. s))) (suc. n)) x) C)
          (bpoly_series_shift R x (bpoly_blind_coeffs S (R .zero) (suc. n) b) (suc. n)) ∎ ]

{` Our index of j : Fin(n+1) (inr ★ has index n). `}
def bpoly_our_index (n : Nat) (j : Fin (suc. n)) : Nat
  ≔ match n [ zero. ↦ zero. | suc. n ↦ match j [ inl. s ↦ bpoly_our_index n s | inr. _ ↦ suc. n ] ]

def bpoly_our_index_top (n : Nat) : Id Nat (bpoly_our_index n (inr. star.)) n
  ≔ match n [ zero. ↦ refl (zero. : Nat) | suc. n ↦ refl (suc. n : Nat) ]

def bpoly_our_index_le (n : Nat) (j : Fin (suc. n)) : Le (bpoly_our_index n j) n
  ≔ match n [
  | zero. ↦ star.
  | suc. n ↦ match j [
    | inl. s ↦ le_trans (bpoly_our_index n s) n (suc. n) (bpoly_our_index_le n s) (le_n_suc n)
    | inr. _ ↦ le_refl (suc. n) ] ]

{` poly_value of the family j ↦ c(our index of j) is the series sum. `}
def bpoly_our_sum (R : AbstractRing) (x : R .carrier) (n : Nat) (c : Nat → R .carrier)
  : Id (R .carrier) (poly_value R x n (j ↦ c (bpoly_our_index n j))) (bpoly_series_sum R x c (suc. n))
  ≔ let S ≔ R .carrier in
    match n [
  | zero. ↦ inverse S (R .add (R .zero) (R .mul (c zero.) (R .one))) (c zero.)
      (concat S (R .add (R .zero) (R .mul (c zero.) (R .one))) (R .mul (c zero.) (R .one)) (c zero.)
        (R .add_laws .unit_left (R .mul (c zero.) (R .one))) (ring_mul_one_right R (c zero.)))
  | suc. n ↦ refl ((u ↦ R .add u (R .mul (c (suc. n)) (ring_power R x (suc. n)))) : S → S) (bpoly_our_sum R x n c) ]

{` Coefficient sequence of a family read in our order. `}
def bpoly_coeff_step (A : Type) (k m : Nat) (d : Decidable (Id Nat k m)) (top rest : A) : A
  ≔ match d [ inl. _ ↦ top | inr. _ ↦ rest ]

def bpoly_coeff_step_eq (A : Type) (k m : Nat) (d : Decidable (Id Nat k m)) (top rest : A) (e : Id Nat k m)
  : Id A (bpoly_coeff_step A k m d top rest) top
  ≔ match d [ inl. _ ↦ refl top | inr. ne ↦ match ne e [ ] ]

def bpoly_coeff_step_ne (A : Type) (k m : Nat) (d : Decidable (Id Nat k m)) (top rest : A) (ne : Not (Id Nat k m))
  : Id A (bpoly_coeff_step A k m d top rest) rest
  ≔ match d [ inl. e ↦ match ne e [ ] | inr. _ ↦ refl rest ]

def bpoly_our_coeffs (A : Type) (z : A) (n : Nat) (a : Fin (suc. n) → A) (k : Nat) : A
  ≔ match n [
  | zero. ↦ bpoly_coeff_step A k zero. (nat_dec_eq k zero.) (a (inr. star.)) z
  | suc. n ↦ bpoly_coeff_step A k (suc. n) (nat_dec_eq k (suc. n)) (a (inr. star.)) (bpoly_our_coeffs A z n (s ↦ a (inl. s)) k) ]

def bpoly_our_coeffs_index (A : Type) (z : A) (n : Nat) (a : Fin (suc. n) → A) (j : Fin (suc. n))
  : Id A (bpoly_our_coeffs A z n a (bpoly_our_index n j)) (a j)
  ≔ match n [
  | zero. ↦ match j [
    | inl. e ↦ match e [ ]
    | inr. u ↦ match u [ star. ↦ bpoly_coeff_step_eq A zero. zero. (nat_dec_eq zero. zero.) (a (inr. star.)) z (refl (zero. : Nat)) ] ]
  | suc. n ↦ match j [
    | inr. u ↦ match u [ star. ↦ bpoly_coeff_step_eq A (suc. n) (suc. n) (nat_dec_eq (suc. n) (suc. n)) (a (inr. star.))
        (bpoly_our_coeffs A z n (s ↦ a (inl. s)) (suc. n)) (refl (suc. n : Nat)) ]
    | inl. s ↦ concat A
        (bpoly_coeff_step A (bpoly_our_index n s) (suc. n) (nat_dec_eq (bpoly_our_index n s) (suc. n)) (a (inr. star.))
          (bpoly_our_coeffs A z n (t ↦ a (inl. t)) (bpoly_our_index n s)))
        (bpoly_our_coeffs A z n (t ↦ a (inl. t)) (bpoly_our_index n s)) (a (inl. s))
        (bpoly_coeff_step_ne A (bpoly_our_index n s) (suc. n) (nat_dec_eq (bpoly_our_index n s) (suc. n)) (a (inr. star.))
          (bpoly_our_coeffs A z n (t ↦ a (inl. t)) (bpoly_our_index n s))
          (e ↦ lt_irrefl n (transport Nat (k ↦ Le k n) (bpoly_our_index n s) (suc. n) e (bpoly_our_index_le n s))))
        (bpoly_our_coeffs_index A z n (t ↦ a (inl. t)) s) ] ]

{` The blind coefficient sequence of s ↦ c(fin_index s) is c (up to n), and
   of b at fin_index s is b s. `}
def bpoly_blind_coeffs_of_seq (A : Type) (z : A) (n : Nat) (c : Nat → A) (k : Nat) (hk : Le k n)
  : Id A (bpoly_blind_coeffs A z n (s ↦ c (fin_index (suc. n) s)) k) (c k)
  ≔ match k [
  | zero. ↦ refl (c zero.)
  | suc. k ↦ match n [
    | zero. ↦ match hk [ ]
    | suc. n ↦ bpoly_blind_coeffs_of_seq A z n (j ↦ c (suc. j)) k hk ] ]

def bpoly_blind_coeffs_index (A : Type) (z : A) (n : Nat) (b : Fin (suc. n) → A) (s : Fin (suc. n))
  : Id A (bpoly_blind_coeffs A z n b (fin_index (suc. n) s)) (b s)
  ≔ match n [
  | zero. ↦ match s [ inl. e ↦ match e [ ] | inr. u ↦ match u [ star. ↦ refl (b (inr. star.)) ] ]
  | suc. n ↦ match s [
    | inr. u ↦ match u [ star. ↦ refl (b (inr. star.)) ]
    | inl. t ↦ bpoly_blind_coeffs_index A z n (r ↦ b (inl. r)) t ] ]

def bpoly_blind_coeffs_map (A B : Type) (zA : A) (zB : B) (f : A → B) (hz : Id B (f zA) zB) (n : Nat)
  (b : Fin (suc. n) → A) (k : Nat)
  : Id B (f (bpoly_blind_coeffs A zA n b k)) (bpoly_blind_coeffs B zB n (s ↦ f (b s)) k)
  ≔ match k [
  | zero. ↦ refl (f (b (inr. star.)))
  | suc. k ↦ match n [
    | zero. ↦ hz
    | suc. n ↦ bpoly_blind_coeffs_map A B zA zB f hz n (s ↦ b (inl. s)) k ] ]

{` The top nonzero coefficient below n + 1 (decidable equality). `}
def bpoly_top_nonzero (A : Type) (dec : DecidableEquality A) (z : A) (c : Nat → A) (n : Nat)
  (nz : Not ((k : Nat) → Le k n → Id A (c k) z))
  : Σ Nat (m ↦ Product (Le m n) (Product (Not (Id A (c m) z)) ((k : Nat) → Lt m k → Le k n → Id A (c k) z)))
  ≔ match dec (c n) z [
  | inr. ne ↦ (n, (le_refl n, (ne, k lt le ↦ match lt_irrefl n (lt_le_trans n k n lt le) [ ])))
  | inl. e ↦ match n [
    | zero. ↦ match nz (k hk ↦ match k [ zero. ↦ e | suc. _ ↦ match hk [ ] ]) [ ]
    | suc. n ↦
      let r ≔ bpoly_top_nonzero A dec z c n
                (h ↦ nz (k hk ↦ match lt_suc_split k (suc. n) hk [
                   | inl. h' ↦ h k h'
                   | inr. q ↦ concat A (c k) (c (suc. n)) z (refl c q) e ])) in
      (r .fst,
       (le_trans (r .fst) n (suc. n) (r .snd .fst) (le_n_suc n),
        (r .snd .snd .fst,
         k lt le ↦ match lt_suc_split k (suc. n) le [
           | inl. h' ↦ r .snd .snd .snd k lt h'
           | inr. q ↦ concat A (c k) (c (suc. n)) z (refl c q) e ]))) ] ]

{` Coefficients vanishing above m do not contribute. `}
def bpoly_series_sum_top (R : AbstractRing) (x : R .carrier) (c : Nat → R .carrier) (m n : Nat) (hmn : Le m n)
  (hz : (k : Nat) → Lt m k → Le k n → Id (R .carrier) (c k) (R .zero))
  : Id (R .carrier) (bpoly_series_sum R x c (suc. n)) (bpoly_series_sum R x c (suc. m))
  ≔ let S ≔ R .carrier in
    match lt_suc_split m n hmn [
  | inr. q ↦ refl ((k ↦ bpoly_series_sum R x c (suc. k)) : Nat → S) (inverse Nat m n q)
  | inl. lt ↦ match n [
    | zero. ↦ match lt [ ]
    | suc. n ↦
      let P ≔ ring_power R x (suc. n) in
      concat S (bpoly_series_sum R x c (suc. (suc. n))) (bpoly_series_sum R x c (suc. n)) (bpoly_series_sum R x c (suc. m))
        (concat S (R .add (bpoly_series_sum R x c (suc. n)) (R .mul (c (suc. n)) P)) (R .add (bpoly_series_sum R x c (suc. n)) (R .zero))
           (bpoly_series_sum R x c (suc. n))
           (refl (R .add (bpoly_series_sum R x c (suc. n)))
             (concat S (R .mul (c (suc. n)) P) (R .mul (R .zero) P) (R .zero)
               (refl ((u ↦ R .mul u P) : S → S) (hz (suc. n) lt (le_refl (suc. n)))) (ring_mul_zero_left R P)))
           (R .add_laws .unit_right (bpoly_series_sum R x c (suc. n))))
        (bpoly_series_sum_top R x c m n lt (k l1 l2 ↦ hz k l1 (le_trans k n (suc. n) l2 (le_n_suc n)))) ] ]

{` blind_poly_eval in the series form. `}
def bridge_blind_eval_series (k : Field) (E : FieldExt k) (n : Nat) (b : Fin (suc. n) → k .fst .carrier)
  (α : E .fst .fst .carrier)
  : Id (E .fst .fst .carrier) (blind_poly_eval k E n b α)
      (bpoly_series_sum (E .fst .fst) α (j ↦ ext_map k E (bpoly_blind_coeffs (k .fst .carrier) (k .fst .zero) n b j)) (suc. n))
  ≔ let K ≔ E .fst .fst in let i ≔ ext_map k E in
    concat (K .carrier) (blind_poly_eval k E n b α)
      (bpoly_series_sum K α (bpoly_blind_coeffs (K .carrier) (K .zero) n (s ↦ i (b s))) (suc. n))
      (bpoly_series_sum K α (j ↦ i (bpoly_blind_coeffs (k .fst .carrier) (k .fst .zero) n b j)) (suc. n))
      (bpoly_blind_sum K α n (s ↦ i (b s)))
      (bpoly_series_sum_ext K α (bpoly_blind_coeffs (K .carrier) (K .zero) n (s ↦ i (b s)))
        (j ↦ i (bpoly_blind_coeffs (k .fst .carrier) (k .fst .zero) n b j)) (suc. n)
        (j _ ↦ inverse (K .carrier) (i (bpoly_blind_coeffs (k .fst .carrier) (k .fst .zero) n b j))
           (bpoly_blind_coeffs (K .carrier) (K .zero) n (s ↦ i (b s)) j)
           (bpoly_blind_coeffs_map (k .fst .carrier) (K .carrier) (k .fst .zero) (K .zero) i (ext_map_zero k E) n b j)))

{` Ours ⇒ blind corrected (no hypothesis). `}
def bridge_algebraic_element_to_blind (k : Field) (E : FieldExt k) (α : ext_carrier k E) (h : IsAlgebraicElement k E α)
  : BlindIsAlgebraicElementCorrected k E α
  ≔ let kc ≔ k .fst .carrier in let kz ≔ k .fst .zero in let K ≔ E .fst .fst in let i ≔ ext_map k E in
    let T ≔ Σ Nat (n ↦ Σ (Fin (suc. n) → kc) (a ↦
              Product (Not ((s : Fin (suc. n)) → Id kc (a s) kz)) (Id (K .carrier) (blind_poly_eval k E n a α) (K .zero)))) in
    mere_rec (Σ Nat (n ↦ Σ (Fin (suc. n) → kc) (a ↦
                Product (Not (Id kc (a (inr. star.)) kz)) (Id (K .carrier) (ext_poly_value k E α n a) (K .zero)))))
      (Mere T) (mere_isprop T)
      (w ↦
        let n ≔ w .fst in let a ≔ w .snd .fst in
        let c : Nat → kc ≔ bpoly_our_coeffs kc kz n a in
        let b : Fin (suc. n) → kc ≔ s ↦ c (fin_index (suc. n) s) in
        let s0 ≔ equiv_inverse_map (Fin (suc. n)) (Below (suc. n)) (fin_below_equiv (suc. n)) (n, le_refl n) in
        let e0 : Id Nat (fin_index (suc. n) s0) n ≔ fin_index_from_bound (suc. n) n (le_refl n) in
        let nz : Not ((s : Fin (suc. n)) → Id kc (b s) kz)
          ≔ hz ↦ w .snd .snd .fst
               (calc
                  a (inr. star.) = c (bpoly_our_index n (inr. star.))
                    by inverse kc (c (bpoly_our_index n (inr. star.))) (a (inr. star.)) (bpoly_our_coeffs_index kc kz n a (inr. star.))
                  = c n by refl c (bpoly_our_index_top n)
                  = b s0 by refl c (inverse Nat (fin_index (suc. n) s0) n e0)
                  = kz by hz s0 ∎) in
        let root : Id (K .carrier) (blind_poly_eval k E n b α) (K .zero)
          ≔ calc
              blind_poly_eval k E n b α
              = bpoly_series_sum K α (j ↦ i (bpoly_blind_coeffs kc kz n b j)) (suc. n) by bridge_blind_eval_series k E n b α
              = bpoly_series_sum K α (j ↦ i (c j)) (suc. n)
                by bpoly_series_sum_ext K α (j ↦ i (bpoly_blind_coeffs kc kz n b j)) (j ↦ i (c j)) (suc. n)
                  (j hj ↦ refl i (bpoly_blind_coeffs_of_seq kc kz n c j hj))
              = poly_value K α n (j ↦ i (c (bpoly_our_index n j)))
                by inverse (K .carrier) (poly_value K α n (j ↦ i (c (bpoly_our_index n j)))) (bpoly_series_sum K α (j ↦ i (c j)) (suc. n))
                  (bpoly_our_sum K α n (j ↦ i (c j)))
              = ext_poly_value k E α n a
                by refl (poly_value K α n)
                  (funext (Fin (suc. n)) (_ ↦ K .carrier) (j ↦ i (c (bpoly_our_index n j))) (j ↦ i (a j))
                    (j ↦ refl i (bpoly_our_coeffs_index kc kz n a j)))
              = K .zero by w .snd .snd .snd ∎ in
        mere T (n, (b, (nz, root))))
      h

{` Blind corrected ⇒ ours, given decidable equality of k. `}
def bridge_algebraic_element_from_blind (k : Field) (E : FieldExt k) (dec : DecidableEquality (k .fst .carrier))
  (α : ext_carrier k E) (h : BlindIsAlgebraicElementCorrected k E α) : IsAlgebraicElement k E α
  ≔ let kc ≔ k .fst .carrier in let kz ≔ k .fst .zero in let K ≔ E .fst .fst in let i ≔ ext_map k E in
    let T ≔ Σ Nat (n ↦ Σ (Fin (suc. n) → kc) (a ↦
              Product (Not (Id kc (a (inr. star.)) kz)) (Id (K .carrier) (ext_poly_value k E α n a) (K .zero)))) in
    mere_rec (Σ Nat (n ↦ Σ (Fin (suc. n) → kc) (a ↦
                Product (Not ((s : Fin (suc. n)) → Id kc (a s) kz)) (Id (K .carrier) (blind_poly_eval k E n a α) (K .zero)))))
      (Mere T) (mere_isprop T)
      (w ↦
        let n ≔ w .fst in let b ≔ w .snd .fst in
        let c : Nat → kc ≔ bpoly_blind_coeffs kc kz n b in
        let nzc : Not ((j : Nat) → Le j n → Id kc (c j) kz)
          ≔ hc ↦ w .snd .snd .fst (s ↦ concat kc (b s) (c (fin_index (suc. n) s)) kz
                   (inverse kc (c (fin_index (suc. n) s)) (b s) (bpoly_blind_coeffs_index kc kz n b s))
                   (hc (fin_index (suc. n) s) (fin_index_bound (suc. n) s))) in
        let t ≔ bpoly_top_nonzero kc dec kz c n nzc in
        let m ≔ t .fst in
        let a' : Fin (suc. m) → kc ≔ j ↦ c (bpoly_our_index m j) in
        let lead : Not (Id kc (a' (inr. star.)) kz)
          ≔ e ↦ t .snd .snd .fst (concat kc (c m) (a' (inr. star.)) kz
                  (refl c (inverse Nat (bpoly_our_index m (inr. star.)) m (bpoly_our_index_top m))) e) in
        let root : Id (K .carrier) (ext_poly_value k E α m a') (K .zero)
          ≔ calc
              ext_poly_value k E α m a' = bpoly_series_sum K α (j ↦ i (c j)) (suc. m) by bpoly_our_sum K α m (j ↦ i (c j))
              = bpoly_series_sum K α (j ↦ i (c j)) (suc. n)
                by inverse (K .carrier) (bpoly_series_sum K α (j ↦ i (c j)) (suc. n)) (bpoly_series_sum K α (j ↦ i (c j)) (suc. m))
                  (bpoly_series_sum_top K α (j ↦ i (c j)) m n (t .snd .fst)
                    (j l1 l2 ↦ concat (K .carrier) (i (c j)) (i kz) (K .zero) (refl i (t .snd .snd .snd j l1 l2)) (ext_map_zero k E)))
              = blind_poly_eval k E n b α
                by inverse (K .carrier) (blind_poly_eval k E n b α) (bpoly_series_sum K α (j ↦ i (c j)) (suc. n))
                  (bridge_blind_eval_series k E n b α)
              = K .zero by w .snd .snd .snd ∎ in
        mere T (m, (a', (lead, root))))
      h

{` Decidable equality of K gives decidable equality of k (field homs are injective). `}
def bridge_dec_base (k : Field) (E : FieldExt k) (dec : DecidableEquality (ext_carrier k E)) : DecidableEquality (k .fst .carrier)
  ≔ a b ↦ match dec (ext_map k E a) (ext_map k E b) [
  | inl. e ↦ inl. (field_hom_injective k (E .fst) (E .snd) a b e)
  | inr. ne ↦ inr. (e ↦ ne (refl (ext_map k E) e)) ]
