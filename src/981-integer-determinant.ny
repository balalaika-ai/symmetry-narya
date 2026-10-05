export "1310-integer-ring"

{` Chapter 9 (subgroups.tex 1186): the determinant of an integer matrix.

   det A is the cofactor (Laplace) expansion along the last row, computed
   through generalized minors over a set of selected columns
   S : Fin n → Bool (rows R : Fin m → Fin n → Int):
     D_0(S) = 1 if S is empty, 0 otherwise;
     D_{m+1}(R; S) = Σ_j [S j] · ε_S(j) · R_last(j) · D_m(R restricted to the first m rows; S − j),
   where ε_S(j) = (−1)^(number of selected columns after j). For S = all
   columns this is the usual expansion det A = Σ_j (−1)^((n−1)+j) a_{n−1,j} M_{n−1,j}
   (with |S| = m the number of selected columns after j is m−1−pos(j)).
   Summing over the fixed index set Fin n (instead of re-indexed minors)
   makes the alternation proof a double-sum swap (module 982).
   Also: finite-sum lemmas, additivity of A · x, and litmus values. `}

{` Integer vectors Int^n = Fin n → Int, integer matrices (A i j = entry in
   row i, column j), finite sums over Fin n (recursion on n, the new index
   last), the matrix-vector product A · x, additive and unimodular
   (additive with a two-sided inverse) self-maps of Int^n, diagonal maps. `}

def IntMatrix (n : Nat) : Type ≔ Fin n → Fin n → Int

def int_fsum (n : Nat) (f : Fin n → Int) : Int
  ≔ match n [ zero. ↦ int_zero | suc. n ↦ int_add (int_fsum n (j ↦ f (inl. j))) (f (inr. star.)) ]

def int_vec_add (n : Nat) (x y : Fin n → Int) : Fin n → Int ≔ i ↦ int_add (x i) (y i)

def int_mat_vec (n : Nat) (A : IntMatrix n) (x : Fin n → Int) : Fin n → Int
  ≔ i ↦ int_fsum n (j ↦ int_mul (A i j) (x j))

def IntVecAdditive (n : Nat) (F : (Fin n → Int) → Fin n → Int) : Type
  ≔ (x y : Fin n → Int) (i : Fin n) → Id Int (F (int_vec_add n x y) i) (int_add (F x i) (F y i))

{` F is unimodular: additive with a two-sided inverse G (pointwise). `}
def IntVecUnimodular (n : Nat) (F : (Fin n → Int) → Fin n → Int) : Type
  ≔ Σ ((Fin n → Int) → Fin n → Int) (G ↦
      Product (IntVecAdditive n F)
        (Product ((x : Fin n → Int) (i : Fin n) → Id Int (F (G x) i) (x i))
          ((x : Fin n → Int) (i : Fin n) → Id Int (G (F x) i) (x i))))

{` diag(d) · x, written x_i · d_i as in circle_multiplication_winding. `}
def int_diag_map (n : Nat) (d : Fin n → Int) (x : Fin n → Int) : Fin n → Int ≔ i ↦ int_mul (x i) (d i)

{` Litmus: (1 2; 3 4) · (1, 1) = (3, 7). `}
def int_mat_vec_litmus
  : Id (Product Int Int)
      (let A : IntMatrix (suc. (suc. zero.)) ≔ i j ↦ match i [
         | inl. _ ↦ match j [ inl. _ ↦ pos. 1 | inr. _ ↦ pos. 2 ]
         | inr. _ ↦ match j [ inl. _ ↦ pos. 3 | inr. _ ↦ pos. 4 ] ] in
       let v ≔ int_mat_vec (suc. (suc. zero.)) A (_ ↦ pos. 1) in
       (v (inl. (inr. star.)), v (inr. star.)))
      (pos. 3, pos. 7)
  ≔ refl ((pos. 3, pos. 7) : Product Int Int)


{` Bool helpers (kept as separate case trees so that lemmas can case on a
   Bool variable). `}
def imat_bif (b : Bool) (x : Int) : Int ≔ match b [ true. ↦ x | false. ↦ int_zero ]

def imat_bsign (b : Bool) (x : Int) : Int ≔ match b [ true. ↦ int_neg x | false. ↦ x ]

def imat_bnot_and (e s : Bool) : Bool ≔ match e [ true. ↦ false. | false. ↦ s ]

{` Structural Boolean equality on Fin n. `}
def imat_fin_eqb (n : Nat) (i j : Fin n) : Bool
  ≔ match n [
  | zero. ↦ match i [ ]
  | suc. n ↦ match i [
    | inl. a ↦ match j [ inl. b ↦ imat_fin_eqb n a b | inr. _ ↦ false. ]
    | inr. _ ↦ match j [ inl. _ ↦ false. | inr. _ ↦ true. ] ] ]

{` S − j (remove column j from the selection). `}
def imat_remove (n : Nat) (S : Fin n → Bool) (j : Fin n) (i : Fin n) : Bool
  ≔ imat_bnot_and (imat_fin_eqb n i j) (S i)

def imat_empty (n : Nat) (S : Fin n → Bool) : Bool
  ≔ match n [ zero. ↦ true. | suc. n ↦ imat_bnot_and (S (inr. star.)) (imat_empty n (i ↦ S (inl. i))) ]

{` ε_S(j) = (−1)^(number of selected columns after j). `}
def imat_sgn (n : Nat) (S : Fin n → Bool) (j : Fin n) : Int
  ≔ match n [
  | zero. ↦ match j [ ]
  | suc. n ↦ match j [
    | inl. j ↦ imat_bsign (S (inr. star.)) (imat_sgn n (i ↦ S (inl. i)) j)
    | inr. _ ↦ int_one ] ]

def imat_minor (m n : Nat) (R : Fin m → Fin n → Int) (S : Fin n → Bool) : Int
  ≔ match m [
  | zero. ↦ imat_bif (imat_empty n S) int_one
  | suc. m ↦ int_fsum n (j ↦ imat_bif (S j)
      (int_mul (int_mul (imat_sgn n S j) (R (inr. star.) j)) (imat_minor m n (i ↦ R (inl. i)) (imat_remove n S j)))) ]

def int_det (n : Nat) (A : IntMatrix n) : Int ≔ imat_minor n n A (_ ↦ true.)

{` Litmus: det (1 2; 3 4) = −2, det of the 3 × 3 matrix (2 0 1; 1 3 0; 0 1 4) = 25,
   det of the 0 × 0 matrix = 1. `}
def int_det_litmus_two
  : Id Int (int_det (suc. (suc. zero.)) (i j ↦ match i [
      | inl. _ ↦ match j [ inl. _ ↦ pos. 1 | inr. _ ↦ pos. 2 ]
      | inr. _ ↦ match j [ inl. _ ↦ pos. 3 | inr. _ ↦ pos. 4 ] ])) (neg. 1)
  ≔ refl (neg. 1 : Int)

def imat_row3 (A : Type) (a b c : A) : Fin 3 → A
  ≔ [ inl. (inl. (inl. e)) ↦ match e [ ] | inl. (inl. (inr. _)) ↦ a | inl. (inr. _) ↦ b | inr. _ ↦ c ]

def int_det_litmus_three
  : Id Int (int_det 3 (imat_row3 (Fin 3 → Int) (imat_row3 Int (pos. 2) (pos. 0) (pos. 1)) (imat_row3 Int (pos. 1) (pos. 3) (pos. 0))
      (imat_row3 Int (pos. 0) (pos. 1) (pos. 4)))) (pos. 25)
  ≔ refl (pos. 25 : Int)

def int_det_litmus_empty : Id Int (int_det zero. (i j ↦ match i [ ])) (pos. 1) ≔ refl (pos. 1 : Int)

{` Finite sums. `}
def int_fsum_ext (n : Nat) (f g : Fin n → Int) (h : (j : Fin n) → Id Int (f j) (g j))
  : Id Int (int_fsum n f) (int_fsum n g)
  ≔ match n [
  | zero. ↦ refl int_zero
  | suc. n ↦ refl int_add (int_fsum_ext n (j ↦ f (inl. j)) (j ↦ g (inl. j)) (j ↦ h (inl. j))) (h (inr. star.)) ]

def int_fsum_zero (n : Nat) (f : Fin n → Int) (h : (j : Fin n) → Id Int (f j) int_zero)
  : Id Int (int_fsum n f) int_zero
  ≔ match n [
  | zero. ↦ refl int_zero
  | suc. n ↦ refl int_add (int_fsum_zero n (j ↦ f (inl. j)) (j ↦ h (inl. j))) (h (inr. star.)) ]

def int_fsum_add (n : Nat) (f g : Fin n → Int)
  : Id Int (int_fsum n (j ↦ int_add (f j) (g j))) (int_add (int_fsum n f) (int_fsum n g))
  ≔ match n [
  | zero. ↦ refl int_zero
  | suc. n ↦ concat Int (int_add (int_fsum n (j ↦ int_add (f (inl. j)) (g (inl. j)))) (int_add (f (inr. star.)) (g (inr. star.))))
      (int_add (int_add (int_fsum n (j ↦ f (inl. j))) (int_fsum n (j ↦ g (inl. j)))) (int_add (f (inr. star.)) (g (inr. star.))))
      (int_add (int_add (int_fsum n (j ↦ f (inl. j))) (f (inr. star.))) (int_add (int_fsum n (j ↦ g (inl. j))) (g (inr. star.))))
      (refl ((x ↦ int_add x (int_add (f (inr. star.)) (g (inr. star.)))) : Int → Int)
        (int_fsum_add n (j ↦ f (inl. j)) (j ↦ g (inl. j))))
      (int_add_interchange (int_fsum n (j ↦ f (inl. j))) (int_fsum n (j ↦ g (inl. j))) (f (inr. star.)) (g (inr. star.))) ]

def int_fsum_scale (n : Nat) (c : Int) (f : Fin n → Int)
  : Id Int (int_fsum n (j ↦ int_mul c (f j))) (int_mul c (int_fsum n f))
  ≔ match n [
  | zero. ↦ refl int_zero
  | suc. n ↦ concat Int (int_add (int_fsum n (j ↦ int_mul c (f (inl. j)))) (int_mul c (f (inr. star.))))
      (int_add (int_mul c (int_fsum n (j ↦ f (inl. j)))) (int_mul c (f (inr. star.))))
      (int_mul c (int_add (int_fsum n (j ↦ f (inl. j))) (f (inr. star.))))
      (refl ((x ↦ int_add x (int_mul c (f (inr. star.)))) : Int → Int) (int_fsum_scale n c (j ↦ f (inl. j))))
      (inverse Int (int_mul c (int_add (int_fsum n (j ↦ f (inl. j))) (f (inr. star.))))
        (int_add (int_mul c (int_fsum n (j ↦ f (inl. j)))) (int_mul c (f (inr. star.))))
        (int_mul_ldistr c (int_fsum n (j ↦ f (inl. j))) (f (inr. star.)))) ]

def int_fsum_neg (n : Nat) (f : Fin n → Int)
  : Id Int (int_fsum n (j ↦ int_neg (f j))) (int_neg (int_fsum n f))
  ≔ match n [
  | zero. ↦ refl int_zero
  | suc. n ↦ concat Int (int_add (int_fsum n (j ↦ int_neg (f (inl. j)))) (int_neg (f (inr. star.))))
      (int_add (int_neg (int_fsum n (j ↦ f (inl. j)))) (int_neg (f (inr. star.))))
      (int_neg (int_add (int_fsum n (j ↦ f (inl. j))) (f (inr. star.))))
      (refl ((x ↦ int_add x (int_neg (f (inr. star.)))) : Int → Int) (int_fsum_neg n (j ↦ f (inl. j))))
      (inverse Int (int_neg (int_add (int_fsum n (j ↦ f (inl. j))) (f (inr. star.))))
        (int_add (int_neg (int_fsum n (j ↦ f (inl. j)))) (int_neg (f (inr. star.))))
        (int_neg_additive (int_fsum n (j ↦ f (inl. j))) (f (inr. star.)))) ]

def int_fsum_swap (n m : Nat) (f : Fin n → Fin m → Int)
  : Id Int (int_fsum n (j ↦ int_fsum m (k ↦ f j k))) (int_fsum m (k ↦ int_fsum n (j ↦ f j k)))
  ≔ match n [
  | zero. ↦ inverse Int (int_fsum m (k ↦ int_zero)) int_zero (int_fsum_zero m (k ↦ int_zero) (k ↦ refl int_zero))
  | suc. n ↦ concat Int (int_add (int_fsum n (j ↦ int_fsum m (k ↦ f (inl. j) k))) (int_fsum m (k ↦ f (inr. star.) k)))
      (int_add (int_fsum m (k ↦ int_fsum n (j ↦ f (inl. j) k))) (int_fsum m (k ↦ f (inr. star.) k)))
      (int_fsum m (k ↦ int_add (int_fsum n (j ↦ f (inl. j) k)) (f (inr. star.) k)))
      (refl ((x ↦ int_add x (int_fsum m (k ↦ f (inr. star.) k))) : Int → Int) (int_fsum_swap n m (j k ↦ f (inl. j) k)))
      (inverse Int (int_fsum m (k ↦ int_add (int_fsum n (j ↦ f (inl. j) k)) (f (inr. star.) k)))
        (int_add (int_fsum m (k ↦ int_fsum n (j ↦ f (inl. j) k))) (int_fsum m (k ↦ f (inr. star.) k)))
        (int_fsum_add m (k ↦ int_fsum n (j ↦ f (inl. j) k)) (k ↦ f (inr. star.) k))) ]

{` A · x is additive. `}
def int_mat_vec_additive (n : Nat) (A : IntMatrix n) : IntVecAdditive n (int_mat_vec n A)
  ≔ x y i ↦ concat Int (int_fsum n (j ↦ int_mul (A i j) (int_add (x j) (y j))))
      (int_fsum n (j ↦ int_add (int_mul (A i j) (x j)) (int_mul (A i j) (y j))))
      (int_add (int_mat_vec n A x i) (int_mat_vec n A y i))
      (int_fsum_ext n (j ↦ int_mul (A i j) (int_add (x j) (y j))) (j ↦ int_add (int_mul (A i j) (x j)) (int_mul (A i j) (y j)))
        (j ↦ int_mul_ldistr (A i j) (x j) (y j)))
      (int_fsum_add n (j ↦ int_mul (A i j) (x j)) (j ↦ int_mul (A i j) (y j)))

{` Generalized minors only depend on the entries and on the selection pointwise. `}
def imat_minor_ext_rows (m n : Nat) (R R' : Fin m → Fin n → Int) (S : Fin n → Bool)
  (h : (i : Fin m) (j : Fin n) → Id Int (R i j) (R' i j))
  : Id Int (imat_minor m n R S) (imat_minor m n R' S)
  ≔ match m [
  | zero. ↦ refl (imat_bif (imat_empty n S) int_one)
  | suc. m ↦ int_fsum_ext n
      (j ↦ imat_bif (S j) (int_mul (int_mul (imat_sgn n S j) (R (inr. star.) j)) (imat_minor m n (i ↦ R (inl. i)) (imat_remove n S j))))
      (j ↦ imat_bif (S j) (int_mul (int_mul (imat_sgn n S j) (R' (inr. star.) j)) (imat_minor m n (i ↦ R' (inl. i)) (imat_remove n S j))))
      (j ↦ refl (imat_bif (S j))
        (refl int_mul (refl (int_mul (imat_sgn n S j)) (h (inr. star.) j))
          (imat_minor_ext_rows m n (i ↦ R (inl. i)) (i ↦ R' (inl. i)) (imat_remove n S j) (i ↦ h (inl. i))))) ]

def imat_minor_ext_cols (m n : Nat) (R : Fin m → Fin n → Int) (S S' : Fin n → Bool)
  (h : (j : Fin n) → Id Bool (S j) (S' j))
  : Id Int (imat_minor m n R S) (imat_minor m n R S')
  ≔ refl (imat_minor m n R) (funext (Fin n) (_ ↦ Bool) S S' h)

def int_det_ext (n : Nat) (A A' : IntMatrix n) (h : (i j : Fin n) → Id Int (A i j) (A' i j))
  : Id Int (int_det n A) (int_det n A')
  ≔ imat_minor_ext_rows n n A A' (_ ↦ true.) h
