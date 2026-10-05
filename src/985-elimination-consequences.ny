export "984-last-column-elimination"

{` Chapter 9 (subgroups.tex 1186): consequences of the elimination of
   module 984. (1) If det A = 0 there is a nonzero x with A · x = 0 (by
   induction on n: either the corner g of the eliminated matrix is 0 and
   x = e_last, or det B = 0 and x = (g y, −r·y) for a kernel vector y of B).
   (2) The block decomposition of a matrix A' with last column (0, …, 0, g):
   A' · x = (B ⊕ 1)(L(diag(1, …, 1, g) x)) with L(y) = (y', r·y' + y_last)
   unimodular, r the last row of A' without its corner. `}

def imat_mul_zero_right_cancel (x y : Int) (hx : Id Int x int_zero → Empty) (h : Id Int (int_mul x y) int_zero)
  : Id Int y int_zero
  ≔ match x [
  | pos. a ↦ match a [
    | zero. ↦ match hx (refl int_zero) [ ]
    | suc. a ↦ int_mul_cancel_pos a y int_zero
        (concat Int (int_mul y (pos. (suc. a))) (int_mul (pos. (suc. a)) y) (int_mul int_zero (pos. (suc. a)))
          (int_mul_comm y (pos. (suc. a)))
          (concat Int (int_mul (pos. (suc. a)) y) int_zero (int_mul int_zero (pos. (suc. a))) h
            (inverse Int (int_mul int_zero (pos. (suc. a))) int_zero (imat_mul_zero_left (pos. (suc. a)))))) ]
  | neg. a ↦ int_mul_cancel_pos a y int_zero
      (concat Int (int_mul y (pos. (suc. a))) (int_mul (pos. (suc. a)) y) (int_mul int_zero (pos. (suc. a)))
        (int_mul_comm y (pos. (suc. a)))
        (calc
          int_mul (pos. (suc. a)) y = int_neg (int_neg (int_mul (pos. (suc. a)) y))
            by inverse Int (int_neg (int_neg (int_mul (pos. (suc. a)) y))) (int_mul (pos. (suc. a)) y) (int_neg_neg (int_mul (pos. (suc. a)) y))
          = int_neg (int_mul (neg. a) y) by refl int_neg (inverse Int (int_mul (neg. a) y) (int_neg (int_mul (pos. (suc. a)) y))
               (imat_mul_neg_left (pos. (suc. a)) y))
          = int_neg int_zero by refl int_neg h
          = int_mul int_zero (pos. (suc. a)) by inverse Int (int_mul int_zero (pos. (suc. a))) int_zero (imat_mul_zero_left (pos. (suc. a))) ∎)) ]

def imat_mul_eq_zero (x y : Int) (h : Id Int (int_mul x y) int_zero) : Sum (Id Int x int_zero) (Id Int y int_zero)
  ≔ match int_dec_eq x int_zero [
  | inl. e ↦ inl. e
  | inr. ne ↦ inr. (imat_mul_zero_right_cancel x y ne h) ]

def imat_additive_zero (n : Nat) (F : (Fin n → Int) → Fin n → Int) (hF : IntVecAdditive n F) (i : Fin n)
  : Id Int (F (_ ↦ int_zero) i) int_zero
  ≔ let z ≔ F (_ ↦ int_zero) i in
    inverse Int int_zero z
      (int_add_cancel_right z int_zero z
        (concat Int (int_add int_zero z) z (int_add z z) (int_add_zero_left z) (hF (_ ↦ int_zero) (_ ↦ int_zero) i)))

{` The kernel vector for det A = 0. `}
def ImatKernelVector (n : Nat) (A : IntMatrix n) : Type
  ≔ Σ (Fin n → Int) (x ↦ Product (((i : Fin n) → Id Int (x i) int_zero) → Empty)
      ((i : Fin n) → Id Int (int_mat_vec n A x i) int_zero))

def imat_kernel_transfer (n : Nat) (A A' : IntMatrix n) (r : ImatRel n A A') (k : ImatKernelVector n A') : ImatKernelVector n A
  ≔ let F ≔ r .snd .fst in
    (k .fst, (k .snd .fst,
      (i ↦ calc
        int_mat_vec n A (k .fst) i = F (int_mat_vec n A' (k .fst)) i by r .snd .snd .snd (k .fst) i
        = F (_ ↦ int_zero) i
          by refl ((v ↦ F v i) : (Fin n → Int) → Int)
               (funext (Fin n) (_ ↦ Int) (int_mat_vec n A' (k .fst)) (_ ↦ int_zero) (k .snd .snd))
        = int_zero by imat_additive_zero n F (r .snd .snd .fst .snd .fst) i ∎)))

def imat_last_vector (n : Nat) : Fin (suc. n) → Int ≔ [ inl. _ ↦ int_zero | inr. _ ↦ int_one ]

def imat_last_col_zero (n : Nat) (A : IntMatrix (suc. n))
  (z : (i : Fin n) → Id Int (A (inl. i) (inr. star.)) int_zero) (g0 : Id Int (A (inr. star.) (inr. star.)) int_zero)
  (i : Fin (suc. n)) : Id Int (A i (inr. star.)) int_zero
  ≔ match i [ inl. k ↦ z k | inr. u ↦ match u [ star. ↦ g0 ] ]

def imat_kernel_corner_zero (n : Nat) (A : IntMatrix (suc. n))
  (z : (i : Fin n) → Id Int (A (inl. i) (inr. star.)) int_zero) (g0 : Id Int (A (inr. star.) (inr. star.)) int_zero)
  : ImatKernelVector (suc. n) A
  ≔ (imat_last_vector n,
     ((h ↦ match int_encode int_one int_zero (h (inr. star.)) [ ]),
      (i ↦ calc
        int_mat_vec (suc. n) A (imat_last_vector n) i = int_add int_zero (A i (inr. star.))
          by refl ((t ↦ int_add t (A i (inr. star.))) : Int → Int)
               (int_fsum_zero n (j ↦ int_mul (A i (inl. j)) int_zero) (j ↦ refl int_zero))
        = A i (inr. star.) by int_add_zero_left (A i (inr. star.))
        = int_zero by imat_last_col_zero n A z g0 i ∎)))

def imat_kernel_extend (n : Nat) (A : IntMatrix (suc. n))
  (z : (i : Fin n) → Id Int (A (inl. i) (inr. star.)) int_zero) (g0 : Id Int (A (inr. star.) (inr. star.)) int_zero → Empty)
  (k : ImatKernelVector n (i j ↦ A (inl. i) (inl. j))) : ImatKernelVector (suc. n) A
  ≔ let g ≔ A (inr. star.) (inr. star.) in
    let y ≔ k .fst in
    let ry ≔ int_fsum n (j ↦ int_mul (A (inr. star.) (inl. j)) (y j)) in
    let x : Fin (suc. n) → Int ≔ [ inl. j ↦ int_mul g (y j) | inr. _ ↦ int_neg ry ] in
    let scaled : (i : Fin (suc. n)) → Id Int (int_fsum n (j ↦ int_mul (A i (inl. j)) (int_mul g (y j))))
                    (int_mul g (int_fsum n (j ↦ int_mul (A i (inl. j)) (y j))))
      ≔ i ↦ concat Int (int_fsum n (j ↦ int_mul (A i (inl. j)) (int_mul g (y j))))
              (int_fsum n (j ↦ int_mul g (int_mul (A i (inl. j)) (y j)))) (int_mul g (int_fsum n (j ↦ int_mul (A i (inl. j)) (y j))))
              (int_fsum_ext n (j ↦ int_mul (A i (inl. j)) (int_mul g (y j))) (j ↦ int_mul g (int_mul (A i (inl. j)) (y j)))
                (j ↦ imat_mul_swap_left (A i (inl. j)) g (y j)))
              (int_fsum_scale n g (j ↦ int_mul (A i (inl. j)) (y j))) in
    (x,
     ((h ↦ k .snd .fst (j ↦ imat_mul_zero_right_cancel g (y j) g0 (h (inl. j)))),
      (i ↦ match i [
        | inl. q ↦ calc
            int_mat_vec (suc. n) A x (inl. q) = int_add (int_mul g int_zero) (int_mul int_zero (int_neg ry))
              by refl int_add (concat Int (int_fsum n (j ↦ int_mul (A (inl. q) (inl. j)) (int_mul g (y j))))
                     (int_mul g (int_fsum n (j ↦ int_mul (A (inl. q) (inl. j)) (y j)))) (int_mul g int_zero)
                     (scaled (inl. q)) (refl (int_mul g) (k .snd .snd q)))
                   (refl ((t ↦ int_mul t (int_neg ry)) : Int → Int) (z q))
            = int_zero by refl (int_add (int_mul g int_zero)) (imat_mul_zero_left (int_neg ry)) ∎
        | inr. u ↦ match u [ star. ↦ calc
            int_mat_vec (suc. n) A x (inr. star.) = int_add (int_mul g ry) (int_neg (int_mul g ry))
              by refl int_add (scaled (inr. star.)) (int_mul_neg_right g ry)
            = int_zero by int_add_neg_right (int_mul g ry) ∎ ] ])))

def imat_kernel_cases (n : Nat) (A : IntMatrix (suc. n))
  (z : (i : Fin n) → Id Int (A (inl. i) (inr. star.)) int_zero)
  (kB : (Id Int (A (inr. star.) (inr. star.)) int_zero → Empty) → ImatKernelVector n (i j ↦ A (inl. i) (inl. j)))
  (d : Decidable (Id Int (A (inr. star.) (inr. star.)) int_zero)) : ImatKernelVector (suc. n) A
  ≔ match d [
  | inl. g0 ↦ imat_kernel_corner_zero n A z g0
  | inr. g0 ↦ imat_kernel_extend n A z g0 (kB g0) ]

def int_det_zero_kernel (n : Nat) (A : IntMatrix n) (h : Id Int (int_det n A) int_zero) : ImatKernelVector n A
  ≔ match n [
  | zero. ↦ match int_encode int_one int_zero h [ ]
  | suc. n ↦
    let E ≔ imat_eliminate n A in
    let A' ≔ E .fst in
    let z : (i : Fin n) → Id Int (A' (inl. i) (inr. star.)) int_zero ≔ i ↦ imat_eliminate_zero n A i in
    let B : IntMatrix n ≔ i j ↦ A' (inl. i) (inl. j) in
    let prod : Id Int (int_mul (A' (inr. star.) (inr. star.)) (int_det n B)) int_zero
      ≔ calc
          int_mul (A' (inr. star.) (inr. star.)) (int_det n B) = int_det (suc. n) A'
            by inverse Int (int_det (suc. n) A') (int_mul (A' (inr. star.) (inr. star.)) (int_det n B)) (int_det_block n A' z)
          = int_det (suc. n) A by E .snd .fst .fst
          = int_zero by h ∎ in
    imat_kernel_transfer (suc. n) A A' (E .snd .fst)
      (imat_kernel_cases n A' z (g0 ↦ int_det_zero_kernel n B (imat_mul_zero_right_cancel (A' (inr. star.) (inr. star.)) (int_det n B) g0 prod))
        (int_dec_eq (A' (inr. star.) (inr. star.)) int_zero)) ]

{` Block decomposition. `}
def imat_corner_diag (n : Nat) (g : Int) : Fin (suc. n) → Int ≔ [ inl. _ ↦ int_one | inr. _ ↦ g ]

def imat_lower (n : Nat) (r : Fin n → Int) (y : Fin (suc. n) → Int) : Fin (suc. n) → Int
  ≔ [ inl. k ↦ y (inl. k) | inr. _ ↦ int_add (int_fsum n (j ↦ int_mul (r j) (y (inl. j)))) (y (inr. star.)) ]

def imat_block1 (n : Nat) (F : (Fin n → Int) → Fin n → Int) (z : Fin (suc. n) → Int) : Fin (suc. n) → Int
  ≔ [ inl. k ↦ F (j ↦ z (inl. j)) k | inr. _ ↦ z (inr. star.) ]

def imat_rdot_add (n : Nat) (r x y : Fin n → Int)
  : Id Int (int_fsum n (j ↦ int_mul (r j) (int_add (x j) (y j))))
      (int_add (int_fsum n (j ↦ int_mul (r j) (x j))) (int_fsum n (j ↦ int_mul (r j) (y j))))
  ≔ concat Int (int_fsum n (j ↦ int_mul (r j) (int_add (x j) (y j)))) (int_fsum n (j ↦ int_add (int_mul (r j) (x j)) (int_mul (r j) (y j))))
      (int_add (int_fsum n (j ↦ int_mul (r j) (x j))) (int_fsum n (j ↦ int_mul (r j) (y j))))
      (int_fsum_ext n (j ↦ int_mul (r j) (int_add (x j) (y j))) (j ↦ int_add (int_mul (r j) (x j)) (int_mul (r j) (y j)))
        (j ↦ int_mul_ldistr (r j) (x j) (y j)))
      (int_fsum_add n (j ↦ int_mul (r j) (x j)) (j ↦ int_mul (r j) (y j)))

def imat_rdot_neg (n : Nat) (r : Fin n → Int) (x : Fin n → Int)
  : Id Int (int_fsum n (j ↦ int_mul (int_neg (r j)) (x j))) (int_neg (int_fsum n (j ↦ int_mul (r j) (x j))))
  ≔ concat Int (int_fsum n (j ↦ int_mul (int_neg (r j)) (x j))) (int_fsum n (j ↦ int_neg (int_mul (r j) (x j))))
      (int_neg (int_fsum n (j ↦ int_mul (r j) (x j))))
      (int_fsum_ext n (j ↦ int_mul (int_neg (r j)) (x j)) (j ↦ int_neg (int_mul (r j) (x j))) (j ↦ imat_mul_neg_left (r j) (x j)))
      (int_fsum_neg n (j ↦ int_mul (r j) (x j)))

def imat_lower_unimod (n : Nat) (r : Fin n → Int) : IntVecUnimodular (suc. n) (imat_lower n r)
  ≔ let dot : (Fin n → Int) → (Fin n → Int) → Int ≔ s x ↦ int_fsum n (j ↦ int_mul (s j) (x j)) in
    (imat_lower n (j ↦ int_neg (r j)),
     ((x y i ↦ match i [
        | inl. k ↦ refl (int_add (x (inl. k)) (y (inl. k)))
        | inr. u ↦ match u [ star. ↦ calc
            int_add (dot r (j ↦ int_add (x (inl. j)) (y (inl. j)))) (int_add (x (inr. star.)) (y (inr. star.)))
            = int_add (int_add (dot r (j ↦ x (inl. j))) (dot r (j ↦ y (inl. j)))) (int_add (x (inr. star.)) (y (inr. star.)))
              by refl ((t ↦ int_add t (int_add (x (inr. star.)) (y (inr. star.)))) : Int → Int)
                   (imat_rdot_add n r (j ↦ x (inl. j)) (j ↦ y (inl. j)))
            = int_add (int_add (dot r (j ↦ x (inl. j))) (x (inr. star.))) (int_add (dot r (j ↦ y (inl. j))) (y (inr. star.)))
              by int_add_interchange (dot r (j ↦ x (inl. j))) (dot r (j ↦ y (inl. j))) (x (inr. star.)) (y (inr. star.)) ∎ ] ]),
      ((x i ↦ match i [
         | inl. k ↦ refl (x (inl. k))
         | inr. u ↦ match u [ star. ↦ calc
             int_add (dot r (j ↦ x (inl. j))) (int_add (dot (j ↦ int_neg (r j)) (j ↦ x (inl. j))) (x (inr. star.)))
             = int_add (dot r (j ↦ x (inl. j))) (int_add (int_neg (dot r (j ↦ x (inl. j)))) (x (inr. star.)))
               by refl ((t ↦ int_add (dot r (j ↦ x (inl. j))) (int_add t (x (inr. star.)))) : Int → Int)
                    (imat_rdot_neg n r (j ↦ x (inl. j)))
             = x (inr. star.) by int_translate_inverse_other (dot r (j ↦ x (inl. j))) (x (inr. star.)) ∎ ] ]),
       (x i ↦ match i [
         | inl. k ↦ refl (x (inl. k))
         | inr. u ↦ match u [ star. ↦ calc
             int_add (dot (j ↦ int_neg (r j)) (j ↦ x (inl. j))) (int_add (dot r (j ↦ x (inl. j))) (x (inr. star.)))
             = int_add (int_neg (dot r (j ↦ x (inl. j)))) (int_add (dot r (j ↦ x (inl. j))) (x (inr. star.)))
               by refl ((t ↦ int_add t (int_add (dot r (j ↦ x (inl. j))) (x (inr. star.)))) : Int → Int)
                    (imat_rdot_neg n r (j ↦ x (inl. j)))
             = x (inr. star.) by int_translate_inverse (dot r (j ↦ x (inl. j))) (x (inr. star.)) ∎ ] ]))))

def imat_block1_unimod (n : Nat) (F : (Fin n → Int) → Fin n → Int) (u : IntVecUnimodular n F)
  : IntVecUnimodular (suc. n) (imat_block1 n F)
  ≔ (imat_block1 n (u .fst),
     ((x y i ↦ match i [
        | inl. k ↦ u .snd .fst (j ↦ x (inl. j)) (j ↦ y (inl. j)) k
        | inr. v ↦ match v [ star. ↦ refl (int_add (x (inr. star.)) (y (inr. star.))) ] ]),
      ((x i ↦ match i [
         | inl. k ↦ u .snd .snd .fst (j ↦ x (inl. j)) k
         | inr. v ↦ match v [ star. ↦ refl (x (inr. star.)) ] ]),
       (x i ↦ match i [
         | inl. k ↦ u .snd .snd .snd (j ↦ x (inl. j)) k
         | inr. v ↦ match v [ star. ↦ refl (x (inr. star.)) ] ]))))

def imat_block_decomposition (n : Nat) (A : IntMatrix (suc. n))
  (z : (i : Fin n) → Id Int (A (inl. i) (inr. star.)) int_zero) (x : Fin (suc. n) → Int) (i : Fin (suc. n))
  : Id Int (int_mat_vec (suc. n) A x i)
      (imat_block1 n (int_mat_vec n (i' j ↦ A (inl. i') (inl. j)))
        (imat_lower n (j ↦ A (inr. star.) (inl. j)) (int_diag_map (suc. n) (imat_corner_diag n (A (inr. star.) (inr. star.))) x)) i)
  ≔ match i [
  | inl. k ↦ refl (int_add (int_fsum n (j ↦ int_mul (A (inl. k) (inl. j)) (x (inl. j)))))
      (concat Int (int_mul (A (inl. k) (inr. star.)) (x (inr. star.))) (int_mul int_zero (x (inr. star.))) int_zero
        (refl ((t ↦ int_mul t (x (inr. star.))) : Int → Int) (z k)) (imat_mul_zero_left (x (inr. star.))))
  | inr. u ↦ match u [ star. ↦
      refl (int_add (int_fsum n (j ↦ int_mul (A (inr. star.) (inl. j)) (x (inl. j)))))
        (int_mul_comm (A (inr. star.) (inr. star.)) (x (inr. star.))) ] ]
