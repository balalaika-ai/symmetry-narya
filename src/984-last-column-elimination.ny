export "983-determinant-row-operations"

{` Chapter 9 (subgroups.tex 1186): Euclid's algorithm on the last column.
   ImatRel A A' says det A' = det A and A · x = U(A' · x) for a unimodular
   U (pointwise in x). The two row operations of module 983 give such
   relations (U is the inverse operation on vectors). For every i, a
   sequence of operations between row i and the last row clears the entry
   (i, last) (strong induction on |entry| by fuel, division with remainder
   of module 55) without changing the other entries of the last column;
   iterating over all rows gives A' with last column (0, …, 0, g). `}

def imat_upd_other (m n : Nat) (R : Fin m → Fin n → Int) (q : Fin m) (r : Fin n → Int) (i : Fin m) (j : Fin n)
  (h : Id Bool (imat_fin_eqb m i q) false.)
  : Id Int (imat_upd m n R q r i j) (R i j)
  ≔ match m [
  | zero. ↦ match q [ ]
  | suc. m ↦ match q [
    | inl. q ↦ match i [
      | inl. i ↦ imat_upd_other m n (i' ↦ R (inl. i')) q r i j h
      | inr. u ↦ match u [ star. ↦ refl (R (inr. star.) j) ] ]
    | inr. v ↦ match v [ star. ↦ match i [
      | inl. i ↦ refl (R (inl. i) j)
      | inr. u ↦ match bool_encode true. false. h [ ] ] ] ] ]

def imat_upd_eqb_true (m n : Nat) (R : Fin m → Fin n → Int) (q : Fin m) (r : Fin n → Int) (i : Fin m) (j : Fin n)
  (h : Id Bool (imat_fin_eqb m i q) true.)
  : Id Int (imat_upd m n R q r i j) (r j)
  ≔ concat Int (imat_upd m n R q r i j) (imat_upd m n R q r q j) (r j)
      (refl ((t ↦ imat_upd m n R q r t j) : Fin m → Int) (imat_fin_eqb_id m i q h)) (imat_upd_at m n R q r j)

{` Unimodular maps compose. `}
def imat_unimod_id (n : Nat) : IntVecUnimodular n (x ↦ x)
  ≔ ((x ↦ x), ((x y i ↦ refl (int_add (x i) (y i))), ((x i ↦ refl (x i)), (x i ↦ refl (x i)))))

def imat_unimod_compose (n : Nat) (F1 F2 : (Fin n → Int) → Fin n → Int) (u1 : IntVecUnimodular n F1) (u2 : IntVecUnimodular n F2)
  : IntVecUnimodular n (x ↦ F1 (F2 x))
  ≔ let G1 ≔ u1 .fst in let G2 ≔ u2 .fst in
    let fe : (f g : Fin n → Int) → ((i : Fin n) → Id Int (f i) (g i)) → Id (Fin n → Int) f g ≔ f g h ↦ funext (Fin n) (_ ↦ Int) f g h in
    ((x ↦ G2 (G1 x)),
     ((x y i ↦ concat Int (F1 (F2 (int_vec_add n x y)) i) (F1 (int_vec_add n (F2 x) (F2 y)) i)
         (int_add (F1 (F2 x) i) (F1 (F2 y) i))
         (refl ((v ↦ F1 v i) : (Fin n → Int) → Int) (fe (F2 (int_vec_add n x y)) (int_vec_add n (F2 x) (F2 y)) (u2 .snd .fst x y)))
         (u1 .snd .fst (F2 x) (F2 y) i)),
      ((x i ↦ concat Int (F1 (F2 (G2 (G1 x))) i) (F1 (G1 x) i) (x i)
          (refl ((v ↦ F1 v i) : (Fin n → Int) → Int) (fe (F2 (G2 (G1 x))) (G1 x) (u2 .snd .snd .fst (G1 x))))
          (u1 .snd .snd .fst x i)),
       (x i ↦ concat Int (G2 (G1 (F1 (F2 x))) i) (G2 (F2 x) i) (x i)
          (refl ((v ↦ G2 v i) : (Fin n → Int) → Int) (fe (G1 (F1 (F2 x))) (F2 x) (u1 .snd .snd .snd (F2 x))))
          (u2 .snd .snd .snd x i)))))

{` The relation produced by row operations. `}
def ImatRel (n : Nat) (A A' : IntMatrix n) : Type
  ≔ Product (Id Int (int_det n A') (int_det n A))
      (Σ ((Fin n → Int) → Fin n → Int) (F ↦ Product (IntVecUnimodular n F)
        ((x : Fin n → Int) (i : Fin n) → Id Int (int_mat_vec n A x i) (F (int_mat_vec n A' x) i))))

def imat_rel_refl (n : Nat) (A : IntMatrix n) : ImatRel n A A
  ≔ (refl (int_det n A), ((x ↦ x), (imat_unimod_id n, (x i ↦ refl (int_mat_vec n A x i)))))

def imat_rel_trans (n : Nat) (A A1 A2 : IntMatrix n) (r1 : ImatRel n A A1) (r2 : ImatRel n A1 A2) : ImatRel n A A2
  ≔ let F1 ≔ r1 .snd .fst in let F2 ≔ r2 .snd .fst in
    (concat Int (int_det n A2) (int_det n A1) (int_det n A) (r2 .fst) (r1 .fst),
     ((x ↦ F1 (F2 x)),
      (imat_unimod_compose n F1 F2 (r1 .snd .snd .fst) (r2 .snd .snd .fst),
       (x i ↦ concat Int (int_mat_vec n A x i) (F1 (int_mat_vec n A1 x) i) (F1 (F2 (int_mat_vec n A2 x)) i)
          (r1 .snd .snd .snd x i)
          (refl ((v ↦ F1 v i) : (Fin n → Int) → Int)
            (funext (Fin n) (_ ↦ Int) (int_mat_vec n A1 x) (F2 (int_mat_vec n A2 x)) (r2 .snd .snd .snd x)))))))

{` Integer arithmetic. `}
def imat_add_lin (xl yl xp yp c : Int)
  : Id Int (int_add (int_add xl yl) (int_mul c (int_add xp yp))) (int_add (int_add xl (int_mul c xp)) (int_add yl (int_mul c yp)))
  ≔ concat Int (int_add (int_add xl yl) (int_mul c (int_add xp yp))) (int_add (int_add xl yl) (int_add (int_mul c xp) (int_mul c yp)))
      (int_add (int_add xl (int_mul c xp)) (int_add yl (int_mul c yp)))
      (refl (int_add (int_add xl yl)) (int_mul_ldistr c xp yp))
      (int_add_interchange xl yl (int_mul c xp) (int_mul c yp))

def imat_cancel_a (a b c : Int) : Id Int (int_add (int_add a (int_mul (int_neg c) b)) (int_mul c b)) a
  ≔ concat Int (int_add (int_add a (int_mul (int_neg c) b)) (int_mul c b)) (int_add (int_sub a (int_mul c b)) (int_mul c b)) a
      (refl ((t ↦ int_add (int_add a t) (int_mul c b)) : Int → Int) (imat_mul_neg_left c b))
      (int_sub_add a (int_mul c b))

def imat_cancel_b (a b c : Int) : Id Int (int_add (int_add a (int_mul c b)) (int_mul (int_neg c) b)) a
  ≔ concat Int (int_add (int_add a (int_mul c b)) (int_mul (int_neg c) b)) (int_sub (int_add a (int_mul c b)) (int_mul c b)) a
      (refl (int_add (int_add a (int_mul c b))) (imat_mul_neg_left c b))
      (int_add_sub a (int_mul c b))

{` The vector operations. `}
def imat_vop_last (n : Nat) (p : Fin n) (c : Int) (y : Fin (suc. n) → Int) : Fin (suc. n) → Int
  ≔ [ inl. k ↦ y (inl. k) | inr. _ ↦ int_add (y (inr. star.)) (int_mul c (y (inl. p))) ]

def imat_vop_row (n : Nat) (p : Fin n) (c : Int) (y : Fin (suc. n) → Int) : Fin (suc. n) → Int
  ≔ [ inl. k ↦ int_add (y (inl. k)) (imat_bif (imat_fin_eqb n k p) (int_mul c (y (inr. star.)))) | inr. _ ↦ y (inr. star.) ]

def imat_vop_last_unimod (n : Nat) (p : Fin n) (c : Int) : IntVecUnimodular (suc. n) (imat_vop_last n p c)
  ≔ (imat_vop_last n p (int_neg c),
     ((x y i ↦ match i [
        | inl. k ↦ refl (int_add (x (inl. k)) (y (inl. k)))
        | inr. u ↦ match u [ star. ↦ imat_add_lin (x (inr. star.)) (y (inr. star.)) (x (inl. p)) (y (inl. p)) c ] ]),
      ((x i ↦ match i [
         | inl. k ↦ refl (x (inl. k))
         | inr. u ↦ match u [ star. ↦ imat_cancel_a (x (inr. star.)) (x (inl. p)) c ] ]),
       (x i ↦ match i [
         | inl. k ↦ refl (x (inl. k))
         | inr. u ↦ match u [ star. ↦ imat_cancel_b (x (inr. star.)) (x (inl. p)) c ] ]))))

def imat_bif_add_lin (e : Bool) (xk yk xl yl c : Int)
  : Id Int (int_add (int_add xk yk) (imat_bif e (int_mul c (int_add xl yl))))
      (int_add (int_add xk (imat_bif e (int_mul c xl))) (int_add yk (imat_bif e (int_mul c yl))))
  ≔ match e [ true. ↦ imat_add_lin xk yk xl yl c | false. ↦ refl (int_add xk yk) ]

def imat_bif_cancel_a (e : Bool) (a b c : Int)
  : Id Int (int_add (int_add a (imat_bif e (int_mul (int_neg c) b))) (imat_bif e (int_mul c b))) a
  ≔ match e [ true. ↦ imat_cancel_a a b c | false. ↦ refl a ]

def imat_bif_cancel_b (e : Bool) (a b c : Int)
  : Id Int (int_add (int_add a (imat_bif e (int_mul c b))) (imat_bif e (int_mul (int_neg c) b))) a
  ≔ match e [ true. ↦ imat_cancel_b a b c | false. ↦ refl a ]

def imat_vop_row_unimod (n : Nat) (p : Fin n) (c : Int) : IntVecUnimodular (suc. n) (imat_vop_row n p c)
  ≔ (imat_vop_row n p (int_neg c),
     ((x y i ↦ match i [
        | inl. k ↦ imat_bif_add_lin (imat_fin_eqb n k p) (x (inl. k)) (y (inl. k)) (x (inr. star.)) (y (inr. star.)) c
        | inr. u ↦ match u [ star. ↦ refl (int_add (x (inr. star.)) (y (inr. star.))) ] ]),
      ((x i ↦ match i [
         | inl. k ↦ imat_bif_cancel_a (imat_fin_eqb n k p) (x (inl. k)) (x (inr. star.)) c
         | inr. u ↦ match u [ star. ↦ refl (x (inr. star.)) ] ]),
       (x i ↦ match i [
         | inl. k ↦ imat_bif_cancel_b (imat_fin_eqb n k p) (x (inl. k)) (x (inr. star.)) c
         | inr. u ↦ match u [ star. ↦ refl (x (inr. star.)) ] ]))))

{` A row of A' that is row i of A plus c times row k of A. `}
def imat_mat_vec_rowcomb (n : Nat) (A A' : IntMatrix n) (i k : Fin n) (c : Int)
  (h : (j : Fin n) → Id Int (A' i j) (int_add (A i j) (int_mul c (A k j)))) (x : Fin n → Int)
  : Id Int (int_mat_vec n A' x i) (int_add (int_mat_vec n A x i) (int_mul c (int_mat_vec n A x k)))
  ≔ calc
      int_mat_vec n A' x i = int_fsum n (j ↦ int_add (int_mul (A i j) (x j)) (int_mul c (int_mul (A k j) (x j))))
        by int_fsum_ext n (j ↦ int_mul (A' i j) (x j)) (j ↦ int_add (int_mul (A i j) (x j)) (int_mul c (int_mul (A k j) (x j))))
             (j ↦ calc
               int_mul (A' i j) (x j) = int_mul (int_add (A i j) (int_mul c (A k j))) (x j)
                 by refl ((t ↦ int_mul t (x j)) : Int → Int) (h j)
               = int_add (int_mul (A i j) (x j)) (int_mul (int_mul c (A k j)) (x j)) by int_mul_rdistr (A i j) (int_mul c (A k j)) (x j)
               = int_add (int_mul (A i j) (x j)) (int_mul c (int_mul (A k j) (x j)))
                 by refl (int_add (int_mul (A i j) (x j)))
                      (inverse Int (int_mul c (int_mul (A k j) (x j))) (int_mul (int_mul c (A k j)) (x j)) (int_mul_assoc c (A k j) (x j))) ∎)
      = int_add (int_mat_vec n A x i) (int_fsum n (j ↦ int_mul c (int_mul (A k j) (x j))))
        by int_fsum_add n (j ↦ int_mul (A i j) (x j)) (j ↦ int_mul c (int_mul (A k j) (x j)))
      = int_add (int_mat_vec n A x i) (int_mul c (int_mat_vec n A x k))
        by refl (int_add (int_mat_vec n A x i)) (int_fsum_scale n c (j ↦ int_mul (A k j) (x j))) ∎

def imat_rel_op_last (n : Nat) (A : IntMatrix (suc. n)) (p : Fin n) (c : Int)
  : ImatRel (suc. n) A (imat_op_last n (suc. n) A p c)
  ≔ let A' ≔ imat_op_last n (suc. n) A p c in
    (imat_minor_op_last n (suc. n) A p c (_ ↦ true.),
     (imat_vop_last n p (int_neg c),
      (imat_vop_last_unimod n p (int_neg c),
       (x i ↦ match i [
         | inl. k ↦ refl (int_mat_vec (suc. n) A x (inl. k))
         | inr. u ↦ match u [ star. ↦ inverse Int
             (int_add (int_mat_vec (suc. n) A' x (inr. star.)) (int_mul (int_neg c) (int_mat_vec (suc. n) A x (inl. p))))
             (int_mat_vec (suc. n) A x (inr. star.))
             (concat Int
               (int_add (int_mat_vec (suc. n) A' x (inr. star.)) (int_mul (int_neg c) (int_mat_vec (suc. n) A x (inl. p))))
               (int_add (int_add (int_mat_vec (suc. n) A x (inr. star.)) (int_mul c (int_mat_vec (suc. n) A x (inl. p))))
                 (int_mul (int_neg c) (int_mat_vec (suc. n) A x (inl. p))))
               (int_mat_vec (suc. n) A x (inr. star.))
               (refl ((t ↦ int_add t (int_mul (int_neg c) (int_mat_vec (suc. n) A x (inl. p)))) : Int → Int)
                 (imat_mat_vec_rowcomb (suc. n) A A' (inr. star.) (inl. p) c (j ↦ refl (A' (inr. star.) j)) x))
               (imat_cancel_b (int_mat_vec (suc. n) A x (inr. star.)) (int_mat_vec (suc. n) A x (inl. p)) c)) ] ]))))

def imat_rel_op_row_inl (n : Nat) (A : IntMatrix (suc. n)) (p : Fin n) (c : Int) (x : Fin (suc. n) → Int) (k : Fin n)
  (e : Bool) (he : Id Bool (imat_fin_eqb n k p) e)
  : Id Int (int_mat_vec (suc. n) A x (inl. k))
      (int_add (int_mat_vec (suc. n) (imat_op_row n (suc. n) A p c) x (inl. k))
        (imat_bif e (int_mul (int_neg c) (int_mat_vec (suc. n) A x (inr. star.)))))
  ≔ let A' ≔ imat_op_row n (suc. n) A p c in
    let w : Fin (suc. n) → Int ≔ j ↦ int_add (A (inl. p) j) (int_mul c (A (inr. star.) j)) in
    match e [
    | true. ↦
      let kp : Id (Fin n) k p ≔ imat_fin_eqb_id n k p he in
      inverse Int
        (int_add (int_mat_vec (suc. n) A' x (inl. k)) (int_mul (int_neg c) (int_mat_vec (suc. n) A x (inr. star.))))
        (int_mat_vec (suc. n) A x (inl. k))
        (concat Int
          (int_add (int_mat_vec (suc. n) A' x (inl. k)) (int_mul (int_neg c) (int_mat_vec (suc. n) A x (inr. star.))))
          (int_add (int_add (int_mat_vec (suc. n) A x (inl. k)) (int_mul c (int_mat_vec (suc. n) A x (inr. star.))))
            (int_mul (int_neg c) (int_mat_vec (suc. n) A x (inr. star.))))
          (int_mat_vec (suc. n) A x (inl. k))
          (refl ((t ↦ int_add t (int_mul (int_neg c) (int_mat_vec (suc. n) A x (inr. star.)))) : Int → Int)
            (imat_mat_vec_rowcomb (suc. n) A A' (inl. k) (inr. star.) c
              (j ↦ concat Int (A' (inl. k) j) (w j) (int_add (A (inl. k) j) (int_mul c (A (inr. star.) j)))
                (imat_upd_eqb_true (suc. n) (suc. n) A (inl. p) w (inl. k) j he)
                (refl ((t ↦ int_add (A (inl. t) j) (int_mul c (A (inr. star.) j))) : Fin n → Int)
                  (inverse (Fin n) k p kp))) x))
          (imat_cancel_b (int_mat_vec (suc. n) A x (inl. k)) (int_mat_vec (suc. n) A x (inr. star.)) c))
    | false. ↦
      inverse Int (int_mat_vec (suc. n) A' x (inl. k)) (int_mat_vec (suc. n) A x (inl. k))
        (int_fsum_ext (suc. n) (j ↦ int_mul (A' (inl. k) j) (x j)) (j ↦ int_mul (A (inl. k) j) (x j))
          (j ↦ refl ((t ↦ int_mul t (x j)) : Int → Int) (imat_upd_other (suc. n) (suc. n) A (inl. p) w (inl. k) j he))) ]

def imat_rel_op_row (n : Nat) (A : IntMatrix (suc. n)) (p : Fin n) (c : Int)
  : ImatRel (suc. n) A (imat_op_row n (suc. n) A p c)
  ≔ (imat_minor_op_row n (suc. n) A p c (_ ↦ true.),
     (imat_vop_row n p (int_neg c),
      (imat_vop_row_unimod n p (int_neg c),
       (x i ↦ match i [
         | inl. k ↦ imat_rel_op_row_inl n A p c x k (imat_fin_eqb n k p) (refl (imat_fin_eqb n k p))
         | inr. u ↦ match u [ star. ↦ refl (int_mat_vec (suc. n) A x (inr. star.)) ] ]))))

{` Division with remainder: b + c · a = r with 0 ≤ r < |a|. `}
def imat_divmod_pos (m : Nat) (b : Int)
  : Σ Int (c ↦ Σ Nat (r ↦ Product (Id Int (int_add b (int_mul c (pos. (suc. m)))) (pos. r)) (Lt r (suc. m))))
  ≔ let u ≔ integer_euclidean_division b (suc. m) (suc. m, ((p ↦ nat_encode (suc. m) zero. p), refl (suc. m))) in
    let q ≔ u .fst .fst in let r ≔ u .fst .snd in
    let qm ≔ int_mul q (pos. (suc. m)) in
    (int_neg q, (r,
      (calc
        int_add b (int_mul (int_neg q) (pos. (suc. m))) = int_add (int_add qm (pos. r)) (int_mul (int_neg q) (pos. (suc. m)))
          by refl ((t ↦ int_add t (int_mul (int_neg q) (pos. (suc. m)))) : Int → Int) (u .snd .snd)
        = int_add (int_add (pos. r) qm) (int_neg qm)
          by refl int_add (int_add_comm qm (pos. r)) (imat_mul_neg_left q (pos. (suc. m)))
        = pos. r by int_add_sub (pos. r) qm ∎,
       lt_from_book r (suc. m) (u .snd .fst))))

def imat_divmod_neg (k : Nat) (b : Int)
  : Σ Int (c ↦ Σ Nat (r ↦ Product (Id Int (int_add b (int_mul c (neg. k))) (pos. r)) (Lt r (suc. k))))
  ≔ let u ≔ integer_euclidean_division b (suc. k) (suc. k, ((p ↦ nat_encode (suc. k) zero. p), refl (suc. k))) in
    let q ≔ u .fst .fst in let r ≔ u .fst .snd in
    let qm ≔ int_mul q (pos. (suc. k)) in
    (q, (r,
      (calc
        int_add b (int_mul q (neg. k)) = int_add (int_add qm (pos. r)) (int_neg qm)
          by refl int_add (u .snd .snd) (int_mul_neg_right q (pos. (suc. k)))
        = int_add (int_add (pos. r) qm) (int_neg qm)
          by refl ((t ↦ int_add t (int_neg qm)) : Int → Int) (int_add_comm qm (pos. r))
        = pos. r by int_add_sub (pos. r) qm ∎,
       lt_from_book r (suc. k) (u .snd .fst))))

{` For a ≠ 0: b + c · a = r with r ≤ int_magnitude a. `}
def imat_divmod (a : Int) (ha : Id Int a int_zero → Empty) (b : Int)
  : Σ Int (c ↦ Σ Nat (r ↦ Product (Id Int (int_add b (int_mul c a)) (pos. r)) (Le r (int_magnitude a))))
  ≔ match a [
  | pos. n ↦ match n [
    | zero. ↦ match ha (refl int_zero) [ ]
    | suc. m ↦ let d ≔ imat_divmod_pos m b in
        (d .fst, (d .snd .fst, (d .snd .snd .fst, le_step (d .snd .fst) m (d .snd .snd .snd)))) ]
  | neg. k ↦ imat_divmod_neg k b ]

{` Clearing entry (i, last). `}
def ImatPairRes (n : Nat) (i : Fin n) (A : IntMatrix (suc. n)) : Type
  ≔ Σ (IntMatrix (suc. n)) (A' ↦ Product (ImatRel (suc. n) A A')
      (Product (Id Int (A' (inl. i) (inr. star.)) int_zero)
        ((k : Fin n) → Id Bool (imat_fin_eqb n k i) false. → Id Int (A' (inl. k) (inr. star.)) (A (inl. k) (inr. star.)))))

def imat_pair_prepend (n : Nat) (i : Fin n) (A A1 : IntMatrix (suc. n)) (r : ImatRel (suc. n) A A1)
  (pres : (k : Fin n) → Id Bool (imat_fin_eqb n k i) false. → Id Int (A1 (inl. k) (inr. star.)) (A (inl. k) (inr. star.)))
  (res : ImatPairRes n i A1) : ImatPairRes n i A
  ≔ (res .fst, (imat_rel_trans (suc. n) A A1 (res .fst) r (res .snd .fst), (res .snd .snd .fst,
      (k hk ↦ concat Int (res .fst (inl. k) (inr. star.)) (A1 (inl. k) (inr. star.)) (A (inl. k) (inr. star.))
        (res .snd .snd .snd k hk) (pres k hk)))))

def imat_pair_finish (n : Nat) (i : Fin n) (A1 : IntMatrix (suc. n))
  (h0 : Id Int (A1 (inr. star.) (inr. star.)) int_zero) : ImatPairRes n i A1
  ≔ let a ≔ A1 (inl. i) (inr. star.) in
    let A2 ≔ imat_op_last n (suc. n) A1 i int_one in
    let A3 ≔ imat_op_row n (suc. n) A2 i (neg. zero.) in
    (A3, (imat_rel_trans (suc. n) A1 A2 A3 (imat_rel_op_last n A1 i int_one) (imat_rel_op_row n A2 i (neg. zero.)),
      (calc
        A3 (inl. i) (inr. star.) = int_add a (int_mul (neg. zero.) (int_add (A1 (inr. star.) (inr. star.)) (int_mul int_one a)))
          by imat_upd_at (suc. n) (suc. n) A2 (inl. i) (j ↦ int_add (A2 (inl. i) j) (int_mul (neg. zero.) (A2 (inr. star.) j))) (inr. star.)
        = int_add a (int_mul (neg. zero.) (int_add int_zero a))
          by refl (int_add a) (refl (int_mul (neg. zero.)) (refl int_add h0 (int_mul_one_left a)))
        = int_add a (int_neg (int_mul int_one a))
          by refl (int_add a) (concat Int (int_mul (neg. zero.) (int_add int_zero a)) (int_mul (neg. zero.) a) (int_neg (int_mul int_one a))
               (refl (int_mul (neg. zero.)) (int_add_zero_left a)) (imat_mul_neg_left int_one a))
        = int_add a (int_neg a) by refl (int_add a) (refl int_neg (int_mul_one_left a))
        = int_zero by int_add_neg_right a ∎,
       (k hk ↦ imat_upd_other (suc. n) (suc. n) A2 (inl. i) (j ↦ int_add (A2 (inl. i) j) (int_mul (neg. zero.) (A2 (inr. star.) j)))
          (inl. k) (inr. star.) hk))))

{` A1 has entries (a, r) in rows (i, last), r ≤ N; recur handles smaller entries. `}
def imat_pair_step (n : Nat) (i : Fin n) (N : Nat)
  (recur : (A2 : IntMatrix (suc. n)) → Lt (int_magnitude (A2 (inl. i) (inr. star.))) N → ImatPairRes n i A2)
  (A1 : IntMatrix (suc. n)) (r : Nat)
  (e1 : Id Int (A1 (inr. star.) (inr. star.)) (pos. r)) (hr : Le r N) : ImatPairRes n i A1
  ≔ match r [
  | zero. ↦ imat_pair_finish n i A1 e1
  | suc. r0 ↦
    let a ≔ A1 (inl. i) (inr. star.) in
    let d2 ≔ imat_divmod_pos r0 a in
    let A2 ≔ imat_op_row n (suc. n) A1 i (d2 .fst) in
    let w : Fin (suc. n) → Int ≔ j ↦ int_add (A1 (inl. i) j) (int_mul (d2 .fst) (A1 (inr. star.) j)) in
    let e2 : Id Int (A2 (inl. i) (inr. star.)) (pos. (d2 .snd .fst))
      ≔ calc
          A2 (inl. i) (inr. star.) = int_add a (int_mul (d2 .fst) (A1 (inr. star.) (inr. star.)))
            by imat_upd_at (suc. n) (suc. n) A1 (inl. i) w (inr. star.)
          = int_add a (int_mul (d2 .fst) (pos. (suc. r0))) by refl (int_add a) (refl (int_mul (d2 .fst)) e1)
          = pos. (d2 .snd .fst) by d2 .snd .snd .fst ∎ in
    imat_pair_prepend n i A1 A2 (imat_rel_op_row n A1 i (d2 .fst))
      (k hk ↦ imat_upd_other (suc. n) (suc. n) A1 (inl. i) w (inl. k) (inr. star.) hk)
      (recur A2
        (transport Int (t ↦ Lt (int_magnitude t) N) (pos. (d2 .snd .fst)) (A2 (inl. i) (inr. star.))
          (inverse Int (A2 (inl. i) (inr. star.)) (pos. (d2 .snd .fst)) e2)
          (le_trans (suc. (d2 .snd .fst)) (suc. r0) N (d2 .snd .snd .snd) hr))) ]

def imat_pair (n : Nat) (i : Fin n) (N : Nat) (A : IntMatrix (suc. n))
  (hN : Lt (int_magnitude (A (inl. i) (inr. star.))) N) : ImatPairRes n i A
  ≔ match N [
  | zero. ↦ match hN [ ]
  | suc. N ↦ match int_dec_eq (A (inl. i) (inr. star.)) int_zero [
    | inl. h0 ↦ (A, (imat_rel_refl (suc. n) A, (h0, (k _ ↦ refl (A (inl. k) (inr. star.))))))
    | inr. ha ↦
      let a ≔ A (inl. i) (inr. star.) in
      let d1 ≔ imat_divmod a ha (A (inr. star.) (inr. star.)) in
      let A1 ≔ imat_op_last n (suc. n) A i (d1 .fst) in
      let e1 : Id Int (A1 (inr. star.) (inr. star.)) (pos. (d1 .snd .fst)) ≔ d1 .snd .snd .fst in
      imat_pair_prepend n i A A1 (imat_rel_op_last n A i (d1 .fst)) (k _ ↦ refl (A (inl. k) (inr. star.)))
        (imat_pair_step n i N (imat_pair n i N) A1 (d1 .snd .fst) e1
          (le_trans (d1 .snd .fst) (int_magnitude a) N (d1 .snd .snd .snd) hN)) ] ]

{` Clearing all rows of a list, then all rows. `}
def ImatInList (n : Nat) (i : Fin n) (l : List (Fin n)) : Type
  ≔ match l [ nil. ↦ Empty | cons. j l ↦ Sum (Id (Fin n) i j) (ImatInList n i l) ]

def imat_list_inl (n : Nat) (l : List (Fin n)) : List (Fin (suc. n))
  ≔ match l [ nil. ↦ nil. | cons. j l ↦ cons. (inl. j) (imat_list_inl n l) ]

def imat_in_list_inl (n : Nat) (i : Fin n) (l : List (Fin n)) (h : ImatInList n i l)
  : ImatInList (suc. n) (inl. i) (imat_list_inl n l)
  ≔ match l [
  | nil. ↦ match h [ ]
  | cons. j l ↦ match h [
    | inl. e ↦ inl. (refl ((x ↦ inl. x) : Fin n → Fin (suc. n)) e)
    | inr. h ↦ inr. (imat_in_list_inl n i l h) ] ]

def imat_fin_all (n : Nat) : List (Fin n)
  ≔ match n [ zero. ↦ nil. | suc. n ↦ cons. (inr. star.) (imat_list_inl n (imat_fin_all n)) ]

def imat_fin_all_in (n : Nat) (i : Fin n) : ImatInList n i (imat_fin_all n)
  ≔ match n [
  | zero. ↦ match i [ ]
  | suc. n ↦ match i [
    | inl. i ↦ inr. (imat_in_list_inl n i (imat_fin_all n) (imat_fin_all_in n i))
    | inr. u ↦ match u [ star. ↦ inl. (refl (inr. star. : Fin (suc. n))) ] ] ]

def ImatCleared (n : Nat) (A : IntMatrix (suc. n)) (l : List (Fin n)) : Type
  ≔ Σ (IntMatrix (suc. n)) (A' ↦ Product (ImatRel (suc. n) A A')
      ((i : Fin n) → ImatInList n i l → Id Int (A' (inl. i) (inr. star.)) int_zero))

def imat_clear_keep (n : Nat) (A1 A2 : IntMatrix (suc. n)) (j i : Fin n)
  (keep : Id Bool (imat_fin_eqb n i j) false. → Id Int (A2 (inl. i) (inr. star.)) (A1 (inl. i) (inr. star.)))
  (z1 : Id Int (A1 (inl. i) (inr. star.)) int_zero) (e : Bool) (he : Id Bool (imat_fin_eqb n i j) e)
  (zj : Id Int (A2 (inl. j) (inr. star.)) int_zero)
  : Id Int (A2 (inl. i) (inr. star.)) int_zero
  ≔ match e [
  | true. ↦ transport (Fin n) (t ↦ Id Int (A2 (inl. t) (inr. star.)) int_zero) j i
      (inverse (Fin n) i j (imat_fin_eqb_id n i j he)) zj
  | false. ↦ concat Int (A2 (inl. i) (inr. star.)) (A1 (inl. i) (inr. star.)) int_zero (keep he) z1 ]

def imat_clear_list (n : Nat) (A : IntMatrix (suc. n)) (l : List (Fin n)) : ImatCleared n A l
  ≔ match l [
  | nil. ↦ (A, (imat_rel_refl (suc. n) A, (i h ↦ match h [ ])))
  | cons. j l ↦
    let c1 ≔ imat_clear_list n A l in
    let A1 ≔ c1 .fst in
    let p ≔ imat_pair n j (suc. (int_magnitude (A1 (inl. j) (inr. star.)))) A1 (le_refl (int_magnitude (A1 (inl. j) (inr. star.)))) in
    (p .fst, (imat_rel_trans (suc. n) A A1 (p .fst) (c1 .snd .fst) (p .snd .fst),
      (i h ↦ match h [
        | inl. e ↦ transport (Fin n) (t ↦ Id Int (p .fst (inl. t) (inr. star.)) int_zero) j i (inverse (Fin n) i j e) (p .snd .snd .fst)
        | inr. h ↦ imat_clear_keep n A1 (p .fst) j i (p .snd .snd .snd i) (c1 .snd .snd i h)
            (imat_fin_eqb n i j) (refl (imat_fin_eqb n i j)) (p .snd .snd .fst) ]))) ]

{` The elimination: A' related to A with last column (0, …, 0, g). `}
def imat_eliminate (n : Nat) (A : IntMatrix (suc. n)) : ImatCleared n A (imat_fin_all n)
  ≔ imat_clear_list n A (imat_fin_all n)

def imat_eliminate_zero (n : Nat) (A : IntMatrix (suc. n)) (i : Fin n)
  : Id Int (imat_eliminate n A .fst (inl. i) (inr. star.)) int_zero
  ≔ imat_eliminate n A .snd .snd i (imat_fin_all_in n i)
