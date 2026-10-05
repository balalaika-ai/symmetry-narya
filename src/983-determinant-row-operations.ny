export "982-determinant-alternating"

{` Chapter 9 (subgroups.tex 1186): consequences of module 982 used by the
   elimination. Swapping the last two rows negates D; D vanishes when some
   row equals the last row; the two kinds of row operations
   (last += c · row p, row p += c · last) keep D; D vanishes when a selected
   column is zero; columns outside the selection can be dropped; and the
   block formula det (B 0; r g) = g · det B for a matrix whose last column
   is (0, …, 0, g). `}

def imat_rows2 (m n : Nat) (R0 : Fin m → Fin n → Int) (a b : Fin n → Int) : Fin (suc. (suc. m)) → Fin n → Int
  ≔ [ inl. (inl. i) ↦ R0 i | inl. (inr. _) ↦ a | inr. _ ↦ b ]

def imat_rows2_upd_last (m n : Nat) (R0 : Fin m → Fin n → Int) (x z w : Fin n → Int) (i : Fin (suc. (suc. m))) (j : Fin n)
  : Id Int (imat_upd (suc. (suc. m)) n (imat_rows2 m n R0 x z) (inr. star.) w i j) (imat_rows2 m n R0 x w i j)
  ≔ match i [ inl. (inl. i) ↦ refl (R0 i j) | inl. (inr. _) ↦ refl (x j) | inr. _ ↦ refl (w j) ]

def imat_rows2_upd_mid (m n : Nat) (R0 : Fin m → Fin n → Int) (z y w : Fin n → Int) (i : Fin (suc. (suc. m))) (j : Fin n)
  : Id Int (imat_upd (suc. (suc. m)) n (imat_rows2 m n R0 z y) (inl. (inr. star.)) w i j) (imat_rows2 m n R0 w y i j)
  ≔ match i [ inl. (inl. i) ↦ refl (R0 i j) | inl. (inr. _) ↦ refl (w j) | inr. _ ↦ refl (y j) ]

def imat_rows2_eta (m n : Nat) (R : Fin (suc. (suc. m)) → Fin n → Int) (i : Fin (suc. (suc. m))) (j : Fin n)
  : Id Int (R i j) (imat_rows2 m n (i' ↦ R (inl. (inl. i'))) (R (inl. (inr. star.))) (R (inr. star.)) i j)
  ≔ match i [
  | inl. (inl. i) ↦ refl (R (inl. (inl. i)) j)
  | inl. (inr. u) ↦ match u [ star. ↦ refl (R (inl. (inr. star.)) j) ]
  | inr. u ↦ match u [ star. ↦ refl (R (inr. star.) j) ] ]

def imat_rows2_lin_last (m n : Nat) (R0 : Fin m → Fin n → Int) (x a b : Fin n → Int) (c : Int) (S : Fin n → Bool)
  : Id Int (imat_minor (suc. (suc. m)) n (imat_rows2 m n R0 x (j ↦ int_add (a j) (int_mul c (b j)))) S)
      (int_add (imat_minor (suc. (suc. m)) n (imat_rows2 m n R0 x a) S) (int_mul c (imat_minor (suc. (suc. m)) n (imat_rows2 m n R0 x b) S)))
  ≔ let M : Nat ≔ suc. (suc. m) in
    let R ≔ imat_rows2 m n R0 x a in
    let w : Fin n → Int ≔ j ↦ int_add (a j) (int_mul c (b j)) in
    calc
      imat_minor M n (imat_rows2 m n R0 x w) S = imat_minor M n (imat_upd M n R (inr. star.) w) S
        by imat_minor_ext_rows M n (imat_rows2 m n R0 x w) (imat_upd M n R (inr. star.) w) S
             (i j ↦ inverse Int (imat_upd M n R (inr. star.) w i j) (imat_rows2 m n R0 x w i j) (imat_rows2_upd_last m n R0 x a w i j))
      = int_add (imat_minor M n (imat_upd M n R (inr. star.) a) S) (int_mul c (imat_minor M n (imat_upd M n R (inr. star.) b) S))
        by imat_minor_linear M n R (inr. star.) a b c S
      = int_add (imat_minor M n (imat_rows2 m n R0 x a) S) (int_mul c (imat_minor M n (imat_rows2 m n R0 x b) S))
        by refl int_add
             (imat_minor_ext_rows M n (imat_upd M n R (inr. star.) a) (imat_rows2 m n R0 x a) S (imat_rows2_upd_last m n R0 x a a))
             (refl (int_mul c)
               (imat_minor_ext_rows M n (imat_upd M n R (inr. star.) b) (imat_rows2 m n R0 x b) S (imat_rows2_upd_last m n R0 x a b))) ∎

def imat_rows2_lin_mid (m n : Nat) (R0 : Fin m → Fin n → Int) (y a b : Fin n → Int) (c : Int) (S : Fin n → Bool)
  : Id Int (imat_minor (suc. (suc. m)) n (imat_rows2 m n R0 (j ↦ int_add (a j) (int_mul c (b j))) y) S)
      (int_add (imat_minor (suc. (suc. m)) n (imat_rows2 m n R0 a y) S) (int_mul c (imat_minor (suc. (suc. m)) n (imat_rows2 m n R0 b y) S)))
  ≔ let M : Nat ≔ suc. (suc. m) in
    let R ≔ imat_rows2 m n R0 a y in
    let w : Fin n → Int ≔ j ↦ int_add (a j) (int_mul c (b j)) in
    calc
      imat_minor M n (imat_rows2 m n R0 w y) S = imat_minor M n (imat_upd M n R (inl. (inr. star.)) w) S
        by imat_minor_ext_rows M n (imat_rows2 m n R0 w y) (imat_upd M n R (inl. (inr. star.)) w) S
             (i j ↦ inverse Int (imat_upd M n R (inl. (inr. star.)) w i j) (imat_rows2 m n R0 w y i j) (imat_rows2_upd_mid m n R0 a y w i j))
      = int_add (imat_minor M n (imat_upd M n R (inl. (inr. star.)) a) S) (int_mul c (imat_minor M n (imat_upd M n R (inl. (inr. star.)) b) S))
        by imat_minor_linear M n R (inl. (inr. star.)) a b c S
      = int_add (imat_minor M n (imat_rows2 m n R0 a y) S) (int_mul c (imat_minor M n (imat_rows2 m n R0 b y) S))
        by refl int_add
             (imat_minor_ext_rows M n (imat_upd M n R (inl. (inr. star.)) a) (imat_rows2 m n R0 a y) S (imat_rows2_upd_mid m n R0 a y a))
             (refl (int_mul c)
               (imat_minor_ext_rows M n (imat_upd M n R (inl. (inr. star.)) b) (imat_rows2 m n R0 b y) S (imat_rows2_upd_mid m n R0 a y b))) ∎

{` Swapping the last two rows negates D. `}
def imat_rows2_swap (m n : Nat) (R0 : Fin m → Fin n → Int) (a b : Fin n → Int) (S : Fin n → Bool)
  : Id Int (imat_minor (suc. (suc. m)) n (imat_rows2 m n R0 a b) S) (int_neg (imat_minor (suc. (suc. m)) n (imat_rows2 m n R0 b a) S))
  ≔ let M : Nat ≔ suc. (suc. m) in
    let G : (Fin n → Int) → (Fin n → Int) → Int ≔ x y ↦ imat_minor M n (imat_rows2 m n R0 x y) S in
    let w : Fin n → Int ≔ j ↦ int_add (a j) (int_mul int_one (b j)) in
    let z : (x : Fin n → Int) → Id Int (G x x) int_zero
      ≔ x ↦ imat_minor_last_two m n (imat_rows2 m n R0 x x) (j ↦ refl (x j)) S in
    let sum : Id Int (int_add (G b a) (G a b)) int_zero
      ≔ calc
          int_add (G b a) (G a b) = int_add (G a b) (G b a) by int_add_comm (G b a) (G a b)
          = int_add (int_add int_zero (G a b)) (int_add (G b a) int_zero)
            by refl ((t ↦ int_add t (G b a)) : Int → Int) (inverse Int (int_add int_zero (G a b)) (G a b) (int_add_zero_left (G a b)))
          = int_add (int_add (G a a) (int_mul int_one (G a b))) (int_add (G b a) (int_mul int_one (G b b)))
            by refl int_add
                 (refl int_add (inverse Int (G a a) int_zero (z a)) (inverse Int (int_mul int_one (G a b)) (G a b) (int_mul_one_left (G a b))))
                 (refl (int_add (G b a)) (refl (int_mul int_one) (inverse Int (G b b) int_zero (z b))))
          = int_add (G a w) (int_mul int_one (G b w))
            by inverse Int (int_add (G a w) (int_mul int_one (G b w)))
                 (int_add (int_add (G a a) (int_mul int_one (G a b))) (int_add (G b a) (int_mul int_one (G b b))))
                 (refl int_add (imat_rows2_lin_last m n R0 a a b int_one S)
                   (concat Int (int_mul int_one (G b w)) (G b w) (int_add (G b a) (int_mul int_one (G b b)))
                     (int_mul_one_left (G b w)) (imat_rows2_lin_last m n R0 b a b int_one S)))
          = G w w by inverse Int (G w w) (int_add (G a w) (int_mul int_one (G b w))) (imat_rows2_lin_mid m n R0 w a b int_one S)
          = int_zero by z w ∎ in
    int_neg_unique (G b a) (G a b) sum

{` D vanishes when row p equals the last row. `}
def imat_minor_alt (m n : Nat) (R : Fin (suc. m) → Fin n → Int) (p : Fin m)
  (h : (j : Fin n) → Id Int (R (inl. p) j) (R (inr. star.) j)) (S : Fin n → Bool)
  : Id Int (imat_minor (suc. m) n R S) int_zero
  ≔ match m [
  | zero. ↦ match p [ ]
  | suc. m ↦ match p [
    | inr. u ↦ match u [ star. ↦ imat_minor_last_two m n R (j ↦ inverse Int (R (inl. (inr. star.)) j) (R (inr. star.) j) (h j)) S ]
    | inl. p ↦
      let R0 : Fin m → Fin n → Int ≔ i ↦ R (inl. (inl. i)) in
      let a ≔ R (inl. (inr. star.)) in
      let b ≔ R (inr. star.) in
      let M : Nat ≔ suc. (suc. m) in
      let zba : Id Int (imat_minor M n (imat_rows2 m n R0 b a) S) int_zero
        ≔ int_fsum_zero n
            (j ↦ imat_bif (S j) (int_mul (int_mul (imat_sgn n S j) (a j))
              (imat_minor (suc. m) n (i ↦ imat_rows2 m n R0 b a (inl. i)) (imat_remove n S j))))
            (j ↦ concat Int
              (imat_bif (S j) (int_mul (int_mul (imat_sgn n S j) (a j))
                (imat_minor (suc. m) n (i ↦ imat_rows2 m n R0 b a (inl. i)) (imat_remove n S j))))
              (imat_bif (S j) int_zero) int_zero
              (refl (imat_bif (S j)) (refl (int_mul (int_mul (imat_sgn n S j) (a j)))
                (imat_minor_alt m n (i ↦ imat_rows2 m n R0 b a (inl. i)) p h (imat_remove n S j))))
              (imat_bif_zero (S j))) in
      calc
        imat_minor M n R S = imat_minor M n (imat_rows2 m n R0 a b) S
          by imat_minor_ext_rows M n R (imat_rows2 m n R0 a b) S (imat_rows2_eta m n R)
        = int_neg (imat_minor M n (imat_rows2 m n R0 b a) S) by imat_rows2_swap m n R0 a b S
        = int_zero by refl int_neg zba ∎ ] ]

{` The row operations used by the elimination. `}
def imat_op_last (m n : Nat) (R : Fin (suc. m) → Fin n → Int) (p : Fin m) (c : Int) : Fin (suc. m) → Fin n → Int
  ≔ imat_upd (suc. m) n R (inr. star.) (j ↦ int_add (R (inr. star.) j) (int_mul c (R (inl. p) j)))

def imat_op_row (m n : Nat) (R : Fin (suc. m) → Fin n → Int) (p : Fin m) (c : Int) : Fin (suc. m) → Fin n → Int
  ≔ imat_upd (suc. m) n R (inl. p) (j ↦ int_add (R (inl. p) j) (int_mul c (R (inr. star.) j)))

def imat_minor_op_last (m n : Nat) (R : Fin (suc. m) → Fin n → Int) (p : Fin m) (c : Int) (S : Fin n → Bool)
  : Id Int (imat_minor (suc. m) n (imat_op_last m n R p c) S) (imat_minor (suc. m) n R S)
  ≔ let M : Nat ≔ suc. m in
    calc
      imat_minor M n (imat_op_last m n R p c) S
      = int_add (imat_minor M n (imat_upd M n R (inr. star.) (R (inr. star.))) S)
          (int_mul c (imat_minor M n (imat_upd M n R (inr. star.) (R (inl. p))) S))
        by imat_minor_linear M n R (inr. star.) (R (inr. star.)) (R (inl. p)) c S
      = int_add (imat_minor M n R S) (int_mul c int_zero)
        by refl int_add (imat_minor_ext_rows M n (imat_upd M n R (inr. star.) (R (inr. star.))) R S (imat_upd_self M n R (inr. star.)))
             (refl (int_mul c) (imat_minor_alt m n (imat_upd M n R (inr. star.) (R (inl. p))) p (j ↦ refl (R (inl. p) j)) S)) ∎

def imat_minor_op_row (m n : Nat) (R : Fin (suc. m) → Fin n → Int) (p : Fin m) (c : Int) (S : Fin n → Bool)
  : Id Int (imat_minor (suc. m) n (imat_op_row m n R p c) S) (imat_minor (suc. m) n R S)
  ≔ let M : Nat ≔ suc. m in
    calc
      imat_minor M n (imat_op_row m n R p c) S
      = int_add (imat_minor M n (imat_upd M n R (inl. p) (R (inl. p))) S)
          (int_mul c (imat_minor M n (imat_upd M n R (inl. p) (R (inr. star.))) S))
        by imat_minor_linear M n R (inl. p) (R (inl. p)) (R (inr. star.)) c S
      = int_add (imat_minor M n R S) (int_mul c int_zero)
        by refl int_add (imat_minor_ext_rows M n (imat_upd M n R (inl. p) (R (inl. p))) R S (imat_upd_self M n R (inl. p)))
             (refl (int_mul c) (imat_minor_alt m n (imat_upd M n R (inl. p) (R (inr. star.))) p
               (j ↦ imat_upd_at M n R (inl. p) (R (inr. star.)) j) S)) ∎

{` A zero selected column. `}
def imat_bif_false (b : Bool) (h : Id Bool b false.) (x : Int) : Id Int (imat_bif b x) int_zero
  ≔ match b [ true. ↦ match bool_encode true. false. h [ ] | false. ↦ refl int_zero ]

def imat_bnot_and_false (e : Bool) (he : Id Bool e false.) (s : Bool) : Id Bool (imat_bnot_and e s) s
  ≔ match e [ true. ↦ match bool_encode true. false. he [ ] | false. ↦ refl s ]

def imat_bsign_false (b : Bool) (h : Id Bool b false.) (x : Int) : Id Int (imat_bsign b x) x
  ≔ match b [ true. ↦ match bool_encode true. false. h [ ] | false. ↦ refl x ]

def imat_bnot_and_false_right (e : Bool) : Id Bool (imat_bnot_and e false.) false.
  ≔ match e [ true. ↦ refl false. | false. ↦ refl false. ]

def imat_empty_false (n : Nat) (S : Fin n → Bool) (c : Fin n) (h : Id Bool (S c) true.) : Id Bool (imat_empty n S) false.
  ≔ match n [
  | zero. ↦ match c [ ]
  | suc. n ↦ match c [
    | inl. c ↦ concat Bool (imat_bnot_and (S (inr. star.)) (imat_empty n (i ↦ S (inl. i))))
        (imat_bnot_and (S (inr. star.)) false.) false.
        (refl (imat_bnot_and (S (inr. star.))) (imat_empty_false n (i ↦ S (inl. i)) c h))
        (imat_bnot_and_false_right (S (inr. star.)))
    | inr. u ↦ match u [ star. ↦
        concat Bool (imat_bnot_and (S (inr. star.)) (imat_empty n (i ↦ S (inl. i))))
          (imat_bnot_and true. (imat_empty n (i ↦ S (inl. i)))) false.
          (refl ((e ↦ imat_bnot_and e (imat_empty n (i ↦ S (inl. i)))) : Bool → Bool) h) (refl false.) ] ] ]

def imat_fin_eqb_id (n : Nat) (i j : Fin n) (h : Id Bool (imat_fin_eqb n i j) true.) : Id (Fin n) i j
  ≔ match n [
  | zero. ↦ match i [ ]
  | suc. n ↦ match i [
    | inl. a ↦ match j [
      | inl. b ↦ refl ((x ↦ inl. x) : Fin n → Fin (suc. n)) (imat_fin_eqb_id n a b h)
      | inr. _ ↦ match bool_encode false. true. h [ ] ]
    | inr. u ↦ match j [
      | inl. _ ↦ match bool_encode false. true. h [ ]
      | inr. v ↦ match u [ star. ↦ match v [ star. ↦ refl (inr. star. : Fin (suc. n)) ] ] ] ] ]

def imat_bnot_and_true (e s : Bool) (he : Id Bool e false.) (hs : Id Bool s true.) : Id Bool (imat_bnot_and e s) true.
  ≔ match e [ true. ↦ match bool_encode true. false. he [ ] | false. ↦ hs ]

def imat_mul_zero_left (x : Int) : Id Int (int_mul int_zero x) int_zero
  ≔ concat Int (int_mul int_zero x) (int_mul x int_zero) int_zero (int_mul_comm int_zero x) (refl int_zero)

def imat_zero_col_term (m n : Nat) (R : Fin (suc. m) → Fin n → Int) (S : Fin n → Bool) (c j : Fin n)
  (hS : Id Bool (S c) true.) (hR : (i : Fin (suc. m)) → Id Int (R i c) int_zero)
  (ih : Id Bool (imat_remove n S j c) true. → Id Int (imat_minor m n (i ↦ R (inl. i)) (imat_remove n S j)) int_zero)
  (e : Bool) (he : Id Bool (imat_fin_eqb n c j) e)
  : Id Int (imat_bif (S j) (int_mul (int_mul (imat_sgn n S j) (R (inr. star.) j)) (imat_minor m n (i ↦ R (inl. i)) (imat_remove n S j))))
      int_zero
  ≔ let D ≔ imat_minor m n (i ↦ R (inl. i)) (imat_remove n S j) in
    match e [
    | true. ↦
      let rj : Id Int (R (inr. star.) j) int_zero
        ≔ concat Int (R (inr. star.) j) (R (inr. star.) c) int_zero
            (inverse Int (R (inr. star.) c) (R (inr. star.) j) (refl (R (inr. star.)) (imat_fin_eqb_id n c j he)))
            (hR (inr. star.)) in
      concat Int (imat_bif (S j) (int_mul (int_mul (imat_sgn n S j) (R (inr. star.) j)) D)) (imat_bif (S j) int_zero) int_zero
        (refl (imat_bif (S j)) (concat Int (int_mul (int_mul (imat_sgn n S j) (R (inr. star.) j)) D) (int_mul int_zero D) int_zero
          (refl ((t ↦ int_mul (int_mul (imat_sgn n S j) t) D) : Int → Int) rj) (imat_mul_zero_left D)))
        (imat_bif_zero (S j))
    | false. ↦
      concat Int (imat_bif (S j) (int_mul (int_mul (imat_sgn n S j) (R (inr. star.) j)) D)) (imat_bif (S j) int_zero) int_zero
        (refl (imat_bif (S j)) (refl (int_mul (int_mul (imat_sgn n S j) (R (inr. star.) j)))
          (ih (imat_bnot_and_true (imat_fin_eqb n c j) (S c) he hS))))
        (imat_bif_zero (S j)) ]

def imat_minor_zero_col (m n : Nat) (R : Fin m → Fin n → Int) (S : Fin n → Bool) (c : Fin n)
  (hS : Id Bool (S c) true.) (hR : (i : Fin m) → Id Int (R i c) int_zero)
  : Id Int (imat_minor m n R S) int_zero
  ≔ match m [
  | zero. ↦ imat_bif_false (imat_empty n S) (imat_empty_false n S c hS) int_one
  | suc. m ↦ int_fsum_zero n
      (j ↦ imat_bif (S j) (int_mul (int_mul (imat_sgn n S j) (R (inr. star.) j)) (imat_minor m n (i ↦ R (inl. i)) (imat_remove n S j))))
      (j ↦ imat_zero_col_term m n R S c j hS hR
        (h ↦ imat_minor_zero_col m n (i ↦ R (inl. i)) (imat_remove n S j) c h (i ↦ hR (inl. i)))
        (imat_fin_eqb n c j) (refl (imat_fin_eqb n c j))) ]

{` Columns outside the selection can be dropped (here: the last one). `}
def imat_minor_restrict (m n : Nat) (R : Fin m → Fin (suc. n) → Int) (S : Fin (suc. n) → Bool)
  (hS : Id Bool (S (inr. star.)) false.)
  : Id Int (imat_minor m (suc. n) R S) (imat_minor m n (i j ↦ R i (inl. j)) (j ↦ S (inl. j)))
  ≔ match m [
  | zero. ↦ refl ((b ↦ imat_bif b int_one) : Bool → Int)
      (imat_bnot_and_false (S (inr. star.)) hS (imat_empty n (j ↦ S (inl. j))))
  | suc. m ↦
    let S' : Fin n → Bool ≔ j ↦ S (inl. j) in
    let R' : Fin (suc. m) → Fin n → Int ≔ i j ↦ R i (inl. j) in
    let T : Fin n → Int ≔ j ↦ imat_bif (S (inl. j)) (int_mul (int_mul (imat_sgn (suc. n) S (inl. j)) (R (inr. star.) (inl. j)))
      (imat_minor m (suc. n) (i ↦ R (inl. i)) (imat_remove (suc. n) S (inl. j)))) in
    calc
      imat_minor (suc. m) (suc. n) R S
      = int_add (int_fsum n T) int_zero
        by refl (int_add (int_fsum n T))
             (imat_bif_false (S (inr. star.)) hS (int_mul (int_mul int_one (R (inr. star.) (inr. star.)))
               (imat_minor m (suc. n) (i ↦ R (inl. i)) (imat_remove (suc. n) S (inr. star.)))))
      = imat_minor (suc. m) n R' S'
        by int_fsum_ext n T
             (j ↦ imat_bif (S' j) (int_mul (int_mul (imat_sgn n S' j) (R' (inr. star.) j))
               (imat_minor m n (i ↦ R' (inl. i)) (imat_remove n S' j))))
             (j ↦ refl (imat_bif (S (inl. j)))
               (refl int_mul
                 (refl ((t ↦ int_mul t (R (inr. star.) (inl. j))) : Int → Int)
                   (imat_bsign_false (S (inr. star.)) hS (imat_sgn n S' j)))
                 (imat_minor_restrict m n (i ↦ R (inl. i)) (imat_remove (suc. n) S (inl. j)) hS))) ∎ ]

{` Block formula: if the last column of A is (0, …, 0, g), det A = g · det B
   with B the upper left n × n block. `}
def int_det_block (n : Nat) (A : IntMatrix (suc. n)) (h : (i : Fin n) → Id Int (A (inl. i) (inr. star.)) int_zero)
  : Id Int (int_det (suc. n) A) (int_mul (A (inr. star.) (inr. star.)) (int_det n (i j ↦ A (inl. i) (inl. j))))
  ≔ let full : Fin (suc. n) → Bool ≔ _ ↦ true. in
    let T : Fin n → Int ≔ j ↦ int_mul (int_mul (imat_sgn (suc. n) full (inl. j)) (A (inr. star.) (inl. j)))
      (imat_minor n (suc. n) (i ↦ A (inl. i)) (imat_remove (suc. n) full (inl. j))) in
    let g ≔ A (inr. star.) (inr. star.) in
    let B : IntMatrix n ≔ i j ↦ A (inl. i) (inl. j) in
    calc
      int_det (suc. n) A
      = int_add int_zero (int_mul (int_mul int_one g) (imat_minor n (suc. n) (i ↦ A (inl. i)) (imat_remove (suc. n) full (inr. star.))))
        by refl ((t ↦ int_add t (int_mul (int_mul int_one g) (imat_minor n (suc. n) (i ↦ A (inl. i)) (imat_remove (suc. n) full (inr. star.)))))
               : Int → Int)
             (int_fsum_zero n T
               (j ↦ refl (int_mul (int_mul (imat_sgn (suc. n) full (inl. j)) (A (inr. star.) (inl. j))))
                 (imat_minor_zero_col n (suc. n) (i ↦ A (inl. i)) (imat_remove (suc. n) full (inl. j)) (inr. star.) (refl true.) h)))
      = int_mul (int_mul int_one g) (imat_minor n (suc. n) (i ↦ A (inl. i)) (imat_remove (suc. n) full (inr. star.)))
        by int_add_zero_left (int_mul (int_mul int_one g) (imat_minor n (suc. n) (i ↦ A (inl. i)) (imat_remove (suc. n) full (inr. star.))))
      = int_mul g (int_det n B)
        by refl int_mul (int_mul_one_left g)
             (imat_minor_restrict n n (i ↦ A (inl. i)) (imat_remove (suc. n) full (inr. star.)) (refl false.)) ∎
