export "981-integer-determinant"

{` Chapter 9 (subgroups.tex 1186): the generalized minors D_m(R; S) of
   module 981 are linear in every row and vanish when a row equals the last
   row. Proof of the alternation: (1) if the last two rows agree, the double
   expansion Σ_j Σ_k r_j r_k Q(j, k) has Q(k, j) = −Q(j, k) (the sign of a
   pair of selected columns flips, the double minor is symmetric), so the
   sum equals its own negative after swapping the summations; (2) hence
   swapping the last two rows negates D (bilinearity); (3) a row p equal to
   the last row: swap the last two rows and use induction on the number of
   rows. `}

{` Replace row q of R by r. `}
def imat_upd (m n : Nat) (R : Fin m → Fin n → Int) (q : Fin m) (r : Fin n → Int) : Fin m → Fin n → Int
  ≔ match m [
  | zero. ↦ match q [ ]
  | suc. m ↦ match q [
    | inl. q ↦ [ inl. i ↦ imat_upd m n (i' ↦ R (inl. i')) q r i | inr. _ ↦ R (inr. star.) ]
    | inr. _ ↦ [ inl. i ↦ R (inl. i) | inr. _ ↦ r ] ] ]

def imat_upd_at (m n : Nat) (R : Fin m → Fin n → Int) (q : Fin m) (r : Fin n → Int) (j : Fin n)
  : Id Int (imat_upd m n R q r q j) (r j)
  ≔ match m [
  | zero. ↦ match q [ ]
  | suc. m ↦ match q [ inl. q ↦ imat_upd_at m n (i' ↦ R (inl. i')) q r j | inr. _ ↦ refl (r j) ] ]

def imat_upd_self (m n : Nat) (R : Fin m → Fin n → Int) (q : Fin m) (i : Fin m) (j : Fin n)
  : Id Int (imat_upd m n R q (R q) i j) (R i j)
  ≔ match m [
  | zero. ↦ match q [ ]
  | suc. m ↦ match q [
    | inl. q ↦ match i [
      | inl. i ↦ imat_upd_self m n (i' ↦ R (inl. i')) q i j
      | inr. u ↦ match u [ star. ↦ refl (R (inr. star.) j) ] ]
    | inr. v ↦ match v [ star. ↦ match i [
      | inl. i ↦ refl (R (inl. i) j)
      | inr. u ↦ match u [ star. ↦ refl (R (inr. star.) j) ] ] ] ] ]

{` Ring arithmetic. `}
def imat_mul_swap_left (x c q : Int) : Id Int (int_mul x (int_mul c q)) (int_mul c (int_mul x q))
  ≔ calc
      int_mul x (int_mul c q) = int_mul (int_mul x c) q by int_mul_assoc x c q
      = int_mul (int_mul c x) q by refl ((y ↦ int_mul y q) : Int → Int) (int_mul_comm x c)
      = int_mul c (int_mul x q) by inverse Int (int_mul c (int_mul x q)) (int_mul (int_mul c x) q) (int_mul_assoc c x q) ∎

def imat_lin_mul_right (x p q c : Int)
  : Id Int (int_mul x (int_add p (int_mul c q))) (int_add (int_mul x p) (int_mul c (int_mul x q)))
  ≔ concat Int (int_mul x (int_add p (int_mul c q))) (int_add (int_mul x p) (int_mul x (int_mul c q)))
      (int_add (int_mul x p) (int_mul c (int_mul x q)))
      (int_mul_ldistr x p (int_mul c q)) (refl (int_add (int_mul x p)) (imat_mul_swap_left x c q))

def imat_lin_term (s a b c d : Int)
  : Id Int (int_mul (int_mul s (int_add a (int_mul c b))) d)
      (int_add (int_mul (int_mul s a) d) (int_mul c (int_mul (int_mul s b) d)))
  ≔ calc
      int_mul (int_mul s (int_add a (int_mul c b))) d = int_mul (int_add (int_mul s a) (int_mul c (int_mul s b))) d
        by refl ((y ↦ int_mul y d) : Int → Int) (imat_lin_mul_right s a b c)
      = int_add (int_mul (int_mul s a) d) (int_mul (int_mul c (int_mul s b)) d)
        by int_mul_rdistr (int_mul s a) (int_mul c (int_mul s b)) d
      = int_add (int_mul (int_mul s a) d) (int_mul c (int_mul (int_mul s b) d))
        by refl (int_add (int_mul (int_mul s a) d))
             (inverse Int (int_mul c (int_mul (int_mul s b) d)) (int_mul (int_mul c (int_mul s b)) d)
               (int_mul_assoc c (int_mul s b) d)) ∎

def imat_mul_interchange (a b c d : Int)
  : Id Int (int_mul (int_mul a b) (int_mul c d)) (int_mul (int_mul a c) (int_mul b d))
  ≔ calc
      int_mul (int_mul a b) (int_mul c d) = int_mul a (int_mul b (int_mul c d))
        by inverse Int (int_mul a (int_mul b (int_mul c d))) (int_mul (int_mul a b) (int_mul c d)) (int_mul_assoc a b (int_mul c d))
      = int_mul a (int_mul c (int_mul b d)) by refl (int_mul a) (imat_mul_swap_left b c d)
      = int_mul (int_mul a c) (int_mul b d) by int_mul_assoc a c (int_mul b d) ∎

def imat_mul_neg_left (x y : Int) : Id Int (int_mul (int_neg x) y) (int_neg (int_mul x y))
  ≔ calc
      int_mul (int_neg x) y = int_mul y (int_neg x) by int_mul_comm (int_neg x) y
      = int_neg (int_mul y x) by int_mul_neg_right y x
      = int_neg (int_mul x y) by refl int_neg (int_mul_comm y x) ∎

def imat_neg_zero_self (x : Int) (h : Id Int x (int_neg x)) : Id Int x int_zero
  ≔ match x [
  | pos. n ↦ match n [ zero. ↦ refl int_zero | suc. n ↦ match int_encode (pos. (suc. n)) (neg. n) h [ ] ]
  | neg. n ↦ match int_encode (neg. n) (pos. (suc. n)) h [ ] ]

def imat_bif_zero (b : Bool) : Id Int (imat_bif b int_zero) int_zero
  ≔ match b [ true. ↦ refl int_zero | false. ↦ refl int_zero ]

def imat_bif_lin (b : Bool) (x y z c : Int) (h : Id Int x (int_add y (int_mul c z)))
  : Id Int (imat_bif b x) (int_add (imat_bif b y) (int_mul c (imat_bif b z)))
  ≔ match b [ true. ↦ h | false. ↦ refl int_zero ]

{` Linearity in row q. `}
def imat_minor_linear (m n : Nat) (R : Fin m → Fin n → Int) (q : Fin m) (u v : Fin n → Int) (c : Int) (S : Fin n → Bool)
  : Id Int (imat_minor m n (imat_upd m n R q (j ↦ int_add (u j) (int_mul c (v j)))) S)
      (int_add (imat_minor m n (imat_upd m n R q u) S) (int_mul c (imat_minor m n (imat_upd m n R q v) S)))
  ≔ match m [
  | zero. ↦ match q [ ]
  | suc. m ↦ match q [
    | inl. q ↦
      let T : (Fin n → Int) → Fin n → Int ≔ w j ↦ imat_bif (S j)
        (int_mul (int_mul (imat_sgn n S j) (R (inr. star.) j)) (imat_minor m n (imat_upd m n (i' ↦ R (inl. i')) q w) (imat_remove n S j))) in
      concat Int (int_fsum n (T (j ↦ int_add (u j) (int_mul c (v j))))) (int_fsum n (j ↦ int_add (T u j) (int_mul c (T v j))))
        (int_add (int_fsum n (T u)) (int_mul c (int_fsum n (T v))))
        (int_fsum_ext n (T (j ↦ int_add (u j) (int_mul c (v j)))) (j ↦ int_add (T u j) (int_mul c (T v j)))
          (j ↦
            let X ≔ int_mul (imat_sgn n S j) (R (inr. star.) j) in
            imat_bif_lin (S j)
              (int_mul X (imat_minor m n (imat_upd m n (i' ↦ R (inl. i')) q (j' ↦ int_add (u j') (int_mul c (v j')))) (imat_remove n S j)))
              (int_mul X (imat_minor m n (imat_upd m n (i' ↦ R (inl. i')) q u) (imat_remove n S j)))
              (int_mul X (imat_minor m n (imat_upd m n (i' ↦ R (inl. i')) q v) (imat_remove n S j))) c
            (concat Int (int_mul X (imat_minor m n (imat_upd m n (i' ↦ R (inl. i')) q (j' ↦ int_add (u j') (int_mul c (v j')))) (imat_remove n S j)))
               (int_mul X (int_add (imat_minor m n (imat_upd m n (i' ↦ R (inl. i')) q u) (imat_remove n S j))
                 (int_mul c (imat_minor m n (imat_upd m n (i' ↦ R (inl. i')) q v) (imat_remove n S j)))))
               (int_add (int_mul X (imat_minor m n (imat_upd m n (i' ↦ R (inl. i')) q u) (imat_remove n S j)))
                 (int_mul c (int_mul X (imat_minor m n (imat_upd m n (i' ↦ R (inl. i')) q v) (imat_remove n S j)))))
               (refl (int_mul X) (imat_minor_linear m n (i' ↦ R (inl. i')) q u v c (imat_remove n S j)))
               (imat_lin_mul_right X (imat_minor m n (imat_upd m n (i' ↦ R (inl. i')) q u) (imat_remove n S j))
                 (imat_minor m n (imat_upd m n (i' ↦ R (inl. i')) q v) (imat_remove n S j)) c))))
        (concat Int (int_fsum n (j ↦ int_add (T u j) (int_mul c (T v j))))
          (int_add (int_fsum n (T u)) (int_fsum n (j ↦ int_mul c (T v j))))
          (int_add (int_fsum n (T u)) (int_mul c (int_fsum n (T v))))
          (int_fsum_add n (T u) (j ↦ int_mul c (T v j)))
          (refl (int_add (int_fsum n (T u))) (int_fsum_scale n c (T v))))
    | inr. _ ↦
      let T : (Fin n → Int) → Fin n → Int ≔ w j ↦ imat_bif (S j)
        (int_mul (int_mul (imat_sgn n S j) (w j)) (imat_minor m n (i' ↦ R (inl. i')) (imat_remove n S j))) in
      concat Int (int_fsum n (T (j ↦ int_add (u j) (int_mul c (v j))))) (int_fsum n (j ↦ int_add (T u j) (int_mul c (T v j))))
        (int_add (int_fsum n (T u)) (int_mul c (int_fsum n (T v))))
        (int_fsum_ext n (T (j ↦ int_add (u j) (int_mul c (v j)))) (j ↦ int_add (T u j) (int_mul c (T v j)))
          (j ↦
            let D ≔ imat_minor m n (i' ↦ R (inl. i')) (imat_remove n S j) in
            imat_bif_lin (S j) (int_mul (int_mul (imat_sgn n S j) (int_add (u j) (int_mul c (v j)))) D)
              (int_mul (int_mul (imat_sgn n S j) (u j)) D) (int_mul (int_mul (imat_sgn n S j) (v j)) D) c
              (imat_lin_term (imat_sgn n S j) (u j) (v j) c D)))
        (concat Int (int_fsum n (j ↦ int_add (T u j) (int_mul c (T v j))))
          (int_add (int_fsum n (T u)) (int_fsum n (j ↦ int_mul c (T v j))))
          (int_add (int_fsum n (T u)) (int_mul c (int_fsum n (T v))))
          (int_fsum_add n (T u) (j ↦ int_mul c (T v j)))
          (refl (int_add (int_fsum n (T u))) (int_fsum_scale n c (T v)))) ] ]

{` Bool and sign lemmas for the double expansion. `}
def imat_fin_eqb_sym (n : Nat) (i j : Fin n) : Id Bool (imat_fin_eqb n i j) (imat_fin_eqb n j i)
  ≔ match n [
  | zero. ↦ match i [ ]
  | suc. n ↦ match i [
    | inl. a ↦ match j [ inl. b ↦ imat_fin_eqb_sym n a b | inr. _ ↦ refl false. ]
    | inr. _ ↦ match j [ inl. _ ↦ refl false. | inr. _ ↦ refl true. ] ] ]

def imat_bnot_and_comm (x y s : Bool) : Id Bool (imat_bnot_and x (imat_bnot_and y s)) (imat_bnot_and y (imat_bnot_and x s))
  ≔ match x [
  | true. ↦ match y [ true. ↦ refl false. | false. ↦ refl false. ]
  | false. ↦ match y [ true. ↦ refl false. | false. ↦ refl s ] ]

def imat_bsign_mul_same (b : Bool) (x y : Int) : Id Int (int_mul (imat_bsign b x) (imat_bsign b y)) (int_mul x y)
  ≔ match b [
  | false. ↦ refl (int_mul x y)
  | true. ↦ calc
      int_mul (int_neg x) (int_neg y) = int_neg (int_mul (int_neg x) y) by int_mul_neg_right (int_neg x) y
      = int_neg (int_neg (int_mul x y)) by refl int_neg (imat_mul_neg_left x y)
      = int_mul x y by int_neg_neg (int_mul x y) ∎ ]

def imat_bsign_true (b : Bool) (h : Id Bool b true.) (x : Int) : Id Int (imat_bsign b x) (int_neg x)
  ≔ match b [ true. ↦ refl (int_neg x) | false. ↦ match bool_encode false. true. h [ ] ]

{` ε_S(j) ε_{S−j}(k) = −ε_S(k) ε_{S−k}(j) for distinct selected j, k. `}
def imat_sgn_antisym (n : Nat) (S : Fin n → Bool) (j k : Fin n)
  (hj : Id Bool (S j) true.) (hk : Id Bool (S k) true.) (hjk : Id Bool (imat_fin_eqb n j k) false.)
  : Id Int (int_mul (imat_sgn n S k) (imat_sgn n (imat_remove n S k) j))
      (int_neg (int_mul (imat_sgn n S j) (imat_sgn n (imat_remove n S j) k)))
  ≔ match n [
  | zero. ↦ match j [ ]
  | suc. n ↦
    let S' : Fin n → Bool ≔ i ↦ S (inl. i) in
    match j [
    | inl. a ↦ match k [
      | inl. b ↦ calc
          int_mul (imat_bsign (S (inr. star.)) (imat_sgn n S' b)) (imat_bsign (S (inr. star.)) (imat_sgn n (imat_remove n S' b) a))
          = int_mul (imat_sgn n S' b) (imat_sgn n (imat_remove n S' b) a)
            by imat_bsign_mul_same (S (inr. star.)) (imat_sgn n S' b) (imat_sgn n (imat_remove n S' b) a)
          = int_neg (int_mul (imat_sgn n S' a) (imat_sgn n (imat_remove n S' a) b))
            by imat_sgn_antisym n S' a b hj hk hjk
          = int_neg (int_mul (imat_bsign (S (inr. star.)) (imat_sgn n S' a)) (imat_bsign (S (inr. star.)) (imat_sgn n (imat_remove n S' a) b)))
            by refl int_neg (inverse Int
                 (int_mul (imat_bsign (S (inr. star.)) (imat_sgn n S' a)) (imat_bsign (S (inr. star.)) (imat_sgn n (imat_remove n S' a) b)))
                 (int_mul (imat_sgn n S' a) (imat_sgn n (imat_remove n S' a) b))
                 (imat_bsign_mul_same (S (inr. star.)) (imat_sgn n S' a) (imat_sgn n (imat_remove n S' a) b))) ∎
      | inr. u ↦ match u [ star. ↦ calc
          int_mul int_one (imat_sgn n S' a) = imat_sgn n S' a by int_mul_one_left (imat_sgn n S' a)
          = int_neg (int_neg (imat_sgn n S' a)) by inverse Int (int_neg (int_neg (imat_sgn n S' a))) (imat_sgn n S' a) (int_neg_neg (imat_sgn n S' a))
          = int_neg (imat_bsign (S (inr. star.)) (imat_sgn n S' a))
            by refl int_neg (inverse Int (imat_bsign (S (inr. star.)) (imat_sgn n S' a)) (int_neg (imat_sgn n S' a))
                 (imat_bsign_true (S (inr. star.)) hk (imat_sgn n S' a)))
          = int_neg (int_mul (imat_bsign (S (inr. star.)) (imat_sgn n S' a)) int_one)
            by refl int_neg (int_mul_one_right (imat_bsign (S (inr. star.)) (imat_sgn n S' a))) ∎ ] ]
    | inr. u ↦ match u [ star. ↦ match k [
      | inl. b ↦ calc
          int_mul (imat_bsign (S (inr. star.)) (imat_sgn n S' b)) int_one = imat_bsign (S (inr. star.)) (imat_sgn n S' b)
            by int_mul_one_right (imat_bsign (S (inr. star.)) (imat_sgn n S' b))
          = int_neg (imat_sgn n S' b) by imat_bsign_true (S (inr. star.)) hj (imat_sgn n S' b)
          = int_neg (int_mul int_one (imat_sgn n S' b))
            by refl int_neg (inverse Int (int_mul int_one (imat_sgn n S' b)) (imat_sgn n S' b) (int_mul_one_left (imat_sgn n S' b))) ∎
      | inr. v ↦ match v [ star. ↦ match bool_encode true. false. hjk [ ] ] ] ] ] ]

{` The double-expansion coefficient and its antisymmetry. `}
def imat_q_antisym (b1 b2 e1 e2 : Bool) (he : Id Bool e1 e2) (x y : Int)
  (hxy : Id Bool e1 false. → Id Bool b1 true. → Id Bool b2 true. → Id Int y (int_neg x))
  : Id Int (imat_bif b2 (imat_bif (imat_bnot_and e2 b1) y)) (int_neg (imat_bif b1 (imat_bif (imat_bnot_and e1 b2) x)))
  ≔ match e1, e2 [
  | true., false. ↦ match bool_encode true. false. he [ ]
  | false., true. ↦ match bool_encode false. true. he [ ]
  | true., true. ↦ match b1, b2 [
    | true., true. ↦ refl int_zero | true., false. ↦ refl int_zero
    | false., true. ↦ refl int_zero | false., false. ↦ refl int_zero ]
  | false., false. ↦ match b1, b2 [
    | true., true. ↦ hxy (refl false.) (refl true.) (refl true.) | true., false. ↦ refl int_zero
    | false., true. ↦ refl int_zero | false., false. ↦ refl int_zero ] ]

def imat_step1_term (e : Bool) (s rj s' rk d : Int)
  : Id Int (int_mul (int_mul s rj) (imat_bif e (int_mul (int_mul s' rk) d)))
      (int_mul (int_mul rj rk) (imat_bif e (int_mul (int_mul s s') d)))
  ≔ match e [
  | false. ↦ refl int_zero
  | true. ↦ calc
      int_mul (int_mul s rj) (int_mul (int_mul s' rk) d) = int_mul (int_mul (int_mul s rj) (int_mul s' rk)) d
        by int_mul_assoc (int_mul s rj) (int_mul s' rk) d
      = int_mul (int_mul (int_mul s s') (int_mul rj rk)) d
        by refl ((z ↦ int_mul z d) : Int → Int) (imat_mul_interchange s rj s' rk)
      = int_mul (int_mul (int_mul rj rk) (int_mul s s')) d
        by refl ((z ↦ int_mul z d) : Int → Int) (int_mul_comm (int_mul s s') (int_mul rj rk))
      = int_mul (int_mul rj rk) (int_mul (int_mul s s') d)
        by inverse Int (int_mul (int_mul rj rk) (int_mul (int_mul s s') d)) (int_mul (int_mul (int_mul rj rk) (int_mul s s')) d)
             (int_mul_assoc (int_mul rj rk) (int_mul s s') d) ∎ ]

def imat_step1 (n : Nat) (b : Bool) (e : Fin n → Bool) (s rj rj' : Int) (s' r d : Fin n → Int) (hr : Id Int rj' rj)
  : Id Int (imat_bif b (int_mul (int_mul s rj') (int_fsum n (k ↦ imat_bif (e k) (int_mul (int_mul (s' k) (r k)) (d k))))))
      (int_fsum n (k ↦ int_mul (int_mul rj (r k)) (imat_bif b (imat_bif (e k) (int_mul (int_mul s (s' k)) (d k))))))
  ≔ match b [
  | false. ↦ inverse Int (int_fsum n (k ↦ int_mul (int_mul rj (r k)) int_zero)) int_zero
      (int_fsum_zero n (k ↦ int_mul (int_mul rj (r k)) int_zero) (k ↦ refl int_zero))
  | true. ↦ calc
      int_mul (int_mul s rj') (int_fsum n (k ↦ imat_bif (e k) (int_mul (int_mul (s' k) (r k)) (d k))))
      = int_mul (int_mul s rj) (int_fsum n (k ↦ imat_bif (e k) (int_mul (int_mul (s' k) (r k)) (d k))))
        by refl ((z ↦ int_mul (int_mul s z) (int_fsum n (k ↦ imat_bif (e k) (int_mul (int_mul (s' k) (r k)) (d k))))) : Int → Int) hr
      = int_fsum n (k ↦ int_mul (int_mul s rj) (imat_bif (e k) (int_mul (int_mul (s' k) (r k)) (d k))))
        by inverse Int (int_fsum n (k ↦ int_mul (int_mul s rj) (imat_bif (e k) (int_mul (int_mul (s' k) (r k)) (d k)))))
             (int_mul (int_mul s rj) (int_fsum n (k ↦ imat_bif (e k) (int_mul (int_mul (s' k) (r k)) (d k)))))
             (int_fsum_scale n (int_mul s rj) (k ↦ imat_bif (e k) (int_mul (int_mul (s' k) (r k)) (d k))))
      = int_fsum n (k ↦ int_mul (int_mul rj (r k)) (imat_bif (e k) (int_mul (int_mul s (s' k)) (d k))))
        by int_fsum_ext n (k ↦ int_mul (int_mul s rj) (imat_bif (e k) (int_mul (int_mul (s' k) (r k)) (d k))))
             (k ↦ int_mul (int_mul rj (r k)) (imat_bif (e k) (int_mul (int_mul s (s' k)) (d k))))
             (k ↦ imat_step1_term (e k) s rj (s' k) (r k) (d k)) ∎ ]

{` The coefficient Q(j, k) of r_j r_k in the double expansion. `}
def imat_q (m n : Nat) (R2 : Fin m → Fin n → Int) (S : Fin n → Bool) (j k : Fin n) : Int
  ≔ imat_bif (S j) (imat_bif (imat_remove n S j k)
      (int_mul (int_mul (imat_sgn n S j) (imat_sgn n (imat_remove n S j) k)) (imat_minor m n R2 (imat_remove n (imat_remove n S j) k))))

def imat_q_swap (m n : Nat) (R2 : Fin m → Fin n → Int) (S : Fin n → Bool) (j k : Fin n)
  : Id Int (imat_q m n R2 S k j) (int_neg (imat_q m n R2 S j k))
  ≔ imat_q_antisym (S j) (S k) (imat_fin_eqb n k j) (imat_fin_eqb n j k) (imat_fin_eqb_sym n k j)
      (int_mul (int_mul (imat_sgn n S j) (imat_sgn n (imat_remove n S j) k)) (imat_minor m n R2 (imat_remove n (imat_remove n S j) k)))
      (int_mul (int_mul (imat_sgn n S k) (imat_sgn n (imat_remove n S k) j)) (imat_minor m n R2 (imat_remove n (imat_remove n S k) j)))
      (hkj hj hk ↦
        let σ ≔ int_mul (imat_sgn n S j) (imat_sgn n (imat_remove n S j) k) in
        let Djk ≔ imat_minor m n R2 (imat_remove n (imat_remove n S j) k) in
        calc
          int_mul (int_mul (imat_sgn n S k) (imat_sgn n (imat_remove n S k) j)) (imat_minor m n R2 (imat_remove n (imat_remove n S k) j))
          = int_mul (int_neg σ) (imat_minor m n R2 (imat_remove n (imat_remove n S k) j))
            by refl ((z ↦ int_mul z (imat_minor m n R2 (imat_remove n (imat_remove n S k) j))) : Int → Int)
                 (imat_sgn_antisym n S j k hj hk
                   (concat Bool (imat_fin_eqb n j k) (imat_fin_eqb n k j) false. (imat_fin_eqb_sym n j k) hkj))
          = int_mul (int_neg σ) Djk
            by refl (int_mul (int_neg σ))
                 (imat_minor_ext_cols m n R2 (imat_remove n (imat_remove n S k) j) (imat_remove n (imat_remove n S j) k)
                   (i ↦ imat_bnot_and_comm (imat_fin_eqb n i j) (imat_fin_eqb n i k) (S i)))
          = int_neg (int_mul σ Djk) by imat_mul_neg_left σ Djk ∎)

{` D vanishes when the last two rows agree. `}
def imat_minor_last_two (m n : Nat) (R : Fin (suc. (suc. m)) → Fin n → Int)
  (h : (j : Fin n) → Id Int (R (inr. star.) j) (R (inl. (inr. star.)) j)) (S : Fin n → Bool)
  : Id Int (imat_minor (suc. (suc. m)) n R S) int_zero
  ≔ let r : Fin n → Int ≔ j ↦ R (inl. (inr. star.)) j in
    let R2 : Fin m → Fin n → Int ≔ i ↦ R (inl. (inl. i)) in
    let Q ≔ imat_q m n R2 S in
    let X ≔ int_fsum n (j ↦ int_fsum n (k ↦ int_mul (int_mul (r j) (r k)) (Q j k))) in
    let e1 : Id Int (imat_minor (suc. (suc. m)) n R S) X
      ≔ int_fsum_ext n
          (j ↦ imat_bif (S j) (int_mul (int_mul (imat_sgn n S j) (R (inr. star.) j))
            (imat_minor (suc. m) n (i ↦ R (inl. i)) (imat_remove n S j))))
          (j ↦ int_fsum n (k ↦ int_mul (int_mul (r j) (r k)) (Q j k)))
          (j ↦ imat_step1 n (S j) (imat_remove n S j) (imat_sgn n S j) (r j) (R (inr. star.) j)
            (imat_sgn n (imat_remove n S j)) r (k ↦ imat_minor m n R2 (imat_remove n (imat_remove n S j) k)) (h j)) in
    let e2 : Id Int X (int_neg X)
      ≔ calc
          X = int_fsum n (k ↦ int_fsum n (j ↦ int_mul (int_mul (r j) (r k)) (Q j k)))
            by int_fsum_swap n n (j k ↦ int_mul (int_mul (r j) (r k)) (Q j k))
          = int_fsum n (k ↦ int_fsum n (j ↦ int_neg (int_mul (int_mul (r k) (r j)) (Q k j))))
            by int_fsum_ext n (k ↦ int_fsum n (j ↦ int_mul (int_mul (r j) (r k)) (Q j k)))
                 (k ↦ int_fsum n (j ↦ int_neg (int_mul (int_mul (r k) (r j)) (Q k j))))
                 (k ↦ int_fsum_ext n (j ↦ int_mul (int_mul (r j) (r k)) (Q j k)) (j ↦ int_neg (int_mul (int_mul (r k) (r j)) (Q k j)))
                   (j ↦ calc
                     int_mul (int_mul (r j) (r k)) (Q j k) = int_mul (int_mul (r k) (r j)) (Q j k)
                       by refl ((z ↦ int_mul z (Q j k)) : Int → Int) (int_mul_comm (r j) (r k))
                     = int_mul (int_mul (r k) (r j)) (int_neg (Q k j))
                       by refl (int_mul (int_mul (r k) (r j))) (imat_q_swap m n R2 S k j)
                     = int_neg (int_mul (int_mul (r k) (r j)) (Q k j)) by int_mul_neg_right (int_mul (r k) (r j)) (Q k j) ∎))
          = int_fsum n (k ↦ int_neg (int_fsum n (j ↦ int_mul (int_mul (r k) (r j)) (Q k j))))
            by int_fsum_ext n (k ↦ int_fsum n (j ↦ int_neg (int_mul (int_mul (r k) (r j)) (Q k j))))
                 (k ↦ int_neg (int_fsum n (j ↦ int_mul (int_mul (r k) (r j)) (Q k j))))
                 (k ↦ int_fsum_neg n (j ↦ int_mul (int_mul (r k) (r j)) (Q k j)))
          = int_neg X by int_fsum_neg n (k ↦ int_fsum n (j ↦ int_mul (int_mul (r k) (r j)) (Q k j))) ∎ in
    concat Int (imat_minor (suc. (suc. m)) n R S) X int_zero e1 (imat_neg_zero_self X e2)
