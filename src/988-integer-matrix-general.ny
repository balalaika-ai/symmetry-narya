export "987-integer-vector-cokernels"
export "985-elimination-consequences"

{` Chapter 9 (subgroups.tex 1186-1191), the example on integer matrices,
   general n × n case. An integer matrix A (A i j = entry in row i, column
   j) is considered as the homomorphism int_matrix_hom C n A : Z^n → Z^n
   (Z^n = int_power_group C n, the n-fold product of the circle group,
   i.e. the delooping of the torus (S^1)^n) acting on symmetries as A on
   winding vectors (int_matrix_hom_windings). Proved:
   - "nonzero determinant corresponds to monomorphism":
     int_matrix_mono_iff (both directions; det A = 0 gives an explicit
     nonzero kernel vector);
   - det A ≠ 0 ⇒ the cokernel at the shape is a finite set with |det A|
     elements (int_matrix_cokernel_card, a mere equivalence with
     Fin |det A|, the book's notion of cardinality);
   - the covering picture: B(hom A) is a covering (a set bundle) all of
     whose fibers have |det A| elements (int_matrix_covering,
     int_matrix_fiber_card).
   Proof: Euclid on the last column (module 984) and the block
   decomposition (module 985) factor A · x = U ∘ (B ⊕ 1) ∘ L ∘ diag(1, …, 1, g)
   with U, L unimodular; recursively this gives a list of unimodular and
   diagonal factors whose diagonal entries multiply to ±det A, and the
   cokernel cardinality is multiplicative along monomorphisms (module 987).
   The determinant is the Laplace expansion of module 981. `}

{` Lists of factors: concatenation and the lift F ↦ F ⊕ 1. `}
def imat_flist_app (n : Nat) (l1 l2 : List (IntMatFactor n)) : List (IntMatFactor n)
  ≔ match l1 [ nil. ↦ l2 | cons. f l ↦ cons. f (imat_flist_app n l l2) ]

def imat_flist_app_eval (n : Nat) (l1 l2 : List (IntMatFactor n)) (x : Fin n → Int) (i : Fin n)
  : Id Int (int_mat_factors_eval n (imat_flist_app n l1 l2) x i) (int_mat_factors_eval n l1 (int_mat_factors_eval n l2 x) i)
  ≔ match l1 [
  | nil. ↦ refl (int_mat_factors_eval n l2 x i)
  | cons. f l ↦ refl ((v ↦ int_mat_factor_map n f v i) : (Fin n → Int) → Int)
      (funext (Fin n) (_ ↦ Int) (int_mat_factors_eval n (imat_flist_app n l l2) x) (int_mat_factors_eval n l (int_mat_factors_eval n l2 x))
        (imat_flist_app_eval n l l2 x)) ]

def imat_flist_app_card (n : Nat) (l1 l2 : List (IntMatFactor n))
  : Id Nat (int_mat_factors_card n (imat_flist_app n l1 l2)) (mul (int_mat_factors_card n l1) (int_mat_factors_card n l2))
  ≔ match l1 [
  | nil. ↦ inverse Nat (mul (suc. zero.) (int_mat_factors_card n l2)) (int_mat_factors_card n l2) (mul_one_left (int_mat_factors_card n l2))
  | cons. f l ↦ concat Nat (mul (int_mat_factor_card n f) (int_mat_factors_card n (imat_flist_app n l l2)))
      (mul (int_mat_factor_card n f) (mul (int_mat_factors_card n l) (int_mat_factors_card n l2)))
      (mul (mul (int_mat_factor_card n f) (int_mat_factors_card n l)) (int_mat_factors_card n l2))
      (refl (mul (int_mat_factor_card n f)) (imat_flist_app_card n l l2))
      (inverse Nat (mul (mul (int_mat_factor_card n f) (int_mat_factors_card n l)) (int_mat_factors_card n l2))
        (mul (int_mat_factor_card n f) (mul (int_mat_factors_card n l) (int_mat_factors_card n l2)))
        (mul_assoc (int_mat_factor_card n f) (int_mat_factors_card n l) (int_mat_factors_card n l2))) ]

def imat_one_nonzero : IntNonzero int_one ≔ h ↦ int_encode int_one int_zero h

def imat_extend_one (n : Nat) (d : Fin n → Int) : Fin (suc. n) → Int ≔ [ inl. k ↦ d k | inr. _ ↦ int_one ]

def imat_extend_one_nonzero (n : Nat) (d : Fin n → Int) (hd : (i : Fin n) → IntNonzero (d i)) (i : Fin (suc. n))
  : IntNonzero (imat_extend_one n d i)
  ≔ match i [ inl. k ↦ hd k | inr. _ ↦ imat_one_nonzero ]

def imat_factor_lift (n : Nat) (f : IntMatFactor n) : IntMatFactor (suc. n)
  ≔ match f [
  | inl. u ↦ inl. (imat_block1 n (u .fst), imat_block1_unimod n (u .fst) (u .snd))
  | inr. d ↦ inr. (imat_extend_one n (d .fst), imat_extend_one_nonzero n (d .fst) (d .snd)) ]

def imat_flist_lift (n : Nat) (l : List (IntMatFactor n)) : List (IntMatFactor (suc. n))
  ≔ match l [ nil. ↦ nil. | cons. f l ↦ cons. (imat_factor_lift n f) (imat_flist_lift n l) ]

def imat_factor_lift_map (n : Nat) (f : IntMatFactor n) (z : Fin (suc. n) → Int) (i : Fin (suc. n))
  : Id Int (int_mat_factor_map (suc. n) (imat_factor_lift n f) z i) (imat_block1 n (int_mat_factor_map n f) z i)
  ≔ match f [
  | inl. u ↦ refl (imat_block1 n (u .fst) z i)
  | inr. d ↦ match i [
    | inl. k ↦ refl (int_mul (z (inl. k)) (d .fst k))
    | inr. v ↦ match v [ star. ↦ refl (z (inr. star.)) ] ] ]

def imat_block1_id (n : Nat) (z : Fin (suc. n) → Int) (i : Fin (suc. n)) : Id Int (imat_block1 n (x ↦ x) z i) (z i)
  ≔ match i [ inl. k ↦ refl (z (inl. k)) | inr. v ↦ match v [ star. ↦ refl (z (inr. star.)) ] ]

def imat_block1_ext (n : Nat) (F G : (Fin n → Int) → Fin n → Int) (h : (x : Fin n → Int) (k : Fin n) → Id Int (F x k) (G x k))
  (z : Fin (suc. n) → Int) (i : Fin (suc. n)) : Id Int (imat_block1 n F z i) (imat_block1 n G z i)
  ≔ match i [ inl. q ↦ h (j ↦ z (inl. j)) q | inr. v ↦ match v [ star. ↦ refl (z (inr. star.)) ] ]

def imat_block1_compose (n : Nat) (F G : (Fin n → Int) → Fin n → Int) (z : Fin (suc. n) → Int) (i : Fin (suc. n))
  : Id Int (imat_block1 n F (imat_block1 n G z) i) (imat_block1 n (x ↦ F (G x)) z i)
  ≔ match i [ inl. q ↦ refl (F (G (j ↦ z (inl. j))) q) | inr. v ↦ match v [ star. ↦ refl (z (inr. star.)) ] ]

def imat_flist_lift_eval (n : Nat) (l : List (IntMatFactor n)) (z : Fin (suc. n) → Int) (i : Fin (suc. n))
  : Id Int (int_mat_factors_eval (suc. n) (imat_flist_lift n l) z i) (imat_block1 n (int_mat_factors_eval n l) z i)
  ≔ match l [
  | nil. ↦ inverse Int (imat_block1 n (x ↦ x) z i) (z i) (imat_block1_id n z i)
  | cons. f l ↦ concat Int
      (int_mat_factor_map (suc. n) (imat_factor_lift n f) (int_mat_factors_eval (suc. n) (imat_flist_lift n l) z) i)
      (imat_block1 n (int_mat_factor_map n f) (imat_block1 n (int_mat_factors_eval n l) z) i)
      (imat_block1 n (int_mat_factors_eval n (cons. f l)) z i)
      (concat Int
      (int_mat_factor_map (suc. n) (imat_factor_lift n f) (int_mat_factors_eval (suc. n) (imat_flist_lift n l) z) i)
      (int_mat_factor_map (suc. n) (imat_factor_lift n f) (imat_block1 n (int_mat_factors_eval n l) z) i)
      (imat_block1 n (int_mat_factor_map n f) (imat_block1 n (int_mat_factors_eval n l) z) i)
      (refl ((v ↦ int_mat_factor_map (suc. n) (imat_factor_lift n f) v i) : (Fin (suc. n) → Int) → Int)
        (funext (Fin (suc. n)) (_ ↦ Int) (int_mat_factors_eval (suc. n) (imat_flist_lift n l) z)
          (imat_block1 n (int_mat_factors_eval n l) z) (imat_flist_lift_eval n l z)))
      (imat_factor_lift_map n f (imat_block1 n (int_mat_factors_eval n l) z) i))
      (imat_block1_compose n (int_mat_factor_map n f) (int_mat_factors_eval n l) z i) ]

def imat_factor_lift_card (n : Nat) (f : IntMatFactor n)
  : Id Nat (int_mat_factor_card (suc. n) (imat_factor_lift n f)) (int_mat_factor_card n f)
  ≔ match f [
  | inl. _ ↦ refl (suc. zero.)
  | inr. d ↦ mul_one_right (fin_nat_prod n (i ↦ int_abs_nat (d .fst i))) ]

def imat_flist_lift_card (n : Nat) (l : List (IntMatFactor n))
  : Id Nat (int_mat_factors_card (suc. n) (imat_flist_lift n l)) (int_mat_factors_card n l)
  ≔ match l [
  | nil. ↦ refl (suc. zero.)
  | cons. f l ↦ refl mul (imat_factor_lift_card n f) (imat_flist_lift_card n l) ]

{` |x · y| = |x| · |y|. `}
def imat_abs_neg (z : Int) : Id Nat (int_abs_nat (int_neg z)) (int_abs_nat z)
  ≔ match z [ pos. a ↦ match a [ zero. ↦ refl zero. | suc. a ↦ refl (suc. a) ] | neg. a ↦ refl (suc. a) ]

def imat_abs_mul_pos (a : Nat) (y : Int) : Id Nat (int_abs_nat (int_mul (pos. a) y)) (mul a (int_abs_nat y))
  ≔ match y [
  | pos. b ↦ refl int_abs_nat (inverse Int (pos. (mul a b)) (int_mul (pos. a) (pos. b)) (int_mul_naturals a b))
  | neg. b ↦ calc
      int_abs_nat (int_mul (pos. a) (neg. b)) = int_abs_nat (int_neg (int_mul (pos. a) (pos. (suc. b))))
        by refl int_abs_nat (int_mul_neg_right (pos. a) (pos. (suc. b)))
      = int_abs_nat (int_mul (pos. a) (pos. (suc. b))) by imat_abs_neg (int_mul (pos. a) (pos. (suc. b)))
      = mul a (suc. b) by refl int_abs_nat (inverse Int (pos. (mul a (suc. b))) (int_mul (pos. a) (pos. (suc. b))) (int_mul_naturals a (suc. b))) ∎ ]

def imat_abs_mul (x y : Int) : Id Nat (int_abs_nat (int_mul x y)) (mul (int_abs_nat x) (int_abs_nat y))
  ≔ match x [
  | pos. a ↦ imat_abs_mul_pos a y
  | neg. a ↦ calc
      int_abs_nat (int_mul (neg. a) y) = int_abs_nat (int_neg (int_mul (pos. (suc. a)) y))
        by refl int_abs_nat (imat_mul_neg_left (pos. (suc. a)) y)
      = int_abs_nat (int_mul (pos. (suc. a)) y) by imat_abs_neg (int_mul (pos. (suc. a)) y)
      = mul (suc. a) (int_abs_nat y) by imat_abs_mul_pos (suc. a) y ∎ ]

def imat_fin_prod_ones (n : Nat) : Id Nat (fin_nat_prod n (_ ↦ suc. zero.)) (suc. zero.)
  ≔ match n [ zero. ↦ refl (suc. zero.) | suc. n ↦ refl ((t ↦ mul t (suc. zero.)) : Nat → Nat) (imat_fin_prod_ones n) ]

{` The factorization: det A ≠ 0 ⇒ A · x is the composite of a list of
   unimodular and diagonal factors, with |det A| = product of |diagonal entries|. `}
def IntMatrixFactorization (n : Nat) (A : IntMatrix n) : Type
  ≔ Σ (List (IntMatFactor n)) (l ↦ Product
      ((x : Fin n → Int) (i : Fin n) → Id Int (int_mat_vec n A x i) (int_mat_factors_eval n l x i))
      (Id Nat (int_abs_nat (int_det n A)) (int_mat_factors_card n l)))

def int_matrix_factorization (n : Nat) (A : IntMatrix n) (h : IntNonzero (int_det n A)) : IntMatrixFactorization n A
  ≔ match n [
  | zero. ↦ (nil., ((x i ↦ match i [ ]), refl (suc. zero.)))
  | suc. n ↦
    let E ≔ imat_eliminate n A in
    let A' ≔ E .fst in
    let rel ≔ E .snd .fst in
    let U ≔ rel .snd .fst in
    let z : (i : Fin n) → Id Int (A' (inl. i) (inr. star.)) int_zero ≔ i ↦ imat_eliminate_zero n A i in
    let g ≔ A' (inr. star.) (inr. star.) in
    let B : IntMatrix n ≔ i j ↦ A' (inl. i) (inl. j) in
    let r : Fin n → Int ≔ j ↦ A' (inr. star.) (inl. j) in
    let dA : Id Int (int_det (suc. n) A) (int_mul g (int_det n B))
      ≔ concat Int (int_det (suc. n) A) (int_det (suc. n) A') (int_mul g (int_det n B))
          (inverse Int (int_det (suc. n) A') (int_det (suc. n) A) (rel .fst)) (int_det_block n A' z) in
    let hg : IntNonzero g
      ≔ g0 ↦ h (concat Int (int_det (suc. n) A) (int_mul g (int_det n B)) int_zero dA
            (concat Int (int_mul g (int_det n B)) (int_mul int_zero (int_det n B)) int_zero
              (refl ((t ↦ int_mul t (int_det n B)) : Int → Int) g0) (imat_mul_zero_left (int_det n B)))) in
    let hB : IntNonzero (int_det n B)
      ≔ b0 ↦ h (concat Int (int_det (suc. n) A) (int_mul g (int_det n B)) int_zero dA (refl (int_mul g) b0)) in
    let fB ≔ int_matrix_factorization n B hB in
    let D : IntMatFactor (suc. n)
      ≔ inr. (imat_corner_diag n g, [ inl. _ ↦ imat_one_nonzero | inr. _ ↦ hg ]) in
    let L : IntMatFactor (suc. n) ≔ inl. (imat_lower n r, imat_lower_unimod n r) in
    let tail : List (IntMatFactor (suc. n)) ≔ cons. L (cons. D nil.) in
    let mid : List (IntMatFactor (suc. n)) ≔ imat_flist_app (suc. n) (imat_flist_lift n (fB .fst)) tail in
    let l : List (IntMatFactor (suc. n)) ≔ cons. (inl. (U, rel .snd .snd .fst)) mid in
    (l,
     ((x i ↦
        let w ≔ imat_lower n r (int_diag_map (suc. n) (imat_corner_diag n g) x) in
        calc
          int_mat_vec (suc. n) A x i = U (int_mat_vec (suc. n) A' x) i by rel .snd .snd .snd x i
          = U (int_mat_factors_eval (suc. n) mid x) i
            by refl ((v ↦ U v i) : (Fin (suc. n) → Int) → Int)
                 (funext (Fin (suc. n)) (_ ↦ Int) (int_mat_vec (suc. n) A' x) (int_mat_factors_eval (suc. n) mid x)
                   (k ↦ calc
                     int_mat_vec (suc. n) A' x k = imat_block1 n (int_mat_vec n B) w k by imat_block_decomposition n A' z x k
                     = imat_block1 n (int_mat_factors_eval n (fB .fst)) w k
                       by imat_block1_ext n (int_mat_vec n B) (int_mat_factors_eval n (fB .fst)) (fB .snd .fst) w k
                     = int_mat_factors_eval (suc. n) (imat_flist_lift n (fB .fst)) w k
                       by inverse Int (int_mat_factors_eval (suc. n) (imat_flist_lift n (fB .fst)) w k)
                            (imat_block1 n (int_mat_factors_eval n (fB .fst)) w k) (imat_flist_lift_eval n (fB .fst) w k)
                     = int_mat_factors_eval (suc. n) mid x k
                       by inverse Int (int_mat_factors_eval (suc. n) mid x k) (int_mat_factors_eval (suc. n) (imat_flist_lift n (fB .fst)) w k)
                            (imat_flist_app_eval (suc. n) (imat_flist_lift n (fB .fst)) tail x k) ∎)) ∎),
      (let cB ≔ int_mat_factors_card n (fB .fst) in
       let cg ≔ int_abs_nat g in
       calc
         int_abs_nat (int_det (suc. n) A) = int_abs_nat (int_mul g (int_det n B)) by refl int_abs_nat dA
         = mul cg (int_abs_nat (int_det n B)) by imat_abs_mul g (int_det n B)
         = mul cg cB by refl (mul cg) (fB .snd .snd)
         = mul cB cg by mul_comm cg cB
         = mul cB (mul (suc. zero.) (mul (mul (fin_nat_prod n (_ ↦ suc. zero.)) cg) (suc. zero.)))
           by refl (mul cB) (calc
                cg = mul (suc. zero.) cg by inverse Nat (mul (suc. zero.) cg) cg (mul_one_left cg)
                = mul (fin_nat_prod n (_ ↦ suc. zero.)) cg
                  by refl ((t ↦ mul t cg) : Nat → Nat) (inverse Nat (fin_nat_prod n (_ ↦ suc. zero.)) (suc. zero.) (imat_fin_prod_ones n))
                = mul (mul (fin_nat_prod n (_ ↦ suc. zero.)) cg) (suc. zero.)
                  by inverse Nat (mul (mul (fin_nat_prod n (_ ↦ suc. zero.)) cg) (suc. zero.)) (mul (fin_nat_prod n (_ ↦ suc. zero.)) cg)
                       (mul_one_right (mul (fin_nat_prod n (_ ↦ suc. zero.)) cg))
                = mul (suc. zero.) (mul (mul (fin_nat_prod n (_ ↦ suc. zero.)) cg) (suc. zero.))
                  by inverse Nat (mul (suc. zero.) (mul (mul (fin_nat_prod n (_ ↦ suc. zero.)) cg) (suc. zero.)))
                       (mul (mul (fin_nat_prod n (_ ↦ suc. zero.)) cg) (suc. zero.))
                       (mul_one_left (mul (mul (fin_nat_prod n (_ ↦ suc. zero.)) cg) (suc. zero.))) ∎)
         = mul (int_mat_factors_card (suc. n) (imat_flist_lift n (fB .fst))) (int_mat_factors_card (suc. n) tail)
           by refl ((t ↦ mul t (int_mat_factors_card (suc. n) tail)) : Nat → Nat)
                (inverse Nat (int_mat_factors_card (suc. n) (imat_flist_lift n (fB .fst))) cB (imat_flist_lift_card n (fB .fst)))
         = int_mat_factors_card (suc. n) mid
           by inverse Nat (int_mat_factors_card (suc. n) mid)
                (mul (int_mat_factors_card (suc. n) (imat_flist_lift n (fB .fst))) (int_mat_factors_card (suc. n) tail))
                (imat_flist_app_card (suc. n) (imat_flist_lift n (fB .fst)) tail)
         = int_mat_factors_card (suc. n) l by inverse Nat (mul (suc. zero.) (int_mat_factors_card (suc. n) mid))
              (int_mat_factors_card (suc. n) mid) (mul_one_left (int_mat_factors_card (suc. n) mid)) ∎))) ]

{` An integer matrix as a homomorphism Z^n → Z^n. `}
def int_matrix_hom (C : CircleSignature) (n : Nat) (A : IntMatrix n) : GroupHom (int_power_group C n) (int_power_group C n)
  ≔ int_vec_hom C n (int_mat_vec n A) (int_mat_vec_additive n A)

def int_matrix_hom_windings (C : CircleSignature) (n : Nat) (A : IntMatrix n) (p : USym (int_power_group C n)) (i : Fin n)
  : Id Int (int_power_winding C n (usym_hom (int_power_group C n) (int_power_group C n) (int_matrix_hom C n A) p) i)
      (int_mat_vec n A (int_power_winding C n p) i)
  ≔ int_vec_hom_windings C n (int_mat_vec n A) (int_mat_vec_additive n A) p i

def int_matrix_hom_factor_path (C : CircleSignature) (n : Nat) (A : IntMatrix n) (f : IntMatrixFactorization n A)
  : Id (GroupHom (int_power_group C n) (int_power_group C n))
      (int_vec_hom C n (int_mat_factors_eval n (f .fst)) (int_mat_factors_additive n (f .fst))) (int_matrix_hom C n A)
  ≔ int_vec_hom_ext C n (int_mat_factors_eval n (f .fst)) (int_mat_vec n A) (int_mat_factors_additive n (f .fst))
      (int_mat_vec_additive n A) (x i ↦ inverse Int (int_mat_vec n A x i) (int_mat_factors_eval n (f .fst) x i) (f .snd .fst x i))

def int_matrix_mono_of_det (C : CircleSignature) (n : Nat) (A : IntMatrix n) (h : IntNonzero (int_det n A))
  : IsGroupMono (int_power_group C n) (int_power_group C n) (int_matrix_hom C n A)
  ≔ let f ≔ int_matrix_factorization n A h in
    let Zn ≔ int_power_group C n in
    transport (GroupHom Zn Zn) (IsGroupMono Zn Zn)
      (int_vec_hom C n (int_mat_factors_eval n (f .fst)) (int_mat_factors_additive n (f .fst))) (int_matrix_hom C n A)
      (int_matrix_hom_factor_path C n A f) (int_vec_factors_hom_good C n (f .fst) .fst)

def int_matrix_det_of_mono (C : CircleSignature) (n : Nat) (A : IntMatrix n)
  (m : IsGroupMono (int_power_group C n) (int_power_group C n) (int_matrix_hom C n A)) : IntNonzero (int_det n A)
  ≔ h0 ↦ let k ≔ int_det_zero_kernel n A h0 in
    int_vec_hom_not_mono C n (int_mat_vec n A) (int_mat_vec_additive n A) (k .fst) (k .snd .fst) (k .snd .snd) m

{` "Nonzero determinant corresponds to monomorphism". `}
def int_matrix_mono_iff (C : CircleSignature) (n : Nat) (A : IntMatrix n)
  : Product (IsGroupMono (int_power_group C n) (int_power_group C n) (int_matrix_hom C n A) → IntNonzero (int_det n A))
      (IntNonzero (int_det n A) → IsGroupMono (int_power_group C n) (int_power_group C n) (int_matrix_hom C n A))
  ≔ (int_matrix_det_of_mono C n A, int_matrix_mono_of_det C n A)

{` The cokernel is a finite set with |det A| elements. `}
def int_matrix_cokernel_card (C : CircleSignature) (n : Nat) (A : IntMatrix n) (h : IntNonzero (int_det n A))
  : Mere (Equiv (gset_underlying (int_power_group C n) (cokernel (int_power_group C n) (int_power_group C n) (int_matrix_hom C n A)))
      (Fin (int_abs_nat (int_det n A))))
  ≔ let f ≔ int_matrix_factorization n A h in
    let Zn ≔ int_power_group C n in
    let c ≔ int_mat_factors_card n (f .fst) in
    transport Nat (k ↦ Mere (Equiv (gset_underlying Zn (cokernel Zn Zn (int_matrix_hom C n A))) (Fin k)))
      c (int_abs_nat (int_det n A)) (inverse Nat (int_abs_nat (int_det n A)) c (f .snd .snd))
      (transport (GroupHom Zn Zn) (hh ↦ Mere (Equiv (gset_underlying Zn (cokernel Zn Zn hh)) (Fin c)))
        (int_vec_hom C n (int_mat_factors_eval n (f .fst)) (int_mat_factors_additive n (f .fst))) (int_matrix_hom C n A)
        (int_matrix_hom_factor_path C n A f) (int_vec_factors_hom_good C n (f .fst) .snd))

{` The covering picture: B(hom A) is a covering of the torus BZ^n by itself
   all of whose fibers have |det A| elements. `}
def int_matrix_fiber_card (C : CircleSignature) (n : Nat) (A : IntMatrix n) (h : IntNonzero (int_det n A))
  (w : BG (int_power_group C n) .carrier)
  : Mere (Equiv (HomFiber (int_power_group C n) (int_power_group C n) (int_matrix_hom C n A) w) (Fin (int_abs_nat (int_det n A))))
  ≔ let f ≔ int_matrix_factorization n A h in
    let Zn ≔ int_power_group C n in
    let c ≔ int_mat_factors_card n (f .fst) in
    transport Nat (k ↦ Mere (Equiv (HomFiber Zn Zn (int_matrix_hom C n A) w) (Fin k)))
      c (int_abs_nat (int_det n A)) (inverse Nat (int_abs_nat (int_det n A)) c (f .snd .snd))
      (transport (GroupHom Zn Zn) (hh ↦ Mere (Equiv (HomFiber Zn Zn hh w) (Fin c)))
        (int_vec_hom C n (int_mat_factors_eval n (f .fst)) (int_mat_factors_additive n (f .fst))) (int_matrix_hom C n A)
        (int_matrix_hom_factor_path C n A f) (int_vec_factors_fiber_card C n (f .fst) w))

def int_matrix_covering (C : CircleSignature) (n : Nat) (A : IntMatrix n) (h : IntNonzero (int_det n A))
  : IsCovering (BG (int_power_group C n) .carrier) (BG (int_power_group C n) .carrier)
      (hom_function (int_power_group C n) (int_power_group C n) (int_matrix_hom C n A))
  ≔ group_mono_covering (int_power_group C n) (int_power_group C n) (int_matrix_hom C n A) (int_matrix_mono_of_det C n A h)

{` Litmus: the factorization is computed, e.g. for A = (2 1; 0 2) (det 4,
   cokernel Z/4, not Z/2 × Z/2) its card is 4 by refl. `}
def int_matrix_factorization_litmus
  : Id Nat (int_mat_factors_card (suc. (suc. zero.))
      (int_matrix_factorization (suc. (suc. zero.)) (i j ↦ match i [
         | inl. _ ↦ match j [ inl. _ ↦ pos. 2 | inr. _ ↦ pos. 1 ]
         | inr. _ ↦ match j [ inl. _ ↦ pos. 0 | inr. _ ↦ pos. 2 ] ])
        (h ↦ int_encode (pos. 4) int_zero h) .fst)) 4
  ≔ refl (4 : Nat)
