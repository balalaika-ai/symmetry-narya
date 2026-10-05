export "965-integer-matrix-negative"
export "407-group-family-products"

{` Chapter 9 (subgroups.tex 1186), diagonal integer matrices
   A = diag(d_1, …, d_k) acting on Z^k = power_group (Fin k) Z (module 407):
   BA(x)_i ≔ B(d_i)(x_i). If all d_i ≠ 0, A is a monomorphism (its
   classifying map is a covering, being a product of coverings) and its
   cokernel at the shape is Π_i Fin |d_i| ≃ Fin (Π_i |d_i|), i.e. has
   |det A| elements. Not formalized: the converse (some d_i = 0 ⇒ not
   mono) for k > 1, and general n × n matrices (reduction to diagonal form
   / Smith normal form, determinants of non-diagonal matrices). `}

def int_abs_nat (d : Int) : Nat ≔ match d [ pos. n ↦ n | neg. n ↦ suc. n ]

def IntNonzero (d : Int) : Type ≔ Id Int d (pos. zero.) → Empty

{` The 1 × 1 facts for all nonzero d. `}
def matrix1_neg_fiber_equiv (C : CircleSignature) (n : Nat)
  : Equiv (HomFiber (circle_group C) (circle_group C) (circle_multiplication_hom C (neg. n)) (shape (circle_group C))) (Fin (suc. n))
  ≔ let Z ≔ circle_group C in
    transport (GroupHom Z Z) (h ↦ Equiv (HomFiber Z Z h (shape Z)) (Fin (suc. n)))
      (matrix1_neg_hom C n) (circle_multiplication_hom C (neg. n)) (matrix1_neg_hom_path C n)
      (compose_equiv (HomFiber Z Z (matrix1_neg_hom C n) (shape Z)) (HomFiber Z Z (matrix1_hom C n) (shape Z)) (Fin (suc. n))
        (preequivalence_fiber_equiv (C .carrier) (C .carrier) (C .carrier) (int_inversion_function_equiv C)
          (hom_function Z Z (matrix1_hom C n)) (shape Z))
        (canonical_inverse_equiv (Fin (suc. n)) (HomFiber Z Z (matrix1_hom C n) (shape Z)) (matrix1_fiber_equiv C n)))

def int_mult_fiber_card (C : CircleSignature) (d : Int) (nz : IntNonzero d)
  : Equiv (HomFiber (circle_group C) (circle_group C) (circle_multiplication_hom C d) (shape (circle_group C))) (Fin (int_abs_nat d))
  ≔ match d [
  | pos. n ↦ match n [
    | zero. ↦ match nz (refl (pos. zero. : Int)) []
    | suc. n ↦ canonical_inverse_equiv (Fin (suc. n))
        (HomFiber (circle_group C) (circle_group C) (circle_multiplication_hom C (pos. (suc. n))) (shape (circle_group C)))
        (matrix1_fiber_equiv C n) ]
  | neg. n ↦ matrix1_neg_fiber_equiv C n ]

def int_mult_mono (C : CircleSignature) (d : Int) (nz : IntNonzero d)
  : IsGroupMono (circle_group C) (circle_group C) (circle_multiplication_hom C d)
  ≔ match d [
  | pos. n ↦ match n [ zero. ↦ match nz (refl (pos. zero. : Int)) [] | suc. n ↦ matrix1_mono C n ]
  | neg. n ↦ matrix1_neg_mono C n ]

{` Z^k and the diagonal homomorphism. `}
def int_power_group (C : CircleSignature) (k : Nat) : Group ≔ power_group (Fin k) (fin_is_finite k) (circle_group C)

def diag_map (C : CircleSignature) (k : Nat) (d : Fin k → Int) (x : Fin k → C .carrier) : Fin k → C .carrier
  ≔ i ↦ hom_function (circle_group C) (circle_group C) (circle_multiplication_hom C (d i)) (x i)

def diag_hom (C : CircleSignature) (k : Nat) (d : Fin k → Int) : GroupHom (int_power_group C k) (int_power_group C k)
  ≔ mkhom (int_power_group C k) (int_power_group C k)
      (diag_map C k d,
       funext (Fin k) (_ ↦ C .carrier) (_ ↦ C .base) (diag_map C k d (_ ↦ C .base))
         (i ↦ hom_point (circle_group C) (circle_group C) (circle_multiplication_hom C (d i))))

{` Fibers of a product map are products of fibers. `}
def diag_fiber_equiv (C : CircleSignature) (k : Nat) (d : Fin k → Int) (w : Fin k → C .carrier)
  : Equiv (BookFiber (Fin k → C .carrier) (Fin k → C .carrier) (diag_map C k d) w)
      ((i : Fin k) → BookFiber (C .carrier) (C .carrier) (hom_function (circle_group C) (circle_group C) (circle_multiplication_hom C (d i))) (w i))
  ≔ let X ≔ C .carrier in
    let f : Fin k → X → X ≔ i ↦ hom_function (circle_group C) (circle_group C) (circle_multiplication_hom C (d i)) in
    quasi_inverse_equiv (BookFiber (Fin k → X) (Fin k → X) (diag_map C k d) w) ((i : Fin k) → BookFiber X X (f i) (w i))
      (u ↦ i ↦ (u .fst i, happly (Fin k) (_ ↦ X) w (diag_map C k d (u .fst)) (u .snd) i))
      (g ↦ ((i ↦ g i .fst), funext (Fin k) (_ ↦ X) w (diag_map C k d (i ↦ g i .fst)) (i ↦ g i .snd)))
      (u ↦ (refl (u .fst), funext_eta (Fin k) (_ ↦ X) w (diag_map C k d (u .fst)) (u .snd)))
      (g ↦ funext (Fin k) (i ↦ BookFiber X X (f i) (w i))
        (i ↦ (g i .fst, happly (Fin k) (_ ↦ X) w (diag_map C k d (j ↦ g j .fst)) (funext (Fin k) (_ ↦ X) w (diag_map C k d (j ↦ g j .fst)) (j ↦ g j .snd)) i))
        g
        (i ↦ (refl (g i .fst),
              inverse (Id X (w i) (f i (g i .fst))) (g i .snd)
                (happly (Fin k) (_ ↦ X) w (diag_map C k d (j ↦ g j .fst)) (funext (Fin k) (_ ↦ X) w (diag_map C k d (j ↦ g j .fst)) (j ↦ g j .snd)) i)
                (funext_beta (Fin k) (_ ↦ X) w (diag_map C k d (j ↦ g j .fst)) (j ↦ g j .snd) i))))

{` All d_i ≠ 0 ⇒ diag(d) is a monomorphism. `}
def diag_mono (C : CircleSignature) (k : Nat) (d : Fin k → Int) (nz : (i : Fin k) → IntNonzero (d i))
  : IsGroupMono (int_power_group C k) (int_power_group C k) (diag_hom C k d)
  ≔ let X ≔ C .carrier in let Z ≔ circle_group C in
    covering_group_mono (int_power_group C k) (int_power_group C k) (diag_hom C k d)
      (w ↦ hlevel_two_to_set (BookFiber (Fin k → X) (Fin k → X) (diag_map C k d) w)
        (hlevel_equiv (suc. (suc. zero.))
          ((i : Fin k) → BookFiber X X (hom_function Z Z (circle_multiplication_hom C (d i))) (w i))
          (BookFiber (Fin k → X) (Fin k → X) (diag_map C k d) w)
          (canonical_inverse_equiv (BookFiber (Fin k → X) (Fin k → X) (diag_map C k d) w)
            ((i : Fin k) → BookFiber X X (hom_function Z Z (circle_multiplication_hom C (d i))) (w i)) (diag_fiber_equiv C k d w))
          (hlevel_pi (suc. (suc. zero.)) (Fin k) (i ↦ BookFiber X X (hom_function Z Z (circle_multiplication_hom C (d i))) (w i))
            (i ↦ set_to_hlevel_two (BookFiber X X (hom_function Z Z (circle_multiplication_hom C (d i))) (w i))
              (group_mono_covering Z Z (circle_multiplication_hom C (d i)) (int_mult_mono C (d i) (nz i)) (w i))))))

{` Finite products of finite sets: Π_{i : Fin k} Fin (a_i) ≃ Fin (Π_i a_i). `}
def fin_nat_prod (k : Nat) (a : Fin k → Nat) : Nat
  ≔ match k [ zero. ↦ suc. zero. | suc. k ↦ mul (fin_nat_prod k (x ↦ a (inl. x))) (a (inr. star.)) ]

def ch9w2_product_equiv_left (A A' B : Type) (e : Equiv A A') : Equiv (Product A B) (Product A' B)
  ≔ quasi_inverse_equiv (Product A B) (Product A' B) (u ↦ (e .map (u .fst), u .snd))
      (v ↦ (equiv_inverse_map A A' e (v .fst), v .snd))
      (u ↦ (equiv_retraction A A' e (u .fst), refl (u .snd))) (v ↦ (equiv_counit A A' e (v .fst), refl (v .snd)))

def ch9w2_sum_unit_join (X : Type) (P : Sum X Unit → Type) (u : Product ((x : X) → P (inl. x)) (P (inr. star.)))
  (s : Sum X Unit) : P s
  ≔ match s [ inl. x ↦ u .fst x | inr. v ↦ match v [ star. ↦ u .snd ] ]

def ch9w2_sum_unit_join_eta (X : Type) (P : Sum X Unit → Type) (f : (s : Sum X Unit) → P s) (s : Sum X Unit)
  : Id (P s) (ch9w2_sum_unit_join X P ((x ↦ f (inl. x)), f (inr. star.)) s) (f s)
  ≔ match s [ inl. x ↦ refl (f (inl. x)) | inr. v ↦ match v [ star. ↦ refl (f (inr. star.)) ] ]

def ch9w2_pi_sum_unit_equiv (X : Type) (P : Sum X Unit → Type)
  : Equiv ((s : Sum X Unit) → P s) (Product ((x : X) → P (inl. x)) (P (inr. star.)))
  ≔ quasi_inverse_equiv ((s : Sum X Unit) → P s) (Product ((x : X) → P (inl. x)) (P (inr. star.)))
      (f ↦ ((x ↦ f (inl. x)), f (inr. star.)))
      (ch9w2_sum_unit_join X P)
      (f ↦ funext (Sum X Unit) P (ch9w2_sum_unit_join X P ((x ↦ f (inl. x)), f (inr. star.))) f
        (ch9w2_sum_unit_join_eta X P f))
      (u ↦ refl u)

def ch9w2_fin_zero_fun (a : Fin zero. → Nat) (i : Fin zero.) : Fin (a i) ≔ match i []

def ch9w2_fin_zero_path (a : Fin zero. → Nat) (f : (i : Fin zero.) → Fin (a i)) (i : Fin zero.)
  : Id (Fin (a i)) (ch9w2_fin_zero_fun a i) (f i) ≔ match i []

def fin_pi_card (k : Nat) (a : Fin k → Nat) : Equiv ((i : Fin k) → Fin (a i)) (Fin (fin_nat_prod k a))
  ≔ match k [
  | zero. ↦ quasi_inverse_equiv ((i : Fin zero.) → Fin (a i)) (Fin (suc. zero.)) (_ ↦ inr. star.) (_ ↦ ch9w2_fin_zero_fun a)
      (f ↦ funext (Fin zero.) (i ↦ Fin (a i)) (ch9w2_fin_zero_fun a) f (ch9w2_fin_zero_path a f))
      [ inl. e ↦ match e [] | inr. v ↦ match v [ star. ↦ refl (inr. star. : Fin (suc. zero.)) ] ]
  | suc. k ↦ compose_equiv ((i : Fin (suc. k)) → Fin (a i)) (Product ((x : Fin k) → Fin (a (inl. x))) (Fin (a (inr. star.))))
      (Fin (fin_nat_prod (suc. k) a))
      (ch9w2_pi_sum_unit_equiv (Fin k) (i ↦ Fin (a i)))
      (compose_equiv (Product ((x : Fin k) → Fin (a (inl. x))) (Fin (a (inr. star.))))
        (Product (Fin (fin_nat_prod k (x ↦ a (inl. x)))) (Fin (a (inr. star.)))) (Fin (fin_nat_prod (suc. k) a))
        (ch9w2_product_equiv_left ((x : Fin k) → Fin (a (inl. x))) (Fin (fin_nat_prod k (x ↦ a (inl. x)))) (Fin (a (inr. star.)))
          (fin_pi_card k (x ↦ a (inl. x))))
        (fin_product_equiv (fin_nat_prod k (x ↦ a (inl. x))) (a (inr. star.)))) ]

{` coker(diag(d))(sh) ≃ Π_i Fin |d_i| ≃ Fin (Π_i |d_i|) = Fin |det diag(d)|. `}
def diag_cokernel_pi (C : CircleSignature) (k : Nat) (d : Fin k → Int) (nz : (i : Fin k) → IntNonzero (d i))
  : Equiv (gset_underlying (int_power_group C k) (cokernel (int_power_group C k) (int_power_group C k) (diag_hom C k d)))
      ((i : Fin k) → Fin (int_abs_nat (d i)))
  ≔ let X ≔ C .carrier in let Z ≔ circle_group C in
    let F ≔ HomFiber (int_power_group C k) (int_power_group C k) (diag_hom C k d) (shape (int_power_group C k)) in
    let P ≔ (i : Fin k) → BookFiber X X (hom_function Z Z (circle_multiplication_hom C (d i))) (C .base) in
    let eF : Equiv F P ≔ diag_fiber_equiv C k d (_ ↦ C .base) in
    let eP : Equiv P ((i : Fin k) → Fin (int_abs_nat (d i)))
      ≔ pi_family_equiv (Fin k) (i ↦ BookFiber X X (hom_function Z Z (circle_multiplication_hom C (d i))) (C .base))
          (i ↦ Fin (int_abs_nat (d i))) (i ↦ int_mult_fiber_card C (d i) (nz i)) in
    let hF : isSet F ≔ hlevel_two_to_set F (hlevel_equiv (suc. (suc. zero.)) ((i : Fin k) → Fin (int_abs_nat (d i))) F
      (canonical_inverse_equiv F ((i : Fin k) → Fin (int_abs_nat (d i))) (compose_equiv F P ((i : Fin k) → Fin (int_abs_nat (d i))) eF eP))
      (hlevel_pi (suc. (suc. zero.)) (Fin k) (i ↦ Fin (int_abs_nat (d i))) (i ↦ set_to_hlevel_two (Fin (int_abs_nat (d i))) (fin_set (int_abs_nat (d i)))))) in
    compose_equiv (SetTrunc F) F ((i : Fin k) → Fin (int_abs_nat (d i))) (set_trunc_of_set_equiv F hF)
      (compose_equiv F P ((i : Fin k) → Fin (int_abs_nat (d i))) eF eP)

def diag_cokernel_card (C : CircleSignature) (k : Nat) (d : Fin k → Int) (nz : (i : Fin k) → IntNonzero (d i))
  : Equiv (gset_underlying (int_power_group C k) (cokernel (int_power_group C k) (int_power_group C k) (diag_hom C k d)))
      (Fin (fin_nat_prod k (i ↦ int_abs_nat (d i))))
  ≔ compose_equiv (gset_underlying (int_power_group C k) (cokernel (int_power_group C k) (int_power_group C k) (diag_hom C k d)))
      ((i : Fin k) → Fin (int_abs_nat (d i))) (Fin (fin_nat_prod k (i ↦ int_abs_nat (d i))))
      (diag_cokernel_pi C k d nz) (fin_pi_card k (i ↦ int_abs_nat (d i)))
