export "962-composite-fibers-rotation-exercise"
export "954-abstract-kernel"
export "1310-integer-ring"
export "824-integer-intersection"
export "1720-blass-counting"
export "434-permutation-hom-litmus"
export "456-sign-inversions"
export "457-sign-permutations"
export "288-chapter-three-text-claims"
export "413-group-motivation"

{` Chapter 9 (subgroups.tex), exa:fibersofcomposites (line 687) and
   xca:fibersofcomposites (line 764): the full stabilizer characterizations.
   Modules 961/962 prove memberships for natural exponents and some
   non-memberships; here every symmetry is classified: for Z ≔ circle_group C,
   g ∈ Ker(mod_4) iff g = loop^{4k} for an integer k, g ∈ Ker(sgn∘prj∘mod_4)
   iff g = loop^{2k}, h ∈ Ker(sgn∘prj) iff h = e or h = s², and for the
   exercise g ∈ Ker(R_4) iff g = loop^{4k}, h ∈ Ker(sgn) iff h is even,
   g ∈ Ker(sgn∘R_4) iff g = loop^{2k}. Ker(f) ∋ g is the stabilizer condition
   g · Bf_pt = Bf_pt in the G-set f^*P_H (kernel_member_iff, module 954);
   the stabilizer forms are the *_stabilizer_iff declarations. Ingredients:
   lem:order-divides (usym_order_divides, 1010), the winding number (28, 413,
   824) and integer arithmetic (1310); USym C_4 has four elements
   (bsix_injection_full, 1720). `}

def foc_four : Nat ≔ suc. three

{` g is loop^{nk} for some integer k. `}
def CircleLoopMultiple (C : CircleSignature) (n : Int) (g : USym (circle_group C)) : Type
  ≔ Mere (Σ Int (k ↦ Id (USym (circle_group C)) g (circle_power C (int_mul n k))))

{` For φ : Hom(Z, K) with φ(loop) = a: φ(loop^z) = a^z. `}
def foc_phi_power (C : CircleSignature) (K : Group) (φ : GroupHom (circle_group C) K) (a : USym K)
  (hl : Id (USym K) (usym_hom (circle_group C) K φ (C .loop)) a) (z : Int)
  : Id (USym K) (usym_hom (circle_group C) K φ (circle_power C z)) (loop_power (BG K .carrier) (shape K) a z)
  ≔ let BK ≔ BG K .carrier in let sK ≔ shape K in
    concat (USym K) (usym_hom (circle_group C) K φ (circle_power C z))
      (loop_power BK sK (usym_hom (circle_group C) K φ (C .loop)) z) (loop_power BK sK a z)
      (loops_map_power (BG (circle_group C)) (BG K) (hom_B (circle_group C) K φ) (C .loop) z)
      (refl ((l ↦ loop_power BK sK l z) : USym K → USym K) hl)

{` If a has order n: loop^{nk} ∈ Ker φ. `}
def foc_z_kernel_back (C : CircleSignature) (K : Group) (φ : GroupHom (circle_group C) K) (a : USym K)
  (hl : Id (USym K) (usym_hom (circle_group C) K φ (C .loop)) a) (n : Nat)
  (min : IsMinimum (UsymPositivePeriod K a) n) (k : Int)
  : InKer (circle_group C) K φ (circle_power C (int_mul (pos. n) k))
  ≔ let Z ≔ circle_group C in let L ≔ USym Z in
    let BK ≔ BG K .carrier in let sK ≔ shape K in
    let p ≔ circle_power C (pos. n) in
    let pk ≔ loop_power (C .carrier) (C .base) p k in
    let e1 : Id L (circle_power C (int_mul (pos. n) k)) pk
      ≔ pbg_winding_injective C (circle_power C (int_mul (pos. n) k)) pk
          (concat Int (circle_winding C (circle_power C (int_mul (pos. n) k))) (int_mul (pos. n) k) (circle_winding C pk)
            (circle_winding_power C (int_mul (pos. n) k))
            (inverse Int (circle_winding C pk) (int_mul (pos. n) k)
              (concat Int (circle_winding C pk) (int_mul (circle_winding C p) k) (int_mul (pos. n) k)
                (circle_winding_power_arbitrary C p k)
                (refl ((w ↦ int_mul w k) : Int → Int) (circle_winding_power C (pos. n)))))) in
    let hp : Id (USym K) (usym_hom Z K φ p) (usym_unit K)
      ≔ concat (USym K) (usym_hom Z K φ p) (usym_power K a n) (usym_unit K)
          (foc_phi_power C K φ a hl (pos. n)) (min .fst .snd) in
    concat (USym K) (usym_hom Z K φ (circle_power C (int_mul (pos. n) k))) (usym_hom Z K φ pk) (usym_unit K)
      (refl (usym_hom Z K φ) e1)
      (concat (USym K) (usym_hom Z K φ pk) (loop_power BK sK (usym_hom Z K φ p) k) (usym_unit K)
        (loops_map_power (BG Z) (BG K) (hom_B Z K φ) p k)
        (loop_power_trivial BK sK (usym_hom Z K φ p) hp k))

{` From a^w = e: w is a multiple of the order n (positive and negative w separately). `}
def foc_z_kernel_fwd_at (C : CircleSignature) (K : Group) (a : USym K) (n : Nat)
  (min : IsMinimum (UsymPositivePeriod K a) n) (g : USym (circle_group C)) (w : Int)
  : Id (USym (circle_group C)) (circle_power C w) g
    → Id (USym K) (loop_power (BG K .carrier) (shape K) a w) (usym_unit K)
    → CircleLoopMultiple C (pos. n) g
  ≔ let L ≔ USym (circle_group C) in
    let BK ≔ BG K .carrier in let sK ≔ shape K in
    let T ≔ Σ Int (k ↦ Id L g (circle_power C (int_mul (pos. n) k))) in
    match w [
    | pos. m ↦ eg hk ↦
        mere_rec (Σ Nat (q ↦ Id Nat m (mul q n))) (Mere T) (mere_isprop T)
          (t ↦ mere T
            (pos. (t .fst),
             concat L g (circle_power C (pos. m)) (circle_power C (int_mul (pos. n) (pos. (t .fst))))
               (inverse L (circle_power C (pos. m)) g eg)
               (refl (circle_power C)
                 (concat Int (pos. m) (pos. (mul n (t .fst))) (int_mul (pos. n) (pos. (t .fst)))
                   (refl ((x ↦ pos. x) : Nat → Int)
                     (concat Nat m (mul (t .fst) n) (mul n (t .fst)) (t .snd) (mul_comm (t .fst) n)))
                   (int_mul_naturals n (t .fst))))))
          (usym_order_divides K a n min m hk)
    | neg. m ↦ eg hk ↦
        let x ≔ loop_power_nat BK sK a (suc. m) in
        let i : Id (USym K) (inverse BK sK sK x) (refl sK)
          ≔ concat (USym K) (inverse BK sK sK x) (loop_power BK sK a (neg. m)) (refl sK)
              (inverse (USym K) (loop_power BK sK a (neg. m)) (inverse BK sK sK x) (usym_power_inv K a (suc. m)))
              hk in
        let hx : Id (USym K) x (usym_unit K)
          ≔ concat (USym K) x (inverse BK sK sK (inverse BK sK sK x)) (refl sK)
              (inverse (USym K) (inverse BK sK sK (inverse BK sK sK x)) x (inverse_inverse BK sK sK x))
              (concat (USym K) (inverse BK sK sK (inverse BK sK sK x)) (inverse BK sK sK (refl sK)) (refl sK)
                (refl (inverse BK sK sK) i) (inverse_refl BK sK)) in
        mere_rec (Σ Nat (q ↦ Id Nat (suc. m) (mul q n))) (Mere T) (mere_isprop T)
          (t ↦ let q ≔ t .fst in
            mere T
            (int_neg (pos. q),
             concat L g (circle_power C (neg. m)) (circle_power C (int_mul (pos. n) (int_neg (pos. q))))
               (inverse L (circle_power C (neg. m)) g eg)
               (refl (circle_power C)
                 (calc
                   (neg. m : Int) = int_neg (pos. (mul n q))
                     by refl ((y ↦ int_neg (pos. y)) : Nat → Int)
                          (concat Nat (suc. m) (mul q n) (mul n q) (t .snd) (mul_comm q n))
                   = int_neg (int_mul (pos. n) (pos. q)) by refl int_neg (int_mul_naturals n q)
                   = int_mul (pos. n) (int_neg (pos. q))
                     by inverse Int (int_mul (pos. n) (int_neg (pos. q))) (int_neg (int_mul (pos. n) (pos. q)))
                          (int_mul_neg_right (pos. n) (pos. q)) ∎))))
          (usym_order_divides K a n min (suc. m) hx) ]

{` The generic kernel characterization: g ∈ Ker φ iff g = loop^{nk} for some integer k. `}
def foc_z_kernel_iff (C : CircleSignature) (K : Group) (φ : GroupHom (circle_group C) K) (a : USym K)
  (hl : Id (USym K) (usym_hom (circle_group C) K φ (C .loop)) a) (n : Nat)
  (min : IsMinimum (UsymPositivePeriod K a) n) (g : USym (circle_group C))
  : Product (InKer (circle_group C) K φ g → CircleLoopMultiple C (pos. n) g) (CircleLoopMultiple C (pos. n) g → InKer (circle_group C) K φ g)
  ≔ let Z ≔ circle_group C in let L ≔ USym Z in
    let BK ≔ BG K .carrier in let sK ≔ shape K in
    (ik ↦
       let w ≔ circle_winding C g in
       let eg : Id L (circle_power C w) g ≔ circle_every_symmetry_power C g in
       foc_z_kernel_fwd_at C K a n min g w eg
         (concat (USym K) (loop_power BK sK a w) (usym_hom Z K φ (circle_power C w)) (usym_unit K)
           (inverse (USym K) (usym_hom Z K φ (circle_power C w)) (loop_power BK sK a w) (foc_phi_power C K φ a hl w))
           (concat (USym K) (usym_hom Z K φ (circle_power C w)) (usym_hom Z K φ g) (usym_unit K)
             (refl (usym_hom Z K φ) eg) ik)),
     lm ↦ mere_rec (Σ Int (k ↦ Id L g (circle_power C (int_mul (pos. n) k)))) (InKer Z K φ g)
       (usym_set K (usym_hom Z K φ g) (usym_unit K))
       (t ↦ transport L (x ↦ InKer Z K φ x) (circle_power C (int_mul (pos. n) (t .fst))) g
         (inverse L g (circle_power C (int_mul (pos. n) (t .fst))) (t .snd))
         (foc_z_kernel_back C K φ a hl n min (t .fst)))
       lm)

{` Orders: s ∈ C_4 and ρ ∈ Σ_4 have order 4; the images of loop in Σ_2 under sgn∘prj∘mod_4 and sgn∘R_4 order 2. `}
def foc_fin4_nonzero (x : Fin foc_four) (c : ex_fin4_code x → Empty)
  : Id (Fin foc_four) x (inr. star.) → Empty
  ≔ q ↦ c (transport (Fin foc_four) ex_fin4_code (inr. star.) x (inverse (Fin foc_four) x (inr. star.) q) star.)

def foc_s_order : IsMinimum (UsymPositivePeriod (cyclic_group_fin three) (cyclic_fin_generator three)) foc_four
  ≔ ((lt_to_book zero. foc_four star., ex_s4_unit),
     (m ↦ match m [
       | zero. ↦ w ↦ absurd (BookLe foc_four zero.) (lt_from_book zero. zero. (w .fst))
       | suc. zero. ↦ w ↦ absurd (BookLe foc_four (suc. zero.)) (ex_s1_not_unit (w .snd))
       | suc. (suc. zero.) ↦ w ↦ absurd (BookLe foc_four (suc. (suc. zero.))) (ex_s2_not_unit (w .snd))
       | suc. (suc. (suc. zero.)) ↦ w ↦ absurd (BookLe foc_four three)
           (ex_s_pow_not_unit three (foc_fin4_nonzero (inl. (inl. (inl. (inr. star.)))) (v ↦ v)) (w .snd))
       | suc. (suc. (suc. (suc. m))) ↦ w ↦ le_to_book foc_four (suc. (suc. (suc. (suc. m)))) star. ]))

def foc_rho_order : IsMinimum (UsymPositivePeriod (symmetric_group foc_four) (finite_successor_symmetry three)) foc_four
  ≔ ((lt_to_book zero. foc_four star., xr_rho4_unit),
     (m ↦ match m [
       | zero. ↦ w ↦ absurd (BookLe foc_four zero.) (lt_from_book zero. zero. (w .fst))
       | suc. zero. ↦ w ↦ absurd (BookLe foc_four (suc. zero.))
           (xr_rho_pow_not_unit (suc. zero.) (foc_fin4_nonzero (inl. (inr. star.)) (v ↦ v)) (w .snd))
       | suc. (suc. zero.) ↦ w ↦ absurd (BookLe foc_four (suc. (suc. zero.)))
           (xr_rho_pow_not_unit (suc. (suc. zero.)) (foc_fin4_nonzero (inl. (inl. (inr. star.))) (v ↦ v)) (w .snd))
       | suc. (suc. (suc. zero.)) ↦ w ↦ absurd (BookLe foc_four three)
           (xr_rho_pow_not_unit three (foc_fin4_nonzero (inl. (inl. (inl. (inr. star.)))) (v ↦ v)) (w .snd))
       | suc. (suc. (suc. (suc. m))) ↦ w ↦ le_to_book foc_four (suc. (suc. (suc. (suc. m)))) star. ]))

def foc_sign_order (G : Group) (φ : GroupHom G sign_sigma_two) (g : USym G)
  (h1 : Id Sign (sigma_two_sign (usym_hom G sign_sigma_two φ (usym_power G g (suc. zero.)))) minus.)
  (h2 : Id Sign (sigma_two_sign (usym_hom G sign_sigma_two φ (usym_power G g two))) plus.)
  : IsMinimum (UsymPositivePeriod sign_sigma_two (usym_hom G sign_sigma_two φ g)) two
  ≔ let S ≔ USym sign_sigma_two in let a ≔ usym_hom G sign_sigma_two φ g in
    ((lt_to_book zero. two star.,
      concat S (usym_power sign_sigma_two a two) (usym_hom G sign_sigma_two φ (usym_power G g two)) (usym_unit sign_sigma_two)
        (inverse S (usym_hom G sign_sigma_two φ (usym_power G g two)) (usym_power sign_sigma_two a two)
          (usym_hom_power G sign_sigma_two φ g two))
        (sigma_two_unit_of_plus (usym_hom G sign_sigma_two φ (usym_power G g two)) h2)),
     (m ↦ match m [
       | zero. ↦ w ↦ absurd (BookLe two zero.) (lt_from_book zero. zero. (w .fst))
       | suc. zero. ↦ w ↦ absurd (BookLe two (suc. zero.))
           (sigma_two_not_unit_of_minus (usym_hom G sign_sigma_two φ (usym_power G g (suc. zero.))) h1
             (concat S (usym_hom G sign_sigma_two φ (usym_power G g (suc. zero.))) (usym_power sign_sigma_two a (suc. zero.))
               (usym_unit sign_sigma_two) (usym_hom_power G sign_sigma_two φ g (suc. zero.)) (w .snd)))
       | suc. (suc. m) ↦ w ↦ le_to_book two (suc. (suc. m)) star. ]))

{` The sign of h : USym Σ_4 computed by inversions of the underlying permutation. `}
def foc_perm_sym_eta (h : USym (symmetric_group foc_four))
  : Id (USym (symmetric_group foc_four)) h (permutation_symmetry (standard_set foc_four) (symmetric_group_usym_equiv foc_four .map h))
  ≔ permutation_symmetry_ext (standard_set foc_four) h
      (permutation_symmetry (standard_set foc_four) (symmetric_group_usym_equiv foc_four .map h))
      (x ↦ inverse (Fin foc_four) (symmetric_group_usym_equiv foc_four .map h .map x)
             (permutation_action (standard_set foc_four) h x)
             (id_to_equiv_transport (Fin foc_four) (Fin foc_four) (h .fst .fst) x))

def foc_usgn_perm_sign (h : USym (symmetric_group foc_four))
  : Id Sign (sigma_two_sign (usgn foc_four h))
      (permutation_sign_at foc_four (standard_shape foc_four) (symmetric_group_usym_equiv foc_four .map h))
  ≔ let t ≔ symmetric_group_usym_equiv foc_four .map h in
    calc
      sigma_two_sign (usgn foc_four h) = sigma_two_sign (usgn foc_four (permutation_symmetry (standard_set foc_four) t))
        by refl ((k ↦ sigma_two_sign (usgn foc_four k)) : USym (symmetric_group foc_four) → Sign) (foc_perm_sym_eta h)
      = bool_sign (nat_odd (inversion_number foc_four t)) by usgn_inversion_number two t
      = bool_sign (nat_odd (inversion_count foc_four t))
        by refl ((k ↦ bool_sign (nat_odd k)) : Nat → Sign)
             (inverse Nat (inversion_count foc_four t) (inversion_number foc_four t) (inversion_count_number foc_four t))
      = permutation_sign_at foc_four (standard_shape foc_four) t
        by inverse Sign (permutation_sign_at foc_four (standard_shape foc_four) t)
             (bool_sign (nat_odd (inversion_count foc_four t))) (permutation_sign_at_inversions foc_four t) ∎

{` Every h : USym C_4 is s^i for some
   i < 4 (the four powers have different values at 0, USym C_4 ≃ Fin 4, pigeonhole bsix_injection_full); the sign
   of s^i is (-1)^i (ex_f2_pow_sign). `}
def foc_nat_of_fin4 : Fin foc_four → Nat ≔ [
  | inr. _ ↦ zero.
  | inl. (inr. _) ↦ suc. zero.
  | inl. (inl. (inr. _)) ↦ suc. (suc. zero.)
  | inl. (inl. (inl. (inr. _))) ↦ three
  | inl. (inl. (inl. (inl. v))) ↦ match v [] ]

def foc_fin4_iterate (i : Fin foc_four)
  : Id (Fin foc_four) (ch9w2_iterate (Fin foc_four) (finite_fin_successor three .map) (foc_nat_of_fin4 i) (inr. star.)) i
  ≔ match i [
  | inr. star. ↦ refl (inr. star. : Fin foc_four)
  | inl. (inr. star.) ↦ refl (inl. (inr. star.) : Fin foc_four)
  | inl. (inl. (inr. star.)) ↦ refl (inl. (inl. (inr. star.)) : Fin foc_four)
  | inl. (inl. (inl. (inr. star.))) ↦ refl (inl. (inl. (inl. (inr. star.))) : Fin foc_four)
  | inl. (inl. (inl. (inl. v))) ↦ match v [] ]

def foc_c4_val (g : USym (cyclic_group_fin three)) : Fin foc_four
  ≔ permutation_action (standard_set foc_four) (usym_hom (cyclic_group_fin three) (symmetric_group foc_four) (cyclic_forget_hom three) g) (inr. star.)

def foc_c4_pow (i : Fin foc_four) : USym (cyclic_group_fin three) ≔ usym_power (cyclic_group_fin three) (cyclic_fin_generator three) (foc_nat_of_fin4 i)

def foc_c4_pow_val (i : Fin foc_four) : Id (Fin foc_four) (foc_c4_val (foc_c4_pow i)) i
  ≔ concat (Fin foc_four) (foc_c4_val (foc_c4_pow i))
      (ch9w2_iterate (Fin foc_four) (finite_fin_successor three .map) (foc_nat_of_fin4 i) (inr. star.)) i
      (ex_prj_pow_action (foc_nat_of_fin4 i) (inr. star.)) (foc_fin4_iterate i)

def foc_c4_enum_map (i : Fin foc_four) : Fin foc_four
  ≔ cyclic_group_fin_usym_equiv three .map (foc_c4_pow i)

def foc_c4_enum_reflects : PathReflecting (Fin foc_four) (Fin foc_four) foc_c4_enum_map
  ≔ i j q ↦
    let F ≔ Fin foc_four in
    let e ≔ equivalence_injective (USym (cyclic_group_fin three)) F (cyclic_group_fin_usym_equiv three) (foc_c4_pow i) (foc_c4_pow j) q in
    calc
      i = foc_c4_val (foc_c4_pow i) by inverse F (foc_c4_val (foc_c4_pow i)) i (foc_c4_pow_val i)
      = foc_c4_val (foc_c4_pow j) by refl foc_c4_val e
      = j by foc_c4_pow_val j ∎

def foc_c4_is_power (h : USym (cyclic_group_fin three)) : Σ (Fin foc_four) (i ↦ Id (USym (cyclic_group_fin three)) h (foc_c4_pow i))
  ≔ let F ≔ Fin foc_four in
    let w ≔ bsix_injection_full foc_four foc_c4_enum_map foc_c4_enum_reflects (cyclic_group_fin_usym_equiv three .map h) in
    (w .fst, equivalence_injective (USym (cyclic_group_fin three)) F (cyclic_group_fin_usym_equiv three) h (foc_c4_pow (w .fst)) (w .snd))

def foc_c4_classify (h : USym (cyclic_group_fin three)) (fx : InKer (cyclic_group_fin three) sign_sigma_two ex_f2 h)
  : (i : Fin foc_four) → Id (USym (cyclic_group_fin three)) h (foc_c4_pow i)
    → Sum (Id (USym (cyclic_group_fin three)) h (usym_unit (cyclic_group_fin three))) (Id (USym (cyclic_group_fin three)) h (usym_mul (cyclic_group_fin three) (cyclic_fin_generator three) (cyclic_fin_generator three)))
  ≔ let U ≔ USym (cyclic_group_fin three) in let s ≔ (cyclic_fin_generator three) in
    let B ≔ BG (cyclic_group_fin three) .carrier in let s0 ≔ shape (cyclic_group_fin three) in
    let odd : (r : Nat) → Id Sign (sign_power minus. r) minus. → Id U h (usym_power (cyclic_group_fin three) s r) → Empty
      ≔ r sr e ↦ sigma_two_not_unit_of_minus (usym_hom (cyclic_group_fin three) sign_sigma_two ex_f2 (usym_power (cyclic_group_fin three) s r))
          (concat Sign (sigma_two_sign (usym_hom (cyclic_group_fin three) sign_sigma_two ex_f2 (usym_power (cyclic_group_fin three) s r))) (sign_power minus. r) minus.
            (ex_f2_pow_sign r) sr)
          (transport U (x ↦ InKer (cyclic_group_fin three) sign_sigma_two ex_f2 x) h (usym_power (cyclic_group_fin three) s r) e fx) in
    i ↦ match i [
    | inr. star. ↦ e ↦ inl. e
    | inl. (inr. star.) ↦ e ↦ match odd (suc. zero.) (refl (minus. : Sign)) e []
    | inl. (inl. (inr. star.)) ↦ e ↦ inr.
        (concat U h (usym_power (cyclic_group_fin three) s (suc. (suc. zero.))) (usym_mul (cyclic_group_fin three) s s) e
          (refl ((r ↦ concat B s0 s0 s0 r s) : U → U) (concat_1p B s0 s0 s)))
    | inl. (inl. (inl. (inr. star.))) ↦ e ↦ match odd three (refl (minus. : Sign)) e []
    | inl. (inl. (inl. (inl. v))) ↦ match v [] ]

{` exa:fibersofcomposites: the kernels of f1 = mod_4, f2 = sgn∘prj and f2 f1. `}
def foc_mod4_kernel_iff (C : CircleSignature) (g : USym (circle_group C))
  : Product (InKer (circle_group C) (cyclic_group_fin three) (ex_f1 C) g → CircleLoopMultiple C (pos. foc_four) g)
      (CircleLoopMultiple C (pos. foc_four) g → InKer (circle_group C) (cyclic_group_fin three) (ex_f1 C) g)
  ≔ foc_z_kernel_iff C (cyclic_group_fin three) (ex_f1 C) (cyclic_fin_generator three) (mod_hom_loop C three) foc_four foc_s_order g

def foc_composite_kernel_iff (C : CircleSignature) (g : USym (circle_group C))
  : Product (InKer (circle_group C) sign_sigma_two (ex_f21 C) g → CircleLoopMultiple C (pos. two) g)
      (CircleLoopMultiple C (pos. two) g → InKer (circle_group C) sign_sigma_two (ex_f21 C) g)
  ≔ let Z ≔ circle_group C in
    foc_z_kernel_iff C sign_sigma_two (ex_f21 C) (usym_hom Z sign_sigma_two (ex_f21 C) (C .loop))
      (refl (usym_hom Z sign_sigma_two (ex_f21 C) (C .loop))) two
      (foc_sign_order Z (ex_f21 C) (C .loop) (ex_f21_pow_sign C (suc. zero.)) (ex_f21_pow_sign C two)) g

def foc_sgnprj_kernel_iff (h : USym (cyclic_group_fin three))
  : Product
      (InKer (cyclic_group_fin three) sign_sigma_two ex_f2 h
        → Sum (Id (USym (cyclic_group_fin three)) h (usym_unit (cyclic_group_fin three)))
              (Id (USym (cyclic_group_fin three)) h (usym_mul (cyclic_group_fin three) (cyclic_fin_generator three) (cyclic_fin_generator three))))
      (Sum (Id (USym (cyclic_group_fin three)) h (usym_unit (cyclic_group_fin three)))
           (Id (USym (cyclic_group_fin three)) h (usym_mul (cyclic_group_fin three) (cyclic_fin_generator three) (cyclic_fin_generator three)))
        → InKer (cyclic_group_fin three) sign_sigma_two ex_f2 h)
  ≔ let C4 ≔ cyclic_group_fin three in
    let U ≔ USym C4 in let s ≔ cyclic_fin_generator three in
    let B ≔ BG C4 .carrier in let s0 ≔ shape C4 in
    let w ≔ foc_c4_is_power h in
    (ik ↦ foc_c4_classify h ik (w .fst) (w .snd),
     c ↦ match c [
       | inl. e ↦ transport U (x ↦ InKer C4 sign_sigma_two ex_f2 x) (usym_unit C4) h (inverse U h (usym_unit C4) e)
           (usym_hom_unit C4 sign_sigma_two ex_f2)
       | inr. e ↦ transport U (x ↦ InKer C4 sign_sigma_two ex_f2 x) (usym_power C4 s (suc. (suc. zero.))) h
           (concat U (usym_power C4 s (suc. (suc. zero.))) (usym_mul C4 s s) h
             (refl ((r ↦ concat B s0 s0 s0 r s) : U → U) (concat_1p B s0 s0 s))
             (inverse U h (usym_mul C4 s s) e))
           ex_f2_kernel_s2 ])

{` xca:fibersofcomposites: the kernels of R_4, sgn and sgn∘R_4. `}
def xr_R4_kernel_iff (C : CircleSignature) (g : USym (circle_group C))
  : Product (InKer (circle_group C) (symmetric_group foc_four) (xr_R4 C) g → CircleLoopMultiple C (pos. foc_four) g)
      (CircleLoopMultiple C (pos. foc_four) g → InKer (circle_group C) (symmetric_group foc_four) (xr_R4 C) g)
  ≔ foc_z_kernel_iff C (symmetric_group foc_four) (xr_R4 C) (finite_successor_symmetry three) (power_finset_loop C three) foc_four
      foc_rho_order g

def xr_sgn_kernel_iff (h : USym (symmetric_group foc_four))
  : Product
      (InKer (symmetric_group foc_four) sign_sigma_two (sign_hom foc_four) h
        → Id Sign (permutation_sign_at foc_four (standard_shape foc_four) (symmetric_group_usym_equiv foc_four .map h)) plus.)
      (Id Sign (permutation_sign_at foc_four (standard_shape foc_four) (symmetric_group_usym_equiv foc_four .map h)) plus.
        → InKer (symmetric_group foc_four) sign_sigma_two (sign_hom foc_four) h)
  ≔ let t ≔ symmetric_group_usym_equiv foc_four .map h in
    let ps ≔ foc_usgn_perm_sign h in
    (ik ↦ concat Sign (permutation_sign_at foc_four (standard_shape foc_four) t) (sigma_two_sign (usgn foc_four h)) plus.
            (inverse Sign (sigma_two_sign (usgn foc_four h)) (permutation_sign_at foc_four (standard_shape foc_four) t) ps)
            (concat Sign (sigma_two_sign (usgn foc_four h)) (sigma_two_sign (usym_unit sign_sigma_two)) plus.
              (refl sigma_two_sign ik) sigma_two_sign_unit),
     e ↦ sigma_two_unit_of_plus (usgn foc_four h)
           (concat Sign (sigma_two_sign (usgn foc_four h)) (permutation_sign_at foc_four (standard_shape foc_four) t) plus.
             ps e))

def xr_sR4_kernel_iff (C : CircleSignature) (g : USym (circle_group C))
  : Product (InKer (circle_group C) sign_sigma_two (xr_sR4 C) g → CircleLoopMultiple C (pos. two) g)
      (CircleLoopMultiple C (pos. two) g → InKer (circle_group C) sign_sigma_two (xr_sR4 C) g)
  ≔ let Z ≔ circle_group C in
    foc_z_kernel_iff C sign_sigma_two (xr_sR4 C) (usym_hom Z sign_sigma_two (xr_sR4 C) (C .loop))
      (refl (usym_hom Z sign_sigma_two (xr_sR4 C) (C .loop))) two
      (foc_sign_order Z (xr_sR4 C) (C .loop) (xr_sR4_pow_sign C (suc. zero.)) (xr_sR4_pow_sign C two)) g

{` The stabilizer forms: g · Bf_pt = Bf_pt in f^*P_H (the book's "stabilizer of refl"). `}
def KernelGsetFixes (G H : Group) (f : GroupHom G H) (g : USym G) : Type
  ≔ Id (gset_underlying G (kernel_gset G H f)) (gset_usym_act G (kernel_gset G H f) g (hom_point G H f)) (hom_point G H f)

def stabilizer_iff_of_kernel_iff (G H : Group) (f : GroupHom G H) (g : USym G) (P : Type)
  (e : Product (InKer G H f g → P) (P → InKer G H f g))
  : Product (KernelGsetFixes G H f g → P) (P → KernelGsetFixes G H f g)
  ≔ (x ↦ e .fst (kernel_member_iff G H f g .fst x), p ↦ kernel_member_iff G H f g .snd (e .snd p))

def foc_mod4_stabilizer_iff (C : CircleSignature) (g : USym (circle_group C))
  : Product (KernelGsetFixes (circle_group C) (cyclic_group_fin three) (ex_f1 C) g → CircleLoopMultiple C (pos. foc_four) g)
      (CircleLoopMultiple C (pos. foc_four) g → KernelGsetFixes (circle_group C) (cyclic_group_fin three) (ex_f1 C) g)
  ≔ stabilizer_iff_of_kernel_iff (circle_group C) (cyclic_group_fin three) (ex_f1 C) g (CircleLoopMultiple C (pos. foc_four) g)
      (foc_mod4_kernel_iff C g)

def foc_composite_stabilizer_iff (C : CircleSignature) (g : USym (circle_group C))
  : Product (KernelGsetFixes (circle_group C) sign_sigma_two (ex_f21 C) g → CircleLoopMultiple C (pos. two) g)
      (CircleLoopMultiple C (pos. two) g → KernelGsetFixes (circle_group C) sign_sigma_two (ex_f21 C) g)
  ≔ stabilizer_iff_of_kernel_iff (circle_group C) sign_sigma_two (ex_f21 C) g (CircleLoopMultiple C (pos. two) g)
      (foc_composite_kernel_iff C g)

def foc_sgnprj_stabilizer_iff (h : USym (cyclic_group_fin three))
  : Product
      (KernelGsetFixes (cyclic_group_fin three) sign_sigma_two ex_f2 h
        → Sum (Id (USym (cyclic_group_fin three)) h (usym_unit (cyclic_group_fin three)))
              (Id (USym (cyclic_group_fin three)) h (usym_mul (cyclic_group_fin three) (cyclic_fin_generator three) (cyclic_fin_generator three))))
      (Sum (Id (USym (cyclic_group_fin three)) h (usym_unit (cyclic_group_fin three)))
           (Id (USym (cyclic_group_fin three)) h (usym_mul (cyclic_group_fin three) (cyclic_fin_generator three) (cyclic_fin_generator three)))
        → KernelGsetFixes (cyclic_group_fin three) sign_sigma_two ex_f2 h)
  ≔ stabilizer_iff_of_kernel_iff (cyclic_group_fin three) sign_sigma_two ex_f2 h
      (Sum (Id (USym (cyclic_group_fin three)) h (usym_unit (cyclic_group_fin three)))
           (Id (USym (cyclic_group_fin three)) h (usym_mul (cyclic_group_fin three) (cyclic_fin_generator three) (cyclic_fin_generator three))))
      (foc_sgnprj_kernel_iff h)

def xr_R4_stabilizer_iff (C : CircleSignature) (g : USym (circle_group C))
  : Product (KernelGsetFixes (circle_group C) (symmetric_group foc_four) (xr_R4 C) g → CircleLoopMultiple C (pos. foc_four) g)
      (CircleLoopMultiple C (pos. foc_four) g → KernelGsetFixes (circle_group C) (symmetric_group foc_four) (xr_R4 C) g)
  ≔ stabilizer_iff_of_kernel_iff (circle_group C) (symmetric_group foc_four) (xr_R4 C) g (CircleLoopMultiple C (pos. foc_four) g)
      (xr_R4_kernel_iff C g)

def xr_sgn_stabilizer_iff (h : USym (symmetric_group foc_four))
  : Product
      (KernelGsetFixes (symmetric_group foc_four) sign_sigma_two (sign_hom foc_four) h
        → Id Sign (permutation_sign_at foc_four (standard_shape foc_four) (symmetric_group_usym_equiv foc_four .map h)) plus.)
      (Id Sign (permutation_sign_at foc_four (standard_shape foc_four) (symmetric_group_usym_equiv foc_four .map h)) plus.
        → KernelGsetFixes (symmetric_group foc_four) sign_sigma_two (sign_hom foc_four) h)
  ≔ stabilizer_iff_of_kernel_iff (symmetric_group foc_four) sign_sigma_two (sign_hom foc_four) h
      (Id Sign (permutation_sign_at foc_four (standard_shape foc_four) (symmetric_group_usym_equiv foc_four .map h)) plus.)
      (xr_sgn_kernel_iff h)

def xr_sR4_stabilizer_iff (C : CircleSignature) (g : USym (circle_group C))
  : Product (KernelGsetFixes (circle_group C) sign_sigma_two (xr_sR4 C) g → CircleLoopMultiple C (pos. two) g)
      (CircleLoopMultiple C (pos. two) g → KernelGsetFixes (circle_group C) sign_sigma_two (xr_sR4 C) g)
  ≔ stabilizer_iff_of_kernel_iff (circle_group C) sign_sigma_two (xr_sR4 C) g (CircleLoopMultiple C (pos. two) g)
      (xr_sR4_kernel_iff C g)
