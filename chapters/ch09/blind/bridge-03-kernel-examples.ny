export "03-kernel-examples"
export "../../../src/962-composite-fibers-rotation-exercise"
export "../../../src/963-integer-matrix-example"
export "../../../src/930-epi-surj-easy"
export "../../../src/954-abstract-kernel"
export "../../../src/456-sign-inversions"

{` Bridges for subgroups.tex exa:fibersofcomposites (687), xca:fibersofcomposites (764) and the 1×1 case of
   the integer-matrix example (1186), blind file 03-kernel-examples: definitions and the easy statements. The
   stabilizer characterizations and F1 are in bridge-03b-stabilizers, coker(R_4) in bridge-03c. `}

{` Definition bridges: the blind homomorphisms are ours by refl. `}
def bridge_def_mod4 (C : CircleSignature) : Id (GroupHom (circle_group C) BlindC4) (blind_mod4 C) (ex_f1 C) ≔ refl (ex_f1 C)

def bridge_def_sgnprj : Id (GroupHom BlindC4 BlindS2) blind_sgnprj ex_f2 ≔ refl ex_f2

def bridge_def_comp4 (C : CircleSignature) : Id (GroupHom (circle_group C) BlindS2) (blind_comp4 C) (ex_f21 C) ≔ refl (ex_f21 C)

def bridge_def_R4 (C : CircleSignature) : Id (GroupHom (circle_group C) BlindS4) (blind_R4 C) (xr_R4 C) ≔ refl (xr_R4 C)

def bridge_def_compR4 (C : CircleSignature) : Id (GroupHom (circle_group C) BlindS2) (blind_compR4 C) (xr_sR4 C) ≔ refl (xr_sR4 C)

def bridge9w_iff_compose (A B C : Type) (e : BlindIff A B) (e' : BlindIff B C) : BlindIff A C
  ≔ (a ↦ e' .fst (e .fst a), c ↦ e .snd (e' .snd c))

{` "g is in the stabilizer" (g · Bf_pt = Bf_pt) is our InKer (kernel_member_iff, module 954). `}
def bridge9w_fixes_inker (G G' : Group) (f : GroupHom G G') (g : USym G)
  : BlindIff (BlindFixesPoint G G' f g) (InKer G G' f g)
  ≔ kernel_member_iff G G' f g

{` A homomorphism whose fiber over the shape is connected has connected fibers (BG' is connected). `}
def bridge9w_connected_fibers_of_shape (G G' : Group) (f : GroupHom G G')
  (c : Connected (BookFiber (BG G .carrier) (BG G' .carrier) (hom_function G G' f) (shape G')))
  : ConnectedFibers (BG G .carrier) (BG G' .carrier) (hom_function G G' f)
  ≔ let A ≔ BG G .carrier in let B ≔ BG G' .carrier in let F ≔ hom_function G G' f in
    w ↦ mere_rec (Id B (shape G') w) (Connected (BookFiber A B F w)) (connected_prop (BookFiber A B F w))
      (p ↦ transport B (v ↦ Connected (BookFiber A B F v)) (shape G') w p c)
      (bg_connected G' .snd (shape G') w)

{` exa:fibersofcomposites, sets paragraph: the fiber projections are injections. `}
def bridge_exa_foc_sets : blind_exa_foc_sets
  ≔ D s0 s1 s2 ↦
    (subtype_embedding (D .X0) (x ↦ Id (D .X1) (D .x1) (D .f1 x)) (x ↦ s1 (D .x1) (D .f1 x)),
     (subtype_embedding (D .X1) (x ↦ Id (D .X2) (D .x2) (D .f2 x)) (x ↦ s2 (D .x2) (D .f2 x)),
      subtype_embedding (D .X0) (x ↦ Id (D .X2) (D .x2) (D .f2 (D .f1 x))) (x ↦ s2 (D .x2) (D .f2 (D .f1 x)))))

{` s = (0 1 2 3) is odd (3 inversions). `}
def bridge_exa_foc_generator_odd : blind_exa_foc_generator_odd
  ≔ let r ≔ finite_fin_successor three in
    calc
      permutation_sign_at blind_four (standard_shape blind_four) r = bool_sign (nat_odd (inversion_count blind_four r))
        by permutation_sign_at_inversions blind_four r
      = bool_sign (nat_odd (inversion_number blind_four r))
        by refl ((k ↦ bool_sign (nat_odd k)) : Nat → Sign) (inversion_count_number blind_four r)
      = bool_sign true. by refl bool_sign ex_rho_inversions_odd
      = minus. by refl (minus. : Sign) ∎

{` The three fibers are connected: mod_4 has connected fibers (module 418); f2 and f2 f1 are surjective on
   symmetries (module 961), hence have connected fibers (lem:epi-surj, module 930). `}
def bridge_exa_foc_fibers_connected : blind_exa_foc_fibers_connected
  ≔ C ↦
    (ex_f1_connected_fibers C (shape BlindC4),
     (gepi_usym_surjective_connected_fibers BlindC4 BlindS2 ex_f2 ex_f2_usym_surjective (shape BlindS2),
      gepi_usym_surjective_connected_fibers (circle_group C) BlindS2 (ex_f21 C) (ex_f21_usym_surjective C) (shape BlindS2)))

{` xca:fibersofcomposites: the fiber of R_4 is not connected (USym R_4 is not surjective, module 962, and connected
   fibers would make it surjective, lem:epi-surj); those of Bsgn and of the composite are. `}
def bridge_xca_foc_R4_fiber_not_connected : blind_xca_foc_R4_fiber_not_connected
  ≔ C c ↦ xr_R4_not_usym_surjective C
      (gepi_connected_fibers_usym_surjective (circle_group C) BlindS4 (xr_R4 C)
        (bridge9w_connected_fibers_of_shape (circle_group C) BlindS4 (xr_R4 C) c))

def bridge_xca_foc_other_fibers_connected : blind_xca_foc_other_fibers_connected
  ≔ C ↦
    (gepi_usym_surjective_connected_fibers BlindS4 BlindS2 blind_sgn4
       (sigma_two_surjective_of_odd BlindS4 blind_sgn4
         (usym_power BlindS4 (finite_successor_symmetry three) (suc. zero.)) (xr_sgn_pow_sign (suc. zero.)))
       (shape BlindS2),
     gepi_usym_surjective_connected_fibers (circle_group C) BlindS2 (xr_sR4 C)
       (sigma_two_surjective_of_odd (circle_group C) (xr_sR4 C)
         (usym_power (circle_group C) (C .loop) (suc. zero.)) (xr_sR4_pow_sign C (suc. zero.)))
       (shape BlindS2))

{` subgroups.tex:1186 for 1×1 matrices (m): the blind deg_m homomorphism is ours (matrix1_hom C n for m = n+1,
   circle_multiplication_hom C 0 for m = 0, module 963/824) by refl. `}
def bridge_def_deg_hom (C : CircleSignature) (n : Nat)
  : Id (GroupHom (circle_group C) (circle_group C)) (blind_deg_hom C (suc. n)) (matrix1_hom C n)
  ≔ refl (matrix1_hom C n)

def bridge9w_suc_ne_zero (n : Nat) (e : Id Nat (suc. n) zero.) : Empty
  ≔ transport Nat ((k ↦ match k [ zero. ↦ Empty | suc. _ ↦ Unit ]) : Nat → Type) (suc. n) zero. e star.

def bridge_linalg_mono_iff_nonzero : blind_linalg_mono_iff_nonzero
  ≔ C m ↦ match m [
    | zero. ↦
      (mono ↦ nz ↦
         circle_multiplication_zero_not_mono C
           (group_monomorphism_mono_equiv (circle_group C) (circle_group C) (blind_deg_hom C zero.) .map mono),
       nz ↦ match nz (refl (zero. : Nat)) [])
    | suc. n ↦ (_ ↦ e ↦ bridge9w_suc_ne_zero n e, _ ↦ matrix1_monomorphism C n) ]

def bridge_linalg_coker_card : blind_linalg_coker_card
  ≔ C n ↦ book_equivalence
      (gset_underlying (circle_group C) (cokernel (circle_group C) (circle_group C) (matrix1_hom C n))) (Fin (suc. n))
      (matrix1_cokernel_card C n)
