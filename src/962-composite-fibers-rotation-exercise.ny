export "961-composite-fibers-mod-example"
export "127-symmetries-of-circle"

{` Chapter 9 (subgroups.tex 764-776), xca:fibersofcomposites: the same
   analysis for Z --R_4--> Σ_4 --Bsgn--> Σ_2 (R_4 = power_finset_hom of
   module 418, R_4(loop) = ρ = (0 1 2 3)). Here the fibers are no longer
   all connected: USym(R_4) is not surjective (its image commutes with ρ,
   Z being abelian, while the transposition (0 1) does not), so by
   lem:epi-surj Bsgn∘… R_4 does not have connected fibers (the step from
   non-surjectivity to non-connectedness is lem:epi-surj, module 930, not
   imported). Checked with -s (as module 961). `}

def xr_R4 (C : CircleSignature) : GroupHom (circle_group C) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) ≔ power_finset_hom C (suc. (suc. (suc. zero.)))

def xr_sR4 (C : CircleSignature) : GroupHom (circle_group C) sign_sigma_two
  ≔ group_hom_compose (circle_group C) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) sign_sigma_two (xr_R4 C) (sign_hom (suc. (suc. (suc. (suc. zero.)))))

def xr_R4_pow (C : CircleSignature) (n : Nat)
  : Id (USym (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (usym_hom (circle_group C) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C) (usym_power (circle_group C) (C .loop) n)) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) n)
  ≔ concat (USym (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (usym_hom (circle_group C) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C) (usym_power (circle_group C) (C .loop) n))
      (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (usym_hom (circle_group C) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C) (C .loop)) n) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) n)
      (usym_hom_power (circle_group C) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C) (C .loop) n)
      (refl ((g ↦ usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) g n) : USym (symmetric_group (suc. (suc. (suc. (suc. zero.))))) → USym (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (power_finset_loop C (suc. (suc. (suc. zero.)))))

{` ρ^4 = e, ρ^2 ≠ e, ρ ≠ e in Σ_4. `}
def xr_rho4_unit : Id (USym (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (suc. (suc. (suc. (suc. zero.))))) (usym_unit (symmetric_group (suc. (suc. (suc. (suc. zero.))))))
  ≔ permutation_symmetries_ext (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (suc. (suc. (suc. (suc. zero.))))) (usym_unit (symmetric_group (suc. (suc. (suc. (suc. zero.))))))
      (x ↦ concat (Fin (suc. (suc. (suc. (suc. zero.))))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (suc. (suc. (suc. (suc. zero.))))) x) x (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_unit (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) x)
        (concat (Fin (suc. (suc. (suc. (suc. zero.))))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (suc. (suc. (suc. (suc. zero.))))) x) (ch9w2_iterate (Fin (suc. (suc. (suc. (suc. zero.))))) (finite_fin_successor (suc. (suc. (suc. zero.))) .map) (suc. (suc. (suc. (suc. zero.)))) x) x
          (ex_rho_pow_action (suc. (suc. (suc. (suc. zero.)))) x) (ex_succ4_identity x))
        (inverse (Fin (suc. (suc. (suc. (suc. zero.))))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_unit (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) x) x (permutation_action_unit (standard_set (suc. (suc. (suc. (suc. zero.))))) x)))

def xr_rho_pow_not_unit (n : Nat) (hn : Id (Fin (suc. (suc. (suc. (suc. zero.))))) (ch9w2_iterate (Fin (suc. (suc. (suc. (suc. zero.))))) (finite_fin_successor (suc. (suc. (suc. zero.))) .map) n (inr. star.)) (inr. star.) → Empty)
  (e : Id (USym (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) n) (usym_unit (symmetric_group (suc. (suc. (suc. (suc. zero.))))))) : Empty
  ≔ hn (calc
      ch9w2_iterate (Fin (suc. (suc. (suc. (suc. zero.))))) (finite_fin_successor (suc. (suc. (suc. zero.))) .map) n (inr. star.)
      = permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) n) (inr. star.)
        by inverse (Fin (suc. (suc. (suc. (suc. zero.))))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) n) (inr. star.)) (ch9w2_iterate (Fin (suc. (suc. (suc. (suc. zero.))))) (finite_fin_successor (suc. (suc. (suc. zero.))) .map) n (inr. star.)) (ex_rho_pow_action n (inr. star.))
      = permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_unit (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (inr. star.) by refl ((g ↦ permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) g (inr. star.)) : USym (symmetric_group (suc. (suc. (suc. (suc. zero.))))) → (Fin (suc. (suc. (suc. (suc. zero.)))))) e
      = (inr. star.) by permutation_action_unit (standard_set (suc. (suc. (suc. (suc. zero.))))) (inr. star.) ∎)

{` Ker(R_4): (loop^4)^k ∈, loop^2 ∉, loop ∉. `}
def xr_R4_kernel_loop4k (C : CircleSignature) (k : Nat)
  : InKer (circle_group C) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C) (usym_power (circle_group C) (usym_power (circle_group C) (C .loop) (suc. (suc. (suc. (suc. zero.))))) k)
  ≔ let Z ≔ circle_group C in
    calc
      usym_hom Z (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C) (usym_power Z (usym_power Z (C .loop) (suc. (suc. (suc. (suc. zero.))))) k)
      = usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (usym_hom Z (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C) (usym_power Z (C .loop) (suc. (suc. (suc. (suc. zero.)))))) k
        by usym_hom_power Z (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C) (usym_power Z (C .loop) (suc. (suc. (suc. (suc. zero.))))) k
      = usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (usym_unit (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) k
        by refl ((g ↦ usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) g k) : USym (symmetric_group (suc. (suc. (suc. (suc. zero.))))) → USym (symmetric_group (suc. (suc. (suc. (suc. zero.))))))
             (concat (USym (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (usym_hom Z (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C) (usym_power Z (C .loop) (suc. (suc. (suc. (suc. zero.)))))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (suc. (suc. (suc. (suc. zero.))))) (usym_unit (symmetric_group (suc. (suc. (suc. (suc. zero.))))))
               (xr_R4_pow C (suc. (suc. (suc. (suc. zero.))))) xr_rho4_unit)
      = usym_unit (symmetric_group (suc. (suc. (suc. (suc. zero.))))) by usym_power_unit (symmetric_group (suc. (suc. (suc. (suc. zero.))))) k ∎

def xr_R4_not_kernel_pow (C : CircleSignature) (n : Nat) (hn : Id (Fin (suc. (suc. (suc. (suc. zero.))))) (ch9w2_iterate (Fin (suc. (suc. (suc. (suc. zero.))))) (finite_fin_successor (suc. (suc. (suc. zero.))) .map) n (inr. star.)) (inr. star.) → Empty)
  (e : InKer (circle_group C) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C) (usym_power (circle_group C) (C .loop) n)) : Empty
  ≔ xr_rho_pow_not_unit n hn
      (concat (USym (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) n) (usym_hom (circle_group C) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C) (usym_power (circle_group C) (C .loop) n))
        (usym_unit (symmetric_group (suc. (suc. (suc. (suc. zero.))))))
        (inverse (USym (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (usym_hom (circle_group C) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C) (usym_power (circle_group C) (C .loop) n)) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) n)
          (xr_R4_pow C n)) e)

def xr_R4_not_kernel_loop2 (C : CircleSignature)
  (e : InKer (circle_group C) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C) (usym_power (circle_group C) (C .loop) (suc. (suc. zero.)))) : Empty
  ≔ xr_R4_not_kernel_pow C (suc. (suc. zero.)) (q ↦ transport (Fin (suc. (suc. (suc. (suc. zero.))))) ex_fin4_code (inr. star.) (inl. (inl. (inr. star.))) (inverse (Fin (suc. (suc. (suc. (suc. zero.))))) (inl. (inl. (inr. star.))) (inr. star.) q) star.) e

def xr_R4_not_kernel_loop (C : CircleSignature)
  (e : InKer (circle_group C) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C) (usym_power (circle_group C) (C .loop) (suc. zero.))) : Empty
  ≔ xr_R4_not_kernel_pow C (suc. zero.) (q ↦ transport (Fin (suc. (suc. (suc. (suc. zero.))))) ex_fin4_code (inr. star.) (inl. (inr. star.)) (inverse (Fin (suc. (suc. (suc. (suc. zero.))))) (inl. (inr. star.)) (inr. star.) q) star.) e

{` Ker(sgn) (the even permutations): ρ^2 ∈, ρ ∉, (0 1) ∉. `}
def xr_sgn_pow_sign (n : Nat)
  : Id Sign (sigma_two_sign (usym_hom (symmetric_group (suc. (suc. (suc. (suc. zero.))))) sign_sigma_two (sign_hom (suc. (suc. (suc. (suc. zero.))))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) n))) (sign_power minus. n)
  ≔ concat Sign (sigma_two_sign (usym_hom (symmetric_group (suc. (suc. (suc. (suc. zero.))))) sign_sigma_two (sign_hom (suc. (suc. (suc. (suc. zero.))))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) n)))
      (sigma_two_sign (usym_power sign_sigma_two (usgn (suc. (suc. (suc. (suc. zero.)))) (finite_successor_symmetry (suc. (suc. (suc. zero.))))) n)) (sign_power minus. n)
      (refl sigma_two_sign (usym_hom_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) sign_sigma_two (sign_hom (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) n))
      (concat Sign (sigma_two_sign (usym_power sign_sigma_two (usgn (suc. (suc. (suc. (suc. zero.)))) (finite_successor_symmetry (suc. (suc. (suc. zero.))))) n)) (sign_power (sigma_two_sign (usgn (suc. (suc. (suc. (suc. zero.)))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))))) n)
        (sign_power minus. n) (sigma_two_sign_pow (usgn (suc. (suc. (suc. (suc. zero.)))) (finite_successor_symmetry (suc. (suc. (suc. zero.))))) n)
        (refl ((t ↦ sign_power t n) : Sign → Sign) ex_rho_sign))

def xr_sgn_kernel_rho2 : InKer (symmetric_group (suc. (suc. (suc. (suc. zero.))))) sign_sigma_two (sign_hom (suc. (suc. (suc. (suc. zero.))))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (suc. (suc. zero.)))
  ≔ sigma_two_unit_of_plus (usym_hom (symmetric_group (suc. (suc. (suc. (suc. zero.))))) sign_sigma_two (sign_hom (suc. (suc. (suc. (suc. zero.))))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (suc. (suc. zero.)))) (xr_sgn_pow_sign (suc. (suc. zero.)))

def xr_sgn_not_kernel_rho (e : InKer (symmetric_group (suc. (suc. (suc. (suc. zero.))))) sign_sigma_two (sign_hom (suc. (suc. (suc. (suc. zero.))))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (suc. zero.))) : Empty
  ≔ sigma_two_not_unit_of_minus (usym_hom (symmetric_group (suc. (suc. (suc. (suc. zero.))))) sign_sigma_two (sign_hom (suc. (suc. (suc. (suc. zero.))))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (suc. zero.))) (xr_sgn_pow_sign (suc. zero.)) e

def xr_sgn_not_kernel_swap01 (e : InKer (symmetric_group (suc. (suc. (suc. (suc. zero.))))) sign_sigma_two (sign_hom (suc. (suc. (suc. (suc. zero.))))) (permutation_symmetry (standard_set (suc. (suc. (suc. (suc. zero.))))) (fin_swap01_equiv (suc. (suc. zero.))))) : Empty
  ≔ sigma_two_not_unit_of_minus (usym_hom (symmetric_group (suc. (suc. (suc. (suc. zero.))))) sign_sigma_two (sign_hom (suc. (suc. (suc. (suc. zero.))))) (permutation_symmetry (standard_set (suc. (suc. (suc. (suc. zero.))))) (fin_swap01_equiv (suc. (suc. zero.))))) (usgn_swap01 (suc. (suc. zero.))) e

{` Ker(sgn ∘ R_4): (loop^2)^k ∈, loop ∉. `}
def xr_sR4_pow_sign (C : CircleSignature) (n : Nat)
  : Id Sign (sigma_two_sign (usym_hom (circle_group C) sign_sigma_two (xr_sR4 C) (usym_power (circle_group C) (C .loop) n))) (sign_power minus. n)
  ≔ let Z ≔ circle_group C in
    calc
      sigma_two_sign (usym_hom Z sign_sigma_two (xr_sR4 C) (usym_power Z (C .loop) n))
      = sigma_two_sign (usym_hom (symmetric_group (suc. (suc. (suc. (suc. zero.))))) sign_sigma_two (sign_hom (suc. (suc. (suc. (suc. zero.))))) (usym_hom Z (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C) (usym_power Z (C .loop) n)))
        by refl sigma_two_sign (happly (USym Z) (_ ↦ USym sign_sigma_two) (usym_hom Z sign_sigma_two (xr_sR4 C))
             (x ↦ usym_hom (symmetric_group (suc. (suc. (suc. (suc. zero.))))) sign_sigma_two (sign_hom (suc. (suc. (suc. (suc. zero.))))) (usym_hom Z (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C) x))
             (usym_hom_compose Z (symmetric_group (suc. (suc. (suc. (suc. zero.))))) sign_sigma_two (xr_R4 C) (sign_hom (suc. (suc. (suc. (suc. zero.)))))) (usym_power Z (C .loop) n))
      = sigma_two_sign (usym_hom (symmetric_group (suc. (suc. (suc. (suc. zero.))))) sign_sigma_two (sign_hom (suc. (suc. (suc. (suc. zero.))))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) n))
        by refl ((g ↦ sigma_two_sign (usym_hom (symmetric_group (suc. (suc. (suc. (suc. zero.))))) sign_sigma_two (sign_hom (suc. (suc. (suc. (suc. zero.))))) g)) : USym (symmetric_group (suc. (suc. (suc. (suc. zero.))))) → Sign) (xr_R4_pow C n)
      = sign_power minus. n by xr_sgn_pow_sign n ∎

def xr_sR4_kernel_loop2k (C : CircleSignature) (k : Nat)
  : InKer (circle_group C) sign_sigma_two (xr_sR4 C) (usym_power (circle_group C) (usym_power (circle_group C) (C .loop) (suc. (suc. zero.))) k)
  ≔ let Z ≔ circle_group C in
    calc
      usym_hom Z sign_sigma_two (xr_sR4 C) (usym_power Z (usym_power Z (C .loop) (suc. (suc. zero.))) k)
      = usym_power sign_sigma_two (usym_hom Z sign_sigma_two (xr_sR4 C) (usym_power Z (C .loop) (suc. (suc. zero.)))) k
        by usym_hom_power Z sign_sigma_two (xr_sR4 C) (usym_power Z (C .loop) (suc. (suc. zero.))) k
      = usym_power sign_sigma_two (usym_unit sign_sigma_two) k
        by refl ((g ↦ usym_power sign_sigma_two g k) : USym sign_sigma_two → USym sign_sigma_two)
             (sigma_two_unit_of_plus (usym_hom Z sign_sigma_two (xr_sR4 C) (usym_power Z (C .loop) (suc. (suc. zero.)))) (xr_sR4_pow_sign C (suc. (suc. zero.))))
      = usym_unit sign_sigma_two by usym_power_unit sign_sigma_two k ∎

def xr_sR4_not_kernel_loop (C : CircleSignature)
  (e : InKer (circle_group C) sign_sigma_two (xr_sR4 C) (usym_power (circle_group C) (C .loop) (suc. zero.))) : Empty
  ≔ sigma_two_not_unit_of_minus (usym_hom (circle_group C) sign_sigma_two (xr_sR4 C) (usym_power (circle_group C) (C .loop) (suc. zero.)))
      (xr_sR4_pow_sign C (suc. zero.)) e

{` "Not as general as possible": R_4 is not surjective on symmetries.
   Images of R_4 commute with ρ = R_4(loop), but (0 1)·ρ and ρ·(0 1)
   differ at 0. `}
def xr_R4_image_commutes (C : CircleSignature) (l : USym (circle_group C))
  : Id (USym (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (usym_mul (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (usym_hom (circle_group C) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C) l) (finite_successor_symmetry (suc. (suc. (suc. zero.)))))
      (usym_mul (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (usym_hom (circle_group C) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C) l))
  ≔ let Z ≔ circle_group C in let R ≔ usym_hom Z (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C) in
    calc
      usym_mul (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (R l) (finite_successor_symmetry (suc. (suc. (suc. zero.))))
      = usym_mul (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (R l) (R (C .loop))
        by refl (usym_mul (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (R l)) (inverse (USym (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (R (C .loop)) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (power_finset_loop C (suc. (suc. (suc. zero.)))))
      = R (usym_mul Z l (C .loop)) by inverse (USym (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (R (usym_mul Z l (C .loop))) (usym_mul (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (R l) (R (C .loop)))
          (usym_hom_mul Z (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C) l (C .loop))
      = R (usym_mul Z (C .loop) l) by refl R (circle_loops_commute C (C .loop) l)
      = usym_mul (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (R (C .loop)) (R l) by usym_hom_mul Z (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C) (C .loop) l
      = usym_mul (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (R l) by refl ((g ↦ usym_mul (symmetric_group (suc. (suc. (suc. (suc. zero.))))) g (R l)) : USym (symmetric_group (suc. (suc. (suc. (suc. zero.))))) → USym (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (power_finset_loop C (suc. (suc. (suc. zero.)))) ∎

def xr_swap_rho_noncommuting (e : Id (USym (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (usym_mul (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (permutation_symmetry (standard_set (suc. (suc. (suc. (suc. zero.))))) (fin_swap01_equiv (suc. (suc. zero.)))) (finite_successor_symmetry (suc. (suc. (suc. zero.))))) (usym_mul (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (permutation_symmetry (standard_set (suc. (suc. (suc. (suc. zero.))))) (fin_swap01_equiv (suc. (suc. zero.)))))) : Empty
  ≔ transport (Fin (suc. (suc. (suc. (suc. zero.))))) ex_fin4_code (inr. star.) (inl. (inl. (inr. star.)))
      (calc
        ((inr. star.) : (Fin (suc. (suc. (suc. (suc. zero.)))))) = fin_swap01 (suc. (suc. zero.)) ((finite_fin_successor (suc. (suc. (suc. zero.))) .map) (inr. star.)) by refl ((inr. star.) : (Fin (suc. (suc. (suc. (suc. zero.))))))
        = permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (permutation_symmetry (standard_set (suc. (suc. (suc. (suc. zero.))))) (fin_swap01_equiv (suc. (suc. zero.)))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (inr. star.))
          by inverse (Fin (suc. (suc. (suc. (suc. zero.))))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (permutation_symmetry (standard_set (suc. (suc. (suc. (suc. zero.))))) (fin_swap01_equiv (suc. (suc. zero.)))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (inr. star.))) (fin_swap01 (suc. (suc. zero.)) ((finite_fin_successor (suc. (suc. (suc. zero.))) .map) (inr. star.)))
               (concat (Fin (suc. (suc. (suc. (suc. zero.))))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (permutation_symmetry (standard_set (suc. (suc. (suc. (suc. zero.))))) (fin_swap01_equiv (suc. (suc. zero.)))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (inr. star.))) (fin_swap01 (suc. (suc. zero.)) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (inr. star.)))
                 (fin_swap01 (suc. (suc. zero.)) ((finite_fin_successor (suc. (suc. (suc. zero.))) .map) (inr. star.)))
                 (permutation_symmetry_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (fin_swap01_equiv (suc. (suc. zero.))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (inr. star.)))
                 (refl (fin_swap01 (suc. (suc. zero.))) (permutation_symmetry_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (finite_fin_successor (suc. (suc. (suc. zero.)))) (inr. star.))))
        = permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_mul (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (permutation_symmetry (standard_set (suc. (suc. (suc. (suc. zero.))))) (fin_swap01_equiv (suc. (suc. zero.)))) (finite_successor_symmetry (suc. (suc. (suc. zero.))))) (inr. star.)
          by inverse (Fin (suc. (suc. (suc. (suc. zero.))))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_mul (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (permutation_symmetry (standard_set (suc. (suc. (suc. (suc. zero.))))) (fin_swap01_equiv (suc. (suc. zero.)))) (finite_successor_symmetry (suc. (suc. (suc. zero.))))) (inr. star.)) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (permutation_symmetry (standard_set (suc. (suc. (suc. (suc. zero.))))) (fin_swap01_equiv (suc. (suc. zero.)))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (inr. star.)))
               (permutation_action_mul (standard_set (suc. (suc. (suc. (suc. zero.))))) (permutation_symmetry (standard_set (suc. (suc. (suc. (suc. zero.))))) (fin_swap01_equiv (suc. (suc. zero.)))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (inr. star.))
        = permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_mul (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (permutation_symmetry (standard_set (suc. (suc. (suc. (suc. zero.))))) (fin_swap01_equiv (suc. (suc. zero.))))) (inr. star.) by refl ((g ↦ permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) g (inr. star.)) : USym (symmetric_group (suc. (suc. (suc. (suc. zero.))))) → (Fin (suc. (suc. (suc. (suc. zero.)))))) e
        = permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (permutation_symmetry (standard_set (suc. (suc. (suc. (suc. zero.))))) (fin_swap01_equiv (suc. (suc. zero.)))) (inr. star.)) by permutation_action_mul (standard_set (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (permutation_symmetry (standard_set (suc. (suc. (suc. (suc. zero.))))) (fin_swap01_equiv (suc. (suc. zero.)))) (inr. star.)
        = (finite_fin_successor (suc. (suc. (suc. zero.))) .map) (fin_swap01 (suc. (suc. zero.)) (inr. star.))
          by concat (Fin (suc. (suc. (suc. (suc. zero.))))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (permutation_symmetry (standard_set (suc. (suc. (suc. (suc. zero.))))) (fin_swap01_equiv (suc. (suc. zero.)))) (inr. star.))) ((finite_fin_successor (suc. (suc. (suc. zero.))) .map) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (permutation_symmetry (standard_set (suc. (suc. (suc. (suc. zero.))))) (fin_swap01_equiv (suc. (suc. zero.)))) (inr. star.)))
               ((finite_fin_successor (suc. (suc. (suc. zero.))) .map) (fin_swap01 (suc. (suc. zero.)) (inr. star.)))
               (permutation_symmetry_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (finite_fin_successor (suc. (suc. (suc. zero.)))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (permutation_symmetry (standard_set (suc. (suc. (suc. (suc. zero.))))) (fin_swap01_equiv (suc. (suc. zero.)))) (inr. star.)))
               (refl (finite_fin_successor (suc. (suc. (suc. zero.))) .map) (permutation_symmetry_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (fin_swap01_equiv (suc. (suc. zero.))) (inr. star.)))
        = (inl. (inl. (inr. star.))) by refl ((inl. (inl. (inr. star.))) : (Fin (suc. (suc. (suc. (suc. zero.)))))) ∎)
      star.

def xr_R4_not_usym_surjective (C : CircleSignature)
  (h : Surjective (USym (circle_group C)) (USym (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (usym_hom (circle_group C) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C))) : Empty
  ≔ mere_rec (BookFiber (USym (circle_group C)) (USym (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (usym_hom (circle_group C) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C)) (permutation_symmetry (standard_set (suc. (suc. (suc. (suc. zero.))))) (fin_swap01_equiv (suc. (suc. zero.))))) Empty (e0 e1 ↦ match e0 [])
      (w ↦ xr_swap_rho_noncommuting
        (transport (USym (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (g ↦ Id (USym (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (usym_mul (symmetric_group (suc. (suc. (suc. (suc. zero.))))) g (finite_successor_symmetry (suc. (suc. (suc. zero.))))) (usym_mul (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) g))
          (usym_hom (circle_group C) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C) (w .fst)) (permutation_symmetry (standard_set (suc. (suc. (suc. (suc. zero.))))) (fin_swap01_equiv (suc. (suc. zero.))))
          (inverse (USym (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (permutation_symmetry (standard_set (suc. (suc. (suc. (suc. zero.))))) (fin_swap01_equiv (suc. (suc. zero.)))) (usym_hom (circle_group C) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (xr_R4 C) (w .fst)) (w .snd))
          (xr_R4_image_commutes C (w .fst))))
      (h (permutation_symmetry (standard_set (suc. (suc. (suc. (suc. zero.))))) (fin_swap01_equiv (suc. (suc. zero.)))))
