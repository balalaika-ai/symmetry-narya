export "419-cyclic-two-and-generated"
export "1010-usym-powers"
export "458-sign-properties"

{` Chapter 9 (subgroups.tex 674-762), exa:fibersofcomposites: the composite
   Z --Bmod_4--> C_4 --Bsgn∘prj--> Σ_2, for an arbitrary circle C (Z ≔
   circle_group C), f1 ≔ mod_hom (module 418), f2 ≔ sgn ∘ prj (prj :
   C_4 → Σ_4 forgets the cycle structure, sign_hom of module 455). C_4 is
   cyclic_group_fin 3 with generator s = (zs, !) and prj(s) = ρ the cyclic
   permutation (0 1 2 3) (forget_hom_generator).

   "The stabilizer of the point of the H-set (sh_H = Bf(-)) picks out g" is
   expressed as InKer f g ≔ (USym f (g) = e) (for the link with the
   stabilizer, i.e. g · Bf_pt = Bf_pt, see kernel_member_iff of module 954).
   Powers g^n are taken for n : Nat (usym_power); loop^(4k) is (loop^4)^k.
   This module is checked with -s (normal runs hit the Meta.Map.find_opt
   cache anomaly on the refl computations). `}

def InKer (G H : Group) (f : GroupHom G H) (g : USym G) : Type ≔ Id (USym H) (usym_hom G H f g) (usym_unit H)

def ch9w2_iterate (A : Type) (f : A → A) (n : Nat) (x : A) : A
  ≔ match n [ zero. ↦ x | suc. n ↦ f (ch9w2_iterate A f n x) ]

{` Signs of powers in Σ_2. `}
def sign_power (s : Sign) (n : Nat) : Sign ≔ match n [ zero. ↦ plus. | suc. n ↦ sign_mul s (sign_power s n) ]

def sigma_two_sign_pow (g : USym sign_sigma_two) (n : Nat)
  : Id Sign (sigma_two_sign (usym_power sign_sigma_two g n)) (sign_power (sigma_two_sign g) n)
  ≔ match n [
  | zero. ↦ sigma_two_sign_unit
  | suc. n ↦ concat Sign (sigma_two_sign (usym_mul sign_sigma_two g (usym_power sign_sigma_two g n)))
      (sign_mul (sigma_two_sign g) (sigma_two_sign (usym_power sign_sigma_two g n)))
      (sign_mul (sigma_two_sign g) (sign_power (sigma_two_sign g) n))
      (sigma_two_sign_mul g (usym_power sign_sigma_two g n))
      (refl (sign_mul (sigma_two_sign g)) (sigma_two_sign_pow g n)) ]

def sigma_two_unit_of_plus (x : USym sign_sigma_two) (e : Id Sign (sigma_two_sign x) plus.)
  : Id (USym sign_sigma_two) x (usym_unit sign_sigma_two)
  ≔ equivalence_injective (USym sign_sigma_two) Sign sigma_two_sign_equiv x (usym_unit sign_sigma_two)
      (concat Sign (sigma_two_sign x) plus. (sigma_two_sign (usym_unit sign_sigma_two)) e
        (inverse Sign (sigma_two_sign (usym_unit sign_sigma_two)) plus. sigma_two_sign_unit))

def sign_minus_not_plus (e : Id Sign minus. plus.) : Empty
  ≔ transport Sign (t ↦ match t [ plus. ↦ Empty | minus. ↦ Unit ]) minus. plus. e star.

def sigma_two_not_unit_of_minus (x : USym sign_sigma_two) (e : Id Sign (sigma_two_sign x) minus.)
  (u : Id (USym sign_sigma_two) x (usym_unit sign_sigma_two)) : Empty
  ≔ sign_minus_not_plus
      (calc (minus. : Sign) = sigma_two_sign x by inverse Sign (sigma_two_sign x) minus. e
        = sigma_two_sign (usym_unit sign_sigma_two) by refl sigma_two_sign u
        = plus. by sigma_two_sign_unit ∎)

{` The cyclic permutation ρ = (0 1 2 3) of Fin 4 is odd: inv(ρ) = 3. `}
def ex_rho_inversions_odd : Id Bool (nat_odd (inversion_number (suc. (suc. (suc. (suc. zero.)))) (finite_fin_successor (suc. (suc. (suc. zero.)))))) true.
  ≔ refl (true. : Bool)

def ex_rho_sign : Id Sign (sigma_two_sign (usgn (suc. (suc. (suc. (suc. zero.)))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))))) minus.
  ≔ concat Sign (sigma_two_sign (usgn (suc. (suc. (suc. (suc. zero.)))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))))) (bool_sign (nat_odd (inversion_number (suc. (suc. (suc. (suc. zero.)))) (finite_fin_successor (suc. (suc. (suc. zero.))))))) minus.
      (usgn_inversion_number (suc. (suc. zero.)) (finite_fin_successor (suc. (suc. (suc. zero.)))))
      (refl bool_sign ex_rho_inversions_odd)

{` The maps. `}
def ex_f1 (C : CircleSignature) : GroupHom (circle_group C) (cyclic_group_fin (suc. (suc. (suc. zero.)))) ≔ mod_hom C (suc. (suc. (suc. zero.)))

def ex_f2 : GroupHom (cyclic_group_fin (suc. (suc. (suc. zero.)))) sign_sigma_two ≔ group_hom_compose (cyclic_group_fin (suc. (suc. (suc. zero.)))) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) sign_sigma_two (cyclic_forget_hom (suc. (suc. (suc. zero.)))) (sign_hom (suc. (suc. (suc. (suc. zero.)))))

def ex_f21 (C : CircleSignature) : GroupHom (circle_group C) sign_sigma_two
  ≔ group_hom_compose (circle_group C) (cyclic_group_fin (suc. (suc. (suc. zero.)))) sign_sigma_two (ex_f1 C) ex_f2

def ex_f2_usym (g : USym (cyclic_group_fin (suc. (suc. (suc. zero.))))) : Id (USym sign_sigma_two) (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) sign_sigma_two ex_f2 g) (usgn (suc. (suc. (suc. (suc. zero.)))) (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (cyclic_forget_hom (suc. (suc. (suc. zero.)))) g))
  ≔ happly (USym (cyclic_group_fin (suc. (suc. (suc. zero.))))) (_ ↦ USym sign_sigma_two) (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) sign_sigma_two ex_f2)
      (x ↦ usym_hom (symmetric_group (suc. (suc. (suc. (suc. zero.))))) sign_sigma_two (sign_hom (suc. (suc. (suc. (suc. zero.))))) (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (cyclic_forget_hom (suc. (suc. (suc. zero.)))) x)) (usym_hom_compose (cyclic_group_fin (suc. (suc. (suc. zero.)))) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) sign_sigma_two (cyclic_forget_hom (suc. (suc. (suc. zero.)))) (sign_hom (suc. (suc. (suc. (suc. zero.)))))) g

def ex_f21_usym (C : CircleSignature) (g : USym (circle_group C))
  : Id (USym sign_sigma_two) (usym_hom (circle_group C) sign_sigma_two (ex_f21 C) g)
      (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) sign_sigma_two ex_f2 (usym_hom (circle_group C) (cyclic_group_fin (suc. (suc. (suc. zero.)))) (ex_f1 C) g))
  ≔ happly (USym (circle_group C)) (_ ↦ USym sign_sigma_two) (usym_hom (circle_group C) sign_sigma_two (ex_f21 C))
      (x ↦ usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) sign_sigma_two ex_f2 (usym_hom (circle_group C) (cyclic_group_fin (suc. (suc. (suc. zero.)))) (ex_f1 C) x))
      (usym_hom_compose (circle_group C) (cyclic_group_fin (suc. (suc. (suc. zero.)))) sign_sigma_two (ex_f1 C) ex_f2) g

{` f1 sends loop^n to s^n; prj sends s^n to ρ^n, which acts as succ^n. `}
def ex_f1_pow (C : CircleSignature) (n : Nat)
  : Id (USym (cyclic_group_fin (suc. (suc. (suc. zero.))))) (usym_hom (circle_group C) (cyclic_group_fin (suc. (suc. (suc. zero.)))) (ex_f1 C) (usym_power (circle_group C) (C .loop) n)) (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) n)
  ≔ concat (USym (cyclic_group_fin (suc. (suc. (suc. zero.))))) (usym_hom (circle_group C) (cyclic_group_fin (suc. (suc. (suc. zero.)))) (ex_f1 C) (usym_power (circle_group C) (C .loop) n))
      (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (usym_hom (circle_group C) (cyclic_group_fin (suc. (suc. (suc. zero.)))) (ex_f1 C) (C .loop)) n) (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) n)
      (usym_hom_power (circle_group C) (cyclic_group_fin (suc. (suc. (suc. zero.)))) (ex_f1 C) (C .loop) n)
      (refl ((g ↦ usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) g n) : USym (cyclic_group_fin (suc. (suc. (suc. zero.)))) → USym (cyclic_group_fin (suc. (suc. (suc. zero.))))) (mod_hom_loop C (suc. (suc. (suc. zero.)))))

def ex_prj_pow (n : Nat) : Id (USym (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (cyclic_forget_hom (suc. (suc. (suc. zero.)))) (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) n)) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) n)
  ≔ concat (USym (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (cyclic_forget_hom (suc. (suc. (suc. zero.)))) (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) n)) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (cyclic_forget_hom (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.))))) n)
      (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) n)
      (usym_hom_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (cyclic_forget_hom (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) n)
      (refl ((g ↦ usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) g n) : USym (symmetric_group (suc. (suc. (suc. (suc. zero.))))) → USym (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (forget_hom_generator (suc. (suc. (suc. zero.)))))

def ex_rho_pow_action (n : Nat) (x : (Fin (suc. (suc. (suc. (suc. zero.))))))
  : Id (Fin (suc. (suc. (suc. (suc. zero.))))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) n) x) (ch9w2_iterate (Fin (suc. (suc. (suc. (suc. zero.))))) (finite_fin_successor (suc. (suc. (suc. zero.))) .map) n x)
  ≔ match n [
  | zero. ↦ permutation_action_unit (standard_set (suc. (suc. (suc. (suc. zero.))))) x
  | suc. n ↦ concat (Fin (suc. (suc. (suc. (suc. zero.))))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_mul (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) n)) x)
      (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) n) x))
      ((finite_fin_successor (suc. (suc. (suc. zero.))) .map) (ch9w2_iterate (Fin (suc. (suc. (suc. (suc. zero.))))) (finite_fin_successor (suc. (suc. (suc. zero.))) .map) n x))
      (permutation_action_mul (standard_set (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) n) x)
      (concat (Fin (suc. (suc. (suc. (suc. zero.))))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) n) x))
        ((finite_fin_successor (suc. (suc. (suc. zero.))) .map) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) n) x))
        ((finite_fin_successor (suc. (suc. (suc. zero.))) .map) (ch9w2_iterate (Fin (suc. (suc. (suc. (suc. zero.))))) (finite_fin_successor (suc. (suc. (suc. zero.))) .map) n x))
        (permutation_symmetry_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (finite_fin_successor (suc. (suc. (suc. zero.)))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) n) x))
        (refl (finite_fin_successor (suc. (suc. (suc. zero.))) .map) (ex_rho_pow_action n x))) ]

def ex_prj_pow_action (n : Nat) (x : (Fin (suc. (suc. (suc. (suc. zero.))))))
  : Id (Fin (suc. (suc. (suc. (suc. zero.))))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (cyclic_forget_hom (suc. (suc. (suc. zero.)))) (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) n)) x) (ch9w2_iterate (Fin (suc. (suc. (suc. (suc. zero.))))) (finite_fin_successor (suc. (suc. (suc. zero.))) .map) n x)
  ≔ concat (Fin (suc. (suc. (suc. (suc. zero.))))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (cyclic_forget_hom (suc. (suc. (suc. zero.)))) (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) n)) x)
      (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) n) x) (ch9w2_iterate (Fin (suc. (suc. (suc. (suc. zero.))))) (finite_fin_successor (suc. (suc. (suc. zero.))) .map) n x)
      (refl ((g ↦ permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) g x) : USym (symmetric_group (suc. (suc. (suc. (suc. zero.))))) → (Fin (suc. (suc. (suc. (suc. zero.)))))) (ex_prj_pow n)) (ex_rho_pow_action n x)

{` The book: s^2 = (0 1 2 3)^2 = (0 2)(1 3). `}
def ex_s2_action_0 : Id (Fin (suc. (suc. (suc. (suc. zero.))))) (ch9w2_iterate (Fin (suc. (suc. (suc. (suc. zero.))))) (finite_fin_successor (suc. (suc. (suc. zero.))) .map) (suc. (suc. zero.)) (inr. star.)) (inl. (inl. (inr. star.))) ≔ refl ((inl. (inl. (inr. star.))) : (Fin (suc. (suc. (suc. (suc. zero.))))))
def ex_s2_action_1 : Id (Fin (suc. (suc. (suc. (suc. zero.))))) (ch9w2_iterate (Fin (suc. (suc. (suc. (suc. zero.))))) (finite_fin_successor (suc. (suc. (suc. zero.))) .map) (suc. (suc. zero.)) (inl. (inr. star.))) (inl. (inl. (inl. (inr. star.)))) ≔ refl ((inl. (inl. (inl. (inr. star.)))) : (Fin (suc. (suc. (suc. (suc. zero.))))))
def ex_s2_action_2 : Id (Fin (suc. (suc. (suc. (suc. zero.))))) (ch9w2_iterate (Fin (suc. (suc. (suc. (suc. zero.))))) (finite_fin_successor (suc. (suc. (suc. zero.))) .map) (suc. (suc. zero.)) (inl. (inl. (inr. star.)))) (inr. star.) ≔ refl ((inr. star.) : (Fin (suc. (suc. (suc. (suc. zero.))))))
def ex_s2_action_3 : Id (Fin (suc. (suc. (suc. (suc. zero.))))) (ch9w2_iterate (Fin (suc. (suc. (suc. (suc. zero.))))) (finite_fin_successor (suc. (suc. (suc. zero.))) .map) (suc. (suc. zero.)) (inl. (inl. (inl. (inr. star.))))) (inl. (inr. star.)) ≔ refl ((inl. (inr. star.)) : (Fin (suc. (suc. (suc. (suc. zero.))))))

{` s^4 = e in C_4, while s ≠ e and s^2 ≠ e. `}
def ex_succ4_identity (x : (Fin (suc. (suc. (suc. (suc. zero.)))))) : Id (Fin (suc. (suc. (suc. (suc. zero.))))) (ch9w2_iterate (Fin (suc. (suc. (suc. (suc. zero.))))) (finite_fin_successor (suc. (suc. (suc. zero.))) .map) (suc. (suc. (suc. (suc. zero.)))) x) x
  ≔ match x [
  | inr. u ↦ match u [ star. ↦ refl ((inr. star.) : (Fin (suc. (suc. (suc. (suc. zero.)))))) ]
  | inl. y ↦ match y [
    | inr. u ↦ match u [ star. ↦ refl ((inl. (inr. star.)) : (Fin (suc. (suc. (suc. (suc. zero.)))))) ]
    | inl. z ↦ match z [
      | inr. u ↦ match u [ star. ↦ refl ((inl. (inl. (inr. star.))) : (Fin (suc. (suc. (suc. (suc. zero.)))))) ]
      | inl. w ↦ match w [
        | inr. u ↦ match u [ star. ↦ refl ((inl. (inl. (inl. (inr. star.)))) : (Fin (suc. (suc. (suc. (suc. zero.)))))) ]
        | inl. v ↦ match v [] ] ] ] ]

def ex_s4_unit : Id (USym (cyclic_group_fin (suc. (suc. (suc. zero.))))) (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) (suc. (suc. (suc. (suc. zero.))))) (usym_unit (cyclic_group_fin (suc. (suc. (suc. zero.)))))
  ≔ forget_hom_injective (suc. (suc. (suc. zero.))) (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) (suc. (suc. (suc. (suc. zero.))))) (usym_unit (cyclic_group_fin (suc. (suc. (suc. zero.)))))
      (permutation_symmetries_ext (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (cyclic_forget_hom (suc. (suc. (suc. zero.)))) (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) (suc. (suc. (suc. (suc. zero.)))))) (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (cyclic_forget_hom (suc. (suc. (suc. zero.)))) (usym_unit (cyclic_group_fin (suc. (suc. (suc. zero.))))))
        (x ↦ calc
          permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (cyclic_forget_hom (suc. (suc. (suc. zero.)))) (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) (suc. (suc. (suc. (suc. zero.)))))) x
          = ch9w2_iterate (Fin (suc. (suc. (suc. (suc. zero.))))) (finite_fin_successor (suc. (suc. (suc. zero.))) .map) (suc. (suc. (suc. (suc. zero.)))) x by ex_prj_pow_action (suc. (suc. (suc. (suc. zero.)))) x
          = x by ex_succ4_identity x
          = permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_unit (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) x by inverse (Fin (suc. (suc. (suc. (suc. zero.))))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_unit (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) x) x (permutation_action_unit (standard_set (suc. (suc. (suc. (suc. zero.))))) x)
          = permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (cyclic_forget_hom (suc. (suc. (suc. zero.)))) (usym_unit (cyclic_group_fin (suc. (suc. (suc. zero.)))))) x
            by refl ((g ↦ permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) g x) : USym (symmetric_group (suc. (suc. (suc. (suc. zero.))))) → (Fin (suc. (suc. (suc. (suc. zero.))))))
                 (inverse (USym (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (cyclic_forget_hom (suc. (suc. (suc. zero.)))) (usym_unit (cyclic_group_fin (suc. (suc. (suc. zero.)))))) (usym_unit (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (usym_hom_unit (cyclic_group_fin (suc. (suc. (suc. zero.)))) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (cyclic_forget_hom (suc. (suc. (suc. zero.)))))) ∎))

def ex_fin4_code (x : (Fin (suc. (suc. (suc. (suc. zero.)))))) : Type ≔ match x [ inr. _ ↦ Unit | inl. _ ↦ Empty ]

def ex_s_pow_not_unit (n : Nat) (hn : Id (Fin (suc. (suc. (suc. (suc. zero.))))) (ch9w2_iterate (Fin (suc. (suc. (suc. (suc. zero.))))) (finite_fin_successor (suc. (suc. (suc. zero.))) .map) n (inr. star.)) (inr. star.) → Empty)
  (e : Id (USym (cyclic_group_fin (suc. (suc. (suc. zero.))))) (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) n) (usym_unit (cyclic_group_fin (suc. (suc. (suc. zero.)))))) : Empty
  ≔ hn (calc
      ch9w2_iterate (Fin (suc. (suc. (suc. (suc. zero.))))) (finite_fin_successor (suc. (suc. (suc. zero.))) .map) n (inr. star.)
      = permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (cyclic_forget_hom (suc. (suc. (suc. zero.)))) (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) n)) (inr. star.)
        by inverse (Fin (suc. (suc. (suc. (suc. zero.))))) (permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (cyclic_forget_hom (suc. (suc. (suc. zero.)))) (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) n)) (inr. star.)) (ch9w2_iterate (Fin (suc. (suc. (suc. (suc. zero.))))) (finite_fin_successor (suc. (suc. (suc. zero.))) .map) n (inr. star.))
             (ex_prj_pow_action n (inr. star.))
      = permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (cyclic_forget_hom (suc. (suc. (suc. zero.)))) (usym_unit (cyclic_group_fin (suc. (suc. (suc. zero.)))))) (inr. star.)
        by refl ((g ↦ permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (cyclic_forget_hom (suc. (suc. (suc. zero.)))) g) (inr. star.)) : USym (cyclic_group_fin (suc. (suc. (suc. zero.)))) → (Fin (suc. (suc. (suc. (suc. zero.)))))) e
      = permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) (usym_unit (symmetric_group (suc. (suc. (suc. (suc. zero.)))))) (inr. star.)
        by refl ((g ↦ permutation_action (standard_set (suc. (suc. (suc. (suc. zero.))))) g (inr. star.)) : USym (symmetric_group (suc. (suc. (suc. (suc. zero.))))) → (Fin (suc. (suc. (suc. (suc. zero.)))))) (usym_hom_unit (cyclic_group_fin (suc. (suc. (suc. zero.)))) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (cyclic_forget_hom (suc. (suc. (suc. zero.)))))
      = (inr. star.) by permutation_action_unit (standard_set (suc. (suc. (suc. (suc. zero.))))) (inr. star.) ∎)

def ex_s2_not_unit (e : Id (USym (cyclic_group_fin (suc. (suc. (suc. zero.))))) (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) (suc. (suc. zero.))) (usym_unit (cyclic_group_fin (suc. (suc. (suc. zero.)))))) : Empty
  ≔ ex_s_pow_not_unit (suc. (suc. zero.)) (q ↦ transport (Fin (suc. (suc. (suc. (suc. zero.))))) ex_fin4_code (inr. star.) (inl. (inl. (inr. star.))) (inverse (Fin (suc. (suc. (suc. (suc. zero.))))) (inl. (inl. (inr. star.))) (inr. star.) q) star.) e

def ex_s1_not_unit (e : Id (USym (cyclic_group_fin (suc. (suc. (suc. zero.))))) (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) (suc. zero.)) (usym_unit (cyclic_group_fin (suc. (suc. (suc. zero.)))))) : Empty
  ≔ ex_s_pow_not_unit (suc. zero.) (q ↦ transport (Fin (suc. (suc. (suc. (suc. zero.))))) ex_fin4_code (inr. star.) (inl. (inr. star.)) (inverse (Fin (suc. (suc. (suc. (suc. zero.))))) (inl. (inr. star.)) (inr. star.) q) star.) e

{` Ker(f1): the stabilizer of refl_(4,zs) picks out loop^(4k): loop^(4k) ∈ Ker(f1)
   for every k, loop^2 ∉ Ker(f1) and loop ∉ Ker(f1). `}
def ex_f1_kernel_loop4k (C : CircleSignature) (k : Nat)
  : InKer (circle_group C) (cyclic_group_fin (suc. (suc. (suc. zero.)))) (ex_f1 C) (usym_power (circle_group C) (usym_power (circle_group C) (C .loop) (suc. (suc. (suc. (suc. zero.))))) k)
  ≔ let Z ≔ circle_group C in
    calc
      usym_hom Z (cyclic_group_fin (suc. (suc. (suc. zero.)))) (ex_f1 C) (usym_power Z (usym_power Z (C .loop) (suc. (suc. (suc. (suc. zero.))))) k)
      = usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (usym_hom Z (cyclic_group_fin (suc. (suc. (suc. zero.)))) (ex_f1 C) (usym_power Z (C .loop) (suc. (suc. (suc. (suc. zero.)))))) k
        by usym_hom_power Z (cyclic_group_fin (suc. (suc. (suc. zero.)))) (ex_f1 C) (usym_power Z (C .loop) (suc. (suc. (suc. (suc. zero.))))) k
      = usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (usym_unit (cyclic_group_fin (suc. (suc. (suc. zero.))))) k
        by refl ((g ↦ usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) g k) : USym (cyclic_group_fin (suc. (suc. (suc. zero.)))) → USym (cyclic_group_fin (suc. (suc. (suc. zero.)))))
             (concat (USym (cyclic_group_fin (suc. (suc. (suc. zero.))))) (usym_hom Z (cyclic_group_fin (suc. (suc. (suc. zero.)))) (ex_f1 C) (usym_power Z (C .loop) (suc. (suc. (suc. (suc. zero.)))))) (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) (suc. (suc. (suc. (suc. zero.))))) (usym_unit (cyclic_group_fin (suc. (suc. (suc. zero.)))))
               (ex_f1_pow C (suc. (suc. (suc. (suc. zero.))))) ex_s4_unit)
      = usym_unit (cyclic_group_fin (suc. (suc. (suc. zero.)))) by usym_power_unit (cyclic_group_fin (suc. (suc. (suc. zero.)))) k ∎

def ex_f1_not_kernel_loop2 (C : CircleSignature)
  (e : InKer (circle_group C) (cyclic_group_fin (suc. (suc. (suc. zero.)))) (ex_f1 C) (usym_power (circle_group C) (C .loop) (suc. (suc. zero.)))) : Empty
  ≔ ex_s2_not_unit (concat (USym (cyclic_group_fin (suc. (suc. (suc. zero.))))) (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) (suc. (suc. zero.)))
      (usym_hom (circle_group C) (cyclic_group_fin (suc. (suc. (suc. zero.)))) (ex_f1 C) (usym_power (circle_group C) (C .loop) (suc. (suc. zero.)))) (usym_unit (cyclic_group_fin (suc. (suc. (suc. zero.)))))
      (inverse (USym (cyclic_group_fin (suc. (suc. (suc. zero.))))) (usym_hom (circle_group C) (cyclic_group_fin (suc. (suc. (suc. zero.)))) (ex_f1 C) (usym_power (circle_group C) (C .loop) (suc. (suc. zero.)))) (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) (suc. (suc. zero.)))
        (ex_f1_pow C (suc. (suc. zero.)))) e)

def ex_f1_not_kernel_loop (C : CircleSignature)
  (e : InKer (circle_group C) (cyclic_group_fin (suc. (suc. (suc. zero.)))) (ex_f1 C) (usym_power (circle_group C) (C .loop) (suc. zero.))) : Empty
  ≔ ex_s1_not_unit (concat (USym (cyclic_group_fin (suc. (suc. (suc. zero.))))) (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) (suc. zero.))
      (usym_hom (circle_group C) (cyclic_group_fin (suc. (suc. (suc. zero.)))) (ex_f1 C) (usym_power (circle_group C) (C .loop) (suc. zero.))) (usym_unit (cyclic_group_fin (suc. (suc. (suc. zero.)))))
      (inverse (USym (cyclic_group_fin (suc. (suc. (suc. zero.))))) (usym_hom (circle_group C) (cyclic_group_fin (suc. (suc. (suc. zero.)))) (ex_f1 C) (usym_power (circle_group C) (C .loop) (suc. zero.))) (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) (suc. zero.))
        (ex_f1_pow C (suc. zero.))) e)

{` Ker(f2): the symmetries s^k of (4, zs) with k = 0, 2, the even ones; s and
   s^3 are odd. The sign of f2(s^n) is (−1)^n. `}
def ex_f2_pow_sign (n : Nat)
  : Id Sign (sigma_two_sign (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) sign_sigma_two ex_f2 (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) n))) (sign_power minus. n)
  ≔ calc
      sigma_two_sign (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) sign_sigma_two ex_f2 (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) n))
      = sigma_two_sign (usgn (suc. (suc. (suc. (suc. zero.)))) (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (cyclic_forget_hom (suc. (suc. (suc. zero.)))) (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) n))) by refl sigma_two_sign (ex_f2_usym (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) n))
      = sigma_two_sign (usgn (suc. (suc. (suc. (suc. zero.)))) (usym_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) n)) by refl ((g ↦ sigma_two_sign (usgn (suc. (suc. (suc. (suc. zero.)))) g)) : USym (symmetric_group (suc. (suc. (suc. (suc. zero.))))) → Sign) (ex_prj_pow n)
      = sigma_two_sign (usym_power sign_sigma_two (usgn (suc. (suc. (suc. (suc. zero.)))) (finite_successor_symmetry (suc. (suc. (suc. zero.))))) n) by refl sigma_two_sign (usym_hom_power (symmetric_group (suc. (suc. (suc. (suc. zero.))))) sign_sigma_two (sign_hom (suc. (suc. (suc. (suc. zero.))))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))) n)
      = sign_power (sigma_two_sign (usgn (suc. (suc. (suc. (suc. zero.)))) (finite_successor_symmetry (suc. (suc. (suc. zero.)))))) n by sigma_two_sign_pow (usgn (suc. (suc. (suc. (suc. zero.)))) (finite_successor_symmetry (suc. (suc. (suc. zero.))))) n
      = sign_power minus. n by refl ((t ↦ sign_power t n) : Sign → Sign) ex_rho_sign ∎

def ex_f2_kernel_s2 : InKer (cyclic_group_fin (suc. (suc. (suc. zero.)))) sign_sigma_two ex_f2 (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) (suc. (suc. zero.)))
  ≔ sigma_two_unit_of_plus (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) sign_sigma_two ex_f2 (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) (suc. (suc. zero.)))) (ex_f2_pow_sign (suc. (suc. zero.)))

def ex_f2_kernel_s0 : InKer (cyclic_group_fin (suc. (suc. (suc. zero.)))) sign_sigma_two ex_f2 (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) zero.)
  ≔ usym_hom_unit (cyclic_group_fin (suc. (suc. (suc. zero.)))) sign_sigma_two ex_f2

def ex_f2_not_kernel_s1 (e : InKer (cyclic_group_fin (suc. (suc. (suc. zero.)))) sign_sigma_two ex_f2 (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) (suc. zero.))) : Empty
  ≔ sigma_two_not_unit_of_minus (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) sign_sigma_two ex_f2 (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) (suc. zero.))) (ex_f2_pow_sign (suc. zero.)) e

def ex_f2_not_kernel_s3 (e : InKer (cyclic_group_fin (suc. (suc. (suc. zero.)))) sign_sigma_two ex_f2 (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) (suc. (suc. (suc. zero.))))) : Empty
  ≔ sigma_two_not_unit_of_minus (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) sign_sigma_two ex_f2 (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) (suc. (suc. (suc. zero.))))) (ex_f2_pow_sign (suc. (suc. (suc. zero.)))) e

{` Ker(f2 f1): loop^(2k) ∈ Ker(f2 f1) for every k, and loop ∉ Ker(f2 f1). `}
def ex_f21_pow_sign (C : CircleSignature) (n : Nat)
  : Id Sign (sigma_two_sign (usym_hom (circle_group C) sign_sigma_two (ex_f21 C) (usym_power (circle_group C) (C .loop) n))) (sign_power minus. n)
  ≔ let Z ≔ circle_group C in
    calc
      sigma_two_sign (usym_hom Z sign_sigma_two (ex_f21 C) (usym_power Z (C .loop) n))
      = sigma_two_sign (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) sign_sigma_two ex_f2 (usym_hom Z (cyclic_group_fin (suc. (suc. (suc. zero.)))) (ex_f1 C) (usym_power Z (C .loop) n)))
        by refl sigma_two_sign (ex_f21_usym C (usym_power Z (C .loop) n))
      = sigma_two_sign (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) sign_sigma_two ex_f2 (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) n))
        by refl ((g ↦ sigma_two_sign (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) sign_sigma_two ex_f2 g)) : USym (cyclic_group_fin (suc. (suc. (suc. zero.)))) → Sign) (ex_f1_pow C n)
      = sign_power minus. n by ex_f2_pow_sign n ∎

def ex_f21_kernel_loop2k (C : CircleSignature) (k : Nat)
  : InKer (circle_group C) sign_sigma_two (ex_f21 C) (usym_power (circle_group C) (usym_power (circle_group C) (C .loop) (suc. (suc. zero.))) k)
  ≔ let Z ≔ circle_group C in
    calc
      usym_hom Z sign_sigma_two (ex_f21 C) (usym_power Z (usym_power Z (C .loop) (suc. (suc. zero.))) k)
      = usym_power sign_sigma_two (usym_hom Z sign_sigma_two (ex_f21 C) (usym_power Z (C .loop) (suc. (suc. zero.)))) k
        by usym_hom_power Z sign_sigma_two (ex_f21 C) (usym_power Z (C .loop) (suc. (suc. zero.))) k
      = usym_power sign_sigma_two (usym_unit sign_sigma_two) k
        by refl ((g ↦ usym_power sign_sigma_two g k) : USym sign_sigma_two → USym sign_sigma_two)
             (sigma_two_unit_of_plus (usym_hom Z sign_sigma_two (ex_f21 C) (usym_power Z (C .loop) (suc. (suc. zero.)))) (ex_f21_pow_sign C (suc. (suc. zero.))))
      = usym_unit sign_sigma_two by usym_power_unit sign_sigma_two k ∎

def ex_f21_not_kernel_loop (C : CircleSignature)
  (e : InKer (circle_group C) sign_sigma_two (ex_f21 C) (usym_power (circle_group C) (C .loop) (suc. zero.))) : Empty
  ≔ sigma_two_not_unit_of_minus (usym_hom (circle_group C) sign_sigma_two (ex_f21 C) (usym_power (circle_group C) (C .loop) (suc. zero.)))
      (ex_f21_pow_sign C (suc. zero.)) e

{` "These fibers ... happen to be connected": the fibers of Bmod_4 are
   connected (module 418). `}
def ex_f1_connected_fibers (C : CircleSignature)
  : ConnectedFibers (C .carrier) (BG (cyclic_group_fin (suc. (suc. (suc. zero.)))) .carrier) (hom_function (circle_group C) (cyclic_group_fin (suc. (suc. (suc. zero.)))) (ex_f1 C))
  ≔ mod_connected_fibers C (suc. (suc. (suc. zero.)))

{` f2 and f2 f1 are surjective on symmetries (hence, by lem:epi-surj, have
   connected fibers): every symmetry of Σ_2 is e or the image of s (resp. loop). `}
def sign_cases (t : Sign) : Sum (Id Sign t plus.) (Id Sign t minus.)
  ≔ match t [ plus. ↦ inl. (refl (plus. : Sign)) | minus. ↦ inr. (refl (minus. : Sign)) ]

def sigma_two_same_sign (x y : USym sign_sigma_two) (e : Id Sign (sigma_two_sign x) (sigma_two_sign y))
  : Id (USym sign_sigma_two) x y
  ≔ equivalence_injective (USym sign_sigma_two) Sign sigma_two_sign_equiv x y e

{` A homomorphism into Σ_2 hitting an odd symmetry is surjective on symmetries. `}
def sigma_two_surjective_of_odd (G : Group) (f : GroupHom G sign_sigma_two) (g : USym G)
  (hg : Id Sign (sigma_two_sign (usym_hom G sign_sigma_two f g)) minus.)
  : Surjective (USym G) (USym sign_sigma_two) (usym_hom G sign_sigma_two f)
  ≔ y ↦ match sign_cases (sigma_two_sign y) [
    | inl. e ↦ mere (BookFiber (USym G) (USym sign_sigma_two) (usym_hom G sign_sigma_two f) y)
        (usym_unit G, concat (USym sign_sigma_two) y (usym_unit sign_sigma_two) (usym_hom G sign_sigma_two f (usym_unit G))
          (sigma_two_unit_of_plus y e)
          (inverse (USym sign_sigma_two) (usym_hom G sign_sigma_two f (usym_unit G)) (usym_unit sign_sigma_two) (usym_hom_unit G sign_sigma_two f)))
    | inr. e ↦ mere (BookFiber (USym G) (USym sign_sigma_two) (usym_hom G sign_sigma_two f) y)
        (g, sigma_two_same_sign y (usym_hom G sign_sigma_two f g)
          (concat Sign (sigma_two_sign y) minus. (sigma_two_sign (usym_hom G sign_sigma_two f g)) e
            (inverse Sign (sigma_two_sign (usym_hom G sign_sigma_two f g)) minus. hg))) ]

def ex_f2_usym_surjective : Surjective (USym (cyclic_group_fin (suc. (suc. (suc. zero.))))) (USym sign_sigma_two) (usym_hom (cyclic_group_fin (suc. (suc. (suc. zero.)))) sign_sigma_two ex_f2)
  ≔ sigma_two_surjective_of_odd (cyclic_group_fin (suc. (suc. (suc. zero.)))) ex_f2 (usym_power (cyclic_group_fin (suc. (suc. (suc. zero.)))) (cyclic_fin_generator (suc. (suc. (suc. zero.)))) (suc. zero.)) (ex_f2_pow_sign (suc. zero.))

def ex_f21_usym_surjective (C : CircleSignature)
  : Surjective (USym (circle_group C)) (USym sign_sigma_two) (usym_hom (circle_group C) sign_sigma_two (ex_f21 C))
  ≔ sigma_two_surjective_of_odd (circle_group C) (ex_f21 C) (usym_power (circle_group C) (C .loop) (suc. zero.)) (ex_f21_pow_sign C (suc. zero.))
