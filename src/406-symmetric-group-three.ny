export "404-group-examples"

{` Concrete symmetries of Σ_3 (litmus for the orientation of usym_mul and
   for remark rem 1202 / exer:first examples). The elements of Fin 3 are
   named as in def:finiteset: 0 = inr star, 1 = inl (inr star),
   2 = inl (inl (inr star)). `}
def three : Nat ≔ suc. (suc. (suc. zero.))

def fin3_zero : Fin three ≔ inr. star.
def fin3_one : Fin three ≔ inl. (inr. star.)
def fin3_two : Fin three ≔ inl. (inl. (inr. star.))

{` The transposition (0 1). `}
def fin3_swap01 : Fin three → Fin three ≔ [
  | inr. u ↦ inl. (inr. u)
  | inl. (inr. u) ↦ inr. u
  | inl. (inl. w) ↦ inl. (inl. w) ]

def fin3_swap01_involutive (x : Fin three) : Id (Fin three) (fin3_swap01 (fin3_swap01 x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin three)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin three)
  | inl. (inl. w) ↦ refl (inl. (inl. w) : Fin three) ]

{` The transposition (1 2). `}
def fin3_swap12 : Fin three → Fin three ≔ [
  | inr. u ↦ inr. u
  | inl. (inr. u) ↦ inl. (inl. (inr. u))
  | inl. (inl. (inr. u)) ↦ inl. (inr. u)
  | inl. (inl. (inl. e)) ↦ match e [] ]

def fin3_swap12_involutive (x : Fin three) : Id (Fin three) (fin3_swap12 (fin3_swap12 x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin three)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin three)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin three)
  | inl. (inl. (inl. e)) ↦ match e [] ]

def fin3_swap01_equiv : Equiv (Fin three) (Fin three)
  ≔ quasi_inverse_equiv (Fin three) (Fin three) fin3_swap01 fin3_swap01
      fin3_swap01_involutive fin3_swap01_involutive

def fin3_swap12_equiv : Equiv (Fin three) (Fin three)
  ≔ quasi_inverse_equiv (Fin three) (Fin three) fin3_swap12 fin3_swap12
      fin3_swap12_involutive fin3_swap12_involutive

{` The symmetries τ = (0 1) and σ = (1 2) in Σ_3. `}
def sigma3_tau : USym (symmetric_group three) ≔ permutation_symmetry (standard_set three) fin3_swap01_equiv

def sigma3_sigma : USym (symmetric_group three) ≔ permutation_symmetry (standard_set three) fin3_swap12_equiv

{` Two different elements of Fin 3. `}
def fin3_two_code : Fin three → Type ≔ [
  | inr. _ ↦ Empty
  | inl. (inr. _) ↦ Empty
  | inl. (inl. _) ↦ Unit ]

def fin3_two_not_one (p : Id (Fin three) fin3_two fin3_one) : Empty
  ≔ transport (Fin three) fin3_two_code fin3_two fin3_one p star.

{` (σ·τ)(0) = σ(τ(0)) = 2 and (τ·σ)(0) = τ(σ(0)) = 1. `}
def sigma3_sigma_tau_zero
  : Id (Fin three) (permutation_action (standard_set three)
      (usym_mul (symmetric_group three) sigma3_sigma sigma3_tau) fin3_zero) fin3_two
  ≔ permutation_action_mul (standard_set three) sigma3_sigma sigma3_tau fin3_zero

def sigma3_tau_sigma_zero
  : Id (Fin three) (permutation_action (standard_set three)
      (usym_mul (symmetric_group three) sigma3_tau sigma3_sigma) fin3_zero) fin3_one
  ≔ permutation_action_mul (standard_set three) sigma3_tau sigma3_sigma fin3_zero

{` Litmus (exer:first examples, second part): Σ_3 is not abelian. `}
def sigma3_tau_sigma_noncommuting
  (h : Id (USym (symmetric_group three))
    (usym_mul (symmetric_group three) sigma3_sigma sigma3_tau)
    (usym_mul (symmetric_group three) sigma3_tau sigma3_sigma)) : Empty
  ≔ let act : USym (symmetric_group three) → Fin three
      ≔ p ↦ permutation_action (standard_set three) p fin3_zero in
    fin3_two_not_one
      (concat (Fin three) fin3_two (act (usym_mul (symmetric_group three) sigma3_tau sigma3_sigma)) fin3_one
        (concat (Fin three) fin3_two (act (usym_mul (symmetric_group three) sigma3_sigma sigma3_tau))
          (act (usym_mul (symmetric_group three) sigma3_tau sigma3_sigma))
          (inverse (Fin three) (act (usym_mul (symmetric_group three) sigma3_sigma sigma3_tau)) fin3_two
            sigma3_sigma_tau_zero)
          (refl act h))
        sigma3_tau_sigma_zero)

def symmetric_group_three_not_abelian (h : IsAbelian (symmetric_group three)) : Empty
  ≔ sigma3_tau_sigma_noncommuting (h sigma3_sigma sigma3_tau)
