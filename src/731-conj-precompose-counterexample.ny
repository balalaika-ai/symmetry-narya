export "723-abstract-conjugation"

{` Chapter 7 (absgroup.tex), ex:conjhom: "similarly for elements in H,
   giving rise to precomposition with conjugation by h" is false as printed.
   Transport along conj^h : H = H in X ↦ absHom(X, K) is precomposition with
   conj^{h⁻¹} (abstract_conj_transport_precompose, module 723), and for
   H = K = abstr Σ₃, f = id and h = τσ (a 3-cycle) this differs from
   precomposition with conj^h: otherwise conj^{h⁻¹}(τ) = conj^h(τ), which
   evaluated at h(0) gives τ(h(h(0))) = h(h(τ(0))), i.e. 2 = 0 in Fin 3. `}

def conj_pre_act (p : USym (symmetric_group three)) (y : Fin three) : Fin three
  ≔ permutation_action (standard_set three) p y

def conj_pre_h : USym (symmetric_group three) ≔ usym_mul (symmetric_group three) sigma3_tau sigma3_sigma

def conj_pre_act_mul (p q : USym (symmetric_group three)) (y : Fin three)
  : Id (Fin three) (conj_pre_act (usym_mul (symmetric_group three) p q) y) (conj_pre_act p (conj_pre_act q y))
  ≔ permutation_action_mul (standard_set three) p q y

{` h(0) = 1, h(1) = 2, h(2) = 0. `}
def conj_pre_h_zero : Id (Fin three) (conj_pre_act conj_pre_h fin3_zero) fin3_one
  ≔ conj_pre_act_mul sigma3_tau sigma3_sigma fin3_zero

def conj_pre_h_one : Id (Fin three) (conj_pre_act conj_pre_h fin3_one) fin3_two
  ≔ conj_pre_act_mul sigma3_tau sigma3_sigma fin3_one

def conj_pre_h_two : Id (Fin three) (conj_pre_act conj_pre_h fin3_two) fin3_zero
  ≔ conj_pre_act_mul sigma3_tau sigma3_sigma fin3_two

{` h(h⁻¹(y)) = y, h⁻¹(h(z)) = z and (h⁻¹)⁻¹ acts as h. `}
def conj_pre_cancel_right (y : Fin three)
  : Id (Fin three) (conj_pre_act conj_pre_h (conj_pre_act (usym_inv (symmetric_group three) conj_pre_h) y)) y
  ≔ let S3 ≔ symmetric_group three in let h ≔ conj_pre_h in let ih ≔ usym_inv S3 h in
    concat (Fin three) (conj_pre_act h (conj_pre_act ih y)) (conj_pre_act (usym_mul S3 h ih) y) y
      (inverse (Fin three) (conj_pre_act (usym_mul S3 h ih) y) (conj_pre_act h (conj_pre_act ih y)) (conj_pre_act_mul h ih y))
      (concat (Fin three) (conj_pre_act (usym_mul S3 h ih) y) (conj_pre_act (usym_unit S3) y) y
        (refl ((p ↦ conj_pre_act p y) : USym S3 → Fin three) (abstr S3 .laws .inv_right h))
        (permutation_action_unit (standard_set three) y))

def conj_pre_cancel_left (z : Fin three)
  : Id (Fin three) (conj_pre_act (usym_inv (symmetric_group three) conj_pre_h) (conj_pre_act conj_pre_h z)) z
  ≔ let S3 ≔ symmetric_group three in let h ≔ conj_pre_h in let ih ≔ usym_inv S3 h in
    concat (Fin three) (conj_pre_act ih (conj_pre_act h z)) (conj_pre_act (usym_mul S3 ih h) z) z
      (inverse (Fin three) (conj_pre_act (usym_mul S3 ih h) z) (conj_pre_act ih (conj_pre_act h z)) (conj_pre_act_mul ih h z))
      (concat (Fin three) (conj_pre_act (usym_mul S3 ih h) z) (conj_pre_act (usym_unit S3) z) z
        (refl ((p ↦ conj_pre_act p z) : USym S3 → Fin three) (ag_inv_left (abstr S3) h))
        (permutation_action_unit (standard_set three) z))

def conj_pre_inv_inv (y : Fin three)
  : Id (Fin three) (conj_pre_act (usym_inv (symmetric_group three) (usym_inv (symmetric_group three) conj_pre_h)) y)
      (conj_pre_act conj_pre_h y)
  ≔ refl ((p ↦ conj_pre_act p y) : USym (symmetric_group three) → Fin three) (ag_inv_inv (abstr (symmetric_group three)) conj_pre_h)

def conj_pre_two_not_zero (p : Id (Fin three) fin3_two fin3_zero) : Empty
  ≔ transport (Fin three) fin3_two_code fin3_two fin3_zero p star.

{` If conj^{h⁻¹}(τ) = conj^h(τ) then 2 = 0. `}
def conj_pre_sigma3_contradiction
  (E : Id (USym (symmetric_group three))
    (abstract_conj (abstr (symmetric_group three)) (usym_inv (symmetric_group three) conj_pre_h) sigma3_tau)
    (abstract_conj (abstr (symmetric_group three)) conj_pre_h sigma3_tau))
  : Empty
  ≔ let S3 ≔ symmetric_group three in let A ≔ conj_pre_act in let M ≔ usym_mul S3 in
    let h ≔ conj_pre_h in let ih ≔ usym_inv S3 h in let t ≔ sigma3_tau in
    let z ≔ fin3_zero in let y ≔ A h z in
    let F : Id (Fin three) (A (M (M ih t) (usym_inv S3 ih)) y) (A (M (M h t) ih) y)
      ≔ refl ((p ↦ A p y) : USym S3 → Fin three) E in
    let L1 : Id (Fin three) (A (M (M ih t) (usym_inv S3 ih)) y) (A ih (A t (A h y)))
      ≔ calc
          A (M (M ih t) (usym_inv S3 ih)) y = A (M ih t) (A (usym_inv S3 ih) y) by conj_pre_act_mul (M ih t) (usym_inv S3 ih) y
          = A (M ih t) (A h y) by refl (A (M ih t)) (conj_pre_inv_inv y)
          = A ih (A t (A h y)) by conj_pre_act_mul ih t (A h y) ∎ in
    let L2 : Id (Fin three) (A (M (M h t) ih) y) (A h (A t z))
      ≔ calc
          A (M (M h t) ih) y = A (M h t) (A ih y) by conj_pre_act_mul (M h t) ih y
          = A (M h t) z by refl (A (M h t)) (conj_pre_cancel_left z)
          = A h (A t z) by conj_pre_act_mul h t z ∎ in
    let K : Id (Fin three) (A ih (A t (A h y))) (A h (A t z))
      ≔ concat (Fin three) (A ih (A t (A h y))) (A (M (M ih t) (usym_inv S3 ih)) y) (A h (A t z))
          (inverse (Fin three) (A (M (M ih t) (usym_inv S3 ih)) y) (A ih (A t (A h y))) L1)
          (concat (Fin three) (A (M (M ih t) (usym_inv S3 ih)) y) (A (M (M h t) ih) y) (A h (A t z)) F L2) in
    let K2 : Id (Fin three) (A t (A h y)) (A h (A h (A t z)))
      ≔ concat (Fin three) (A t (A h y)) (A h (A ih (A t (A h y)))) (A h (A h (A t z)))
          (inverse (Fin three) (A h (A ih (A t (A h y)))) (A t (A h y)) (conj_pre_cancel_right (A t (A h y))))
          (refl (A h) K) in
    let lhs : Id (Fin three) (A t (A h y)) fin3_two
      ≔ refl (A t) (concat (Fin three) (A h y) (A h fin3_one) fin3_two (refl (A h) conj_pre_h_zero) conj_pre_h_one) in
    let rhs : Id (Fin three) (A h (A h (A t z))) fin3_zero
      ≔ concat (Fin three) (A h (A h (A t z))) (A h fin3_two) fin3_zero (refl (A h) conj_pre_h_one) conj_pre_h_two in
    conj_pre_two_not_zero
      (concat (Fin three) fin3_two (A t (A h y)) fin3_zero
        (inverse (Fin three) (A t (A h y)) fin3_two lhs)
        (concat (Fin three) (A t (A h y)) (A h (A h (A t z))) fin3_zero K2 rhs))

{` The printed reading of ex:conjhom (precomposition with conj^h) fails. `}
def abstract_conj_transport_precompose_printed_fails
  (hyp : (H K : AbstractGroup) (x : H .carrier) (f : AbstractHom H K)
    → Id (H .carrier → K .carrier)
        (transport AbstractGroup (X ↦ AbstractHom X K) H H (abstract_conj_path H x) f .fst)
        (t ↦ f .fst (abstract_conj H x t)))
  : Empty
  ≔ let S3 ≔ symmetric_group three in let AG ≔ abstr S3 in let h ≔ conj_pre_h in
    let tr ≔ transport AbstractGroup (X ↦ AbstractHom X AG) AG AG (abstract_conj_path AG h) (abstract_hom_id AG) .fst in
    let E0 : Id (USym S3 → USym S3) tr (t ↦ abstract_conj AG h t) ≔ hyp AG AG h (abstract_hom_id AG) in
    let E1 : Id (USym S3 → USym S3) tr (t ↦ abstract_conj AG (usym_inv S3 h) t)
      ≔ refl ((φ ↦ φ .fst) : AbstractHom AG AG → (USym S3 → USym S3))
          (abstract_conj_transport_precompose AG AG h (abstract_hom_id AG)) in
    let E : Id (USym S3 → USym S3) (t ↦ abstract_conj AG (usym_inv S3 h) t) (t ↦ abstract_conj AG h t)
      ≔ concat (USym S3 → USym S3) (t ↦ abstract_conj AG (usym_inv S3 h) t) tr (t ↦ abstract_conj AG h t)
          (inverse (USym S3 → USym S3) tr (t ↦ abstract_conj AG (usym_inv S3 h) t) E1) E0 in
    conj_pre_sigma3_contradiction (E (refl sigma3_tau))
