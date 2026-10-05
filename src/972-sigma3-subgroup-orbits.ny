export "970-conjugation-closed-subgroups"
export "583-fixed-point-subgroups"
export "460-sign-counting"
export "930-epi-surj-easy"
export "905-normal-quotient-equivalence"

{` Chapter 9 (subgroups.tex), xca:Sub(Sigma3) (line 1311), second part:
   the orbit structure of Sub(Σ_3) under conjugation, plus litmus checks
   for normal subgroups and quotients (A_n = ker sgn is normal, Σ_3/A_3 is
   Σ_2).

   - The three subgroups of order 2: T_k ≔ (Fin-valued standard Σ_3-set,
     k), the stabilizer of k : Fin 3 (fixed_point_subgroup of module 583,
     underlying group Σ_2 by fixed_point_subgroup_group_path). Conjugation
     moves the point: g · T_k = T_{g(k)}. So they form one orbit
     {T_0, T_1, T_2}; they are pairwise different and none is normal.
   - The fixed points (normal subgroups): 1 (principal_subgroup), Σ_3
     (group_full_subgroup) and A_3 ≔ E(ker sgn); 1 ≠ Σ_3.
   Not formalized: that every subgroup of Σ_3 is one of these six, and
   that A_3 differs from 1 and Σ_3. `}

def sigma3_point_subgroup (k : Fin three) : Subgroups (symmetric_group three) ≔ fixed_point_subgroup two k

{` g · T_k = T_{g(k)}. `}
def sigma3_point_subgroup_conjugate (g : USym (symmetric_group three)) (k : Fin three)
  : Id (Subgroups (symmetric_group three))
      (subgroups_move (symmetric_group three) (shape (symmetric_group three)) (shape (symmetric_group three)) g
        (sigma3_point_subgroup k))
      (sigma3_point_subgroup (gset_usym_act (symmetric_group three) (standard_symmetric_gset three) g k))
  ≔ let G ≔ symmetric_group three in
    let X ≔ standard_symmetric_gset three in
    let y ≔ gset_usym_act G X g k in
    refl ((t ↦ (X, y, t)) : IsTransitive G X → Subgroups G)
      (is_transitive_prop G X (subgroup_transitive_move G (shape G) (shape G) X (fixed_point_gset_transitive two))
        (fixed_point_gset_transitive two))

{` T_i ≠ T_j when some symmetry fixes i but not j. `}
def sigma3_point_subgroups_differ (i j : Fin three) (s : USym (symmetric_group three))
  (fix : SubgroupHasSymmetry (symmetric_group three) (sigma3_point_subgroup i) s)
  (move : Not (SubgroupHasSymmetry (symmetric_group three) (sigma3_point_subgroup j) s))
  (e : Id (Subgroups (symmetric_group three)) (sigma3_point_subgroup i) (sigma3_point_subgroup j)) : Empty
  ≔ move (subgroup_symmetry_transport (symmetric_group three) (sigma3_point_subgroup i) (sigma3_point_subgroup j) e s fix)

def fin3_differ (a b : Fin three) (q : Id Bool (decision_bool (Id (Fin three) a b) (fin_decidable_equality three a b)) false.)
  : Not (Id (Fin three) a b)
  ≔ nat_decision_false_reflect (Id (Fin three) a b) (fin_decidable_equality three a b) q

{` (0 2) as a symmetry of Σ_3. `}
def sigma3_swap02 : USym (symmetric_group three) ≔ permutation_symmetry (standard_set three) fin3_swap02_equiv

def sigma3_T0_ne_T1 (e : Id (Subgroups (symmetric_group three)) (sigma3_point_subgroup fin3_zero) (sigma3_point_subgroup fin3_one))
  : Empty
  ≔ sigma3_point_subgroups_differ fin3_zero fin3_one sigma3_sigma (refl fin3_zero)
      (fin3_differ fin3_two fin3_one (refl (false. : Bool))) e

def sigma3_T0_ne_T2 (e : Id (Subgroups (symmetric_group three)) (sigma3_point_subgroup fin3_zero) (sigma3_point_subgroup fin3_two))
  : Empty
  ≔ sigma3_point_subgroups_differ fin3_zero fin3_two sigma3_sigma (refl fin3_zero)
      (fin3_differ fin3_one fin3_two (refl (false. : Bool))) e

def sigma3_T1_ne_T2 (e : Id (Subgroups (symmetric_group three)) (sigma3_point_subgroup fin3_one) (sigma3_point_subgroup fin3_two))
  : Empty
  ≔ sigma3_point_subgroups_differ fin3_one fin3_two sigma3_swap02 (refl fin3_one)
      (fin3_differ fin3_zero fin3_two (refl (false. : Bool))) e

{` The orbit of T_0 contains T_1 and T_2 (τ = (0 1), (0 2)), and every
   conjugate of any T_k is T_0, T_1 or T_2. `}
def sigma3_T0_conjugate_T1
  : Id (Subgroups (symmetric_group three))
      (subgroups_move (symmetric_group three) (shape (symmetric_group three)) (shape (symmetric_group three)) sigma3_tau
        (sigma3_point_subgroup fin3_zero))
      (sigma3_point_subgroup fin3_one)
  ≔ sigma3_point_subgroup_conjugate sigma3_tau fin3_zero

def sigma3_T0_conjugate_T2
  : Id (Subgroups (symmetric_group three))
      (subgroups_move (symmetric_group three) (shape (symmetric_group three)) (shape (symmetric_group three)) sigma3_swap02
        (sigma3_point_subgroup fin3_zero))
      (sigma3_point_subgroup fin3_two)
  ≔ sigma3_point_subgroup_conjugate sigma3_swap02 fin3_zero

def sigma3_point_subgroup_cases (y : Fin three)
  : Sum (Id (Subgroups (symmetric_group three)) (sigma3_point_subgroup y) (sigma3_point_subgroup fin3_zero))
      (Sum (Id (Subgroups (symmetric_group three)) (sigma3_point_subgroup y) (sigma3_point_subgroup fin3_one))
        (Id (Subgroups (symmetric_group three)) (sigma3_point_subgroup y) (sigma3_point_subgroup fin3_two)))
  ≔ match y [
  | inr. star. ↦ inl. (refl (sigma3_point_subgroup fin3_zero))
  | inl. (inr. star.) ↦ inr. (inl. (refl (sigma3_point_subgroup fin3_one)))
  | inl. (inl. (inr. star.)) ↦ inr. (inr. (refl (sigma3_point_subgroup fin3_two)))
  | inl. (inl. (inl. v)) ↦ match v [] ]

def sigma3_order_two_orbit (g : USym (symmetric_group three)) (k : Fin three)
  : Sum (Id (Subgroups (symmetric_group three))
          (subgroups_move (symmetric_group three) (shape (symmetric_group three)) (shape (symmetric_group three)) g
            (sigma3_point_subgroup k))
          (sigma3_point_subgroup fin3_zero))
      (Sum (Id (Subgroups (symmetric_group three))
             (subgroups_move (symmetric_group three) (shape (symmetric_group three)) (shape (symmetric_group three)) g
               (sigma3_point_subgroup k))
             (sigma3_point_subgroup fin3_one))
        (Id (Subgroups (symmetric_group three))
          (subgroups_move (symmetric_group three) (shape (symmetric_group three)) (shape (symmetric_group three)) g
            (sigma3_point_subgroup k))
          (sigma3_point_subgroup fin3_two)))
  ≔ let G ≔ symmetric_group three in
    let SG ≔ Subgroups G in
    let gT ≔ subgroups_move G (shape G) (shape G) g (sigma3_point_subgroup k) in
    let y ≔ gset_usym_act G (standard_symmetric_gset three) g k in
    let c ≔ sigma3_point_subgroup_conjugate g k in
    match sigma3_point_subgroup_cases y [
    | inl. e ↦ inl. (concat SG gT (sigma3_point_subgroup y) (sigma3_point_subgroup fin3_zero) c e)
    | inr. (inl. e) ↦ inr. (inl. (concat SG gT (sigma3_point_subgroup y) (sigma3_point_subgroup fin3_one) c e))
    | inr. (inr. e) ↦ inr. (inr. (concat SG gT (sigma3_point_subgroup y) (sigma3_point_subgroup fin3_two) c e)) ]

{` No subgroup of order 2 is normal: τ · T_0 = T_1, τ · T_1 = T_0,
   σ · T_2 = T_1 with σ = (1 2). `}
def sigma3_moved_not_normal (k : Fin three) (g : USym (symmetric_group three))
  (d : Id (Subgroups (symmetric_group three)) (sigma3_point_subgroup (gset_usym_act (symmetric_group three) (standard_symmetric_gset three) g k))
         (sigma3_point_subgroup k) → Empty)
  (n : IsNormalSubgroup (symmetric_group three) (sigma3_point_subgroup k)) : Empty
  ≔ let G ≔ symmetric_group three in
    let T ≔ sigma3_point_subgroup k in
    let T' ≔ sigma3_point_subgroup (gset_usym_act G (standard_symmetric_gset three) g k) in
    d (concat (Subgroups G) T' (subgroups_move G (shape G) (shape G) g T) T
        (inverse (Subgroups G) (subgroups_move G (shape G) (shape G) g T) T' (sigma3_point_subgroup_conjugate g k))
        (normal_subgroup_fixed G T n g))

def sigma3_point_subgroup_not_normal (k : Fin three) : Not (IsNormalSubgroup (symmetric_group three) (sigma3_point_subgroup k))
  ≔ match k [
  | inr. star. ↦ sigma3_moved_not_normal fin3_zero sigma3_tau
      (e ↦ sigma3_T0_ne_T1 (inverse (Subgroups (symmetric_group three)) (sigma3_point_subgroup fin3_one) (sigma3_point_subgroup fin3_zero) e))
  | inl. (inr. star.) ↦ sigma3_moved_not_normal fin3_one sigma3_tau sigma3_T0_ne_T1
  | inl. (inl. (inr. star.)) ↦ sigma3_moved_not_normal fin3_two sigma3_sigma
      (e ↦ sigma3_T1_ne_T2 e)
  | inl. (inl. (inl. v)) ↦ match v [] ]

{` The sign homomorphism Σ_n → Σ_2 (n ≥ 2) is surjective on symmetries
   ((0 1) has sign −), hence has connected fibers (lem:epi-surj, module
   930); so A_n ≔ E(ker sgn) is a normal subgroup (kernel_normal). `}
def sign_surjective_case (m : Nat) (h : USym sign_sigma_two) (t : Sign)
  : Id Sign (sigma_two_sign h) t
    → Mere (BookFiber (USym (symmetric_group (suc. (suc. m)))) (USym sign_sigma_two) (usgn (suc. (suc. m))) h)
  ≔ let n : Nat ≔ suc. (suc. m) in
    let Sn ≔ symmetric_group n in
    let F ≔ BookFiber (USym Sn) (USym sign_sigma_two) (usgn n) h in
    let inj ≔ equivalence_injective (USym sign_sigma_two) Sign sigma_two_sign_equiv in
    match t [
    | plus. ↦ q ↦ mere F (usym_unit Sn,
        inj h (usgn n (usym_unit Sn))
          (calc
            sigma_two_sign h = plus. by q
            = sigma_two_sign (usym_unit sign_sigma_two)
              by inverse Sign (sigma_two_sign (usym_unit sign_sigma_two)) plus. sigma_two_sign_unit
            = sigma_two_sign (usgn n (usym_unit Sn))
              by refl sigma_two_sign
                   (inverse (USym sign_sigma_two) (usgn n (usym_unit Sn)) (usym_unit sign_sigma_two)
                     (usym_hom_unit Sn sign_sigma_two (sign_hom n))) ∎))
    | minus. ↦ q ↦
        let s ≔ permutation_symmetry (standard_set n) (fin_swap01_equiv m) in
        mere F (s,
          inj h (usgn n s)
            (concat Sign (sigma_two_sign h) minus. (sigma_two_sign (usgn n s)) q
              (inverse Sign (sigma_two_sign (usgn n s)) minus. (usgn_swap01 m)))) ]

def sign_hom_usym_surjective (m : Nat)
  : Surjective (USym (symmetric_group (suc. (suc. m)))) (USym sign_sigma_two)
      (usym_hom (symmetric_group (suc. (suc. m))) sign_sigma_two (sign_hom (suc. (suc. m))))
  ≔ h ↦ sign_surjective_case m h (sigma_two_sign h) (refl (sigma_two_sign h))

def sign_hom_connected (m : Nat)
  : IsConnectedHom (symmetric_group (suc. (suc. m))) sign_sigma_two (sign_hom (suc. (suc. m)))
  ≔ gepi_usym_surjective_connected_fibers (symmetric_group (suc. (suc. m))) sign_sigma_two (sign_hom (suc. (suc. m)))
      (sign_hom_usym_surjective m)

def alternating_subgroup (m : Nat) : Subgroups (symmetric_group (suc. (suc. m)))
  ≔ mono_to_subgroup (symmetric_group (suc. (suc. m))) (kernel (symmetric_group (suc. (suc. m))) sign_sigma_two (sign_hom (suc. (suc. m))))

def alternating_subgroup_normal (m : Nat) : IsNormalSubgroup (symmetric_group (suc. (suc. m))) (alternating_subgroup m)
  ≔ kernel_normal (symmetric_group (suc. (suc. m))) sign_sigma_two (sign_hom (suc. (suc. m))) (sign_hom_connected m)

{` A_n as an element of Nor(Σ_n) (nor of the connected epimorphism sgn),
   with underlying subgroup E(ker sgn) (lem:diagfornormal), and the
   quotient Σ_n/A_n is Σ_2 (lem:qeq: q(nor(sgn)) = sgn). `}
def sign_connected_epi (m : Nat) : ConnectedEpis (symmetric_group (suc. (suc. m)))
  ≔ (sign_sigma_two, (sign_hom (suc. (suc. m)), sign_hom_connected m))

def alternating_normal_subgroup (m : Nat) : NormalSubgroups (symmetric_group (suc. (suc. m)))
  ≔ nor_conn (symmetric_group (suc. (suc. m))) (sign_connected_epi m)

def alternating_normal_subgroup_underlying (m : Nat)
  : Id (Subgroups (symmetric_group (suc. (suc. m))))
      (normal_to_subgroup (symmetric_group (suc. (suc. m))) (alternating_normal_subgroup m)) (alternating_subgroup m)
  ≔ diag_for_normal (symmetric_group (suc. (suc. m))) sign_sigma_two (sign_hom (suc. (suc. m))) (sign_hom_connected m)

def alternating_quotient_path (m : Nat)
  : Id Group (normal_quotient_group (symmetric_group (suc. (suc. m))) (alternating_normal_subgroup m)) sign_sigma_two
  ≔ refl ((u ↦ u .fst) : ConnectedEpis (symmetric_group (suc. (suc. m))) → Group)
      (q_nor_path (symmetric_group (suc. (suc. m))) (sign_connected_epi m))

{` Litmus: Σ_n/A_n has exactly two symmetries (USym ≃ Sign). `}
def alternating_quotient_usym_sign (m : Nat)
  : Equiv (USym (normal_quotient_group (symmetric_group (suc. (suc. m))) (alternating_normal_subgroup m))) Sign
  ≔ let Q ≔ normal_quotient_group (symmetric_group (suc. (suc. m))) (alternating_normal_subgroup m) in
    compose_equiv (USym Q) (USym sign_sigma_two) Sign
      (id_to_equiv (USym Q) (USym sign_sigma_two) (map_path Group Type USym Q sign_sigma_two (alternating_quotient_path m)))
      sigma_two_sign_equiv

{` The case n = 3: the fixed points of Sub(Σ_3) named in the exercise. `}
def sigma3_alternating_normal : IsNormalSubgroup (symmetric_group three) (alternating_subgroup (suc. zero.))
  ≔ alternating_subgroup_normal (suc. zero.)

def sigma3_trivial_normal : IsNormalSubgroup (symmetric_group three) (principal_subgroup (symmetric_group three))
  ≔ principal_subgroup_normal (symmetric_group three)

def sigma3_full_normal : IsNormalSubgroup (symmetric_group three) (group_full_subgroup (symmetric_group three))
  ≔ full_subgroup_normal (symmetric_group three)

def sigma3_quotient_alternating : Id Group (normal_quotient_group (symmetric_group three) (alternating_normal_subgroup (suc. zero.)))
    sign_sigma_two
  ≔ alternating_quotient_path (suc. zero.)

{` 1 ≠ Σ_3: τ is a symmetry of the full subgroup but not of 1. `}
def sigma3_tau_ne_unit (e : Id (USym (symmetric_group three)) sigma3_tau (usym_unit (symmetric_group three))) : Empty
  ≔ let G ≔ symmetric_group three in
    let X ≔ standard_symmetric_gset three in
    fin3_differ fin3_one fin3_zero (refl (false. : Bool))
      (concat (Fin three) fin3_one (gset_usym_act G X (usym_unit G) fin3_zero) fin3_zero
        (refl ((p ↦ gset_usym_act G X p fin3_zero) : USym G → Fin three) e)
        (gset_act_refl G X (shape G) fin3_zero))

def sigma3_trivial_ne_full
  (e : Id (Subgroups (symmetric_group three)) (principal_subgroup (symmetric_group three)) (group_full_subgroup (symmetric_group three)))
  : Empty
  ≔ let G ≔ symmetric_group three in
    sigma3_tau_ne_unit
      (principal_subgroup_symmetry_unit G sigma3_tau
        (subgroup_symmetry_transport G (group_full_subgroup G) (principal_subgroup G)
          (inverse (Subgroups G) (principal_subgroup G) (group_full_subgroup G) e) sigma3_tau
          (full_subgroup_has_symmetry G sigma3_tau)))
