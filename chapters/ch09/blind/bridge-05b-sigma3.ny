export "05-subgroup-action"
export "../../../src/977-sigma3-classification-lem"
export "../../../src/520-orbit-relations"
export "../../../src/1720-blass-counting"

{` Bridges for xca:Sub(Sigma3) (2) (subgroups.tex:1311, blind file 05-subgroup-action): the orbits of
   Sub(Σ_3). Corrected statement (with excluded middle) derived from ours (modules 972, 976); the literal statement
   (no hypothesis) implies excluded middle (through module 977), so it is not provable constructively. `}

def bridge9w_rep : Fin blind_nat_four → Subgroups (symmetric_group three) ≔ [
  | inr. _ ↦ principal_subgroup (symmetric_group three)
  | inl. (inr. _) ↦ alternating_subgroup (suc. zero.)
  | inl. (inl. (inr. _)) ↦ group_full_subgroup (symmetric_group three)
  | inl. (inl. (inl. (inr. _))) ↦ sigma3_point_subgroup fin3_zero
  | inl. (inl. (inl. (inl. v))) ↦ match v [] ]

def bridge9w_orb (i : Fin blind_nat_four) : Orbits (symmetric_group three) (subgroups_gset (symmetric_group three))
  ≔ orbit_of_point (symmetric_group three) (subgroups_gset (symmetric_group three)) (bridge9w_rep i)

{` A normal subgroup is fixed: g · N = S implies N = S; and g · T_0 = T_{g(0)}. `}
def bridge9w_fix (N S : Subgroups (symmetric_group three)) (n : IsNormalSubgroup (symmetric_group three) N)
  (g : USym (symmetric_group three))
  (e : Id (Subgroups (symmetric_group three)) (gset_usym_act (symmetric_group three) (subgroups_gset (symmetric_group three)) g N) S)
  : Id (Subgroups (symmetric_group three)) N S
  ≔ let G ≔ symmetric_group three in let SG ≔ Subgroups G in
    let gN ≔ gset_usym_act G (subgroups_gset G) g N in
    concat SG N gN S
      (inverse SG gN N
        (concat SG gN (subgroups_move G (shape G) (shape G) g N) N (subgroups_gset_usym_act G g N) (normal_subgroup_fixed G N n g)))
      e

def bridge9w_T0_move (g : USym (symmetric_group three)) (S : Subgroups (symmetric_group three))
  (e : Id (Subgroups (symmetric_group three))
         (gset_usym_act (symmetric_group three) (subgroups_gset (symmetric_group three)) g (sigma3_point_subgroup fin3_zero)) S)
  : Id (Subgroups (symmetric_group three))
      (sigma3_point_subgroup (gset_usym_act (symmetric_group three) (standard_symmetric_gset three) g fin3_zero)) S
  ≔ let G ≔ symmetric_group three in let SG ≔ Subgroups G in
    let T0 ≔ sigma3_point_subgroup fin3_zero in
    let gT ≔ gset_usym_act G (subgroups_gset G) g T0 in
    let Tg ≔ sigma3_point_subgroup (gset_usym_act G (standard_symmetric_gset three) g fin3_zero) in
    concat SG Tg gT S
      (inverse SG gT Tg
        (concat SG gT (subgroups_move G (shape G) (shape G) g T0) Tg (subgroups_gset_usym_act G g T0)
          (sigma3_point_subgroup_conjugate g fin3_zero)))
      e

def bridge9w_T_ne_normal (N : Subgroups (symmetric_group three)) (n : IsNormalSubgroup (symmetric_group three) N)
  (g : USym (symmetric_group three))
  (e : Id (Subgroups (symmetric_group three))
         (gset_usym_act (symmetric_group three) (subgroups_gset (symmetric_group three)) g (sigma3_point_subgroup fin3_zero)) N)
  : Empty
  ≔ let k ≔ gset_usym_act (symmetric_group three) (standard_symmetric_gset three) g fin3_zero in
    sigma3_normal_ne_point_subgroup N n k
      (inverse (Subgroups (symmetric_group three)) (sigma3_point_subgroup k) N (bridge9w_T0_move g N e))

{` The four representatives lie in four different orbits. `}
def bridge9w_reflect_raw (i j : Fin blind_nat_four)
  : (g : USym (symmetric_group three))
    → Id (Subgroups (symmetric_group three))
        (gset_usym_act (symmetric_group three) (subgroups_gset (symmetric_group three)) g (bridge9w_rep i)) (bridge9w_rep j)
    → Id (Fin blind_nat_four) i j
  ≔ let G ≔ symmetric_group three in let SG ≔ Subgroups G in
    let P1 ≔ principal_subgroup G in let A3 ≔ alternating_subgroup (suc. zero.) in
    let F ≔ group_full_subgroup G in let T0 ≔ sigma3_point_subgroup fin3_zero in
    let n0 ≔ sigma3_trivial_normal in let n1 ≔ sigma3_alternating_normal in let n2 ≔ sigma3_full_normal in
    match i [
    | inr. star. ↦ match j [
      | inr. star. ↦ g e ↦ refl (inr. star. : Fin blind_nat_four)
      | inl. (inr. star.) ↦ g e ↦ match sigma3_a3_ne_trivial (inverse SG P1 A3 (bridge9w_fix P1 A3 n0 g e)) []
      | inl. (inl. (inr. star.)) ↦ g e ↦ match sigma3_trivial_ne_full (bridge9w_fix P1 F n0 g e) []
      | inl. (inl. (inl. (inr. star.))) ↦ g e ↦ match sigma3_normal_ne_point_subgroup P1 n0 fin3_zero (bridge9w_fix P1 T0 n0 g e) []
      | inl. (inl. (inl. (inl. v))) ↦ match v [] ]
    | inl. (inr. star.) ↦ match j [
      | inr. star. ↦ g e ↦ match sigma3_a3_ne_trivial (bridge9w_fix A3 P1 n1 g e) []
      | inl. (inr. star.) ↦ g e ↦ refl (inl. (inr. star.) : Fin blind_nat_four)
      | inl. (inl. (inr. star.)) ↦ g e ↦ match sigma3_a3_ne_full (bridge9w_fix A3 F n1 g e) []
      | inl. (inl. (inl. (inr. star.))) ↦ g e ↦ match sigma3_normal_ne_point_subgroup A3 n1 fin3_zero (bridge9w_fix A3 T0 n1 g e) []
      | inl. (inl. (inl. (inl. v))) ↦ match v [] ]
    | inl. (inl. (inr. star.)) ↦ match j [
      | inr. star. ↦ g e ↦ match sigma3_trivial_ne_full (inverse SG F P1 (bridge9w_fix F P1 n2 g e)) []
      | inl. (inr. star.) ↦ g e ↦ match sigma3_a3_ne_full (inverse SG F A3 (bridge9w_fix F A3 n2 g e)) []
      | inl. (inl. (inr. star.)) ↦ g e ↦ refl (inl. (inl. (inr. star.)) : Fin blind_nat_four)
      | inl. (inl. (inl. (inr. star.))) ↦ g e ↦ match sigma3_normal_ne_point_subgroup F n2 fin3_zero (bridge9w_fix F T0 n2 g e) []
      | inl. (inl. (inl. (inl. v))) ↦ match v [] ]
    | inl. (inl. (inl. (inr. star.))) ↦ match j [
      | inr. star. ↦ g e ↦ match bridge9w_T_ne_normal P1 n0 g e []
      | inl. (inr. star.) ↦ g e ↦ match bridge9w_T_ne_normal A3 n1 g e []
      | inl. (inl. (inr. star.)) ↦ g e ↦ match bridge9w_T_ne_normal F n2 g e []
      | inl. (inl. (inl. (inr. star.))) ↦ g e ↦ refl (inl. (inl. (inl. (inr. star.))) : Fin blind_nat_four)
      | inl. (inl. (inl. (inl. v))) ↦ match v [] ]
    | inl. (inl. (inl. (inl. v))) ↦ match v [] ]

def bridge9w_reflect : PathReflecting (Fin blind_nat_four) (Orbits (symmetric_group three) (subgroups_gset (symmetric_group three)))
    bridge9w_orb
  ≔ i j p ↦
    let G ≔ symmetric_group three in let X ≔ subgroups_gset G in
    mere_rec (Σ (USym G) (g ↦ Id (Subgroups G) (gset_usym_act G X g (bridge9w_rep i)) (bridge9w_rep j)))
      (Id (Fin blind_nat_four) i j) (fin_set blind_nat_four i j)
      (w ↦ bridge9w_reflect_raw i j (w .fst) (w .snd))
      (orbit_relation_from_path G X (bridge9w_rep i) (bridge9w_rep j) p)

{` Under excluded middle every subgroup of Σ_3 is decidable, hence one of the six (module 976), hence in the orbit
   of a representative. `}
def bridge9w_lem_decidable (lem : ExcludedMiddle) (S : Subgroups (symmetric_group three))
  : IsDecidableSubgroup (symmetric_group three) S
  ≔ x y ↦ lem (Id (S .gset (shape (symmetric_group three)) .fst) x y) (S .gset (shape (symmetric_group three)) .snd x y)

def bridge9w_T_orbit (k : Fin three) (g : USym (symmetric_group three))
  (e : Id (Subgroups (symmetric_group three))
         (subgroups_move (symmetric_group three) (shape (symmetric_group three)) (shape (symmetric_group three)) g
           (sigma3_point_subgroup fin3_zero))
         (sigma3_point_subgroup k))
  : Id (Orbits (symmetric_group three) (subgroups_gset (symmetric_group three)))
      (orbit_of_point (symmetric_group three) (subgroups_gset (symmetric_group three)) (sigma3_point_subgroup k))
      (bridge9w_orb (inl. (inl. (inl. (inr. star.)))))
  ≔ let G ≔ symmetric_group three in let X ≔ subgroups_gset G in let SG ≔ Subgroups G in
    let T0 ≔ sigma3_point_subgroup fin3_zero in
    inverse (Orbits G X) (orbit_of_point G X T0) (orbit_of_point G X (sigma3_point_subgroup k))
      (orbit_relation_to_path G X T0 (sigma3_point_subgroup k)
        (mere (Σ (USym G) (h ↦ Id SG (gset_usym_act G X h T0) (sigma3_point_subgroup k)))
          (g, concat SG (gset_usym_act G X g T0) (subgroups_move G (shape G) (shape G) g T0) (sigma3_point_subgroup k)
                (subgroups_gset_usym_act G g T0) e)))

def bridge9w_classify_index (S : Subgroups (symmetric_group three)) (c : Sigma3SixSubgroups S)
  : Σ (Fin blind_nat_four) (i ↦ Id (Orbits (symmetric_group three) (subgroups_gset (symmetric_group three)))
      (orbit_of_point (symmetric_group three) (subgroups_gset (symmetric_group three)) S) (bridge9w_orb i))
  ≔ let G ≔ symmetric_group three in let X ≔ subgroups_gset G in
    let O ≔ Orbits G X in let op ≔ orbit_of_point G X in
    let r3 : Fin blind_nat_four ≔ inl. (inl. (inl. (inr. star.))) in
    match c [
    | inl. e ↦ (inr. star., refl op e)
    | inr. (inl. e) ↦ (inl. (inr. star.), refl op e)
    | inr. (inr. (inl. e)) ↦ (inl. (inl. (inr. star.)), refl op e)
    | inr. (inr. (inr. (inl. e))) ↦ (r3, refl op e)
    | inr. (inr. (inr. (inr. (inl. e)))) ↦
        (r3, concat O (op S) (op (sigma3_point_subgroup fin3_one)) (bridge9w_orb r3) (refl op e)
               (bridge9w_T_orbit fin3_one sigma3_tau sigma3_T0_conjugate_T1))
    | inr. (inr. (inr. (inr. (inr. e)))) ↦
        (r3, concat O (op S) (op (sigma3_point_subgroup fin3_two)) (bridge9w_orb r3) (refl op e)
               (bridge9w_T_orbit fin3_two sigma3_swap02 sigma3_T0_conjugate_T2)) ]

def bridge9w_surjective (lem : ExcludedMiddle)
  : Surjective (Fin blind_nat_four) (Orbits (symmetric_group three) (subgroups_gset (symmetric_group three))) bridge9w_orb
  ≔ Ob ↦
    let G ≔ symmetric_group three in let X ≔ subgroups_gset G in let O ≔ Orbits G X in
    let F ≔ BookFiber (Fin blind_nat_four) O bridge9w_orb Ob in
    mere_rec (BookFiber (Subgroups G) O (orbit_of_point G X) Ob) (Mere F) (mere_isprop F)
      (u ↦ let c ≔ bridge9w_classify_index (u .fst)
             (sigma3_decidable_subgroup_classification (u .fst) (bridge9w_lem_decidable lem (u .fst))) in
        mere F (c .fst, concat O Ob (orbit_of_point G X (u .fst)) (bridge9w_orb (c .fst)) (u .snd) (c .snd)))
      (orbit_of_point_surjective G X Ob)

{` xca:Sub(Sigma3) (2), corrected (excluded middle): Sub(Σ_3)/Σ_3 ≃ Fin 4. `}
def bridge_sub_sigma3_orbits_corrected : blind_sub_sigma3_orbits_corrected
  ≔ lem ↦
    let O ≔ Orbits (symmetric_group three) (subgroups_gset (symmetric_group three)) in
    let F4 ≔ Fin blind_nat_four in
    canonical_inverse_equiv F4 O
      (native_equivalence F4 O
        (embedding_surjection_equiv native_truncation F4 O bridge9w_orb
          (path_reflecting_set_embedding F4 O (orbits_set (symmetric_group three) (subgroups_gset (symmetric_group three)))
            bridge9w_orb bridge9w_reflect)
          (bridge9w_surjective lem)))

{` The literal statement implies excluded middle. For a proposition P let S_P be module 977's subgroup with
   symmetries {e} ∪ {(1 2) | P}. Given Sub(Σ_3)/Σ_3 ≃ Fin 4, the four representative orbits are four different
   points of Fin 4, so they exhaust it (bsix_injection_full of appendix B) and S_P lies in the orbit of one of
   them: of 1 gives ¬P, of A_3, Σ_3 or T_0 gives P. `}
def bridge9w_point_member (P : Type) (hP : isProp P) (k : Fin three)
  : Id (Subgroups (symmetric_group three)) (sigma3_point_subgroup k) (sigma3_prop_subgroup P) → P
  ≔ let G ≔ symmetric_group three in
    match k [
    | inr. star. ↦ e ↦ sigma3_prop_member P hP t12. fin3_one (fin3_differ fin3_two fin3_one (refl (false. : Bool)))
        (subgroup_symmetry_transport G (sigma3_point_subgroup fin3_zero) (sigma3_prop_subgroup P) e (sigma3_sym t12.)
          (refl fin3_zero))
    | inl. (inr. star.) ↦ e ↦ sigma3_prop_member P hP t02. fin3_zero (fin3_differ fin3_two fin3_zero (refl (false. : Bool)))
        (subgroup_symmetry_transport G (sigma3_point_subgroup fin3_one) (sigma3_prop_subgroup P) e (sigma3_sym t02.)
          (refl fin3_one))
    | inl. (inl. (inr. star.)) ↦ e ↦ sigma3_prop_member P hP t01. fin3_zero (fin3_differ fin3_one fin3_zero (refl (false. : Bool)))
        (subgroup_symmetry_transport G (sigma3_point_subgroup fin3_two) (sigma3_prop_subgroup P) e (sigma3_sym t01.)
          (refl fin3_two))
    | inl. (inl. (inl. v)) ↦ match v [] ]

def bridge9w_decide (P : Type) (hP : isProp P) (i : Fin blind_nat_four)
  : OrbitRelation (symmetric_group three) (subgroups_gset (symmetric_group three)) (bridge9w_rep i) (sigma3_prop_subgroup P)
    → Decidable P
  ≔ let G ≔ symmetric_group three in let X ≔ subgroups_gset G in let SG ≔ Subgroups G in
    let S ≔ sigma3_prop_subgroup P in
    let W : Subgroups G → Type ≔ R ↦ Σ (USym G) (g ↦ Id SG (gset_usym_act G X g R) S) in
    match i [
    | inr. star. ↦ r ↦ inr. (p ↦ mere_rec (W (principal_subgroup G)) Empty empty_prop
        (w ↦ sigma3_not_trivial_mem t12. fin3_one (fin3_differ fin3_two fin3_one (refl (false. : Bool)))
          (subgroup_symmetry_transport G S (principal_subgroup G)
            (inverse SG (principal_subgroup G) S (bridge9w_fix (principal_subgroup G) S sigma3_trivial_normal (w .fst) (w .snd)))
            (sigma3_sym t12.) (involution_subgroup_has_t G (sigma3_sym t12.) sigma3_t12_involution P p)))
        r)
    | inl. (inr. star.) ↦ r ↦ inl. (mere_rec (W (alternating_subgroup (suc. zero.))) P hP
        (w ↦ sigma3_prop_member P hP cyc. fin3_zero (fin3_differ fin3_one fin3_zero (refl (false. : Bool)))
          (subgroup_symmetry_transport G (alternating_subgroup (suc. zero.)) S
            (bridge9w_fix (alternating_subgroup (suc. zero.)) S sigma3_alternating_normal (w .fst) (w .snd))
            (sigma3_sym cyc.) (sigma3_a3_mem_of_plus (sigma3_sym cyc.) sigma3_sign_cyc)))
        r)
    | inl. (inl. (inr. star.)) ↦ r ↦ inl. (mere_rec (W (group_full_subgroup G)) P hP
        (w ↦ sigma3_prop_member P hP t01. fin3_zero (fin3_differ fin3_one fin3_zero (refl (false. : Bool)))
          (subgroup_symmetry_transport G (group_full_subgroup G) S
            (bridge9w_fix (group_full_subgroup G) S sigma3_full_normal (w .fst) (w .snd))
            (sigma3_sym t01.) (full_subgroup_has_symmetry G (sigma3_sym t01.))))
        r)
    | inl. (inl. (inl. (inr. star.))) ↦ r ↦ inl. (mere_rec (W (sigma3_point_subgroup fin3_zero)) P hP
        (w ↦ bridge9w_point_member P hP (gset_usym_act G (standard_symmetric_gset three) (w .fst) fin3_zero)
          (bridge9w_T0_move (w .fst) S (w .snd)))
        r)
    | inl. (inl. (inl. (inl. v))) ↦ match v [] ]

def bridge_sub_sigma3_orbits_lem (E : blind_sub_sigma3_orbits) : ExcludedMiddle
  ≔ P hP ↦
    let G ≔ symmetric_group three in let X ≔ subgroups_gset G in
    let O ≔ Orbits G X in let F4 ≔ Fin blind_nat_four in
    let S ≔ sigma3_prop_subgroup P in
    let f : F4 → F4 ≔ i ↦ E .map (bridge9w_orb i) in
    let finj : PathReflecting F4 F4 f
      ≔ i j q ↦ bridge9w_reflect i j (equivalence_injective O F4 E (bridge9w_orb i) (bridge9w_orb j) q) in
    let w ≔ bsix_injection_full blind_nat_four f finj (E .map (orbit_of_point G X S)) in
    let p : Id O (orbit_of_point G X S) (bridge9w_orb (w .fst))
      ≔ equivalence_injective O F4 E (orbit_of_point G X S) (bridge9w_orb (w .fst)) (w .snd) in
    bridge9w_decide P hP (w .fst)
      (orbit_relation_from_path G X (bridge9w_rep (w .fst)) S
        (inverse O (orbit_of_point G X S) (bridge9w_orb (w .fst)) p))
