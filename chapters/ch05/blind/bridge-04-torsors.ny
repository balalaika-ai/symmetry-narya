{` Bridges for chapter 5, blind file 04-torsors (torsors, restriction and induction, Cayley, Burnside, Fermat).
   The C₄-examples are in bridge-04b-c4. `}
export "04-torsors"
export "bridge-03-orbits"
export "../../../src/545-cayley-oversize"
export "../../../src/543-subtype-images"
export "../../../src/530-burnside-lemma"
export "../../../src/534-fermat-little-theorem"
export "../../../src/412-symmetric-group-two"
export "../../../src/223-constructed-circle"

{` def:Gtorsor. The blind base point differs from ours only in its (propositional) witness. `}
def bridge_def_torsors (G : Group) : Id Type (BlindTorsors G) (Torsors G) ≔ refl (Torsors G)

def bridge_torsor_path (G : Group) (S T : Torsors G) (p : Id (GSet G) (S .fst) (T .fst)) : Id (Torsors G) S T
  ≔ subtype_equal (GSet G) (X ↦ Mere (Id (GSet G) (principal_gset G) X)) (X ↦ mere_isprop (Id (GSet G) (principal_gset G) X)) S T p

def bridge_def_torsors_base (G : Group) : Id (Torsors G) (blind_torsors_base G) (principal_torsor G)
  ≔ bridge_torsor_path G (blind_torsors_base G) (principal_torsor G) (refl (principal_gset G))

def bridge_def_pathsp_torsor (G : Group) (y : BG G .carrier) : Id (Torsors G) (blind_pathsp_torsor G y) (bg_to_torsors G y)
  ≔ bridge_torsor_path G (blind_pathsp_torsor G y) (bg_to_torsors G y) (refl (gset_paths G y))

{` xca:torsor=free+transitive. `}
def bridge_torsor_free_transitive : blind_torsor_free_transitive
  ≔ G X ↦
    let ours ≔ torsor_iff_free_transitive G X in
    (h ↦ (bridge_def_gset_free G X .snd (ours .fst h .fst), ours .fst h .snd),
     u ↦ ours .snd (bridge_def_gset_free G X .fst (u .fst), u .snd))

{` Remark at actions.tex 2065. `}
def bridge_torsors_component : blind_torsors_component
  ≔ G ↦ canonical_inverse_equiv (NativeComponent (Coverings (BG G .carrier)) (universal_covering_over G)) (Torsors G)
      (torsors_coverings_component_equiv G)

def bridge_torsors_connected_groupoid : blind_torsors_connected_groupoid ≔ G ↦ (torsors_connected G, torsors_groupoid G)

def bridge_torsors_classify_G : blind_torsors_classify_G
  ≔ G c h ↦
    let T ≔ Torsors G in
    let b ≔ blind_torsors_base G in
    let p0 ≔ principal_torsor G in
    concat Group (mkgroup (T, b, c, h)) (mkgroup (T, p0, c, h)) G
      (refl ((x ↦ mkgroup (T, x, c, h)) : T → Group) (bridge_def_torsors_base G))
      (concat Group (mkgroup (T, p0, c, h)) (mkgroup (T, p0, torsors_connected G, h)) G
        (refl ((d ↦ mkgroup (T, p0, d, h)) : Connected T → Group) (connected_isprop T c (torsors_connected G)))
        (concat Group (mkgroup (T, p0, torsors_connected G, h)) (torsor_group G) G
          (refl ((k ↦ mkgroup (T, p0, torsors_connected G, k)) : isGroupoid T → Group) (isgroupoid_isprop T h (torsors_groupoid G)))
          (inverse Group G (torsor_group G) (torsor_group_path G))))

{` def:BG2TorsG, rem:pathsptransport, lem:pathsptransportiseq, lem:BGbytorsor. `}
def bridge_pathsp_tot_contractible : blind_pathsp_tot_contractible ≔ G y ↦ gset_paths_action_type_contractible G y

def bridge_pathsp_ap_transport : blind_pathsp_ap_transport ≔ G y z q x p ↦ gset_paths_transport G y z x q p

def bridge_pathsptransportiseq : blind_pathsptransportiseq ≔ G y z ↦ gset_paths_ap_is_equiv G y z

def bridge_BGbytorsor : blind_BGbytorsor
  ≔ G ↦ book_isequiv_homotopic (BG G .carrier) (Torsors G) (bg_to_torsors G) (blind_pathsp_torsor G)
      (y ↦ inverse (Torsors G) (blind_pathsp_torsor G y) (bg_to_torsors G y) (bridge_def_pathsp_torsor G y))
      (bg_to_torsors_is_equiv G)

{` def:restrictandinduce and its footnotes. `}
def bridge_def_restrict (G H : Group) (f : GroupHom G H) : Id (GSet H → GSet G) (blind_restrict G H f) (gset_restrict G H f)
  ≔ refl (gset_restrict G H f)

def bridge_def_induce (G H : Group) (f : GroupHom G H) : Id (GSet G → GSet H) (blind_induce G H f) (gset_induce G H f)
  ≔ refl (gset_induce G H f)

def bridge_def_induce_gset (G H : Group) (f : GroupHom G H) (X : GSet G) (w : BG H .carrier)
  : Id (GSet G) (blind_induce_gset G H f X w) (induced_sum_gset G H f X w)
  ≔ refl (induced_sum_gset G H f X w)

def bridge_tilde_is_restriction : blind_tilde_is_restriction ≔ G X x ↦ refl (stabilizer_tilde_gset G X x)

def bridge_induce_orbitset : blind_induce_orbitset
  ≔ G H f X w ↦
    let Y ≔ induced_sum_gset G H f X w in
    (compose_equiv (gset_induce G H f X w .fst) (SetTrunc (ActionType G Y)) (Orbits G Y)
       (transport_equiv (gset_induce G H f X w .fst) (SetTrunc (ActionType G Y)) (induce_as_set_trunc G H f X w))
       (native_equivalence (SetTrunc (ActionType G Y)) (Orbits G Y) (orbits_set_trunc_equiv G Y)),
     induced_sum_underlying_equiv G H f X w)

{` xca:why-setTrunc_f_!: Z → 1 and the trivial Z-set 1, with Z = mkgroup(S¹) for the constructed circle. `}
def bridge_why_setTrunc : blind_why_setTrunc
  ≔ (circle_group constructed_circle, (unit_group, (group_hom_to_unit (circle_group constructed_circle),
      (gset_trivial (circle_group constructed_circle) (Unit, unit_set),
       h ↦ why_set_trunc_not_set constructed_circle (h star.)))))

{` xca:adjunction-_!-^*, rem:^*-_!-as-(pre)image, rem:coinduced-Hset, rem:coinduced-subset, xca:adjunction-^*-_*. `}
def bridge_induce_iso : blind_induce_iso ≔ G H f hf X w ↦ induce_iso_equiv G H f hf X w

def bridge_adjunction_induce_restrict : blind_adjunction_induce_restrict ≔ G H f X Y ↦ induce_restrict_adjunction G H f X Y

def bridge_def_subtype_image (A B : Type) (f : A → B) : Id (Subtypes A → Subtypes B) (blind_subtype_image A B f) (subtype_image_exists A B f)
  ≔ refl (subtype_image_exists A B f)

def bridge_connected_predicates_constant : blind_connected_predicates_constant
  ≔ A hA P x y ↦ connected_subtype_constant A hA P x y

def bridge_def_coinduce (G H : Group) (f : GroupHom G H) : Id (GSet G → GSet H) (blind_coinduce G H f) (gset_coinduce G H f)
  ≔ refl (gset_coinduce G H f)

def bridge_coinduce_invariant : blind_coinduce_invariant
  ≔ G H f X w ↦ transport_equiv (gset_coinduce G H f X w .fst)
      (InvariantMaps G (z ↦ (Id (BG H .carrier) (hom_function G H f z) w → X z .fst,
        pi_set (Id (BG H .carrier) (hom_function G H f z) w) (_ ↦ X z .fst) (_ ↦ X z .snd))))
      (coinduced_invariant_maps G H f X w)

def bridge_def_subtype_coimage (A B : Type) (f : A → B)
  : Id (Subtypes A → Subtypes B) (blind_subtype_coimage A B f) (subtype_coinduced_forall A B f)
  ≔ refl (subtype_coinduced_forall A B f)

def bridge_coinduced_subset : blind_coinduced_subset
  ≔ A B f X b ↦ bridge_iff_of_equiv (subtype_coinduced_forall A B f X b .fst) ((u : BookFiber A B f b) → X (u .fst) .fst)
      (subtype_forall_preimage_equiv A B f X b)

def bridge_adjunction_restrict_coinduce : blind_adjunction_restrict_coinduce ≔ G H f X Y ↦ restrict_coinduce_adjunction G H f X Y

{` con:inducedtorsor. Ours f_! on torsors, repointed at the blind base points. `}
def bridge_inducedtorsor : blind_inducedtorsor
  ≔ G H f ↦
    let F ≔ induced_torsor G H f in
    let pt : Id (Torsors H) (blind_torsors_base H) (F (blind_torsors_base G))
      ≔ concat (Torsors H) (blind_torsors_base H) (principal_torsor H) (F (blind_torsors_base G))
          (bridge_def_torsors_base H)
          (concat (Torsors H) (principal_torsor H) (F (principal_torsor G)) (F (blind_torsors_base G))
            (induced_torsor_pointed G H f .snd)
            (refl F (inverse (Torsors G) (blind_torsors_base G) (principal_torsor G) (bridge_def_torsors_base G)))) in
    ((F, pt),
     (T ↦ refl (gset_induce G H f (T .fst)),
      funext (BG G .carrier) (_ ↦ Torsors H) (z ↦ F (blind_pathsp_torsor G z)) (z ↦ blind_pathsp_torsor H (hom_function G H f z))
        (z ↦ bridge_torsor_path H (F (blind_pathsp_torsor G z)) (blind_pathsp_torsor H (hom_function G H f z))
           (refl ((T ↦ T .fst) : Torsors H → GSet H)
             (happly (BG G .carrier) (_ ↦ Torsors H) (z' ↦ F (bg_to_torsors G z')) (z' ↦ bg_to_torsors H (hom_function G H f z'))
               (induced_torsor_naturality G H f) z)))))

{` lem:epifullyfaithful. `}
def bridge_epifullyfaithful : blind_epifullyfaithful ≔ G H f hs ↦ restriction_injective G H f hs

{` lem:allgpsarepermutationgps (Cayley) and the remark after it. The blind Bρ_G agrees with ours up to the
   (propositional) component witness; covering-ness transfers and gives the monomorphism. `}
def bridge_def_rho_B (G : Group) (z : BG G .carrier)
  : Id (BG (permutation_group (cayley_set G)) .carrier) (cayley_classifying_map G z) (blind_rho_B G z)
  ≔ component_path SetTypes (cayley_set G) (cayley_classifying_map G z) (blind_rho_B G z) (refl (gset_paths G z (shape G)))

def bridge_cayley_covering : blind_cayley_covering
  ≔ G ↦ transport (BG G .carrier → BG (permutation_group (cayley_set G)) .carrier)
      (F ↦ IsCovering (BG G .carrier) (BG (permutation_group (cayley_set G)) .carrier) F)
      (cayley_classifying_map G) (blind_rho_B G)
      (funext (BG G .carrier) (_ ↦ BG (permutation_group (cayley_set G)) .carrier) (cayley_classifying_map G) (blind_rho_B G)
        (bridge_def_rho_B G))
      (cayley_classifying_covering G)

def bridge_cayley : blind_cayley
  ≔ G ↦ covering_group_mono G (permutation_group (cayley_set G)) (blind_rho G) (bridge_cayley_covering G)

{` rem:CayleyOversize. `}
def bridge_def_PP (G : Group) : Id (GSet G) (blind_PP G) (cayley_pp_gset G) ≔ refl (cayley_pp_gset G)

def bridge_CayleyOversize : blind_CayleyOversize
  ≔ ((symmetric_group_finite three, symmetric_group_three_card),
     (G z ↦ refl (gset_paths G z (shape G)),
      G ↦ cayley_pp_invariant_equiv G))

{` xca:PP-fixed-permutations. Fixed elements of PP(sh_G) are the permutations with π(g g') = g π(g'). `}
def BridgePPS (G : Group) : SetTypes ≔ principal_gset G (shape G)

def BridgePP (G : Group) : Type ≔ Id SetTypes (BridgePPS G) (BridgePPS G)

def bridge_pp_fixed_to (G : Group) (π : BridgePP G) (h : IsFixedElement G (cayley_pp_gset G) π)
  : IsCayleyFixed G (set_path_permutation (BridgePPS G) (BridgePPS G) π)
  ≔ cayley_pp_fixed_to G π
      (g ↦ inverse (BridgePP G) π (gset_usym_act G (cayley_pp_gset G) g π) (fixed_element_fixed_by_all G (cayley_pp_gset G) π .map h g))

def bridge_pp_fixed_from (G : Group) (π : BridgePP G) (c : IsCayleyFixed G (set_path_permutation (BridgePPS G) (BridgePPS G) π))
  : IsFixedElement G (cayley_pp_gset G) π
  ≔ equiv_inverse_map (IsFixedElement G (cayley_pp_gset G) π)
      ((g : USym G) → Id (BridgePP G) π (gset_usym_act G (cayley_pp_gset G) g π))
      (fixed_element_fixed_by_all G (cayley_pp_gset G) π)
      (g ↦ inverse (BridgePP G) (gset_usym_act G (cayley_pp_gset G) g π) π (cayley_pp_fixed_from G π c g))

def bridge_PP_fixed_char : blind_PP_fixed_char ≔ G π ↦ (bridge_pp_fixed_to G π, bridge_pp_fixed_from G π)

{` Applying a composite of identifications is composing the applications. `}
def bridge_pp_apply_concat (G : Group) (π1 π2 : BridgePP G) (x : USym G)
  : Id (USym G) (blind_PP_apply G (concat SetTypes (BridgePPS G) (BridgePPS G) (BridgePPS G) π2 π1) x)
      (blind_PP_apply G π1 (blind_PP_apply G π2 x))
  ≔ let S ≔ BridgePPS G in
    concat (USym G) (blind_PP_apply G (concat SetTypes S S S π2 π1) x)
      (transport Type (A ↦ A) (USym G) (USym G) (concat Type (USym G) (USym G) (USym G) (π2 .fst) (π1 .fst)) x)
      (blind_PP_apply G π1 (blind_PP_apply G π2 x))
      (refl ((r : Id Type (USym G) (USym G)) ↦ transport Type (A ↦ A) (USym G) (USym G) r x)
        (map_path_concat SetTypes Type (T ↦ T .fst) S S S π2 π1))
      (transport_concat Type (A ↦ A) (USym G) (USym G) (USym G) (π2 .fst) (π1 .fst) x)

{` The PP-element of right multiplication by c, and its fixedness. `}
def bridge_pp_right (G : Group) (c : USym G) : BridgePP G
  ≔ set_types_path (BridgePPS G) (BridgePPS G) (cayley_right_mult G c .fst)

def bridge_pp_right_fixed (G : Group) (c : USym G) : IsFixedElement G (cayley_pp_gset G) (bridge_pp_right G c)
  ≔ bridge_pp_fixed_from G (bridge_pp_right G c) (cayley_right_mult G c .snd)

{` The literal statement is false (Σ₃): it would make τ σ = σ τ. `}
def bridge_PP_fixed_group_refuted (h : blind_PP_fixed_group) : Empty
  ≔ let G ≔ symmetric_group three in
    let e ≔ usym_unit G in
    let m ≔ usym_mul G in
    let ps ≔ bridge_pp_right G sigma3_sigma in
    let pt ≔ bridge_pp_right G sigma3_tau in
    let lit ≔ h G .snd ps pt (bridge_pp_right_fixed G sigma3_sigma) (bridge_pp_right_fixed G sigma3_tau) in
    let ul ≔ usym_abstract_laws G .unit_left in
    sigma3_tau_sigma_noncommuting
      (calc
        m sigma3_sigma sigma3_tau
        = m (m e sigma3_sigma) sigma3_tau
          by refl ((s ↦ m s sigma3_tau) : USym G → USym G) (inverse (USym G) (m e sigma3_sigma) sigma3_sigma (ul sigma3_sigma))
        = m (m e sigma3_sigma) (m e sigma3_tau)
          by refl (m (m e sigma3_sigma)) (inverse (USym G) (m e sigma3_tau) sigma3_tau (ul sigma3_tau))
        = blind_PP_apply G (concat SetTypes (BridgePPS G) (BridgePPS G) (BridgePPS G) pt ps) e
          by inverse (USym G) (blind_PP_apply G (concat SetTypes (BridgePPS G) (BridgePPS G) (BridgePPS G) pt ps) e)
               (m (m e sigma3_sigma) (m e sigma3_tau)) lit
        = m (m e sigma3_tau) sigma3_sigma by bridge_pp_apply_concat G ps pt e
        = m sigma3_tau sigma3_sigma
          by refl ((s ↦ m s sigma3_sigma) : USym G → USym G) (ul sigma3_tau) ∎)

{` The corrected statement: a bijection that reverses composition. `}
def BridgePPFixed (G : Group) : Type ≔ Σ (BridgePP G) (π ↦ IsFixedElement G (cayley_pp_gset G) π)

def bridge_pp_to_perms (G : Group) (u : BridgePPFixed G) : CayleyFixedPerms G
  ≔ (set_paths_transport_equiv (BridgePPS G) (BridgePPS G) .map (u .fst), bridge_pp_fixed_to G (u .fst) (u .snd))

def bridge_pp_from_perms (G : Group) (p : CayleyFixedPerms G) : BridgePPFixed G
  ≔ let E ≔ set_paths_transport_equiv (BridgePPS G) (BridgePPS G) in
    let π ≔ equiv_inverse_map (BridgePP G) (Equiv (USym G) (USym G)) E (p .fst) in
    (π, bridge_pp_fixed_from G π
          (transport (Equiv (USym G) (USym G)) (e ↦ IsCayleyFixed G (e .map)) (p .fst) (E .map π)
            (inverse (Equiv (USym G) (USym G)) (E .map π) (p .fst) (equiv_counit (BridgePP G) (Equiv (USym G) (USym G)) E (p .fst)))
            (p .snd)))

def bridge_pp_perms_equiv (G : Group) : Equiv (BridgePPFixed G) (CayleyFixedPerms G)
  ≔ let E ≔ set_paths_transport_equiv (BridgePPS G) (BridgePPS G) in
    quasi_inverse_equiv (BridgePPFixed G) (CayleyFixedPerms G) (bridge_pp_to_perms G) (bridge_pp_from_perms G)
      (u ↦ subtype_equal (BridgePP G) (π ↦ IsFixedElement G (cayley_pp_gset G) π)
         (π ↦ is_fixed_element_prop G (cayley_pp_gset G) π) (bridge_pp_from_perms G (bridge_pp_to_perms G u)) u
         (inverse (BridgePP G) (u .fst) (equiv_inverse_map (BridgePP G) (Equiv (USym G) (USym G)) E (E .map (u .fst)))
           (equiv_unit (BridgePP G) (Equiv (USym G) (USym G)) E (u .fst))))
      (p ↦ subtype_equal (Equiv (USym G) (USym G)) (e ↦ IsCayleyFixed G (e .map)) (e ↦ is_cayley_fixed_prop G (e .map))
         (bridge_pp_to_perms G (bridge_pp_from_perms G p)) p
         (equiv_counit (BridgePP G) (Equiv (USym G) (USym G)) E (p .fst)))

def bridge_PP_fixed_group_corrected : blind_PP_fixed_group_corrected
  ≔ G ↦
    (book_equivalence (BridgePPFixed G) (USym G)
       (compose_equiv (BridgePPFixed G) (CayleyFixedPerms G) (USym G) (bridge_pp_perms_equiv G)
         (native_equivalence (CayleyFixedPerms G) (USym G) (cayley_fixed_eval_equiv G))) .equiv,
     π1 π2 h1 h2 ↦
       concat (USym G) (blind_PP_apply G (concat SetTypes (BridgePPS G) (BridgePPS G) (BridgePPS G) π2 π1) (usym_unit G))
         (blind_PP_apply G π1 (blind_PP_apply G π2 (usym_unit G)))
         (usym_mul G (blind_PP_apply G π2 (usym_unit G)) (blind_PP_apply G π1 (usym_unit G)))
         (bridge_pp_apply_concat G π1 π2 (usym_unit G))
         (cayley_fixed_right_mult G (set_path_permutation (BridgePPS G) (BridgePPS G) π1) (bridge_pp_fixed_to G π1 h1)
           (blind_PP_apply G π2 (usym_unit G))))

{` lem:burnside. `}
def bridge_burnside : blind_burnside
  ≔ G hG X hX ↦ (g ↦ burnside_fixed_by_finite G X hX g,
                 (burnside_sum_finite G hG X hX, (burnside_orbits_finite G hG X hX, burnside_lemma G hG X hX)))

{` Fermat's little theorem. The blind power and truncated subtraction agree with ours. `}
def bridge_pow (n k : Nat) : Id Nat (blind_pow n k) (nat_power n k)
  ≔ match k [
  | zero. ↦ refl (suc. zero. : Nat)
  | suc. k ↦ refl ((x ↦ mul x n) : Nat → Nat) (bridge_pow n k) ]

def bridge_monus (m n : Nat) : Id Nat (blind_monus m n) (nat_truncated_sub m n)
  ≔ match m, n [
  | zero., zero. ↦ refl (zero. : Nat)
  | zero., suc. _ ↦ refl (zero. : Nat)
  | suc. m, zero. ↦ refl (suc. m : Nat)
  | suc. m, suc. n ↦ bridge_monus m n ]

def bridge_def_is_prime (p : Nat) : Id Type (BlindIsPrime p) (NatIsPrime p) ≔ refl (NatIsPrime p)

def bridge_fermat : blind_fermat
  ≔ p hp n ↦ transport Nat (k ↦ NatDivides p k) (nat_truncated_sub (nat_power n p) n) (blind_monus (blind_pow n p) n)
      (concat Nat (nat_truncated_sub (nat_power n p) n) (nat_truncated_sub (blind_pow n p) n) (blind_monus (blind_pow n p) n)
        (refl ((x ↦ nat_truncated_sub x n) : Nat → Nat) (inverse Nat (blind_pow n p) (nat_power n p) (bridge_pow n p)))
        (inverse Nat (blind_monus (blind_pow n p) n) (nat_truncated_sub (blind_pow n p) n) (bridge_monus (blind_pow n p) n)))
      (fermat_little_theorem p n hp)
