export "bridge-01-groups"
export "../../../src/419-cyclic-two-and-generated"
export "../../../src/415-natural-integer-permutations"

{` Bridges for group.tex lines 419-566 (blind file 01-groups.ny). `}

{` ex:groups (line 419). `}
def bridge_tg : Id Group (bridge_g blind_TG) trivial_group
  ≔ bridge_aut_any PropTypes blind_props_groupoid props_groupoid true_proposition

def bridge_sg (n : Nat) : Id Group (bridge_g (blind_SG n)) (symmetric_group n)
  ≔ bridge_aut SetTypes sets_groupoid (standard_set n)

def bridge_sg_set (S : SetTypes) : Id Group (bridge_g (blind_SG_set S)) (permutation_group S)
  ≔ bridge_aut SetTypes sets_groupoid S

def bridge_ex_true_loops_contractible : blind_ex_true_loops_contractible ≔ true_proposition_loops_contractible

def bridge_ex_trivgroup_contractible : blind_ex_trivgroup_contractible
  ≔ X h ↦ bridge_gpath_via blind_TG (blind_mkgroup X) trivial_group trivial_group bridge_tg (refl trivial_group)
      (concat Group (mkgroup (bridge_pcg X)) (contractible_group (X .fst) (X .snd .fst) h) trivial_group
        (classifying ≔ pcg_witnesses_unique (X .fst) (X .snd .fst) (X .snd .snd .fst)
          (contractible_connected (X .fst) h) (X .snd .snd .snd) (contractible_groupoid (X .fst) h))
        (contractible_group_trivial (X .fst) (X .snd .fst) h))

def bridge_ex_trivgroup_set : blind_ex_trivgroup_set
  ≔ S x ↦ bridge_gpath_via blind_TG (blind_Aut (S .fst) (blind_set_groupoid (S .fst) (S .snd)) x) trivial_group trivial_group
      bridge_tg (refl trivial_group)
      (concat Group (bridge_g (blind_Aut (S .fst) (blind_set_groupoid (S .fst) (S .snd)) x))
        (automorphism_group (S .fst) (set_is_groupoid (S .fst) (S .snd)) x) trivial_group
        (bridge_aut_any (S .fst) (blind_set_groupoid (S .fst) (S .snd)) (set_is_groupoid (S .fst) (S .snd)) x)
        (set_automorphism_group_trivial (S .fst) (S .snd) x))

{` A light equivalence BookFiniteSetsAt n ≃ FiniteSetsAt n (mere SetTypes
   paths versus mere Type paths), identity on the underlying set. `}
def bridge_finset_to (n : Nat) (u : BookFiniteSetsAt n) : FiniteSetsAt n
  ≔ (u .fst, mere_rec (Id SetTypes (Fin n, fin_set n) (u .fst)) (Mere (Id Type (Fin n) (u .fst .fst)))
      (mere_isprop (Id Type (Fin n) (u .fst .fst)))
      (p ↦ mere (Id Type (Fin n) (u .fst .fst)) (map_path SetTypes Type (S ↦ S .fst) (Fin n, fin_set n) (u .fst) p))
      (u .snd))

def bridge_finset_from (n : Nat) (u : FiniteSetsAt n) : BookFiniteSetsAt n
  ≔ (u .fst, mere_rec (Id Type (Fin n) (u .fst .fst)) (Mere (Id SetTypes (Fin n, fin_set n) (u .fst)))
      (mere_isprop (Id SetTypes (Fin n, fin_set n) (u .fst)))
      (p ↦ mere (Id SetTypes (Fin n, fin_set n) (u .fst)) (subtype_equal Type isSet isset_isprop (Fin n, fin_set n) (u .fst) p))
      (u .snd))

def bridge_finset_equiv (n : Nat) : Equiv (BookFiniteSetsAt n) (FiniteSetsAt n)
  ≔ quasi_inverse_equiv (BookFiniteSetsAt n) (FiniteSetsAt n) (bridge_finset_to n) (bridge_finset_from n)
      (u ↦ subtype_equal SetTypes (S ↦ Mere (Id SetTypes (Fin n, fin_set n) S)) (S ↦ mere_isprop (Id SetTypes (Fin n, fin_set n) S))
        (bridge_finset_from n (bridge_finset_to n u)) u (refl (u .fst)))
      (u ↦ subtype_equal SetTypes (S ↦ Mere (Id Type (Fin n) (S .fst))) (S ↦ mere_isprop (Id Type (Fin n) (S .fst)))
        (bridge_finset_to n (bridge_finset_from n u)) u (refl (u .fst)))

def bridge_finset_point (n : Nat)
  : Id (FiniteSetsAt n) (bridge_finset_equiv n .map (component_point SetTypes (standard_set n))) (blind_bn_finset n)
  ≔ subtype_equal SetTypes (S ↦ Mere (Id Type (Fin n) (S .fst))) (S ↦ mere_isprop (Id Type (Fin n) (S .fst)))
      (bridge_finset_equiv n .map (component_point SetTypes (standard_set n))) (blind_bn_finset n) (refl (standard_set n))

def bridge_ex_permgroup_classifying : blind_ex_permgroup_classifying
  ≔ n ↦ bridge_pointed_path (BookFiniteSetsAt n) (FiniteSetsAt n) (bridge_finset_equiv n)
      (component_point SetTypes (standard_set n)) (blind_bn_finset n) (bridge_finset_point n)

def bridge_ex_permgroup_finset_n : blind_ex_permgroup_finset_n
  ≔ n ↦ let B ≔ automorphism_group (FiniteSetsAt n) (blind_finsetn_groupoid n) (blind_bn_finset n) in
    bridge_gpath_via (blind_SG n) (blind_Aut (FiniteSetsAt n) (blind_finsetn_groupoid n) (blind_bn_finset n))
      (symmetric_group n) B (bridge_sg n)
      (concat Group (symmetric_group n)
        (automorphism_group (BookFiniteSetsAt n) (bg_groupoid (symmetric_group n)) (shape (symmetric_group n))) B
        (symmetric_group_finset_n_automorphism n)
        (automorphism_group_equiv_path_at (BookFiniteSetsAt n) (FiniteSetsAt n) (bg_groupoid (symmetric_group n))
          (blind_finsetn_groupoid n) (bridge_finset_equiv n) (shape (symmetric_group n)) (blind_bn_finset n)
          (bridge_finset_point n)))
      (bridge_aut (FiniteSetsAt n) (blind_finsetn_groupoid n) (blind_bn_finset n))

def bridge_ex_permgroup_universe : blind_ex_permgroup_universe
  ≔ n ↦ (universe_set_component_groupoid (Fin n) (fin_set n),
      bridge_gpath_via (blind_SG n)
        (blind_mkgroup (NativeComponent Type (Fin n), (blind_component_point Type (Fin n),
          (native_component_connected Type (Fin n), universe_set_component_groupoid (Fin n) (fin_set n)))))
        (symmetric_group n) (universe_set_automorphism_group (Fin n) (fin_set n)) (bridge_sg n)
        (symmetric_group_universe_path n) (refl (universe_set_automorphism_group (Fin n) (fin_set n))))

{` xca:group-example-details (line 512). `}
def bridge_xca_aut_prop_trivial : blind_xca_aut_prop_trivial
  ≔ P ↦ bridge_gpath_via blind_TG (blind_Aut PropTypes blind_props_groupoid P) trivial_group trivial_group bridge_tg
      (refl trivial_group)
      (concat Group (bridge_g (blind_Aut PropTypes blind_props_groupoid P)) (automorphism_group PropTypes props_groupoid P)
        trivial_group (bridge_aut_any PropTypes blind_props_groupoid props_groupoid P) (prop_automorphism_group_trivial P))

def bridge_xca_sg0_trivial : blind_xca_sg0_trivial
  ≔ bridge_gpath_via (blind_SG zero.) blind_TG (symmetric_group zero.) trivial_group (bridge_sg zero.)
      symmetric_group_zero_trivial bridge_tg

def bridge_xca_sg1_trivial : blind_xca_sg1_trivial
  ≔ bridge_gpath_via (blind_SG (suc. zero.)) blind_TG (symmetric_group (suc. zero.)) trivial_group (bridge_sg (suc. zero.))
      symmetric_group_one_trivial bridge_tg

def bridge_xca_sgfalse_trivial : blind_xca_sgfalse_trivial
  ≔ bridge_gpath_via (blind_SG_set (Empty, empty_set)) blind_TG empty_permutation_group trivial_group
      (bridge_sg_set (Empty, empty_set)) empty_permutation_group_trivial bridge_tg

def bridge_xca_aut_finset_sg : blind_xca_aut_finset_sg
  ≔ n ↦ bridge_gpath_via (blind_Aut FiniteSets finite_sets_groupoid (standard_finite_set n)) (blind_SG n)
      (finite_set_automorphism_group n) (symmetric_group n)
      (bridge_aut FiniteSets finite_sets_groupoid (standard_finite_set n)) (finite_set_automorphism_symmetric n) (bridge_sg n)

def bridge_xca_aut_nat_int : blind_xca_aut_nat_int
  ≔ bridge_gpath_via (blind_SG_set (Nat, nat_set)) (blind_SG_set (Int, int_set)) (permutation_group nat_set_type)
      (permutation_group int_set_type) (bridge_sg_set nat_set_type) nat_int_permutation_groups_path
      (bridge_sg_set int_set_type)

{` ex:cyclicgroups (line 522). The blind C_m = Aut_Cyc(bn m, s) is our
   cyclic_group_fin. The blind chain uses the book's Σ(X:Set)(X → X); ours
   uses Σ(X:Set)(X ≃ X) (Permutations). The two automorphism groups agree:
   Permutations ≃ Σ(u : Σ X (X → X)) isEquiv(u), a subtype. `}
def bridge_cg (n : Nat) : Id Group (bridge_g (blind_CG n)) (cyclic_group_fin n)
  ≔ bridge_aut Cycles cycles_groupoid (finite_fin_cycle n)

def BridgeEquivEndo : Type ≔ Σ BlindEndoSets (u ↦ isEquiv (u .fst .fst) (u .fst .fst) (u .snd))

def bridge_perm_endo : Equiv Permutations BridgeEquivEndo
  ≔ quasi_inverse_equiv Permutations BridgeEquivEndo (p ↦ ((p .fst, p .snd .map), p .snd .equiv))
      (u ↦ (u .fst .fst, (u .fst .snd, u .snd))) (p ↦ refl p) (u ↦ refl u)

def bridge_equiv_endo_groupoid : isGroupoid BridgeEquivEndo
  ≔ blind_groupoid_sigma BlindEndoSets (u ↦ isEquiv (u .fst .fst) (u .fst .fst) (u .snd)) blind_endo_sets_groupoid
      (u ↦ blind_set_groupoid (isEquiv (u .fst .fst) (u .fst .fst) (u .snd))
        (prop_is_set (isEquiv (u .fst .fst) (u .fst .fst) (u .snd)) (isequiv_isprop (u .fst .fst) (u .fst .fst) (u .snd))))

def bridge_cyclic_endo_path (n : Nat)
  : Id Group (cyclic_group_fin n)
      (automorphism_group BlindEndoSets blind_endo_sets_groupoid (blind_bn_set (suc. n), finite_fin_successor n .map))
  ≔ let p ≔ finite_fin_cycle n .fst in
    concat Group (cyclic_group_fin n) (automorphism_group Permutations permutations_groupoid p)
      (automorphism_group BlindEndoSets blind_endo_sets_groupoid (blind_bn_set (suc. n), finite_fin_successor n .map))
      (cycle_permutation_automorphism_path (finite_fin_cycle n))
      (concat Group (automorphism_group Permutations permutations_groupoid p)
        (automorphism_group BridgeEquivEndo bridge_equiv_endo_groupoid (bridge_perm_endo .map p))
        (automorphism_group BlindEndoSets blind_endo_sets_groupoid (blind_bn_set (suc. n), finite_fin_successor n .map))
        (automorphism_group_equiv_path Permutations BridgeEquivEndo permutations_groupoid bridge_equiv_endo_groupoid
          bridge_perm_endo p)
        (automorphism_group_subtype_path BlindEndoSets (u ↦ isEquiv (u .fst .fst) (u .fst .fst) (u .snd))
          (u ↦ isequiv_isprop (u .fst .fst) (u .fst .fst) (u .snd)) bridge_equiv_endo_groupoid blind_endo_sets_groupoid
          (bridge_perm_endo .map p)))

def bridge_degree_cover_path (C : CircleSignature) (n : Nat)
  : Id Group (automorphism_group (Coverings (C .carrier)) (coverings_groupoid (C .carrier)) (circle_degree_standard_cover C n))
      (automorphism_group (Coverings (C .carrier)) (coverings_groupoid (C .carrier))
        (circle_degree_cover C (suc. n) (blind_positive_suc n)))
  ≔ map_path (BookLt zero. (suc. n)) Group
      (h ↦ automorphism_group (Coverings (C .carrier)) (coverings_groupoid (C .carrier)) (circle_degree_cover C (suc. n) h))
      (lt_to_book zero. (suc. n) star.) (blind_positive_suc n) (book_lt_prop zero. (suc. n) (lt_to_book zero. (suc. n) star.) (blind_positive_suc n))

def bridge_ex_cyclicgroups_chain : blind_ex_cyclicgroups_chain
  ≔ C n ↦
    let E ≔ automorphism_group BlindEndoSets blind_endo_sets_groupoid (blind_bn_set (suc. n), finite_fin_successor n .map) in
    let A1 ≔ blind_Aut BlindEndoSets blind_endo_sets_groupoid (blind_bn_set (suc. n), finite_fin_successor n .map) in
    let cov ≔ circle_degree_cover C (suc. n) (blind_positive_suc n) in
    let A2 ≔ blind_Aut (Coverings (C .carrier)) (coverings_groupoid (C .carrier)) cov in
    let K ≔ automorphism_group (Coverings (C .carrier)) (coverings_groupoid (C .carrier)) cov in
    let Ks ≔ automorphism_group (Coverings (C .carrier)) (coverings_groupoid (C .carrier)) (circle_degree_standard_cover C n) in
    let P ≔ automorphism_group Permutations permutations_groupoid (finite_fin_cycle n .fst) in
    (bridge_gpath_via (blind_CG n) A1 (cyclic_group_fin n) E (bridge_cg n) (bridge_cyclic_endo_path n)
       (bridge_aut BlindEndoSets blind_endo_sets_groupoid (blind_bn_set (suc. n), finite_fin_successor n .map)),
     (bridge_gpath_via A1 A2 E K (bridge_aut BlindEndoSets blind_endo_sets_groupoid (blind_bn_set (suc. n), finite_fin_successor n .map))
        (concat Group E (cyclic_group_fin n) K (inverse Group (cyclic_group_fin n) E (bridge_cyclic_endo_path n))
          (concat Group (cyclic_group_fin n) P K (cycle_permutation_automorphism_path (finite_fin_cycle n))
            (concat Group P Ks K (inverse Group Ks P (degree_cover_permutation_group_path C n)) (bridge_degree_cover_path C n))))
        (bridge_aut (Coverings (C .carrier)) (coverings_groupoid (C .carrier)) cov),
      bridge_gpath_via A2 (blind_ZmodmZ C n) K (integers_mod_group C n)
        (bridge_aut (Coverings (C .carrier)) (coverings_groupoid (C .carrier)) cov)
        (concat Group K Ks (integers_mod_group C n) (inverse Group Ks K (bridge_degree_cover_path C n))
          (degree_cover_integers_mod_path C n))
        (bridge_aut_any (C .carrier → SetTypes) (blind_circle_families_groupoid C) (set_families_groupoid (C .carrier))
          (power_circle_family C n))))

def bridge_ex_cyclic_order_one : blind_ex_cyclic_order_one
  ≔ bridge_gpath_via (blind_CG zero.) blind_TG (cyclic_group_fin zero.) trivial_group (bridge_cg zero.)
      cyclic_group_one_trivial bridge_tg

def bridge_ex_cyclic_order_two : blind_ex_cyclic_order_two
  ≔ bridge_gpath_via (blind_CG (suc. zero.)) (blind_SG two) (cyclic_group_fin (suc. zero.)) (symmetric_group two)
      (bridge_cg (suc. zero.)) cyclic_two_symmetric_two_path (bridge_sg two)

def bridge_ex_cyclic_card : blind_ex_cyclic_card
  ≔ n ↦ mere (Id Type (Fin (suc. n)) (BlindUSym (blind_CG n)))
      (inverse Type (USym (cyclic_group_fin n)) (Fin (suc. n))
        (ua (USym (cyclic_group_fin n)) (Fin (suc. n)) (cyclic_group_fin_usym_equiv n)))

def bridge_ex_symmetric_card : blind_ex_symmetric_card
  ≔ n ↦ mere (Id Type (Fin (factorial n)) (BlindUSym (blind_SG n)))
      (inverse Type (USym (symmetric_group n)) (Fin (factorial n))
        (ua (USym (symmetric_group n)) (Fin (factorial n))
          (compose_equiv (USym (symmetric_group n)) (Equiv (Fin n) (Fin n)) (Fin (factorial n))
            (symmetric_group_usym_equiv n) (fin_automorphisms_equiv n))))
