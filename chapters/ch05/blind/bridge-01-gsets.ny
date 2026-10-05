{` Bridges for chapter 5, blind file 01-gsets (section "Group actions (G-sets)"), part 1.
   The examples ex:S2-acts-on-C3, xca:AutC3 and xca:not-normal are in bridge-01b-examples. `}
export "01-gsets"
export "../../../src/560-gset-action-equivalences"
export "../../../src/561-gset-coverings-subsets"
export "../../../src/564-adjoint-principal-gsets"
export "../../../src/565-standard-symmetric-gsets"

{` Definition bridges: the blind G-sets, actions, maps, subsets, transitivity and normality are ours on the nose. `}
def bridge_def_gset (G : Group) : Id Type (BlindGSet G) (GSet G) ≔ refl (GSet G)

def bridge_def_underlying (G : Group) (X : GSet G) : Id Type (blind_underlying_set G X) (gset_underlying G X)
  ≔ refl (gset_underlying G X)

def bridge_def_act (G : Group) (X : GSet G) (z w : BG G .carrier) (p : Id (BG G .carrier) z w)
  : Id (X z .fst → X w .fst) (blind_act G X z w p) (gset_act G X z w p)
  ≔ refl (gset_act G X z w p)

def bridge_def_usym_act (G : Group) (X : GSet G) : Id (USym G → gset_underlying G X → gset_underlying G X)
    (blind_usym_act G X) (gset_usym_act G X)
  ≔ refl (gset_usym_act G X)

def bridge_def_triv (G : Group) (S : SetTypes) : Id (GSet G) (blind_triv G S) (gset_trivial G S) ≔ refl (gset_trivial G S)

def bridge_def_princ (G : Group) : Id (GSet G) (blind_princ G) (principal_gset G) ≔ refl (principal_gset G)

def bridge_def_pathsp (G : Group) (y : BG G .carrier) : Id (GSet G) (blind_pathsp G y) (gset_paths G y)
  ≔ refl (gset_paths G y)

def bridge_def_Ad (G : Group) : Id (GSet G) (blind_Ad G) (adjoint_gset G) ≔ refl (adjoint_gset G)

def bridge_def_hom_hg (H G : Group) : Id (GSet (product_group H G)) (blind_hom_hg H G) (group_hom_pair_gset H G)
  ≔ refl (group_hom_pair_gset H G)

def bridge_def_hom_g (H G : Group) : Id (GSet G) (blind_hom_g H G) (group_hom_gset H G) ≔ refl (group_hom_gset H G)

def bridge_def_hom (G : Group) (X Y : GSet G) : Id Type (BlindHomG G X Y) (GSetHom G X Y) ≔ refl (GSetHom G X Y)

def bridge_def_tot (G : Group) (X : GSet G) : Id Type (BlindTot G X) (ActionType G X) ≔ refl (ActionType G X)

def bridge_def_prop_set : Id SetTypes blind_prop_set gsubset_prop_set ≔ refl gsubset_prop_set

def bridge_def_subg (G : Group) (X : GSet G) : Id Type (BlindSubG G X) (GSubsets G X) ≔ refl (GSubsets G X)

def bridge_def_gsubset_underlying (G : Group) (X : GSet G) (P : GSubsets G X)
  : Id (GSet G) (blind_gsubset_underlying G X P) (gsubset_gset G X P)
  ≔ refl (gsubset_gset G X P)

def bridge_def_closed_subsets (G : Group) (X : GSet G) : Id Type (BlindClosedSubsets G X) (GSetClosedSubsets G X)
  ≔ refl (GSetClosedSubsets G X)

def bridge_def_action (G : Group) (S : SetTypes) : Id Type (BlindAction G S) (GroupActionOnSet G S)
  ≔ refl (GroupActionOnSet G S)

def bridge_def_finite_gset (G : Group) (X : GSet G) : Id Type (BlindIsFiniteGSet G X) (IsFiniteGSet G X)
  ≔ refl (IsFiniteGSet G X)

def bridge_def_gset_card (G : Group) (X : GSet G) (h : IsFiniteGSet G X)
  : Id Nat (blind_gset_card G X h) (gset_card G X h)
  ≔ refl (gset_card G X h)

def bridge_def_trans (G : Group) (X : GSet G) : Id Type (BlindIsTrans G X) (IsTransitive G X) ≔ refl (IsTransitive G X)

def bridge_def_gset_ev (G : Group) (X : GSet G) (z : BG G .carrier) (x : X z .fst)
  : Id (Id (GSet G) X X → X z .fst) (blind_gset_ev G X z x) (gset_path_eval G X X z x)
  ≔ refl (gset_path_eval G X X z x)

{` BlindIsNormal G X = istrans(X) × (ours). `}
def bridge_def_normal (G : Group) (X : GSet G)
  : Id Type (BlindIsNormal G X) (Product (IsTransitive G X) (IsNormalGSet G X))
  ≔ refl (Product (IsTransitive G X) (IsNormalGSet G X))

def bridge_def_action_in (G : Group) (A : Type) : Id Type (BlindActionIn G A) (ActionInType G A)
  ≔ refl (ActionInType G A)

def bridge_def_action_object (G : Group) (A : Type) (X : ActionInType G A)
  : Id A (blind_action_object G A X) (action_object G A X)
  ≔ refl (action_object G A X)

{` The blind ∞-group homomorphism G → Aut_A(a) is a one-field record around our pointed map. `}
def bridge_def_action_on (G : Group) (A : Type) (a : A) : Equiv (BlindActionOn G A a) (ActionOnElement G A a)
  ≔ quasi_inverse_equiv (BlindActionOn G A a) (ActionOnElement G A a)
      (h ↦ h .classifying_map)
      (k ↦ mk_infty_hom (group_to_infty_group G) (infty_automorphism_group A a) k)
      (h ↦ refl h) (k ↦ refl k)

def bridge_def_standard_action (G : Group) : Id (ActionInType G (BG G .carrier)) (blind_standard_action G) (standard_action G)
  ≔ refl (standard_action G)

def bridge_def_standard_sn_set (n : Nat)
  : Id (GSet (symmetric_group n)) (blind_standard_sn_set n) (standard_symmetric_gset n)
  ≔ refl (standard_symmetric_gset n)

def bridge_def_sn_decidable_subsets (n : Nat)
  : Id (GSet (symmetric_group n)) (blind_sn_decidable_subsets n) (decidable_subsets_gset n)
  ≔ refl (decidable_subsets_gset n)

{` def:Gset. `}
def bridge_act_is_equiv : blind_act_is_equiv
  ≔ G X z w p ↦ book_equivalence (X z .fst) (X w .fst) (gset_act_equiv G X z w p) .equiv

{` rem:G-set-vs-set-bundle. `}
def bridge_gset_vs_coverings : blind_gset_vs_coverings ≔ G ↦ gset_coverings_equiv G

{` def:principaltorsor / eq:pathsp. `}
def bridge_pathsp_transport : blind_pathsp_transport
  ≔ G y y' q z p ↦ transport_path_to (BG G .carrier) z y y' q p

def bridge_princ_underlying : blind_princ_underlying ≔ G ↦ principal_gset_underlying G

{` def:adjointrep / ft:adjoint-transport. `}
def bridge_Ad_transport : blind_Ad_transport ≔ G y z p q ↦ adjoint_gset_act G y z p q

def bridge_princ_transport : blind_princ_transport ≔ G y z p q ↦ gset_paths_act G (shape G) y z p q

def bridge_Ad_free_loops : blind_Ad_free_loops
  ≔ G C ↦ (book_equivalence (ActionType G (adjoint_gset G)) (C .carrier → BG G .carrier) (adjoint_free_loops_equiv G C),
           u ↦ adjoint_free_loops_base G C u)

{` ex:HomHGasGset. `}
def bridge_hom_hg_unfold : blind_hom_hg_unfold ≔ H G x y ↦ group_hom_pair_unfold H G x y

{` xca:HomZGvsAdG. `}
def bridge_HomZGvsAdG : blind_HomZGvsAdG ≔ C G ↦ adjoint_hom_z_path C G

{` def:map-of-Gsets. `}
def bridge_hom_g_set : blind_hom_g_set ≔ G X Y ↦ gset_hom_set G X Y

{` xca:equivariant-map-totalization. `}
def bridge_equivariant_map_totalization : blind_equivariant_map_totalization
  ≔ G X Y ↦ gset_hom_totalization_equiv G X Y

{` rem:map-of-Gsets. `}
def bridge_map_of_gsets_equivariant : blind_map_of_gsets_equivariant
  ≔ G X Y f z w x g ↦ gset_hom_natural G X Y f z w g x

def bridge_map_to_prop_invariant : blind_map_to_prop_invariant
  ≔ G X P z w x g ↦ gsubset_invariant_iff G X P z w g x

{` def:Gsubset / ft:SubTotX. `}
def bridge_subg_unfold : blind_subg_unfold ≔ G X ↦ gsubsets_unfold G X

def bridge_subg_set : blind_subg_set ≔ G X ↦ gsubsets_set G X

def bridge_subg_tot : blind_subg_tot ≔ G X ↦ gsubsets_total_equiv G X

{` xca:SubGX-closedSubXshG: our map and the blind evaluation agree (same subset, closure proofs in a proposition). `}
def bridge_subset_eval_agree (G : Group) (X : GSet G) (P : GSubsets G X)
  : Id (GSetClosedSubsets G X) (gsubsets_closed_equiv G X .map P) (blind_subset_eval G X P)
  ≔ subtype_equal (Subtypes (gset_underlying G X))
      (Q ↦ (x : gset_underlying G X) → Q x .fst → (g : USym G) → Q (gset_usym_act G X g x) .fst)
      (gset_closed_condition_prop G X) (gsubsets_closed_equiv G X .map P) (blind_subset_eval G X P)
      (refl (P (shape G)))

def bridge_SubGX_closedSubXshG : blind_SubGX_closedSubXshG
  ≔ G X ↦ book_isequiv_homotopic (GSubsets G X) (GSetClosedSubsets G X)
      (gsubsets_closed_equiv G X .map) (blind_subset_eval G X) (bridge_subset_eval_agree G X)
      (book_equivalence (GSubsets G X) (GSetClosedSubsets G X) (gsubsets_closed_equiv G X) .equiv)

{` xca:ptd-conn-to-comp. `}
def bridge_ptd_conn_to_comp : blind_ptd_conn_to_comp ≔ A B hA ↦ ptd_conn_to_comp_equiv A B hA

{` rem:GSet=SetHomG. Our equivalence sends X to (X(sh_G), gset_to_action G X) by refl; the compatibility uses
   the identification refl of underlying sets and gset_to_action_usym_act. `}
def bridge_gset_sethom_compatible (G : Group) (X : GSet G)
  : BlindActionCompatible G X (gset_action_equiv G .map X)
  ≔ let S ≔ X (shape G) in
    let tr : S .fst → S .fst ≔ transport SetTypes (T ↦ T .fst) S S (refl S) in
    (refl S,
     g x ↦
       concat (S .fst) (tr (gset_usym_act G X g x)) (gset_usym_act G X g x)
         (permutation_action S (usym_hom G (permutation_group S) (gset_to_action G X) g) (tr x))
         (transport_refl SetTypes (T ↦ T .fst) S (gset_usym_act G X g x))
         (concat (S .fst) (gset_usym_act G X g x)
            (permutation_action S (usym_hom G (permutation_group S) (gset_to_action G X) g) x)
            (permutation_action S (usym_hom G (permutation_group S) (gset_to_action G X) g) (tr x))
            (inverse (S .fst) (permutation_action S (usym_hom G (permutation_group S) (gset_to_action G X) g) x)
               (gset_usym_act G X g x) (gset_to_action_usym_act G X g x))
            (refl (permutation_action S (usym_hom G (permutation_group S) (gset_to_action G X) g))
               (inverse (S .fst) (tr x) x (transport_refl SetTypes (T ↦ T .fst) S x)))))

def bridge_GSet_SetHomG : blind_GSet_SetHomG ≔ G ↦ (gset_action_equiv G, X ↦ bridge_gset_sethom_compatible G X)

{` xca:Ad-triv-abelian, xca:Ad-princ-trivial. `}
def bridge_Ad_triv_abelian : blind_Ad_triv_abelian ≔ G ↦ adjoint_trivial_iff_abelian G

def bridge_Ad_princ_trivial : blind_Ad_princ_trivial ≔ G ↦ adjoint_principal_iff_trivial G

{` def:finite-G-set (footnote). `}
def bridge_finite_gset_everywhere : blind_finite_gset_everywhere ≔ G X ↦ gset_finite_everywhere_iff G X

{` Mere (Fin n = X(z)) as types vs as sets. `}
def bridge_n_element_to (G : Group) (X : GSet G) (n : Nat) (z : BG G .carrier)
  (h : Mere (Id Type (Fin n) (X z .fst))) : GSetNElementAt G X n z
  ≔ mere_rec (Id Type (Fin n) (X z .fst)) (GSetNElementAt G X n z) (mere_isprop (Id SetTypes (Fin n, fin_set n) (X z)))
      (p ↦ mere (Id SetTypes (Fin n, fin_set n) (X z)) (subtype_equal Type isSet isset_isprop (Fin n, fin_set n) (X z) p)) h

def bridge_n_element_from (G : Group) (X : GSet G) (n : Nat) (z : BG G .carrier)
  (h : GSetNElementAt G X n z) : Mere (Id Type (Fin n) (X z .fst))
  ≔ mere_rec (Id SetTypes (Fin n, fin_set n) (X z)) (Mere (Id Type (Fin n) (X z .fst))) (mere_isprop (Id Type (Fin n) (X z .fst)))
      (p ↦ mere (Id Type (Fin n) (X z .fst)) (refl ((T ↦ T .fst) : SetTypes → Type) p)) h

def bridge_n_element_gset_everywhere : blind_n_element_gset_everywhere
  ≔ G X n ↦
    (h z ↦ bridge_n_element_from G X n z
        (gset_n_element_everywhere_iff G X n .fst (bridge_n_element_to G X n (shape G) h) z),
     h ↦ bridge_n_element_from G X n (shape G)
        (gset_n_element_everywhere_iff G X n .snd (z ↦ bridge_n_element_to G X n z (h z))))

{` eq:Gset-trans-gen. `}
def bridge_trans_iff_surjective : blind_trans_iff_surjective ≔ G X ↦ transitive_surjective_iff G X

def bridge_trans_iff_all_z : blind_trans_iff_all_z ≔ G X ↦ transitive_everywhere_iff G X

def bridge_trans_iff_nonempty : blind_trans_iff_nonempty ≔ G X ↦ transitive_pairwise_iff G X

def bridge_empty_not_trans : blind_empty_not_trans ≔ G t ↦ gset_empty_not_transitive G t

{` lem:conistrans, lem:evisinjwhentransitive. `}
def bridge_conistrans : blind_conistrans ≔ G X ↦ transitive_iff_connected_covering G X

def bridge_evisinjwhentransitive : blind_evisinjwhentransitive
  ≔ G X Y z x t ↦ gset_hom_eval_injective G X Y z x t

{` xca:normal-action-equiv. `}
def bridge_normal_action_equiv : blind_normal_action_equiv
  ≔ G X t z x h z' x' ↦ normal_action_equiv G X t z x h z' x'

{` Example (actions.tex 669). `}
def bridge_standard_sn_set_transitive : blind_standard_sn_set_transitive ≔ m ↦ standard_symmetric_gset_transitive m

def bridge_sn_decidable_subsets_underlying : blind_sn_decidable_subsets_underlying
  ≔ n ↦ decidable_subsets_gset_underlying n
