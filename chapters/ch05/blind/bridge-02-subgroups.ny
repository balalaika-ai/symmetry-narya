{` Bridges for chapter 5, blind file 02-subgroups (section "Subgroups"), part 1: the general statements.
   The examples are in bridge-02b-subgroup-examples. `}
export "02-subgroups"
export "../../../src/508-stabilizer-subgroups"
export "../../../src/527-lagrange-counting"
export "../../../src/580-product-inclusions"
export "../../../src/562-gset-transitivity-finiteness"

{` def:set-of-subgroups. The blind Σ-type is our record SubgroupsSigma; translations with refl round trips. `}
def bridge_sub_from (G : Group) (S : BlindSubgroups G) : Subgroups G ≔ (S .fst, S .snd .fst, S .snd .snd)

def bridge_sub_to (G : Group) (S : Subgroups G) : BlindSubgroups G ≔ (S .gset, (S .point, S .transitive))

def bridge_def_subgroups (G : Group) : Equiv (BlindSubgroups G) (Subgroups G)
  ≔ quasi_inverse_equiv (BlindSubgroups G) (Subgroups G) (bridge_sub_from G) (bridge_sub_to G) (S ↦ refl S) (S ↦ refl S)

def bridge_def_subgroups_sigma (G : Group) : Id Type (BlindSubgroups G) (SubgroupsSigma G) ≔ refl (SubgroupsSigma G)

{` Underlying groups and inclusions only differ in the proof of connectedness of Tot(X) (a proposition). `}
def bridge_hominto_at (G : Group) (X : GSet G) (x : gset_underlying G X) (c : Connected (ActionType G X)) : BlindHomInto G
  ≔ (mkgroup (ActionType G X, (shape G, x), c, action_type_groupoid G X),
     mkhom (mkgroup (ActionType G X, (shape G, x), c, action_type_groupoid G X)) G ((u ↦ u .fst), refl (shape G)))

def bridge_hominto_conn (G : Group) (X : GSet G) (x : gset_underlying G X) (c c' : Connected (ActionType G X))
  : Id (BlindHomInto G) (bridge_hominto_at G X x c) (bridge_hominto_at G X x c')
  ≔ refl (bridge_hominto_at G X x) (connected_isprop (ActionType G X) c c')

def bridge_group_conn (G : Group) (X : GSet G) (x : gset_underlying G X) (c c' : Connected (ActionType G X))
  : Id Group (mkgroup (ActionType G X, (shape G, x), c, action_type_groupoid G X))
      (mkgroup (ActionType G X, (shape G, x), c', action_type_groupoid G X))
  ≔ refl ((d ↦ mkgroup (ActionType G X, (shape G, x), d, action_type_groupoid G X)) : Connected (ActionType G X) → Group)
      (connected_isprop (ActionType G X) c c')

def bridge_def_subgroup_group (G : Group) (S : BlindSubgroups G)
  : Id Group (blind_subgroup_group G S) (subgroup_group G (bridge_sub_from G S))
  ≔ bridge_group_conn G (S .fst) (S .snd .fst) (blind_tot_connected G (S .fst) (S .snd .snd))
      (transitive_action_type_connected G (S .fst) (S .snd .snd))

def bridge_forget_mono (G : Group) (m : GroupMonos G) : BlindHomInto G ≔ (m .fst, m .snd .fst)

def bridge_def_F0 (G : Group) (S : BlindSubgroups G)
  : Id (BlindHomInto G) (blind_F0 G S) (bridge_forget_mono G (subgroup_to_mono G (bridge_sub_from G S)))
  ≔ bridge_hominto_conn G (S .fst) (S .snd .fst) (blind_tot_connected G (S .fst) (S .snd .snd))
      (transitive_action_type_connected G (S .fst) (S .snd .snd))

{` The same with the monomorphism witness. `}
def BridgeConnMono (G : Group) (X : GSet G) (x : gset_underlying G X) : Type
  ≔ Σ (Connected (ActionType G X)) (c ↦ IsGroupMono (bridge_hominto_at G X x c .fst) G (bridge_hominto_at G X x c .snd))

def bridge_mono_at (G : Group) (X : GSet G) (x : gset_underlying G X) (u : BridgeConnMono G X x) : GroupMonos G
  ≔ (bridge_hominto_at G X x (u .fst) .fst, (bridge_hominto_at G X x (u .fst) .snd, u .snd))

def bridge_mono_conn (G : Group) (X : GSet G) (x : gset_underlying G X) (u v : BridgeConnMono G X x)
  : Id (GroupMonos G) (bridge_mono_at G X x u) (bridge_mono_at G X x v)
  ≔ refl (bridge_mono_at G X x)
      (subtype_equal (Connected (ActionType G X))
        (c ↦ IsGroupMono (bridge_hominto_at G X x c .fst) G (bridge_hominto_at G X x c .snd))
        (c ↦ is_group_mono_prop (bridge_hominto_at G X x c .fst) G (bridge_hominto_at G X x c .snd))
        u v (connected_isprop (ActionType G X) (u .fst) (v .fst)))

{` xca:group-Xx!. `}
def bridge_group_Xx : blind_group_Xx ≔ G X t ↦ (transitive_action_type_connected G X t, action_type_groupoid G X)

{` lem:SubGisset. `}
def bridge_SubGisset : blind_SubGisset
  ≔ G ↦ hlevel_two_to_set (BlindSubgroups G)
      (hlevel_equiv (suc. (suc. zero.)) (Subgroups G) (BlindSubgroups G)
        (canonical_inverse_equiv (BlindSubgroups G) (Subgroups G) (bridge_def_subgroups G))
        (set_to_hlevel_two (Subgroups G) (subgroups_set G)))

{` def:decidable-subgroup, def:typeofmono, def:triv-proper-Mono. `}
def bridge_def_subgroup_decidable (G : Group) (S : BlindSubgroups G)
  : Id Type (BlindSubgroupDecidable G S) (IsDecidableSubgroup G (bridge_sub_from G S))
  ≔ refl (IsDecidableSubgroup G (bridge_sub_from G S))

def bridge_def_ismono (H G : Group) (i : GroupHom H G) : Id Type (BlindIsMono H G i) (IsGroupMono H G i)
  ≔ refl (IsGroupMono H G i)

def bridge_ismono_prop : blind_ismono_prop ≔ H G i ↦ is_group_mono_prop H G i

def bridge_def_mono (G : Group) : Id Type (BlindMono G) (GroupMonos G) ≔ refl (GroupMonos G)

def bridge_def_mono_trivial (G : Group) (M : GroupMonos G)
  : Product (BlindMonoTrivial G M → IsTrivialMono G M) (IsTrivialMono G M → BlindMonoTrivial G M)
  ≔ (trivial_group_iff_path (M .fst) .snd, trivial_group_iff_path (M .fst) .fst)

def bridge_def_mono_proper (G : Group) (M : GroupMonos G) : Id Type (BlindMonoProper G M) (IsProperMono G M)
  ≔ refl (IsProperMono G M)

def bridge_def_subgroup_trivial (G : Group) (S : BlindSubgroups G)
  : Id Type (BlindSubgroupTrivial G S) (IsTrivialSubgroup G (bridge_sub_from G S))
  ≔ refl (IsTrivialSubgroup G (bridge_sub_from G S))

def bridge_def_subgroup_proper (G : Group) (S : BlindSubgroups G)
  : Id Type (BlindSubgroupProper G S) (IsProperSubgroup G (bridge_sub_from G S))
  ≔ refl (IsProperSubgroup G (bridge_sub_from G S))

def bridge_subgroup_trivial_iff : blind_subgroup_trivial_iff
  ≔ G S ↦
    let H ≔ subgroup_group G (bridge_sub_from G S) in
    (h ↦ concat Group (blind_subgroup_group G S) H trivial_group (bridge_def_subgroup_group G S) (trivial_group_path H h),
     p ↦ path_trivial_group H
       (concat Group H (blind_subgroup_group G S) trivial_group
         (inverse Group (blind_subgroup_group G S) H (bridge_def_subgroup_group G S)) p))

{` lem:SubG=MonoG. `}
def bridge_SubG_incl_mono : blind_SubG_incl_mono ≔ G S ↦ subgroup_inclusion_mono G (bridge_sub_from G S)

def bridge_F_agree (G : Group) (m : (S : BlindSubgroups G) → BlindIsMono (blind_subgroup_group G S) G (blind_subgroup_incl G S))
  (S : BlindSubgroups G)
  : Id (GroupMonos G) (subgroup_to_mono G (bridge_sub_from G S)) (blind_F G m S)
  ≔ bridge_mono_conn G (S .fst) (S .snd .fst)
      (transitive_action_type_connected G (S .fst) (S .snd .snd), subgroup_inclusion_mono G (bridge_sub_from G S))
      (blind_tot_connected G (S .fst) (S .snd .snd), m S)

def bridge_SubG_MonoG : blind_SubG_MonoG
  ≔ G m ↦
    let e ≔ compose_equiv (BlindSubgroups G) (Subgroups G) (GroupMonos G) (bridge_def_subgroups G)
        (native_equivalence (Subgroups G) (GroupMonos G) (subgroups_monos_equiv G)) in
    book_isequiv_homotopic (BlindSubgroups G) (GroupMonos G) (e .map) (blind_F G m) (bridge_F_agree G m)
      (book_equivalence (BlindSubgroups G) (GroupMonos G) e .equiv)

{` lem:setofsubgroups. `}
def bridge_setofsubgroups : blind_setofsubgroups ≔ G ↦ group_monos_set G

{` lem:E-preserves-symms. Ours is stated for monomorphisms; the blind M is only a pair (H, i), but equal to F(S). `}
def BridgePickedOut (G : Group) (g : USym G) (M : BlindHomInto G) : Type
  ≔ Mere (Σ (USym (M .fst)) (h ↦ Id (USym G) g (usym_hom (M .fst) G (M .snd) h)))

def bridge_E_preserves_symms : blind_E_preserves_symms
  ≔ G g S M e ↦
    let S' ≔ bridge_sub_from G S in
    let F ≔ bridge_forget_mono G (subgroup_to_mono G S') in
    let pM : Id (BlindHomInto G) M F
      ≔ concat (BlindHomInto G) M (blind_F0 G S) F e (bridge_def_F0 G S) in
    let ours ≔ mono_preserves_symmetries G S' (subgroup_to_mono G S') (refl (subgroup_to_mono G S')) g in
    (h ↦ transport (BlindHomInto G) (BridgePickedOut G g) F M (inverse (BlindHomInto G) M F pM) (ours .fst h),
     h ↦ ours .snd (transport (BlindHomInto G) (BridgePickedOut G g) M F pM h))

{` ex:prodinclismono. The blind inclusions are ours on the nose. `}
def bridge_def_prod_incl1 (G H : Group) : Id (GroupHom G (product_group G H)) (blind_prod_incl1 G H) (product_group_incl1 G H)
  ≔ refl (product_group_incl1 G H)

def bridge_def_prod_incl2 (G H : Group) : Id (GroupHom H (product_group G H)) (blind_prod_incl2 G H) (product_group_incl2 G H)
  ≔ refl (product_group_incl2 G H)

def bridge_prodinclismono : blind_prodinclismono ≔ G H ↦ (product_incl1_mono G H, product_incl2_mono G H)

def bridge_prod_incl1_usym : blind_prod_incl1_usym ≔ G H g ↦ product_incl1_usym G H g

def bridge_prod_incl1_covering : blind_prod_incl1_covering ≔ G H ↦ product_incl1_covering G H

{` ex:prodinclisGset. `}
def bridge_def_princ_proj2 (G G' : Group)
  : Id (GSet (product_group G G')) (blind_princ_proj2 G G') (product_proj2_principal_gset G G')
  ≔ refl (product_proj2_principal_gset G G')

def bridge_prodinclisGset_tot : blind_prodinclisGset_tot ≔ G G' ↦ product_proj2_total_equiv G G'

def bridge_prodinclisGset : blind_prodinclisGset
  ≔ G G' t ↦
    let K ≔ product_group G G' in
    let X ≔ product_proj2_principal_gset G G' in
    let S ≔ product_proj2_subgroup G G' in
    concat (BlindHomInto K) (G, product_group_incl1 G G') (bridge_forget_mono K (subgroup_to_mono K S))
      (blind_F0 K (X, (refl (shape G'), t)))
      (inverse (BlindHomInto K) (bridge_forget_mono K (subgroup_to_mono K S)) (G, product_group_incl1 G G')
        (refl (bridge_forget_mono K) (product_incl1_subgroup_path G G')))
      (bridge_hominto_conn K X (refl (shape G')) (transitive_action_type_connected K X (product_proj2_transitive G G'))
        (blind_tot_connected K X t))

{` con:lagrange, cor:lagrange-dep-sum, xca:lagrange (= xca:lagrange2). `}
def bridge_def_choice_map (G : Group) (S : BlindSubgroups G)
  : Id Type (BlindChoiceMap G S) (LagrangeChoice G (S .fst) (S .snd .fst))
  ≔ refl (LagrangeChoice G (S .fst) (S .snd .fst))

def bridge_lagrange_construction : blind_lagrange_construction
  ≔ G S c ↦ lagrange_construction G (bridge_sub_from G S) c

def bridge_lagrange_dep_sum : blind_lagrange_dep_sum ≔ G S c ↦ lagrange_dep_sum_equiv G (S .fst) (S .snd .fst) c

def bridge_lagrange : blind_lagrange
  ≔ G hG S hX ↦ (lagrange_subgroup_finite G (bridge_sub_from G S) hG hX, lagrange_cardinality G (bridge_sub_from G S) hG hX)
