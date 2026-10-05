export "507-subgroups-monos-equiv"

{` Chapter 5, ex:prodinclismono and ex:prodinclisGset: the inclusions of a
   factor into a product of groups are monomorphisms, and the first
   inclusion corresponds to the (G × G')-set P_{G'} ∘ proj_2. The inclusions
   are chapter 4's product_group_incl1/2 (Bi_G(z) = (z, sh_H), pointed by refl). `}

{` The preimage of (z, t) under Bi_G is Σ_{z'} (z = z') × (t = sh_H), which
   contracts away to the set t = sh_H (book footnote): Bi_G is a covering. `}
def product_incl1_fiber_equiv (G H : Group) (zt : BG (product_group G H) .carrier)
  : Equiv (BookFiber (BG G .carrier) (BG (product_group G H) .carrier) (z ↦ (z, shape H)) zt)
      (Id (BG H .carrier) (zt .snd) (shape H))
  ≔ let A ≔ BG G .carrier in
    let B ≔ BG H .carrier in
    let P ≔ BG (product_group G H) .carrier in
    let F ≔ BookFiber A P (z ↦ (z, shape H)) zt in
    let S ≔ Σ A (z' ↦ Product (Id A (zt .fst) z') (Id B (zt .snd) (shape H))) in
    compose_equiv F S (Id B (zt .snd) (shape H))
      (family_equiv A (z' ↦ Id P zt (z', shape H)) (z' ↦ Product (Id A (zt .fst) z') (Id B (zt .snd) (shape H)))
        (z' ↦ quasi_inverse_equiv (Id P zt (z', shape H)) (Product (Id A (zt .fst) z') (Id B (zt .snd) (shape H)))
          (r ↦ (r .fst, r .snd)) (pq ↦ (pq .fst, pq .snd)) (r ↦ refl r) (pq ↦ refl pq)))
      (contract_away_simple A (zt .fst) (_ ↦ Id B (zt .snd) (shape H)))

def product_incl1_covering (G H : Group)
  : IsCovering (BG G .carrier) (BG (product_group G H) .carrier) (z ↦ (z, shape H))
  ≔ zt ↦ hlevel_two_to_set (BookFiber (BG G .carrier) (BG (product_group G H) .carrier) (z ↦ (z, shape H)) zt)
      (hlevel_equiv (suc. (suc. zero.)) (Id (BG H .carrier) (zt .snd) (shape H))
        (BookFiber (BG G .carrier) (BG (product_group G H) .carrier) (z ↦ (z, shape H)) zt)
        (canonical_inverse_equiv (BookFiber (BG G .carrier) (BG (product_group G H) .carrier) (z ↦ (z, shape H)) zt)
          (Id (BG H .carrier) (zt .snd) (shape H)) (product_incl1_fiber_equiv G H zt))
        (set_to_hlevel_two (Id (BG H .carrier) (zt .snd) (shape H)) (bg_groupoid H (zt .snd) (shape H))))

def product_incl1_mono (G H : Group) : IsGroupMono G (product_group G H) (product_group_incl1 G H)
  ≔ covering_group_mono G (product_group G H) (product_group_incl1 G H) (product_incl1_covering G H)

{` USym i_G maps g to (g, refl_{sh_H}). `}
def product_incl1_usym (G H : Group) (g : USym G)
  : Id (USym (product_group G H)) (usym_hom G (product_group G H) (product_group_incl1 G H) g) (g, refl (shape H))
  ≔ loop_conjugate_at_refl (BG (product_group G H) .carrier) (shape G, shape H) (g, refl (shape H))

def product_incl2_fiber_equiv (G H : Group) (zt : BG (product_group G H) .carrier)
  : Equiv (BookFiber (BG H .carrier) (BG (product_group G H) .carrier) (z ↦ (shape G, z)) zt)
      (Id (BG G .carrier) (zt .fst) (shape G))
  ≔ let A ≔ BG G .carrier in
    let B ≔ BG H .carrier in
    let P ≔ BG (product_group G H) .carrier in
    let F ≔ BookFiber B P (z ↦ (shape G, z)) zt in
    let S ≔ Σ B (z' ↦ Product (Id B (zt .snd) z') (Id A (zt .fst) (shape G))) in
    compose_equiv F S (Id A (zt .fst) (shape G))
      (family_equiv B (z' ↦ Id P zt (shape G, z')) (z' ↦ Product (Id B (zt .snd) z') (Id A (zt .fst) (shape G)))
        (z' ↦ quasi_inverse_equiv (Id P zt (shape G, z')) (Product (Id B (zt .snd) z') (Id A (zt .fst) (shape G)))
          (r ↦ (r .snd, r .fst)) (pq ↦ (pq .snd, pq .fst)) (r ↦ refl r) (pq ↦ refl pq)))
      (contract_away_simple B (zt .snd) (_ ↦ Id A (zt .fst) (shape G)))

def product_incl2_covering (G H : Group)
  : IsCovering (BG H .carrier) (BG (product_group G H) .carrier) (z ↦ (shape G, z))
  ≔ zt ↦ hlevel_two_to_set (BookFiber (BG H .carrier) (BG (product_group G H) .carrier) (z ↦ (shape G, z)) zt)
      (hlevel_equiv (suc. (suc. zero.)) (Id (BG G .carrier) (zt .fst) (shape G))
        (BookFiber (BG H .carrier) (BG (product_group G H) .carrier) (z ↦ (shape G, z)) zt)
        (canonical_inverse_equiv (BookFiber (BG H .carrier) (BG (product_group G H) .carrier) (z ↦ (shape G, z)) zt)
          (Id (BG G .carrier) (zt .fst) (shape G)) (product_incl2_fiber_equiv G H zt))
        (set_to_hlevel_two (Id (BG G .carrier) (zt .fst) (shape G)) (bg_groupoid G (zt .fst) (shape G))))

def product_incl2_mono (G H : Group) : IsGroupMono H (product_group G H) (product_group_incl2 G H)
  ≔ covering_group_mono H (product_group G H) (product_group_incl2 G H) (product_incl2_covering G H)

{` ex:prodinclisGset. The (G × G')-set P_{G'} ∘ proj_2, pointed by refl_{sh_{G'}}. `}
def product_proj2_principal_gset (G H : Group) : GSet (product_group G H)
  ≔ zt ↦ principal_gset H (zt .snd)

def product_proj2_total_equiv (G H : Group)
  : Equiv (ActionType (product_group G H) (product_proj2_principal_gset G H)) (BG G .carrier)
  ≔ let A ≔ BG G .carrier in
    let B ≔ BG H .carrier in
    let T ≔ ActionType (product_group G H) (product_proj2_principal_gset G H) in
    quasi_inverse_equiv T A (u ↦ u .fst .fst) (z ↦ ((z, shape H), refl (shape H)))
      (u ↦ J B (shape H) (w p ↦ Id T ((u .fst .fst, shape H), refl (shape H)) ((u .fst .fst, w), p))
             (refl ((u .fst .fst, shape H), refl (shape H))) (u .fst .snd) (u .snd))
      (z ↦ refl z)

def product_proj2_transitive (G H : Group) : IsTransitive (product_group G H) (product_proj2_principal_gset G H)
  ≔ connected_action_type_transitive (product_group G H) (product_proj2_principal_gset G H)
      (connected_equiv (BG G .carrier) (ActionType (product_group G H) (product_proj2_principal_gset G H))
        (canonical_inverse_equiv (ActionType (product_group G H) (product_proj2_principal_gset G H)) (BG G .carrier)
          (product_proj2_total_equiv G H))
        .map (bg_connected G))

def product_proj2_subgroup (G H : Group) : Subgroups (product_group G H)
  ≔ (product_proj2_principal_gset G H, refl (shape H), product_proj2_transitive G H)

{` F(P_{G'} ∘ proj_2, refl) = (G, i_1) in Mono(G × G'): the equivalence
   φ : Tot ≃ BG is pointed by refl and fst = i_1 ∘ φ as pointed maps. `}
def product_proj2_pointed_equiv (G H : Group)
  : BookPointedEquiv (BG (subgroup_group (product_group G H) (product_proj2_subgroup G H))) (BG G)
  ≔ ((u ↦ u .fst .fst, refl (shape G)),
     book_equivalence (ActionType (product_group G H) (product_proj2_principal_gset G H)) (BG G .carrier)
       (product_proj2_total_equiv G H) .equiv)

def product_proj2_homotopy (G H : Group)
  : PointedHomotopy (BG (subgroup_group (product_group G H) (product_proj2_subgroup G H))) (BG (product_group G H))
      (book_pointed_compose (BG (subgroup_group (product_group G H) (product_proj2_subgroup G H))) (BG G) (BG (product_group G H))
        (product_proj2_pointed_equiv G H .fst) (hom_B G (product_group G H) (product_group_incl1 G H)))
      (hom_B (subgroup_group (product_group G H) (product_proj2_subgroup G H)) (product_group G H)
        (subgroup_inclusion (product_group G H) (product_proj2_subgroup G H)))
  ≔ let P ≔ BG (product_group G H) .carrier in
    let o : P ≔ (shape G, shape H) in
    (u ↦ (refl (u .fst .fst), u .snd),
     concat (Id P o o) (concat P o o o (concat P o o o (refl o) (refl o)) (refl o)) (concat P o o o (refl o) (refl o)) (refl o)
       (concat_p1 P o o (concat P o o o (refl o) (refl o))) (concat_p1 P o o (refl o)))

def product_incl1_monomorphism (G H : Group) : GroupMonos (product_group G H)
  ≔ (G, (product_group_incl1 G H, product_incl1_mono G H))

def product_incl1_subgroup_path (G H : Group)
  : Id (GroupMonos (product_group G H)) (subgroup_to_mono (product_group G H) (product_proj2_subgroup G H))
      (product_incl1_monomorphism G H)
  ≔ let K ≔ product_group G H in
    let S ≔ product_proj2_subgroup G H in
    let B ≔ BG K in
    map_path (MonoData K) (GroupMonos K) (mono_data_to_mono K)
      (mono_to_mono_data K (subgroup_to_mono K S)) (mono_to_mono_data K (product_incl1_monomorphism G H))
      (subtype_equal (PointedMapsOver B)
        (w ↦ Product (Product (Connected (w .fst .carrier)) (isGroupoid (w .fst .carrier)))
          (IsEmbedding (Loop (w .fst)) (USym K) (loops_map (w .fst) B (w .snd))))
        (mono_data_prop K)
        (mono_to_mono_data K (subgroup_to_mono K S)) (mono_to_mono_data K (product_incl1_monomorphism G H))
        (pointed_over_path B (BG (subgroup_group K S)) (BG G) (hom_B (subgroup_group K S) K (subgroup_inclusion K S))
          (hom_B G K (product_group_incl1 G H)) (product_proj2_pointed_equiv G H) (product_proj2_homotopy G H)))
