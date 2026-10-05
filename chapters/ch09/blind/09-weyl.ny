{` Blind statements for chapter 9: section "The Weyl group" (subgroups.tex) and the isomorphism theorems
   (symmetry.tex). The subgroup H is given by S = (X, pt_X, !) : Sub(G), with H its underlying group
   mkgroup(Σ_{y:BG} X(y), (sh_G, pt_X)) and i_H the first projection (so BH ≡ Σ_y X(y), as the book uses). `}
export "06-normal"

{` Transitivity of X relative to any base point y (the field of Sub(mkgroup(BG÷, y))). `}
def blind_transitive_at (G : Group) (X : GSet G) (t : IsTransitive G X) (y : BG G .carrier) : IsTransitive (group_at G y) X
  ≔ connected_action_type_transitive (group_at G y) X (transitive_action_type_connected G X t)

{` def:Weyl. W_G H ≔ Aut_{G-set}(X). `}
def BlindWeyl (G : Group) (S : Subgroups G) : Group ≔ automorphism_group (GSet G) (gset_groupoid G) (S .gset)

{` def:normalizer. N_G H ≔ Aut_{Σ_{y:BG} Sub(G)(y)}(sh_G, X, pt_X). `}
def BlindNormalizer (G : Group) (S : Subgroups G) : Group
  ≔ automorphism_group (ActionType G (BlindSubGSet G)) (action_type_groupoid G (BlindSubGSet G)) (shape G, S)

{` i_{N_G H} : Hom(N_G H, G), (y, Y, pt, !) ↦ y. `}
def blind_normalizer_incl (G : Group) (S : Subgroups G) : GroupHom (BlindNormalizer G S) G
  ≔ mkhom (BlindNormalizer G S) G ((u ↦ u .fst .fst), refl (shape G))

{` p_G^H : Hom(N_G H, W_G H), (y, Y, pt, !) ↦ (Y, !). `}
def blind_normalizer_proj (G : Group) (S : Subgroups G) : GroupHom (BlindNormalizer G S) (BlindWeyl G S)
  ≔ mkhom (BlindNormalizer G S) (BlindWeyl G S)
      (blind_component_map (ActionType G (BlindSubGSet G)) (GSet G) (shape G, S) (S .gset)
        (u ↦ u .snd .gset) (refl (S .gset)))

{` j_H : Hom(H, N_G H), (y, v) ↦ (y, X, v, !). `}
def blind_j_map (G : Group) (S : Subgroups G) (u : ActionType G (S .gset)) : ActionType G (BlindSubGSet G)
  ≔ (u .fst, (S .gset, u .snd, blind_transitive_at G (S .gset) (S .transitive) (u .fst)))

def blind_j_point (G : Group) (S : Subgroups G)
  : Id (ActionType G (BlindSubGSet G)) (shape G, S) (blind_j_map G S (shape G, S .point))
  ≔ (refl (shape G), (refl (S .gset), refl (S .point),
       is_transitive_prop G (S .gset) (S .transitive) (blind_transitive_at G (S .gset) (S .transitive) (shape G))))

def blind_normalizer_j (G : Group) (S : Subgroups G) : GroupHom (subgroup_group G S) (BlindNormalizer G S)
  ≔ mkhom (subgroup_group G S) (BlindNormalizer G S)
      (blind_into_component (ActionType G (S .gset)) (bg_connected (subgroup_group G S)) (shape G, S .point)
        (ActionType G (BlindSubGSet G)) (shape G, S) (blind_j_map G S) (blind_j_point G S))

{` Lemma (subgroups.tex:2141). i_G^H is a monomorphism and p_G^H an epimorphism. `}
def blind_weyl_incl_mono_proj_epi : Type
  ≔ (G : Group) (S : Subgroups G)
    → Product (BlindIsMono (BlindNormalizer G S) G (blind_normalizer_incl G S))
        (BlindIsEpi (BlindNormalizer G S) (BlindWeyl G S) (blind_normalizer_proj G S))

{` Lemma (subgroups.tex:2141). ker p_G^H = (H, j_H, !) in Mono(N_G H). The printed "(H, i_H, !)" does not have
   type Mono(N_G H) (marked "?for?" in the book); j_H is the evident intention. `}
def blind_weyl_ker_proj : Type
  ≔ (G : Group) (S : Subgroups G)
    → Σ (IsGroupMono (subgroup_group G S) (BlindNormalizer G S) (blind_normalizer_j G S)) (mj ↦
        Id (GroupMonos (BlindNormalizer G S))
          (blind_ker (BlindNormalizer G S) (BlindWeyl G S) (blind_normalizer_proj G S))
          (subgroup_group G S, (blind_normalizer_j G S, mj)))

{` Lemma (subgroups.tex:2141). j_H defines H as a normal subgroup of N_G H. `}
def blind_weyl_j_normal : Type
  ≔ (G : Group) (S : Subgroups G)
    → Σ (IsGroupMono (subgroup_group G S) (BlindNormalizer G S) (blind_normalizer_j G S)) (mj ↦
      Σ (BlindNor (BlindNormalizer G S)) (Nn ↦
        Id (Subgroups (BlindNormalizer G S)) (blind_nor_incl (BlindNormalizer G S) Nn)
          (mono_to_subgroup (BlindNormalizer G S) (subgroup_group G S, (blind_normalizer_j G S, mj)))))

{` Lemma (subgroups.tex:2141). i_H = i_G^H j_H in Hom(H, G). `}
def blind_weyl_incl_factor : Type
  ≔ (G : Group) (S : Subgroups G)
    → Id (GroupHom (subgroup_group G S) G) (subgroup_inclusion G S)
        (group_hom_compose (subgroup_group G S) (BlindNormalizer G S) G (blind_normalizer_j G S) (blind_normalizer_incl G S))

{` Text before lem:WGHisHfixofG/H: (pt_W = pt_W) is (X = X). `}
def blind_weyl_usym : Type
  ≔ (G : Group) (S : Subgroups G) → Equiv (USym (BlindWeyl G S)) (Id (GSet G) (S .gset) (S .gset))

{` lem:WGHisHfixofG/H. e : (X = X) → Π_{x:BH} X(Bi_H x), e(f)(y, v) ≔ f_y(v) (printed "f(y)"), defines an
   equivalence (pt_W = pt_W) ≃ (G/H)^H. `}
def blind_weyl_e (G : Group) (S : Subgroups G) (f : Id (GSet G) (S .gset) (S .gset))
  : InvariantMaps (subgroup_group G S) (gset_restrict (subgroup_group G S) G (subgroup_inclusion G S) (S .gset))
  ≔ u ↦ gset_path_transport G (S .gset) (S .gset) f (u .fst) (u .snd)

def blind_WGH_is_H_fix : Type
  ≔ (G : Group) (S : Subgroups G)
    → BookIsEquiv (USym (BlindWeyl G S))
        (InvariantMaps (subgroup_group G S) (gset_restrict (subgroup_group G S) G (subgroup_inclusion G S) (S .gset)))
        (ω ↦ blind_weyl_e G S (ω .fst))

{` lem:aut-orbit (symmetry.tex:398). The automorphism group of the G-set G/H ≔ coker(i_H) is isomorphic to
   N_G(H)/H (H normal in N_G(H) via j_H). `}
def blind_aut_orbit : Type
  ≔ (G : Group) (S : Subgroups G)
    → let NG ≔ BlindNormalizer G S in
      Σ (IsGroupMono (subgroup_group G S) NG (blind_normalizer_j G S)) (mj ↦
      Σ (BlindNor NG) (Nn ↦
      Σ (Id (Subgroups NG) (blind_nor_incl NG Nn) (mono_to_subgroup NG (subgroup_group G S, (blind_normalizer_j G S, mj)))) (_ ↦
        GroupIso (automorphism_group (GSet G) (gset_groupoid G) (blind_coker (subgroup_group G S) G (subgroup_inclusion G S)))
          (BlindQuotientGroup NG Nn))))

{` thm:fund-thm-homs (symmetry.tex:403). For f : Hom(G,G'), G/ker f ≅ im f (the map is TODO in the book; ker f is
   normal, given by some N : Nor(G) with i(N) = E(ker f)). `}
def blind_fund_thm_homs : Type
  ≔ (G G' : Group) (f : GroupHom G G')
    → Σ (BlindNor G) (N ↦
      Σ (Id (Subgroups G) (blind_nor_incl G N) (mono_to_subgroup G (blind_ker G G' f))) (_ ↦
        GroupIso (BlindQuotientGroup G N) (BlindImage G G' f)))
