export "09-weyl"
export "bridge-04a-image-core"
export "../../../src/911-weyl-kernel"
export "../../../src/993-weyl-fixed-counterexample"
export "../../../src/918-ch9-text-claims"

{` Bridges for subgroups.tex sec:weyl and symmetry.tex 398/403 (blind file 09-weyl). `}

def bridge_def_weyl (G : Group) (S : Subgroups G) : Id Group (BlindWeyl G S) (weyl_group G S) ≔ refl (BlindWeyl G S)

def bridge_def_normalizer (G : Group) (S : Subgroups G) : Id Group (BlindNormalizer G S) (normalizer_group G S)
  ≔ refl (BlindNormalizer G S)

def bridge_def_normalizer_incl (G : Group) (S : Subgroups G)
  : Id (GroupHom (normalizer_group G S) G) (blind_normalizer_incl G S) (normalizer_inclusion G S)
  ≔ refl (blind_normalizer_incl G S)

{` p_G^H: both are maps into the component of X with the same projection. `}
def bridge_def_normalizer_proj (G : Group) (S : Subgroups G)
  : Id (GroupHom (normalizer_group G S) (weyl_group G S)) (weyl_projection G S) (blind_normalizer_proj G S)
  ≔ let N ≔ normalizer_group G S in let W ≔ weyl_group G S in
    let X ≔ BG N in let A ≔ GSet G in let a ≔ S .gset in
    let go ≔ hom_B N W (weyl_projection G S) in let gb ≔ hom_B N W (blind_normalizer_proj G S) in
    let L ≔ component_lift X (bg_connected N) A a (component_project X A a go) in
    refl (mkhom N W)
      (concat (BookPointedMap X (NativeComponent A a, component_point A a)) go L gb
        (inverse (BookPointedMap X (NativeComponent A a, component_point A a)) L go (component_lift_project X (bg_connected N) A a go))
        (component_lift_project X (bg_connected N) A a gb))

{` j_H: the blind map differs from ours only in the transitivity proofs. `}
def bridge_def_normalizer_j (G : Group) (S : Subgroups G)
  : Id (GroupHom (subgroup_group G S) (normalizer_group G S)) (normalizer_subgroup_hom G S) (blind_normalizer_j G S)
  ≔ let H ≔ subgroup_group G S in let N ≔ normalizer_group G S in
    let X ≔ BG H in let A ≔ ActionType G (subgroups_gset G) in let a : A ≔ (shape G, S) in
    let B ≔ BG G .carrier in
    let P ≔ BookPointedMap X (NativeComponent A a, component_point A a) in
    let g ≔ hom_B H N (normalizer_subgroup_hom G S) in
    let pj ≔ component_project X A a g in
    let bjp : BookPointedMap X (A, a) ≔ (blind_j_map G S, blind_j_point G S) in
    let hom : (u : X .carrier) → Id A (pj .fst u) (bjp .fst u)
      ≔ u ↦ (refl (u .fst),
              (refl (S .gset), refl (u .snd),
               is_transitive_prop (group_at G (u .fst)) (S .gset) (pj .fst u .snd .transitive) (bjp .fst u .snd .transitive))) in
    let x0 ≔ X .point in
    let lhs ≔ concat A a (pj .fst x0) (bjp .fst x0) (pj .snd) (hom x0) in
    let r : Id (Id B (shape G) (shape G)) (lhs .fst) (bjp .snd .fst)
      ≔ concat (Id B (shape G) (shape G)) (lhs .fst)
          (concat B (shape G) (shape G) (shape G) (pj .snd .fst) (hom x0 .fst)) (refl (shape G))
          (map_path_concat A B (t ↦ t .fst) a (pj .fst x0) (bjp .fst x0) (pj .snd) (hom x0))
          (concat_1p B (shape G) (shape G) (refl (shape G))) in
    let cond ≔ bridge9_sigma_set_path_eq B (y ↦ Subgroups (group_at G y)) (y ↦ subgroups_set (group_at G y))
      a (bjp .fst x0) lhs (bjp .snd) r in
    let hpath : Id (BookPointedMap X (A, a)) pj bjp
      ≔ equiv_inverse_map (Id (BookPointedMap X (A, a)) pj bjp) (PointedHomotopy X (A, a) pj bjp)
          (pointed_map_path_equiv X (A, a) pj bjp) (hom, cond) in
    let L ≔ component_lift X (bg_connected H) A a pj in
    refl (mkhom H N)
      (concat P g L (component_lift X (bg_connected H) A a bjp)
        (inverse P L g (component_lift_project X (bg_connected H) A a g))
        (refl (component_lift X (bg_connected H) A a) hpath))

{` Lemma at line 2141. `}
def bridge_weyl_incl_mono_proj_epi : blind_weyl_incl_mono_proj_epi
  ≔ G S ↦
    let N ≔ normalizer_group G S in let W ≔ weyl_group G S in
    (usym_injective_group_mono N G (normalizer_inclusion G S) (normalizer_inclusion_mono G S),
     transport (GroupHom N W) (IsGroupEpi N W) (weyl_projection G S) (blind_normalizer_proj G S)
       (bridge_def_normalizer_proj G S) (weyl_projection_epi G S))

def bridge9_ker_stmt (G : Group) (S : Subgroups G) (j : GroupHom (subgroup_group G S) (normalizer_group G S))
  (p : GroupHom (normalizer_group G S) (weyl_group G S)) : Type
  ≔ Σ (IsGroupMono (subgroup_group G S) (normalizer_group G S) j) (mj ↦
      Id (GroupMonos (normalizer_group G S)) (kernel (normalizer_group G S) (weyl_group G S) p) (subgroup_group G S, (j, mj)))

def bridge_weyl_ker_proj : blind_weyl_ker_proj
  ≔ G S ↦
    let H ≔ subgroup_group G S in let N ≔ normalizer_group G S in let W ≔ weyl_group G S in
    let ours : bridge9_ker_stmt G S (normalizer_subgroup_hom G S) (weyl_projection G S)
      ≔ (normalizer_subgroup_mono G S,
         inverse (GroupMonos N) (normalizer_subgroup_as_mono G S) (kernel N W (weyl_projection G S)) (weyl_kernel_mono_path G S)) in
    transport (GroupHom H N) (j ↦ bridge9_ker_stmt G S j (blind_normalizer_proj G S))
      (normalizer_subgroup_hom G S) (blind_normalizer_j G S) (bridge_def_normalizer_j G S)
      (transport (GroupHom N W) (p ↦ bridge9_ker_stmt G S (normalizer_subgroup_hom G S) p)
        (weyl_projection G S) (blind_normalizer_proj G S) (bridge_def_normalizer_proj G S) ours)

def bridge9_j_normal_stmt (G : Group) (S : Subgroups G) (j : GroupHom (subgroup_group G S) (normalizer_group G S)) : Type
  ≔ Σ (IsGroupMono (subgroup_group G S) (normalizer_group G S) j) (mj ↦
      Σ (NormalSubgroups (normalizer_group G S)) (Nn ↦
        Id (Subgroups (normalizer_group G S)) (Nn (shape (normalizer_group G S)))
          (mono_to_subgroup (normalizer_group G S) (subgroup_group G S, (j, mj)))))

def bridge_weyl_j_normal : blind_weyl_j_normal
  ≔ G S ↦
    transport (GroupHom (subgroup_group G S) (normalizer_group G S)) (bridge9_j_normal_stmt G S)
      (normalizer_subgroup_hom G S) (blind_normalizer_j G S) (bridge_def_normalizer_j G S)
      (normalizer_subgroup_mono G S, (normalizer_subgroup_normal_element G S, normalizer_subgroup_normal_element_underlying G S))

def bridge_weyl_incl_factor : blind_weyl_incl_factor
  ≔ G S ↦
    let H ≔ subgroup_group G S in let N ≔ normalizer_group G S in
    transport (GroupHom H N) (j ↦ Id (GroupHom H G) (subgroup_inclusion G S) (group_hom_compose H N G j (normalizer_inclusion G S)))
      (normalizer_subgroup_hom G S) (blind_normalizer_j G S) (bridge_def_normalizer_j G S)
      (inverse (GroupHom H G) (group_hom_compose H N G (normalizer_subgroup_hom G S) (normalizer_inclusion G S)) (subgroup_inclusion G S)
        (normalizer_inclusion_factor G S))

{` Text before lem:WGHisHfixofG/H and the map e. `}
def bridge_weyl_usym : blind_weyl_usym ≔ G S ↦ automorphism_group_usym_equiv (GSet G) (gset_groupoid G) (S .gset)

def bridge_def_weyl_e (G : Group) (S : Subgroups G) (f : Id (GSet G) (S .gset) (S .gset))
  : Id (InvariantMaps (subgroup_group G S) (gset_restrict (subgroup_group G S) G (subgroup_inclusion G S) (S .gset)))
      (blind_weyl_e G S f) (weyl_fixed_map G S f)
  ≔ refl (blind_weyl_e G S f)

{` lem:WGHisHfixofG/H: the blind (literal) statement is false (module 993: G = Σ_{ℕ⊔ℕ}, H the stabilizer of
   inl : ℕ → ℕ⊔ℕ, the H-fixed point "drop the first value" is not in the image of e; weyl_fixed_printed is
   blind_WGH_is_H_fix by definition). It holds when G/H is finite, and e is always an injection. `}
def bridge_WGH_is_H_fix_refuted : Not blind_WGH_is_H_fix ≔ weyl_fixed_printed_refuted

def bridge_WGH_is_H_fix_finite (G : Group) (S : Subgroups G) (hfin : IsFinite (gset_underlying G (S .gset)))
  : BookIsEquiv (USym (BlindWeyl G S))
      (InvariantMaps (subgroup_group G S) (gset_restrict (subgroup_group G S) G (subgroup_inclusion G S) (S .gset)))
      (ω ↦ blind_weyl_e G S (ω .fst))
  ≔ book_equivalence (USym (weyl_group G S))
      (InvariantMaps (subgroup_group G S) (gset_restrict (subgroup_group G S) G (subgroup_inclusion G S) (S .gset)))
      (weyl_usym_fixed_equiv_finite G S hfin) .equiv

def bridge_WGH_e_injective (G : Group) (S : Subgroups G)
  : IsEmbedding (Id (GSet G) (S .gset) (S .gset))
      (InvariantMaps (subgroup_group G S) (gset_restrict (subgroup_group G S) G (subgroup_inclusion G S) (S .gset)))
      (blind_weyl_e G S)
  ≔ weyl_fixed_map_injective G S

{` G/H ≔ coker(i_H) is X. `}
def bridge9_coker_inclusion_path (G : Group) (S : Subgroups G)
  : Id (GSet G) (cokernel (subgroup_group G S) G (subgroup_inclusion G S)) (S .gset)
  ≔ let H ≔ subgroup_group G S in let i ≔ subgroup_inclusion G S in
    map_path (Subgroups G) (GSet G) (T ↦ T .gset) (image_subgroup H G i) S
      (concat (Subgroups G) (image_subgroup H G i) (mono_to_subgroup G (subgroup_to_mono G S)) S
        (inverse (Subgroups G) (mono_to_subgroup G (subgroup_to_mono G S)) (image_subgroup H G i)
          (mono_subgroup_cokernel_path G H i (subgroup_inclusion_mono G S)))
        (subgroup_mono_roundtrip G S))

{` lem:aut-orbit (symmetry.tex 398). `}
def bridge9_aut_orbit_stmt (G : Group) (S : Subgroups G) (j : GroupHom (subgroup_group G S) (normalizer_group G S)) : Type
  ≔ let NG ≔ normalizer_group G S in
    Σ (IsGroupMono (subgroup_group G S) NG j) (mj ↦
    Σ (NormalSubgroups NG) (Nn ↦
    Σ (Id (Subgroups NG) (Nn (shape NG)) (mono_to_subgroup NG (subgroup_group G S, (j, mj)))) (_ ↦
      GroupIso (automorphism_group (GSet G) (gset_groupoid G) (cokernel (subgroup_group G S) G (subgroup_inclusion G S)))
        (normal_quotient_group NG Nn))))

def bridge_aut_orbit : blind_aut_orbit
  ≔ G S ↦
    let NG ≔ normalizer_group G S in
    let Nn ≔ normalizer_subgroup_normal_element G S in
    let Q ≔ normal_quotient_group NG Nn in
    let C ≔ automorphism_group (GSet G) (gset_groupoid G) (cokernel (subgroup_group G S) G (subgroup_inclusion G S)) in
    let α : Id Group C Q
      ≔ concat Group C (weyl_group G S) Q
          (map_path (GSet G) Group (Y ↦ automorphism_group (GSet G) (gset_groupoid G) Y)
            (cokernel (subgroup_group G S) G (subgroup_inclusion G S)) (S .gset) (bridge9_coker_inclusion_path G S))
          (group_path_from_iso (weyl_group G S) Q (aut_orbit_iso G S)) in
    transport (GroupHom (subgroup_group G S) NG) (bridge9_aut_orbit_stmt G S)
      (normalizer_subgroup_hom G S) (blind_normalizer_j G S) (bridge_def_normalizer_j G S)
      (normalizer_subgroup_mono G S,
       (Nn, (normalizer_subgroup_normal_element_underlying G S, group_path_iso_equiv C Q .map α)))

{` thm:fund-thm-homs (symmetry.tex 403). `}
def bridge_fund_thm_homs : blind_fund_thm_homs
  ≔ G G' f ↦
    let N ≔ kernel_normal_subgroup G G' f in
    let Q ≔ normal_quotient_group G N in
    let α : Id Group Q (BlindImage G G' f)
      ≔ concat Group Q (image_group G G' f) (BlindImage G G' f)
          (fundamental_theorem_homs_path G G' f)
          (inverse Group (BlindImage G G' f) (image_group G G' f)
            (group_path_from_iso (BlindImage G G' f) (image_group G G' f) (bridge9_aut_iso G G' f))) in
    (N, (kernel_normal_subgroup_is_kernel G G' f, group_path_iso_equiv Q (BlindImage G G' f) .map α))
