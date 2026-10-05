export "906-associated-kernels"

{` Chapter 9 (subgroups.tex), sec:Weyl: def:Weyl and def:normalizer, the
   rewriting e : BN_GH ≃ Σ_{(y,Y) : BG × BW_GH} Y(y) of the running text, and
   the homomorphisms i_{N_GH}, p_G^H, j_H of the lemma at line 2141.

   Throughout, the subgroup H is given as S = (X, pt_X, !) : Sub(G); the
   corresponding monomorphism is subgroup_inclusion G S : Hom(H, G) with
   H = subgroup_group G S, BH ≡ Σ_{y:BG} X(y) at (sh_G, pt_X). We write the
   book's Σ_{(y,Y) : BG × BW_GH} Y(y) in the reshuffled order
   Σ_{Y : BW_GH} Σ_{y : BG} Y(y). `}

def weyl_group (G : Group) (S : Subgroups G) : Group
  ≔ automorphism_group (GSet G) (gset_groupoid G) (S .gset)

{` N_GH ≔ Aut_{Σ_{y:BG} Sub(G)(y)}(sh_G, X, pt_X): the stabilizer of S in the
   G-set Sub(G). `}
def normalizer_group (G : Group) (S : Subgroups G) : Group ≔ stabilizer_group G (subgroups_gset G) S

def normalizer_inclusion (G : Group) (S : Subgroups G) : GroupHom (normalizer_group G S) G
  ≔ stabilizer_inclusion G (subgroups_gset G) S

{` Lemma at line 2141, first part: i_{N_GH} is a monomorphism. `}
def normalizer_inclusion_mono (G : Group) (S : Subgroups G)
  : IsGroupMono (normalizer_group G S) G (normalizer_inclusion G S)
  ≔ stabilizer_inclusion_mono G (subgroups_gset G) S

{` The rewritten classifying type Σ_{Y : BW_GH} Σ_{y : BG} Y(y). `}
def NormalizerSigma (G : Group) (S : Subgroups G) : Type
  ≔ Σ (BG (weyl_group G S) .carrier) (Y ↦ ActionType G (Y .fst))

{` Transitivity of every Y in the component of X. `}
def weyl_component_transitive (G : Group) (S : Subgroups G) (Y : GSet G) (m : Mere (Id (GSet G) (S .gset) Y))
  (y : BG G .carrier) : IsTransitive (group_at G y) Y
  ≔ mere_rec (Id (GSet G) (S .gset) Y) (IsTransitive (group_at G y) Y) (is_transitive_prop (group_at G y) Y)
      (b ↦ transport (GSet G) (Z ↦ IsTransitive (group_at G y) Z) (S .gset) Y b
        (subgroup_transitive_move G (shape G) y (S .gset) (S .transitive)))
      m

def weyl_component_connected (G : Group) (S : Subgroups G) (Y : BG (weyl_group G S) .carrier)
  : Connected (ActionType G (Y .fst))
  ≔ transitive_action_type_connected G (Y .fst)
      (weyl_component_transitive G S (Y .fst) (Y .snd) (shape G))

{` e : BN_GH → Σ_Y Σ_y Y(y), (y, Y, pt_Y, !) ↦ (Y, !, y, pt_Y). `}
def normalizer_to_sigma (G : Group) (S : Subgroups G)
  (u : BG (normalizer_group G S) .carrier) : NormalizerSigma G S
  ≔ let A ≔ ActionType G (subgroups_gset G) in
    ((u .fst .snd .gset,
      mere_rec (Id A (shape G, S) (u .fst)) (Mere (Id (GSet G) (S .gset) (u .fst .snd .gset)))
        (mere_isprop (Id (GSet G) (S .gset) (u .fst .snd .gset)))
        (r ↦ mere (Id (GSet G) (S .gset) (u .fst .snd .gset))
          (map_path A (GSet G) (w ↦ w .snd .gset) (shape G, S) (u .fst) r))
        (u .snd)),
     (u .fst .fst, u .fst .snd .point))

{` The inverse: the transitivity of X gives, for β : X = Y and v : Y(y), a
   g : sh_G = y with g ·_X pt_X = β_y⁻¹(v), hence ‖(sh_G, X, pt_X) = (y, Y, v)‖. `}
def normalizer_sigma_path (G : Group) (S : Subgroups G) (Y : GSet G) (m : Mere (Id (GSet G) (S .gset) Y))
  (y : BG G .carrier) (v : Y y .fst) (b : Id (GSet G) (S .gset) Y)
  : Mere (Id (ActionType G (subgroups_gset G)) (shape G, S) (y, (Y, v, weyl_component_transitive G S Y m y)))
  ≔ let A ≔ ActionType G (subgroups_gset G) in
    let X ≔ S .gset in
    let Gy ≔ group_at G y in
    let T : Subgroups Gy ≔ (Y, v, weyl_component_transitive G S Y m y) in
    let eb ≔ gset_path_equiv G X Y .map b in
    let w ≔ equiv_inverse_map (X y .fst) (Y y .fst) (eb y) v in
    let connX ≔ transitive_action_type_connected G X (S .transitive) in
    mere_rec (Id (ActionType G X) (shape G, S .point) (y, w)) (Mere (Id A (shape G, S) (y, T)))
      (mere_isprop (Id A (shape G, S) (y, T)))
      (r ↦
        let ge ≔ action_type_path_equiv G X (shape G, S .point) (y, w) .map r in
        let g ≔ ge .fst in
        let gpt ≔ gset_act G X (shape G) y g (S .point) in
        let ex : Id (Y y .fst) (eb y .map gpt) v
          ≔ concat (Y y .fst) (eb y .map gpt) (eb y .map w) v (refl (eb y .map) (ge .snd))
              (equiv_counit (X y .fst) (Y y .fst) (eb y) v) in
        let E : Id (Subgroups Gy) (gset_act G (subgroups_gset G) (shape G) y g S) T
          ≔ concat (Subgroups Gy) (gset_act G (subgroups_gset G) (shape G) y g S) (subgroups_move G (shape G) y g S) T
              (subgroups_gset_act G (shape G) y g S)
              (subgroup_path Gy (subgroups_move G (shape G) y g S) T
                (pointed_gset_path Gy X Y gpt v eb ex)) in
        mere (Id A (shape G, S) (y, T)) (action_type_path G (subgroups_gset G) (shape G) y S T g E))
      (connX .snd (shape G, S .point) (y, w))

def sigma_to_normalizer (G : Group) (S : Subgroups G) (w : NormalizerSigma G S)
  : BG (normalizer_group G S) .carrier
  ≔ let A ≔ ActionType G (subgroups_gset G) in
    let Y ≔ w .fst .fst in let m ≔ w .fst .snd in let y ≔ w .snd .fst in let v ≔ w .snd .snd in
    ((y, (Y, v, weyl_component_transitive G S Y m y)),
     mere_rec (Id (GSet G) (S .gset) Y)
       (Mere (Id A (shape G, S) (y, (Y, v, weyl_component_transitive G S Y m y))))
       (mere_isprop (Id A (shape G, S) (y, (Y, v, weyl_component_transitive G S Y m y))))
       (normalizer_sigma_path G S Y m y v) m)

def normalizer_sigma_equiv (G : Group) (S : Subgroups G)
  : Equiv (BG (normalizer_group G S) .carrier) (NormalizerSigma G S)
  ≔ let A ≔ ActionType G (subgroups_gset G) in
    let BN ≔ BG (normalizer_group G S) .carrier in
    quasi_inverse_equiv BN (NormalizerSigma G S) (normalizer_to_sigma G S) (sigma_to_normalizer G S)
      (u ↦
        let y ≔ u .fst .fst in let T ≔ u .fst .snd in
        let Gy ≔ group_at G y in
        let tr ≔ weyl_component_transitive G S (T .gset) (normalizer_to_sigma G S u .fst .snd) y in
        component_path A (shape G, S) (sigma_to_normalizer G S (normalizer_to_sigma G S u)) u
          (map_path (Subgroups Gy) A (T' ↦ (y, T')) (T .gset, T .point, tr) T
            (map_path (IsTransitive Gy (T .gset)) (Subgroups Gy) (t ↦ (T .gset, T .point, t)) tr (T .transitive)
              (is_transitive_prop Gy (T .gset) tr (T .transitive)))))
      (w ↦
        let Y ≔ w .fst .fst in
        map_path (Mere (Id (GSet G) (S .gset) Y)) (NormalizerSigma G S) (m ↦ ((Y, m), w .snd))
          (normalizer_to_sigma G S (sigma_to_normalizer G S w) .fst .snd) (w .fst .snd)
          (mere_isprop (Id (GSet G) (S .gset) Y) (normalizer_to_sigma G S (sigma_to_normalizer G S w) .fst .snd)
            (w .fst .snd)))

{` p_G^H : Hom(N_GH, W_GH), Bp(y, Y, pt_Y, !) ≔ (Y, !), pointed by the
   component path with first component refl. `}
def weyl_projection_map (G : Group) (S : Subgroups G)
  : BG (normalizer_group G S) .carrier → BG (weyl_group G S) .carrier
  ≔ compose (BG (normalizer_group G S) .carrier) (NormalizerSigma G S) (BG (weyl_group G S) .carrier)
      (w ↦ w .fst) (normalizer_sigma_equiv G S .map)

def weyl_projection_point (G : Group) (S : Subgroups G)
  : Id (BG (weyl_group G S) .carrier) (shape (weyl_group G S)) (weyl_projection_map G S (shape (normalizer_group G S)))
  ≔ component_path (GSet G) (S .gset) (shape (weyl_group G S)) (weyl_projection_map G S (shape (normalizer_group G S)))
      (refl (S .gset))

def weyl_projection (G : Group) (S : Subgroups G) : GroupHom (normalizer_group G S) (weyl_group G S)
  ≔ mkhom (normalizer_group G S) (weyl_group G S) (weyl_projection_map G S, weyl_projection_point G S)

{` Lemma at line 2141: p_G^H is an epimorphism. Its fibers are those of the
   first projection of Σ_Y Σ_y Y(y), i.e. the (connected) action types of the
   Y in the component of X. `}
def weyl_projection_connected (G : Group) (S : Subgroups G)
  : IsConnectedHom (normalizer_group G S) (weyl_group G S) (weyl_projection G S)
  ≔ let BN ≔ BG (normalizer_group G S) .carrier in
    let BW ≔ BG (weyl_group G S) .carrier in
    let P : BW → Type ≔ Y ↦ ActionType G (Y .fst) in
    let e ≔ normalizer_sigma_equiv G S in
    Y0 ↦
      let fib_fst ≔ BookFiber (NormalizerSigma G S) BW (w ↦ w .fst) Y0 in
      let fib_p ≔ BookFiber BN BW (weyl_projection_map G S) Y0 in
      let c1 : Connected fib_fst
        ≔ connected_equiv (P Y0) fib_fst
            (canonical_inverse_equiv fib_fst (P Y0) (projection_book_fiber_equiv BW P Y0)) .map
            (weyl_component_connected G S Y0) in
      connected_equiv fib_fst fib_p
        (canonical_inverse_equiv fib_p fib_fst
          (preequivalence_fiber_equiv BN (NormalizerSigma G S) BW e (w ↦ w .fst) Y0)) .map c1

def weyl_projection_epi (G : Group) (S : Subgroups G)
  : IsGroupEpi (normalizer_group G S) (weyl_group G S) (weyl_projection G S)
  ≔ gepi_connected_fibers_epi (normalizer_group G S) (weyl_group G S) (weyl_projection G S)
      (weyl_projection_connected G S)

{` j_H : Hom(H, N_GH), Bj_H(y, v) ≔ (y, X, v, !) (the inverse rewriting at
   Y ≡ X). `}
def normalizer_subgroup_point (G : Group) (S : Subgroups G) (z : BG G .carrier) (a : S .gset z .fst)
  : ActionType G (subgroups_gset G)
  ≔ (z, (S .gset, a, weyl_component_transitive G S (S .gset) (shape (weyl_group G S) .snd) z))

def normalizer_subgroup_base (G : Group) (S : Subgroups G)
  : Id (ActionType G (subgroups_gset G)) (shape G, S) (normalizer_subgroup_point G S (shape G) (S .point))
  ≔ let tr ≔ weyl_component_transitive G S (S .gset) (shape (weyl_group G S) .snd) (shape G) in
    map_path (IsTransitive G (S .gset)) (ActionType G (subgroups_gset G)) (t ↦ (shape G, (S .gset, S .point, t)))
      (S .transitive) tr (is_transitive_prop G (S .gset) (S .transitive) tr)

def normalizer_subgroup_map (G : Group) (S : Subgroups G)
  : BG (subgroup_group G S) .carrier → BG (normalizer_group G S) .carrier
  ≔ u ↦ sigma_to_normalizer G S (shape (weyl_group G S), u)

def normalizer_subgroup_point_path (G : Group) (S : Subgroups G)
  : Id (BG (normalizer_group G S) .carrier) (shape (normalizer_group G S))
      (normalizer_subgroup_map G S (shape (subgroup_group G S)))
  ≔ component_path (ActionType G (subgroups_gset G)) (shape G, S) (shape (normalizer_group G S))
      (normalizer_subgroup_map G S (shape (subgroup_group G S))) (normalizer_subgroup_base G S)

def normalizer_subgroup_hom (G : Group) (S : Subgroups G) : GroupHom (subgroup_group G S) (normalizer_group G S)
  ≔ mkhom (subgroup_group G S) (normalizer_group G S) (normalizer_subgroup_map G S, normalizer_subgroup_point_path G S)

{` Lemma at line 2141, last part: i_H = i_{N_GH} ∘ j_H in Hom(H, G). `}
def normalizer_inclusion_factor (G : Group) (S : Subgroups G)
  : Id (GroupHom (subgroup_group G S) G)
      (group_hom_compose (subgroup_group G S) (normalizer_group G S) G (normalizer_subgroup_hom G S)
        (normalizer_inclusion G S))
      (subgroup_inclusion G S)
  ≔ let H ≔ subgroup_group G S in
    let B ≔ BG G .carrier in
    let comp ≔ group_hom_compose H (normalizer_group G S) G (normalizer_subgroup_hom G S) (normalizer_inclusion G S) in
    equiv_inverse_map (Id (GroupHom H G) comp (subgroup_inclusion G S))
      (PointedHomotopy (BG H) (BG G) (hom_B H G comp) (hom_B H G (subgroup_inclusion G S)))
      (group_hom_path_equiv H G comp (subgroup_inclusion G S))
      (u ↦ refl (u .fst),
       calc
         concat B (shape G) (shape G) (shape G) (hom_point H G comp) (refl (shape G))
         = hom_point H G comp by concat_p1 B (shape G) (shape G) (hom_point H G comp)
         = refl (shape G) by concat_p1 B (shape G) (shape G) (refl (shape G)) ∎)
