export "910-weyl-normalizer"
export "1720-blass-counting"
export "562-gset-transitivity-finiteness"

{` Chapter 9 (subgroups.tex), lem:WGHisHfixofG/H: the map
   e : (X = X) → Π_{x:BH} X(Bi_H x), e(f)(y, v) ≔ f_y(v), from the symmetries
   of the shape of W_GH to the H-fixed points (G/H)^H.

   Deviation (the lemma is false as printed for infinite groups): the
   book's argument identifies Π_y (X(y) = X(y)) with Π_{(y,v)} X(y), i.e. it
   treats every G-map X → X as an automorphism. For transitive X every
   G-map X → X is surjective, but it need not be injective: for the
   Baumslag-Solitar group G = BS(1,2) = ⟨a, t | t a t⁻¹ = a²⟩ and H = ⟨a⟩
   one has t⁻¹ H t ⊋ H, and (G/H)^H ≅ {gH : g⁻¹ H g ⊆ H} is strictly larger
   than N_G(H)/H ≅ W_GH. We prove that e is an injection (for every
   subgroup) and an equivalence when the set X(sh_G) = G/H is finite (the
   case used for finite groups in chapter 10). `}

def weyl_fixed_map (G : Group) (S : Subgroups G) (f : Id (GSet G) (S .gset) (S .gset))
  : InvariantMaps (subgroup_group G S) (gset_restrict (subgroup_group G S) G (subgroup_inclusion G S) (S .gset))
  ≔ u ↦ gset_path_transport G (S .gset) (S .gset) f (u .fst) (u .snd)

{` e is an injection. `}
def weyl_fixed_map_injective (G : Group) (S : Subgroups G)
  : IsEmbedding (Id (GSet G) (S .gset) (S .gset))
      (InvariantMaps (subgroup_group G S) (gset_restrict (subgroup_group G S) G (subgroup_inclusion G S) (S .gset)))
      (weyl_fixed_map G S)
  ≔ let X ≔ S .gset in
    let H ≔ subgroup_group G S in
    path_reflecting_set_embedding (Id (GSet G) X X)
      (InvariantMaps H (gset_restrict H G (subgroup_inclusion G S) X))
      (invariant_maps_set H (gset_restrict H G (subgroup_inclusion G S) X))
      (weyl_fixed_map G S)
      (f f' h ↦ gset_path_to_hom_reflects G X X f f'
        (gset_hom_eval_reflects G X X (shape G) (S .point) (S .transitive)
          (gset_path_to_hom G X X f) (gset_path_to_hom G X X f')
          (h (refl ((shape G, S .point) : ActionType G X)))))

{` A G-map φ : X → X of a transitive G-set is surjective at sh_G. `}
def weyl_endo_surjective (G : Group) (S : Subgroups G) (φ : GSetHom G (S .gset) (S .gset))
  : Surjective (gset_underlying G (S .gset)) (gset_underlying G (S .gset)) (φ (shape G))
  ≔ let X ≔ S .gset in
    let A ≔ gset_underlying G X in
    let pt ≔ S .point in
    x ↦ mere_rec (Σ (USym G) (g ↦ Id A x (gset_usym_act G X g (φ (shape G) pt))))
      (Mere (BookFiber A A (φ (shape G)) x)) (mere_isprop (BookFiber A A (φ (shape G)) x))
      (ge ↦ mere (BookFiber A A (φ (shape G)) x)
        (gset_usym_act G X (ge .fst) pt,
         concat A x (gset_usym_act G X (ge .fst) (φ (shape G) pt)) (φ (shape G) (gset_usym_act G X (ge .fst) pt))
           (ge .snd)
           (inverse A (φ (shape G) (gset_usym_act G X (ge .fst) pt)) (gset_usym_act G X (ge .fst) (φ (shape G) pt))
             (gset_hom_natural G X X φ (shape G) (shape G) (ge .fst) pt))))
      (transitive_pairwise_iff G X .fst (S .transitive) .snd x (φ (shape G) pt))

{` If X(sh_G) is finite, every G-map φ : X → X is an equivalence at sh_G
   (surjective self-maps of finite sets are injective, module 1720), hence
   at every z : BG. `}
def weyl_endo_equiv_finite (G : Group) (S : Subgroups G) (hfin : IsFinite (gset_underlying G (S .gset)))
  (φ : GSetHom G (S .gset) (S .gset)) (z : BG G .carrier)
  : BookIsEquiv (S .gset z .fst) (S .gset z .fst) (φ z)
  ≔ let X ≔ S .gset in
    let A ≔ gset_underlying G X in
    let hA ≔ gset_underlying_set G X in
    let at_shape : BookIsEquiv A A (φ (shape G))
      ≔ mere_rec (Σ Nat (n ↦ Id Type A (Fin n))) (BookIsEquiv A A (φ (shape G))) (book_isequiv_isprop A A (φ (shape G)))
          (np ↦ embedding_surjection_equiv native_truncation A A (φ (shape G))
            (path_reflecting_set_embedding A A hA (φ (shape G))
              (bsix_surjective_injective (np .fst) A hA
                (mere (Id Type (Fin (np .fst)) A) (inverse Type A (Fin (np .fst)) (np .snd)))
                (φ (shape G)) (weyl_endo_surjective G S φ)))
            (weyl_endo_surjective G S φ) .equiv)
          hfin in
    connected_based_elim native_truncation (BG G .carrier) (bg_connected G) (shape G)
      (w ↦ BookIsEquiv (X w .fst) (X w .fst) (φ w)) (w ↦ book_isequiv_isprop (X w .fst) (X w .fst) (φ w))
      at_shape z

{` lem:WGHisHfixofG/H, corrected: e is an equivalence when G/H is finite. `}
def weyl_fixed_map_surjective_finite (G : Group) (S : Subgroups G) (hfin : IsFinite (gset_underlying G (S .gset)))
  : Surjective (Id (GSet G) (S .gset) (S .gset))
      (InvariantMaps (subgroup_group G S) (gset_restrict (subgroup_group G S) G (subgroup_inclusion G S) (S .gset)))
      (weyl_fixed_map G S)
  ≔ let X ≔ S .gset in
    let H ≔ subgroup_group G S in
    let P ≔ Id (GSet G) X X in
    let I ≔ InvariantMaps H (gset_restrict H G (subgroup_inclusion G S) X) in
    s ↦
      let φ : GSetHom G X X ≔ z a ↦ s (z, a) in
      let eqs : (z : BG G .carrier) → Equiv (X z .fst) (X z .fst)
        ≔ z ↦ native_equivalence (X z .fst) (X z .fst) (φ z, weyl_endo_equiv_finite G S hfin φ z) in
      let f ≔ gset_path_from_equivs G X X eqs in
      mere (BookFiber P I (weyl_fixed_map G S) s)
        (f, funext (ActionType G X) (u ↦ X (u .fst) .fst) s (weyl_fixed_map G S f)
              (u ↦ inverse (X (u .fst) .fst) (weyl_fixed_map G S f u) (s u)
                (gset_path_from_equivs_transport G X X eqs (u .fst) (u .snd))))

def weyl_fixed_equiv_finite (G : Group) (S : Subgroups G) (hfin : IsFinite (gset_underlying G (S .gset)))
  : BookEquiv (Id (GSet G) (S .gset) (S .gset))
      (InvariantMaps (subgroup_group G S) (gset_restrict (subgroup_group G S) G (subgroup_inclusion G S) (S .gset)))
  ≔ embedding_surjection_equiv native_truncation (Id (GSet G) (S .gset) (S .gset))
      (InvariantMaps (subgroup_group G S) (gset_restrict (subgroup_group G S) G (subgroup_inclusion G S) (S .gset)))
      (weyl_fixed_map G S) (weyl_fixed_map_injective G S) (weyl_fixed_map_surjective_finite G S hfin)

{` The same from the symmetries of the shape of W_GH (USym W_GH ≃ (X = X)). `}
def weyl_usym_fixed_map (G : Group) (S : Subgroups G) (w : USym (weyl_group G S))
  : InvariantMaps (subgroup_group G S) (gset_restrict (subgroup_group G S) G (subgroup_inclusion G S) (S .gset))
  ≔ weyl_fixed_map G S (w .fst)

def weyl_usym_fixed_equiv_finite (G : Group) (S : Subgroups G) (hfin : IsFinite (gset_underlying G (S .gset)))
  : Equiv (USym (weyl_group G S))
      (InvariantMaps (subgroup_group G S) (gset_restrict (subgroup_group G S) G (subgroup_inclusion G S) (S .gset)))
  ≔ compose_equiv (USym (weyl_group G S)) (Id (GSet G) (S .gset) (S .gset))
      (InvariantMaps (subgroup_group G S) (gset_restrict (subgroup_group G S) G (subgroup_inclusion G S) (S .gset)))
      (automorphism_group_usym_equiv (GSet G) (gset_groupoid G) (S .gset))
      (native_equivalence (Id (GSet G) (S .gset) (S .gset))
        (InvariantMaps (subgroup_group G S) (gset_restrict (subgroup_group G S) G (subgroup_inclusion G S) (S .gset)))
        (weyl_fixed_equiv_finite G S hfin))
