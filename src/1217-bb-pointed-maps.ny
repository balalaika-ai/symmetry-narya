export "1216-bbmap-loops-equivalence"

{` Chapter 12, the lemma at abelian.tex 928: for abelian groups G and H there
   is a bijection of sets USym(Hom(G, H)) ≃ (BB G →* BB H). The book gives
   no proof. Here: USym(Hom(G, H)) ≃ Hom(G, H) (module 1207) ≃ (BG →* BH)
   ≃ (BB G →* BB H), the last step by bb_pointed_maps_equiv, whose forward
   map is Ω transported along ev : Ω(BB G) ≃* BG and Ω(BB H) ≃* BH
   (bb_pointed_maps_equiv_square). `}

{` Precomposition with a pointed equivalence X ≃* X', for maps into BL with
   L abelian (equality of such maps only needs a homotopy, module 1213).
   The map is k ↦ k ∘ e (book_pointed_compose). `}
def bbmap_pointed_precompose_equiv (X X' : Pointed) (e : BookPointedEquiv X X') (L : Group) (hL : IsAbelian L)
  : Equiv (BookPointedMap X' (BG L)) (BookPointedMap X (BG L))
  ≔ let A ≔ X .carrier in let A' ≔ X' .carrier in
    let eN ≔ native_equivalence A A' (e .fst .fst, e .snd) in
    let inv ≔ equiv_inverse_map A A' eN in
    let einv : BookPointedMap X' X
      ≔ (inv, concat A (X .point) (inv (e .fst .fst (X .point))) (inv (X' .point))
          (inverse A (inv (e .fst .fst (X .point))) (X .point) (equiv_retraction A A' eN (X .point)))
          (refl inv (inverse A' (X' .point) (e .fst .fst (X .point)) (e .fst .snd)))) in
    quasi_inverse_equiv (BookPointedMap X' (BG L)) (BookPointedMap X (BG L))
      (k ↦ book_pointed_compose X X' (BG L) (e .fst) k)
      (h ↦ book_pointed_compose X' X (BG L) einv h)
      (k ↦ bbmap_pointed_path_from_homotopy X' L hL
        (book_pointed_compose X' X (BG L) einv (book_pointed_compose X X' (BG L) (e .fst) k)) k
        (x' ↦ refl (k .fst) (equiv_counit A A' eN x')))
      (h ↦ bbmap_pointed_path_from_homotopy X L hL
        (book_pointed_compose X X' (BG L) (e .fst) (book_pointed_compose X' X (BG L) einv h)) h
        (x ↦ refl (h .fst) (equiv_retraction A A' eN x)))

def bbmap_bg_precompose_equiv (K L : Group) (hK : IsAbelian K) (hL : IsAbelian L)
  : Equiv (BookPointedMap (BG K) (BG L)) (BookPointedMap (Omega (BB K)) (BG L))
  ≔ bbmap_pointed_precompose_equiv (Omega (BB K)) (BG K) (abelian_bb_loops_pointed_equiv K hK) L hL

{` Main theorem: (BB K →* BB L) ≃ (BK →* BL) for abelian K and L. `}
def bb_pointed_maps_equiv (K L : Group) (hK : IsAbelian K) (hL : IsAbelian L)
  : Equiv (BookPointedMap (BB K) (BB L)) (BookPointedMap (BG K) (BG L))
  ≔ compose_equiv (BookPointedMap (BB K) (BB L)) (BookPointedMap (Omega (BB K)) (BG L)) (BookPointedMap (BG K) (BG L))
      (bbmap_loops_compose_equiv K L hK hL)
      (canonical_inverse_equiv (BookPointedMap (BG K) (BG L)) (BookPointedMap (Omega (BB K)) (BG L))
        (bbmap_bg_precompose_equiv K L hK hL))

{` The forward map is Ω transported: (image of F) ∘ ev_K = ev_L ∘ Ω F as
   pointed maps Ω(BB K) →* BL. `}
def bb_pointed_maps_equiv_square (K L : Group) (hK : IsAbelian K) (hL : IsAbelian L) (F : BookPointedMap (BB K) (BB L))
  : Id (BookPointedMap (Omega (BB K)) (BG L))
      (book_pointed_compose (Omega (BB K)) (BG K) (BG L) (bb_loops_evaluation_pointed K)
        (bb_pointed_maps_equiv K L hK hL .map F))
      (book_pointed_compose (Omega (BB K)) (Omega (BB L)) (BG L) (loops_pointed_map (BB K) (BB L) F)
        (bb_loops_evaluation_pointed L))
  ≔ equiv_counit (BookPointedMap (BG K) (BG L)) (BookPointedMap (Omega (BB K)) (BG L))
      (bbmap_bg_precompose_equiv K L hK hL) (bbmap_loops_compose K L F)

{` lemma (abelian.tex 928): USym(Hom(G, H)) ≃ (BB G →* BB H). `}
def abelian_hom_usym_bb_equiv (G H : AbelianGroup)
  : Equiv (USym (abelian_hom_group (G .fst) H)) (BookPointedMap (BB (G .fst)) (BB (H .fst)))
  ≔ compose_equiv (USym (abelian_hom_group (G .fst) H)) (GroupHom (G .fst) (H .fst))
      (BookPointedMap (BB (G .fst)) (BB (H .fst)))
      (abelian_hom_usym_equiv (G .fst) H)
      (compose_equiv (GroupHom (G .fst) (H .fst)) (BookPointedMap (BG (G .fst)) (BG (H .fst)))
        (BookPointedMap (BB (G .fst)) (BB (H .fst)))
        (group_hom_classifying_equiv (G .fst) (H .fst))
        (canonical_inverse_equiv (BookPointedMap (BB (G .fst)) (BB (H .fst))) (BookPointedMap (BG (G .fst)) (BG (H .fst)))
          (bb_pointed_maps_equiv (G .fst) (H .fst) (G .snd) (H .snd))))

{` Litmus: the identity of BB K corresponds to the identity of BK. `}
def bb_pointed_maps_equiv_identity (K : Group) (hK : IsAbelian K)
  : Id (BookPointedMap (BG K) (BG K)) (bb_pointed_maps_equiv K K hK hK .map (book_pointed_identity (BB K)))
      (book_pointed_identity (BG K))
  ≔ let P ≔ bbmap_bg_precompose_equiv K K hK hK in
    let A ≔ BookPointedMap (BG K) (BG K) in let B ≔ BookPointedMap (Omega (BB K)) (BG K) in
    concat A (equiv_inverse_map A B P (bbmap_loops_compose K K (book_pointed_identity (BB K))))
      (equiv_inverse_map A B P (P .map (book_pointed_identity (BG K)))) (book_pointed_identity (BG K))
      (refl (equiv_inverse_map A B P)
        (bbmap_pointed_path_from_homotopy (Omega (BB K)) K hK (bbmap_loops_compose K K (book_pointed_identity (BB K)))
          (P .map (book_pointed_identity (BG K)))
          (l ↦ refl (bb_loops_evaluation K) (loop_conjugate_at_refl (BB K .carrier) (bb_point K) l))))
      (equiv_retraction A B P (book_pointed_identity (BG K)))

{` Litmus: BB 1 →* BB H is contractible. `}
def bb_unit_pointed_maps_contractible (H : AbelianGroup)
  : BookIsContr (BookPointedMap (BB unit_group) (BB (H .fst)))
  ≔ book_contractibility_equiv (BookPointedMap (BG unit_group) (BG (H .fst))) (BookPointedMap (BB unit_group) (BB (H .fst)))
      (canonical_inverse_equiv (BookPointedMap (BB unit_group) (BB (H .fst))) (BookPointedMap (BG unit_group) (BG (H .fst)))
        (bb_pointed_maps_equiv unit_group (H .fst) unit_group_abelian (H .snd)))
      .map (contractible_domain_pointed_maps (BG unit_group) (BG (H .fst)) (star., u ↦ unit_prop star. u))
