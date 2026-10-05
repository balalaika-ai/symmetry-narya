export "1215-bbmap-construction"

{` Chapter 12, the core of the lemma at abelian.tex 928: for abelian K and L,
   F ↦ ev_L ∘ Ω F is an equivalence (BB K →* BB L) ≃ (Ω(BB K) →* BL),
   where ev_L : Ω(BB L) ≃* BL is bb_loops_evaluation (module 1204).

   Injectivity: module 1214 (BB K is simply connected, BB L a 2-type) and
   ev_L is injective. Surjectivity: for ψ : Ω(BB K) →* BL the map BB f of
   module 1215 with f ≔ ψ ∘ (-)⁻¹ ∘ ev_K⁻¹ is a preimage. The inversion
   compensates the contravariance of the construction: Ω(BB f)(ℓ) is
   f(ℓ₁⁻¹(sh_K)) = f(ev_K(ℓ⁻¹)) (bbmap_loops_value, bbmap_theta_evaluation).
   Equality of pointed maps into BL only needs an unpointed homotopy
   (module 1213, L abelian), and Ω(BB K) →* BL is a set, so the mere
   identification of the base element of Comp with f suffices. `}

{` Transport along an inverse path of types is backward transport. `}
def bbmap_inverse_trr (X Y : Type) (P : Id Type X Y) (y : Y) : Id X (inverse Type X Y P .trr y) (P .trl y)
  ≔ J Type X (Y' P' ↦ (y' : Y') → Id X (inverse Type X Y' P' .trr y') (P' .trl y'))
      (y' ↦ calc
        inverse Type X X (refl X) .trr y' = refl X .trr y'
          by refl ((χ ↦ χ .trr y') : Id Type X X → X) (inverse_refl Type X)
        = y' by inverse X y' (refl X .trr y') (refl X .liftr y')
        = refl X .trl y' by inverse X (refl X .trl y') y' (refl X .liftl y') ∎)
      Y P y

{` θ(ℓ) ≔ ℓ₁⁻¹(refl .trr sh_K): the point at which the base element of Comp
   is evaluated after transport along ℓ; it is ev_K(ℓ⁻¹). `}
def bbmap_theta (K : Group) (l : Loop (BB K)) : BG K .carrier ≔ l .fst .trl (refl (BG K .carrier) .trr (shape K))

def bbmap_theta_evaluation (K : Group) (l : Loop (BB K))
  : Id (BG K .carrier) (bbmap_theta K l) (bb_loops_evaluation K (inverse (BB K .carrier) (bb_point K) (bb_point K) l))
  ≔ let BK ≔ BG K .carrier in
    calc
      l .fst .trl (refl BK .trr (shape K)) = l .fst .trl (shape K)
        by refl (l .fst .trl) (inverse BK (shape K) (refl BK .trr (shape K)) (refl BK .liftr (shape K)))
      = inverse Type BK BK (l .fst) .trr (shape K)
        by inverse BK (inverse Type BK BK (l .fst) .trr (shape K)) (l .fst .trl (shape K))
          (bbmap_inverse_trr BK BK (l .fst) (shape K)) ∎

{` The base element of Comp(pt) (the image of sh_L). `}
def bbmap_base_element (K L : Group) (hL : IsAbelian L) (f : BG K .carrier → BG L .carrier)
  : BBMapComp K L f (BG K .carrier) (set_trunc (Id Type (BG K .carrier) (BG K .carrier)) (refl (BG K .carrier)))
  ≔ bbmap_base_path K L hL f .trr (shape L)

{` Round trip, pointwise: ev_L(Ω(BB f)(ℓ)) = c0(θ(ℓ)), c0 the base element. `}
def bbmap_loops_value (K L : Group) (hL : IsAbelian L) (f : BG K .carrier → BG L .carrier) (l : Loop (BB K))
  : Id (BG L .carrier) (bb_loops_evaluation L (loops_map (BB K) (BB L) (bbmap_pointed K L hL f) l))
      (bbmap_base_element K L hL f .fst (bbmap_theta K l))
  ≔ let BK ≔ BG K .carrier in let BL ≔ BG L .carrier in
    let C0 ≔ BBMapComp K L f BK (set_trunc (Id Type BK BK) (refl BK)) in
    let E ≔ bbmap_eval_equiv K L hL f BK (refl BK) in
    let P0 ≔ bbmap_base_path K L hL f in
    let Q ≔ refl ((u ↦ BBMapComp K L f (u .fst) (u .snd)) : BB K .carrier → Type) l in
    let c0 ≔ P0 .trr (shape L) in
    let c' ≔ Q .trr c0 in
    calc
      concat Type BL C0 BL P0 (concat Type C0 C0 BL Q (inverse Type BL C0 P0)) .trr (shape L)
        = concat Type C0 C0 BL Q (inverse Type BL C0 P0) .trr c0
        by transport_concat Type (T ↦ T) BL C0 BL P0 (concat Type C0 C0 BL Q (inverse Type BL C0 P0)) (shape L)
      = inverse Type BL C0 P0 .trr c'
        by transport_concat Type (T ↦ T) C0 C0 BL Q (inverse Type BL C0 P0) c0
      = ua C0 BL E .trr c'
        by refl ((χ ↦ χ .trr c') : Id Type C0 BL → BL) (inverse_inverse Type C0 BL (ua C0 BL E))
      = c0 .fst (bbmap_theta K l)
        by inverse BL (c0 .fst (bbmap_theta K l)) (c' .fst (refl BK .trr (shape K)))
          (Q .liftr c0 .fst (l .fst .liftl (refl BK .trr (shape K)))) ∎

{` The map F ↦ ev_L ∘ Ω F. `}
def bbmap_loops_compose (K L : Group) (F : BookPointedMap (BB K) (BB L)) : BookPointedMap (Omega (BB K)) (BG L)
  ≔ book_pointed_compose (Omega (BB K)) (Omega (BB L)) (BG L) (loops_pointed_map (BB K) (BB L) F)
      (bb_loops_evaluation_pointed L)

def bbmap_loops_target_set (K L : Group) : isSet (BookPointedMap (Omega (BB K)) (BG L))
  ≔ hlevel_two_to_set (BookPointedMap (Omega (BB K)) (BG L))
      (pointed_maps_truncation_level (suc. zero.) (suc. (suc. zero.)) (Omega (BB K)) (BG L)
        (equiv_inverse_map (NConnectedType (suc. zero.) (Loop (BB K))) (Connected (Loop (BB K)))
          (zero_connected_connected (Loop (BB K))) (bb_simply_connected K .snd))
        (groupoid_to_hlevel (BG L .carrier) (bg_groupoid L)))

def bbmap_inverse_evaluation (K : Group) (hK : IsAbelian K) : BG K .carrier → Loop (BB K)
  ≔ equiv_inverse_map (Loop (BB K)) (BG K .carrier)
      (native_equivalence (Loop (BB K)) (BG K .carrier) (bb_loops_evaluation K, abelian_bb_loops_equiv K hK))

def bbmap_preimage_function (K L : Group) (hK : IsAbelian K) (ψ : BookPointedMap (Omega (BB K)) (BG L))
  : BG K .carrier → BG L .carrier
  ≔ x ↦ ψ .fst (inverse (BB K .carrier) (bb_point K) (bb_point K) (bbmap_inverse_evaluation K hK x))

{` Surjectivity: ev_L ∘ Ω(BB f) = ψ for f = ψ ∘ (-)⁻¹ ∘ ev_K⁻¹. `}
def bbmap_round_trip (K L : Group) (hK : IsAbelian K) (hL : IsAbelian L) (ψ : BookPointedMap (Omega (BB K)) (BG L))
  : Id (BookPointedMap (Omega (BB K)) (BG L))
      (bbmap_loops_compose K L (bbmap_pointed K L hL (bbmap_preimage_function K L hK ψ))) ψ
  ≔ let BK ≔ BG K .carrier in let BL ≔ BG L .carrier in
    let BBK ≔ BB K .carrier in let pt ≔ bb_point K in
    let f ≔ bbmap_preimage_function K L hK ψ in
    let c0 ≔ bbmap_base_element K L hL f in
    let M ≔ BookPointedMap (Omega (BB K)) (BG L) in
    let G ≔ bbmap_loops_compose K L (bbmap_pointed K L hL f) in
    let ev ≔ native_equivalence (Loop (BB K)) BK (bb_loops_evaluation K, abelian_bb_loops_equiv K hK) in
    mere_rec (Id (BK → BL) f (c0 .fst)) (Id M G ψ) (bbmap_loops_target_set K L G ψ)
      (γ ↦ bbmap_pointed_path_from_homotopy (Omega (BB K)) L hL G ψ
        (l ↦ calc
          G .fst l = c0 .fst (bbmap_theta K l) by bbmap_loops_value K L hL f l
          = f (bbmap_theta K l) by inverse BL (f (bbmap_theta K l)) (c0 .fst (bbmap_theta K l)) (γ (refl (bbmap_theta K l)))
          = f (bb_loops_evaluation K (inverse BBK pt pt l)) by refl f (bbmap_theta_evaluation K l)
          = ψ .fst (inverse BBK pt pt (inverse BBK pt pt l))
            by refl ((t ↦ ψ .fst (inverse BBK pt pt t)) : Loop (BB K) → BL)
              (equiv_retraction (Loop (BB K)) BK ev (inverse BBK pt pt l))
          = ψ .fst l by refl (ψ .fst) (inverse_inverse BBK pt pt l) ∎))
      (c0 .snd)

def bbmap_loops_compose_surjective (K L : Group) (hK : IsAbelian K) (hL : IsAbelian L)
  : Surjective (BookPointedMap (BB K) (BB L)) (BookPointedMap (Omega (BB K)) (BG L)) (bbmap_loops_compose K L)
  ≔ ψ ↦ mere (BookFiber (BookPointedMap (BB K) (BB L)) (BookPointedMap (Omega (BB K)) (BG L)) (bbmap_loops_compose K L) ψ)
      (bbmap_pointed K L hL (bbmap_preimage_function K L hK ψ),
       inverse (BookPointedMap (Omega (BB K)) (BG L))
         (bbmap_loops_compose K L (bbmap_pointed K L hL (bbmap_preimage_function K L hK ψ))) ψ
         (bbmap_round_trip K L hK hL ψ))

{` Injectivity: ev_L ∘ Ω F = ev_L ∘ Ω F' implies F = F'. `}
def bbmap_loops_compose_injective (K L : Group) (hL : IsAbelian L) (F F' : BookPointedMap (BB K) (BB L))
  (q : Id (BookPointedMap (Omega (BB K)) (BG L)) (bbmap_loops_compose K L F) (bbmap_loops_compose K L F'))
  : Id (BookPointedMap (BB K) (BB L)) F F'
  ≔ bbmap_loops_injective (BB K) (BB L) (bb_simply_connected K) (bb_two_type L) F F'
      (l ↦ equivalence_injective (Loop (BB L)) (BG L .carrier)
        (native_equivalence (Loop (BB L)) (BG L .carrier) (bb_loops_evaluation L, abelian_bb_loops_equiv L hL))
        (loops_map (BB K) (BB L) F l) (loops_map (BB K) (BB L) F' l) (q .fst (refl l)))

def bbmap_loops_compose_embedding (K L : Group) (hL : IsAbelian L)
  : IsEmbedding (BookPointedMap (BB K) (BB L)) (BookPointedMap (Omega (BB K)) (BG L)) (bbmap_loops_compose K L)
  ≔ ψ u v ↦
    let M ≔ BookPointedMap (Omega (BB K)) (BG L) in
    subtype_equal (BookPointedMap (BB K) (BB L)) (F ↦ Id M ψ (bbmap_loops_compose K L F))
      (F ↦ bbmap_loops_target_set K L ψ (bbmap_loops_compose K L F)) u v
      (bbmap_loops_compose_injective K L hL (u .fst) (v .fst)
        (concat M (bbmap_loops_compose K L (u .fst)) ψ (bbmap_loops_compose K L (v .fst))
          (inverse M ψ (bbmap_loops_compose K L (u .fst)) (u .snd)) (v .snd)))

{` (BB K →* BB L) ≃ (Ω(BB K) →* BL), map F ↦ ev_L ∘ Ω F. `}
def bbmap_loops_compose_equiv (K L : Group) (hK : IsAbelian K) (hL : IsAbelian L)
  : Equiv (BookPointedMap (BB K) (BB L)) (BookPointedMap (Omega (BB K)) (BG L))
  ≔ native_equivalence (BookPointedMap (BB K) (BB L)) (BookPointedMap (Omega (BB K)) (BG L))
      (bbmap_loops_compose K L,
       native_embedding_surjection_equiv_book_map (BookPointedMap (BB K) (BB L)) (BookPointedMap (Omega (BB K)) (BG L))
         (bbmap_loops_compose K L) (bbmap_loops_compose_embedding K L hL) (bbmap_loops_compose_surjective K L hK hL))
