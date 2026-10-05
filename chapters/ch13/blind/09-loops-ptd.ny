export "08-swap"

{` Blind statements, chapter 13 (fields.tex): rem:grpHomOK (with
   fig:ulrik) and con:ptw-swap-ptd-doms. `}

{` rem:grpHomOK: h(p) : refl_{pt_Y} = ap_{cst_{pt_Y}}(p)·refl_{pt_Y} by induction
   on p : pt_X = x. The right-hand side is written as Ω(cst, refl)(p) (the
   conjugation formula of def:loops-map, loops_map). The book's base case is
   refl_{refl}; in Narya the corresponding base case is the pointing path
   (Ω(cst, refl))_pt = loops_map_point, which the book's refl stands for. `}
def blind_loops_cst_h (X Y : Pointed) (x : X .carrier) (p : Id (X .carrier) (X .point) x)
  : Id (Loop Y) (refl (Y .point))
      (pointed_loop_conjugate (Y .carrier) (Y .point) (Y .point) (refl (Y .point))
        (refl (constant (X .carrier) (Y .carrier) (Y .point)) p))
  ≔ J (X .carrier) (X .point)
      (x p ↦ Id (Loop Y) (refl (Y .point))
        (pointed_loop_conjugate (Y .carrier) (Y .point) (Y .point) (refl (Y .point))
          (refl (constant (X .carrier) (Y .carrier) (Y .point)) p)))
      (loops_map_point X Y (book_pointed_constant X Y)) x p

{` The pointing condition of (h, refl³): concat refl (h refl) = (Ω cst)_pt. `}
def blind_loops_cst_h_pt (X Y : Pointed)
  : Id (Id (Loop Y) (refl (Y .point)) (loops_map X Y (book_pointed_constant X Y) (refl (X .point))))
      (concat (Loop Y) (refl (Y .point)) (refl (Y .point)) (loops_map X Y (book_pointed_constant X Y) (refl (X .point)))
        (refl (refl (Y .point))) (blind_loops_cst_h X Y (X .point) (refl (X .point))))
      (loops_map_point X Y (book_pointed_constant X Y))
  ≔ let L ≔ Loop Y in let r ≔ refl (Y .point) in
    let t ≔ loops_map X Y (book_pointed_constant X Y) (refl (X .point)) in
    concat (Id L r t)
      (concat L r r t (refl r) (blind_loops_cst_h X Y (X .point) (refl (X .point))))
      (blind_loops_cst_h X Y (X .point) (refl (X .point)))
      (loops_map_point X Y (book_pointed_constant X Y))
      (concat_1p L r t (blind_loops_cst_h X Y (X .point) (refl (X .point))))
      (inverse (Id L r t) (loops_map_point X Y (book_pointed_constant X Y))
        (blind_loops_cst_h X Y (X .point) (refl (X .point)))
        (Jβ (X .carrier) (X .point)
          (x p ↦ Id (Loop Y) (refl (Y .point))
            (pointed_loop_conjugate (Y .carrier) (Y .point) (Y .point) (refl (Y .point))
              (refl (constant (X .carrier) (Y .carrier) (Y .point)) p)))
          (loops_map_point X Y (book_pointed_constant X Y))))

{` Ω_pt ≔ ptw_*^{-1}(h, refl³) : (cst_{refl}, refl_{refl}) = Ω(cst_{pt_Y}, refl)
   (ptw_* of con:identity-ptd-maps). `}
def blind_loops_pt (X Y : Pointed)
  : Id (BookPointedMap (Omega X) (Omega Y)) (book_pointed_constant (Omega X) (Omega Y))
      (loops_pointed_map X Y (book_pointed_constant X Y))
  ≔ let f ≔ book_pointed_constant (Omega X) (Omega Y) in
    let g ≔ loops_pointed_map X Y (book_pointed_constant X Y) in
    equiv_inverse_map (Id (BookPointedMap (Omega X) (Omega Y)) f g) (PointedHomotopy (Omega X) (Omega Y) f g)
      (pointed_map_path_equiv (Omega X) (Omega Y) f g)
      ((l ↦ blind_loops_cst_h X Y (X .point) l), blind_loops_cst_h_pt X Y)

{` Ω as a pointed map (X →* Y) →* (ΩX →* ΩY), pointed by Ω_pt. `}
def blind_loops_ptd_map (X Y : Pointed)
  : BookPointedMap (blind_ptd_maps X Y) (blind_ptd_maps (Omega X) (Omega Y))
  ≔ (k ↦ loops_pointed_map X Y k, blind_loops_pt X Y)

{` The red Ω(Ω)(q) ≔ Ω_pt⁻¹ · ap_Ω(q) · Ω_pt : Ω(ΩX →* ΩY), for q : Ω(X →* Y). `}
def blind_loops_loops (X Y : Pointed) (q : Loop (blind_ptd_maps X Y)) : Loop (blind_ptd_maps (Omega X) (Omega Y))
  ≔ loops_map (blind_ptd_maps X Y) (blind_ptd_maps (Omega X) (Omega Y)) (blind_loops_ptd_map X Y) q

{` i ≔ (q : Ω²Y ↦ q⁻¹), pointed by inverse_refl. `}
def blind_loop_reversal (Y : Pointed) : BookPointedMap (Omega (Omega Y)) (Omega (Omega Y))
  ≔ (q ↦ inverse (Loop Y) (refl (Y .point)) (refl (Y .point)) q,
     inverse (Loop (Omega Y)) (inverse (Loop Y) (refl (Y .point)) (refl (Y .point)) (refl (refl (Y .point))))
       (refl (refl (Y .point))) (inverse_refl (Loop Y) (refl (Y .point))))

{` rem:grpHomOK / fig:ulrik ("Fill!"): the diagram commutes,
   ptw_*(Ω(Ω)(q)) = i ∘ Ω(ptw_*(q)) in ΩX →* Ω²Y for all q : Ω(X →* Y)
   (ptw_* the variant of rem:loops-at-ptd-cst). The book leaves the filler
   as a TODO. `}
def blind_rem_grpHomOK_fill : Type
  ≔ (X Y : Pointed) (q : Loop (blind_ptd_maps X Y))
    → Id (BookPointedMap (Omega X) (Omega (Omega Y)))
        (blind_ptw_loops (Omega X) (Omega Y) .map (blind_loops_loops X Y q))
        (book_pointed_compose (Omega X) (Omega (Omega Y)) (Omega (Omega Y))
          (loops_pointed_map X (Omega Y) (blind_ptw_loops X Y .map q)) (blind_loop_reversal Y))

{` con:ptw-swap-ptd-doms uses the swap of con:swap-ptd-doms through the
   description in its implementation: swap(f)(x) is z ↦ f(z)(x) pointed by
   f'_pt(x) ≔ ptw(fst(f_pt))(x). The specification of con:swap-ptd-doms alone
   (only swap÷÷) leaves these inner pointing paths free, and ev depends on
   them, so the swap is required to have them. `}
def BlindSwapInner (X Y Z : Pointed) (sw : BlindSwap X Y Z) : Type
  ≔ (F : BookPointedMap X (blind_ptd_maps Y Z)) (y : Y .carrier)
    → Id (BookPointedMap X Z) (sw .fst .fst .fst F .fst y)
        ((x ↦ F .fst x .fst y), F .snd .fst (refl y))

{` con:ptw-swap-ptd-doms: ev ∘ swap(-) = ptw_* ∘ ev as maps
   O(X →* Y) → (X →* ΩY) (fig:ptw-swap-ptd-doms). `}
def blind_con_ptw_swap_ptd_doms : Type
  ≔ (C : CircleSignature) (X Y : Pointed) (sw : BlindSwap (circle_pointed C) X Y)
    → BlindSwapInner (circle_pointed C) X Y sw
    → Id (BookPointedMap (circle_pointed C) (blind_ptd_maps X Y) → BookPointedMap X (Omega Y))
        (f ↦ book_pointed_compose X (blind_O C Y) (Omega Y) (sw .fst .fst .fst f) (blind_ev C Y))
        (f ↦ blind_ptw_loops X Y .map (blind_ev C (blind_ptd_maps X Y) .fst f))
