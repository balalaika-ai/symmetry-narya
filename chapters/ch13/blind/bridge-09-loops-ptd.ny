export "09-loops-ptd"
export "../../../src/1337-loops-of-pointed-maps"

{` Bridges for fields.tex, rem:grpHomOK / fig:ulrik (714) and con:ptw-swap-ptd-doms (800).
   The blind h, Ω_pt, Ω as a pointed map, Ω(Ω) and i are ours by refl (loops_map_point at the constant
   map is the base case of loops_constant_pointing judgmentally). The blind filler statement follows from
   ulrik_square after replacing the blind ptw_* (built on pointed_map_path_equiv) by
   constant_loops_pointed_equiv (pointwise equal maps). For 800 the blind statement quantifies over every
   swap sw satisfying the specification of con:swap-ptd-doms plus the inner pointing BlindSwapInner; for such
   sw, sw(f)(x) = ours(f)(x) as pointed maps, so ev ∘ sw(f) and ev ∘ swap(f) have the same underlying
   function, and maps into ΩY are determined by it (cor:Id-(B->*loopsA)); then ptw_swap_pointed_domains
   applies. Our swap satisfies BlindSwapInner (bridge_def_swap_inner). `}

{` ptw_* (blind, via pointed_map_path_equiv) agrees with constant_loops_pointed_equiv. `}
def bridge_ptw_loops_agree (X Y : Pointed) (r : Loop (blind_ptd_maps X Y))
  : Id (BookPointedMap X (Omega Y)) (blind_ptw_loops X Y .map r) (constant_loops_pointed_equiv X Y .map r)
  ≔ refl (constant_pointed_homotopy_equiv X Y .map)
      (pointed_map_path_equiv_ptw X Y (book_pointed_constant X Y) (book_pointed_constant X Y) r)

{` rem:grpHomOK, fig:ulrik (fields.tex:714). `}
def bridge_def_loops_cst_h (X Y : Pointed) (x : X .carrier) (p : Id (X .carrier) (X .point) x)
  : Id (Id (Loop Y) (refl (Y .point))
        (pointed_loop_conjugate (Y .carrier) (Y .point) (Y .point) (refl (Y .point))
          (refl (constant (X .carrier) (Y .carrier) (Y .point)) p)))
      (blind_loops_cst_h X Y x p) (loops_constant_pointing X Y x p)
  ≔ refl (loops_constant_pointing X Y x p)

def bridge_def_loops_pt (X Y : Pointed)
  : Id (Id (BookPointedMap (Omega X) (Omega Y)) (book_pointed_constant (Omega X) (Omega Y))
        (loops_pointed_map X Y (book_pointed_constant X Y)))
      (blind_loops_pt X Y) (loops_functor_point X Y)
  ≔ refl (loops_functor_point X Y)

def bridge_def_loops_ptd_map (X Y : Pointed)
  : Id (BookPointedMap (pointed_maps_pointed X Y) (pointed_maps_pointed (Omega X) (Omega Y)))
      (blind_loops_ptd_map X Y) (loops_functor_pointed X Y)
  ≔ refl (loops_functor_pointed X Y)

def bridge_def_loops_loops (X Y : Pointed) (q : Loop (pointed_maps_pointed X Y))
  : Id (Loop (pointed_maps_pointed (Omega X) (Omega Y))) (blind_loops_loops X Y q) (loops_of_loops_functor X Y q)
  ≔ refl (loops_of_loops_functor X Y q)

def bridge_def_loop_reversal (Y : Pointed)
  : Id (BookPointedMap (Omega (Omega Y)) (Omega (Omega Y))) (blind_loop_reversal Y) (double_loop_inverse Y)
  ≔ refl (double_loop_inverse Y)

def bridge_rem_grpHomOK_fill : blind_rem_grpHomOK_fill
  ≔ X Y q ↦
    let M ≔ BookPointedMap (Omega X) (Omega (Omega Y)) in
    let R ≔ (k ↦ book_pointed_compose (Omega X) (Omega (Omega Y)) (Omega (Omega Y)) (loops_pointed_map X (Omega Y) k)
        (double_loop_inverse Y)) : BookPointedMap X (Omega Y) → M in
    concat M (blind_ptw_loops (Omega X) (Omega Y) .map (loops_of_loops_functor X Y q)) (ulrik_left X Y q)
      (R (blind_ptw_loops X Y .map q))
      (bridge_ptw_loops_agree (Omega X) (Omega Y) (loops_of_loops_functor X Y q))
      (concat M (ulrik_left X Y q) (ulrik_right X Y q) (R (blind_ptw_loops X Y .map q))
        (ulrik_square X Y q)
        (refl R (inverse (BookPointedMap X (Omega Y)) (blind_ptw_loops X Y .map q) (constant_loops_pointed_equiv X Y .map q)
          (bridge_ptw_loops_agree X Y q))))

{` con:ptw-swap-ptd-doms (fields.tex:800). Our swap as a BlindSwap, and its inner pointing. `}
def bridge_swap_as_blind (X Y Z : Pointed) : BlindSwap X Y Z
  ≔ (swap_pointed_domains X Y Z, F ↦ swap_pointed_domains_underlying X Y Z F)

def bridge_def_swap_inner (X Y Z : Pointed) : BlindSwapInner X Y Z (bridge_swap_as_blind X Y Z)
  ≔ F y ↦
    (refl ((x ↦ F .fst x .fst y) : X .carrier → Z .carrier),
     refl ((H ↦ H .fst y) : PointedHomotopy Y Z (book_pointed_constant Y Z) (F .fst (X .point)) → Id (Z .carrier) (Z .point) (F .fst (X .point) .fst y))
       (pointed_map_path_equiv_ptw Y Z (book_pointed_constant Y Z) (F .fst (X .point)) (F .snd)))

def bridge_con_ptw_swap_ptd_doms_at (C : CircleSignature) (X Y : Pointed) (sw : BlindSwap (circle_pointed C) X Y)
  (inner : BlindSwapInner (circle_pointed C) X Y sw) (f : BookPointedMap (circle_pointed C) (blind_ptd_maps X Y))
  : Id (BookPointedMap X (Omega Y))
      (book_pointed_compose X (blind_O C Y) (Omega Y) (sw .fst .fst .fst f) (blind_ev C Y))
      (blind_ptw_loops X Y .map (blind_ev C (blind_ptd_maps X Y) .fst f))
  ≔ let S ≔ circle_pointed C in
    let ev ≔ pointed_circle_ev C Y in
    let r ≔ pointed_circle_ev C (pointed_maps_pointed X Y) f in
    let ours ≔ swap_pointed_domains_map S X Y f in
    let F ≔ X .carrier → Loop Y in
    loops_pointed_map_path_from_underlying Y X
      (book_pointed_compose X (blind_O C Y) (Omega Y) (sw .fst .fst .fst f) (blind_ev C Y))
      (blind_ptw_loops X Y .map r)
      (concat F (x ↦ ev (sw .fst .fst .fst f .fst x)) (x ↦ ev (ours .fst x)) (blind_ptw_loops X Y .map r .fst)
        (funext (X .carrier) (_ ↦ Loop Y) (x ↦ ev (sw .fst .fst .fst f .fst x)) (x ↦ ev (ours .fst x))
          (x ↦ refl ev (concat (BookPointedMap S Y) (sw .fst .fst .fst f .fst x)
            ((z ↦ f .fst z .fst x), f .snd .fst (refl x)) (ours .fst x)
            (inner f x)
            (inverse (BookPointedMap S Y) (ours .fst x) ((z ↦ f .fst z .fst x), f .snd .fst (refl x))
              (bridge_def_swap_inner S X Y f x)))))
        (concat F (x ↦ ev (ours .fst x)) (constant_loops_pointed_equiv X Y .map r .fst) (blind_ptw_loops X Y .map r .fst)
          (ptw_swap_pointed_domains C X Y f .fst)
          (inverse F (blind_ptw_loops X Y .map r .fst) (constant_loops_pointed_equiv X Y .map r .fst)
            (bridge_ptw_loops_agree X Y r .fst))))

def bridge_con_ptw_swap_ptd_doms : blind_con_ptw_swap_ptd_doms
  ≔ C X Y sw inner ↦
    funext (BookPointedMap (circle_pointed C) (blind_ptd_maps X Y)) (_ ↦ BookPointedMap X (Omega Y))
      (f ↦ book_pointed_compose X (blind_O C Y) (Omega Y) (sw .fst .fst .fst f) (blind_ev C Y))
      (f ↦ blind_ptw_loops X Y .map (blind_ev C (blind_ptd_maps X Y) .fst f))
      (f ↦ bridge_con_ptw_swap_ptd_doms_at C X Y sw inner f)

{` The blind hypotheses are satisfiable: our swap meets both. `}
def bridge_con_ptw_swap_ptd_doms_ours (C : CircleSignature) (X Y : Pointed)
  : Id (BookPointedMap (circle_pointed C) (blind_ptd_maps X Y) → BookPointedMap X (Omega Y))
      (f ↦ book_pointed_compose X (blind_O C Y) (Omega Y) (swap_pointed_domains_map (circle_pointed C) X Y f) (blind_ev C Y))
      (f ↦ blind_ptw_loops X Y .map (blind_ev C (blind_ptd_maps X Y) .fst f))
  ≔ bridge_con_ptw_swap_ptd_doms C X Y (bridge_swap_as_blind (circle_pointed C) X Y)
      (bridge_def_swap_inner (circle_pointed C) X Y)
