export "12-example-m"
export "../../../src/1396-double-loops-evaluation"

{` Bridges for fields.tex, exa:allS1*-swap (block 638). Ours works over any pointed Y with
   E : Ω Y ≃* S¹ and instantiates at Y = BB ℤ, E = example_bbz_loops C, whose map is the blind evaluation
   bb_loops_evaluation_pointed (and BG ℤ is circle_pointed C by refl). The blind k-loop L k is any family
   with Ω E(L k) = loopᵏ (BlindKLoops); such a family exists (bridge_def_k_loops: L k = ev(dg'_k)) and is
   unique (bridge_k_loops_unique, Ω E is injective). For every such L the blind dg'_k and m_k are our
   example_degree_loops and example_m (bridge_def_exa_m_dg, bridge_def_exa_m_m), and the three computed
   claims follow from example_m_loop, example_degree_loops_power and example_m_power_along_circle
   (module 1396, the ijk-loop of fields.tex:679), using that Ω E is injective. `}

def bridge12_equiv_inverse_agree (A B : Type) (e e' : Equiv A B) (h : (a : A) → Id B (e .map a) (e' .map a)) (b : B)
  : Id A (equiv_inverse_map A B e b) (equiv_inverse_map A B e' b)
  ≔ let g ≔ equiv_inverse_map A B e in let g' ≔ equiv_inverse_map A B e' in
    concat A (g b) (g (e .map (g' b))) (g' b)
      (refl g (inverse B (e .map (g' b)) b
        (concat B (e .map (g' b)) (e' .map (g' b)) b (h (g' b)) (equiv_counit A B e' b))))
      (equiv_retraction A B e (g' b))

def bridge12_ptw_agree (X Y : Pointed) (r : Loop (blind_ptd_maps X Y))
  : Id (BookPointedMap X (Omega Y)) (blind_ptw_loops X Y .map r) (constant_loops_pointed_equiv X Y .map r)
  ≔ refl (constant_pointed_homotopy_equiv X Y .map)
      (pointed_map_path_equiv_ptw X Y (book_pointed_constant X Y) (book_pointed_constant X Y) r)

{` Ω of a pointed equivalence is injective. `}
def bridge12_loops_map_injective (X Y : Pointed) (w : BookPointedEquiv X Y) (l l' : Loop X)
  (h : Id (Loop Y) (loops_map X Y (w .fst) l) (loops_map X Y (w .fst) l'))
  : Id (Loop X) l l'
  ≔ let A ≔ X .carrier in let a ≔ X .point in
    pointed_equiv_induction X
      (Y' w' ↦ (l l' : Loop X) → Id (Loop Y') (loops_map X Y' (w' .fst) l) (loops_map X Y' (w' .fst) l') → Id (Loop X) l l')
      (l l' h ↦
        concat (Loop X) l (pointed_loop_conjugate A a a (refl a) l) l'
          (inverse (Loop X) (pointed_loop_conjugate A a a (refl a) l) l (loop_conjugate_at_refl A a l))
          (concat (Loop X) (pointed_loop_conjugate A a a (refl a) l) (pointed_loop_conjugate A a a (refl a) l') l'
            h (loop_conjugate_at_refl A a l')))
      Y w l l' h

{` exa:allS1*-swap (fields.tex:638), definitions. `}
def bridge_def_exa_m_Z (C : CircleSignature) : Id Group (blind_exa_m_Z C) (circle_group C) ≔ refl (circle_group C)

def bridge_def_exa_m_M (C : CircleSignature)
  : Id Type (blind_exa_m_M C) (example_M C (example_bbz C) (example_bbz_loops C))
  ≔ refl (example_M C (example_bbz C) (example_bbz_loops C))

{` Our k-loop around id: ev(dg'_k); it satisfies the blind characterisation. `}
def bridge_k_loop (C : CircleSignature) (k : Int) : Loop (Omega (example_bbz C))
  ≔ pointed_circle_ev C (Omega (example_bbz C)) (example_degree_loops C (example_bbz C) (example_bbz_loops C) k)

def bridge_def_k_loops (C : CircleSignature) : BlindKLoops C (bridge_k_loop C)
  ≔ k ↦
    let S ≔ circle_pointed C in let Y ≔ example_bbz C in let E ≔ example_bbz_loops C in
    let dg ≔ example_degree_loops C Y E k in
    calc
      loops_map (Omega Y) S (E .fst) (loops_map S (Omega Y) dg (C .loop))
        = loops_map S S (example_post_e C Y E .map dg) (C .loop)
        by inverse (Loop S) (loops_map S S (example_post_e C Y E .map dg) (C .loop))
          (loops_map (Omega Y) S (E .fst) (loops_map S (Omega Y) dg (C .loop)))
          (loops_map_compose_pointwise S (Omega Y) S dg (E .fst) (C .loop))
      = loops_map S S (example_degree_map C k) (C .loop)
        by refl ((f ↦ loops_map S S f (C .loop)) : BookPointedMap S S → Loop S) (example_degree_loops_spec C Y E k)
      = loop_power (C .carrier) (C .base) (C .loop) k
        by pointed_circle_ev_inverse_beta C S (loop_power (C .carrier) (C .base) (C .loop) k) ∎

def bridge_k_loops_unique (C : CircleSignature) (L L' : Int → Loop (Omega (example_bbz C)))
  (hL : BlindKLoops C L) (hL' : BlindKLoops C L') (k : Int)
  : Id (Loop (Omega (example_bbz C))) (L k) (L' k)
  ≔ let S ≔ circle_pointed C in let Y ≔ example_bbz C in let E ≔ example_bbz_loops C in
    bridge12_loops_map_injective (Omega Y) S E (L k) (L' k)
      (concat (Loop S) (loops_map (Omega Y) S (E .fst) (L k)) (loop_power (C .carrier) (C .base) (C .loop) k)
        (loops_map (Omega Y) S (E .fst) (L' k))
        (hL k)
        (inverse (Loop S) (loops_map (Omega Y) S (E .fst) (L' k)) (loop_power (C .carrier) (C .base) (C .loop) k) (hL' k)))

def bridge_def_exa_m_dg (C : CircleSignature) (L : Int → Loop (Omega (example_bbz C))) (hL : BlindKLoops C L) (k : Int)
  : Id (BookPointedMap (circle_pointed C) (Omega (example_bbz C)))
      (blind_exa_m_dg C L k) (example_degree_loops C (example_bbz C) (example_bbz_loops C) k)
  ≔ let S ≔ circle_pointed C in let Y ≔ example_bbz C in let E ≔ example_bbz_loops C in
    let bdg ≔ blind_exa_m_dg C L k in
    let dg ≔ example_degree_loops C Y E k in
    let post ≔ example_post_e C Y E in
    let lk ≔ loop_power (C .carrier) (C .base) (C .loop) k in
    let evS ≔ native_equivalence (BookPointedMap S S) (Loop S) (pointed_circle_ev C S, pointed_circle_ev_book_equiv C S) in
    let ev_eq : Id (Loop S) (pointed_circle_ev C S (post .map bdg)) (pointed_circle_ev C S (example_degree_map C k))
      ≔ calc
          pointed_circle_ev C S (post .map bdg)
            = loops_map (Omega Y) S (E .fst) (loops_map S (Omega Y) bdg (C .loop))
            by loops_map_compose_pointwise S (Omega Y) S bdg (E .fst) (C .loop)
          = loops_map (Omega Y) S (E .fst) (L k)
            by refl (loops_map (Omega Y) S (E .fst))
              (pointed_circle_loop_rec_beta C (Loop Y) (refl (Y .point)) (L k))
          = lk by hL k
          = pointed_circle_ev C S (example_degree_map C k)
            by inverse (Loop S) (pointed_circle_ev C S (example_degree_map C k)) lk (pointed_circle_ev_inverse_beta C S lk) ∎ in
    equivalence_injective (BookPointedMap S (Omega Y)) (BookPointedMap S S) post bdg dg
      (concat (BookPointedMap S S) (post .map bdg) (example_degree_map C k) (post .map dg)
        (equivalence_injective (BookPointedMap S S) (Loop S) evS (post .map bdg) (example_degree_map C k) ev_eq)
        (inverse (BookPointedMap S S) (post .map dg) (example_degree_map C k) (example_degree_loops_spec C Y E k)))

def bridge_def_exa_m_m (C : CircleSignature) (L : Int → Loop (Omega (example_bbz C))) (hL : BlindKLoops C L) (k : Int)
  : Id (blind_exa_m_M C) (blind_exa_m_m C L k) (example_m C (example_bbz C) (example_bbz_loops C) k)
  ≔ let S ≔ circle_pointed C in let Y ≔ example_bbz C in let E ≔ example_bbz_loops C in
    let P ≔ pointed_maps_pointed S Y in
    let cinv ≔ equiv_inverse_map (Loop P) (BookPointedMap S (Omega Y)) (constant_loops_pointed_equiv S Y) in
    refl (pointed_circle_loop_rec C (P .carrier) (P .point))
      (concat (Loop P) (blind_ptw_loops_inv S Y (blind_exa_m_dg C L k)) (cinv (blind_exa_m_dg C L k))
        (cinv (example_degree_loops C Y E k))
        (bridge12_equiv_inverse_agree (Loop P) (BookPointedMap S (Omega Y)) (blind_ptw_loops S Y)
          (constant_loops_pointed_equiv S Y) (bridge12_ptw_agree S Y) (blind_exa_m_dg C L k))
        (refl cinv (bridge_def_exa_m_dg C L hL k)))

{` exa:allS1*-swap, claims. `}
def bridge_exa_allS1_swap_loops_BBZ : blind_exa_allS1_swap_loops_BBZ ≔ C ↦ example_bbz_loops C

def bridge_exa_allS1_swap_M : blind_exa_allS1_swap_M
  ≔ C ↦
    (book_equivalence (blind_exa_m_M C) (Loop (Omega (example_bbz C))) (example_M_bbz_double_loops C),
     book_equivalence (blind_exa_m_M C) Int (example_M_bbz_integers C))

def bridge_exa_allS1_swap_ptw : blind_exa_allS1_swap_ptw
  ≔ C ↦ book_equivalence (Loop (pointed_maps_pointed (circle_pointed C) (example_bbz C)))
      (BookPointedMap (circle_pointed C) (circle_pointed C)) (example_loops_maps_circle C (example_bbz C) (example_bbz_loops C))

def bridge_exa_allS1_swap_mk_loop (C : CircleSignature) (L : Int → Loop (Omega (example_bbz C))) (hL : BlindKLoops C L) (k : Int)
  : Id (BookPointedMap (circle_pointed C) (Omega (example_bbz C)))
      (blind_ptw_loops (circle_pointed C) (example_bbz C) .map
        (loops_map (circle_pointed C) (blind_ptd_maps (circle_pointed C) (example_bbz C)) (blind_exa_m_m C L k) (C .loop)))
      (blind_exa_m_dg C L k)
  ≔ let S ≔ circle_pointed C in let Y ≔ example_bbz C in let E ≔ example_bbz_loops C in
    let P ≔ pointed_maps_pointed S Y in let Q ≔ BookPointedMap S (Omega Y) in
    let cl ≔ constant_loops_pointed_equiv S Y in
    let bm ≔ blind_exa_m_m C L k in
    calc
      blind_ptw_loops S Y .map (loops_map S P bm (C .loop)) = cl .map (loops_map S P bm (C .loop))
        by bridge12_ptw_agree S Y (loops_map S P bm (C .loop))
      = cl .map (loops_map S P (example_m C Y E k) (C .loop))
        by refl ((m ↦ cl .map (loops_map S P m (C .loop))) : BookPointedMap S P → Q) (bridge_def_exa_m_m C L hL k)
      = example_degree_loops C Y E k by example_m_loop C Y E k
      = blind_exa_m_dg C L k
        by inverse Q (blind_exa_m_dg C L k) (example_degree_loops C Y E k) (bridge_def_exa_m_dg C L hL k) ∎

def bridge_exa_allS1_swap_mk_jk (C : CircleSignature) (L : Int → Loop (Omega (example_bbz C))) (hL : BlindKLoops C L) (k j : Int)
  : Id (Loop (Omega (example_bbz C)))
      (loops_map (circle_pointed C) (Omega (example_bbz C)) (blind_exa_m_dg C L k) (loop_power (C .carrier) (C .base) (C .loop) j))
      (L (int_mul j k))
  ≔ let S ≔ circle_pointed C in let Y ≔ example_bbz C in let E ≔ example_bbz_loops C in
    let pw ≔ (n : Int) ↦ loop_power (C .carrier) (C .base) (C .loop) n in
    let dg ≔ example_degree_loops C Y E k in
    let ΩE ≔ loops_map (Omega Y) S (E .fst) in
    bridge12_loops_map_injective (Omega Y) S E (loops_map S (Omega Y) (blind_exa_m_dg C L k) (pw j)) (L (int_mul j k))
      (calc
        ΩE (loops_map S (Omega Y) (blind_exa_m_dg C L k) (pw j)) = ΩE (loops_map S (Omega Y) dg (pw j))
          by refl ((F ↦ ΩE (loops_map S (Omega Y) F (pw j))) : BookPointedMap S (Omega Y) → Loop S) (bridge_def_exa_m_dg C L hL k)
        = loops_map S S (example_post_e C Y E .map dg) (pw j)
          by inverse (Loop S) (loops_map S S (example_post_e C Y E .map dg) (pw j)) (ΩE (loops_map S (Omega Y) dg (pw j)))
            (loops_map_compose_pointwise S (Omega Y) S dg (E .fst) (pw j))
        = loop_power (C .carrier) (C .base) (pw k) j by example_degree_loops_power C Y E k j
        = pw (int_mul k j) by circle_loop_power_power C k j
        = pw (int_mul j k) by refl pw (int_mul_comm k j)
        = ΩE (L (int_mul j k)) by inverse (Loop S) (ΩE (L (int_mul j k))) (pw (int_mul j k)) (hL (int_mul j k)) ∎)

def bridge_exa_allS1_swap_mk_ijk (C : CircleSignature) (L : Int → Loop (Omega (example_bbz C))) (hL : BlindKLoops C L) (k i j : Int)
  : Id (Loop (Omega (example_bbz C)))
      (loops_map (circle_pointed C) (Omega (example_bbz C))
        (blind_ptw_loops (circle_pointed C) (example_bbz C) .map
          (loops_map (circle_pointed C) (blind_ptd_maps (circle_pointed C) (example_bbz C)) (blind_exa_m_m C L k)
            (loop_power (C .carrier) (C .base) (C .loop) i)))
        (loop_power (C .carrier) (C .base) (C .loop) j))
      (L (int_mul (int_mul i j) k))
  ≔ let S ≔ circle_pointed C in let Y ≔ example_bbz C in let E ≔ example_bbz_loops C in
    let P ≔ pointed_maps_pointed S Y in let Q ≔ BookPointedMap S (Omega Y) in
    let pw ≔ (n : Int) ↦ loop_power (C .carrier) (C .base) (C .loop) n in
    let ΩE ≔ loops_map (Omega Y) S (E .fst) in
    let cl ≔ constant_loops_pointed_equiv S Y in
    let bm ≔ blind_exa_m_m C L k in
    let lhs ≔ loops_map S (Omega Y) (blind_ptw_loops S Y .map (loops_map S P bm (pw i))) (pw j) in
    let F_eq : Id Q (blind_ptw_loops S Y .map (loops_map S P bm (pw i))) (cl .map (loops_map S P (example_m C Y E k) (pw i)))
      ≔ concat Q (blind_ptw_loops S Y .map (loops_map S P bm (pw i))) (cl .map (loops_map S P bm (pw i)))
          (cl .map (loops_map S P (example_m C Y E k) (pw i)))
          (bridge12_ptw_agree S Y (loops_map S P bm (pw i)))
          (refl ((m ↦ cl .map (loops_map S P m (pw i))) : BookPointedMap S P → Q) (bridge_def_exa_m_m C L hL k)) in
    bridge12_loops_map_injective (Omega Y) S E lhs (L (int_mul (int_mul i j) k))
      (calc
        ΩE lhs = ΩE (loops_eval_along S Y (pw j) (loops_map S P (example_m C Y E k) (pw i)))
          by refl ((F ↦ ΩE (loops_map S (Omega Y) F (pw j))) : Q → Loop S) F_eq
        = pw (int_mul (int_mul i j) k) by example_m_power_along_circle C Y E k i j
        = ΩE (L (int_mul (int_mul i j) k))
          by inverse (Loop S) (ΩE (L (int_mul (int_mul i j) k))) (pw (int_mul (int_mul i j) k)) (hL (int_mul (int_mul i j) k)) ∎)

def bridge_exa_allS1_swap_mk : blind_exa_allS1_swap_mk
  ≔ C L hL k ↦
    (bridge_exa_allS1_swap_mk_loop C L hL k,
     (j ↦ bridge_exa_allS1_swap_mk_jk C L hL k j,
      i j ↦ bridge_exa_allS1_swap_mk_ijk C L hL k i j))
