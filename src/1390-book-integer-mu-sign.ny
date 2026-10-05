export "1338-integer-double-loops-example"
export "1352-book-integer-multiplication"

{` Chapter 13 (fields.tex 1177-1219), the example of the integers as a ring: the book's curried
   Bμ(z) ≔ ve(sh_BBℤ, (e_z, !)) as a pointed map S¹ →* (S¹ →* BBℤ), compared with the maps m_k of
   exa:allS1*-swap (module 1338). Result: postcomposing Bμ with ev (fixing z, moving the inner variable along
   loop) gives the degree-1 family z ↦ (e_z, !), i.e. the book's computation Bμ(z, loopᵏ) = e_zᵏ, e_{loopʲ}ᵏ = s^{jk}
   holds in that order; hence Bμ = swap(m_1) = m_{-1}. In the order of the footnote of def:ring (USym μ moves
   the outer variable, then ptw_* and ev ∘ -), Bμ gives the degree −1 map, not B id_ℤ. `}

def bmu_bbz (C : CircleSignature) : Pointed ≔ example_bbz C

def bmu_M (C : CircleSignature) : Type ≔ example_M C (example_bbz C) (example_bbz_loops C)

{` Bμ as a pointed map, pointed by Bμ(base) = cst (book_integer_mu_base). `}
def book_integer_mu_pointed (C : CircleSignature) : bmu_M C
  ≔ (book_integer_mu C,
     inverse (BookPointedMap (circle_pointed C) (BB (circle_group C))) (book_integer_mu C (C .base))
       (book_pointed_constant (circle_pointed C) (BB (circle_group C))) (book_integer_mu_base C))

{` Fixing z and evaluating along the inner loop gives (e_z, !), whose evaluation at the shape is z. `}
def book_integer_mu_ev_value (C : CircleSignature) (z : C .carrier)
  : Id (C .carrier)
      (example_post_e C (example_bbz C) (example_bbz_loops C) .map
        (example_post_ev C (example_bbz C) (example_bbz_loops C) .map (book_integer_mu_pointed C)) .fst z) z
  ≔ let Y ≔ example_bbz C in
    concat (C .carrier)
      (bb_loops_evaluation (circle_group C) (pointed_circle_ev C Y (book_integer_mu C z)))
      (bb_loops_evaluation (circle_group C) (book_integer_mu_loop C z)) z
      (refl (bb_loops_evaluation (circle_group C)) (pointed_circle_ev_inverse_beta C Y (book_integer_mu_loop C z)))
      (book_integer_mu_loop_evaluation C z)

{` The degree-1 map is the identity pointwise. `}
def example_degree_one_value (C : CircleSignature) (z : C .carrier)
  : Id (C .carrier) (example_degree_map C (pos. (suc. zero.)) .fst z) z
  ≔ let S ≔ C .carrier in
    refl ((f ↦ f z) : (S → S) → S)
      (concat (S → S) (circle_rec C S (C .base, loop_power S (C .base) (C .loop) (pos. (suc. zero.))))
        (circle_rec C S (C .base, C .loop)) (identity S)
        (refl ((l ↦ circle_rec C S (C .base, l)) : Id S (C .base) (C .base) → S → S)
          (concat_1p S (C .base) (C .base) (C .loop)))
        (circle_rec_eta C S (identity S)))

{` Hence ev ∘ Bμ = dg'_1 (pointed maps into a loop space are determined by their functions). `}
def book_integer_mu_post_ev (C : CircleSignature)
  : Id (BookPointedMap (circle_pointed C) (Omega (example_bbz C)))
      (example_post_ev C (example_bbz C) (example_bbz_loops C) .map (book_integer_mu_pointed C))
      (example_degree_loops C (example_bbz C) (example_bbz_loops C) (pos. (suc. zero.)))
  ≔ let Y ≔ example_bbz C in let E ≔ example_bbz_loops C in let S ≔ C .carrier in
    let one ≔ pos. (suc. zero.) : Int in
    let f ≔ example_post_ev C Y E .map (book_integer_mu_pointed C) in
    let g ≔ example_degree_loops C Y E one in
    let En ≔ native_equivalence (Loop Y) S (E .fst .fst, E .snd) in
    loops_pointed_map_path_from_underlying Y (circle_pointed C) f g
      (funext S (_ ↦ Loop Y) (f .fst) (g .fst)
        (z ↦ equivalence_injective (Loop Y) S En (f .fst z) (g .fst z)
          (concat S (E .fst .fst (f .fst z)) z (E .fst .fst (g .fst z))
            (book_integer_mu_ev_value C z)
            (concat S z (example_degree_map C one .fst z) (E .fst .fst (g .fst z))
              (inverse S (example_degree_map C one .fst z) z (example_degree_one_value C z))
              (refl ((h ↦ h .fst z) : BookPointedMap (circle_pointed C) (circle_pointed C) → S)
                (inverse (BookPointedMap (circle_pointed C) (circle_pointed C))
                  (example_post_e C Y E .map g) (example_degree_map C one)
                  (example_degree_loops_spec C Y E one)))))))

{` Bμ = swap(m_1). `}
def book_integer_mu_swap_m_one (C : CircleSignature)
  : Id (bmu_M C) (book_integer_mu_pointed C)
      (swap_pointed_domains_map (circle_pointed C) (circle_pointed C) (example_bbz C)
        (example_m C (example_bbz C) (example_bbz_loops C) (pos. (suc. zero.))))
  ≔ let Y ≔ example_bbz C in let E ≔ example_bbz_loops C in let one ≔ pos. (suc. zero.) : Int in
    let P ≔ BookPointedMap (circle_pointed C) (Omega Y) in
    let sm ≔ swap_pointed_domains_map (circle_pointed C) (circle_pointed C) Y (example_m C Y E one) in
    equivalence_injective (bmu_M C) P (example_post_ev C Y E) (book_integer_mu_pointed C) sm
      (concat P (example_post_ev C Y E .map (book_integer_mu_pointed C)) (example_degree_loops C Y E one)
        (example_post_ev C Y E .map sm)
        (book_integer_mu_post_ev C)
        (inverse P (example_post_ev C Y E .map sm) (example_degree_loops C Y E one) (example_swap_m C Y E one)))

{` Bμ = m_{-1}, and swap(Bμ) = m_1. `}
def book_integer_mu_m_neg_one (C : CircleSignature)
  : Id (bmu_M C) (book_integer_mu_pointed C) (example_m C (example_bbz C) (example_bbz_loops C) (neg. zero.))
  ≔ concat (bmu_M C) (book_integer_mu_pointed C)
      (swap_pointed_domains_map (circle_pointed C) (circle_pointed C) (example_bbz C)
        (example_m C (example_bbz C) (example_bbz_loops C) (pos. (suc. zero.))))
      (example_m C (example_bbz C) (example_bbz_loops C) (neg. zero.))
      (book_integer_mu_swap_m_one C) (example_swap_m_negative C (pos. (suc. zero.)))

def book_integer_mu_swap (C : CircleSignature)
  : Id (bmu_M C) (swap_pointed_domains_map (circle_pointed C) (circle_pointed C) (example_bbz C) (book_integer_mu_pointed C))
      (example_m C (example_bbz C) (example_bbz_loops C) (pos. (suc. zero.)))
  ≔ concat (bmu_M C)
      (swap_pointed_domains_map (circle_pointed C) (circle_pointed C) (example_bbz C) (book_integer_mu_pointed C))
      (swap_pointed_domains_map (circle_pointed C) (circle_pointed C) (example_bbz C)
        (example_m C (example_bbz C) (example_bbz_loops C) (neg. zero.)))
      (example_m C (example_bbz C) (example_bbz_loops C) (pos. (suc. zero.)))
      (refl (swap_pointed_domains_map (circle_pointed C) (circle_pointed C) (example_bbz C)) (book_integer_mu_m_neg_one C))
      (example_swap_m_negative C (neg. zero.))
