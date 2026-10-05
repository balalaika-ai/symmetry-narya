export "1390-book-integer-mu-sign"
export "1391-integer-mu-curried"

{` Chapter 13, example of the integers as a ring (fields.tex 1177-1219): the book's curried
   Bμ(z) ≔ ve(sh, (e_z, !)) (module 1390) compared with the ring's μ of module 1351 curried (module 1391).
   Bμ is the swap of the ring's μ, and not the ring's μ itself: Bμ = m_{-1}, μ̂ = m_1. In the reading of the
   footnote of def:ring (USym μ (loop), then ptw_* and ev ∘ -), Bμ gives the degree −1 map, so the book's Bμ
   satisfies the printed unit law ev ∘ USym(μ ∘ 1_ℤ)(loop) = B id_ℤ only after swapping its arguments (or with
   1_ℤ = −id); the book's computation Bμ(loopʲ, loopᵏ) = s^{jk} holds in the order of the swapped map. `}

def book_integer_mu_is_swap_ring_mu (C : CircleSignature)
  : Id (bmu_M C) (book_integer_mu_pointed C)
      (swap_pointed_domains_map (circle_pointed C) (circle_pointed C) (example_bbz C) (integer_mu_curried C))
  ≔ let sw ≔ swap_pointed_domains_map (circle_pointed C) (circle_pointed C) (example_bbz C) in
    let m1 ≔ example_m C (example_bbz C) (example_bbz_loops C) (pos. (suc. zero.)) in
    concat (bmu_M C) (book_integer_mu_pointed C) (sw m1) (sw (integer_mu_curried C))
      (book_integer_mu_swap_m_one C)
      (refl sw (inverse (bmu_M C) (integer_mu_curried C) m1 (integer_mu_curried_m_one C)))

def swap_book_integer_mu_is_ring_mu (C : CircleSignature)
  : Id (bmu_M C) (swap_pointed_domains_map (circle_pointed C) (circle_pointed C) (example_bbz C) (book_integer_mu_pointed C))
      (integer_mu_curried C)
  ≔ let m1 ≔ example_m C (example_bbz C) (example_bbz_loops C) (pos. (suc. zero.)) in
    concat (bmu_M C)
      (swap_pointed_domains_map (circle_pointed C) (circle_pointed C) (example_bbz C) (book_integer_mu_pointed C)) m1
      (integer_mu_curried C)
      (book_integer_mu_swap C) (inverse (bmu_M C) (integer_mu_curried C) m1 (integer_mu_curried_m_one C))

{` The degree read off along the footnote's order: m ↦ ev(ev ∘ ptw_*(ev(m))) sends m_k to loopᵏ. `}
def footnote_degree (C : CircleSignature) (m : bmu_M C) : Loop (circle_pointed C)
  ≔ pointed_circle_ev C (circle_pointed C)
      (example_post_e C (example_bbz C) (example_bbz_loops C) .map
        (constant_loops_pointed_equiv (circle_pointed C) (example_bbz C) .map
          (pointed_circle_ev C (pointed_maps_pointed (circle_pointed C) (example_bbz C)) m)))

def footnote_degree_m (C : CircleSignature) (k : Int)
  : Id (Loop (circle_pointed C)) (footnote_degree C (example_m C (example_bbz C) (example_bbz_loops C) k))
      (loop_power (C .carrier) (C .base) (C .loop) k)
  ≔ let Y ≔ example_bbz C in let E ≔ example_bbz_loops C in let S ≔ circle_pointed C in
    let Q ≔ BookPointedMap S S in
    let ptw ≔ constant_loops_pointed_equiv S Y in
    let m ≔ example_m C Y E k in
    calc
      footnote_degree C m = pointed_circle_ev C S (example_post_e C Y E .map (example_degree_loops C Y E k))
        by refl ((g ↦ pointed_circle_ev C S (example_post_e C Y E .map g)) : BookPointedMap S (Omega Y) → Loop S)
          (example_m_loop C Y E k)
      = pointed_circle_ev C S (example_degree_map C k)
        by refl (pointed_circle_ev C S) (example_degree_loops_spec C Y E k)
      = loop_power (C .carrier) (C .base) (C .loop) k
        by pointed_circle_ev_inverse_beta C S (loop_power (C .carrier) (C .base) (C .loop) k) ∎

{` In the footnote's order, Bμ has degree −1 and the ring's μ degree 1. `}
def book_integer_mu_footnote_degree (C : CircleSignature)
  : Id (Loop (circle_pointed C)) (footnote_degree C (book_integer_mu_pointed C))
      (loop_power (C .carrier) (C .base) (C .loop) (neg. zero.))
  ≔ concat (Loop (circle_pointed C)) (footnote_degree C (book_integer_mu_pointed C))
      (footnote_degree C (example_m C (example_bbz C) (example_bbz_loops C) (neg. zero.)))
      (loop_power (C .carrier) (C .base) (C .loop) (neg. zero.))
      (refl (footnote_degree C) (book_integer_mu_m_neg_one C))
      (footnote_degree_m C (neg. zero.))

def integer_mu_footnote_degree (C : CircleSignature)
  : Id (Loop (circle_pointed C)) (footnote_degree C (integer_mu_curried C))
      (loop_power (C .carrier) (C .base) (C .loop) (pos. (suc. zero.)))
  ≔ concat (Loop (circle_pointed C)) (footnote_degree C (integer_mu_curried C))
      (footnote_degree C (example_m C (example_bbz C) (example_bbz_loops C) (pos. (suc. zero.))))
      (loop_power (C .carrier) (C .base) (C .loop) (pos. (suc. zero.)))
      (refl (footnote_degree C) (integer_mu_curried_m_one C))
      (footnote_degree_m C (pos. (suc. zero.)))

def int_neg_one_ne_one (p : Id Int (neg. zero.) (pos. (suc. zero.))) : Empty
  ≔ transport Int (z ↦ match z [ pos. _ ↦ Empty | neg. _ ↦ Unit ]) (neg. zero.) (pos. (suc. zero.)) p star.

{` Hence Bμ is not the ring's μ. `}
def book_integer_mu_ne_ring_mu (C : CircleSignature)
  (e : Id (bmu_M C) (book_integer_mu_pointed C) (integer_mu_curried C)) : Empty
  ≔ let L ≔ Loop (circle_pointed C) in let X ≔ C .carrier in let b ≔ C .base in
    let lm ≔ loop_power X b (C .loop) (neg. zero.) in let l1 ≔ loop_power X b (C .loop) (pos. (suc. zero.)) in
    let q : Id L lm l1
      ≔ calc
          lm = footnote_degree C (book_integer_mu_pointed C)
            by inverse L (footnote_degree C (book_integer_mu_pointed C)) lm (book_integer_mu_footnote_degree C)
          = footnote_degree C (integer_mu_curried C) by refl (footnote_degree C) e
          = l1 by integer_mu_footnote_degree C ∎ in
    int_neg_one_ne_one
      (calc
         (neg. zero. : Int) = circle_winding C lm by inverse Int (circle_winding C lm) (neg. zero.) (circle_winding_power C (neg. zero.))
         = circle_winding C l1 by refl (circle_winding C) q
         = pos. (suc. zero.) by circle_winding_power C (pos. (suc. zero.)) ∎)

