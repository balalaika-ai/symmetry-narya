export "1390-book-integer-mu-sign"
export "1396-double-loops-evaluation"

{` Chapter 13, example of the integers as a ring (fields.tex 1177-1219): Bμ(loopʲ, loopᵏ) = s^{jk}, using
   Bμ = m_{-1} and swap(Bμ) = m_1 (module 1390) and the ijk-loop computation for m_k (module 1396). `}

{` The two-dimensional computation. Applying Bμ to loopʲ (outer variable) and evaluating ptw_* of the result
   along loopᵏ (inner variable), the footnote's order, gives loop^{-jk} under Ω(BBℤ) ≃* S¹. The book's display
   Bμ(loopʲ, loopᵏ) = e_{loopʲ}ᵏ = s^{jk} moves the inner variable along loopᵏ first, i.e. it is the same
   evaluation for swap(Bμ) = m_1 with the roles of j, k exchanged, and gives loop^{jk} (s^{jk} evaluated at
   base). `}
def bmu_double_loop (C : CircleSignature) (m : bmu_M C) (i j : Int) : Loop (circle_pointed C)
  ≔ loops_map (Omega (example_bbz C)) (circle_pointed C) (example_bbz_loops C .fst)
      (loops_eval_along (circle_pointed C) (example_bbz C) (loop_power (C .carrier) (C .base) (C .loop) j)
        (loops_map (circle_pointed C) (pointed_maps_pointed (circle_pointed C) (example_bbz C)) m
          (loop_power (C .carrier) (C .base) (C .loop) i)))

def book_integer_mu_double_loop_footnote (C : CircleSignature) (j k : Int)
  : Id (Loop (circle_pointed C)) (bmu_double_loop C (book_integer_mu_pointed C) j k)
      (loop_power (C .carrier) (C .base) (C .loop) (int_mul (int_mul j k) (neg. zero.)))
  ≔ concat (Loop (circle_pointed C)) (bmu_double_loop C (book_integer_mu_pointed C) j k)
      (bmu_double_loop C (example_m C (example_bbz C) (example_bbz_loops C) (neg. zero.)) j k)
      (loop_power (C .carrier) (C .base) (C .loop) (int_mul (int_mul j k) (neg. zero.)))
      (refl ((m ↦ bmu_double_loop C m j k) : bmu_M C → Loop (circle_pointed C)) (book_integer_mu_m_neg_one C))
      (example_m_power_along_bbz C (neg. zero.) j k)

def book_integer_mu_double_loop_book_order (C : CircleSignature) (j k : Int)
  : Id (Loop (circle_pointed C))
      (bmu_double_loop C
        (swap_pointed_domains_map (circle_pointed C) (circle_pointed C) (example_bbz C) (book_integer_mu_pointed C)) k j)
      (loop_power (C .carrier) (C .base) (C .loop) (int_mul (int_mul k j) (pos. (suc. zero.))))
  ≔ let sb ≔ swap_pointed_domains_map (circle_pointed C) (circle_pointed C) (example_bbz C) (book_integer_mu_pointed C) in
    concat (Loop (circle_pointed C)) (bmu_double_loop C sb k j)
      (bmu_double_loop C (example_m C (example_bbz C) (example_bbz_loops C) (pos. (suc. zero.))) k j)
      (loop_power (C .carrier) (C .base) (C .loop) (int_mul (int_mul k j) (pos. (suc. zero.))))
      (refl ((m ↦ bmu_double_loop C m k j) : bmu_M C → Loop (circle_pointed C)) (book_integer_mu_swap C))
      (example_m_power_along_bbz C (pos. (suc. zero.)) k j)
