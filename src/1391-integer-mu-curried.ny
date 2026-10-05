export "1338-integer-double-loops-example"
export "1351-integer-concrete-ring"

{` Chapter 13, the integers as a concrete ring (module 1351): the ring's μ : Hom(ℤ, Hom(ℤ, ℤ)), curried to a
   pointed map S¹ →* (S¹ →* BBℤ) (its classifying map followed by the projection out of the component of the
   constant map), is the map m_1 of exa:allS1*-swap (module 1338). Reason: its value at loop is the symmetry σ
   with ev ∘ ptw_*(σ) = B id_ℤ = dg_1 (the printed unit law). Module 1392 compares it with the book's Bμ. `}

def integer_mu_projection (C : CircleSignature)
  : BookPointedMap (BG (abelian_hom_group (circle_group C) (circle_abelian_group C)))
      (pointed_maps_pointed (circle_pointed C) (BB (circle_group C)))
  ≔ (u ↦ u .fst, refl (book_pointed_constant (circle_pointed C) (BB (circle_group C))))

def integer_mu_curried (C : CircleSignature) : example_M C (example_bbz C) (example_bbz_loops C)
  ≔ book_pointed_compose (circle_pointed C) (BG (abelian_hom_group (circle_group C) (circle_abelian_group C)))
      (pointed_maps_pointed (circle_pointed C) (BB (circle_group C)))
      (hom_B (circle_group C) (abelian_hom_group (circle_group C) (circle_abelian_group C)) (integer_concrete_mu C))
      (integer_mu_projection C)

{` Generic: for μ : ℤ → H with USym μ (loop) = σ and the projection pr out of the component, ev(pr ∘ Bμ) = σ₁.
   (Stated for arbitrary H and σ so that σ is never unfolded.) `}
def curried_component_ev (C : CircleSignature) (A : Type) (hA : isGroupoid A) (a : A)
  (μ : GroupHom (circle_group C) (automorphism_group A hA a)) (σ : USym (automorphism_group A hA a))
  (hμ : Id (USym (automorphism_group A hA a)) (usym_hom (circle_group C) (automorphism_group A hA a) μ (C .loop)) σ)
  : Id (Id A a a)
      (pointed_circle_ev C (A, a)
        (book_pointed_compose (circle_pointed C) (BG (automorphism_group A hA a)) (A, a)
          (hom_B (circle_group C) (automorphism_group A hA a) μ) ((u ↦ u .fst), refl a)))
      (σ .fst)
  ≔ let Z ≔ circle_group C in let H ≔ automorphism_group A hA a in
    let pr ≔ ((u ↦ u .fst), refl a) : BookPointedMap (BG H) (A, a) in
    calc
      pointed_circle_ev C (A, a) (book_pointed_compose (circle_pointed C) (BG H) (A, a) (hom_B Z H μ) pr)
      = loops_map (circle_pointed C) (A, a) (book_pointed_compose (circle_pointed C) (BG H) (A, a) (hom_B Z H μ) pr) (C .loop)
        by pointed_circle_ev_loops_map C (A, a) (book_pointed_compose (circle_pointed C) (BG H) (A, a) (hom_B Z H μ) pr)
      = loops_map (BG H) (A, a) pr (usym_hom Z H μ (C .loop))
        by loops_map_compose_pointwise (circle_pointed C) (BG H) (A, a) (hom_B Z H μ) pr (C .loop)
      = loops_map (BG H) (A, a) pr σ by refl (loops_map (BG H) (A, a) pr) hμ
      = σ .fst by loop_conjugate_at_refl A a (σ .fst) ∎

def integer_mu_curried_ev (C : CircleSignature)
  : Id (Loop (pointed_maps_pointed (circle_pointed C) (BB (circle_group C))))
      (pointed_circle_ev C (pointed_maps_pointed (circle_pointed C) (BB (circle_group C))) (integer_mu_curried C))
      (integer_mu_symmetry C .fst)
  ≔ curried_component_ev C (BookPointedMap (circle_pointed C) (BB (circle_group C)))
      (pointed_maps_bb_groupoid (circle_group C) (circle_group C))
      (book_pointed_constant (circle_pointed C) (BB (circle_group C)))
      (integer_concrete_mu C) (integer_mu_symmetry C)
      (circle_group_hom_from_symmetry_loop C (abelian_hom_group (circle_group C) (circle_abelian_group C)) (integer_mu_symmetry C))

{` The identity of S¹ is the degree-1 map. `}
def circle_identity_degree_one (C : CircleSignature)
  : Id (BookPointedMap (circle_pointed C) (circle_pointed C)) (book_pointed_identity (circle_pointed C))
      (example_degree_map C (pos. (suc. zero.)))
  ≔ let S ≔ circle_pointed C in let b ≔ C .base in let X ≔ C .carrier in
    equivalence_injective (BookPointedMap S S) (Loop S)
      (native_equivalence (BookPointedMap S S) (Loop S) (pointed_circle_ev C S, pointed_circle_ev_book_equiv C S))
      (book_pointed_identity S) (example_degree_map C (pos. (suc. zero.)))
      (calc
         pointed_circle_ev C S (book_pointed_identity S) = C .loop by loop_conjugate_at_refl X b (C .loop)
         = loop_power X b (C .loop) (pos. (suc. zero.))
           by inverse (Loop S) (loop_power X b (C .loop) (pos. (suc. zero.))) (C .loop) (concat_1p X b b (C .loop))
         = pointed_circle_ev C S (example_degree_map C (pos. (suc. zero.)))
           by inverse (Loop S) (pointed_circle_ev C S (example_degree_map C (pos. (suc. zero.))))
             (loop_power X b (C .loop) (pos. (suc. zero.)))
             (pointed_circle_ev_inverse_beta C S (loop_power X b (C .loop) (pos. (suc. zero.)))) ∎)

{` The classifying map of hom_of_symmetry(p) is ev ∘ ptw_*(p) (by definition; stated generically so that the
   comparison is made once, for an arbitrary abelian group). `}
def hom_of_symmetry_classifying (G : AbelianGroup) (p : USym (abelian_hom_group (G .fst) G))
  : Id (BookPointedMap (BG (G .fst)) (BG (G .fst)))
      (book_pointed_compose (BG (G .fst)) (Omega (BB (G .fst))) (BG (G .fst))
        (constant_loops_pointed_equiv (BG (G .fst)) (BB (G .fst)) .map (p .fst)) (bb_loops_evaluation_pointed (G .fst)))
      (hom_B (G .fst) (G .fst) (hom_of_symmetry (G .fst) G p))
  ≔ refl (hom_B (G .fst) (G .fst) (hom_of_symmetry (G .fst) G p))

{` ev ∘ ptw_*(σ) = B id_ℤ = dg_1, hence ptw_*(σ) = dg'_1. `}
def integer_mu_symmetry_degree (C : CircleSignature)
  : Id (BookPointedMap (circle_pointed C) (circle_pointed C))
      (example_post_e C (example_bbz C) (example_bbz_loops C) .map
        (constant_loops_pointed_equiv (circle_pointed C) (BB (circle_group C)) .map (integer_mu_symmetry C .fst)))
      (example_degree_map C (pos. (suc. zero.)))
  ≔ let Z ≔ circle_group C in let Q ≔ BookPointedMap (circle_pointed C) (circle_pointed C) in
    concat Q
      (example_post_e C (example_bbz C) (example_bbz_loops C) .map
        (constant_loops_pointed_equiv (circle_pointed C) (BB Z) .map (integer_mu_symmetry C .fst)))
      (hom_B Z Z (hom_of_symmetry Z (circle_abelian_group C) (integer_mu_symmetry C)))
      (example_degree_map C (pos. (suc. zero.)))
      (hom_of_symmetry_classifying (circle_abelian_group C) (integer_mu_symmetry C))
      (concat Q (hom_B Z Z (hom_of_symmetry Z (circle_abelian_group C) (integer_mu_symmetry C)))
        (book_pointed_identity (circle_pointed C)) (example_degree_map C (pos. (suc. zero.)))
        (refl (hom_B Z Z) (integer_mu_symmetry_hom C))
        (circle_identity_degree_one C))

def integer_mu_symmetry_ptw (C : CircleSignature)
  : Id (BookPointedMap (circle_pointed C) (Omega (BB (circle_group C))))
      (constant_loops_pointed_equiv (circle_pointed C) (BB (circle_group C)) .map (integer_mu_symmetry C .fst))
      (example_degree_loops C (example_bbz C) (example_bbz_loops C) (pos. (suc. zero.)))
  ≔ let Y ≔ example_bbz C in let E ≔ example_bbz_loops C in let one ≔ pos. (suc. zero.) : Int in
    let P ≔ BookPointedMap (circle_pointed C) (Omega Y) in
    let Q ≔ BookPointedMap (circle_pointed C) (circle_pointed C) in
    let k ≔ constant_loops_pointed_equiv (circle_pointed C) Y .map (integer_mu_symmetry C .fst) in
    equivalence_injective P Q (example_post_e C Y E) k (example_degree_loops C Y E one)
      (concat Q (example_post_e C Y E .map k) (example_degree_map C one) (example_post_e C Y E .map (example_degree_loops C Y E one))
        (integer_mu_symmetry_degree C)
        (inverse Q (example_post_e C Y E .map (example_degree_loops C Y E one)) (example_degree_map C one)
          (example_degree_loops_spec C Y E one)))

{` μ̂ = m_1. `}
def integer_mu_curried_m_one (C : CircleSignature)
  : Id (example_M C (example_bbz C) (example_bbz_loops C)) (integer_mu_curried C)
      (example_m C (example_bbz C) (example_bbz_loops C) (pos. (suc. zero.)))
  ≔ let Y ≔ example_bbz C in let E ≔ example_bbz_loops C in let one ≔ pos. (suc. zero.) : Int in
    let S ≔ circle_pointed C in let P ≔ pointed_maps_pointed S Y in
    let L ≔ Loop P in let K ≔ BookPointedMap S (Omega Y) in
    let ptw ≔ constant_loops_pointed_equiv S Y in
    let m1 ≔ example_m C Y E one in
    equivalence_injective (example_M C Y E) L
      (native_equivalence (example_M C Y E) L (pointed_circle_ev C P, pointed_circle_ev_book_equiv C P))
      (integer_mu_curried C) m1
      (equivalence_injective L K ptw (pointed_circle_ev C P (integer_mu_curried C)) (pointed_circle_ev C P m1)
        (calc
           ptw .map (pointed_circle_ev C P (integer_mu_curried C)) = ptw .map (integer_mu_symmetry C .fst)
             by refl (ptw .map) (integer_mu_curried_ev C)
           = example_degree_loops C Y E one by integer_mu_symmetry_ptw C
           = ptw .map (pointed_circle_ev C P m1)
             by inverse K (ptw .map (pointed_circle_ev C P m1)) (example_degree_loops C Y E one) (example_m_loop C Y E one) ∎))
