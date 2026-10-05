export "10-hom-group"

{` Blind statements, chapter 13 (fields.tex), exa:allS1*-swap:
   M ≔ (S¹ →* (S¹ →* BBℤ)), BBℤ = Σ (X : U) ‖S¹ = X‖₀ (chapter 12's BB of
   the circle group), pointed at (S¹, |refl|). `}

def blind_exa_m_Z (C : CircleSignature) : Group ≔ circle_group C

def blind_exa_m_M (C : CircleSignature) : Type
  ≔ BookPointedMap (circle_pointed C) (blind_ptd_maps (circle_pointed C) (BB (blind_exa_m_Z C)))

{` Ω(BBℤ) is equivalent to Bℤ ≡ S¹ (pointed). `}
def blind_exa_allS1_swap_loops_BBZ : Type
  ≔ (C : CircleSignature) → BookPointedEquiv (Omega (BB (blind_exa_m_Z C))) (circle_pointed C)

{` M is equivalent to ΩΩ(BBℤ), and hence to ℤ. `}
def blind_exa_allS1_swap_M : Type
  ≔ (C : CircleSignature)
    → Product (BookEquiv (blind_exa_m_M C) (Loop (Omega (BB (blind_exa_m_Z C)))))
        (BookEquiv (blind_exa_m_M C) Int)

{` Ω(S¹ →* BBℤ) is equivalent to S¹ →* S¹. `}
def blind_exa_allS1_swap_ptw : Type
  ≔ (C : CircleSignature)
    → BookEquiv (Loop (blind_ptd_maps (circle_pointed C) (BB (blind_exa_m_Z C))))
        (BookPointedMap (circle_pointed C) (circle_pointed C))

{` "The k-loop around id_S¹" (given by function extensionality from loop^k at
   base), as a 2-loop L k : refl = refl in Ω(BBℤ). It is characterised here
   by its image under Ω(ev) for the evaluation ev : Ω(BBℤ) →* S¹ at base,
   which is loop^k (this determines L k, Ω(ev) being an equivalence). `}
def BlindKLoops (C : CircleSignature) (L : Int → Loop (Omega (BB (blind_exa_m_Z C)))) : Type
  ≔ (k : Int)
    → Id (Loop (circle_pointed C))
        (loops_map (Omega (BB (blind_exa_m_Z C))) (BG (blind_exa_m_Z C))
          (bb_loops_evaluation_pointed (blind_exa_m_Z C)) (L k))
        (loop_power (C .carrier) (C .base) (C .loop) k)

{` dg'_k : S¹ →* Ω(BBℤ), base ↦ id_S¹ (= refl_pt), loop ↦ k-loop, pointed by
   the (propositional) base computation. `}
def blind_exa_m_dg (C : CircleSignature) (L : Int → Loop (Omega (BB (blind_exa_m_Z C)))) (k : Int)
  : BookPointedMap (circle_pointed C) (Omega (BB (blind_exa_m_Z C)))
  ≔ pointed_circle_loop_rec C (Loop (BB (blind_exa_m_Z C))) (refl (BB (blind_exa_m_Z C) .point)) (L k)

{` m_k : M, base ↦ pt_{S¹ →* BBℤ}, loop ↦ ptw_*^{-1}(dg'_k), (m_k)_pt ≔ refl
   (propositional base computation). `}
def blind_exa_m_m (C : CircleSignature) (L : Int → Loop (Omega (BB (blind_exa_m_Z C)))) (k : Int)
  : blind_exa_m_M C
  ≔ pointed_circle_loop_rec C (BookPointedMap (circle_pointed C) (BB (blind_exa_m_Z C)))
      (book_pointed_constant (circle_pointed C) (BB (blind_exa_m_Z C)))
      (blind_ptw_loops_inv (circle_pointed C) (BB (blind_exa_m_Z C)) (blind_exa_m_dg C L k))

{` exa:allS1*-swap, computed claims: ptw_*(m_k(loop)) = dg'_k; applying dg'_k to
   loop^j gives the jk-loop; applying ptw_*(m_k(loop^i)) to loop^j gives the
   ijk-loop around id_S¹ (via con:ptd-homotopy-compo). m_k(p) and dg'_k(p)
   are read as Ω of the pointed maps (conjugation by the pointing paths). `}
def blind_exa_allS1_swap_mk : Type
  ≔ (C : CircleSignature) (L : Int → Loop (Omega (BB (blind_exa_m_Z C)))) → BlindKLoops C L
    → let S ≔ circle_pointed C in let Y ≔ BB (blind_exa_m_Z C) in
      let pw ≔ (n : Int) ↦ loop_power (C .carrier) (C .base) (C .loop) n in
      (k : Int)
      → Product
          (Id (BookPointedMap S (Omega Y))
            (blind_ptw_loops S Y .map (loops_map S (blind_ptd_maps S Y) (blind_exa_m_m C L k) (C .loop)))
            (blind_exa_m_dg C L k))
          (Product
            ((j : Int) → Id (Loop (Omega Y)) (loops_map S (Omega Y) (blind_exa_m_dg C L k) (pw j)) (L (int_mul j k)))
            ((i j : Int)
              → Id (Loop (Omega Y))
                  (loops_map S (Omega Y)
                    (blind_ptw_loops S Y .map (loops_map S (blind_ptd_maps S Y) (blind_exa_m_m C L k) (pw i)))
                    (pw j))
                  (L (int_mul (int_mul i j) k))))
