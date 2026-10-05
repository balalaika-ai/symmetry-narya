export "03-ptd-homotopies"
export "../../../src/1207-abelian-hom-group"

{` Blind statements, chapter 13 (fields.tex): def:AbHomgroup, lem:grpHomOK.
   BB G = Σ (X : U) ‖BG÷ = X‖₀ pointed at (BG÷, |refl|) is chapter 12's BB;
   BH →* BB G is a 1-type by chapter 12's pointed_maps_bb_groupoid. `}

{` def:AbHomgroup: grpHom(H, G) ≔ Aut_{BH →* BB G}(cst_{pt_{BB G}}, refl). `}
def blind_grphom (H : Group) (G : AbelianGroup) : Group
  ≔ automorphism_group (BookPointedMap (BG H) (BB (G .fst))) (pointed_maps_bb_groupoid H (G .fst))
      (book_pointed_constant (BG H) (BB (G .fst)))

{` The chain of lem:grpHomOK: (sh = sh) → (BH →* Ω BB G) (ptw_*, the variant of
   rem:loops-at-ptd-cst) → (BH →* BG) (ev ∘ -, ev = evaluation at sh_G,
   bb_loops_evaluation_pointed) → absHom(abstr H, abstr G) (abstr). A
   symmetry of grpHom(H, G) is a path in the component; its first
   component is the path sh = sh in BH →* BB G. `}
def blind_grphom_chain (H : Group) (G : AbelianGroup) (p : USym (blind_grphom H G))
  : AbstractHom (abstr H) (abstr (G .fst))
  ≔ abstr_hom H (G .fst)
      (mkhom H (G .fst)
        (book_pointed_compose (BG H) (Omega (BB (G .fst))) (BG (G .fst))
          (blind_ptw_loops (BG H) (BB (G .fst)) .map (p .fst))
          (bb_loops_evaluation_pointed (G .fst))))

{` lem:grpHomOK: the composite is an abstract isomorphism from
   abstr(grpHom(H, G)) to absHom_ptw(abstr H, abstr G): it is an equivalence
   and sends the product p·q (usym_mul) to the pointwise product. `}
def blind_lem_grpHomOK : Type
  ≔ (H : Group) (G : AbelianGroup)
    → Product
        (BookIsEquiv (USym (blind_grphom H G)) (AbstractHom (abstr H) (abstr (G .fst))) (blind_grphom_chain H G))
        ((p q : USym (blind_grphom H G)) (g : USym H)
          → Id (USym (G .fst))
              (blind_grphom_chain H G (usym_mul (blind_grphom H G) p q) .fst g)
              (usym_mul (G .fst) (blind_grphom_chain H G p .fst g) (blind_grphom_chain H G q .fst g)))
