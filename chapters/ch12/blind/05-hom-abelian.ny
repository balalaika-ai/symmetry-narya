{` Blind statements for chapter 12 (abelian.tex), sec:ab-hom. `}
export "04-warn-torsors"

{` The constant pointed map cst_{pt_{B²H}} : BG →* B²H, pointed by refl. `}
def blind_grphom_cst (G H : Group) : BookPointedMap (BG G) (BlindBB H) ≔ book_pointed_constant (BG G) (BlindBB H)

{` Definition (abelian.tex:792). Hom(G, H) ≔ Aut_{BG →* B²H}(cst) for H abelian. Its classifying type is the
   component of cst in BG →* B²H, pointed at (cst, !). Making it a Group needs BG →* B²H to be a groupoid
   (the book's remark after the definition), so the Group is formed from a witness of that; the claim itself is
   blind_grphom_well_defined. Everything below uses only the pointed classifying type and its loops. `}
def blind_grphom_classifying (G H : Group) (hH : IsAbelian H) : Pointed
  ≔ (NativeComponent (BookPointedMap (BG G) (BlindBB H)) (blind_grphom_cst G H),
     component_point (BookPointedMap (BG G) (BlindBB H)) (blind_grphom_cst G H))

def BlindGrpHom (G H : Group) (hH : IsAbelian H) (lvl : isGroupoid (BookPointedMap (BG G) (BlindBB H))) : Group
  ≔ automorphism_group (BookPointedMap (BG G) (BlindBB H)) lvl (blind_grphom_cst G H)

{` abelian.tex:808: since B²H is a 2-type, BG →* B²H is a 1-type, so Hom(G, H) is well defined. `}
def blind_grphom_well_defined : Type
  ≔ (G H : Group) → IsAbelian H → isGroupoid (BookPointedMap (BG G) (BlindBB H))

{` USym of Hom(G, H): the loops at the base point of the classifying type (≡ USym (BlindGrpHom G H hH lvl)). `}
def BlindGrpHomSym (G H : Group) (hH : IsAbelian H) : Type ≔ Loop (blind_grphom_classifying G H hH)

{` Multiplication of abstr(Hom(G, H)): p · q = concat q p (repository convention usym_mul). `}
def blind_grphom_mul (G H : Group) (hH : IsAbelian H) (p q : BlindGrpHomSym G H hH) : BlindGrpHomSym G H hH
  ≔ concat (blind_grphom_classifying G H hH .carrier) (blind_grphom_classifying G H hH .point)
      (blind_grphom_classifying G H hH .point) (blind_grphom_classifying G H hH .point) q p

{` Construction (abelian.tex:802). For abelian G, H: USym Hom(G, H) ≃ Hom^abs(G, H) (abstract homomorphisms
   abstr G → abstr H). `}
def blind_grphom_abstract_hom_equiv : Type
  ≔ (G H : AbelianGroup)
    → BookEquiv (BlindGrpHomSym (G .fst) (H .fst) (H .snd)) (AbstractHom (abstr (G .fst)) (abstr (H .fst)))

{` Lemma (abelian.tex:824). The previous equivalence is a homomorphism from abstr(Hom(G, H)) to the pointwise
   group structure on Hom^abs(G, H): E(p · q)(g) = E(p)(g) · E(q)(g). "The previous equivalence" is not pinned
   down here (the construction's chain is not formalized), so the statement asserts an equivalence with this
   property. `}
def blind_grphom_equiv_pointwise_hom : Type
  ≔ (G H : AbelianGroup)
    → Σ (BookEquiv (BlindGrpHomSym (G .fst) (H .fst) (H .snd)) (AbstractHom (abstr (G .fst)) (abstr (H .fst))))
        (E ↦ (p q : BlindGrpHomSym (G .fst) (H .fst) (H .snd)) (g : USym (G .fst))
          → Id (USym (H .fst)) (E .map (blind_grphom_mul (G .fst) (H .fst) (H .snd) p q) .fst g)
              (usym_mul (H .fst) (E .map p .fst g) (E .map q .fst g)))

{` Lemma (abelian.tex:928). For abelian G, H: USym Hom(G, H) ≃ (B²G →* B²H). `}
def blind_grphom_bb_maps_equiv : Type
  ≔ (G H : AbelianGroup)
    → BookEquiv (BlindGrpHomSym (G .fst) (H .fst) (H .snd)) (BookPointedMap (BlindBB (G .fst)) (BlindBB (H .fst)))
