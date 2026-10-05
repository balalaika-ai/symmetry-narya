export "05-hom-abelian"
export "../../../src/1219-abelian-hom-abstract"
export "../../../src/1217-bb-pointed-maps"
export "../../../src/410-pointed-connected-groupoids"

{` Bridges for abelian.tex, sec:ab-hom (blocks 792, 802, 824, 928). The blind constant map, classifying
   type, symmetries and multiplication of Hom(G, H) are ours by refl; BlindGrpHom G H hH lvl differs from
   abelian_hom_group G (mk_abelian_group H hH) only in the groupoid witness (bridge_def_grphom). Ours never uses that H is
   abelian for the groupoid property, nor that G is abelian for 802/824. The blind lemma at 824 asserts only that
   SOME equivalence is multiplicative; ours states it for the equivalence of construction 802 itself
   (abelian_hom_abstract_book_equiv, map p ↦ abstr(hom_of_symmetry p)), which is stronger. `}

{` Definition (abelian.tex:792). `}
def bridge_def_grphom_cst (G H : Group)
  : Id (BookPointedMap (BG G) (BB H)) (blind_grphom_cst G H) (book_pointed_constant (BG G) (BB H))
  ≔ refl (book_pointed_constant (BG G) (BB H))

def bridge_def_grphom_classifying (G H : Group) (hH : IsAbelian H)
  : Id Pointed (blind_grphom_classifying G H hH) (BG (abelian_hom_group G (mk_abelian_group H hH)))
  ≔ refl (BG (abelian_hom_group G (mk_abelian_group H hH)))

def bridge_aut_group_path (A : Type) (hA hA' : isGroupoid A) (a : A)
  : Id Group (automorphism_group A hA a) (automorphism_group A hA' a)
  ≔ map_path (isGroupoid A) Group (h ↦ automorphism_group A h a) hA hA' (isgroupoid_isprop A hA hA')

def bridge_def_grphom (G H : Group) (hH : IsAbelian H) (lvl : isGroupoid (BookPointedMap (BG G) (BlindBB H)))
  : Id Group (abelian_hom_group G (mk_abelian_group H hH)) (BlindGrpHom G H hH lvl)
  ≔ bridge_aut_group_path (BookPointedMap (BG G) (BB H)) (pointed_maps_bb_groupoid G H) lvl
      (book_pointed_constant (BG G) (BB H))

def bridge_def_grphom_sym (G H : Group) (hH : IsAbelian H)
  : Id Type (BlindGrpHomSym G H hH) (USym (abelian_hom_group G (mk_abelian_group H hH)))
  ≔ refl (USym (abelian_hom_group G (mk_abelian_group H hH)))

def bridge_def_grphom_mul (G H : Group) (hH : IsAbelian H) (p q : BlindGrpHomSym G H hH)
  : Id (USym (abelian_hom_group G (mk_abelian_group H hH))) (blind_grphom_mul G H hH p q) (usym_mul (abelian_hom_group G (mk_abelian_group H hH)) p q)
  ≔ refl (usym_mul (abelian_hom_group G (mk_abelian_group H hH)) p q)

def bridge_grphom_well_defined : blind_grphom_well_defined ≔ G H hH ↦ pointed_maps_bb_groupoid G H

{` Construction (abelian.tex:802). `}
def bridge_grphom_abstract_hom_equiv : blind_grphom_abstract_hom_equiv
  ≔ G H ↦ abelian_hom_abstract_book_equiv (G .fst) H

{` Lemma (abelian.tex:824), with E the equivalence of 802. `}
def bridge_grphom_equiv_pointwise_hom : blind_grphom_equiv_pointwise_hom
  ≔ G H ↦ (abelian_hom_abstract_book_equiv (G .fst) H,
           p q g ↦ map_path (AbstractHom (abstr (G .fst)) (abstr (H .fst))) (USym (H .fst)) (φ ↦ φ .fst g)
             (abelian_hom_abstract_map (G .fst) H (usym_mul (abelian_hom_group (G .fst) H) p q))
             (pointwise_hom_mul (G .fst) H (abelian_hom_abstract_map (G .fst) H p) (abelian_hom_abstract_map (G .fst) H q))
             (abelian_hom_abstract_mul (G .fst) H p q))

{` Lemma (abelian.tex:928). `}
def bridge_grphom_bb_maps_equiv : blind_grphom_bb_maps_equiv
  ≔ G H ↦ book_equivalence (USym (abelian_hom_group (G .fst) H)) (BookPointedMap (BB (G .fst)) (BB (H .fst)))
      (abelian_hom_usym_bb_equiv G H)
