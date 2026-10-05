export "1208-abelian-hom-pointwise"
export "710-hom-delooping"

{` Chapter 12, construction at abelian.tex 802, last step: with
   lem:homomabstrconcr of chapter 7 (abstr_hom_is_equiv, module 710) the
   hypothesis AbstrHomIsEquiv of module 1207 is discharged, giving the
   bijection USym(Hom(G, H)) ≃ absHom(G, H) without hypotheses. Its map is
   p ↦ abstr(hom_of_symmetry p), and by the lemma at abelian.tex 824
   (abelian_hom_abstract_mul, module 1208) it sends products in
   abstr(Hom(G, H)) to pointwise products. Kept apart from the chapter 12
   core so that the core does not depend on chapter 7. `}
def abelian_hom_abstract_book_equiv (G : Group) (H : AbelianGroup)
  : BookEquiv (USym (abelian_hom_group G H)) (AbstractHom (abstr G) (abstr (H .fst)))
  ≔ abelian_hom_abstract_equiv G H (abstr_hom_is_equiv G (H .fst))

def abelian_hom_abstract_book_equiv_map (G : Group) (H : AbelianGroup) (p : USym (abelian_hom_group G H))
  : Id (AbstractHom (abstr G) (abstr (H .fst)))
      (abelian_hom_abstract_book_equiv G H .map p) (abelian_hom_abstract_map G H p)
  ≔ refl (abelian_hom_abstract_map G H p)
