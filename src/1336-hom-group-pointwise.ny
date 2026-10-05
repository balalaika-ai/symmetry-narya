export "1219-abelian-hom-abstract"
export "1300-abstract-rings"
export "702-abstract-group-identity"

{` Chapter 13 (fields.tex 853-1103): the group Hom(H, G) of homomorphisms
   into an abelian group and lem:grpHomOK. Hom(H, G) is abelian_hom_group of
   chapter 12 (module 1207). `}

{` Running text (fields.tex 892-900): BB G is a 2-type, so BH →* BB G is a
   2-type, pointed at the constant map at pt_{BB G} (pointed by refl); in
   fact it is a 1-type since the maps are pointed (module 1207). `}
def bh_pointed_maps_bb_two_type (H : Group) (G : Group)
  : HLevel (suc. (suc. (suc. (suc. zero.)))) (BookPointedMap (BG H) (BB G))
  ≔ hlevel_raise (suc. (suc. (suc. zero.))) (BookPointedMap (BG H) (BB G))
      (groupoid_to_hlevel (BookPointedMap (BG H) (BB G)) (pointed_maps_bb_groupoid H G))

{` def:AbHomgroup: Hom(H, G) ≔ Aut_{BH →* BB G}(cst_{pt_{BB G}}, refl). `}
def hom_group_definition (H : Group) (G : AbelianGroup)
  : Id Group (abelian_hom_group H G)
      (automorphism_group (BookPointedMap (BG H) (BB (G .fst))) (pointed_maps_bb_groupoid H (G .fst))
        (constant (BG H .carrier) (BB (G .fst) .carrier) (bb_point (G .fst)), refl (bb_point (G .fst))))
  ≔ refl (abelian_hom_group H G)

{` absHom_ptw(H, G) is abstract_hom_ptw_group of module 1300
   (xca:abs-homgroup with xca:abstract-group-of-maps). `}

{` lem:grpHomOK. The composite of the chain
   (sh = sh) ≃ (BH →* Ω(BB G)) (ptw_*) ≃ (BH →* BG) (ev ∘ -) ≃ absHom(abstr H, abstr G) (abstr)
   (abelian_hom_usym_equiv of module 1207 followed by abstr_hom, an
   equivalence by lem:homomabstrconcr) is an abstract isomorphism
   abstr(Hom(H, G)) ≅ absHom_ptw(abstr H, abstr G). The book's proof is
   unfinished; multiplicativity is the lemma at abelian.tex 824
   (abelian_hom_abstract_mul, module 1208). `}
def hom_group_abstract_iso (H : Group) (G : AbelianGroup)
  : AbstractIso (abstr (abelian_hom_group H G)) (abstract_hom_ptw_group (abstr H) (abstr (G .fst)) (G .snd))
  ≔ let K ≔ G .fst in
    let A ≔ AbstractHom (abstr H) (abstr K) in
    let F ≔ abelian_hom_abstract_map H G in
    (native_equivalence (USym (abelian_hom_group H G)) A (abelian_hom_abstract_book_equiv H G),
     p q ↦ concat A (F (usym_mul (abelian_hom_group H G) p q)) (pointwise_hom_mul H G (F p) (F q))
       (ptw_mul_hom (abstr H) (abstr K) (G .snd) (F p) (F q))
       (abelian_hom_abstract_mul H G p q)
       (abstract_hom_ext (abstr H) (abstr K) (pointwise_hom_mul H G (F p) (F q))
         (ptw_mul_hom (abstr H) (abstr K) (G .snd) (F p) (F q))
         (s ↦ refl (usym_mul K (F p .fst s) (F q .fst s)))))

{` The map of the isomorphism is the composite of the chain: p ↦ abstr(f_p),
   where f_p = abelian_hom_usym_equiv H G p has classifying map
   x ↦ ev(ptw(p)(x)) (abelian_hom_usym_function, module 1207). `}
def hom_group_abstract_iso_map (H : Group) (G : AbelianGroup) (p : USym (abelian_hom_group H G))
  : Id (AbstractHom (abstr H) (abstr (G .fst))) (hom_group_abstract_iso H G .fst .map p)
      (abstr_hom H (G .fst) (abelian_hom_usym_equiv H G .map p))
  ≔ refl (abstr_hom H (G .fst) (abelian_hom_usym_equiv H G .map p))

{` Running text (fields.tex 911-916): Hom(H, G) is the delooping of
   absHom_ptw(abstr H, abstr G) (identification of abstract groups) and
   consequently an abelian group. `}
def hom_group_abstract_path (H : Group) (G : AbelianGroup)
  : Id AbstractGroup (abstr (abelian_hom_group H G)) (abstract_hom_ptw_group (abstr H) (abstr (G .fst)) (G .snd))
  ≔ abstract_group_path_from_iso (abstr (abelian_hom_group H G)) (abstract_hom_ptw_group (abstr H) (abstr (G .fst)) (G .snd))
      (hom_group_abstract_iso H G)

def hom_group_is_abelian (H : Group) (G : AbelianGroup) : IsAbelian (abelian_hom_group H G)
  ≔ abelian_hom_group_abelian H G
