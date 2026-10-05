export "784-abelian-heaps"
export "709-groups-are-abstract-groups"
export "710-hom-delooping"

{` Chapter 7 (absgroup.tex), sec:heaps, the parts of the exercises at lines
   1384 and 1391 that use thm:Groupsareidentitytypes (concr, module 709)
   and lem:homomabstrconcr (abstr_hom_equiv, module 710): the translation
   group of a heap as a (concrete) group, identified with the end group
   (and the variant with the start group); and for abelian heaps the
   canonical isomorphism of groups between the endpoint groups. `}

{` The map from heaps to groups of the exercise at line 1384:
   H ↦ concr(symmetries r ↦ p q⁻¹ r of USym H), identified with the
   symmetry group of the end shape. `}
def heap_translation_concrete_group (H : Heap) : Group ≔ concr (heap_translation_group H)

def heap_translation_concrete_end_path (H : Heap)
  : Id Group (heap_end_group H) (heap_translation_concrete_group H)
  ≔ concat Group (heap_end_group H) (concr (abstr (heap_end_group H))) (concr (heap_translation_group H))
      (inverse Group (concr (abstr (heap_end_group H))) (heap_end_group H) (concr_abstr_path (heap_end_group H)))
      (refl concr (heap_translation_end_path H))

{` The variant r ↦ r p⁻¹ q gives the start group. `}
def heap_translation_start_concrete_group (H : Heap) : Group ≔ concr (heap_translation_start_group H)

def heap_translation_start_concrete_path (H : Heap)
  : Id Group (heap_start_group H) (heap_translation_start_concrete_group H)
  ≔ concat Group (heap_start_group H) (concr (abstr (heap_start_group H))) (concr (heap_translation_start_group H))
      (inverse Group (concr (abstr (heap_start_group H))) (heap_start_group H) (concr_abstr_path (heap_start_group H)))
      (refl concr (heap_translation_start_path H))

{` For an abelian heap, the isomorphisms of groups "conjugation by p"
   (module 784, exa:conj-concrete) agree for all p, p' : a = a': their
   abstract homomorphisms agree, and abstr is injective on homomorphisms
   (lem:homomabstrconcr). `}
def heap_endpoint_iso_constant (H : Heap) (hab : IsAbelianHeap H)
  : WeaklyConstant (heap_usym H) (GroupIso (heap_start_group H) (heap_end_group H)) (heap_endpoint_iso H)
  ≔ let G ≔ heap_start_group H in
    let K ≔ heap_end_group H in
    let b ≔ heap_end_shape H in
    p p' ↦ subtype_equal (GroupHom G K) (IsGroupIso G K) (is_group_iso_prop G K) (heap_endpoint_iso H p)
      (heap_endpoint_iso H p')
      (equivalence_injective (GroupHom G K) (AbstractHom (abstr G) (abstr K)) (abstr_hom_equiv G K)
        (conj_hom G b p) (conj_hom G b p')
        (abstract_hom_ext (abstr G) (abstr K) (abstr_hom G K (conj_hom G b p)) (abstr_hom G K (conj_hom G b p'))
          (g ↦ heap_conj_abstract_constant H hab p p' .fst .map (refl g))))

{` The exercise at line 1391, second part: for abelian heaps the symmetry
   groups of the endpoints are purely isomorphic. The canonical isomorphism
   is defined without choosing p (thm:wconstant-elim) and equals
   conjugation by every p; it is an identification of groups, and its
   abstract homomorphism is the canonical abstract isomorphism of module 784. `}
def heap_canonical_iso (H : Heap) (hab : IsAbelianHeap H) : GroupIso (heap_start_group H) (heap_end_group H)
  ≔ weakly_constant_rec (heap_usym H) (GroupIso (heap_start_group H) (heap_end_group H)) (heap_endpoint_iso H)
      (group_iso_set (heap_start_group H) (heap_end_group H)) (heap_endpoint_iso_constant H hab) (heap_pair_mere_point H)

def heap_canonical_iso_value (H : Heap) (hab : IsAbelianHeap H) (p : heap_usym H)
  : Id (GroupIso (heap_start_group H) (heap_end_group H)) (heap_canonical_iso H hab) (heap_endpoint_iso H p)
  ≔ weakly_constant_rec_value (heap_usym H) (GroupIso (heap_start_group H) (heap_end_group H)) (heap_endpoint_iso H)
      (group_iso_set (heap_start_group H) (heap_end_group H)) (heap_endpoint_iso_constant H hab) (heap_pair_mere_point H) p

def heap_canonical_group_path (H : Heap) (hab : IsAbelianHeap H) : Id Group (heap_start_group H) (heap_end_group H)
  ≔ group_path_from_iso (heap_start_group H) (heap_end_group H) (heap_canonical_iso H hab)

def heap_canonical_iso_abstract (H : Heap) (hab : IsAbelianHeap H)
  : Id (AbstractHom (abstr (heap_start_group H)) (abstr (heap_end_group H)))
      (abstr_hom (heap_start_group H) (heap_end_group H) (heap_canonical_iso H hab .fst))
      (abstract_iso_hom (abstr (heap_start_group H)) (abstr (heap_end_group H)) (heap_canonical_abstract_iso H hab))
  ≔ let G ≔ heap_start_group H in
    let K ≔ heap_end_group H in
    let M ≔ AbstractHom (abstr G) (abstr K) in
    let x ≔ abstr_hom G K (heap_canonical_iso H hab .fst) in
    let y ≔ abstract_iso_hom (abstr G) (abstr K) (heap_canonical_abstract_iso H hab) in
    mere_rec (heap_usym H) (Id M x y) (abstract_hom_set (abstr G) (abstr K) x y)
      (p ↦ concat M x (abstr_hom G K (heap_endpoint_iso H p .fst)) y
        (refl ((φ ↦ abstr_hom G K (φ .fst)) : GroupIso G K → M) (heap_canonical_iso_value H hab p))
        (inverse M y (abstract_iso_hom (abstr G) (abstr K) (heap_conj_abstract_iso H p))
          (refl (abstract_iso_hom (abstr G) (abstr K)) (heap_canonical_abstract_iso_value H hab p))))
      (heap_pair_mere_point H)
