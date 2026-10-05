export "783-heap-translations"
export "437-conjugation-inner-automorphisms"

{` Chapter 7 (absgroup.tex), sec:heaps, the exercise at line 1391: the
   symmetry groups of the two endpoints of a heap are merely isomorphic;
   abelian heaps; for abelian heaps the endpoint groups are (purely,
   canonically) isomorphic. `}

{` For p : a = a', conjugation by p is an isomorphism and an identification
   of groups from the start group to the end group (exa:conj-concrete,
   module 437: the end group is group_at (start group) a', judgmentally). `}
def heap_endpoint_iso (H : Heap) (p : heap_usym H) : GroupIso (heap_start_group H) (heap_end_group H)
  ≔ conj_iso (heap_start_group H) (heap_end_shape H) p

def heap_endpoint_group_path (H : Heap) (p : heap_usym H) : Id Group (heap_start_group H) (heap_end_group H)
  ≔ conj_group_path (heap_start_group H) (heap_end_shape H) p

{` The endpoint groups are merely isomorphic, and merely equal (BH is
   connected). `}
def heap_endpoints_merely_iso (H : Heap) : Mere (GroupIso (heap_start_group H) (heap_end_group H))
  ≔ mere_rec (heap_usym H) (Mere (GroupIso (heap_start_group H) (heap_end_group H)))
      (mere_isprop (GroupIso (heap_start_group H) (heap_end_group H)))
      (p ↦ mere (GroupIso (heap_start_group H) (heap_end_group H)) (heap_endpoint_iso H p))
      (heap_pair_mere_point H)

def heap_endpoints_merely_equal (H : Heap) : Mere (Id Group (heap_start_group H) (heap_end_group H))
  ≔ mere_rec (heap_usym H) (Mere (Id Group (heap_start_group H) (heap_end_group H)))
      (mere_isprop (Id Group (heap_start_group H) (heap_end_group H)))
      (p ↦ mere (Id Group (heap_start_group H) (heap_end_group H)) (heap_endpoint_group_path H p))
      (heap_pair_mere_point H)

{` Abelian heaps (the book leaves the definition to the reader): the
   ternary operation is symmetric in its outer arguments, p q⁻¹ r = r q⁻¹ p
   for all p, q, r : a = a' (the classical definition of an abelian heap). `}
def IsAbelianHeap (H : Heap) : Type
  ≔ (p q r : heap_usym H) → Id (heap_usym H) (heap_ternary H p q r) (heap_ternary H r q p)

def is_abelian_heap_prop (H : Heap) : isProp (IsAbelianHeap H)
  ≔ let S ≔ heap_usym H in
    pi_prop S (p ↦ (q r : S) → Id S (heap_ternary H p q r) (heap_ternary H r q p))
      (p ↦ pi_prop S (q ↦ (r : S) → Id S (heap_ternary H p q r) (heap_ternary H r q p))
        (q ↦ pi_prop S (r ↦ Id S (heap_ternary H p q r) (heap_ternary H r q p))
          (r ↦ heap_usym_set H (heap_ternary H p q r) (heap_ternary H r q p))))

{` A heap is abelian iff its end group is abelian. `}
def heap_end_abelian_to_heap (H : Heap) (hab : IsAbelian (heap_end_group H)) : IsAbelianHeap H
  ≔ let A ≔ BHeap H in
    let a ≔ heap_start_shape H in
    let b ≔ heap_end_shape H in
    p q r ↦
      let g ≔ heap_end_loop H p q in
      let h ≔ heap_end_loop H r q in
      calc
        concat A a b b r g
        = concat A a b b (concat A a b b q h) g
          by refl ((t ↦ concat A a b b t g) : Id A a b → Id A a b)
            (inverse (Id A a b) (concat A a b b q h) r (heap_concat_cancel_pre A a b b q r))
        = concat A a b b q (concat A b b b h g) by concat_assoc A a b b b q h g
        = concat A a b b q (concat A b b b g h) by refl (concat A a b b q) (hab g h)
        = concat A a b b (concat A a b b q g) h
          by inverse (Id A a b) (concat A a b b (concat A a b b q g) h) (concat A a b b q (concat A b b b g h))
            (concat_assoc A a b b b q g h)
        = concat A a b b p h
          by refl ((t ↦ concat A a b b t h) : Id A a b → Id A a b) (heap_concat_cancel_pre A a b b q p) ∎

def heap_abelian_to_end (H : Heap) (hab : IsAbelianHeap H) : IsAbelian (heap_end_group H)
  ≔ let A ≔ BHeap H in
    let a ≔ heap_start_shape H in
    let b ≔ heap_end_shape H in
    let E ≔ USym (heap_end_group H) in
    g h ↦ mere_rec (heap_usym H) (Id E (usym_mul (heap_end_group H) g h) (usym_mul (heap_end_group H) h g))
      (usym_set (heap_end_group H) (usym_mul (heap_end_group H) g h) (usym_mul (heap_end_group H) h g))
      (r0 ↦
        let ir0 ≔ inverse A a b r0 in
        let pg ≔ concat A a b b r0 g in
        let ph ≔ concat A a b b r0 h in
        concat_cancel_left A a b b r0 (concat A b b b h g) (concat A b b b g h)
          (calc
            concat A a b b r0 (concat A b b b h g)
            = concat A a b b ph g
              by inverse (Id A a b) (concat A a b b ph g) (concat A a b b r0 (concat A b b b h g))
                (concat_assoc A a b b b r0 h g)
            = concat A a b b ph (concat A b a b ir0 pg)
              by refl (concat A a b b ph) (inverse E (concat A b a b ir0 pg) g (concat_left_inverse A a b b r0 g))
            = concat A a b b pg (concat A b a b ir0 ph) by hab pg r0 ph
            = concat A a b b pg h by refl (concat A a b b pg) (concat_left_inverse A a b b r0 h)
            = concat A a b b r0 (concat A b b b g h) by concat_assoc A a b b b r0 g h ∎))
      (heap_pair_mere_point H)

def heap_abelian_end_equiv (H : Heap) : Equiv (IsAbelianHeap H) (IsAbelian (heap_end_group H))
  ≔ iff_equiv (IsAbelianHeap H) (IsAbelian (heap_end_group H)) (is_abelian_heap_prop H)
      (is_abelian_prop (heap_end_group H)) (heap_abelian_to_end H) (heap_end_abelian_to_heap H)

{` The start group is abelian iff the end group is (they are merely
   equal); hence a heap is abelian iff its start group is abelian. `}
def heap_start_end_abelian (H : Heap) (hs : IsAbelian (heap_start_group H)) : IsAbelian (heap_end_group H)
  ≔ mere_rec (heap_usym H) (IsAbelian (heap_end_group H)) (is_abelian_prop (heap_end_group H))
      (p ↦ transport Group IsAbelian (heap_start_group H) (heap_end_group H) (heap_endpoint_group_path H p) hs)
      (heap_pair_mere_point H)

def heap_end_start_abelian (H : Heap) (he : IsAbelian (heap_end_group H)) : IsAbelian (heap_start_group H)
  ≔ mere_rec (heap_usym H) (IsAbelian (heap_start_group H)) (is_abelian_prop (heap_start_group H))
      (p ↦ transport Group IsAbelian (heap_end_group H) (heap_start_group H)
        (inverse Group (heap_start_group H) (heap_end_group H) (heap_endpoint_group_path H p)) he)
      (heap_pair_mere_point H)

def heap_abelian_start_equiv (H : Heap) : Equiv (IsAbelianHeap H) (IsAbelian (heap_start_group H))
  ≔ iff_equiv (IsAbelianHeap H) (IsAbelian (heap_start_group H)) (is_abelian_heap_prop H)
      (is_abelian_prop (heap_start_group H))
      (hab ↦ heap_end_start_abelian H (heap_abelian_to_end H hab))
      (hs ↦ heap_end_abelian_to_heap H (heap_start_end_abelian H hs))

{` Conjugation by p as an isomorphism of the abstract groups:
   g ↦ p g p⁻¹ (book order; loop_conjugate p g = concat p⁻¹ (concat g p)). `}
def heap_conj_abstract_iso (H : Heap) (p : heap_usym H)
  : AbstractIso (abstr (heap_start_group H)) (abstr (heap_end_group H))
  ≔ (conj_usym_equiv (heap_start_group H) (heap_end_shape H) p,
     abstr_hom (heap_start_group H) (heap_end_group H) (conj_hom (heap_start_group H) (heap_end_shape H) p) .snd)

{` If the loops at a commute, conjugation by p : a = b does not depend on
   p (path induction on p). `}
def heap_conj_constant_base (A : Type) (a : A)
  (hab : (g h : Id A a a) → Id (Id A a a) (concat A a a a h g) (concat A a a a g h)) (g : Id A a a)
  (p' : Id A a a)
  : Id (Id A a a) (loop_conjugate A a a (refl a) g) (loop_conjugate A a a p' g)
  ≔ calc
      concat A a a a (inverse A a a (refl a)) (concat A a a a g (refl a))
      = concat A a a a (refl a) (concat A a a a g (refl a))
        by refl ((t ↦ concat A a a a t (concat A a a a g (refl a))) : Id A a a → Id A a a) (inverse_refl A a)
      = concat A a a a g (refl a) by concat_1p A a a (concat A a a a g (refl a))
      = g by concat_p1 A a a g
      = concat A a a a (inverse A a a p') (concat A a a a p' g)
        by inverse (Id A a a) (concat A a a a (inverse A a a p') (concat A a a a p' g)) g
          (concat_left_inverse A a a a p' g)
      = concat A a a a (inverse A a a p') (concat A a a a g p')
        by refl (concat A a a a (inverse A a a p')) (hab g p') ∎

def heap_conj_constant (A : Type) (a : A)
  (hab : (g h : Id A a a) → Id (Id A a a) (concat A a a a h g) (concat A a a a g h)) (g : Id A a a)
  (b : A) (p p' : Id A a b)
  : Id (Id A b b) (loop_conjugate A a b p g) (loop_conjugate A a b p' g)
  ≔ J A a (y q ↦ (q' : Id A a y) → Id (Id A y y) (loop_conjugate A a y q g) (loop_conjugate A a y q' g))
      (heap_conj_constant_base A a hab g) b p p'

{` For an abelian heap the abstract conjugation isomorphisms agree for all
   p, p' : a = a'. `}
def heap_conj_abstract_constant (H : Heap) (hab : IsAbelianHeap H)
  : WeaklyConstant (heap_usym H) (AbstractIso (abstr (heap_start_group H)) (abstr (heap_end_group H)))
      (heap_conj_abstract_iso H)
  ≔ let G ≔ heap_start_group H in
    let A ≔ BHeap H in
    let a ≔ heap_start_shape H in
    let b ≔ heap_end_shape H in
    let hs ≔ heap_end_start_abelian H (heap_abelian_to_end H hab) in
    p p' ↦ abstract_iso_path (abstr G) (abstr (heap_end_group H)) (heap_conj_abstract_iso H p) (heap_conj_abstract_iso H p')
      (funext (USym G) (_ ↦ Id A b b) (usym_hom G (heap_end_group H) (conj_hom G b p))
        (usym_hom G (heap_end_group H) (conj_hom G b p'))
        (g ↦ calc
            usym_hom G (heap_end_group H) (conj_hom G b p) g = loop_conjugate A a b p g by conj_usym G b p g
            = loop_conjugate A a b p' g by heap_conj_constant A a hs g b p p'
            = usym_hom G (heap_end_group H) (conj_hom G b p') g
              by inverse (Id A b b) (usym_hom G (heap_end_group H) (conj_hom G b p') g) (loop_conjugate A a b p' g)
                (conj_usym G b p' g) ∎))

{` For abelian heaps the endpoint groups are purely isomorphic: the
   canonical isomorphism (as abstract groups) g ↦ p g p⁻¹, defined without
   choosing p (weakly constant elimination, thm:wconstant-elim), and equal
   to conjugation by every p. `}
def heap_canonical_abstract_iso (H : Heap) (hab : IsAbelianHeap H)
  : AbstractIso (abstr (heap_start_group H)) (abstr (heap_end_group H))
  ≔ weakly_constant_rec (heap_usym H) (AbstractIso (abstr (heap_start_group H)) (abstr (heap_end_group H)))
      (heap_conj_abstract_iso H) (abstract_iso_set (abstr (heap_start_group H)) (abstr (heap_end_group H)))
      (heap_conj_abstract_constant H hab) (heap_pair_mere_point H)

def heap_canonical_abstract_iso_value (H : Heap) (hab : IsAbelianHeap H) (p : heap_usym H)
  : Id (AbstractIso (abstr (heap_start_group H)) (abstr (heap_end_group H))) (heap_canonical_abstract_iso H hab)
      (heap_conj_abstract_iso H p)
  ≔ weakly_constant_rec_value (heap_usym H) (AbstractIso (abstr (heap_start_group H)) (abstr (heap_end_group H)))
      (heap_conj_abstract_iso H) (abstract_iso_set (abstr (heap_start_group H)) (abstr (heap_end_group H)))
      (heap_conj_abstract_constant H hab) (heap_pair_mere_point H) p

def heap_canonical_abstract_path (H : Heap) (hab : IsAbelianHeap H)
  : Id AbstractGroup (abstr (heap_start_group H)) (abstr (heap_end_group H))
  ≔ abstract_group_path_from_iso (abstr (heap_start_group H)) (abstr (heap_end_group H))
      (heap_canonical_abstract_iso H hab)
