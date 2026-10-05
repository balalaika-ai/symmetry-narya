export "780-heaps"
export "782-symmetry-image-groups"
export "702-abstract-group-identity"

{` Chapter 7 (absgroup.tex), sec:heaps, lines 1371-1389: the ternary
   operation of a heap, the symmetries r ↦ p q⁻¹ r of the set USym H, when
   two pairs give the same symmetry, their composition, the group they form
   (the exercise at line 1384: an abstract group of symmetries of USym H),
   its identification with the symmetry group of the end shape, and the
   variant r ↦ r p⁻¹ q, which gives the symmetry group of the start shape.

   Composition convention. The book writes qp (also q·p, q∘p) for
   trans(p)(q) = "first p, then q" (def:eq-trans), i.e. concat p q here
   (module 400 likewise documents that the book's g·h on USym G is
   concat h g). For p, q, r : a = a' the word p q⁻¹ r is therefore: first
   r : a = a', then q⁻¹ : a' = a, then p : a = a'. We bracket it as
   (p q⁻¹) r = concat r (concat q⁻¹ p), so that r ↦ p q⁻¹ r is
   post-composition with the symmetry p q⁻¹ = concat q⁻¹ p of the end shape
   (module 413 brackets the same word as p (q⁻¹ r); module 785 compares). `}

{` The symmetries p q⁻¹ (book order) of the end shape a' and q⁻¹ p of the
   start shape a determined by p, q : a = a'. `}
def heap_end_loop (H : Heap) (p q : heap_usym H) : USym (heap_end_group H)
  ≔ concat (BHeap H) (heap_end_shape H) (heap_start_shape H) (heap_end_shape H)
      (inverse (BHeap H) (heap_start_shape H) (heap_end_shape H) q) p

def heap_start_loop (H : Heap) (p q : heap_usym H) : USym (heap_start_group H)
  ≔ concat (BHeap H) (heap_start_shape H) (heap_end_shape H) (heap_start_shape H)
      p (inverse (BHeap H) (heap_start_shape H) (heap_end_shape H) q)

{` The symmetries of the end shape act on USym H by post-composition,
   g · r ≔ g r = concat r g (the action of the end group on the torsor
   z ↦ (a = z) of module 500); those of the start shape by
   g · r ≔ r g⁻¹ = concat g⁻¹ r. Both are left actions (below). `}
def heap_end_act (H : Heap) (g : USym (heap_end_group H)) (r : heap_usym H) : heap_usym H
  ≔ concat (BHeap H) (heap_start_shape H) (heap_end_shape H) (heap_end_shape H) r g

def heap_start_act (H : Heap) (g : USym (heap_start_group H)) (r : heap_usym H) : heap_usym H
  ≔ concat (BHeap H) (heap_start_shape H) (heap_start_shape H) (heap_end_shape H)
      (inverse (BHeap H) (heap_start_shape H) (heap_start_shape H) g) r

{` The ternary operation (p, q, r) ↦ p q⁻¹ r of rem:heap-preview and of
   the running text, bracketed as (p q⁻¹) r. `}
def heap_ternary (H : Heap) (p q r : heap_usym H) : heap_usym H
  ≔ concat (BHeap H) (heap_start_shape H) (heap_end_shape H) (heap_end_shape H) r
      (concat (BHeap H) (heap_end_shape H) (heap_start_shape H) (heap_end_shape H)
        (inverse (BHeap H) (heap_start_shape H) (heap_end_shape H) q) p)

{` The symmetry r ↦ p q⁻¹ r of USym H; it is post-composition with the
   end-shape symmetry p q⁻¹, judgmentally. `}
def heap_translation (H : Heap) (p q : heap_usym H) : heap_usym H → heap_usym H
  ≔ r ↦ heap_ternary H p q r

def heap_translation_end_act (H : Heap) (p q : heap_usym H)
  : Id (heap_usym H → heap_usym H) (heap_translation H p q) (heap_end_act H (heap_end_loop H p q))
  ≔ refl (heap_translation H p q)

{` Path algebra: p · (p⁻¹ · q) = q in concatenation order. `}
def heap_concat_cancel_pre (A : Type) (x y z : A) (p : Id A x y) (q : Id A x z)
  : Id (Id A x z) (concat A x y z p (concat A y x z (inverse A x y p) q)) q
  ≔ calc
      concat A x y z p (concat A y x z (inverse A x y p) q)
      = concat A x x z (concat A x y x p (inverse A x y p)) q
        by inverse (Id A x z) (concat A x x z (concat A x y x p (inverse A x y p)) q)
          (concat A x y z p (concat A y x z (inverse A x y p) q)) (concat_assoc A x y x z p (inverse A x y p) q)
      = concat A x x z (refl x) q
        by refl ((t ↦ concat A x x z t q) : Id A x x → Id A x z) (concat_inverse_right A x y p)
      = q by concat_1p A x z q ∎

{` A mere element of USym H (BH is connected). `}
def heap_pair_mere_point (H : Heap) : Mere (heap_usym H)
  ≔ bh_connected H .snd (heap_start_shape H) (heap_end_shape H)

def heap_translation_fun_set (H : Heap) : isSet (heap_usym H → heap_usym H)
  ≔ pi_set (heap_usym H) (_ ↦ heap_usym H) (_ ↦ heap_usym_set H)

{` (p, q) and (p', q') determine the same symmetry iff p q⁻¹ = p' q'⁻¹
   (equal symmetries of the end shape). All types are propositions, so this
   is a logical equivalence, stated as an equivalence. `}
def heap_translation_same_end (H : Heap) (p q p' q' : heap_usym H)
  : Equiv (Id (heap_usym H → heap_usym H) (heap_translation H p q) (heap_translation H p' q'))
      (Id (USym (heap_end_group H)) (heap_end_loop H p q) (heap_end_loop H p' q'))
  ≔ let A ≔ BHeap H in
    let a ≔ heap_start_shape H in
    let b ≔ heap_end_shape H in
    iff_equiv (Id (heap_usym H → heap_usym H) (heap_translation H p q) (heap_translation H p' q'))
      (Id (USym (heap_end_group H)) (heap_end_loop H p q) (heap_end_loop H p' q'))
      (heap_translation_fun_set H (heap_translation H p q) (heap_translation H p' q'))
      (usym_set (heap_end_group H) (heap_end_loop H p q) (heap_end_loop H p' q'))
      (e ↦ concat_cancel_left A a b b q (heap_end_loop H p q) (heap_end_loop H p' q') (e (refl q)))
      (e ↦ refl (heap_end_act H) e)

{` p q⁻¹ = p' q'⁻¹ iff p'⁻¹ p = q'⁻¹ q (equal symmetries of the start
   shape; p'⁻¹ p = concat p p'⁻¹ = heap_start_loop H p p'). `}
def heap_end_to_start_loop (H : Heap) (p q p' q' : heap_usym H)
  (e : Id (USym (heap_end_group H)) (heap_end_loop H p q) (heap_end_loop H p' q'))
  : Id (USym (heap_start_group H)) (heap_start_loop H p p') (heap_start_loop H q q')
  ≔ let A ≔ BHeap H in
    let a ≔ heap_start_shape H in
    let b ≔ heap_end_shape H in
    let iq ≔ inverse A a b q in
    let iq' ≔ inverse A a b q' in
    let ip' ≔ inverse A a b p' in
    calc
      concat A a b a p ip'
      = concat A a b a (concat A a b b q (concat A b a b iq p)) ip'
        by refl ((t ↦ concat A a b a t ip') : Id A a b → Id A a a)
          (inverse (Id A a b) (concat A a b b q (concat A b a b iq p)) p (heap_concat_cancel_pre A a b b q p))
      = concat A a b a (concat A a b b q (concat A b a b iq' p')) ip'
        by refl ((t ↦ concat A a b a (concat A a b b q t) ip') : Id A b b → Id A a a) e
      = concat A a b a q (concat A b b a (concat A b a b iq' p') ip')
        by concat_assoc A a b b a q (concat A b a b iq' p') ip'
      = concat A a b a q iq' by refl (concat A a b a q) (concat_cancel_inverse_right A b a b iq' p') ∎

def heap_start_to_end_loop (H : Heap) (p q p' q' : heap_usym H)
  (e : Id (USym (heap_start_group H)) (heap_start_loop H p p') (heap_start_loop H q q'))
  : Id (USym (heap_end_group H)) (heap_end_loop H p q) (heap_end_loop H p' q')
  ≔ let A ≔ BHeap H in
    let a ≔ heap_start_shape H in
    let b ≔ heap_end_shape H in
    let iq ≔ inverse A a b q in
    let iq' ≔ inverse A a b q' in
    let ip' ≔ inverse A a b p' in
    calc
      concat A b a b iq p
      = concat A b a b iq (concat A a a b (concat A a b a p ip') p')
        by refl (concat A b a b iq)
          (inverse (Id A a b) (concat A a a b (concat A a b a p ip') p') p (concat_inverse_cancel_right A a b a p p'))
      = concat A b a b iq (concat A a a b (concat A a b a q iq') p')
        by refl ((t ↦ concat A b a b iq (concat A a a b t p')) : Id A a a → Id A b b) e
      = concat A b a b iq (concat A a b b q (concat A b a b iq' p'))
        by refl (concat A b a b iq) (concat_assoc A a b a b q iq' p')
      = concat A b a b iq' p' by concat_left_inverse A a b b q (concat A b a b iq' p') ∎

def heap_end_loop_start_loop (H : Heap) (p q p' q' : heap_usym H)
  : Equiv (Id (USym (heap_end_group H)) (heap_end_loop H p q) (heap_end_loop H p' q'))
      (Id (USym (heap_start_group H)) (heap_start_loop H p p') (heap_start_loop H q q'))
  ≔ iff_equiv (Id (USym (heap_end_group H)) (heap_end_loop H p q) (heap_end_loop H p' q'))
      (Id (USym (heap_start_group H)) (heap_start_loop H p p') (heap_start_loop H q q'))
      (usym_set (heap_end_group H) (heap_end_loop H p q) (heap_end_loop H p' q'))
      (usym_set (heap_start_group H) (heap_start_loop H p p') (heap_start_loop H q q'))
      (heap_end_to_start_loop H p q p' q') (heap_start_to_end_loop H p q p' q')

{` The end action is a left action: (g·h) · r = g · (h · r), with
   g·h = usym_mul = concat h g. `}
def heap_end_act_mul (H : Heap) (g h : USym (heap_end_group H)) (r : heap_usym H)
  : Id (heap_usym H) (heap_end_act H (usym_mul (heap_end_group H) g h) r) (heap_end_act H g (heap_end_act H h r))
  ≔ let A ≔ BHeap H in
    let a ≔ heap_start_shape H in
    let b ≔ heap_end_shape H in
    inverse (Id A a b) (concat A a b b (concat A a b b r h) g) (concat A a b b r (concat A b b b h g))
      (concat_assoc A a b b b r h g)

{` Composition: (p, q)(p', q') = (p q⁻¹ p', q') = (p, q' p'⁻¹ q). First on
   end-shape symmetries: p q⁻¹ p' with q'⁻¹ ... `}
def heap_end_loop_ternary_left (H : Heap) (p q p' q' : heap_usym H)
  : Id (USym (heap_end_group H)) (heap_end_loop H (heap_ternary H p q p') q')
      (usym_mul (heap_end_group H) (heap_end_loop H p q) (heap_end_loop H p' q'))
  ≔ let A ≔ BHeap H in
    let a ≔ heap_start_shape H in
    let b ≔ heap_end_shape H in
    let iq' ≔ inverse A a b q' in
    let g ≔ heap_end_loop H p q in
    inverse (Id A b b) (concat A b b b (concat A b a b iq' p') g) (concat A b a b iq' (concat A a b b p' g))
      (concat_assoc A b a b b iq' p' g)

def heap_end_loop_ternary_right (H : Heap) (p q p' q' : heap_usym H)
  : Id (USym (heap_end_group H)) (heap_end_loop H p (heap_ternary H q' p' q))
      (usym_mul (heap_end_group H) (heap_end_loop H p q) (heap_end_loop H p' q'))
  ≔ let A ≔ BHeap H in
    let a ≔ heap_start_shape H in
    let b ≔ heap_end_shape H in
    let iq ≔ inverse A a b q in
    let iq' ≔ inverse A a b q' in
    let ip' ≔ inverse A a b p' in
    let X ≔ concat A b a b ip' q' in
    let invX : Id (Id A b b) (inverse A b b X) (concat A b a b iq' p')
      ≔ calc
          inverse A b b X = concat A b a b iq' (inverse A b a ip') by inverse_concat A b a b ip' q'
          = concat A b a b iq' p' by refl (concat A b a b iq') (inverse_inverse A a b p') ∎ in
    calc
      concat A b a b (inverse A a b (concat A a b b q X)) p
      = concat A b a b (concat A b b a (inverse A b b X) iq) p
        by refl ((t ↦ concat A b a b t p) : Id A b a → Id A b b) (inverse_concat A a b b q X)
      = concat A b a b (concat A b b a (concat A b a b iq' p') iq) p
        by refl ((t ↦ concat A b a b (concat A b b a t iq) p) : Id A b b → Id A b b) invX
      = concat A b b b (concat A b a b iq' p') (concat A b a b iq p)
        by concat_assoc A b b a b (concat A b a b iq' p') iq p ∎

{` The composition laws for the symmetries of USym H themselves. `}
def heap_translation_compose_left (H : Heap) (p q p' q' : heap_usym H)
  : Id (heap_usym H → heap_usym H) (r ↦ heap_translation H p q (heap_translation H p' q' r))
      (heap_translation H (heap_ternary H p q p') q')
  ≔ let E ≔ USym (heap_end_group H) in
    let g ≔ heap_end_loop H p q in
    let g' ≔ heap_end_loop H p' q' in
    let k ≔ heap_end_loop H (heap_ternary H p q p') q' in
    funext (heap_usym H) (_ ↦ heap_usym H) (r ↦ heap_translation H p q (heap_translation H p' q' r))
      (heap_translation H (heap_ternary H p q p') q')
      (r ↦ concat (heap_usym H) (heap_end_act H g (heap_end_act H g' r))
        (heap_end_act H (usym_mul (heap_end_group H) g g') r) (heap_end_act H k r)
        (inverse (heap_usym H) (heap_end_act H (usym_mul (heap_end_group H) g g') r)
          (heap_end_act H g (heap_end_act H g' r)) (heap_end_act_mul H g g' r))
        (refl ((t ↦ heap_end_act H t r) : E → heap_usym H)
          (inverse E k (usym_mul (heap_end_group H) g g') (heap_end_loop_ternary_left H p q p' q'))))

def heap_translation_compose_right (H : Heap) (p q p' q' : heap_usym H)
  : Id (heap_usym H → heap_usym H) (r ↦ heap_translation H p q (heap_translation H p' q' r))
      (heap_translation H p (heap_ternary H q' p' q))
  ≔ let E ≔ USym (heap_end_group H) in
    let g ≔ heap_end_loop H p q in
    let g' ≔ heap_end_loop H p' q' in
    let k ≔ heap_end_loop H p (heap_ternary H q' p' q) in
    funext (heap_usym H) (_ ↦ heap_usym H) (r ↦ heap_translation H p q (heap_translation H p' q' r))
      (heap_translation H p (heap_ternary H q' p' q))
      (r ↦ concat (heap_usym H) (heap_end_act H g (heap_end_act H g' r))
        (heap_end_act H (usym_mul (heap_end_group H) g g') r) (heap_end_act H k r)
        (inverse (heap_usym H) (heap_end_act H (usym_mul (heap_end_group H) g g') r)
          (heap_end_act H g (heap_end_act H g' r)) (heap_end_act_mul H g g' r))
        (refl ((t ↦ heap_end_act H t r) : E → heap_usym H)
          (inverse E k (usym_mul (heap_end_group H) g g') (heap_end_loop_ternary_right H p q p' q'))))

{` The translations as equivalences of USym H. `}
def heap_end_act_equiv (H : Heap) (g : USym (heap_end_group H)) : Equiv (heap_usym H) (heap_usym H)
  ≔ let A ≔ BHeap H in
    let a ≔ heap_start_shape H in
    let b ≔ heap_end_shape H in
    quasi_inverse_equiv (heap_usym H) (heap_usym H) (heap_end_act H g) (heap_end_act H (inverse A b b g))
      (r ↦ concat_cancel_inverse_right A a b b r g) (r ↦ concat_inverse_cancel_right A a b b r g)

def heap_translation_equiv (H : Heap) (p q : heap_usym H) : Equiv (heap_usym H) (heap_usym H)
  ≔ heap_end_act_equiv H (heap_end_loop H p q)

def heap_translation_equiv_map (H : Heap) (p q : heap_usym H)
  : Id (heap_usym H → heap_usym H) (heap_translation_equiv H p q .map) (heap_translation H p q)
  ≔ refl (heap_translation H p q)

{` Every end-shape symmetry is some p q⁻¹ (merely: from a mere r₀ : a = a',
   g = (r₀ g) r₀⁻¹ ... in book order, i.e. (concat r₀ g, r₀)). `}
def heap_end_loop_surjective (H : Heap)
  : Surjective (Product (heap_usym H) (heap_usym H)) (USym (heap_end_group H)) (u ↦ heap_end_loop H (u .fst) (u .snd))
  ≔ let A ≔ BHeap H in
    let a ≔ heap_start_shape H in
    let b ≔ heap_end_shape H in
    let I ≔ Product (heap_usym H) (heap_usym H) in
    let σ : I → USym (heap_end_group H) ≔ u ↦ heap_end_loop H (u .fst) (u .snd) in
    g ↦ mere_rec (heap_usym H) (Mere (BookFiber I (USym (heap_end_group H)) σ g))
      (mere_isprop (BookFiber I (USym (heap_end_group H)) σ g))
      (r0 ↦ mere (BookFiber I (USym (heap_end_group H)) σ g)
        ((concat A a b b r0 g, r0),
         inverse (Id A b b) (concat A b a b (inverse A a b r0) (concat A a b b r0 g)) g
           (concat_left_inverse A a b b r0 g)))
      (heap_pair_mere_point H)

def heap_end_symmetry_data (H : Heap) : SymmetryImageData (heap_usym H)
  ≔ (heap_usym_set H, abstr (heap_end_group H), heap_end_act_equiv H, heap_end_act_mul H,
     Product (heap_usym H) (heap_usym H), u ↦ heap_end_loop H (u .fst) (u .snd), heap_end_loop_surjective H)

{` The exercise at line 1384: the symmetries r ↦ p q⁻¹ r of USym H form a
   group under composition (an abstract group, the image of
   (p, q) ↦ heap_translation_equiv H p q in USym H ≃ USym H). `}
def heap_translation_group (H : Heap) : AbstractGroup ≔ symmetry_image_group (heap_usym H) (heap_end_symmetry_data H)

def heap_translation_group_carrier (H : Heap)
  : Id Type (heap_translation_group H .carrier)
      (Image (Product (heap_usym H) (heap_usym H)) (Equiv (heap_usym H) (heap_usym H))
        (u ↦ heap_translation_equiv H (u .fst) (u .snd)))
  ≔ refl (heap_translation_group H .carrier)

{` The end action is faithful (USym H is merely inhabited). `}
def heap_end_act_injective (H : Heap) : SymmetryActInjective (heap_usym H) (heap_end_symmetry_data H)
  ≔ let A ≔ BHeap H in
    let a ≔ heap_start_shape H in
    let b ≔ heap_end_shape H in
    g h e ↦ mere_rec (heap_usym H) (Id (USym (heap_end_group H)) g h) (usym_set (heap_end_group H) g h)
      (r0 ↦ concat_cancel_left A a b b r0 g h (e r0)) (heap_pair_mere_point H)

{` "Can you identify the resulting group with the symmetry group of the
   start or end shape?": it is the symmetry group of the end shape, via
   g ↦ (r ↦ g r); hence an identification of abstract groups. `}
def heap_translation_end_iso (H : Heap) : AbstractIso (abstr (heap_end_group H)) (heap_translation_group H)
  ≔ symmetry_image_iso (heap_usym H) (heap_end_symmetry_data H) (heap_end_act_injective H)

def heap_translation_end_path (H : Heap) : Id AbstractGroup (abstr (heap_end_group H)) (heap_translation_group H)
  ≔ abstract_group_path_from_iso (abstr (heap_end_group H)) (heap_translation_group H) (heap_translation_end_iso H)

{` The other endpoint: use the symmetries r ↦ r p⁻¹ q (= heap_ternary H r p q)
   instead. They are the actions r ↦ r g⁻¹ of the start-shape symmetries
   g = q⁻¹ p (book order), and form a group identified with the symmetry
   group of the start shape. `}
def heap_translation_start (H : Heap) (p q : heap_usym H) : heap_usym H → heap_usym H
  ≔ r ↦ heap_ternary H r p q

def heap_start_act_ternary (H : Heap) (p q r : heap_usym H)
  : Id (heap_usym H) (heap_start_act H (heap_start_loop H p q) r) (heap_translation_start H p q r)
  ≔ let A ≔ BHeap H in
    let a ≔ heap_start_shape H in
    let b ≔ heap_end_shape H in
    let iq ≔ inverse A a b q in
    let ip ≔ inverse A a b p in
    calc
      concat A a a b (inverse A a a (concat A a b a p iq)) r
      = concat A a a b (concat A a b a (inverse A b a iq) ip) r
        by refl ((t ↦ concat A a a b t r) : Id A a a → Id A a b) (inverse_concat A a b a p iq)
      = concat A a a b (concat A a b a q ip) r
        by refl ((t ↦ concat A a a b (concat A a b a t ip) r) : Id A a b → Id A a b) (inverse_inverse A a b q)
      = concat A a b b q (concat A b a b ip r) by concat_assoc A a b a b q ip r ∎

def heap_start_act_mul (H : Heap) (g h : USym (heap_start_group H)) (r : heap_usym H)
  : Id (heap_usym H) (heap_start_act H (usym_mul (heap_start_group H) g h) r) (heap_start_act H g (heap_start_act H h r))
  ≔ let A ≔ BHeap H in
    let a ≔ heap_start_shape H in
    let b ≔ heap_end_shape H in
    calc
      concat A a a b (inverse A a a (concat A a a a h g)) r
      = concat A a a b (concat A a a a (inverse A a a g) (inverse A a a h)) r
        by refl ((t ↦ concat A a a b t r) : Id A a a → Id A a b) (inverse_concat A a a a h g)
      = concat A a a b (inverse A a a g) (concat A a a b (inverse A a a h) r)
        by concat_assoc A a a a b (inverse A a a g) (inverse A a a h) r ∎

def heap_start_act_equiv (H : Heap) (g : USym (heap_start_group H)) : Equiv (heap_usym H) (heap_usym H)
  ≔ let A ≔ BHeap H in
    let a ≔ heap_start_shape H in
    let b ≔ heap_end_shape H in
    quasi_inverse_equiv (heap_usym H) (heap_usym H) (heap_start_act H g) (r ↦ concat A a a b g r)
      (r ↦ heap_concat_cancel_pre A a a b g r) (r ↦ concat_left_inverse A a a b g r)

def heap_start_loop_surjective (H : Heap)
  : Surjective (Product (heap_usym H) (heap_usym H)) (USym (heap_start_group H)) (u ↦ heap_start_loop H (u .fst) (u .snd))
  ≔ let A ≔ BHeap H in
    let a ≔ heap_start_shape H in
    let b ≔ heap_end_shape H in
    let I ≔ Product (heap_usym H) (heap_usym H) in
    let σ : I → USym (heap_start_group H) ≔ u ↦ heap_start_loop H (u .fst) (u .snd) in
    g ↦ mere_rec (heap_usym H) (Mere (BookFiber I (USym (heap_start_group H)) σ g))
      (mere_isprop (BookFiber I (USym (heap_start_group H)) σ g))
      (r0 ↦ mere (BookFiber I (USym (heap_start_group H)) σ g)
        ((concat A a a b g r0, r0),
         inverse (Id A a a) (concat A a b a (concat A a a b g r0) (inverse A a b r0)) g
           (concat_cancel_inverse_right A a a b g r0)))
      (heap_pair_mere_point H)

def heap_start_symmetry_data (H : Heap) : SymmetryImageData (heap_usym H)
  ≔ (heap_usym_set H, abstr (heap_start_group H), heap_start_act_equiv H, heap_start_act_mul H,
     Product (heap_usym H) (heap_usym H), u ↦ heap_start_loop H (u .fst) (u .snd), heap_start_loop_surjective H)

def heap_translation_start_group (H : Heap) : AbstractGroup
  ≔ symmetry_image_group (heap_usym H) (heap_start_symmetry_data H)

{` The generating symmetries of this group are exactly r ↦ r p⁻¹ q. `}
def heap_translation_start_family (H : Heap) (p q r : heap_usym H)
  : Id (heap_usym H) (symmetry_image_map (heap_usym H) (heap_start_symmetry_data H) (p, q) .map r)
      (heap_translation_start H p q r)
  ≔ heap_start_act_ternary H p q r

def heap_start_act_injective (H : Heap) : SymmetryActInjective (heap_usym H) (heap_start_symmetry_data H)
  ≔ let A ≔ BHeap H in
    let a ≔ heap_start_shape H in
    let b ≔ heap_end_shape H in
    g h e ↦ mere_rec (heap_usym H) (Id (USym (heap_start_group H)) g h) (usym_set (heap_start_group H) g h)
      (r0 ↦ calc
          g = inverse A a a (inverse A a a g)
            by inverse (Id A a a) (inverse A a a (inverse A a a g)) g (inverse_inverse A a a g)
          = inverse A a a (inverse A a a h)
            by refl (inverse A a a) (concat_cancel_right A a a b (inverse A a a g) (inverse A a a h) r0 (e r0))
          = h by inverse_inverse A a a h ∎)
      (heap_pair_mere_point H)

def heap_translation_start_iso (H : Heap) : AbstractIso (abstr (heap_start_group H)) (heap_translation_start_group H)
  ≔ symmetry_image_iso (heap_usym H) (heap_start_symmetry_data H) (heap_start_act_injective H)

def heap_translation_start_path (H : Heap)
  : Id AbstractGroup (abstr (heap_start_group H)) (heap_translation_start_group H)
  ≔ abstract_group_path_from_iso (abstr (heap_start_group H)) (heap_translation_start_group H)
      (heap_translation_start_iso H)

{` Composition of the variant: (p, q)(p', q') = (p q'⁻¹ p', q), on
   start-shape symmetries and on the maps r ↦ r p⁻¹ q. `}
def heap_start_loop_ternary (H : Heap) (p q p' q' : heap_usym H)
  : Id (USym (heap_start_group H)) (heap_start_loop H (heap_ternary H p q' p') q)
      (usym_mul (heap_start_group H) (heap_start_loop H p q) (heap_start_loop H p' q'))
  ≔ let A ≔ BHeap H in
    let a ≔ heap_start_shape H in
    let b ≔ heap_end_shape H in
    let iq ≔ inverse A a b q in
    let iq' ≔ inverse A a b q' in
    calc
      concat A a b a (concat A a b b p' (concat A b a b iq' p)) iq
      = concat A a b a p' (concat A b b a (concat A b a b iq' p) iq)
        by concat_assoc A a b b a p' (concat A b a b iq' p) iq
      = concat A a b a p' (concat A b a a iq' (concat A a b a p iq))
        by refl (concat A a b a p') (concat_assoc A b a b a iq' p iq)
      = concat A a a a (concat A a b a p' iq') (concat A a b a p iq)
        by inverse (Id A a a) (concat A a a a (concat A a b a p' iq') (concat A a b a p iq))
          (concat A a b a p' (concat A b a a iq' (concat A a b a p iq)))
          (concat_assoc A a b a a p' iq' (concat A a b a p iq)) ∎

def heap_translation_start_compose (H : Heap) (p q p' q' r : heap_usym H)
  : Id (heap_usym H) (heap_translation_start H p q (heap_translation_start H p' q' r))
      (heap_translation_start H (heap_ternary H p q' p') q r)
  ≔ let S ≔ heap_usym H in
    let E ≔ USym (heap_start_group H) in
    let s ≔ heap_start_loop H p q in
    let s' ≔ heap_start_loop H p' q' in
    let k ≔ heap_start_loop H (heap_ternary H p q' p') q in
    calc
      heap_translation_start H p q (heap_translation_start H p' q' r)
      = heap_translation_start H p q (heap_start_act H s' r)
        by refl (heap_translation_start H p q)
          (inverse S (heap_start_act H s' r) (heap_translation_start H p' q' r) (heap_start_act_ternary H p' q' r))
      = heap_start_act H s (heap_start_act H s' r)
        by inverse S (heap_start_act H s (heap_start_act H s' r)) (heap_translation_start H p q (heap_start_act H s' r))
          (heap_start_act_ternary H p q (heap_start_act H s' r))
      = heap_start_act H (usym_mul (heap_start_group H) s s') r
        by inverse S (heap_start_act H (usym_mul (heap_start_group H) s s') r) (heap_start_act H s (heap_start_act H s' r))
          (heap_start_act_mul H s s' r)
      = heap_start_act H k r
        by refl ((t ↦ heap_start_act H t r) : E → S)
          (inverse E k (usym_mul (heap_start_group H) s s') (heap_start_loop_ternary H p q p' q'))
      = heap_translation_start H (heap_ternary H p q' p') q r by heap_start_act_ternary H (heap_ternary H p q' p') q r ∎
