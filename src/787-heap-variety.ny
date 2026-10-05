export "785-pointed-heaps"
export "781-heap-group-torsor"
export "709-groups-are-abstract-groups"

{` Chapter 7 (absgroup.tex), sec:heaps, xca:heap-variety (line 1408), using
   thm:Groupsareidentitytypes (group_abstract_group_equiv, module 709):
   for a set S the fiber Σ_{H : Heap}(S = USym H) is a set; for a ternary
   operation t on S the fiber of H ↦ (USym H, (p, q, r) ↦ p q⁻¹ r) at (S, t)
   is a proposition, equivalent to "S is merely inhabited and t satisfies
   the heap equations t(x, x, y) = y, t(x, y, y) = x,
   t(t(x, y, z), u, v) = t(x, y, t(z, u, v))". `}

{` The fiber of (H, p) ↦ (USym H, p q⁻¹ r, p) over a pointed ternary set X
   is the proposition "X satisfies the heap equations": reindex along
   c : Group ≃ Σ_H USym H (xca:group+torsor-heap, module 781) and
   abstr : Group ≃ AbstractGroup (module 709) — for a group G both
   composites send G to (USym G, x y⁻¹ z, refl) judgmentally — and use
   abstract groups = pointed heaps (module 785). `}
def heap_pointed_fiber_laws_equiv (X : PointedTernarySets)
  : Equiv (BookFiber (Σ Heap heap_usym) PointedTernarySets heap_pointed_structure X) (PointedHeapLaws X)
  ≔ let U ≔ Σ Heap heap_usym in
    let P ≔ PointedTernarySets in
    let FG ≔ BookFiber Group P (G ↦ abstract_group_pointed_ternary (abstr G)) X in
    compose_equiv (BookFiber U P heap_pointed_structure X) FG (PointedHeapLaws X)
      (canonical_inverse_equiv FG (BookFiber U P heap_pointed_structure X)
        (preequivalence_fiber_equiv Group U P heap_double_equiv heap_pointed_structure X))
      (compose_equiv FG (BookFiber AbstractGroup P abstract_group_pointed_ternary X) (PointedHeapLaws X)
        (preequivalence_fiber_equiv Group AbstractGroup P group_abstract_group_equiv abstract_group_pointed_ternary X)
        (abstract_group_pointed_fiber_equiv X))

{` Hence, for every s : S, the fiber of H ↦ (USym H, p q⁻¹ r) at (S, t) is
   equivalent to the heap equations (module 785, heap_pointed_fiber_equiv). `}
def heap_ternary_fiber_pointed_equiv (X : TernarySets) (s : X .fst .fst)
  : Equiv (BookFiber Heap TernarySets heap_ternary_structure X) (HeapEquations (X .fst .fst) (X .snd))
  ≔ compose_equiv (BookFiber Heap TernarySets heap_ternary_structure X)
      (BookFiber (Σ Heap heap_usym) PointedTernarySets heap_pointed_structure (X, s))
      (HeapEquations (X .fst .fst) (X .snd))
      (canonical_inverse_equiv (BookFiber (Σ Heap heap_usym) PointedTernarySets heap_pointed_structure (X, s))
        (BookFiber Heap TernarySets heap_ternary_structure X) (heap_pointed_fiber_equiv X s))
      (heap_pointed_fiber_laws_equiv (X, s))

def heap_equiv_prop (A B : Type) (e : Equiv A B) (hB : isProp B) : isProp A
  ≔ u v ↦ equivalence_injective A B e u v (hB (e .map u) (e .map v))

{` xca:heap-variety, second part: the fiber at (S, t) is a proposition (an
   element gives a mere element of S, and then the fiber is equivalent to
   the heap equations, a proposition since S is a set). `}
def heap_ternary_fiber_prop (X : TernarySets) : isProp (BookFiber Heap TernarySets heap_ternary_structure X)
  ≔ let F ≔ BookFiber Heap TernarySets heap_ternary_structure X in
    let S ≔ X .fst .fst in
    let h : F → isProp F
      ≔ w ↦ mere_rec S (isProp F) (isprop_isprop F)
          (s ↦ heap_equiv_prop F (HeapEquations S (X .snd)) (heap_ternary_fiber_pointed_equiv X s)
            (heap_equations_prop S (X .fst .snd) (X .snd)))
          (heap_fiber_laws X w .fst) in
    u v ↦ h u u v

{` "Describe this proposition in terms of equations": the fiber at (S, t)
   is equivalent to Mere S × (heap equations for t). `}
def heap_ternary_fiber_equiv (X : TernarySets)
  : Equiv (BookFiber Heap TernarySets heap_ternary_structure X) (TernaryHeapLaws X)
  ≔ let F ≔ BookFiber Heap TernarySets heap_ternary_structure X in
    let S ≔ X .fst .fst in
    iff_equiv F (TernaryHeapLaws X) (heap_ternary_fiber_prop X) (heap_laws_prop S (X .fst .snd) (X .snd))
      (heap_fiber_laws X)
      (l ↦ mere_rec S F (heap_ternary_fiber_prop X)
        (s ↦ equiv_inverse_map F (HeapEquations S (X .snd)) (heap_ternary_fiber_pointed_equiv X s) (l .snd))
        (l .fst))

{` The converse as a construction: a merely inhabited set with a ternary
   operation satisfying the heap equations is (USym H, p q⁻¹ r) for a heap H
   (built from the abstract group of a chosen point by concr). `}
def heap_from_laws (X : TernarySets) (l : TernaryHeapLaws X) : BookFiber Heap TernarySets heap_ternary_structure X
  ≔ equiv_inverse_map (BookFiber Heap TernarySets heap_ternary_structure X) (TernaryHeapLaws X)
      (heap_ternary_fiber_equiv X) l

{` xca:heap-variety, first part: for a set S, the fiber
   USym⁻¹(S) ≡ Σ_{H : Heap}(S = USym H) is a set. It is the sum over
   ternary operations t on S of the fibers at (S, t)
   (projection_composite_fiber_equiv, module 104), which are propositions. `}
def heap_usym_fiber_ternary_equiv (S : SetTypes)
  : Equiv (Σ (Ternary (S .fst)) (t ↦ BookFiber Heap TernarySets heap_ternary_structure (S, t)))
      (BookFiber Heap SetTypes heap_usym_settype S)
  ≔ projection_composite_fiber_equiv Heap SetTypes (X ↦ Ternary (X .fst)) heap_ternary_structure S

def heap_usym_fiber_set (S : SetTypes) : isSet (BookFiber Heap SetTypes heap_usym_settype S)
  ≔ let A ≔ Σ (Ternary (S .fst)) (t ↦ BookFiber Heap TernarySets heap_ternary_structure (S, t)) in
    hlevel_two_to_set (BookFiber Heap SetTypes heap_usym_settype S)
      (hlevel_equiv (suc. (suc. zero.)) A (BookFiber Heap SetTypes heap_usym_settype S)
        (heap_usym_fiber_ternary_equiv S)
        (set_to_hlevel_two A
          (sigma_set (Ternary (S .fst)) (t ↦ BookFiber Heap TernarySets heap_ternary_structure (S, t))
            (pi_set (Product (S .fst) (Product (S .fst) (S .fst))) (_ ↦ S .fst) (_ ↦ S .snd))
            (t ↦ prop_is_set (BookFiber Heap TernarySets heap_ternary_structure (S, t))
              (heap_ternary_fiber_prop (S, t))))))
