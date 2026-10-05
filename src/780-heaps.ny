export "404-group-examples"

{` Chapter 7 (absgroup.tex), sec:heaps, lines 1289-1365: bipointed connected
   groupoids (def:bipt-conn-groupoid), heaps (def:heap), the start and end
   shapes, ISym and the underlying identifications USym : Heap → Set, the
   doubling map (a functor) from groups to heaps, its lift to heaps with a
   chosen identification, and the two maps (functors) from heaps to groups
   taking the start or the end shape as designated shape. `}

{` The book's U^{=1}, "the type of connected groupoids", is not displayed;
   by analogy with def:pt-conn-groupoid (U^{=1}_* ≔ Σ(A : U)(A × isconn(A) ×
   isgrpd(A)), module 400) it is Σ(A : U)(isconn(A) × isgrpd(A)). `}
def ConnectedGroupoids : Type ≔ Σ Type (A ↦ Product (Connected A) (isGroupoid A))

{` def:bipt-conn-groupoid, literally: U^{=1}_{••} ≔ Σ(A : U^{=1})(A × A). `}
def BipointedConnectedGroupoidSigma : Type ≔ Σ ConnectedGroupoids (A ↦ Product (A .fst) (A .fst))

{` The record form used below: (A, a, a') with the two endpoints a (start)
   and a' (finish), and the two witnesses. bpcg_sigma_equiv identifies it
   with the printed Σ-form; both round trips hold by reflexivity. `}
def BipointedConnectedGroupoid : Type ≔ sig (
  carrier : Type,
  start : carrier,
  finish : carrier,
  connected : Connected carrier,
  groupoid : isGroupoid carrier)

def bpcg_sigma_equiv : Equiv BipointedConnectedGroupoid BipointedConnectedGroupoidSigma
  ≔ quasi_inverse_equiv BipointedConnectedGroupoid BipointedConnectedGroupoidSigma
      (X ↦ ((X .carrier, (X .connected, X .groupoid)), (X .start, X .finish)))
      (Y ↦ (Y .fst .fst, Y .snd .fst, Y .snd .snd, Y .fst .snd .fst, Y .fst .snd .snd))
      (X ↦ refl X) (Y ↦ refl Y)

{` def:heap. Heap ≔ Copy_mkheap(U^{=1}_{••}). Exactly as Group in module 400
   (def:typegroup), the wrapped copy is a one-field record rather than the
   data type Copy of module 16: records have judgmental eta, so
   mkheap (heap_B H) ≡ H and heap_B (mkheap X) ≡ X hold by definition, the
   induction principle of the copy is trivial, and identity types of Heap
   compute fieldwise. `}
def Heap : Type ≔ sig (classifying : BipointedConnectedGroupoid)

def mkheap (X : BipointedConnectedGroupoid) : Heap ≔ (classifying ≔ X)

{` The destructor B : Heap → U^{=1}_{••}; heap_B H is the classifying type BH. `}
def heap_B (H : Heap) : BipointedConnectedGroupoid ≔ H .classifying

def heap_eta (H : Heap) : Id Heap (mkheap (heap_B H)) H ≔ refl H

def heap_beta (X : BipointedConnectedGroupoid) : Id BipointedConnectedGroupoid (heap_B (mkheap X)) X ≔ refl X

def heap_classifying_equiv : Equiv Heap BipointedConnectedGroupoid
  ≔ quasi_inverse_equiv Heap BipointedConnectedGroupoid heap_B mkheap (H ↦ refl H) (X ↦ refl X)

{` The underlying type of BH, the start shape (first point) and the end
   shape (second point). `}
def BHeap (H : Heap) : Type ≔ H .classifying .carrier

def heap_start_shape (H : Heap) : BHeap H ≔ H .classifying .start

def heap_end_shape (H : Heap) : BHeap H ≔ H .classifying .finish

def bh_connected (H : Heap) : Connected (BHeap H) ≔ H .classifying .connected

def bh_groupoid (H : Heap) : isGroupoid (BHeap H) ≔ H .classifying .groupoid

{` ISym(A, a, a') ≔ (a = a'), a set because A is a groupoid; as a map
   ISym : U^{=1}_{••} → Set it is isym_settype. `}
def ISym (X : BipointedConnectedGroupoid) : Type ≔ Id (X .carrier) (X .start) (X .finish)

def isym_set (X : BipointedConnectedGroupoid) : isSet (ISym X) ≔ X .groupoid (X .start) (X .finish)

def isym_settype (X : BipointedConnectedGroupoid) : SetTypes ≔ (ISym X, isym_set X)

{` USym : Heap → Set, mkheap X ↦ ISym X: the underlying identifications
   (start shape = end shape) of a heap. `}
def heap_usym (H : Heap) : Type ≔ ISym (heap_B H)

def heap_usym_set (H : Heap) : isSet (heap_usym H) ≔ isym_set (heap_B H)

def heap_usym_settype (H : Heap) : SetTypes ≔ isym_settype (heap_B H)

def heap_usym_mkheap (X : BipointedConnectedGroupoid)
  : Id SetTypes (heap_usym_settype (mkheap X)) (isym_settype X)
  ≔ refl (isym_settype X)

def heap_usym_unfold (H : Heap)
  : Id Type (heap_usym H) (Id (BHeap H) (heap_start_shape H) (heap_end_shape H))
  ≔ refl (heap_usym H)

{` The obvious map from groups to heaps, doubling the point: keep the
   classifying type and use the designated shape as start and end shape.
   Its underlying identifications are USym G, judgmentally. `}
def group_heap (G : Group) : Heap
  ≔ mkheap (BG G .carrier, shape G, shape G, bg_connected G, bg_groupoid G)

def group_heap_usym (G : Group) : Id Type (heap_usym (group_heap G)) (USym G) ≔ refl (USym G)

{` "This map lifts to the type of heaps with a chosen identification":
   G ↦ (group_heap G, refl sh_G). `}
def group_heap_lift (G : Group) : Σ Heap heap_usym ≔ (group_heap G, refl (shape G))

def group_heap_lift_fst (G : Group) : Id Heap (group_heap_lift G .fst) (group_heap G) ≔ refl (group_heap G)

{` The two obvious maps from heaps to groups: the start or the end shape as
   designated shape (USym of these groups is (a = a), resp. (a' = a')). `}
def heap_start_group (H : Heap) : Group
  ≔ mkgroup (BHeap H, heap_start_shape H, bh_connected H, bh_groupoid H)

def heap_end_group (H : Heap) : Group
  ≔ mkgroup (BHeap H, heap_end_shape H, bh_connected H, bh_groupoid H)

def heap_start_group_usym (H : Heap)
  : Id Type (USym (heap_start_group H)) (Id (BHeap H) (heap_start_shape H) (heap_start_shape H))
  ≔ refl (USym (heap_start_group H))

def heap_end_group_usym (H : Heap)
  : Id Type (USym (heap_end_group H)) (Id (BHeap H) (heap_end_shape H) (heap_end_shape H))
  ≔ refl (USym (heap_end_group H))

{` Both maps are retractions of the doubling map, judgmentally. `}
def heap_start_group_double (G : Group) : Id Group (heap_start_group (group_heap G)) G ≔ refl G

def heap_end_group_double (G : Group) : Id Group (heap_end_group (group_heap G)) G ≔ refl G

{` The heaps (BG, sh_G, y) and (BG, y, sh_G) of a group G and a point y of
   BG (used for the inverses of the equivalences l and r of
   xca:group+torsor-heap, module 781). `}
def heap_with_end (G : Group) (y : BG G .carrier) : Heap
  ≔ mkheap (BG G .carrier, shape G, y, bg_connected G, bg_groupoid G)

def heap_with_start (G : Group) (y : BG G .carrier) : Heap
  ≔ mkheap (BG G .carrier, y, shape G, bg_connected G, bg_groupoid G)

def heap_with_end_double (G : Group) : Id Heap (heap_with_end G (shape G)) (group_heap G) ≔ refl (group_heap G)

def heap_with_end_end_group (G : Group) (y : BG G .carrier)
  : Id Group (heap_end_group (heap_with_end G y)) (mkgroup (BG G .carrier, y, bg_connected G, bg_groupoid G))
  ≔ refl (heap_end_group (heap_with_end G y))

{` Morphisms of heaps, for the functoriality claims of the running text.
   The book does not define them; by analogy with def:grouphomomorphism a
   morphism H → K is a bipointed map BH → BK, with the book's orientation of
   the pointing paths (start_K = f(start_H) and end_K = f(end_H)). `}
def HeapHom (H K : Heap) : Type
  ≔ Σ (BHeap H → BHeap K) (f ↦
      Product (Id (BHeap K) (heap_start_shape K) (f (heap_start_shape H)))
        (Id (BHeap K) (heap_end_shape K) (f (heap_end_shape H))))

def heap_hom_id (H : Heap) : HeapHom H H
  ≔ (identity (BHeap H), (refl (heap_start_shape H), refl (heap_end_shape H)))

{` heap_hom_compose H K L f g is g ∘ f (f first), pointed at both endpoints
   as book_pointed_compose (module 98). `}
def heap_hom_compose (H K L : Heap) (f : HeapHom H K) (g : HeapHom K L) : HeapHom H L
  ≔ (x ↦ g .fst (f .fst x),
     (concat (BHeap L) (heap_start_shape L) (g .fst (heap_start_shape K)) (g .fst (f .fst (heap_start_shape H)))
        (g .snd .fst) (refl (g .fst) (f .snd .fst)),
      concat (BHeap L) (heap_end_shape L) (g .fst (heap_end_shape K)) (g .fst (f .fst (heap_end_shape H)))
        (g .snd .snd) (refl (g .fst) (f .snd .snd))))

{` The doubling map is a functor: f ↦ (Bf÷, Bf_pt, Bf_pt), preserving
   identities and composition judgmentally. `}
def group_heap_hom (G K : Group) (f : GroupHom G K) : HeapHom (group_heap G) (group_heap K)
  ≔ (hom_function G K f, (hom_point G K f, hom_point G K f))

def group_heap_hom_id (G : Group)
  : Id (HeapHom (group_heap G) (group_heap G)) (group_heap_hom G G (group_hom_id G)) (heap_hom_id (group_heap G))
  ≔ refl (heap_hom_id (group_heap G))

def group_heap_hom_compose (G K L : Group) (f : GroupHom G K) (g : GroupHom K L)
  : Id (HeapHom (group_heap G) (group_heap L)) (group_heap_hom G L (group_hom_compose G K L f g))
      (heap_hom_compose (group_heap G) (group_heap K) (group_heap L) (group_heap_hom G K f) (group_heap_hom K L g))
  ≔ refl (group_heap_hom G L (group_hom_compose G K L f g))

{` The two maps from heaps to groups are functors: a morphism of heaps
   forgets one of its two pointings. Identities and composition are
   preserved judgmentally. `}
def heap_start_hom (H K : Heap) (f : HeapHom H K) : GroupHom (heap_start_group H) (heap_start_group K)
  ≔ mkhom (heap_start_group H) (heap_start_group K) (f .fst, f .snd .fst)

def heap_end_hom (H K : Heap) (f : HeapHom H K) : GroupHom (heap_end_group H) (heap_end_group K)
  ≔ mkhom (heap_end_group H) (heap_end_group K) (f .fst, f .snd .snd)

def heap_start_hom_id (H : Heap)
  : Id (GroupHom (heap_start_group H) (heap_start_group H)) (heap_start_hom H H (heap_hom_id H))
      (group_hom_id (heap_start_group H))
  ≔ refl (group_hom_id (heap_start_group H))

def heap_end_hom_id (H : Heap)
  : Id (GroupHom (heap_end_group H) (heap_end_group H)) (heap_end_hom H H (heap_hom_id H))
      (group_hom_id (heap_end_group H))
  ≔ refl (group_hom_id (heap_end_group H))

def heap_start_hom_compose (H K L : Heap) (f : HeapHom H K) (g : HeapHom K L)
  : Id (GroupHom (heap_start_group H) (heap_start_group L)) (heap_start_hom H L (heap_hom_compose H K L f g))
      (group_hom_compose (heap_start_group H) (heap_start_group K) (heap_start_group L)
        (heap_start_hom H K f) (heap_start_hom K L g))
  ≔ refl (heap_start_hom H L (heap_hom_compose H K L f g))

def heap_end_hom_compose (H K L : Heap) (f : HeapHom H K) (g : HeapHom K L)
  : Id (GroupHom (heap_end_group H) (heap_end_group L)) (heap_end_hom H L (heap_hom_compose H K L f g))
      (group_hom_compose (heap_end_group H) (heap_end_group K) (heap_end_group L)
        (heap_end_hom H K f) (heap_end_hom K L g))
  ≔ refl (heap_end_hom H L (heap_hom_compose H K L f g))

{` Composite functors: start (or end) after doubling is the identity
   functor, judgmentally. `}
def heap_start_hom_double (G K : Group) (f : GroupHom G K)
  : Id (GroupHom G K) (heap_start_hom (group_heap G) (group_heap K) (group_heap_hom G K f)) f
  ≔ refl f

def heap_end_hom_double (G K : Group) (f : GroupHom G K)
  : Id (GroupHom G K) (heap_end_hom (group_heap G) (group_heap K) (group_heap_hom G K f)) f
  ≔ refl f

{` Litmus: the doubled heap of the cyclic group C_m has classifying type
   CycleComponent m, both shapes the principal point, and USym ≡ USym C_m. `}
def heap_cyclic_double_carrier (m : Nat) : Id Type (BHeap (group_heap (cyclic_group m))) (CycleComponent m)
  ≔ refl (CycleComponent m)

def heap_cyclic_double_usym (m : Nat)
  : Id Type (heap_usym (group_heap (cyclic_group m))) (USym (cyclic_group m))
  ≔ refl (USym (cyclic_group m))
