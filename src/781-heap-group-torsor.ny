export "780-heaps"
export "504-torsors"

{` Chapter 7 (absgroup.tex), sec:heaps, xca:group+torsor-heap (line 1356)
   and the running text after it (lines 1360-1369): the two equivalences
   l, r : Heap ≃ Σ_{G : Group} BG, the equivalence c : Group ≃ Σ_{H : Heap}
   USym H, the two descriptions of a heap as a group with a torsor
   (lem:BGbytorsor), and the type of heaps is a groupoid. `}

{` The book's Σ_{G : Group} BG and Σ_{G : Group} Torsor_G. `}
def GroupWithBGPoint : Type ≔ Σ Group (G ↦ BG G .carrier)

def GroupWithTorsor : Type ≔ Σ Group Torsors

{` l takes the start shape as designated shape and keeps the end shape as a
   point of BG; its inverse is (G, y) ↦ (BG, sh_G, y). Both round trips
   hold judgmentally (record eta). `}
def heap_left_map (H : Heap) : GroupWithBGPoint ≔ (heap_start_group H, heap_end_shape H)

def heap_left_equiv : Equiv Heap GroupWithBGPoint
  ≔ quasi_inverse_equiv Heap GroupWithBGPoint heap_left_map (u ↦ heap_with_end (u .fst) (u .snd))
      (H ↦ refl H) (u ↦ refl u)

{` r takes the end shape as designated shape and keeps the start shape as a
   point of BG; its inverse is (G, y) ↦ (BG, y, sh_G). `}
def heap_right_map (H : Heap) : GroupWithBGPoint ≔ (heap_end_group H, heap_start_shape H)

def heap_right_equiv : Equiv Heap GroupWithBGPoint
  ≔ quasi_inverse_equiv Heap GroupWithBGPoint heap_right_map (u ↦ heap_with_start (u .fst) (u .snd))
      (H ↦ refl H) (u ↦ refl u)

{` Litmus: l and r of a doubled heap are (G, sh_G); l and r differ on a
   heap (BG, sh_G, y) in which group they produce. `}
def heap_left_double (G : Group) : Id GroupWithBGPoint (heap_left_equiv .map (group_heap G)) (G, shape G)
  ≔ refl (G, shape G)

def heap_right_double (G : Group) : Id GroupWithBGPoint (heap_right_equiv .map (group_heap G)) (G, shape G)
  ≔ refl (G, shape G)

def heap_right_with_end (G : Group) (y : BG G .carrier)
  : Id GroupWithBGPoint (heap_right_equiv .map (heap_with_end G y))
      (mkgroup (BG G .carrier, y, bg_connected G, bg_groupoid G), shape G)
  ≔ refl (heap_right_equiv .map (heap_with_end G y))

{` c : Group ≃ Σ_{H : Heap} USym H, G ↦ (doubled heap, refl sh_G) (the lift
   of the doubling map); its inverse takes the start group. One round trip
   is judgmental; the other contracts the end shape and the chosen
   identification p : a = a' to (a, refl a) in the contractible type
   Σ(y : A)(a = y) (lem:thepathspaceiscontractible). `}
def heap_double_section (u : Σ Heap heap_usym)
  : Id (Σ Heap heap_usym) (group_heap_lift (heap_start_group (u .fst))) u
  ≔ let H ≔ u .fst in
    let A ≔ BHeap H in
    let a ≔ heap_start_shape H in
    let φ : Σ A (y ↦ Id A a y) → Σ Heap heap_usym
      ≔ v ↦ (mkheap (A, a, v .fst, bh_connected H, bh_groupoid H), v .snd) in
    refl φ (inverse (Σ A (y ↦ Id A a y)) (heap_end_shape H, u .snd) (a, refl a)
      (iscontr_idfrom A a .contract (heap_end_shape H, u .snd)))

def heap_double_equiv : Equiv Group (Σ Heap heap_usym)
  ≔ quasi_inverse_equiv Group (Σ Heap heap_usym) group_heap_lift (u ↦ heap_start_group (u .fst))
      (G ↦ refl G) heap_double_section

def heap_double_equiv_map (G : Group) : Id (Σ Heap heap_usym) (heap_double_equiv .map G) (group_heap G, refl (shape G))
  ≔ refl (group_heap_lift G)

{` A heap is the same as a group G together with a G-torsor, in two ways:
   via l the group is the start group and the torsor is P_{a'} (paths from
   the end shape), via r the group is the end group and the torsor is P_a.
   This composes l, r with lem:BGbytorsor (bg_torsors_equiv, module 504). `}
def bg_torsors_family_equiv : Equiv GroupWithBGPoint GroupWithTorsor
  ≔ family_equiv Group (G ↦ BG G .carrier) Torsors
      (G ↦ native_equivalence (BG G .carrier) (Torsors G) (bg_torsors_equiv G))

def heap_left_torsor_equiv : Equiv Heap GroupWithTorsor
  ≔ compose_equiv Heap GroupWithBGPoint GroupWithTorsor heap_left_equiv bg_torsors_family_equiv

def heap_right_torsor_equiv : Equiv Heap GroupWithTorsor
  ≔ compose_equiv Heap GroupWithBGPoint GroupWithTorsor heap_right_equiv bg_torsors_family_equiv

def heap_left_torsor_value (H : Heap)
  : Id GroupWithTorsor (heap_left_torsor_equiv .map H)
      (heap_start_group H, bg_to_torsors (heap_start_group H) (heap_end_shape H))
  ≔ refl (heap_left_torsor_equiv .map H)

def heap_right_torsor_value (H : Heap)
  : Id GroupWithTorsor (heap_right_torsor_equiv .map H)
      (heap_end_group H, bg_to_torsors (heap_end_group H) (heap_start_shape H))
  ≔ refl (heap_right_torsor_equiv .map H)

{` The torsor attached by l is P_{a'}: its value at the start shape is
   (a' = a), the inverse direction of USym H. `}
def heap_left_torsor_underlying (H : Heap)
  : Id Type (gset_underlying (heap_start_group H) (bg_to_torsors (heap_start_group H) (heap_end_shape H) .fst))
      (Id (BHeap H) (heap_end_shape H) (heap_start_shape H))
  ≔ refl (Id (BHeap H) (heap_end_shape H) (heap_start_shape H))

{` "The type of heaps is a (large) groupoid": transfer along l from
   Σ_{G : Group} BG (Group is a groupoid, xca:typegroupisgroupoid, and each
   BG is a groupoid). Narya has a single universe, so largeness is not
   recorded. `}
def heap_type_groupoid : isGroupoid Heap
  ≔ let n3 : Nat ≔ suc. (suc. (suc. zero.)) in
    hlevel_to_groupoid Heap
      (hlevel_equiv n3 GroupWithBGPoint Heap (canonical_inverse_equiv Heap GroupWithBGPoint heap_left_equiv)
        (hlevel_sigma n3 Group (G ↦ BG G .carrier) (groupoid_to_hlevel Group group_groupoid)
          (G ↦ groupoid_to_hlevel (BG G .carrier) (bg_groupoid G))))

{` The types Σ_{G : Group} BG and Σ_{G : Group} Torsor_G are groupoids as
   well. `}
def group_with_torsor_groupoid : isGroupoid GroupWithTorsor
  ≔ let n3 : Nat ≔ suc. (suc. (suc. zero.)) in
    hlevel_to_groupoid GroupWithTorsor
      (hlevel_sigma n3 Group Torsors (groupoid_to_hlevel Group group_groupoid)
        (G ↦ groupoid_to_hlevel (Torsors G) (torsors_groupoid G)))
