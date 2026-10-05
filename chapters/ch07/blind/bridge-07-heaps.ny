export "bridge-00-core"
export "07-heaps"
export "../../../src/786-heap-concrete-groups"
export "../../../src/787-heap-variety"

{` Bridges for absgroup.tex, sec:heaps (lines 1289-1420).

   The blind Σ-form of bipointed connected groupoids and our record form
   (carrier, start, finish, connected, groupoid) are inverse up to eta, so
   bridge_heap : BlindHeap → Heap has refl round trips, and the blind start
   and end shapes, USym, the start and end groups, l, r, c, the ternary
   operation, abelian heaps and the ternary structure all agree with ours
   judgmentally after bridge_heap. The blind group of shears r ↦ p q⁻¹ r
   lives in USym H → USym H (a subtype by a mere fiber), ours in the image
   in USym H ≃ USym H; bridge_hshear_image_equiv identifies them and is an
   abstract isomorphism with the blind composition group. `}

{` def:bipt-conn-groupoid. `}
def bridge_def_conn_groupoid : Id Type BlindConnGroupoid ConnectedGroupoids ≔ refl ConnectedGroupoids

def bridge_def_bipcg_sigma : Id Type BlindBiPCG BipointedConnectedGroupoidSigma
  ≔ refl BipointedConnectedGroupoidSigma

def bridge_bipcg (X : BlindBiPCG) : BipointedConnectedGroupoid
  ≔ (X .fst .fst, X .snd .fst, X .snd .snd, X .fst .snd .fst, X .fst .snd .snd)

def bridge_bipcg_inv (X : BipointedConnectedGroupoid) : BlindBiPCG
  ≔ ((X .carrier, (X .connected, X .groupoid)), (X .start, X .finish))

def bridge_def_bipcg : Equiv BlindBiPCG BipointedConnectedGroupoid
  ≔ quasi_inverse_equiv BlindBiPCG BipointedConnectedGroupoid bridge_bipcg bridge_bipcg_inv (X ↦ refl X) (X ↦ refl X)

{` def:heap. `}
def bridge_heap (H : BlindHeap) : Heap ≔ mkheap (bridge_bipcg (H .classifying))

def bridge_heap_inv (H : Heap) : BlindHeap ≔ blind_mkheap (bridge_bipcg_inv (heap_B H))

def bridge_def_heap : Equiv BlindHeap Heap
  ≔ quasi_inverse_equiv BlindHeap Heap bridge_heap bridge_heap_inv (H ↦ refl H) (H ↦ refl H)

def bridge_def_mkheap (X : BlindBiPCG) : Id Heap (bridge_heap (blind_mkheap X)) (mkheap (bridge_bipcg X))
  ≔ refl (mkheap (bridge_bipcg X))

def bridge_def_heap_carrier (H : BlindHeap) : Id Type (blind_heap_carrier H) (BHeap (bridge_heap H))
  ≔ refl (blind_heap_carrier H)

def bridge_def_heap_start (H : BlindHeap) : Id (BHeap (bridge_heap H)) (blind_heap_start H) (heap_start_shape (bridge_heap H))
  ≔ refl (blind_heap_start H)

def bridge_def_heap_end (H : BlindHeap) : Id (BHeap (bridge_heap H)) (blind_heap_end H) (heap_end_shape (bridge_heap H))
  ≔ refl (blind_heap_end H)

def bridge_def_heap_usym (H : BlindHeap) : Id SetTypes (blind_heap_usym_set H) (heap_usym_settype (bridge_heap H))
  ≔ refl (blind_heap_usym_set H)

def bridge_def_heap_start_group (H : BlindHeap) : Id Group (blind_heap_start_group H) (heap_start_group (bridge_heap H))
  ≔ refl (blind_heap_start_group H)

def bridge_def_heap_end_group (H : BlindHeap) : Id Group (blind_heap_end_group H) (heap_end_group (bridge_heap H))
  ≔ refl (blind_heap_end_group H)

{` The maps l, r and c of xca:group+torsor-heap. `}
def bridge_def_heap_l (H : BlindHeap) : Id GroupWithBGPoint (blind_heap_l H) (heap_left_map (bridge_heap H))
  ≔ refl (blind_heap_l H)

def bridge_def_heap_r (H : BlindHeap) : Id GroupWithBGPoint (blind_heap_r H) (heap_right_map (bridge_heap H))
  ≔ refl (blind_heap_r H)

def bridge_heap_lift (u : Σ BlindHeap blind_heap_usym) : Σ Heap heap_usym ≔ (bridge_heap (u .fst), u .snd)

def bridge_heap_lift_inv (u : Σ Heap heap_usym) : Σ BlindHeap blind_heap_usym ≔ (bridge_heap_inv (u .fst), u .snd)

def bridge_def_heap_lift : Equiv (Σ BlindHeap blind_heap_usym) (Σ Heap heap_usym)
  ≔ quasi_inverse_equiv (Σ BlindHeap blind_heap_usym) (Σ Heap heap_usym) bridge_heap_lift bridge_heap_lift_inv
      (u ↦ refl u) (u ↦ refl u)

def bridge_def_heap_c (G : Group) : Id (Σ Heap heap_usym) (bridge_heap_lift (blind_heap_c G)) (group_heap_lift G)
  ≔ refl (group_heap_lift G)

{` The ternary operation p q⁻¹ r, abelian heaps, the ternary structure. `}
def bridge_def_heap_t (H : BlindHeap) (p q r : blind_heap_usym H)
  : Id (blind_heap_usym H) (blind_heap_t H p q r) (heap_ternary (bridge_heap H) p q r)
  ≔ refl (blind_heap_t H p q r)

def bridge_def_abelian_heap (H : BlindHeap) : Id Type (BlindIsAbelianHeap H) (IsAbelianHeap (bridge_heap H))
  ≔ refl (BlindIsAbelianHeap H)

def bridge_def_ternary (S : SetTypes) : Id Type (BlindTernary S) (Ternary (S .fst)) ≔ refl (BlindTernary S)

def bridge_def_ternary_structure (H : BlindHeap)
  : Id TernarySets (blind_heap_ternary_structure H) (heap_ternary_structure (bridge_heap H))
  ≔ refl (blind_heap_ternary_structure H)

{` The blind heap laws are ours with the factors reordered. `}
def bridge_heap_laws_to_blind (S : SetTypes) (t : BlindTernary S) (l : HeapLaws (S .fst) t) : BlindHeapLaws S t
  ≔ (l .fst, (l .snd .snd .snd, (l .snd .fst, l .snd .snd .fst)))

def bridge_heap_laws_of_blind (S : SetTypes) (t : BlindTernary S) (l : BlindHeapLaws S t) : HeapLaws (S .fst) t
  ≔ (l .fst, (l .snd .snd .fst, (l .snd .snd .snd, l .snd .fst)))

def bridge_def_heap_laws (S : SetTypes) (t : BlindTernary S) : Equiv (HeapLaws (S .fst) t) (BlindHeapLaws S t)
  ≔ quasi_inverse_equiv (HeapLaws (S .fst) t) (BlindHeapLaws S t) (bridge_heap_laws_to_blind S t)
      (bridge_heap_laws_of_blind S t) (l ↦ refl l) (l ↦ refl l)

{` xca:group+torsor-heap (absgroup.tex 1356): l and r from heap_left_equiv
   and heap_right_equiv, c from heap_double_equiv, transported along
   bridge_def_heap (the composite maps are the blind ones judgmentally). `}
def bridge_heap_l_equiv : Equiv BlindHeap GroupWithBGPoint
  ≔ compose_equiv BlindHeap Heap GroupWithBGPoint bridge_def_heap heap_left_equiv

def bridge_heap_r_equiv : Equiv BlindHeap GroupWithBGPoint
  ≔ compose_equiv BlindHeap Heap GroupWithBGPoint bridge_def_heap heap_right_equiv

def bridge_heap_c_equiv : Equiv Group (Σ BlindHeap blind_heap_usym)
  ≔ compose_equiv Group (Σ Heap heap_usym) (Σ BlindHeap blind_heap_usym) heap_double_equiv
      (canonical_inverse_equiv (Σ BlindHeap blind_heap_usym) (Σ Heap heap_usym) bridge_def_heap_lift)

def bridge_xca_group_torsor_heap : blind_xca_group_torsor_heap
  ≔ let B ≔ Σ Group (G ↦ BG G .carrier) in
    let C ≔ Σ BlindHeap blind_heap_usym in
    (bridge_book_equiv_homotopic BlindHeap B (bridge_book_equiv_of BlindHeap B bridge_heap_l_equiv) blind_heap_l
       (H ↦ refl (blind_heap_l H)),
     (bridge_book_equiv_homotopic BlindHeap B (bridge_book_equiv_of BlindHeap B bridge_heap_r_equiv) blind_heap_r
        (H ↦ refl (blind_heap_r H)),
      bridge_book_equiv_homotopic Group C (bridge_book_equiv_of Group C bridge_heap_c_equiv) blind_heap_c
        (G ↦ refl (blind_heap_c G))))

{` Converse: our three equivalences, from the blind ones. `}
def bridge_xca_group_torsor_heap_converse (b : blind_xca_group_torsor_heap)
  : Product (Equiv Heap GroupWithBGPoint) (Product (Equiv Heap GroupWithBGPoint) (Equiv Group (Σ Heap heap_usym)))
  ≔ let B ≔ Σ Group (G ↦ BG G .carrier) in
    let C ≔ Σ BlindHeap blind_heap_usym in
    let hb ≔ canonical_inverse_equiv BlindHeap Heap bridge_def_heap in
    (compose_equiv Heap BlindHeap B hb (native_equivalence BlindHeap B (blind_heap_l, b .fst)),
     (compose_equiv Heap BlindHeap B hb (native_equivalence BlindHeap B (blind_heap_r, b .snd .fst)),
      compose_equiv Group C (Σ Heap heap_usym) (native_equivalence Group C (blind_heap_c, b .snd .snd))
        bridge_def_heap_lift))

{` The exercise at absgroup.tex 1384. The blind shears of USym H are the
   functions s with a mere (p, q) such that s = (r ↦ p q⁻¹ r). `}
def bridge_hshear_fiber (H : BlindHeap) (s : blind_heap_usym H → blind_heap_usym H) : Type
  ≔ Σ (blind_heap_usym H) (p ↦ Σ (blind_heap_usym H) (q ↦
      Id (blind_heap_usym H → blind_heap_usym H) s (r ↦ blind_heap_t H p q r)))

def bridge_hshear_witness (H : BlindHeap) (s : blind_heap_usym H → blind_heap_usym H) : Type
  ≔ Mere (bridge_hshear_fiber H s)

def bridge_hshear_path (H : BlindHeap) (s u : BlindHeapShear H)
  (h : (r : blind_heap_usym H) → Id (blind_heap_usym H) (s .fst r) (u .fst r))
  : Id (BlindHeapShear H) s u
  ≔ let S ≔ blind_heap_usym H in
    subtype_equal (S → S) (bridge_hshear_witness H) (f ↦ mere_isprop (bridge_hshear_fiber H f)) s u
      (funext S (_ ↦ S) (s .fst) (u .fst) h)

def bridge_hshear_set (H : BlindHeap) : isSet (BlindHeapShear H)
  ≔ let S ≔ blind_heap_usym H in
    sigma_set (S → S) (bridge_hshear_witness H) (heap_translation_fun_set (bridge_heap H))
      (f ↦ prop_is_set (bridge_hshear_witness H f) (mere_isprop (bridge_hshear_fiber H f)))

{` Our translations: the image group in USym H ≃ USym H. `}
def bridge_hshear_image (H : BlindHeap) : Type
  ≔ SymmetryImage (heap_usym (bridge_heap H)) (heap_end_symmetry_data (bridge_heap H))

{` From our image to the blind shears: forget the equivalence proof. `}
def bridge_hshear_of_image (H : BlindHeap) (u : bridge_hshear_image H) : BlindHeapShear H
  ≔ let K ≔ bridge_heap H in
    let S ≔ heap_usym K in
    let D ≔ heap_end_symmetry_data K in
    (u .fst .map,
     mere_rec (BookFiber (Product S S) (Equiv S S) (symmetry_image_map S D) (u .fst))
       (bridge_hshear_witness H (u .fst .map)) (mere_isprop (bridge_hshear_fiber H (u .fst .map)))
       (w ↦ mere (bridge_hshear_fiber H (u .fst .map))
         (w .fst .fst, (w .fst .snd, refl ((d ↦ d .map) : Equiv S S → (S → S)) (w .snd))))
       (u .snd))

{` A blind shear is an equivalence (each r ↦ p q⁻¹ r is one). `}
def bridge_hshear_is_equiv (H : BlindHeap) (s : BlindHeapShear H)
  : isEquiv (blind_heap_usym H) (blind_heap_usym H) (s .fst)
  ≔ let K ≔ bridge_heap H in
    let S ≔ heap_usym K in
    mere_rec (bridge_hshear_fiber H (s .fst)) (isEquiv S S (s .fst)) (isequiv_isprop S S (s .fst))
      (w ↦ transport (S → S) (isEquiv S S) (heap_translation K (w .fst) (w .snd .fst)) (s .fst)
        (inverse (S → S) (s .fst) (heap_translation K (w .fst) (w .snd .fst)) (w .snd .snd))
        (heap_translation_equiv K (w .fst) (w .snd .fst) .equiv))
      (s .snd)

def bridge_hshear_equiv (H : BlindHeap) (s : BlindHeapShear H) : Equiv (blind_heap_usym H) (blind_heap_usym H)
  ≔ (s .fst, bridge_hshear_is_equiv H s)

def bridge_image_of_hshear (H : BlindHeap) (s : BlindHeapShear H) : bridge_hshear_image H
  ≔ let K ≔ bridge_heap H in
    let S ≔ heap_usym K in
    let D ≔ heap_end_symmetry_data K in
    let e ≔ bridge_hshear_equiv H s in
    (e,
     mere_rec (bridge_hshear_fiber H (s .fst)) (SymmetryImageWitness S D e) (symmetry_image_witness_prop S D e)
       (w ↦ mere (BookFiber (Product S S) (Equiv S S) (symmetry_image_map S D) e)
         ((w .fst, w .snd .fst),
          equiv_homotopy S S e (symmetry_image_map S D (w .fst, w .snd .fst)) (r ↦ w .snd .snd (refl r))))
       (s .snd))

def bridge_hshear_image_equiv (H : BlindHeap) : Equiv (bridge_hshear_image H) (BlindHeapShear H)
  ≔ let K ≔ bridge_heap H in
    let S ≔ heap_usym K in
    let D ≔ heap_end_symmetry_data K in
    quasi_inverse_equiv (bridge_hshear_image H) (BlindHeapShear H) (bridge_hshear_of_image H) (bridge_image_of_hshear H)
      (u ↦ symmetry_image_path S D (bridge_image_of_hshear H (bridge_hshear_of_image H u)) u
        (r ↦ refl (u .fst .map r)))
      (s ↦ bridge_hshear_path H (bridge_hshear_of_image H (bridge_image_of_hshear H s)) s (r ↦ refl (s .fst r)))

def bridge_def_heap_shear (H : BlindHeap) : Equiv (BlindHeapShear H) (heap_translation_group (bridge_heap H) .carrier)
  ≔ canonical_inverse_equiv (bridge_hshear_image H) (BlindHeapShear H) (bridge_hshear_image_equiv H)

{` The group operations on the blind shears, transported from ours: on
   underlying functions they are id, composition and the inverse map. `}
def bridge_hshear_unit (H : BlindHeap) : BlindHeapShear H
  ≔ bridge_hshear_of_image H (symmetry_image_unit (heap_usym (bridge_heap H)) (heap_end_symmetry_data (bridge_heap H)))

def bridge_hshear_mul (H : BlindHeap) (s u : BlindHeapShear H) : BlindHeapShear H
  ≔ bridge_hshear_of_image H
      (symmetry_image_mul (heap_usym (bridge_heap H)) (heap_end_symmetry_data (bridge_heap H))
        (bridge_image_of_hshear H s) (bridge_image_of_hshear H u))

def bridge_hshear_inv (H : BlindHeap) (s : BlindHeapShear H) : BlindHeapShear H
  ≔ bridge_hshear_of_image H
      (symmetry_image_inv (heap_usym (bridge_heap H)) (heap_end_symmetry_data (bridge_heap H))
        (bridge_image_of_hshear H s))

def bridge_hshear_unit_map (H : BlindHeap)
  : Id (blind_heap_usym H → blind_heap_usym H) (bridge_hshear_unit H .fst) (r ↦ r)
  ≔ refl ((r ↦ r) : blind_heap_usym H → blind_heap_usym H)

def bridge_hshear_mul_map (H : BlindHeap) (s u : BlindHeapShear H)
  : Id (blind_heap_usym H → blind_heap_usym H) (bridge_hshear_mul H s u .fst) (r ↦ s .fst (u .fst r))
  ≔ refl ((r ↦ s .fst (u .fst r)) : blind_heap_usym H → blind_heap_usym H)

def bridge_hshear_laws (H : BlindHeap)
  : AbstractGroupLaws (BlindHeapShear H) (bridge_hshear_unit H) (bridge_hshear_mul H) (bridge_hshear_inv H)
  ≔ let m ≔ bridge_hshear_mul H in
    let e ≔ bridge_hshear_unit H in
    (carrier_set ≔ bridge_hshear_set H,
     unit_right ≔ s ↦ bridge_hshear_path H (m s e) s (r ↦ refl (s .fst r)),
     unit_left ≔ s ↦ bridge_hshear_path H (m e s) s (r ↦ refl (s .fst r)),
     assoc ≔ s u v ↦ bridge_hshear_path H (m s (m u v)) (m (m s u) v) (r ↦ refl (s .fst (u .fst (v .fst r)))),
     inv_right ≔ s ↦ bridge_hshear_path H (m s (bridge_hshear_inv H s)) e
       (r ↦ equiv_counit (blind_heap_usym H) (blind_heap_usym H) (bridge_hshear_equiv H s) r))

def bridge_hshear_group (H : BlindHeap) : AbstractGroup
  ≔ (BlindHeapShear H, bridge_hshear_unit H, bridge_hshear_mul H, bridge_hshear_inv H, bridge_hshear_laws H)

{` Our translation group is isomorphic to the blind shear group. `}
def bridge_hshear_iso (H : BlindHeap) : AbstractIso (heap_translation_group (bridge_heap H)) (bridge_hshear_group H)
  ≔ (bridge_hshear_image_equiv H,
     u v ↦ bridge_hshear_path H
       (bridge_hshear_of_image H (heap_translation_group (bridge_heap H) .mul u v))
       (bridge_hshear_mul H (bridge_hshear_of_image H u) (bridge_hshear_of_image H v))
       (r ↦ refl (u .fst .map (v .fst .map r))))

{` concr of the blind shear group is the end group: bridge_concr_path,
   then the iso above, then heap_translation_concrete_end_path. `}
def bridge_hshear_concr_path (H : BlindHeap)
  : Id Group (blind_concr (bridge_ag7_inv (bridge_hshear_group H))) (blind_heap_end_group H)
  ≔ let K ≔ bridge_heap H in
    let T ≔ bridge_hshear_group H in
    let Tr ≔ heap_translation_group K in
    concat Group (blind_concr (bridge_ag7_inv T)) (concr T) (heap_end_group K)
      (bridge_concr_path (bridge_ag7_inv T))
      (concat Group (concr T) (concr Tr) (heap_end_group K)
        (refl concr (inverse AbstractGroup Tr T (abstract_group_path_from_iso Tr T (bridge_hshear_iso H))))
        (inverse Group (heap_end_group K) (concr Tr) (heap_translation_concrete_end_path K)))

def bridge_xca_heap_to_group : blind_xca_heap_to_group
  ≔ H ↦ (bridge_hshear_unit H, (bridge_hshear_mul H, (bridge_hshear_inv H,
      (bridge_hshear_unit_map H, (bridge_hshear_mul_map H,
        (group_laws_from_record (BlindHeapShear H) (bridge_hshear_unit H) (bridge_hshear_mul H) (bridge_hshear_inv H)
           (bridge_hshear_laws H),
         bridge_hshear_concr_path H))))))

{` The exercise at absgroup.tex 1391: heap_endpoints_merely_iso and, for
   abelian heaps, heap_canonical_iso. `}
def bridge_xca_heap_endpoints : blind_xca_heap_endpoints
  ≔ (H ↦ heap_endpoints_merely_iso (bridge_heap H), H hab ↦ heap_canonical_iso (bridge_heap H) hab)

{` Converse: our statements from the blind ones. `}
def bridge_xca_heap_endpoints_converse (b : blind_xca_heap_endpoints)
  : Product ((H : Heap) → Mere (GroupIso (heap_start_group H) (heap_end_group H)))
      ((H : Heap) → IsAbelianHeap H → GroupIso (heap_start_group H) (heap_end_group H))
  ≔ (H ↦ b .fst (bridge_heap_inv H), H hab ↦ b .snd (bridge_heap_inv H) hab)

{` xca:heap-variety (absgroup.tex 1408). `}
def bridge_set_of_equiv (A B : Type) (e : Equiv A B) (hB : isSet B) : isSet A
  ≔ hlevel_two_to_set A
      (hlevel_equiv (suc. (suc. zero.)) B A (canonical_inverse_equiv A B e) (set_to_hlevel_two B hB))

def bridge_usym_fiber_equiv (S : SetTypes)
  : Equiv (Σ BlindHeap (H ↦ Id SetTypes S (blind_heap_usym_set H))) (BookFiber Heap SetTypes heap_usym_settype S)
  ≔ quasi_inverse_equiv (Σ BlindHeap (H ↦ Id SetTypes S (blind_heap_usym_set H)))
      (BookFiber Heap SetTypes heap_usym_settype S)
      (u ↦ (bridge_heap (u .fst), u .snd)) (u ↦ (bridge_heap_inv (u .fst), u .snd)) (u ↦ refl u) (u ↦ refl u)

def bridge_ternary_fiber_equiv (S : SetTypes) (t : BlindTernary S)
  : Equiv (BookFiber BlindHeap (Σ SetTypes BlindTernary) blind_heap_ternary_structure (S, t))
      (BookFiber Heap TernarySets heap_ternary_structure (S, t))
  ≔ quasi_inverse_equiv (BookFiber BlindHeap (Σ SetTypes BlindTernary) blind_heap_ternary_structure (S, t))
      (BookFiber Heap TernarySets heap_ternary_structure (S, t))
      (u ↦ (bridge_heap (u .fst), u .snd)) (u ↦ (bridge_heap_inv (u .fst), u .snd)) (u ↦ refl u) (u ↦ refl u)

def bridge_xca_heap_variety : blind_xca_heap_variety
  ≔ (S ↦ bridge_set_of_equiv (Σ BlindHeap (H ↦ Id SetTypes S (blind_heap_usym_set H)))
        (BookFiber Heap SetTypes heap_usym_settype S) (bridge_usym_fiber_equiv S) (heap_usym_fiber_set S),
     S t ↦ heap_equiv_prop (BookFiber BlindHeap (Σ SetTypes BlindTernary) blind_heap_ternary_structure (S, t))
        (BookFiber Heap TernarySets heap_ternary_structure (S, t)) (bridge_ternary_fiber_equiv S t)
        (heap_ternary_fiber_prop (S, t)))

def bridge_xca_heap_variety_description : blind_xca_heap_variety_description
  ≔ S t ↦
    let F ≔ BookFiber BlindHeap (Σ SetTypes BlindTernary) blind_heap_ternary_structure (S, t) in
    let F' ≔ BookFiber Heap TernarySets heap_ternary_structure (S, t) in
    bridge_book_equiv_of F (BlindHeapLaws S t)
      (compose_equiv F (HeapLaws (S .fst) t) (BlindHeapLaws S t)
        (compose_equiv F F' (HeapLaws (S .fst) t) (bridge_ternary_fiber_equiv S t) (heap_ternary_fiber_equiv (S, t)))
        (bridge_def_heap_laws S t))

{` Converse: our description from the blind one. `}
def bridge_xca_heap_variety_description_converse (b : blind_xca_heap_variety_description) (S : SetTypes)
  (t : Ternary (S .fst))
  : Equiv (BookFiber Heap TernarySets heap_ternary_structure (S, t)) (HeapLaws (S .fst) t)
  ≔ let F ≔ BookFiber BlindHeap (Σ SetTypes BlindTernary) blind_heap_ternary_structure (S, t) in
    let F' ≔ BookFiber Heap TernarySets heap_ternary_structure (S, t) in
    compose_equiv F' F (HeapLaws (S .fst) t) (canonical_inverse_equiv F F' (bridge_ternary_fiber_equiv S t))
      (compose_equiv F (BlindHeapLaws S t) (HeapLaws (S .fst) t) (native_equivalence F (BlindHeapLaws S t) (b S t))
        (canonical_inverse_equiv (HeapLaws (S .fst) t) (BlindHeapLaws S t) (bridge_def_heap_laws S t)))
