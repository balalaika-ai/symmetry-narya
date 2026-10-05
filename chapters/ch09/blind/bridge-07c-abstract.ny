export "07-intersections"
export "../../../src/916-conjugation-abstract"
export "../../../src/973-abstract-subgroup-intersections"

{` Bridges for the xca at subgroups.tex:1801 (blind file 07-intersections). An intersection of abstract
   monos into abstr(G), transported from chapter 8's intersection of monomorphisms (group_mono_intersection) along
   our equivalence Mono(G) ≃ abstract monos (concrete_abstract_monos_equiv, module 916); its members are the common
   members (intersection_picked_out_iff, module 973). The transport is done for an abstract equivalence first, so
   that the (expensive) inverse of the concrete equivalence is never unfolded. `}

def bridge9w_tr_inter (M A : Type) (e : Equiv M A) (inter : M → M → M) (x y : A) : A
  ≔ e .map (inter (equiv_inverse_map M A e x) (equiv_inverse_map M A e y))

def bridge9w_tr_inter_agrees (M A : Type) (e : Equiv M A) (inter : M → M → M) (m m' : M)
  : Id A (bridge9w_tr_inter M A e inter (e .map m) (e .map m')) (e .map (inter m m'))
  ≔ let ei ≔ equiv_inverse_map M A e in
    let c : M → M → A ≔ a b ↦ e .map (inter a b) in
    concat A (c (ei (e .map m)) (ei (e .map m'))) (c m (ei (e .map m'))) (c m m')
      (refl ((a ↦ c a (ei (e .map m'))) : M → A) (equiv_retraction M A e m))
      (refl (c m) (equiv_retraction M A e m'))

def bridge9w_tr_inter_members (M A : Type) (e : Equiv M A) (inter : M → M → M) (Mem : A → Type) (PO : M → Type)
  (hPO : (m : M) → BlindIff (PO m) (Mem (e .map m)))
  (hint : (m m' : M) → BlindIff (PO (inter m m')) (Product (PO m) (PO m'))) (x y : A)
  : BlindIff (Mem (bridge9w_tr_inter M A e inter x y)) (Product (Mem x) (Mem y))
  ≔ let ei ≔ equiv_inverse_map M A e in
    let mx ≔ ei x in let my ≔ ei y in
    let cx : Id A (e .map mx) x ≔ equiv_counit M A e x in
    let cy : Id A (e .map my) y ≔ equiv_counit M A e y in
    let tr : (z z' : A) → Id A z z' → Mem z → Mem z' ≔ z z' p r ↦ transport A Mem z z' p r in
    (r ↦ let b ≔ hint mx my .fst (hPO (inter mx my) .snd r) in
          (tr (e .map mx) x cx (hPO mx .fst (b .fst)), tr (e .map my) y cy (hPO my .fst (b .snd))),
     b ↦ hPO (inter mx my) .fst
          (hint mx my .snd
            (hPO mx .snd (tr x (e .map mx) (inverse A (e .map mx) x cx) (b .fst)),
             hPO my .snd (tr y (e .map my) (inverse A (e .map my) y cy) (b .snd)))))

def bridge_abstract_intersection : blind_abstract_intersection
  ≔ (G ↦ bridge9w_tr_inter (GroupMonos G) (BlindAbsMonos G) (concrete_abstract_monos_equiv G) (group_mono_intersection G),
     (G m m' ↦ bridge9w_tr_inter_agrees (GroupMonos G) (BlindAbsMonos G) (concrete_abstract_monos_equiv G)
        (group_mono_intersection G) m m',
      G x y g ↦ bridge9w_tr_inter_members (GroupMonos G) (BlindAbsMonos G) (concrete_abstract_monos_equiv G)
        (group_mono_intersection G) (z ↦ BlindAbsMember G z g) (m ↦ SymmetryPickedOut G m g)
        (m ↦ ((r ↦ r), (r ↦ r))) (m m' ↦ intersection_picked_out_iff G m m' g) x y))
