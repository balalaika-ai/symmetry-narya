export "958-center-as-abelian-group"
export "957-outer-automorphisms-simple"

{` Chapter 9 (symmetry.tex 461-488): the running text after def:center:
   the evaluation homomorphism e : Z(G) → G and its fiber, the fiber of
   i : BInn(G) → BAut(G), and BOut(G) ≔ ‖Σ_{X:Bunch} ‖bunch(G) = X‖‖₁ with
   its loop type. For 1-groups. BInn(G) is Img(inn) of module 956 (the book
   here writes Σ_{H:Group} ‖bunch(G) = bunch(H)‖₀, which is the same type up
   to inner_aut_classifying_equiv_group and path inversion). `}

{` "There is a canonical homomorphism from Z(G) to G given by the pointed
   map from BZ(G) to BG that evaluates at sh_G." `}
def center_evaluation_hom (G : Group) : GroupHom (center_fun_group G) G
  ≔ mkhom (center_fun_group G) G ((u ↦ u .fst (shape G)), refl (shape G))

{` fiber_e(sh_G) ≡ Σ_{f : BG → BG} ‖f ~ id‖ × (sh_G = f sh_G)
   ≃ Σ_{f : BG →* BG} ‖f ~ id‖ (book orientation of the pointing). `}
def center_evaluation_fiber_equiv (G : Group)
  : Equiv (HomFiber (center_fun_group G) G (center_evaluation_hom G) (shape G))
      (Σ (BookPointedMap (BG G) (BG G)) (f ↦ Mere (Homotopy (BG G .carrier) (_ ↦ BG G .carrier) (f .fst) (identity (BG G .carrier)))))
  ≔ let X ≔ BG G .carrier in
    quasi_inverse_equiv (HomFiber (center_fun_group G) G (center_evaluation_hom G) (shape G))
      (Σ (BookPointedMap (BG G) (BG G)) (f ↦ Mere (Homotopy X (_ ↦ X) (f .fst) (identity X))))
      (w ↦ ((w .fst .fst, w .snd), w .fst .snd)) (v ↦ ((v .fst .fst, v .snd), v .fst .snd))
      (w ↦ refl w) (v ↦ refl v)

{` The fiber of i : BInn(G) → BAut(G) (the inclusion of the image of inn,
   forgetting the component) at sh is ‖bunch(G) = bunch(G)‖₀, here
   ‖BG÷ = BG÷‖₀. `}
def inner_inclusion_fiber_equiv (G : Group)
  : Equiv (HomFiber (inner_aut_group G) (group_aut G) (image_inclusion G (group_aut G) (inn G)) (shape (group_aut G)))
      (SetTrunc (Id Type (BG G .carrier) (BG G .carrier)))
  ≔ let A ≔ group_aut G in
    compose_equiv (HomFiber (inner_aut_group G) A (image_inclusion G A (inn G)) (shape A)) (outer_gset G (shape A) .fst)
      (SetTrunc (Id Type (BG G .carrier) (BG G .carrier)))
      (native_equivalence (HomFiber (inner_aut_group G) A (image_inclusion G A (inn G)) (shape A)) (outer_gset G (shape A) .fst)
        (book_projection_fiber_equiv (BG A .carrier) (z ↦ outer_gset G z .fst) (shape A)))
      (outer_gset_equiv G (shape A))

{` BOut(G) ≔ ‖Σ_{X:Bunch} ‖bunch(G) = X‖‖₁ (the 1-truncation, module 202's
   Trunc 2, of the component of bunch(G) in Bunch, a 2-type). `}
def OutBunchClassifying (G : Group) : Type ≔ Trunc (suc. (suc. zero.)) (NativeComponent Bunch (bunch G))

def out_bunch_point (G : Group) : OutBunchClassifying G
  ≔ trunc_unit (suc. (suc. zero.)) (NativeComponent Bunch (bunch G)) (component_point Bunch (bunch G))

def out_bunch_groupoid (G : Group) : isGroupoid (OutBunchClassifying G)
  ≔ hlevel_to_groupoid (OutBunchClassifying G) (trunc_level (suc. (suc. zero.)) (NativeComponent Bunch (bunch G)))

def out_bunch_connected (G : Group) : Connected (OutBunchClassifying G)
  ≔ let C ≔ NativeComponent Bunch (bunch G) in
    let k : Nat ≔ suc. (suc. zero.) in
    connected_from_point (OutBunchClassifying G) (out_bunch_point G)
      (trunc_induction_book k C (x ↦ Mere (Id (OutBunchClassifying G) (out_bunch_point G) x))
        (x ↦ prop_hlevel (suc. (suc. zero.)) (Mere (Id (OutBunchClassifying G) (out_bunch_point G) x))
          (mere_isprop (Id (OutBunchClassifying G) (out_bunch_point G) x)))
        (c ↦ mere_rec (Id C (component_point Bunch (bunch G)) c) (Mere (Id (OutBunchClassifying G) (out_bunch_point G) (trunc_unit k C c)))
          (mere_isprop (Id (OutBunchClassifying G) (out_bunch_point G) (trunc_unit k C c)))
          (q ↦ mere (Id (OutBunchClassifying G) (out_bunch_point G) (trunc_unit k C c))
            (refl (trunc_unit k C) q))
          (native_component_connected Bunch (bunch G) .snd (component_point Bunch (bunch G)) c)))

def out_bunch_group (G : Group) : Group
  ≔ mkgroup (OutBunchClassifying G, out_bunch_point G, out_bunch_connected G, out_bunch_groupoid G)

{` "This is evidently the type of loops in BOut(G)": Ω BOut(G) ≃
   ‖bunch(G) = bunch(G)‖₀ ≃ ‖BG÷ = BG÷‖₀ ≃ fiber of i. `}
def out_bunch_loops_equiv (G : Group)
  : Equiv (USym (out_bunch_group G)) (SetTrunc (Id Bunch (bunch G) (bunch G)))
  ≔ let C ≔ NativeComponent Bunch (bunch G) in let c0 ≔ component_point Bunch (bunch G) in
    compose_equiv (USym (out_bunch_group G)) (Trunc (suc. zero.) (Id C c0 c0)) (SetTrunc (Id Bunch (bunch G) (bunch G)))
      (canonical_inverse_equiv (Trunc (suc. zero.) (Id C c0 c0)) (USym (out_bunch_group G)) (trunc_path_equiv (suc. zero.) C c0 c0))
      (compose_equiv (Trunc (suc. zero.) (Id C c0 c0)) (SetTrunc (Id C c0 c0)) (SetTrunc (Id Bunch (bunch G) (bunch G)))
        (trunc_one_set_trunc_equiv (Id C c0 c0))
        (ch9w2_set_trunc_equiv (Id C c0 c0) (Id Bunch (bunch G) (bunch G)) (component_path_equiv Bunch (bunch G) c0 c0)))

def out_bunch_loops_fiber_equiv (G : Group)
  : Equiv (USym (out_bunch_group G))
      (HomFiber (inner_aut_group G) (group_aut G) (image_inclusion G (group_aut G) (inn G)) (shape (group_aut G)))
  ≔ let X ≔ BG G .carrier in
    compose_equiv (USym (out_bunch_group G)) (SetTrunc (Id Bunch (bunch G) (bunch G)))
      (HomFiber (inner_aut_group G) (group_aut G) (image_inclusion G (group_aut G) (inn G)) (shape (group_aut G)))
      (out_bunch_loops_equiv G)
      (compose_equiv (SetTrunc (Id Bunch (bunch G) (bunch G))) (SetTrunc (Id Type X X))
        (HomFiber (inner_aut_group G) (group_aut G) (image_inclusion G (group_aut G) (inn G)) (shape (group_aut G)))
        (ch9w2_set_trunc_equiv (Id Bunch (bunch G) (bunch G)) (Id Type X X) (bunch_path_equiv (bunch G) (bunch G)))
        (canonical_inverse_equiv (HomFiber (inner_aut_group G) (group_aut G) (image_inclusion G (group_aut G) (inn G)) (shape (group_aut G)))
          (SetTrunc (Id Type X X)) (inner_inclusion_fiber_equiv G)))
