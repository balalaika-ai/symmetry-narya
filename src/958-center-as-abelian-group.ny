export "903-normal-subgroups"
export "1204-double-delooping"
export "953-coker-of-composites-restriction"

{` Chapter 9 (symmetry.tex 411-460), sec:automorphisms: Bunch, def:center
   (Z(G) as an abelian group) and the litmus checks. The book allows higher
   groups in this section; here G is a (1-)group, BG÷ a groupoid.

   Conventions: X ≔ BG÷. Z(G) ≔ Π_{z:BG}(z = z); BZ(G) ≔ Σ_{f : BG → BG}
   ‖f ~ id‖, pointed at (id, |refl|); B²Z(G) ≔ Σ_{Y:Bunch} ‖bunch(G) = Y‖₀.
   Module 1202's group_center (Aut_{(BG÷ = BG÷)}(refl), the center of
   sec:abelian-groups) is identified with mkgroup(BZ(G)); the abelian
   structure comes from B²Z(G) = BB G of module 1204 (Eckmann-Hilton). `}

{` Bunch: the type of connected groupoids; bunch(G) ≔ BG÷. `}
def Bunch : Type ≔ Σ Type (Y ↦ Product (Connected Y) (isGroupoid Y))

def bunch (G : Group) : Bunch ≔ (BG G .carrier, (bg_connected G, bg_groupoid G))

def bunch_structure_prop (Y : Type) : isProp (Product (Connected Y) (isGroupoid Y))
  ≔ product_prop (Connected Y) (isGroupoid Y) (connected_prop Y) (isgroupoid_isprop Y)

{` "The type of groups is equivalent to Σ_{X:Bunch} X." `}
def group_bunch_equiv : Equiv Group (Σ Bunch (Y ↦ Y .fst))
  ≔ quasi_inverse_equiv Group (Σ Bunch (Y ↦ Y .fst))
      (G ↦ (bunch G, shape G))
      (u ↦ mkgroup (u .fst .fst, u .snd, u .fst .snd .fst, u .fst .snd .snd))
      (G ↦ refl G) (u ↦ refl u)

{` def:center. Z(G) ≔ Π_{z:BG} (z = z), the fixed points of the adjoint action. `}
def CenterFixedPoints (G : Group) : Type ≔ (z : BG G .carrier) → Id (BG G .carrier) z z

def center_fixed_points_adjoint (G : Group) : Id Type (CenterFixedPoints G) (InvariantMaps G (adjoint_gset G))
  ≔ refl (CenterFixedPoints G)

{` "equivalent to the automorphism group of the identity on bunch(G)":
   Z(G) ≃ (id = id) in BG÷ → BG÷ (function extensionality). `}
def center_identity_loops_equiv (G : Group)
  : Equiv (Id (BG G .carrier → BG G .carrier) (identity (BG G .carrier)) (identity (BG G .carrier))) (CenterFixedPoints G)
  ≔ canonical_inverse_equiv (CenterFixedPoints G) (Id (BG G .carrier → BG G .carrier) (identity (BG G .carrier)) (identity (BG G .carrier)))
      (funext_equiv (BG G .carrier) (_ ↦ BG G .carrier) (identity (BG G .carrier)) (identity (BG G .carrier)))

{` BZ(G) ≔ Σ_{f : BG → BG} ‖f ~ id‖. `}
def CenterClassifying (G : Group) : Type
  ≔ Σ (BG G .carrier → BG G .carrier) (f ↦ Mere (Homotopy (BG G .carrier) (_ ↦ BG G .carrier) f (identity (BG G .carrier))))

def center_classifying_point (G : Group) : CenterClassifying G
  ≔ (identity (BG G .carrier), mere (Homotopy (BG G .carrier) (_ ↦ BG G .carrier) (identity (BG G .carrier)) (identity (BG G .carrier)))
       (x ↦ refl x))

def center_classifying_prop (G : Group) (f : BG G .carrier → BG G .carrier)
  : isProp (Mere (Homotopy (BG G .carrier) (_ ↦ BG G .carrier) f (identity (BG G .carrier))))
  ≔ mere_isprop (Homotopy (BG G .carrier) (_ ↦ BG G .carrier) f (identity (BG G .carrier)))

def center_classifying_groupoid (G : Group) : isGroupoid (CenterClassifying G)
  ≔ let X ≔ BG G .carrier in
    let h ≔ hlevel_sigma (suc. (suc. (suc. zero.))) (X → X) (f ↦ Mere (Homotopy X (_ ↦ X) f (identity X)))
        (hlevel_function (suc. (suc. (suc. zero.))) X X (x y ↦ set_to_hlevel_two (Id X x y) (bg_groupoid G x y)))
        (f ↦ prop_hlevel (suc. (suc. zero.)) (Mere (Homotopy X (_ ↦ X) f (identity X))) (center_classifying_prop G f)) in
    x y ↦ hlevel_two_to_set (Id (CenterClassifying G) x y) (h x y)

def center_classifying_connected (G : Group) : Connected (CenterClassifying G)
  ≔ let X ≔ BG G .carrier in
    connected_from_point (CenterClassifying G) (center_classifying_point G)
      (u ↦ mere_rec (Homotopy X (_ ↦ X) (u .fst) (identity X)) (Mere (Id (CenterClassifying G) (center_classifying_point G) u))
        (mere_isprop (Id (CenterClassifying G) (center_classifying_point G) u))
        (h ↦ mere (Id (CenterClassifying G) (center_classifying_point G) u)
          (subtype_equal (X → X) (f ↦ Mere (Homotopy X (_ ↦ X) f (identity X))) (center_classifying_prop G)
            (center_classifying_point G) u
            (funext X (_ ↦ X) (identity X) (u .fst) (x ↦ inverse X (u .fst x) x (h x)))))
        (u .snd))

{` The center as a group, from BZ(G). `}
def center_fun_group (G : Group) : Group
  ≔ mkgroup (CenterClassifying G, center_classifying_point G, center_classifying_connected G, center_classifying_groupoid G)

{` "and hence [Z(G) is] the loop type of BZ(G)". `}
def center_fun_loops_equiv (G : Group) : Equiv (USym (center_fun_group G)) (CenterFixedPoints G)
  ≔ let X ≔ BG G .carrier in
    compose_equiv (USym (center_fun_group G)) (Id (X → X) (identity X) (identity X)) (CenterFixedPoints G)
      (subtype_path_equiv (X → X) (f ↦ Mere (Homotopy X (_ ↦ X) f (identity X))) (center_classifying_prop G)
        (center_classifying_point G) (center_classifying_point G))
      (center_identity_loops_equiv G)

{` Comparison with the center of sec:abelian-groups (module 1202):
   Aut_{(BG÷ = BG÷)}(refl) ≅ mkgroup(BZ(G)), induced by φ ↦ φ.trr, an
   embedding (BG÷ = BG÷) ↪ (BG÷ → BG÷) (univalence, and isEquiv is a
   proposition), followed by ‖id = f‖ ≃ ‖f ~ id‖. `}
def ch9w2_equiv_map_embedding (A B : Type) : IsEmbedding (Equiv A B) (A → B) (e ↦ e .map)
  ≔ b ↦
    let F ≔ BookFiber (Equiv A B) (A → B) (e ↦ e .map) b in
    let F' ≔ BookFiber (Σ (A → B) (isEquiv A B)) (A → B) (t ↦ t .fst) b in
    let eq ≔ preequivalence_fiber_equiv (Equiv A B) (Σ (A → B) (isEquiv A B)) (A → B) (equiv_sigma_equiv A B) (t ↦ t .fst) b in
    x y ↦ equivalence_injective F F' eq x y
      (subtype_projection_embedding (A → B) (isEquiv A B) (isequiv_isprop A B) b (eq .map x) (eq .map y))

def ch9w2_transport_map_embedding (A B : Type) : IsEmbedding (Id Type A B) (A → B) (φ ↦ φ .trr)
  ≔ b ↦
    let F ≔ BookFiber (Id Type A B) (A → B) (φ ↦ φ .trr) b in
    let F' ≔ BookFiber (Equiv A B) (A → B) (e ↦ e .map) b in
    let eq ≔ preequivalence_fiber_equiv (Id Type A B) (Equiv A B) (A → B) (transport_univalence_equiv A B) (e ↦ e .map) b in
    x y ↦ equivalence_injective F F' eq x y (ch9w2_equiv_map_embedding A B b (eq .map x) (eq .map y))

def center_trr_point (G : Group)
  : Id (BG G .carrier → BG G .carrier) (identity (BG G .carrier)) (refl (BG G .carrier) .trr)
  ≔ funext (BG G .carrier) (_ ↦ BG G .carrier) (identity (BG G .carrier)) (refl (BG G .carrier) .trr)
      (x ↦ refl (BG G .carrier) .liftr x)

def center_component_classifying_equiv (G : Group)
  : Equiv (NativeComponent (BG G .carrier → BG G .carrier) (identity (BG G .carrier))) (CenterClassifying G)
  ≔ let X ≔ BG G .carrier in
    family_equiv (X → X) (f ↦ Mere (Id (X → X) (identity X) f)) (f ↦ Mere (Homotopy X (_ ↦ X) f (identity X)))
      (f ↦ iff_equiv (Mere (Id (X → X) (identity X) f)) (Mere (Homotopy X (_ ↦ X) f (identity X)))
        (mere_isprop (Id (X → X) (identity X) f)) (center_classifying_prop G f)
        (mere_rec (Id (X → X) (identity X) f) (Mere (Homotopy X (_ ↦ X) f (identity X))) (center_classifying_prop G f)
          (q ↦ mere (Homotopy X (_ ↦ X) f (identity X)) (x ↦ inverse X x (f x) (happly X (_ ↦ X) (identity X) f q x))))
        (mere_rec (Homotopy X (_ ↦ X) f (identity X)) (Mere (Id (X → X) (identity X) f)) (mere_isprop (Id (X → X) (identity X) f))
          (h ↦ mere (Id (X → X) (identity X) f) (funext X (_ ↦ X) (identity X) f (x ↦ inverse X (f x) x (h x))))))

def center_comparison_map (G : Group) (u : BG (group_center G) .carrier) : CenterClassifying G
  ≔ center_component_classifying_equiv G .map
      (ch9w2_component_map (Id Type (BG G .carrier) (BG G .carrier)) (BG G .carrier → BG G .carrier) (φ ↦ φ .trr)
        (refl (BG G .carrier)) (identity (BG G .carrier)) (center_trr_point G) u)

def center_comparison_equiv (G : Group)
  : BookPointedEquiv (BG (group_center G)) (BG (center_fun_group G))
  ≔ let X ≔ BG G .carrier in
    let cm ≔ ch9w2_component_map (Id Type X X) (X → X) (φ ↦ φ .trr) (refl X) (identity X) (center_trr_point G) in
    let e1 : Equiv (BG (group_center G) .carrier) (NativeComponent (X → X) (identity X))
      ≔ native_equivalence (BG (group_center G) .carrier) (NativeComponent (X → X) (identity X))
          (cm, ch9w2_component_map_embedding_equiv (Id Type X X) (X → X) (φ ↦ φ .trr) (refl X) (identity X) (center_trr_point G)
            (ch9w2_transport_map_embedding X X)) in
    ((center_comparison_map G,
      subtype_equal (X → X) (f ↦ Mere (Homotopy X (_ ↦ X) f (identity X))) (center_classifying_prop G)
        (center_classifying_point G) (center_comparison_map G (shape (group_center G))) (center_trr_point G)),
     book_equivalence (BG (group_center G) .carrier) (CenterClassifying G)
       (compose_equiv (BG (group_center G) .carrier) (NativeComponent (X → X) (identity X)) (CenterClassifying G) e1
         (center_component_classifying_equiv G)) .equiv)

def center_comparison_path (G : Group) : Id Group (group_center G) (center_fun_group G)
  ≔ group_path_from_pointed_equiv (group_center G) (center_fun_group G) (center_comparison_equiv G)

{` "BZ(G) is itself the loop type of the pointed connected type
   B²Z(G) ≔ Σ_{Y:Bunch} ‖bunch(G) = Y‖₀". First B²Z(G) is BB G of module
   1204 (the sum over Type), as the bunch structure is a proposition
   implied by ‖BG÷ = Y‖₀. `}
def BTwoCenter (G : Group) : Type ≔ Σ Bunch (Y ↦ SetTrunc (Id Bunch (bunch G) Y))

def btwo_center_point (G : Group) : BTwoCenter G ≔ (bunch G, set_trunc (Id Bunch (bunch G) (bunch G)) (refl (bunch G)))

def bunch_path_equiv (Y Z : Bunch) : Equiv (Id Bunch Y Z) (Id Type (Y .fst) (Z .fst))
  ≔ subtype_path_equiv Type (W ↦ Product (Connected W) (isGroupoid W)) bunch_structure_prop Y Z

def bunch_structure_transport (G : Group) (Y : Type) (t : SetTrunc (Id Type (BG G .carrier) Y))
  : Product (Connected Y) (isGroupoid Y)
  ≔ set_trunc_rec (Id Type (BG G .carrier) Y) (Product (Connected Y) (isGroupoid Y))
      (prop_is_set (Product (Connected Y) (isGroupoid Y)) (bunch_structure_prop Y))
      (p ↦ transport Type (W ↦ Product (Connected W) (isGroupoid W)) (BG G .carrier) Y p (bunch G .snd)) t

def btwo_center_bb_equiv (G : Group) : Equiv (BTwoCenter G) (BB G .carrier)
  ≔ let X ≔ BG G .carrier in
    let S : Type → Type ≔ W ↦ Product (Connected W) (isGroupoid W) in
    let T : Type → Type ≔ W ↦ SetTrunc (Id Type X W) in
    compose_equiv (BTwoCenter G) (Σ Bunch (Y ↦ T (Y .fst))) (BB G .carrier)
      (family_equiv Bunch (Y ↦ SetTrunc (Id Bunch (bunch G) Y)) (Y ↦ T (Y .fst))
        (Y ↦ ch9w2_set_trunc_equiv (Id Bunch (bunch G) Y) (Id Type X (Y .fst)) (bunch_path_equiv (bunch G) Y)))
      (compose_equiv (Σ Bunch (Y ↦ T (Y .fst))) (Σ Type (W ↦ Σ (S W) (_ ↦ T W))) (BB G .carrier)
        (sigma_assoc Type S (W _ ↦ T W))
        (family_equiv Type (W ↦ Σ (S W) (_ ↦ T W)) T
          (W ↦ compose_equiv (Σ (S W) (_ ↦ T W)) (Σ (T W) (_ ↦ S W)) (T W)
            (quasi_inverse_equiv (Σ (S W) (_ ↦ T W)) (Σ (T W) (_ ↦ S W)) (u ↦ (u .snd, u .fst)) (u ↦ (u .snd, u .fst))
              (u ↦ refl u) (u ↦ refl u))
            (ch9w2_drop_contractible_prop (T W) (_ ↦ S W) (_ ↦ bunch_structure_prop W) (t ↦ bunch_structure_transport G W t)))))

def btwo_center_bb_point (G : Group)
  : Id (BB G .carrier) (btwo_center_bb_equiv G .map (btwo_center_point G)) (bb_point G)
  ≔ refl (bb_point G)

def btwo_center_connected (G : Group) : Connected (BTwoCenter G)
  ≔ connected_equiv (BB G .carrier) (BTwoCenter G)
      (canonical_inverse_equiv (BTwoCenter G) (BB G .carrier) (btwo_center_bb_equiv G))
      .map (univ_cover_connected Type (BG G .carrier))

def btwo_center_loops_equiv (G : Group)
  : Equiv (Id (BTwoCenter G) (btwo_center_point G) (btwo_center_point G)) (CenterClassifying G)
  ≔ let X ≔ BG G .carrier in
    compose_equiv (Id (BTwoCenter G) (btwo_center_point G) (btwo_center_point G)) (Loop (BB G)) (CenterClassifying G)
      (equivalence_on_paths (BTwoCenter G) (BB G .carrier) (btwo_center_bb_equiv G) (btwo_center_point G) (btwo_center_point G))
      (compose_equiv (Loop (BB G)) (BG (group_center G) .carrier) (CenterClassifying G)
        (univ_cover_loops_component_equiv Type X)
        (native_equivalence (BG (group_center G) .carrier) (CenterClassifying G)
          (center_comparison_equiv G .fst .fst, center_comparison_equiv G .snd)))

{` "and we use this to give Z(G) the structure of an abelian group": the
   group of loops of B²Z(G) = BB G (a simply connected 2-type) is abelian by
   Eckmann-Hilton (module 1204), and it is the center. `}
def center_bb_loops_path (G : Group) : Id Group (sc2_loop_group (bb_sc2 G)) (group_center G)
  ≔ let X ≔ BG G .carrier in
    group_path_from_pointed_equiv (sc2_loop_group (bb_sc2 G)) (group_center G)
      ((univ_cover_loops_component_equiv Type X .map,
        component_path (Id Type X X) (refl X) (component_point (Id Type X X) (refl X))
          (univ_cover_loops_component_equiv Type X .map (refl (bb_point G))) (refl (refl X))),
       book_equivalence (Loop (BB G)) (BG (group_center G) .carrier) (univ_cover_loops_component_equiv Type X) .equiv)

def center_group_abelian (G : Group) : IsAbelian (group_center G)
  ≔ abelian_transport (sc2_loop_group (bb_sc2 G)) (group_center G) (center_bb_loops_path G) (sc2_loop_group_abelian (bb_sc2 G))

def center_fun_abelian (G : Group) : IsAbelian (center_fun_group G)
  ≔ abelian_transport (group_center G) (center_fun_group G) (center_comparison_path G) (center_group_abelian G)

def center_abelian_group (G : Group) : AbelianGroup ≔ (center_fun_group G, center_fun_abelian G)

{` Litmus 1: the center of an abelian group is everything. `}
def center_of_abelian_path (G : Group) (h : IsAbelian G) : Id Group (center_fun_group G) G
  ≔ concat Group (center_fun_group G) (group_center G) G
      (inverse Group (group_center G) (center_fun_group G) (center_comparison_path G)) (abelian_center_path G h)

def center_of_abelian_usym_equiv (G : Group) (h : IsAbelian G) : Equiv (CenterFixedPoints G) (USym G)
  ≔ compose_equiv (CenterFixedPoints G) (USym (center_fun_group G)) (USym G)
      (canonical_inverse_equiv (USym (center_fun_group G)) (CenterFixedPoints G) (center_fun_loops_equiv G))
      (transport_equiv (USym (center_fun_group G)) (USym G) (refl USym (center_of_abelian_path G h)))

{` Litmus 2: the value at sh_G of an element of Z(G) is central (naturality
   in the family z ↦ (z = z)); hence the transposition τ of Σ₃ is not the
   value of any element of Z(Σ₃). `}
def center_fixed_point_central (G : Group) (f : CenterFixedPoints G) (h : USym G)
  : Id (USym G) (concat (BG G .carrier) (shape G) (shape G) (shape G) h (f (shape G)))
      (concat (BG G .carrier) (shape G) (shape G) (shape G) (f (shape G)) h)
  ≔ let A ≔ BG G .carrier in let a ≔ shape G in
    loop_conjugate_fixed_commutes_right A a (f a) h
      (concat (Id A a a) (concat A a a a (inverse A a a h) (concat A a a a (f a) h))
        (transport A (z ↦ Id A z z) a a h (f a)) (f a)
        (inverse (Id A a a) (transport A (z ↦ Id A z z) a a h (f a)) (loop_conjugate A a a h (f a))
          (loop_transport_conjugate A a a h (f a)))
        (pathover_transport_equiv A (z ↦ Id A z z) a a h (f a) (f a) .map (refl f h)))

def sigma3_tau_not_in_center (f : CenterFixedPoints (symmetric_group three))
  (e : Id (USym (symmetric_group three)) (f (shape (symmetric_group three))) sigma3_tau) : Empty
  ≔ let S ≔ symmetric_group three in let A ≔ BG S .carrier in let a ≔ shape S in
    sigma3_tau_sigma_noncommuting
      (transport (USym S) (g ↦ Id (USym S) (concat A a a a g sigma3_sigma) (concat A a a a sigma3_sigma g))
        (f a) sigma3_tau e
        (inverse (USym S) (concat A a a a sigma3_sigma (f a)) (concat A a a a (f a) sigma3_sigma)
          (center_fixed_point_central S f sigma3_sigma)))
