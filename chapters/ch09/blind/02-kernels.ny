{` Blind statements for chapter 9 (subgroups.tex), section "Images, kernels and cokernels": kernels and cokernels. `}
export "01-epi-mono"

{` The preimage (Bf)^{-1}(w) ≔ Σ_{z:BG} (w = Bf(z)). `}
def BlindHomFiber (G G' : Group) (f : GroupHom G G') (w : BG G' .carrier) : Type
  ≔ BookFiber (BG G .carrier) (BG G' .carrier) (hom_function G G' f) w

{` The preimage over sh_{G'} is a groupoid (it is literally the action type of z ↦ (sh_{G'} = Bf(z))). `}
def blind_hom_fiber_groupoid (G G' : Group) (f : GroupHom G G') : isGroupoid (BlindHomFiber G G' f (shape G'))
  ≔ action_type_groupoid G (gset_restrict G G' f (principal_gset G'))

{` def:kernel. Ker(f) ≔ Aut_{(Bf)^{-1}(sh_{G'})}(sh_G, Bf_pt), the component of the preimage at (sh_G, Bf_pt). `}
def BlindKer (G G' : Group) (f : GroupHom G G') : Group
  ≔ automorphism_group (BlindHomFiber G G' f (shape G')) (blind_hom_fiber_groupoid G G' f) (shape G, hom_point G G' f)

{` def:kernel. ker_f : Hom(Ker(f), G) given by the first projection, pointed by reflexivity. `}
def blind_kermap (G G' : Group) (f : GroupHom G G') : GroupHom (BlindKer G G' f) G
  ≔ mkhom (BlindKer G G' f) G ((u ↦ u .fst .fst), refl (shape G))

{` The proof "!" that ker_f is a monomorphism (in the sense of def:typeofmono): the projection is a covering.
   BlindKer is literally the stabilizer group of the G-set z ↦ (sh_{G'} = Bf(z)) at Bf_pt. `}
def blind_kermap_mono (G G' : Group) (f : GroupHom G G') : IsGroupMono (BlindKer G G' f) G (blind_kermap G G' f)
  ≔ stabilizer_inclusion_mono G (gset_restrict G G' f (principal_gset G')) (hom_point G G' f)

{` def:kernel. ker : Hom(G,G') → Mono(G), ker(f) ≔ (Ker(f), ker_f, !). `}
def blind_ker (G G' : Group) (f : GroupHom G G') : GroupMonos G
  ≔ (BlindKer G G' f, (blind_kermap G G' f, blind_kermap_mono G G' f))

{` def:cokernel. coker(f) : BG' → Set, w ↦ ‖(Bf)^{-1}(w)‖₀. `}
def blind_coker (G G' : Group) (f : GroupHom G G') : GSet G'
  ≔ w ↦ (SetTrunc (BlindHomFiber G G' f w), set_trunc_set (BlindHomFiber G G' f w))

{` The point |(sh_G, Bf_pt)|₀ of coker(f)(sh_{G'}). `}
def blind_coker_point (G G' : Group) (f : GroupHom G G') : gset_underlying G' (blind_coker G G' f)
  ≔ set_trunc (BlindHomFiber G G' f (shape G')) (shape G, hom_point G G' f)

{` lem:isTrans(coker). The cokernel is a transitive G'-set. `}
def blind_coker_transitive : Type
  ≔ (G G' : Group) (f : GroupHom G G') → IsTransitive G' (blind_coker G G' f)

{` rem:imageandcokernel. Given transitivity, (coker(f), |(sh_G, Bf_pt)|₀, !) : Sub(G'). `}
def blind_coker_subgroup (G G' : Group) (f : GroupHom G G') (t : IsTransitive G' (blind_coker G G' f)) : Subgroups G'
  ≔ (blind_coker G G' f, blind_coker_point G G' f, t)

{` rem:imageandcokernel, second proof: BG ≃ Σ_{w:BG'} (Bf)^{-1}(w), which maps surjectively onto
   Σ_{w:BG'} ‖(Bf)^{-1}(w)‖₀; the latter type is connected. `}
def blind_coker_total_equiv : Type
  ≔ (G G' : Group) (f : GroupHom G G') → BookEquiv (BG G .carrier) (Σ (BG G' .carrier) (w ↦ BlindHomFiber G G' f w))

def blind_coker_total_surjective : Type
  ≔ (G G' : Group) (f : GroupHom G G')
    → Surjective (Σ (BG G' .carrier) (w ↦ BlindHomFiber G G' f w)) (ActionType G' (blind_coker G G' f))
        (u ↦ (u .fst, set_trunc (BlindHomFiber G G' f (u .fst)) (u .snd)))

def blind_coker_total_connected : Type
  ≔ (G G' : Group) (f : GroupHom G G') → Connected (ActionType G' (blind_coker G G' f))

{` The trivial homomorphism L → G' (constant at sh_{G'}, pointed by reflexivity). `}
def blind_trivial_hom (L G' : Group) : GroupHom L G' ≔ mkhom L G' ((_ ↦ shape G'), refl (shape G'))

{` xca after rem:imageandcokernel (subgroups.tex:409), (1): f mono iff the kernel is trivial. `}
def blind_mono_iff_kernel_trivial : Type
  ≔ (G G' : Group) (f : GroupHom G G') → BlindIff (BlindIsMono G G' f) (IsTrivialGroup (BlindKer G G' f))

{` (2): f epi iff the cokernel is contractible (its underlying set coker(f)(sh_{G'})). `}
def blind_epi_iff_cokernel_contractible : Type
  ≔ (G G' : Group) (f : GroupHom G G')
    → BlindIff (BlindIsEpi G G' f) (BookIsContr (gset_underlying G' (blind_coker G G' f)))

{` (3): universal property of the kernel: if f h is trivial, there is a unique k with h = ker_f k. `}
def blind_kernel_universal : Type
  ≔ (L G G' : Group) (f : GroupHom G G') (h : GroupHom L G)
    → Id (GroupHom L G') (group_hom_compose L G G' h f) (blind_trivial_hom L G')
    → BookIsContr (Σ (GroupHom L (BlindKer G G' f))
        (k ↦ Id (GroupHom L G) h (group_hom_compose L (BlindKer G G' f) G k (blind_kermap G G' f))))

{` lem:fibersofcomposites. Two composable pointed functions (f1,p1) : (X0,x0) →* (X1,x1), (f2,p2) : (X1,x1) →* (X2,x2)
   (book pointing p_i : x_i = f_i(x_{i-1})). `}
def BlindTwoPtdMaps : Type ≔ sig (
  X0 : Type, X1 : Type, X2 : Type,
  x0 : X0, x1 : X1, x2 : X2,
  f1 : X0 → X1, p1 : Id X1 x1 (f1 x0),
  f2 : X1 → X2, p2 : Id X2 x2 (f2 x1))

def BlindFib02 (D : BlindTwoPtdMaps) : Type ≔ BookFiber (D .X0) (D .X2) (x ↦ D .f2 (D .f1 x)) (D .x2)
def BlindFib12 (D : BlindTwoPtdMaps) : Type ≔ BookFiber (D .X1) (D .X2) (D .f2) (D .x2)
def BlindFib01 (D : BlindTwoPtdMaps) : Type ≔ BookFiber (D .X0) (D .X1) (D .f1) (D .x1)

{` F1(x,q) ≔ (f1 x, q). `}
def blind_F1 (D : BlindTwoPtdMaps) (u : BlindFib02 D) : BlindFib12 D ≔ (D .f1 (u .fst), u .snd)

{` F2(x,p) ≔ (x, f2(p) p2), the book's "f2(p) p2" being p2 followed by ap_{f2}(p). `}
def blind_F2 (D : BlindTwoPtdMaps) (u : BlindFib01 D) : BlindFib02 D
  ≔ (u .fst, concat (D .X2) (D .x2) (D .f2 (D .x1)) (D .f2 (D .f1 (u .fst))) (D .p2) (refl (D .f2) (u .snd)))

def BlindFibF1 (D : BlindTwoPtdMaps) : Type
  ≔ BookFiber (BlindFib02 D) (BlindFib12 D) (blind_F1 D) (D .x1, D .p2)

{` H(x, q, pair⁼(p, r)) ≔ (x, p). `}
def blind_H (D : BlindTwoPtdMaps) (v : BlindFibF1 D) : BlindFib01 D ≔ (v .fst .fst, v .snd .fst)

{` lem:fibersofcomposites (1). H is an equivalence, and its inverse sends (x,p) to a pair whose first
   component is (x, f2(p) p2) = F2(x,p). `}
def blind_fibersofcomposites_H : Type
  ≔ (D : BlindTwoPtdMaps)
    → Σ (BookIsEquiv (BlindFibF1 D) (BlindFib01 D) (blind_H D))
        (e ↦ (u : BlindFib01 D) → Id (BlindFib02 D) (e u .center .fst .fst) (blind_F2 D u))

{` lem:fibersofcomposites (2). The lower square and the adjacent triangles commute. `}
def blind_fibersofcomposites_square : Type
  ≔ (D : BlindTwoPtdMaps)
    → Product (Id (BlindFib02 D → D .X1) (u ↦ blind_F1 D u .fst) (u ↦ D .f1 (u .fst)))
        (Id (BlindFib01 D → D .X0) (u ↦ blind_F2 D u .fst) (u ↦ u .fst))

{` lem:fibersofcomposites (3). F2 H = fst. `}
def blind_fibersofcomposites_triangle : Type
  ≔ (D : BlindTwoPtdMaps)
    → Id (BlindFibF1 D → BlindFib02 D) (v ↦ blind_F2 D (blind_H D v)) (v ↦ v .fst)

{` xca:ptd-fibersofcomposites. The fibers are pointed at a0 ≔ (x0, f2(p1) p2), c0 ≔ (x1, p2), b0 ≔ (x0, p1);
   there are a point d0 of F1^{-1}(x1,p2) and pointings of F1, H and fst : F1^{-1}(x1,p2) → (f2f1)^{-1}(x2)
   (F2 and the other projections are pointed by reflexivity) such that the diagram commutes as pointed maps. `}
def blind_a0 (D : BlindTwoPtdMaps) : BlindFib02 D ≔ blind_F2 D (D .x0, D .p1)

def blind_ptd_fibersofcomposites : Type
  ≔ (D : BlindTwoPtdMaps)
    → Σ (BlindFibF1 D) (d0 ↦
      Σ (Id (BlindFib12 D) (D .x1, D .p2) (blind_F1 D (blind_a0 D))) (pF1 ↦
      Σ (Id (BlindFib01 D) (D .x0, D .p1) (blind_H D d0)) (pH ↦
      Σ (Id (BlindFib02 D) (blind_a0 D) (d0 .fst)) (pfst ↦
        Product
          (Id (BookPointedMap (BlindFibF1 D, d0) (BlindFib02 D, blind_a0 D))
            (book_pointed_compose (BlindFibF1 D, d0) (BlindFib01 D, (D .x0, D .p1)) (BlindFib02 D, blind_a0 D)
              (blind_H D, pH) (blind_F2 D, refl (blind_a0 D)))
            ((v ↦ v .fst), pfst))
        (Product
          (Id (BookPointedMap (BlindFib02 D, blind_a0 D) (D .X1, D .x1))
            (book_pointed_compose (BlindFib02 D, blind_a0 D) (BlindFib12 D, (D .x1, D .p2)) (D .X1, D .x1)
              (blind_F1 D, pF1) ((u ↦ u .fst), refl (D .x1)))
            (book_pointed_compose (BlindFib02 D, blind_a0 D) (D .X0, D .x0) (D .X1, D .x1)
              ((u ↦ u .fst), refl (D .x0)) (D .f1, D .p1)))
          (Id (BookPointedMap (BlindFib01 D, (D .x0, D .p1)) (D .X0, D .x0))
            (book_pointed_compose (BlindFib01 D, (D .x0, D .p1)) (BlindFib02 D, blind_a0 D) (D .X0, D .x0)
              (blind_F2 D, refl (blind_a0 D)) ((u ↦ u .fst), refl (D .x0)))
            ((u ↦ u .fst), refl (D .x0))))))))

{` Helper: a path x = x' and q : b = f(x) give (x, q) = (x', q · ap_f(u)) in the fiber. `}
def blind_fiber_path (A B : Type) (f : A → B) (b : B) (a : A) (q : Id B b (f a)) (a' : A) (u : Id A a a')
  : Id (BookFiber A B f b) (a, q) (a', concat B b (f a) (f a') q (refl f u))
  ≔ J A a (a'' u' ↦ Id (BookFiber A B f b) (a, q) (a'', concat B b (f a) (f a'') q (refl f u')))
      (refl a, inverse (Id B b (f a)) (concat B b (f a) (f a) q (refl (f a))) q (concat_p1 B b (f a) q)) a' u

{` ft:cmpnt:UUp->UUp. A pointed map k : (A,a) →* (B,b) induces a pointed map of components A_(a) →* B_(b). `}
def blind_component_map (A B : Type) (a : A) (b : B) (k : A → B) (kp : Id B b (k a))
  : BookPointedMap (NativeComponent A a, component_point A a) (NativeComponent B b, component_point B b)
  ≔ ((u ↦ (k (u .fst),
        mere_rec (Id A a (u .fst)) (Mere (Id B b (k (u .fst)))) (mere_isprop (Id B b (k (u .fst))))
          (p ↦ mere (Id B b (k (u .fst))) (concat B b (k a) (k (u .fst)) kp (refl k p))) (u .snd))),
     component_path B b (component_point B b)
       (k a, mere_rec (Id A a a) (Mere (Id B b (k a))) (mere_isprop (Id B b (k a)))
          (p ↦ mere (Id B b (k a)) (concat B b (k a) (k a) kp (refl k p))) (component_point A a .snd))
       kp)

{` cor:cokermaps. Composable f1 : Hom(G0,G1), f2 : Hom(G1,G2) and f2 f1 : Hom(G0,G2). `}
def blind_f21 (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2) : GroupHom G0 G2
  ≔ group_hom_compose G0 G1 G2 f1 f2

{` F1 : Hom(Ker(f2 f1), Ker(f2)), (x, q) ↦ (f1 x, q) on components, pointed via (p1, refl). `}
def blind_cor_F1 (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : GroupHom (BlindKer G0 G2 (blind_f21 G0 G1 G2 f1 f2)) (BlindKer G1 G2 f2)
  ≔ mkhom (BlindKer G0 G2 (blind_f21 G0 G1 G2 f1 f2)) (BlindKer G1 G2 f2)
      (blind_component_map (BlindHomFiber G0 G2 (blind_f21 G0 G1 G2 f1 f2) (shape G2)) (BlindHomFiber G1 G2 f2 (shape G2))
        (shape G0, hom_point G0 G2 (blind_f21 G0 G1 G2 f1 f2)) (shape G1, hom_point G1 G2 f2)
        (u ↦ (hom_function G0 G1 f1 (u .fst), u .snd))
        (blind_fiber_path (BG G1 .carrier) (BG G2 .carrier) (hom_function G1 G2 f2) (shape G2)
          (shape G1) (hom_point G1 G2 f2) (hom_function G0 G1 f1 (shape G0)) (hom_point G0 G1 f1)))

{` F2 : Hom(Ker(f1), Ker(f2 f1)), (x, p) ↦ (x, f2(p) p2) on components, pointed by reflexivity. `}
def blind_cor_F2 (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : GroupHom (BlindKer G0 G1 f1) (BlindKer G0 G2 (blind_f21 G0 G1 G2 f1 f2))
  ≔ mkhom (BlindKer G0 G1 f1) (BlindKer G0 G2 (blind_f21 G0 G1 G2 f1 f2))
      (blind_component_map (BlindHomFiber G0 G1 f1 (shape G1)) (BlindHomFiber G0 G2 (blind_f21 G0 G1 G2 f1 f2) (shape G2))
        (shape G0, hom_point G0 G1 f1) (shape G0, hom_point G0 G2 (blind_f21 G0 G1 G2 f1 f2))
        (u ↦ (u .fst, concat (BG G2 .carrier) (shape G2) (hom_function G1 G2 f2 (shape G1))
                 (hom_function G1 G2 f2 (hom_function G0 G1 f1 (u .fst))) (hom_point G1 G2 f2)
                 (refl (hom_function G1 G2 f2) (u .snd))))
        (refl (shape G0, hom_point G0 G2 (blind_f21 G0 G1 G2 f1 f2))))

{` cor:cokermaps (1). H (pointed by reflexivity) induces an isomorphism Ker(F1) ≅ Ker(f1): an isomorphism whose
   classifying map sends ((x,q,!), w, !) to (x, (w on the X1-coordinate)) = H(x, q, w) on the underlying fibers. `}
def blind_cokermaps_H_iso : Type
  ≔ (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
    → let K21 ≔ BlindKer G0 G2 (blind_f21 G0 G1 G2 f1 f2) in
      let K2 ≔ BlindKer G1 G2 f2 in
      let KF1 ≔ BlindKer K21 K2 (blind_cor_F1 G0 G1 G2 f1 f2) in
      Σ (GroupIso KF1 (BlindKer G0 G1 f1))
        (e ↦ (v : BG KF1 .carrier)
          → Id (BlindHomFiber G0 G1 f1 (shape G1))
              (hom_function KF1 (BlindKer G0 G1 f1) (e .fst) v .fst)
              (v .fst .fst .fst .fst, v .fst .snd .fst .fst))

{` cor:cokermaps (2). F1 is the unique homomorphism with f1 ker_{f2 f1} = ker_{f2} F1. `}
def blind_cokermaps_F1_unique : Type
  ≔ (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
    → let K21 ≔ BlindKer G0 G2 (blind_f21 G0 G1 G2 f1 f2) in
      let K2 ≔ BlindKer G1 G2 f2 in
      BookIsContr (Σ (GroupHom K21 K2) (F ↦
        Id (GroupHom K21 G1)
          (group_hom_compose K21 G0 G1 (blind_kermap G0 G2 (blind_f21 G0 G1 G2 f1 f2)) f1)
          (group_hom_compose K21 K2 G1 F (blind_kermap G1 G2 f2))))

{` The constructed F1 satisfies the equation (part of (2)). `}
def blind_cokermaps_F1_square : Type
  ≔ (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
    → let K21 ≔ BlindKer G0 G2 (blind_f21 G0 G1 G2 f1 f2) in
      let K2 ≔ BlindKer G1 G2 f2 in
      Id (GroupHom K21 G1)
        (group_hom_compose K21 G0 G1 (blind_kermap G0 G2 (blind_f21 G0 G1 G2 f1 f2)) f1)
        (group_hom_compose K21 K2 G1 (blind_cor_F1 G0 G1 G2 f1 f2) (blind_kermap G1 G2 f2))

{` cor:cokermaps (3). There is a unique monomorphism F2 with ker_{f1} = ker_{f2 f1} F2. `}
def blind_cokermaps_F2_unique : Type
  ≔ (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
    → let K21 ≔ BlindKer G0 G2 (blind_f21 G0 G1 G2 f1 f2) in
      let K1 ≔ BlindKer G0 G1 f1 in
      BookIsContr (Σ (GroupHom K1 K21) (F ↦
        Product (BlindIsMono K1 K21 F)
          (Id (GroupHom K1 G0) (blind_kermap G0 G1 f1)
            (group_hom_compose K1 K21 G0 F (blind_kermap G0 G2 (blind_f21 G0 G1 G2 f1 f2))))))

{` The constructed F2 satisfies the equation (part of (3)). `}
def blind_cokermaps_F2_triangle : Type
  ≔ (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
    → let K21 ≔ BlindKer G0 G2 (blind_f21 G0 G1 G2 f1 f2) in
      let K1 ≔ BlindKer G0 G1 f1 in
      Id (GroupHom K1 G0) (blind_kermap G0 G1 f1)
        (group_hom_compose K1 K21 G0 (blind_cor_F2 G0 G1 G2 f1 f2) (blind_kermap G0 G2 (blind_f21 G0 G1 G2 f1 f2)))

{` cor:cokermaps (4). (Ker(f1), F2) = (Ker(F1), ker_{F1}) in Mono(Ker(f2 f1)). `}
def blind_cokermaps_Ker_f1_F1 : Type
  ≔ (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
    → let K21 ≔ BlindKer G0 G2 (blind_f21 G0 G1 G2 f1 f2) in
      let K2 ≔ BlindKer G1 G2 f2 in
      let K1 ≔ BlindKer G0 G1 f1 in
      Σ (IsGroupMono K1 K21 (blind_cor_F2 G0 G1 G2 f1 f2)) (m ↦
        Id (GroupMonos K21) (K1, (blind_cor_F2 G0 G1 G2 f1 f2, m)) (blind_ker K21 K2 (blind_cor_F1 G0 G1 G2 f1 f2)))

{` cor:cokermaps (5). coker(F1) = coker(f1) ∘ Bker_{f2} as Ker(f2)-sets. `}
def blind_cokermaps_coker_f1_F1 : Type
  ≔ (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
    → let K21 ≔ BlindKer G0 G2 (blind_f21 G0 G1 G2 f1 f2) in
      let K2 ≔ BlindKer G1 G2 f2 in
      Id (GSet K2) (blind_coker K21 K2 (blind_cor_F1 G0 G1 G2 f1 f2))
        (gset_restrict K2 G1 (blind_kermap G1 G2 f2) (blind_coker G0 G1 f1))

{` cor:cokermaps (6). If f2 is a monomorphism, F2 is an isomorphism. `}
def blind_cokermaps_mono_F2_iso : Type
  ≔ (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
    → BlindIsMono G1 G2 f2
    → IsGroupIso (BlindKer G0 G1 f1) (BlindKer G0 G2 (blind_f21 G0 G1 G2 f1 f2)) (blind_cor_F2 G0 G1 G2 f1 f2)

{` cor:cokermaps, the generalized F'_1(w)(x,q) ≔ (f1 x, q) and the map of G2-sets tot(‖F'_1(-)‖₀). `}
def blind_cokermaps_F1' (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : GSetHom G2 (blind_coker G0 G2 (blind_f21 G0 G1 G2 f1 f2)) (blind_coker G1 G2 f2)
  ≔ w ↦ set_trunc_rec (BlindHomFiber G0 G2 (blind_f21 G0 G1 G2 f1 f2) w) (SetTrunc (BlindHomFiber G1 G2 f2 w))
      (set_trunc_set (BlindHomFiber G1 G2 f2 w))
      (u ↦ set_trunc (BlindHomFiber G1 G2 f2 w) (hom_function G0 G1 f1 (u .fst), u .snd))

{` cor:cokermaps (7). If f1 is an epimorphism, tot(‖F'_1(-)‖₀) is an equivalence of G2-sets. `}
def blind_cokermaps_epi_F1'_equiv : Type
  ≔ (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
    → BlindIsEpi G0 G1 f1
    → (w : BG G2 .carrier)
    → BookIsEquiv (SetTrunc (BlindHomFiber G0 G2 (blind_f21 G0 G1 G2 f1 f2) w)) (SetTrunc (BlindHomFiber G1 G2 f2 w))
        (blind_cokermaps_F1' G0 G1 G2 f1 f2 w)

{` xca:abstract-kernel. X(f)(z) ≔ Σ_{p : sh_H = Bf(z)} ∃_{g : sh_G = z} (p = Bf(g) Bf_pt), where Bf(g) Bf_pt is
   Bf_pt followed by ap_{Bf}(g). `}
def BlindAbsKerWitness (G H : Group) (f : GroupHom G H) (z : BG G .carrier)
  (p : Id (BG H .carrier) (shape H) (hom_function G H f z)) : Type
  ≔ Σ (Id (BG G .carrier) (shape G) z) (g ↦
      Id (Id (BG H .carrier) (shape H) (hom_function G H f z)) p
        (concat (BG H .carrier) (shape H) (hom_function G H f (shape G)) (hom_function G H f z)
          (hom_point G H f) (refl (hom_function G H f) g)))

def BlindAbsKerFamily (G H : Group) (f : GroupHom G H) (z : BG G .carrier) : Type
  ≔ Σ (Id (BG H .carrier) (shape H) (hom_function G H f z)) (p ↦ Mere (BlindAbsKerWitness G H f z p))

def blind_abs_ker_gset (G H : Group) (f : GroupHom G H) : GSet G
  ≔ z ↦ (BlindAbsKerFamily G H f z,
      sigma_set (Id (BG H .carrier) (shape H) (hom_function G H f z)) (p ↦ Mere (BlindAbsKerWitness G H f z p))
        (bg_groupoid H (shape H) (hom_function G H f z))
        (p ↦ prop_is_set (Mere (BlindAbsKerWitness G H f z p)) (mere_isprop (BlindAbsKerWitness G H f z p))))

{` The chosen point Bf_pt : X(f)(sh_G), with witness g ≔ refl. `}
def blind_abs_ker_point (G H : Group) (f : GroupHom G H) : gset_underlying G (blind_abs_ker_gset G H f)
  ≔ (hom_point G H f,
     mere (BlindAbsKerWitness G H f (shape G) (hom_point G H f)) (refl (shape G),
       inverse (Id (BG H .carrier) (shape H) (hom_function G H f (shape G)))
         (concat (BG H .carrier) (shape H) (hom_function G H f (shape G)) (hom_function G H f (shape G))
           (hom_point G H f) (refl (hom_function G H f (shape G))))
         (hom_point G H f)
         (concat_p1 (BG H .carrier) (shape H) (hom_function G H f (shape G)) (hom_point G H f))))

{` xca:abstract-kernel (1). X(f) is transitive and (X(f), Bf_pt, !) = E(ker(f)) in Sub(G). `}
def blind_abstract_kernel : Type
  ≔ (G H : Group) (f : GroupHom G H)
    → Σ (IsTransitive G (blind_abs_ker_gset G H f)) (t ↦
        Id (Subgroups G) (blind_abs_ker_gset G H f, blind_abs_ker_point G H f, t)
          (mono_to_subgroup G (blind_ker G H f)))

{` xca:abstract-kernel (2). If f is an epimorphism, X(f) simplifies to z ↦ (sh_H = Bf(z)) (pointed at Bf_pt). `}
def blind_abstract_kernel_epi : Type
  ≔ (G H : Group) (f : GroupHom G H) → BlindIsEpi G H f
    → Id (PointedGSet G) (blind_abs_ker_gset G H f, blind_abs_ker_point G H f)
        (gset_restrict G H f (principal_gset H), hom_point G H f)
