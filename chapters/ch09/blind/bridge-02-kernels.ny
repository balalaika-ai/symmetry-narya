export "bridge-01-epi-mono"
export "../../../src/953-coker-of-composites-restriction"
export "../../../src/964-epi-versions"

{` Bridges for subgroups.tex, sec:ker (blind file 02-kernels). `}

{` def:kernel: the blind kernel is ours by refl (bridge-00-core); the groupoid proof too. `}
def bridge_def_hom_fiber (G H : Group) (f : GroupHom G H) (w : BG H .carrier)
  : Id Type (BlindHomFiber G H f w) (HomFiber G H f w) ≔ refl (BlindHomFiber G H f w)

{` lem:isTrans(coker). `}
def bridge_coker_transitive : blind_coker_transitive ≔ G G' f ↦ cokernel_transitive G G' f

{` rem:imageandcokernel: the blind subgroup is ours for every transitivity proof. `}
def bridge_coker_subgroup (G G' : Group) (f : GroupHom G G') (t : IsTransitive G' (blind_coker G G' f))
  : Id (Subgroups G') (blind_coker_subgroup G G' f t) (image_subgroup G G' f)
  ≔ (refl (cokernel G G' f), refl (cokernel_point G G' f),
     is_transitive_prop G' (cokernel G G' f) t (cokernel_transitive G G' f))

def bridge_coker_total_equiv : blind_coker_total_equiv
  ≔ G G' f ↦ book_equivalence (BG G .carrier) (Σ (BG G' .carrier) (w ↦ HomFiber G G' f w))
      (fiber_decomposition_equiv (BG G .carrier) (BG G' .carrier) (hom_function G G' f))

def bridge_coker_total_surjective : blind_coker_total_surjective
  ≔ G G' f s ↦
    let F ≔ HomFiber G G' f (s .fst) in
    let T ≔ Σ (BG G' .carrier) (w ↦ HomFiber G G' f w) in
    let m : T → ActionType G' (cokernel G G' f) ≔ u ↦ (u .fst, set_trunc (HomFiber G G' f (u .fst)) (u .snd)) in
    mere_rec (BookFiber F (SetTrunc F) (set_trunc F) (s .snd)) (Mere (BookFiber T (ActionType G' (cokernel G G' f)) m s))
      (mere_isprop (BookFiber T (ActionType G' (cokernel G G' f)) m s))
      (x ↦ mere (BookFiber T (ActionType G' (cokernel G G' f)) m s) ((s .fst, x .fst), (refl (s .fst), x .snd)))
      (set_trunc_surjective F (s .snd))

def bridge_coker_total_connected : blind_coker_total_connected ≔ G G' f ↦ cokernel_action_type_connected G G' f

{` xca after rem:imageandcokernel (line 409). `}
def bridge_def_trivial_hom (L G' : Group) : Id (GroupHom L G') (blind_trivial_hom L G') (EqmcTrivialHom L G')
  ≔ refl (blind_trivial_hom L G')

def bridge_mono_iff_kernel_trivial : blind_mono_iff_kernel_trivial
  ≔ G G' f ↦ bridge_iff_of_equiv (IsGroupMonomorphism G G' f) (IsTrivialMono G (kernel G G' f))
      (eqmc_mono_kernel_trivial_equiv G G' f)

def bridge_epi_iff_cokernel_contractible : blind_epi_iff_cokernel_contractible
  ≔ G G' f ↦ bridge_iff_of_equiv (IsGroupEpi G G' f) (BookIsContr (gset_underlying G' (cokernel G G' f)))
      (eqmc_epi_cokernel_point_contractible_equiv G G' f)

def bridge_kernel_universal : blind_kernel_universal
  ≔ L G G' f h r ↦ eqmc_kernel_universal_property G G' f L h r

{` lem:fibersofcomposites. The blind fibers, F1, F2, H are ours by refl. `}
def bridge_def_F1 (D : BlindTwoPtdMaps)
  : Id (BlindFib02 D → BlindFib12 D) (blind_F1 D) (fibcomp_F1 (D .X0) (D .X1) (D .X2) (D .f1) (D .f2) (D .x2))
  ≔ refl (blind_F1 D)

def bridge_def_F2 (D : BlindTwoPtdMaps)
  : Id (BlindFib01 D → BlindFib02 D) (blind_F2 D) (fibcomp_F2 (D .X0) (D .X1) (D .X2) (D .f1) (D .f2) (D .x1) (D .x2) (D .p2))
  ≔ refl (blind_F2 D)

def bridge_def_H (D : BlindTwoPtdMaps)
  : Id (BlindFibF1 D → BlindFib01 D) (blind_H D) (fibcomp_H (D .X0) (D .X1) (D .X2) (D .f1) (D .f2) (D .x1) (D .x2) (D .p2))
  ≔ refl (blind_H D)

def bridge_fibersofcomposites_H : blind_fibersofcomposites_H
  ≔ D ↦
    let H ≔ fibcomp_H (D .X0) (D .X1) (D .X2) (D .f1) (D .f2) (D .x1) (D .x2) (D .p2) in
    let F2 ≔ blind_F2 D in
    let e ≔ fibcomp_H_book_equiv (D .X0) (D .X1) (D .X2) (D .f1) (D .f2) (D .x1) (D .x2) (D .p2) .equiv in
    (e, u ↦
      let c ≔ e u .center in
      concat (BlindFib02 D) (c .fst .fst) (F2 (H (c .fst))) (F2 u)
        (inverse (BlindFib02 D) (F2 (H (c .fst))) (c .fst .fst)
          (fibcomp_triangle_point (D .X0) (D .X1) (D .X2) (D .f1) (D .f2) (D .x1) (D .x2) (D .p2) (c .fst)))
        (refl F2 (inverse (BlindFib01 D) u (H (c .fst)) (c .snd))))

def bridge_fibersofcomposites_square : blind_fibersofcomposites_square
  ≔ D ↦ (fibcomp_lower_square (D .X0) (D .X1) (D .X2) (D .f1) (D .f2) (D .x2),
         fibcomp_right_triangle (D .X0) (D .X1) (D .X2) (D .f1) (D .f2) (D .x1) (D .x2) (D .p2))

def bridge_fibersofcomposites_triangle : blind_fibersofcomposites_triangle
  ≔ D ↦ fibcomp_upper_triangle (D .X0) (D .X1) (D .X2) (D .f1) (D .f2) (D .x1) (D .x2) (D .p2)

{` xca:ptd-fibersofcomposites: d0 ≔ H⁻¹(x0, p1); pointings of F1 (p1, pathover), H and fst by refl. `}
def bridge_ptd_fibersofcomposites : blind_ptd_fibersofcomposites
  ≔ D ↦
    let X0 ≔ D .X0 in let X1 ≔ D .X1 in let X2 ≔ D .X2 in let f1 ≔ D .f1 in let f2 ≔ D .f2 in
    let x0 ≔ D .x0 in let x1 ≔ D .x1 in let x2 ≔ D .x2 in let p1 ≔ D .p1 in let p2 ≔ D .p2 in
    let A ≔ fibcomp_pt_fibF1 X0 X1 X2 f1 f2 x0 x1 x2 p1 p2 in
    let C ≔ fibcomp_pt_comp X0 X1 X2 f1 f2 x0 x1 x2 p1 p2 in
    let B1 ≔ fibcomp_pt_fib1 X0 X1 f1 x0 x1 p1 in
    let B2 ≔ fibcomp_pt_fib2 X1 X2 f2 x1 x2 p2 in
    (fibcomp_H_inv X0 X1 X2 f1 f2 x1 x2 p2 (x0, p1),
     (fibcomp_F1_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2 .snd,
      (refl ((x0, p1) : BlindFib01 D),
       (refl (blind_a0 D),
        (equiv_inverse_map (Id (BookPointedMap A C)
             (book_pointed_compose A B1 C (fibcomp_H_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (fibcomp_F2_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2))
             (fibcomp_fst_fibF1_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2))
           (PointedHomotopy A C
             (book_pointed_compose A B1 C (fibcomp_H_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (fibcomp_F2_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2))
             (fibcomp_fst_fibF1_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2))
           (pointed_map_path_equiv A C
             (book_pointed_compose A B1 C (fibcomp_H_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (fibcomp_F2_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2))
             (fibcomp_fst_fibF1_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2))
           (fibcomp_upper_triangle_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2),
         (equiv_inverse_map (Id (BookPointedMap C (X1, x1))
              (book_pointed_compose C B2 (X1, x1) (fibcomp_F1_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (fibcomp_fst_fib2_pointed X1 X2 f2 x1 x2 p2))
              (book_pointed_compose C (X0, x0) (X1, x1) (fibcomp_fst_comp_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (f1, p1)))
            (PointedHomotopy C (X1, x1)
              (book_pointed_compose C B2 (X1, x1) (fibcomp_F1_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (fibcomp_fst_fib2_pointed X1 X2 f2 x1 x2 p2))
              (book_pointed_compose C (X0, x0) (X1, x1) (fibcomp_fst_comp_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (f1, p1)))
            (pointed_map_path_equiv C (X1, x1)
              (book_pointed_compose C B2 (X1, x1) (fibcomp_F1_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (fibcomp_fst_fib2_pointed X1 X2 f2 x1 x2 p2))
              (book_pointed_compose C (X0, x0) (X1, x1) (fibcomp_fst_comp_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (f1, p1)))
            (fibcomp_lower_square_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2),
          equiv_inverse_map (Id (BookPointedMap B1 (X0, x0))
              (book_pointed_compose B1 C (X0, x0) (fibcomp_F2_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (fibcomp_fst_comp_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2))
              (fibcomp_fst_fib1_pointed X0 X1 f1 x0 x1 p1))
            (PointedHomotopy B1 (X0, x0)
              (book_pointed_compose B1 C (X0, x0) (fibcomp_F2_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (fibcomp_fst_comp_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2))
              (fibcomp_fst_fib1_pointed X0 X1 f1 x0 x1 p1))
            (pointed_map_path_equiv B1 (X0, x0)
              (book_pointed_compose B1 C (X0, x0) (fibcomp_F2_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2) (fibcomp_fst_comp_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2))
              (fibcomp_fst_fib1_pointed X0 X1 f1 x0 x1 p1))
            (fibcomp_right_triangle_pointed X0 X1 X2 f1 f2 x0 x1 x2 p1 p2)))))))

{` cor:cokermaps. The blind F1 differs from ours only in the pointing path of the fibers, a J-defined path
   versus ours (p1, pathover); the two agree (paths in a fiber over a groupoid with the same first
   component). Both homomorphisms are instances of bridge9_F1_at. `}
def bridge9_fiber_path_base (X1 X2 : Type) (hX2 : isGroupoid X2) (f2 : X1 → X2) (x2 : X2) (x1 : X1) (p2 : Id X2 x2 (f2 x1))
  : Id (Id (BookFiber X1 X2 f2 x2) (x1, p2) (x1, concat X2 x2 (f2 x1) (f2 x1) p2 (refl (f2 x1))))
      (blind_fiber_path X1 X2 f2 x2 x1 p2 x1 (refl x1))
      (refl x1, mapped_pathover_append X1 X2 f2 x2 x1 x1 (refl x1) p2)
  ≔ let q ≔ concat X2 x2 (f2 x1) (f2 x1) p2 (refl (f2 x1)) in
    let F ≔ BookFiber X1 X2 f2 x2 in
    let P ≔ (a'' u' ↦ Id F (x1, p2) (a'', concat X2 x2 (f2 x1) (f2 a'') p2 (refl f2 u'))) : (a'' : X1) → Id X1 x1 a'' → Type in
    let s1 ≔ inverse (Id X2 x2 (f2 x1)) q p2 (concat_p1 X2 x2 (f2 x1) p2) in
    let b0 : Id F (x1, p2) (x1, q) ≔ (refl x1, s1) in
    let pr ≔ (s ↦ (refl x1, s)) : Id (Id X2 x2 (f2 x1)) p2 q → Id F (x1, p2) (x1, q) in
    concat (Id F (x1, p2) (x1, q)) (J X1 x1 P b0 x1 (refl x1)) b0 (refl x1, mapped_pathover_append X1 X2 f2 x2 x1 x1 (refl x1) p2)
      (inverse (Id F (x1, p2) (x1, q)) b0 (J X1 x1 P b0 x1 (refl x1)) (Jβ X1 x1 P b0))
      (refl pr (hX2 x2 (f2 x1) p2 q s1 (mapped_pathover_append X1 X2 f2 x2 x1 x1 (refl x1) p2)))

def bridge9_fiber_path_agree (X1 X2 : Type) (hX2 : isGroupoid X2) (f2 : X1 → X2) (x2 : X2) (x1 : X1) (p2 : Id X2 x2 (f2 x1))
  (a' : X1) (u : Id X1 x1 a')
  : Id (Id (BookFiber X1 X2 f2 x2) (x1, p2) (a', concat X2 x2 (f2 x1) (f2 a') p2 (refl f2 u)))
      (blind_fiber_path X1 X2 f2 x2 x1 p2 a' u)
      (u, mapped_pathover_append X1 X2 f2 x2 x1 a' u p2)
  ≔ J X1 x1 (a'' u' ↦ Id (Id (BookFiber X1 X2 f2 x2) (x1, p2) (a'', concat X2 x2 (f2 x1) (f2 a'') p2 (refl f2 u')))
                 (blind_fiber_path X1 X2 f2 x2 x1 p2 a'' u')
                 (u', mapped_pathover_append X1 X2 f2 x2 x1 a'' u' p2))
      (bridge9_fiber_path_base X1 X2 hX2 f2 x2 x1 p2) a' u

def bridge9_F1_point_type (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2) : Type
  ≔ Id (HomFiber G1 G2 f2 (shape G2)) (kernel_shape G1 G2 f2)
      (fibcomp_F1 (BG G0 .carrier) (BG G1 .carrier) (BG G2 .carrier) (hom_function G0 G1 f1) (hom_function G1 G2 f2) (shape G2)
        (kernel_shape G0 G2 (kc_compose G0 G1 G2 f1 f2)))

def bridge9_F1_at (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2) (kp : bridge9_F1_point_type G0 G1 G2 f1 f2)
  : GroupHom (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2)
  ≔ ch9w2_aut_hom (HomFiber G0 G2 (kc_compose G0 G1 G2 f1 f2) (shape G2)) (HomFiber G1 G2 f2 (shape G2))
      (hom_fiber_groupoid G0 G2 (kc_compose G0 G1 G2 f1 f2) (shape G2)) (hom_fiber_groupoid G1 G2 f2 (shape G2))
      (fibcomp_F1 (BG G0 .carrier) (BG G1 .carrier) (BG G2 .carrier) (hom_function G0 G1 f1) (hom_function G1 G2 f2) (shape G2))
      (kernel_shape G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_shape G1 G2 f2) kp

def bridge9_blind_kp (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2) : bridge9_F1_point_type G0 G1 G2 f1 f2
  ≔ blind_fiber_path (BG G1 .carrier) (BG G2 .carrier) (hom_function G1 G2 f2) (shape G2)
      (shape G1) (hom_point G1 G2 f2) (hom_function G0 G1 f1 (shape G0)) (hom_point G0 G1 f1)

def bridge9_kp_path (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : Id (bridge9_F1_point_type G0 G1 G2 f1 f2) (kc_F1_point G0 G1 G2 f1 f2) (bridge9_blind_kp G0 G1 G2 f1 f2)
  ≔ inverse (bridge9_F1_point_type G0 G1 G2 f1 f2) (bridge9_blind_kp G0 G1 G2 f1 f2) (kc_F1_point G0 G1 G2 f1 f2)
      (bridge9_fiber_path_agree (BG G1 .carrier) (BG G2 .carrier) (bg_groupoid G2) (hom_function G1 G2 f2) (shape G2)
        (shape G1) (hom_point G1 G2 f2) (hom_function G0 G1 f1 (shape G0)) (hom_point G0 G1 f1))

def bridge_def_cor_F1_blind (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : Id (GroupHom (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2))
      (blind_cor_F1 G0 G1 G2 f1 f2) (bridge9_F1_at G0 G1 G2 f1 f2 (bridge9_blind_kp G0 G1 G2 f1 f2))
  ≔ refl (blind_cor_F1 G0 G1 G2 f1 f2)

def bridge_def_cor_F1_ours (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : Id (GroupHom (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2))
      (kc_F1 G0 G1 G2 f1 f2) (bridge9_F1_at G0 G1 G2 f1 f2 (kc_F1_point G0 G1 G2 f1 f2))
  ≔ refl (kc_F1 G0 G1 G2 f1 f2)

def bridge_def_cor_F1 (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : Id (GroupHom (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)) (kernel_group G1 G2 f2))
      (kc_F1 G0 G1 G2 f1 f2) (blind_cor_F1 G0 G1 G2 f1 f2)
  ≔ refl (bridge9_F1_at G0 G1 G2 f1 f2) (bridge9_kp_path G0 G1 G2 f1 f2)

def bridge_def_cor_F2 (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : Id (GroupHom (kernel_group G0 G1 f1) (kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2)))
      (blind_cor_F2 G0 G1 G2 f1 f2) (kc_F2 G0 G1 G2 f1 f2)
  ≔ refl (blind_cor_F2 G0 G1 G2 f1 f2)

{` Transport of a statement about F1 from our pointing to the blind one. `}
def bridge9_F1_transport (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  (P : bridge9_F1_point_type G0 G1 G2 f1 f2 → Type) (h : P (kc_F1_point G0 G1 G2 f1 f2)) : P (bridge9_blind_kp G0 G1 G2 f1 f2)
  ≔ transport (bridge9_F1_point_type G0 G1 G2 f1 f2) P (kc_F1_point G0 G1 G2 f1 f2) (bridge9_blind_kp G0 G1 G2 f1 f2)
      (bridge9_kp_path G0 G1 G2 f1 f2) h

{` cor:cokermaps (1). `}
def bridge9_H_iso_stmt (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2) (kp : bridge9_F1_point_type G0 G1 G2 f1 f2) : Type
  ≔ let K21 ≔ kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2) in
    let K2 ≔ kernel_group G1 G2 f2 in
    let KF1 ≔ kernel_group K21 K2 (bridge9_F1_at G0 G1 G2 f1 f2 kp) in
    Σ (GroupIso KF1 (kernel_group G0 G1 f1))
      (e ↦ (v : BG KF1 .carrier)
        → Id (HomFiber G0 G1 f1 (shape G1))
            (hom_function KF1 (kernel_group G0 G1 f1) (e .fst) v .fst)
            (v .fst .fst .fst .fst, v .fst .snd .fst .fst))

def bridge_cokermaps_H_iso : blind_cokermaps_H_iso
  ≔ G0 G1 G2 f1 f2 ↦
    bridge9_F1_transport G0 G1 G2 f1 f2 (bridge9_H_iso_stmt G0 G1 G2 f1 f2)
      (kc_H_group_iso G0 G1 G2 f1 f2,
       v ↦ refl ((v .fst .fst .fst .fst, v .fst .snd .fst .fst) : HomFiber G0 G1 f1 (shape G1)))

{` cor:cokermaps (2). `}
def bridge_cokermaps_F1_unique : blind_cokermaps_F1_unique ≔ G0 G1 G2 f1 f2 ↦ kc_F1_unique G0 G1 G2 f1 f2

def bridge_cokermaps_F1_square : blind_cokermaps_F1_square
  ≔ G0 G1 G2 f1 f2 ↦
    let K21 ≔ kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2) in
    let K2 ≔ kernel_group G1 G2 f2 in
    bridge9_F1_transport G0 G1 G2 f1 f2
      (kp ↦ Id (GroupHom K21 G1)
        (group_hom_compose K21 G0 G1 (kernel_inclusion G0 G2 (kc_compose G0 G1 G2 f1 f2)) f1)
        (group_hom_compose K21 K2 G1 (bridge9_F1_at G0 G1 G2 f1 f2 kp) (kernel_inclusion G1 G2 f2)))
      (kc_lower_square G0 G1 G2 f1 f2)

{` cor:cokermaps (3): the blind Σ also carries a (propositional) mono proof, implied by the equation. `}
def bridge_cokermaps_F2_unique : blind_cokermaps_F2_unique
  ≔ G0 G1 G2 f1 f2 ↦
    let K ≔ kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2) in
    let K1 ≔ kernel_group G0 G1 f1 in
    let ki ≔ kernel_inclusion G0 G2 (kc_compose G0 G1 G2 f1 f2) in
    let E ≔ (F ↦ Id (GroupHom K1 G0) (kernel_inclusion G0 G1 f1) (group_hom_compose K1 K G0 F ki)) : GroupHom K1 K → Type in
    let mono_of ≔ (F ↦ e ↦ group_monomorphism_cancel K1 K G0 F ki
        (transport (GroupHom K1 G0) (IsGroupMonomorphism K1 G0) (kernel_inclusion G0 G1 f1) (group_hom_compose K1 K G0 F ki) e
          (usym_injective_group_mono K1 G0 (kernel_inclusion G0 G1 f1) (kernel_inclusion_mono G0 G1 f1))))
      : (F : GroupHom K1 K) → E F → IsGroupMonomorphism K1 K F in
    book_contractibility_equiv (Σ (GroupHom K1 K) E) (Σ (GroupHom K1 K) (F ↦ Product (IsGroupMonomorphism K1 K F) (E F)))
      (quasi_inverse_equiv (Σ (GroupHom K1 K) E) (Σ (GroupHom K1 K) (F ↦ Product (IsGroupMonomorphism K1 K F) (E F)))
        (t ↦ (t .fst, (mono_of (t .fst) (t .snd), t .snd))) (t ↦ (t .fst, t .snd .snd))
        (t ↦ refl t)
        (t ↦ (refl (t .fst), (is_group_monomorphism_prop K1 K (t .fst) (mono_of (t .fst) (t .snd .snd)) (t .snd .fst),
                               refl (t .snd .snd)))))
      .map (kc_F2_unique G0 G1 G2 f1 f2)

def bridge_cokermaps_F2_triangle : blind_cokermaps_F2_triangle ≔ G0 G1 G2 f1 f2 ↦ kc_upper_right G0 G1 G2 f1 f2

{` cor:cokermaps (4). `}
def bridge_cokermaps_Ker_f1_F1 : blind_cokermaps_Ker_f1_F1
  ≔ G0 G1 G2 f1 f2 ↦
    let K21 ≔ kernel_group G0 G2 (kc_compose G0 G1 G2 f1 f2) in
    let K2 ≔ kernel_group G1 G2 f2 in
    let K1 ≔ kernel_group G0 G1 f1 in
    bridge9_F1_transport G0 G1 G2 f1 f2
      (kp ↦ Σ (IsGroupMono K1 K21 (kc_F2 G0 G1 G2 f1 f2)) (m ↦
        Id (GroupMonos K21) (K1, (kc_F2 G0 G1 G2 f1 f2, m)) (kernel K21 K2 (bridge9_F1_at G0 G1 G2 f1 f2 kp))))
      (kc_F2_mono G0 G1 G2 f1 f2, kc_monos_path G0 G1 G2 f1 f2)

{` cor:cokermaps (5) is false as printed: counterexample G0 = 1, G1 = G2 = Σ3, f1 the unique map, f2 = id. `}
def bridge_cokermaps_coker_f1_F1_refuted (h : blind_cokermaps_coker_f1_F1) : Empty
  ≔ let S ≔ symmetric_group three in
    let f1 ≔ group_hom_from_unit S in let f2 ≔ group_hom_id S in
    let K21 ≔ kernel_group unit_group S (kc_compose unit_group S S f1 f2) in
    let K2 ≔ kernel_group S S f2 in
    let P ≔ (kp ↦ Id (GSet K2) (cokernel K21 K2 (bridge9_F1_at unit_group S S f1 f2 kp))
                 (gset_restrict K2 S (kernel_inclusion S S f2) (cokernel unit_group S f1)))
          : bridge9_F1_point_type unit_group S S f1 f2 → Type in
    kc_coker_restriction_counterexample
      (transport (bridge9_F1_point_type unit_group S S f1 f2) P
        (bridge9_blind_kp unit_group S S f1 f2) (kc_F1_point unit_group S S f1 f2)
        (inverse (bridge9_F1_point_type unit_group S S f1 f2) (kc_F1_point unit_group S S f1 f2) (bridge9_blind_kp unit_group S S f1 f2)
          (bridge9_kp_path unit_group S S f1 f2))
        (h unit_group S S f1 f2))

{` cor:cokermaps (6), (7). `}
def bridge_cokermaps_mono_F2_iso : blind_cokermaps_mono_F2_iso ≔ G0 G1 G2 f1 f2 m ↦ kc_F2_iso_of_mono G0 G1 G2 f1 f2 m

def bridge_def_cokermaps_F1' (G0 G1 G2 : Group) (f1 : GroupHom G0 G1) (f2 : GroupHom G1 G2)
  : Id (GSetHom G2 (cokernel G0 G2 (kc_compose G0 G1 G2 f1 f2)) (cokernel G1 G2 f2))
      (blind_cokermaps_F1' G0 G1 G2 f1 f2) (kc_coker_hom G0 G1 G2 f1 f2)
  ≔ refl (blind_cokermaps_F1' G0 G1 G2 f1 f2)

def bridge_cokermaps_epi_F1'_equiv : blind_cokermaps_epi_F1'_equiv
  ≔ G0 G1 G2 f1 f2 e w ↦ kc_coker_hom_is_equiv_of_epi G0 G1 G2 f1 f2 e w

{` xca:abstract-kernel. The blind X(f) and its point are ours by refl. `}
def bridge_def_abs_ker_gset (G H : Group) (f : GroupHom G H) : Id (GSet G) (blind_abs_ker_gset G H f) (abstract_kernel_gset G H f)
  ≔ refl (blind_abs_ker_gset G H f)

def bridge_def_abs_ker_point (G H : Group) (f : GroupHom G H)
  : Id (gset_underlying G (abstract_kernel_gset G H f)) (blind_abs_ker_point G H f) (abstract_kernel_point G H f)
  ≔ refl (blind_abs_ker_point G H f)

def bridge_abstract_kernel : blind_abstract_kernel
  ≔ G H f ↦ (abstract_kernel_transitive G H f, abstract_kernel_path G H f)

def bridge_abstract_kernel_epi : blind_abstract_kernel_epi
  ≔ G H f e ↦ pointed_gset_path G (abstract_kernel_gset G H f) (kernel_gset G H f) (abstract_kernel_point G H f) (hom_point G H f)
      (abstract_kernel_epi_equiv_of_epi G H f e) (refl (hom_point G H f))
