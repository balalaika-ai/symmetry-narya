export "bridge-00-core"
export "../../../src/411-defgroup-counterexample"
export "../../../src/416-integer-group-identifications"

{` Bridges for group.tex, section "The type of groups" (blind file
   01-groups.ny). `}

{` ex:base=base (line 71). The map of circle_integer_loop_equiv is loop_power
   judgmentally; additivity is circle_power_concat. `}
def bridge_ex_base_eq_base : blind_ex_base_eq_base
  ≔ C ↦ (circle_integer_loop_equiv C,
      (n ↦ refl (loop_power (C .carrier) (C .base) (C .loop) n),
       m n ↦ inverse (Id (C .carrier) (C .base) (C .base))
         (concat (C .carrier) (C .base) (C .base) (C .base) (circle_power C m) (circle_power C n))
         (circle_power C (int_add m n)) (circle_power_concat C m n)))

{` Line 89. The blind swap (successor mod 2) is our fin2_swap_equiv. `}
def bridge_fin2_swap_pointwise (x : Fin two) : Id (Fin two) (blind_swap2 .map x) (fin2_swap_equiv .map x)
  ≔ match x [
  | inr. u ↦ match u [ star. ↦ refl (fin2_one) ]
  | inl. y ↦ match y [
    | inr. u ↦ match u [ star. ↦ refl fin2_zero ]
    | inl. e ↦ match e [ ] ] ]

def bridge_fin2_swap_path : Id (Equiv (Fin two) (Fin two)) blind_swap2 fin2_swap_equiv
  ≔ equiv_homotopy (Fin two) (Fin two) blind_swap2 fin2_swap_equiv bridge_fin2_swap_pointwise

def bridge_fin2_swap_twice (x : Fin two)
  : Id (Fin two) (compose_equiv (Fin two) (Fin two) (Fin two) blind_swap2 blind_swap2 .map x) (identity_equiv (Fin two) .map x)
  ≔ match x [
  | inr. u ↦ match u [ star. ↦ refl fin2_zero ]
  | inl. y ↦ match y [
    | inr. u ↦ match u [ star. ↦ refl fin2_one ]
    | inl. e ↦ match e [ ] ] ]

def bridge_fin2_ua_cases (b : Fin two)
  : Sum (Id (Id Type (Fin two) (Fin two)) (ua (Fin two) (Fin two) (fin2_automorphism b)) (refl (Fin two)))
      (Id (Id Type (Fin two) (Fin two)) (ua (Fin two) (Fin two) (fin2_automorphism b)) (ua (Fin two) (Fin two) blind_swap2))
  ≔ match b [
  | inr. _ ↦ inl. (ua_identity (Fin two))
  | inl. y ↦ match y [
    | inr. _ ↦ inr. (refl (ua (Fin two) (Fin two)) (inverse (Equiv (Fin two) (Fin two)) blind_swap2 fin2_swap_equiv
        bridge_fin2_swap_path))
    | inl. e ↦ match e [ ] ] ]

def bridge_fin2_type_loop_path (p : Id Type (Fin two) (Fin two))
  : Id (Id Type (Fin two) (Fin two))
      (ua (Fin two) (Fin two) (fin2_automorphism (id_to_equiv (Fin two) (Fin two) p .map fin2_zero))) p
  ≔ concat (Id Type (Fin two) (Fin two))
      (ua (Fin two) (Fin two) (fin2_automorphism (id_to_equiv (Fin two) (Fin two) p .map fin2_zero)))
      (ua (Fin two) (Fin two) (id_to_equiv (Fin two) (Fin two) p)) p
      (refl (ua (Fin two) (Fin two)) (fin2_automorphism_eta (id_to_equiv (Fin two) (Fin two) p)))
      (ua_eta (Fin two) (Fin two) p)

def bridge_fin2_sum_transport (P Q R : Type) (u : Id Type P Q) (v : Id Type P R) (s : Sum P R) : Sum Q R
  ≔ match s [ inl. x ↦ inl. (u .trr x) | inr. y ↦ inr. y ]

def bridge_ex_fin_two_symmetries : blind_ex_fin_two_symmetries
  ≔ let F ≔ Fin two in
    let L ≔ Id Type F F in
    let sw ≔ ua F F blind_swap2 in
    (p ↦ let r ≔ ua F F (fin2_automorphism (id_to_equiv F F p .map fin2_zero)) in
         let q ≔ bridge_fin2_type_loop_path p in
         match bridge_fin2_ua_cases (id_to_equiv F F p .map fin2_zero) [
         | inl. h ↦ inl. (concat L p r (refl F) (inverse L r p q) h)
         | inr. h ↦ inr. (concat L p r sw (inverse L r p q) h) ],
     (h ↦ fin2_zero_ne_one (concat F fin2_zero (transport Type (X ↦ X) F F (refl F) fin2_zero) fin2_one
        (inverse F (transport Type (X ↦ X) F F (refl F) fin2_zero) fin2_zero (transport_refl Type (X ↦ X) F fin2_zero))
        (map_path L F (t ↦ t .trr fin2_zero) (refl F) sw h)),
      calc
        concat Type F F F sw sw = ua F F (compose_equiv F F F blind_swap2 blind_swap2)
          by inverse L (ua F F (compose_equiv F F F blind_swap2 blind_swap2)) (concat Type F F F sw sw)
            (ua_compose F F F blind_swap2 blind_swap2)
        = ua F F (identity_equiv F)
          by refl (ua F F) (equiv_homotopy F F (compose_equiv F F F blind_swap2 blind_swap2) (identity_equiv F)
            bridge_fin2_swap_twice)
        = refl F by ua_identity F ∎))

{` Line 89, second part: the map S¹ → FinSet_2 (blind FinSet = mere Type
   paths) by circle recursion, as in our circle_finset_two_map (module 413,
   on BookFiniteSetsAt); the free-loop identification is the β-rule. `}
def bridge_ex_circle_to_finset_two : blind_ex_circle_to_finset_two
  ≔ C ↦ let d : FreeLoop (FiniteSetsAt two) ≔ (blind_bn_finset two, blind_finset_loop two blind_swap2) in
    (circle_rec C (FiniteSetsAt two) d, circle_rec_beta C (FiniteSetsAt two) d)

{` rem:heap-preview (line 139): transport in x ↦ (a = x) along f⁻¹, as
   path_heap_transport_equiv (module 413) does along f. `}
def bridge_rem_heap_preview : blind_rem_heap_preview
  ≔ A a a' f ↦ book_equivalence (Id A a a') (Id A a a)
      (transport_equiv (Id A a a') (Id A a a) (refl ((x ↦ Id A a x) : A → Type) (inverse A a a' f))) .equiv

{` rem:whypointedconngpoid (line 161). `}
def bridge_rem_component_loops : blind_rem_component_loops
  ≔ A a ↦ book_equivalence (Id (NativeComponent A a) (component_point A a) (component_point A a)) (Id A a a)
      (component_loops_equiv A a) .equiv

{` def:pt-conn-groupoid (line 194): the core bridge plus the margin notations. `}
def bridge_def_groupoid_types : Id Type BlindGroupoidTypes GroupoidTypes ≔ refl GroupoidTypes
def bridge_def_connected_types : Id Type BlindConnectedTypes ConnectedTypes ≔ refl ConnectedTypes
def bridge_def_ptconn_pointed (X : BlindPtConnGroupoid) : Id Pointed (blind_ptconn_pointed X) (pcg_pointed (bridge_pcg X))
  ≔ refl (blind_ptconn_pointed X)

{` xca:defgroup (line 215). The literal second part is refuted by our
   counterexample (U, ∅); the corrected one (A connected) is ours. `}
def bridge_xca_defgroup_connected : blind_xca_defgroup_connected
  ≔ A a ↦ (connected_based_equiv A a .map,
      equiv_inverse_map (Connected A) ((x : A) → Mere (Id A a x)) (connected_based_equiv A a))

def bridge_xca_defgroup_groupoid_refuted : Not blind_xca_defgroup_groupoid
  ≔ h ↦ defgroup_unconditional_fails (A a s ↦ h A a .snd s)

def bridge_xca_defgroup_groupoid_corrected : blind_xca_defgroup_groupoid_corrected
  ≔ A a c ↦ (connected_groupoid_loops_equiv A a c .map,
      equiv_inverse_map (isGroupoid A) (isSet (Id A a a)) (connected_groupoid_loops_equiv A a c))

def bridge_xca_defgroup_equiv : blind_xca_defgroup_equiv
  ≔ book_equivalence BlindPtConnGroupoid DefGroupSigma
      (compose_equiv BlindPtConnGroupoid PointedConnectedGroupoid DefGroupSigma bridge_def_pt_conn_groupoid
        pcg_defgroup_equiv)

{` Line 228. `}
def bridge_rem_ptconn_props : blind_rem_ptconn_props ≔ A ↦ (connected_prop A, isgroupoid_isprop A)

{` rem:aut (line 331). `}
def bridge_rem_aut_equiv : blind_rem_aut_equiv
  ≔ book_equivalence BlindGroup BlindPtConnGroupoid
      (compose_equiv BlindGroup Group BlindPtConnGroupoid bridge_def_group
        (compose_equiv Group PointedConnectedGroupoid BlindPtConnGroupoid group_classifying_equiv
          (canonical_inverse_equiv BlindPtConnGroupoid PointedConnectedGroupoid bridge_def_pt_conn_groupoid))) .equiv

def bridge_rem_aut_subtype : blind_rem_aut_subtype
  ≔ X Y ↦ book_equivalence (Id BlindPtConnGroupoid X Y) (Id Pointed (blind_ptconn_pointed X) (blind_ptconn_pointed Y))
      (compose_equiv (Id BlindPtConnGroupoid X Y) (Id PointedConnectedGroupoid (bridge_pcg X) (bridge_pcg Y))
        (Id Pointed (blind_ptconn_pointed X) (blind_ptconn_pointed Y))
        (equivalence_on_paths BlindPtConnGroupoid PointedConnectedGroupoid bridge_def_pt_conn_groupoid X Y)
        (pcg_path_pointed_equiv (bridge_pcg X) (bridge_pcg Y))) .equiv

def bridge_rem_aut_paths : blind_rem_aut_paths
  ≔ G H ↦ book_equivalence (Id BlindGroup G H) (Id Pointed (blind_BG G) (blind_BG H))
      (compose_equiv (Id BlindGroup G H) (Id Group (bridge_g G) (bridge_g H)) (Id Pointed (blind_BG G) (blind_BG H))
        (bridge_group_paths G H) (group_path_pointed_equiv (bridge_g G) (bridge_g H)))

{` rem:BG-convention (line 343). Ours holds by record eta (group_eta is
   refl); for the blind Copy type the inverse is defined by matching. `}
def bridge_bg_convention_inv (T : BlindGroup → Type) (g : (X : BlindPtConnGroupoid) → T (blind_mkgroup X))
  : (G : BlindGroup) → T G
  ≔ [ copy. X ↦ g X ]

def bridge_bg_convention_eta (T : BlindGroup → Type) (f : (G : BlindGroup) → T G)
  : (G : BlindGroup) → Id (T G) (bridge_bg_convention_inv T (X ↦ f (blind_mkgroup X)) G) (f G)
  ≔ [ copy. X ↦ refl (f (blind_mkgroup X)) ]

def bridge_rem_bg_convention : blind_rem_bg_convention
  ≔ T ↦ book_quasi_inverse_equiv ((G : BlindGroup) → T G) ((X : BlindPtConnGroupoid) → T (blind_mkgroup X))
      (f ↦ X ↦ f (blind_mkgroup X)) (bridge_bg_convention_inv T)
      (f ↦ funext BlindGroup T (bridge_bg_convention_inv T (X ↦ f (blind_mkgroup X))) f (bridge_bg_convention_eta T f))
      (g ↦ refl g) .equiv

{` rem:symmetriesofnonconnectedgroupoids (line 375). `}
def bridge_rem_component_fst_equiv : blind_rem_component_fst_equiv
  ≔ A a c ↦ connected_component_fst_equiv A c a

def bridge_rem_group_is_aut_shape : blind_rem_group_is_aut_shape
  ≔ G ↦ let A ≔ blind_B G .fst in let hA ≔ blind_B G .snd .snd .snd in let s ≔ blind_shape G in
    bridge_gpath G (blind_Aut A hA s)
      (concat Group (bridge_g G) (automorphism_group A hA s) (bridge_g (blind_Aut A hA s))
        (group_shape_automorphism_path (bridge_g G))
        (inverse Group (bridge_g (blind_Aut A hA s)) (automorphism_group A hA s) (bridge_aut A hA s)))

{` ex:circlegroup (line 389). blind_ZZ C is our circle_group C. `}
def bridge_def_zz (C : CircleSignature) : Id Group (bridge_g (blind_ZZ C)) (circle_group C) ≔ refl (circle_group C)

def bridge_ex_circlegroup_aut : blind_ex_circlegroup_aut
  ≔ C ↦ let A ≔ C .carrier in let hA ≔ circle_groupoid C in
    bridge_gpath (blind_ZZ C) (blind_Aut A hA (C .base))
      (concat Group (circle_group C) (automorphism_group A hA (C .base)) (bridge_g (blind_Aut A hA (C .base)))
        (circle_group_automorphism_path C)
        (inverse Group (bridge_g (blind_Aut A hA (C .base))) (automorphism_group A hA (C .base)) (bridge_aut A hA (C .base))))

{` xca:groups (line 414). The blind statement is for every circle C; ours
   (module 416) is for the constructed circle, whose classifying type is the
   component of Cycles at (Z, s), plus the general part of module 413 (two
   different self-identifications of circle_group C). Any circle C is
   pointed-equivalent to the constructed one (circle_delooping_equiv with
   p ↦ loop^{winding p}), which transfers ours to every C. `}
def bridge_circle_loops_map (C D : CircleSignature) (p : Id (C .carrier) (C .base) (C .base))
  : Id (D .carrier) (D .base) (D .base)
  ≔ loop_power (D .carrier) (D .base) (D .loop) (circle_winding C p)

def bridge_circle_loops_roundtrip (C D : CircleSignature) (p : Id (C .carrier) (C .base) (C .base))
  : Id (Id (C .carrier) (C .base) (C .base)) (bridge_circle_loops_map D C (bridge_circle_loops_map C D p)) p
  ≔ concat (Id (C .carrier) (C .base) (C .base)) (bridge_circle_loops_map D C (bridge_circle_loops_map C D p))
      (circle_power C (circle_winding C p)) p
      (refl (circle_power C) (circle_winding_power D (circle_winding C p)))
      (circle_power_winding C p)

def bridge_circle_loops_equiv (C D : CircleSignature)
  : Equiv (Id (C .carrier) (C .base) (C .base)) (Id (D .carrier) (D .base) (D .base))
  ≔ quasi_inverse_equiv (Id (C .carrier) (C .base) (C .base)) (Id (D .carrier) (D .base) (D .base))
      (bridge_circle_loops_map C D) (bridge_circle_loops_map D C)
      (bridge_circle_loops_roundtrip C D) (bridge_circle_loops_roundtrip D C)

def bridge_circle_loops_unit (C D : CircleSignature)
  : LoopMapUnit (C .carrier) (D .carrier) (C .base) (D .base) (bridge_circle_loops_map C D)
  ≔ refl (circle_power D) (circle_winding_power C int_zero)

def bridge_circle_loops_comp (C D : CircleSignature)
  : LoopMapComposition (C .carrier) (D .carrier) (C .base) (D .base) (bridge_circle_loops_map C D)
  ≔ p q ↦ concat (Id (D .carrier) (D .base) (D .base))
      (bridge_circle_loops_map C D (concat (C .carrier) (C .base) (C .base) (C .base) p q))
      (circle_power D (int_add (circle_winding C p) (circle_winding C q)))
      (concat (D .carrier) (D .base) (D .base) (D .base) (bridge_circle_loops_map C D p) (bridge_circle_loops_map C D q))
      (refl (circle_power D) (circle_winding_composition C p q))
      (inverse (Id (D .carrier) (D .base) (D .base))
        (concat (D .carrier) (D .base) (D .base) (D .base) (bridge_circle_loops_map C D p) (bridge_circle_loops_map C D q))
        (circle_power D (int_add (circle_winding C p) (circle_winding C q)))
        (circle_power_concat D (circle_winding C p) (circle_winding C q)))

def bridge_circle_pointed_equiv (C D : CircleSignature) : BookPointedEquiv (circle_pointed C) (circle_pointed D)
  ≔ (pointed_circle_loop_rec C (D .carrier) (D .base) (bridge_circle_loops_map C D (C .loop)),
      circle_delooping_equiv C (D .carrier) (native_circle_connected D) (D .base) (bridge_circle_loops_equiv C D)
        (bridge_circle_loops_unit C D) (bridge_circle_loops_comp C D) .equiv)

def bridge_circle_group_path (C D : CircleSignature) : Id Group (circle_group C) (circle_group D)
  ≔ group_path_from_pointed_equiv (circle_group C) (circle_group D) (bridge_circle_pointed_equiv C D)

def bridge_xca_groups : blind_xca_groups
  ≔ C ↦
    let A ≔ blind_Aut Cycles cycles_groupoid infinite_cycle in
    let K ≔ cyclic_group zero. in
    let q ≔ bridge_circle_group_path C constructed_circle in
    let P1 ≔ concat Group (circle_group C) integer_group K q integer_cyclic_path in
    let P2 ≔ concat Group (circle_group C) integer_group K q integer_cyclic_flip_path in
    let r ≔ bridge_aut Cycles cycles_groupoid infinite_cycle in
    let L ≔ Id Group (circle_group C) (bridge_g A) in
    let fix : Id Group (circle_group C) K → L ≔ P ↦
      concat Group (circle_group C) K (bridge_g A) P (inverse Group (bridge_g A) K r) in
    (bridge_gpath (blind_ZZ C) A (fix P1),
     (bridge_gpath (blind_ZZ C) A (fix P2),
      h ↦ integer_cyclic_paths_differ
        (concat_cancel_left Group (circle_group C) integer_group K q integer_cyclic_path integer_cyclic_flip_path
          (concat_cancel_right Group (circle_group C) K (bridge_g A) P1 P2 (inverse Group (bridge_g A) K r)
            (bridge_gpath_inj (blind_ZZ C) A (fix P1) (fix P2) h)))))

