export "591-c6-half-subgroup"

{` exa:C3subC6 (part 3): Ψ(pt) = ((Fin 6, s), [0]) (c6half_psi_point), hence F
   is transitive (its action type is connected), (F, [0]) : Sub(C_6) is a
   decidable subgroup, and its underlying group is C_3 = Aut_Cyc(Fin 3, s)
   (c6half_subgroup_is_c3; cyclic_group_fin_path 2 identifies cyclic_group 3
   with the literal C_3). `}

{` Evaluating isomorphisms of permutations along a path of isomorphisms
   (separate definition to avoid bug[E0500]). `}
def c6half_iso_eval_path (p q : Permutations) (h h' : PermutationIsomorphisms p q)
  (r : Id (PermutationIsomorphisms p q) h h') (x : p .fst .fst) : Id (q .fst .fst) (h .fst .map x) (h' .fst .map x)
  ≔ refl ((k ↦ k .fst .map x) : PermutationIsomorphisms p q → q .fst .fst) r

{` fst(e0(0)) = 0: the identification (Fin 6, s) = ρ_2(Z/3, s) sends 0 to (0, 0). `}
def c6half_e0_zero
  : Id (Product (Fin two) (Remainder c6half_three)) (inr. star., remainder_at (suc. (suc. zero.)) zero. star.)
      (cycle_path_evaluate c6half_cycle (c6half_root c6half_p3) c6half_e0 c6half_q0)
  ≔ let fsc ≔ finite_standard_cycle c6half_five in
    let rp ≔ c6half_root c6half_p3 in
    let P ≔ Product (Fin two) (Remainder c6half_three) in
    let e ≔ fin_book_below_equiv c6half_six in
    let iso : PermutationIsomorphisms (c6half_cycle .fst) (fsc .fst)
      ≔ (e, x ↦ equiv_counit (Fin c6half_six) (Remainder c6half_six) e (modular_successor c6half_five (e .map x))) in
    let x0 ≔ remainder_at c6half_five zero. star. in
    let y0 : P ≔ (inr. star., remainder_at (suc. (suc. zero.)) zero. star.) in
    let rpp ≔ root_principal_path (suc. zero.) c6half_three in
    let ev1 ≔ cycle_path_evaluate c6half_cycle fsc (fin_remainder_cycle_path c6half_five) c6half_q0 in
    let b : Id (Remainder c6half_six) ev1 (e .map c6half_q0)
      ≔ c6half_iso_eval_path (c6half_cycle .fst) (fsc .fst)
          (cycle_paths_equiv c6half_cycle fsc .map (fin_remainder_cycle_path c6half_five)) iso
          (equiv_counit (Id Cycles c6half_cycle fsc) (PermutationIsomorphisms (c6half_cycle .fst) (fsc .fst))
            (cycle_paths_equiv c6half_cycle fsc) iso) c6half_q0 in
    let c : Id (Remainder c6half_six) (e .map c6half_q0) x0
      ≔ remainder_equal c6half_six (e .map c6half_q0) x0 (refl (zero. : Nat)) in
    let d : Id P y0 (cycle_path_evaluate fsc rp rpp x0)
      ≔ cycle_evaluation_from_periods fsc rp (root_finite_standard_periods (suc. zero.) (suc. (suc. zero.))) x0
          .equiv y0 .center .snd in
    calc
      y0 = cycle_path_evaluate fsc rp rpp x0 by d
      = cycle_path_evaluate fsc rp rpp ev1
        by refl (cycle_path_evaluate fsc rp rpp)
             (inverse (Remainder c6half_six) ev1 x0 (concat (Remainder c6half_six) ev1 (e .map c6half_q0) x0 b c))
      = cycle_path_evaluate c6half_cycle rp c6half_e0 c6half_q0
        by inverse P (cycle_path_evaluate c6half_cycle rp c6half_e0 c6half_q0) (cycle_path_evaluate fsc rp rpp ev1)
             (cycle_path_evaluation_concat c6half_cycle fsc rp (fin_remainder_cycle_path c6half_five) rpp c6half_q0) ∎

{` The class V_refl of thm:fiber-cdg at ρ_2(Z/3) contains e0(0). `}
def c6half_class_member
  : root_fiber_class (suc. zero.) (c6half_root c6half_p3) (c6half_p3, refl (c6half_root c6half_p3))
      .fst (cycle_path_evaluate c6half_cycle (c6half_root c6half_p3) c6half_e0 c6half_q0) .fst
  ≔ let rp ≔ c6half_root c6half_p3 in
    let P ≔ Product (Fin two) (Remainder c6half_three) in
    let y ≔ cycle_path_evaluate c6half_cycle rp c6half_e0 c6half_q0 in
    let w : RootFiber (suc. zero.) rp ≔ (c6half_p3, refl rp) in
    equiv_inverse_map (root_fiber_class (suc. zero.) rp w .fst y .fst)
      (Id (Fin two) (cycle_path_evaluate rp rp (refl rp) y .fst) (inr. star.))
      (root_fiber_class_members (suc. zero.) rp w y)
      (concat (Fin two) (cycle_path_evaluate rp rp (refl rp) y .fst) (y .fst) (inr. star.)
        (refl ((u ↦ u .fst) : P → Fin two) (transport_refl Type (X ↦ X) P y))
        (inverse (Fin two) (inr. star.) (y .fst) (refl ((u ↦ u .fst) : P → Fin two) c6half_e0_zero)))

{` Transport of classes along paths in BC_6 (the family z ↦ z/2). `}
def c6half_comp_transport_class (u v : NativeComponent Cycles c6half_cycle)
  (cp : Id (NativeComponent Cycles c6half_cycle) u v) (x : u .fst .fst .fst .fst)
  : Id (c6half_quot_family (v .fst))
      (transport (NativeComponent Cycles c6half_cycle) (z ↦ c6half_quot_family (z .fst)) u v cp
        (quotient_class (u .fst .fst .fst .fst) (mod_relation (suc. zero.) (u .fst .fst .fst .fst) (u .fst .fst .snd)) x))
      (quotient_class (v .fst .fst .fst .fst) (mod_relation (suc. zero.) (v .fst .fst .fst .fst) (v .fst .fst .snd))
        (cycle_path_evaluate (u .fst) (v .fst) (cp .fst) x))
  ≔ quotient_cycle_ap_evaluate (suc. zero.) (NativeComponent Cycles c6half_cycle) (z ↦ z .fst) u v cp x

{` Ψ(pt_{BC_3}) = ((Fin 6, s), [0]). `}
def c6half_psi_point
  : Id (ActionType c6half_group c6half_gset) (shape c6half_group, c6half_class c6half_q0)
      (c6half_psi (principal_component_point c6half_three))
  ≔ let rp ≔ c6half_root c6half_p3 in
    let u : ActionType c6half_group c6half_gset ≔ c6half_psi (principal_component_point c6half_three) in
    let Q : Type ≔ c6half_quot_family rp in
    let y : Product (Fin two) (Remainder c6half_three) ≔ cycle_path_evaluate c6half_cycle rp c6half_e0 c6half_q0 in
    let Xr : Type ≔ Product (Fin two) (Remainder c6half_three) in
    let Rr : EquivalenceRelation Xr ≔ mod_relation (suc. zero.) Xr (rp .fst .snd) in
    let V : Q ≔ root_fiber_class (suc. zero.) rp (c6half_p3, refl rp) in
    let cp : Id (NativeComponent Cycles c6half_cycle) (shape c6half_group) (u .fst)
      ≔ component_path Cycles c6half_cycle (shape c6half_group) (u .fst) c6half_e0 in
    let Vp : Id Q V (quotient_class Xr Rr y) ≔ quotient_path_of_member Xr Rr V y c6half_class_member in
    let tr : Q ≔ transport (NativeComponent Cycles c6half_cycle) (z ↦ c6half_quot_family (z .fst)) (shape c6half_group) (u .fst) cp
          (c6half_class c6half_q0) in
    (cp, pathover_of_eq (NativeComponent Cycles c6half_cycle) (z ↦ c6half_quot_family (z .fst))
      (shape c6half_group) (u .fst) cp (c6half_class c6half_q0) V
      (concat Q tr (quotient_class Xr Rr y) V
        (c6half_comp_transport_class (shape c6half_group) (u .fst) cp c6half_q0)
        (inverse Q V (quotient_class Xr Rr y) Vp)))

{` exa:C3subC6: F is transitive (its action type ≃ BC_3 is connected). `}
def c6half_transitive : IsTransitive c6half_group c6half_gset
  ≔ connected_action_type_transitive c6half_group c6half_gset
      (connected_equiv (CycleComponent c6half_three) (ActionType c6half_group c6half_gset) c6half_action_type_equiv
        .map (native_component_connected Cycles c6half_p3))

{` exa:C3subC6: (F, [0]) : Sub(C_6). `}
def c6half_subgroup : Subgroups c6half_group ≔ (c6half_gset, c6half_class c6half_q0, c6half_transitive)

{` The subgroup is decidable (claim after def:decidable-subgroup). `}
def c6half_subgroup_decidable : IsDecidableSubgroup c6half_group c6half_subgroup ≔ c6half_decidable_equality

def c6half_pointed_equiv
  : BookPointedEquiv (BG (cyclic_group c6half_three)) (BG (subgroup_group c6half_group c6half_subgroup))
  ≔ ((c6half_psi, c6half_psi_point),
     book_equivalence (CycleComponent c6half_three) (ActionType c6half_group c6half_gset) c6half_action_type_equiv .equiv)

{` exa:C3subC6: the underlying group of (F, [0]) is C_3 = Aut_Cyc(Fin 3, s). `}
def c6half_subgroup_is_c3
  : Id Group (subgroup_group c6half_group c6half_subgroup) (cyclic_group_fin (suc. (suc. zero.)))
  ≔ concat Group (subgroup_group c6half_group c6half_subgroup) (cyclic_group c6half_three) (cyclic_group_fin (suc. (suc. zero.)))
      (inverse Group (cyclic_group c6half_three) (subgroup_group c6half_group c6half_subgroup)
        (group_path_from_pointed_equiv (cyclic_group c6half_three) (subgroup_group c6half_group c6half_subgroup)
          c6half_pointed_equiv))
      (inverse Group (cyclic_group_fin (suc. (suc. zero.))) (cyclic_group c6half_three) (cyclic_group_fin_path (suc. (suc. zero.))))
