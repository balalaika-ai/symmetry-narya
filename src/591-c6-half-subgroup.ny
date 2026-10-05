export "590-c6-half-quotient"

{` exa:C3subC6 (part 2): (F, [0]) : Sub(C_6) and its underlying group is C_3.

   Following the book: ρ_2 : Cyc_3 → Cyc_6 (cycle_root 1 on cycles of the
   order of the standard 3-cycle), the identification of the fiber of ρ_2 over
   (X, t) with X/2 (thm:fiber-cdg in the form of root_order_fiber_equiv,
   module 145), and lem:sum-of-fibers give an equivalence
   Ψ : BC_3 ≃ Σ_{(X,t) : BC_6} X/2 (c6half_action_type_equiv). Here BC_3 is
   the component of the standard 3-cycle (cyclic_group 3). The pointing,
   the subgroup and the identification with C_3 are in module 592. `}

def c6half_three : Nat ≔ suc. (suc. (suc. zero.))

def c6half_p3 : Cycles ≔ principal_cycle c6half_three

def c6half_root (d : Cycles) : Cycles ≔ cycle_root (suc. zero.) d

{` (Fin 6, s) = ρ_2(Z/3, s), sending 0 to (0, 0). `}
def c6half_e0 : Id Cycles c6half_cycle (c6half_root c6half_p3)
  ≔ concat Cycles c6half_cycle (finite_standard_cycle c6half_five) (c6half_root c6half_p3)
      (fin_remainder_cycle_path c6half_five) (root_principal_path (suc. zero.) c6half_three)

def c6half_d3 : Order ≔ cycle_order c6half_p3

def C3Cyc : Type ≔ CyclesOfOrder c6half_d3

def C6Cyc : Type ≔ CyclesOfOrder (order_root (suc. zero.) c6half_d3)

def c6half_mere_sym (A : Type) (x y : A) (m : Mere (Id A x y)) : Mere (Id A y x)
  ≔ mere_rec (Id A x y) (Mere (Id A y x)) (mere_isprop (Id A y x)) (p ↦ mere (Id A y x) (inverse A x y p)) m

{` BC_3 = Cyc_3 (component of the standard 3-cycle) is the type of cycles of its order. `}
def c6half_comp3_equiv : Equiv (CycleComponent c6half_three) C3Cyc
  ≔ family_equiv Cycles (x ↦ Mere (Id Cycles c6half_p3 x)) (x ↦ Id Order (cycle_order x) c6half_d3)
      (x ↦ iff_equiv (Mere (Id Cycles c6half_p3 x)) (Id Order (cycle_order x) c6half_d3)
        (mere_isprop (Id Cycles c6half_p3 x)) (order_set (cycle_order x) c6half_d3)
        (m ↦ equiv_inverse_map (Id Order (cycle_order x) c6half_d3) (Mere (Id Cycles x c6half_p3))
          (set_trunc_paths Cycles x c6half_p3) (c6half_mere_sym Cycles c6half_p3 x m))
        (h ↦ c6half_mere_sym Cycles x c6half_p3 (set_trunc_paths Cycles x c6half_p3 .map h)))

def c6half_order6 : Id Order (order_root (suc. zero.) c6half_d3) (cycle_order c6half_cycle)
  ≔ refl cycle_order (inverse Cycles c6half_cycle (c6half_root c6half_p3) c6half_e0)

def c6half_order6_iff (x : Cycles)
  : Equiv (Id Order (cycle_order x) (order_root (suc. zero.) c6half_d3)) (Mere (Id Cycles c6half_cycle x))
  ≔ let e6 ≔ order_root (suc. zero.) c6half_d3 in
    iff_equiv (Id Order (cycle_order x) e6) (Mere (Id Cycles c6half_cycle x))
      (order_set (cycle_order x) e6) (mere_isprop (Id Cycles c6half_cycle x))
      (h ↦ c6half_mere_sym Cycles x c6half_cycle (set_trunc_paths Cycles x c6half_cycle .map
        (concat Order (cycle_order x) e6 (cycle_order c6half_cycle) h c6half_order6)))
      (m ↦ concat Order (cycle_order x) (cycle_order c6half_cycle) e6
        (equiv_inverse_map (Id Order (cycle_order x) (cycle_order c6half_cycle)) (Mere (Id Cycles x c6half_cycle))
          (set_trunc_paths Cycles x c6half_cycle) (c6half_mere_sym Cycles c6half_cycle x m))
        (inverse Order e6 (cycle_order c6half_cycle) c6half_order6))

def c6half_quot_family (c : Cycles) : Type ≔ ModQuotient (suc. zero.) (c .fst .fst .fst) (c .fst .snd)

{` Σ over Cyc_6 (cycles of order 6) ≃ the action type Σ_{z : BC_6} F(z). `}
def c6half_total_equiv
  : Equiv (Σ C6Cyc (b ↦ c6half_quot_family (b .fst))) (ActionType c6half_group c6half_gset)
  ≔ let e6 ≔ order_root (suc. zero.) c6half_d3 in
    let S ≔ Σ C6Cyc (b ↦ c6half_quot_family (b .fst)) in
    let T ≔ ActionType c6half_group c6half_gset in
    let fw : S → T ≔ u ↦ ((u .fst .fst, c6half_order6_iff (u .fst .fst) .map (u .fst .snd)), u .snd) in
    let bw : T → S ≔ v ↦ ((v .fst .fst,
        equiv_inverse_map (Id Order (cycle_order (v .fst .fst)) e6) (Mere (Id Cycles c6half_cycle (v .fst .fst)))
          (c6half_order6_iff (v .fst .fst)) (v .fst .snd)), v .snd) in
    quasi_inverse_equiv S T fw bw
      (u ↦ ((refl (u .fst .fst), order_set (cycle_order (u .fst .fst)) e6 (bw (fw u) .fst .snd) (u .fst .snd)), refl (u .snd)))
      (v ↦ ((refl (v .fst .fst), mere_isprop (Id Cycles c6half_cycle (v .fst .fst)) (fw (bw v) .fst .snd) (v .fst .snd)),
        refl (v .snd)))

def c6half_rho (v : C3Cyc) : C6Cyc ≔ cycle_root_of_order (suc. zero.) c6half_d3 v

{` Ψ : BC_3 ≃ Σ_{(X,t) : BC_6} X/2, by lem:sum-of-fibers and thm:fiber-cdg. `}
def c6half_action_type_equiv : Equiv (CycleComponent c6half_three) (ActionType c6half_group c6half_gset)
  ≔ let e6 ≔ order_root (suc. zero.) c6half_d3 in
    let Fib ≔ Σ C6Cyc (b ↦ BookFiber C3Cyc C6Cyc c6half_rho b) in
    let Qs ≔ Σ C6Cyc (b ↦ c6half_quot_family (b .fst)) in
    compose_equiv (CycleComponent c6half_three) C3Cyc (ActionType c6half_group c6half_gset) c6half_comp3_equiv
      (compose_equiv C3Cyc Fib (ActionType c6half_group c6half_gset)
        (canonical_inverse_equiv Fib C3Cyc (sum_of_fibers_equiv C3Cyc C6Cyc c6half_rho))
        (compose_equiv Fib Qs (ActionType c6half_group c6half_gset)
          (family_equiv C6Cyc (b ↦ BookFiber C3Cyc C6Cyc c6half_rho b) (b ↦ c6half_quot_family (b .fst))
            (b ↦ root_order_fiber_equiv (suc. zero.) c6half_d3 b))
          c6half_total_equiv))

def c6half_psi (u : CycleComponent c6half_three) : ActionType c6half_group c6half_gset
  ≔ c6half_action_type_equiv .map u

def c6half_psi_point_fst
  : Id Cycles (c6half_psi (principal_component_point c6half_three) .fst .fst) (c6half_root c6half_p3)
  ≔ refl (c6half_root c6half_p3)

def c6half_psi_point_snd
  : Id (c6half_quot_family (c6half_root c6half_p3)) (c6half_psi (principal_component_point c6half_three) .snd)
      (root_fiber_class (suc. zero.) (c6half_root c6half_p3) (c6half_p3, refl (c6half_root c6half_p3)))
  ≔ refl (root_fiber_class (suc. zero.) (c6half_root c6half_p3) (c6half_p3, refl (c6half_root c6half_p3)))
