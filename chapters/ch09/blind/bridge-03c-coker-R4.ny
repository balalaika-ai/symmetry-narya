export "bridge-03-kernel-examples"
export "../../../src/242-cycle-structures-count"
export "../../../src/66-cycle-identity-classification"

{` Bridges bridge for xca:fibersofcomposites (764): coker(R_4)(sh) ≃ Fin 6. ‖R_4⁻¹(sh)‖₀ is the set of cycle
   structures on Fin 4 (power_fiber_cycle_structures, module 418, ex:Cm), and the cycle structures on Fin (j+1) are
   counted by j! (cycle_structures_fin_count, module 242); 3! = 6. The two forms of "cycle structure" (merely
   isomorphic to the standard cycle / cyclic) agree since cycles with the same periods are merely equal
   (cycle_periods_imply_paths, module 66). `}

def bridge9w_cycle_structures_equiv
  : Equiv (CycleStructuresOn three (shape BlindS4)) (CycleStructures (Fin blind_four))
  ≔ let F ≔ Fin blind_four in
    let S ≔ standard_set blind_four in
    family_equiv (Equiv F F) (t ↦ Mere (Id Permutations (finite_fin_cycle three .fst) (S, t))) (Cyclic F)
      (t ↦ iff_equiv (Mere (Id Permutations (finite_fin_cycle three .fst) (S, t))) (Cyclic F t)
        (mere_isprop (Id Permutations (finite_fin_cycle three .fst) (S, t))) (cyclic_prop F t)
        (w ↦ structure_cyclic three S t w)
        (cy ↦ trunc_map native_truncation (Id Cycles (finite_fin_cycle three) (fin_structure_cycle three (t, cy)))
          (Id Permutations (finite_fin_cycle three .fst) (S, t))
          (p ↦ refl ((c ↦ c .fst) : Cycles → Permutations) p)
          (cycle_periods_imply_paths (finite_fin_cycle three) (fin_structure_cycle three (t, cy))
            (concat (Subtypes Int) (CyclePeriods (finite_fin_cycle three)) (Multiples blind_four)
              (CyclePeriods (fin_structure_cycle three (t, cy)))
              (fin_standard_periods three)
              (inverse (Subtypes Int) (CyclePeriods (fin_structure_cycle three (t, cy))) (Multiples blind_four)
                (fin_structure_periods three (t, cy)))))))

def bridge_xca_foc_R4_coker : blind_xca_foc_R4_coker
  ≔ C ↦
    let K ≔ gset_underlying BlindS4 (cokernel (circle_group C) BlindS4 (xr_R4 C)) in
    book_equivalence K (Fin blind_six)
      (compose_equiv K (CycleStructuresOn three (shape BlindS4)) (Fin blind_six)
        (power_fiber_cycle_structures C three (shape BlindS4))
        (compose_equiv (CycleStructuresOn three (shape BlindS4)) (CycleStructures (Fin blind_four)) (Fin blind_six)
          bridge9w_cycle_structures_equiv (cycle_structures_fin_count three)))
