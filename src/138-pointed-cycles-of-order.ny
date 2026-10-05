export "137-root-periods"

{` Cyc_d, the component of cycles of order d. `}
def CyclesOfOrder (d : Order) : Type ≔ Σ Cycles (c ↦ Id Order (cycle_order c) d)
def PointedCyclesOfOrder (d : Order) : Type ≔ Σ (CyclesOfOrder d) (u ↦ u .fst .fst .fst .fst)

def cycle_order_paths (c d : Cycles) (h : Id Order (cycle_order c) (cycle_order d)) : Mere (Id Cycles d c)
  ≔ set_trunc_paths Cycles d c .map (inverse Order (cycle_order c) (cycle_order d) h)

def pointed_cycle_of_order_path (c0 : Cycles) (x0 : c0 .fst .fst .fst) (u : PointedCyclesOfOrder (cycle_order c0))
  : PointedCyclePaths c0 (u .fst .fst) x0 (u .snd)
  ≔ cycle_periods_imply_pointed c0 (u .fst .fst)
      (cycle_paths_imply_periods c0 (u .fst .fst) (cycle_order_paths (u .fst .fst) c0 (u .fst .snd)))
      x0 (u .snd) .center

def pointed_cycles_of_order_contractible_at (c0 : Cycles) (x0 : c0 .fst .fst .fst)
  : isContr (PointedCyclesOfOrder (cycle_order c0))
  ≔ let B ≔ PointedCyclesOfOrder (cycle_order c0) in
    let f ≔ ((v ↦ ((v .fst, refl cycle_order (v .snd)),
        cycle_path_evaluate c0 (v .fst) (inverse Cycles (v .fst) c0 (v .snd)) x0))
      : Σ Cycles (c ↦ Id Cycles c c0) → B) in
    let g ≔ ((u ↦ (u .fst .fst, inverse Cycles c0 (u .fst .fst) (pointed_cycle_of_order_path c0 x0 u .fst)))
      : B → Σ Cycles (c ↦ Id Cycles c c0)) in
    contractible_retract (Σ Cycles (c ↦ Id Cycles c c0)) B (path_to_contractible Cycles c0) f g
      (u ↦ let P ≔ pointed_cycle_of_order_path c0 x0 u in
        ((refl (u .fst .fst),
          order_set (cycle_order (u .fst .fst)) (cycle_order c0)
            (refl cycle_order (inverse Cycles c0 (u .fst .fst) (P .fst))) (u .fst .snd)),
         calc
          cycle_path_evaluate c0 (u .fst .fst)
            (inverse Cycles (u .fst .fst) c0 (inverse Cycles c0 (u .fst .fst) (P .fst))) x0
          = cycle_path_evaluate c0 (u .fst .fst) (P .fst) x0
            by refl ((p ↦ cycle_path_evaluate c0 (u .fst .fst) p x0) : Id Cycles c0 (u .fst .fst) → u .fst .fst .fst .fst .fst)
              (inverse_inverse Cycles c0 (u .fst .fst) (P .fst))
          = u .snd by P .snd ∎))

{` lem:sum-cycle-point-contr, for every order d : Order = SetTrunc Cycles. `}
def pointed_cycles_of_order_contractible (d : Order) : BookIsContr (PointedCyclesOfOrder d)
  ≔ set_trunc_induction Cycles (d ↦ BookIsContr (PointedCyclesOfOrder d))
      (d ↦ prop_is_set (BookIsContr (PointedCyclesOfOrder d)) (book_iscontr_isprop (PointedCyclesOfOrder d)))
      (c0 ↦ mere_rec (c0 .fst .fst .fst) (BookIsContr (PointedCyclesOfOrder (cycle_order c0)))
        (book_iscontr_isprop (PointedCyclesOfOrder (cycle_order c0)))
        (x0 ↦ book_contraction (PointedCyclesOfOrder (cycle_order c0)) (pointed_cycles_of_order_contractible_at c0 x0))
        (c0 .snd .fst)) d
