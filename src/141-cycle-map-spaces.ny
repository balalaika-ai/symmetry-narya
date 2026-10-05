export "140-root-fibers"

{` The exercise of the section "Getting our cycles in order": for cycles
   (X,t), (Y,u) and x0 : X, maps of cycles are P × Y with
   P = (ord(u) | ord(t)), i.e. H_t ⊆ H_u.  The map is f ↦ (!, f(x0)). `}
def cycle_map_to_point (c d : Cycles) (x0 : c .fst .fst .fst)
  (f : PermutationMap (c .fst .fst .fst) (d .fst .fst .fst) (c .fst .snd) (d .fst .snd))
  : Product (OrderDivides (cycle_order d) (cycle_order c)) (d .fst .fst .fst)
  ≔ (cycle_map_period_inclusion (c .fst .fst .fst) (d .fst .fst .fst) (d .fst .fst .snd) (c .fst .snd) (d .fst .snd)
      (c .snd) (d .snd) f, f .fst x0)

def cycle_map_from_point (c d : Cycles) (x0 : c .fst .fst .fst)
  (v : Product (OrderDivides (cycle_order d) (cycle_order c)) (d .fst .fst .fst))
  : PermutationMap (c .fst .fst .fst) (d .fst .fst .fst) (c .fst .snd) (d .fst .snd)
  ≔ pointed_cycle_map (c .fst .fst .fst) (d .fst .fst .fst) (c .fst .fst .snd) (d .fst .fst .snd) (c .fst .snd) (d .fst .snd)
      (c .snd) (v .fst) x0 (v .snd) .fst

def cycle_map_point_equiv (c d : Cycles) (x0 : c .fst .fst .fst)
  : Equiv (PermutationMap (c .fst .fst .fst) (d .fst .fst .fst) (c .fst .snd) (d .fst .snd))
      (Product (OrderDivides (cycle_order d) (cycle_order c)) (d .fst .fst .fst))
  ≔ let X ≔ c .fst .fst .fst in let Y ≔ d .fst .fst .fst in
    let P ≔ OrderDivides (cycle_order d) (cycle_order c) in
    quasi_inverse_equiv (PermutationMap X Y (c .fst .snd) (d .fst .snd)) (Product P Y)
      (cycle_map_to_point c d x0) (cycle_map_from_point c d x0)
      (f ↦ refl ((g ↦ g .fst) : PointedPermutationMaps X Y (c .fst .snd) (d .fst .snd) x0 (f .fst x0)
          → PermutationMap X Y (c .fst .snd) (d .fst .snd))
        (pointed_cycle_maps_prop X Y (d .fst .fst .snd) (c .fst .snd) (d .fst .snd) (c .snd) x0 (f .fst x0)
          (pointed_cycle_map X Y (c .fst .fst .snd) (d .fst .fst .snd) (c .fst .snd) (d .fst .snd) (c .snd)
            (cycle_map_to_point c d x0 f .fst) x0 (f .fst x0))
          (f, refl (f .fst x0))))
      (v ↦ (order_divides_prop (cycle_order d) (cycle_order c) (cycle_map_to_point c d x0 (cycle_map_from_point c d x0 v) .fst) (v .fst),
        pointed_cycle_map X Y (c .fst .fst .snd) (d .fst .fst .snd) (c .fst .snd) (d .fst .snd) (c .snd) (v .fst) x0 (v .snd) .snd))

{` Hence an order p divides an order q iff there merely is a map of cycles
   from a cycle of order q to a cycle of order p. `}
def cycle_map_divides (c d : Cycles)
  (f : PermutationMap (c .fst .fst .fst) (d .fst .fst .fst) (c .fst .snd) (d .fst .snd))
  : OrderDivides (cycle_order d) (cycle_order c)
  ≔ cycle_map_period_inclusion (c .fst .fst .fst) (d .fst .fst .fst) (d .fst .fst .snd) (c .fst .snd) (d .fst .snd)
      (c .snd) (d .snd) f

def divides_cycle_map (c d : Cycles) (h : OrderDivides (cycle_order d) (cycle_order c))
  : Mere (PermutationMap (c .fst .fst .fst) (d .fst .fst .fst) (c .fst .snd) (d .fst .snd))
  ≔ mere_rec (c .fst .fst .fst) (Mere (PermutationMap (c .fst .fst .fst) (d .fst .fst .fst) (c .fst .snd) (d .fst .snd)))
      (mere_isprop (PermutationMap (c .fst .fst .fst) (d .fst .fst .fst) (c .fst .snd) (d .fst .snd)))
      (x0 ↦ mere_rec (d .fst .fst .fst)
        (Mere (PermutationMap (c .fst .fst .fst) (d .fst .fst .fst) (c .fst .snd) (d .fst .snd)))
        (mere_isprop (PermutationMap (c .fst .fst .fst) (d .fst .fst .fst) (c .fst .snd) (d .fst .snd)))
        (y ↦ mere (PermutationMap (c .fst .fst .fst) (d .fst .fst .fst) (c .fst .snd) (d .fst .snd))
          (cycle_map_from_point c d x0 (h, y)))
        (d .snd .fst))
      (c .snd .fst)
