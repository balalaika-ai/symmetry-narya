export "220-free-integer-actions"

{` The carrier of the constructed circle is the component Cyc_0 of the
   standard infinite cycle (Int, succ); its loop is the successor symmetry. `}
def infinite_successor_iso : PermutationIsomorphisms (infinite_cycle .fst) (infinite_cycle .fst)
  ≔ (int_succ_equiv, x ↦ refl (int_succ (int_succ x)))

def infinite_successor_loop_cycles : Id Cycles infinite_cycle infinite_cycle
  ≔ equiv_inverse_map (Id Cycles infinite_cycle infinite_cycle)
      (PermutationIsomorphisms (infinite_cycle .fst) (infinite_cycle .fst))
      (cycle_paths_equiv infinite_cycle infinite_cycle) infinite_successor_iso

def infinite_successor_loop_action (x : Int)
  : Id Int (cycle_path_evaluate infinite_cycle infinite_cycle infinite_successor_loop_cycles x) (int_succ x)
  ≔ evaluation_of_inverse_beta (Id Cycles infinite_cycle infinite_cycle)
      (PermutationIsomorphisms (infinite_cycle .fst) (infinite_cycle .fst)) Int
      (cycle_paths_equiv infinite_cycle infinite_cycle) (h ↦ h .fst .map x) infinite_successor_iso

def circle_component_prop (c : Cycles) : isProp (Mere (Id Cycles infinite_cycle c))
  ≔ mere_isprop (Id Cycles infinite_cycle c)

def circle_loop : Id (CycleComponent zero.) (principal_component_point zero.) (principal_component_point zero.)
  ≔ subtype_equal Cycles (c ↦ Mere (Id Cycles infinite_cycle c)) circle_component_prop
      (principal_component_point zero.) (principal_component_point zero.) infinite_successor_loop_cycles

def circle_loop_underlying
  : Id (Id Cycles infinite_cycle infinite_cycle) (circle_loop .fst) infinite_successor_loop_cycles
  ≔ equiv_counit (Id (CycleComponent zero.) (principal_component_point zero.) (principal_component_point zero.))
      (Id Cycles infinite_cycle infinite_cycle)
      (subtype_path_equiv Cycles (c ↦ Mere (Id Cycles infinite_cycle c)) circle_component_prop
        (principal_component_point zero.) (principal_component_point zero.))
      infinite_successor_loop_cycles

{` Loops of the base are the integers, by evaluation at 0. `}
def circle_loop_equiv
  : Equiv (Id (CycleComponent zero.) (principal_component_point zero.) (principal_component_point zero.)) Int
  ≔ compose_equiv (Id (CycleComponent zero.) (principal_component_point zero.) (principal_component_point zero.))
      (Id Cycles infinite_cycle infinite_cycle) Int
      (subtype_path_equiv Cycles (c ↦ Mere (Id Cycles infinite_cycle c)) circle_component_prop
        (principal_component_point zero.) (principal_component_point zero.))
      (native_equivalence (Id Cycles infinite_cycle infinite_cycle) Int
        (cycle_automorphisms_evaluation infinite_cycle int_zero))

{` Composition with the loop on the left is the successor. `}
def circle_loop_left
  (t : Id (CycleComponent zero.) (principal_component_point zero.) (principal_component_point zero.))
  : Id Int (circle_loop_equiv .map (concat (CycleComponent zero.) (principal_component_point zero.)
      (principal_component_point zero.) (principal_component_point zero.) circle_loop t))
      (int_succ (circle_loop_equiv .map t))
  ≔ let c ≔ infinite_cycle in let C ≔ CycleComponent zero. in let pt ≔ principal_component_point zero. in
    let ev ≔ ((p ↦ cycle_path_evaluate c c p int_zero) : Id Cycles c c → Int) in
    calc
      ev (concat C pt pt pt circle_loop t .fst) = ev (concat Cycles c c c (circle_loop .fst) (t .fst))
        by refl ev (map_path_concat C Cycles (u ↦ u .fst) pt pt pt circle_loop t)
      = cycle_path_evaluate c c (t .fst) (cycle_path_evaluate c c (circle_loop .fst) int_zero)
        by cycle_path_evaluation_concat c c c (circle_loop .fst) (t .fst) int_zero
      = cycle_path_evaluate c c (t .fst) (cycle_path_evaluate c c infinite_successor_loop_cycles int_zero)
        by refl ((p ↦ cycle_path_evaluate c c (t .fst) (cycle_path_evaluate c c p int_zero)) : Id Cycles c c → Int)
          circle_loop_underlying
      = cycle_path_evaluate c c (t .fst) (int_succ int_zero)
        by refl (cycle_path_evaluate c c (t .fst)) (infinite_successor_loop_action int_zero)
      = int_succ (ev (t .fst)) by cycle_paths_equiv c c .map (t .fst) .snd int_zero ∎

{` An equivalence Int ≃ B intertwining succ with G identifies (Int, succ) and (B, G). `}
def automorphism_path_from_equiv (B : Type) (e : Equiv Int B) (G : Equiv B B)
  (h : (x : Int) → Id B (e .map (int_succ x)) (G .map (e .map x)))
  : Id TypeAutomorphisms (Int, int_succ_equiv) (B, G)
  ≔ equivalence_induction Int
      (B e ↦ (G : Equiv B B) → ((x : Int) → Id B (e .map (int_succ x)) (G .map (e .map x)))
        → Id TypeAutomorphisms (Int, int_succ_equiv) (B, G))
      (G h ↦ (refl Int, equiv_path Int Int int_succ_equiv G (funext Int (_ ↦ Int) (int_succ_equiv .map) (G .map) h)))
      B e G h

def int_maps_transfer (L : Type) (E : Equiv L L) (w : Id TypeAutomorphisms (Int, int_succ_equiv) (L, E))
  (Y : Type) (F : Equiv Y Y) : Equiv (PermutationMap L Y E F) Y
  ≔ compose_equiv (PermutationMap L Y E F) (IntMaps Y F) Y
      (id_to_equiv (PermutationMap L Y E F) (IntMaps Y F)
        (refl ((X ↦ PermutationMap (X .fst) Y (X .snd) F) : TypeAutomorphisms → Type)
          (inverse TypeAutomorphisms (Int, int_succ_equiv) (L, E) w)))
      (int_maps_equiv Y F)

def circle_loop_intertwine (x : Int)
  : Id (Id (CycleComponent zero.) (principal_component_point zero.) (principal_component_point zero.))
      (equiv_inverse_map (Id (CycleComponent zero.) (principal_component_point zero.) (principal_component_point zero.)) Int
        circle_loop_equiv (int_succ x))
      (concat (CycleComponent zero.) (principal_component_point zero.) (principal_component_point zero.)
        (principal_component_point zero.) circle_loop
        (equiv_inverse_map (Id (CycleComponent zero.) (principal_component_point zero.) (principal_component_point zero.)) Int
          circle_loop_equiv x))
  ≔ let C ≔ CycleComponent zero. in let pt ≔ principal_component_point zero. in
    let psi ≔ equiv_inverse_map (Id C pt pt) Int circle_loop_equiv in
    inverse_at_known_point (Id C pt pt) Int circle_loop_equiv (concat C pt pt pt circle_loop (psi x)) (int_succ x)
      (concat Int (circle_loop_equiv .map (concat C pt pt pt circle_loop (psi x)))
        (int_succ (circle_loop_equiv .map (psi x))) (int_succ x)
        (circle_loop_left (psi x))
        (refl int_succ (equiv_counit (Id C pt pt) Int circle_loop_equiv x)))

def circle_loop_automorphism_path
  : Id TypeAutomorphisms (Int, int_succ_equiv)
      (Id (CycleComponent zero.) (principal_component_point zero.) (principal_component_point zero.),
       loop_concat_equiv (CycleComponent zero.) (principal_component_point zero.) (principal_component_point zero.) circle_loop)
  ≔ let C ≔ CycleComponent zero. in let pt ≔ principal_component_point zero. in
    automorphism_path_from_equiv (Id C pt pt) (canonical_inverse_equiv (Id C pt pt) Int circle_loop_equiv)
      (loop_concat_equiv C pt pt circle_loop) circle_loop_intertwine

{` Maps of types with automorphism from the loops of the base with
   left composition by the loop to (Y, F) are equivalent to Y. `}
def circle_loop_actions (Y : Type) (F : Equiv Y Y)
  : Equiv (PermutationMap (Id (CycleComponent zero.) (principal_component_point zero.) (principal_component_point zero.)) Y
      (loop_concat_equiv (CycleComponent zero.) (principal_component_point zero.) (principal_component_point zero.) circle_loop) F) Y
  ≔ int_maps_transfer (Id (CycleComponent zero.) (principal_component_point zero.) (principal_component_point zero.))
      (loop_concat_equiv (CycleComponent zero.) (principal_component_point zero.) (principal_component_point zero.) circle_loop)
      circle_loop_automorphism_path Y F
