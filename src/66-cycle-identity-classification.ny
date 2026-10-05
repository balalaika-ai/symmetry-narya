export "65-cycle-paths"

def CyclePeriods (c : Cycles) : Subtypes Int
  ≔ cycle_periods (c .fst .fst .fst) (c .fst .fst .snd) (c .fst .snd)

def cycle_period_equality_inclusion (c d : Cycles) (p : Id (Subtypes Int) (CyclePeriods c) (CyclePeriods d))
  : PeriodInclusion (c .fst .fst .fst) (d .fst .fst .fst) (c .fst .snd) (d .fst .snd)
  ≔ n h ↦ p (refl n) .fst .trr h

def CyclePointedUniqueness (c d : Cycles) : Type
  ≔ (x : c .fst .fst .fst) (y : d .fst .fst .fst) → BookIsContr (PointedCyclePaths c d x y)

def cycle_pointed_uniqueness_prop (c d : Cycles) : isProp (CyclePointedUniqueness c d)
  ≔ pi_prop (c .fst .fst .fst) (x ↦ (y : d .fst .fst .fst) → BookIsContr (PointedCyclePaths c d x y))
      (x ↦ pi_prop (d .fst .fst .fst) (y ↦ BookIsContr (PointedCyclePaths c d x y))
        (y ↦ book_iscontr_isprop (PointedCyclePaths c d x y)))

def cycle_periods_imply_pointed (c d : Cycles) (p : Id (Subtypes Int) (CyclePeriods c) (CyclePeriods d))
  : CyclePointedUniqueness c d
  ≔ x y ↦ book_contractibility_equiv
      (PointedCycleEquivalences (c .fst .fst .fst) (d .fst .fst .fst) (c .fst .snd) (d .fst .snd) x y)
      (PointedCyclePaths c d x y)
      (canonical_inverse_equiv (PointedCyclePaths c d x y)
        (PointedCycleEquivalences (c .fst .fst .fst) (d .fst .fst .fst) (c .fst .snd) (d .fst .snd) x y)
        (pointed_cycle_paths_equiv c d x y)) .map
      (pointed_cycle_equivalences_contractible (c .fst .fst .fst) (d .fst .fst .fst)
        (c .fst .fst .snd) (d .fst .fst .snd) (c .fst .snd) (d .fst .snd) (c .snd) (d .snd)
        (cycle_period_equality_inclusion c d p)
        (cycle_period_equality_inclusion d c (inverse (Subtypes Int) (CyclePeriods c) (CyclePeriods d) p)) x y)

def cycle_pointed_imply_paths (c d : Cycles) (h : CyclePointedUniqueness c d) : Mere (Id Cycles c d)
  ≔ mere_rec (c .fst .fst .fst) (Mere (Id Cycles c d)) (mere_isprop (Id Cycles c d))
      (x ↦ mere_rec (d .fst .fst .fst) (Mere (Id Cycles c d)) (mere_isprop (Id Cycles c d))
        (y ↦ mere (Id Cycles c d) (h x y .center .fst)) (d .snd .fst)) (c .snd .fst)

def cycle_paths_imply_periods (c d : Cycles) : Mere (Id Cycles c d) → Id (Subtypes Int) (CyclePeriods c) (CyclePeriods d)
  ≔ mere_rec (Id Cycles c d) (Id (Subtypes Int) (CyclePeriods c) (CyclePeriods d))
      (subtypes_set Int (CyclePeriods c) (CyclePeriods d)) (map_path Cycles (Subtypes Int) CyclePeriods c d)

def cycle_periods_imply_paths (c d : Cycles) (p : Id (Subtypes Int) (CyclePeriods c) (CyclePeriods d))
  : Mere (Id Cycles c d) ≔ cycle_pointed_imply_paths c d (cycle_periods_imply_pointed c d p)

{` lem:IdCycle, conditions (i) and (ii). `}
def cycle_components_periods_equiv (c d : Cycles)
  : Equiv (Mere (Id Cycles c d)) (Id (Subtypes Int) (CyclePeriods c) (CyclePeriods d))
  ≔ iff_equiv (Mere (Id Cycles c d)) (Id (Subtypes Int) (CyclePeriods c) (CyclePeriods d))
      (mere_isprop (Id Cycles c d)) (subtypes_set Int (CyclePeriods c) (CyclePeriods d))
      (cycle_paths_imply_periods c d) (cycle_periods_imply_paths c d)

{` lem:IdCycle, conditions (ii) and (iii), with native cycle paths. `}
def cycle_periods_pointed_equiv (c d : Cycles)
  : Equiv (Id (Subtypes Int) (CyclePeriods c) (CyclePeriods d)) (CyclePointedUniqueness c d)
  ≔ iff_equiv (Id (Subtypes Int) (CyclePeriods c) (CyclePeriods d)) (CyclePointedUniqueness c d)
      (subtypes_set Int (CyclePeriods c) (CyclePeriods d)) (cycle_pointed_uniqueness_prop c d)
      (cycle_periods_imply_pointed c d) (h ↦ cycle_paths_imply_periods c d (cycle_pointed_imply_paths c d h))

def cycle_components_pointed_equiv (c d : Cycles)
  : Equiv (Mere (Id Cycles c d)) (CyclePointedUniqueness c d)
  ≔ compose_equiv (Mere (Id Cycles c d)) (Id (Subtypes Int) (CyclePeriods c) (CyclePeriods d))
      (CyclePointedUniqueness c d) (cycle_components_periods_equiv c d) (cycle_periods_pointed_equiv c d)

def cycle_evaluation_from_pointed (c d : Cycles) (h : CyclePointedUniqueness c d) (x : c .fst .fst .fst)
  : Equiv (Id Cycles c d) (d .fst .fst .fst)
  ≔ ((p ↦ cycle_path_evaluate c d p x), y ↦ native_contraction (PointedCyclePaths c d x y) (h x y))

{` cor:ConnCycles, using condition (ii); the other two hypotheses are
   interchangeable by the three equivalences above. `}
def cycle_evaluation_from_periods (c d : Cycles) (p : Id (Subtypes Int) (CyclePeriods c) (CyclePeriods d))
  (x : c .fst .fst .fst) : BookEquiv (Id Cycles c d) (d .fst .fst .fst)
  ≔ book_equivalence (Id Cycles c d) (d .fst .fst .fst)
      (cycle_evaluation_from_pointed c d (cycle_periods_imply_pointed c d p) x)

def cycle_evaluation_from_component (c d : Cycles) (p : Mere (Id Cycles c d)) (x : c .fst .fst .fst)
  : BookEquiv (Id Cycles c d) (d .fst .fst .fst)
  ≔ cycle_evaluation_from_periods c d (cycle_paths_imply_periods c d p) x

def cycle_automorphisms_evaluation (c : Cycles) (x : c .fst .fst .fst)
  : BookEquiv (Id Cycles c c) (c .fst .fst .fst)
  ≔ cycle_evaluation_from_periods c c (refl (CyclePeriods c)) x

def cycle_automorphisms_identity_beta (c : Cycles) (x : c .fst .fst .fst)
  : Id (c .fst .fst .fst) (cycle_automorphisms_evaluation c x .map (refl c)) x
  ≔ transport_refl Type (X ↦ X) (c .fst .fst .fst) x

def cycles_groupoid : isGroupoid Cycles
  ≔ c d ↦ hlevel_two_to_set (Id Cycles c d)
      (hlevel_equiv (suc. (suc. zero.)) (PermutationIsomorphisms (c .fst) (d .fst)) (Id Cycles c d)
        (canonical_inverse_equiv (Id Cycles c d) (PermutationIsomorphisms (c .fst) (d .fst)) (cycle_paths_equiv c d))
        (set_to_hlevel_two (PermutationIsomorphisms (c .fst) (d .fst))
          (sigma_set (Equiv (c .fst .fst .fst) (d .fst .fst .fst))
            (h ↦ Commutes (c .fst .fst .fst) (d .fst .fst .fst) (c .fst .snd) (d .fst .snd) (h .map))
            (equivalences_set (c .fst .fst .fst) (d .fst .fst .fst) (d .fst .fst .snd))
            (h ↦ prop_is_set (Commutes (c .fst .fst .fst) (d .fst .fst .fst) (c .fst .snd) (d .fst .snd) (h .map))
              (commutes_prop (c .fst .fst .fst) (d .fst .fst .fst) (d .fst .fst .snd) (c .fst .snd) (d .fst .snd) (h .map))))))
