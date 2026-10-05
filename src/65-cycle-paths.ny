export "64-pointed-cycle-maps"

def SetAutomorphisms (S : SetTypes) : Type ≔ Equiv (S .fst) (S .fst)

def automorphism_refl_commutes (S : SetTypes) (e f : SetAutomorphisms S)
  : Equiv (Id (SetAutomorphisms S) e f)
      (Commutes (S .fst) (S .fst) e f (transport_equiv (S .fst) (S .fst) (refl (S .fst)) .map))
  ≔ iff_equiv (Id (SetAutomorphisms S) e f)
      (Commutes (S .fst) (S .fst) e f (transport_equiv (S .fst) (S .fst) (refl (S .fst)) .map))
      (equivalences_set (S .fst) (S .fst) (S .snd) e f)
      (commutes_prop (S .fst) (S .fst) (S .snd) e f (transport_equiv (S .fst) (S .fst) (refl (S .fst)) .map))
      (p x ↦ calc
        transport Type (X ↦ X) (S .fst) (S .fst) (refl (S .fst)) (e .map x)
        = e .map x by transport_refl Type (X ↦ X) (S .fst) (e .map x)
        = f .map x by p .map (refl x)
        = f .map (transport Type (X ↦ X) (S .fst) (S .fst) (refl (S .fst)) x)
          by refl (f .map) (transport_refl Type (X ↦ X) (S .fst) x) ∎)
      (h ↦ equiv_homotopy (S .fst) (S .fst) e f (x ↦ calc
        e .map x = transport Type (X ↦ X) (S .fst) (S .fst) (refl (S .fst)) (e .map x)
          by transport_refl Type (X ↦ X) (S .fst) (e .map x)
        = f .map (transport Type (X ↦ X) (S .fst) (S .fst) (refl (S .fst)) x) by h x
        = f .map x by refl (f .map) (transport_refl Type (X ↦ X) (S .fst) x) ∎))

def automorphism_pathover_commutes (S T : SetTypes) (p : Id SetTypes S T) (e : SetAutomorphisms S) (f : SetAutomorphisms T)
  : Equiv (Id SetAutomorphisms p e f)
      (Commutes (S .fst) (T .fst) e f (set_paths_transport_equiv S T .map p .map))
  ≔ J SetTypes S
      (T p ↦ (f : SetAutomorphisms T) → Equiv (Id SetAutomorphisms p e f)
        (Commutes (S .fst) (T .fst) e f (set_paths_transport_equiv S T .map p .map)))
      (automorphism_refl_commutes S e) T p f

def automorphism_pathover_prop (S T : SetTypes) (p : Id SetTypes S T) (e : SetAutomorphisms S) (f : SetAutomorphisms T)
  : isProp (Id SetAutomorphisms p e f)
  ≔ hlevel_one_to_prop (Id SetAutomorphisms p e f)
      (pathover_hlevel (suc. zero.) SetTypes SetAutomorphisms
        (S ↦ set_to_hlevel_two (SetAutomorphisms S) (equivalences_set (S .fst) (S .fst) (S .snd))) S T p e f)

def PermutationIsomorphisms (p q : Permutations) : Type
  ≔ Σ (Equiv (p .fst .fst) (q .fst .fst)) (h ↦ Commutes (p .fst .fst) (q .fst .fst) (p .snd) (q .snd) (h .map))

def permutation_paths_equiv (p q : Permutations) : Equiv (Id Permutations p q) (PermutationIsomorphisms p q)
  ≔ compose_equiv (Id Permutations p q) (SigmaPath SetTypes SetAutomorphisms p q) (PermutationIsomorphisms p q)
      (canonical_inverse_equiv (SigmaPath SetTypes SetAutomorphisms p q) (Id Permutations p q)
        (sigma_path_equiv SetTypes SetAutomorphisms p q))
      (propositional_subtype_equiv (Id SetTypes (p .fst) (q .fst)) (Equiv (p .fst .fst) (q .fst .fst))
        (s ↦ Id SetAutomorphisms s (p .snd) (q .snd))
        (h ↦ Commutes (p .fst .fst) (q .fst .fst) (p .snd) (q .snd) (h .map))
        (s ↦ automorphism_pathover_prop (p .fst) (q .fst) s (p .snd) (q .snd))
        (h ↦ commutes_prop (p .fst .fst) (q .fst .fst) (q .fst .snd) (p .snd) (q .snd) (h .map))
        (set_paths_transport_equiv (p .fst) (q .fst))
        (s ↦ automorphism_pathover_commutes (p .fst) (q .fst) s (p .snd) (q .snd)))

def cycle_paths_equiv (c d : Cycles)
  : Equiv (Id Cycles c d) (PermutationIsomorphisms (c .fst) (d .fst))
  ≔ compose_equiv (Id Cycles c d) (Id Permutations (c .fst) (d .fst)) (PermutationIsomorphisms (c .fst) (d .fst))
      (subtype_path_equiv Permutations cyclic_permutation (p ↦ cyclic_prop (p .fst .fst) (p .snd)) c d)
      (permutation_paths_equiv (c .fst) (d .fst))

def cycle_path_evaluate (c d : Cycles) (p : Id Cycles c d) (x : c .fst .fst .fst) : d .fst .fst .fst
  ≔ cycle_paths_equiv c d .map p .fst .map x

def cycle_path_evaluate_transport (c d : Cycles) (p : Id Cycles c d) (x : c .fst .fst .fst)
  : Id (d .fst .fst .fst) (cycle_path_evaluate c d p x) (p .fst .fst .fst .trr x)
  ≔ refl (p .fst .fst .fst .trr x)

def PointedCyclePaths (c d : Cycles) (x : c .fst .fst .fst) (y : d .fst .fst .fst) : Type
  ≔ Σ (Id Cycles c d) (p ↦ Id (d .fst .fst .fst) (cycle_path_evaluate c d p x) y)

def pointed_isomorphism_reorder (c d : Cycles) (x : c .fst .fst .fst) (y : d .fst .fst .fst)
  : Equiv (Σ (PermutationIsomorphisms (c .fst) (d .fst)) (h ↦ Id (d .fst .fst .fst) (h .fst .map x) y))
      (PointedCycleEquivalences (c .fst .fst .fst) (d .fst .fst .fst) (c .fst .snd) (d .fst .snd) x y)
  ≔ quasi_inverse_equiv
      (Σ (PermutationIsomorphisms (c .fst) (d .fst)) (h ↦ Id (d .fst .fst .fst) (h .fst .map x) y))
      (PointedCycleEquivalences (c .fst .fst .fst) (d .fst .fst .fst) (c .fst .snd) (d .fst .snd) x y)
      (h ↦ (((h .fst .fst .map, h .fst .snd), h .snd), h .fst .fst .equiv))
      (h ↦ (((h .fst .fst .fst, h .snd), h .fst .fst .snd), h .fst .snd))
      (h ↦ refl h) (h ↦ refl h)

def pointed_cycle_paths_equiv (c d : Cycles) (x : c .fst .fst .fst) (y : d .fst .fst .fst)
  : Equiv (PointedCyclePaths c d x y)
      (PointedCycleEquivalences (c .fst .fst .fst) (d .fst .fst .fst) (c .fst .snd) (d .fst .snd) x y)
  ≔ compose_equiv (PointedCyclePaths c d x y)
      (Σ (PermutationIsomorphisms (c .fst) (d .fst)) (h ↦ Id (d .fst .fst .fst) (h .fst .map x) y))
      (PointedCycleEquivalences (c .fst .fst .fst) (d .fst .fst .fst) (c .fst .snd) (d .fst .snd) x y)
      (propositional_subtype_equiv (Id Cycles c d) (PermutationIsomorphisms (c .fst) (d .fst))
        (p ↦ Id (d .fst .fst .fst) (cycle_path_evaluate c d p x) y)
        (h ↦ Id (d .fst .fst .fst) (h .fst .map x) y)
        (p ↦ d .fst .fst .snd (cycle_path_evaluate c d p x) y)
        (h ↦ d .fst .fst .snd (h .fst .map x) y)
        (cycle_paths_equiv c d) (p ↦ identity_equiv (Id (d .fst .fst .fst) (cycle_path_evaluate c d p x) y)))
      (pointed_isomorphism_reorder c d x y)
