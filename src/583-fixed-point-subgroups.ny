export "582-pointed-finite-sets"

{` Chapter 5, xca:n-is-ptd-n+1 and exa:fix1subSGn. `}

def PointedFiniteSetsAt (n : Nat) : Type ≔ Σ (BookFiniteSetsAt n) (S ↦ S .fst .fst)

def finite_sets_at_finite (n : Nat) (S : BookFiniteSetsAt n) : IsFinite (S .fst .fst)
  ≔ mere_rec (Id SetTypes (Fin n, fin_set n) (S .fst)) (IsFinite (S .fst .fst)) (isfinite_prop (S .fst .fst))
      (p ↦ mere (Σ Nat (k ↦ Id Type (S .fst .fst) (Fin k))) (n, inverse Type (Fin n) (S .fst .fst) (p .fst)))
      (S .snd)

def without_set (S : SetTypes) (s : S .fst) : SetTypes
  ≔ (Without (S .fst) s, sigma_set (S .fst) (x ↦ Id (S .fst) x s → Empty) (S .snd)
       (x ↦ prop_is_set (Id (S .fst) x s → Empty) (negation_prop (Id (S .fst) x s))))

{` (A) ↦ (A + 1, inr ★) and (S, s) ↦ S ∖ {s}. `}
def finite_plus_point (n : Nat) (A : BookFiniteSetsAt n) : PointedFiniteSetsAt (suc. n)
  ≔ ((set_plus_one (A .fst),
      mere_rec (Id SetTypes (Fin n, fin_set n) (A .fst)) (Mere (Id SetTypes (Fin (suc. n), fin_set (suc. n)) (set_plus_one (A .fst))))
        (mere_isprop (Id SetTypes (Fin (suc. n), fin_set (suc. n)) (set_plus_one (A .fst))))
        (p ↦ mere (Id SetTypes (Fin (suc. n), fin_set (suc. n)) (set_plus_one (A .fst)))
          (map_path SetTypes SetTypes set_plus_one (Fin n, fin_set n) (A .fst) p))
        (A .snd)),
     inr. star.)

def finite_remove_point_equiv (n : Nat) (S : SetTypes) (s : S .fst) (p : Id SetTypes (Fin (suc. n), fin_set (suc. n)) S)
  : Equiv (Fin n) (Without (S .fst) s)
  ≔ let e ≔ transport_equiv (Fin (suc. n)) (S .fst) (p .fst) in
    let ei ≔ canonical_inverse_equiv (Fin (suc. n)) (S .fst) e in
    compose_equiv (Fin n) (Without (Fin (suc. n)) (ei .map s)) (Without (S .fst) s)
      (canonical_inverse_equiv (Without (Fin (suc. n)) (ei .map s)) (Fin n) (without_fin_equiv n (ei .map s)))
      (canonical_inverse_equiv (Without (S .fst) s) (Without (Fin (suc. n)) (ei .map s)) (without_equiv (S .fst) (Fin (suc. n)) ei s))

def finite_remove_point (n : Nat) (u : PointedFiniteSetsAt (suc. n)) : BookFiniteSetsAt n
  ≔ (without_set (u .fst .fst) (u .snd),
     mere_rec (Id SetTypes (Fin (suc. n), fin_set (suc. n)) (u .fst .fst))
       (Mere (Id SetTypes (Fin n, fin_set n) (without_set (u .fst .fst) (u .snd))))
       (mere_isprop (Id SetTypes (Fin n, fin_set n) (without_set (u .fst .fst) (u .snd))))
       (p ↦ mere (Id SetTypes (Fin n, fin_set n) (without_set (u .fst .fst) (u .snd)))
         (set_types_path (Fin n, fin_set n) (without_set (u .fst .fst) (u .snd))
           (finite_remove_point_equiv n (u .fst .fst) (u .snd) p)))
       (u .fst .snd))

def finite_sets_path (n : Nat) (A B : BookFiniteSetsAt n) (e : Equiv (A .fst .fst) (B .fst .fst)) : Id (BookFiniteSetsAt n) A B
  ≔ subtype_equal SetTypes (S ↦ Mere (Id SetTypes (Fin n, fin_set n) S)) (S ↦ mere_isprop (Id SetTypes (Fin n, fin_set n) S))
      A B (set_types_path (A .fst) (B .fst) e)

def finite_remove_plus (n : Nat) (A : BookFiniteSetsAt n)
  : Id (BookFiniteSetsAt n) (finite_remove_point n (finite_plus_point n A)) A
  ≔ finite_sets_path n (finite_remove_point n (finite_plus_point n A)) A (without_last_equiv (A .fst .fst))

def finite_plus_remove (n : Nat) (u : PointedFiniteSetsAt (suc. n))
  : Id (PointedFiniteSetsAt (suc. n)) (finite_plus_point n (finite_remove_point n u)) u
  ≔ let S ≔ u .fst in
    let s ≔ u .snd in
    let dS ≔ finite_decidable_equality (S .fst .fst) (finite_sets_at_finite (suc. n) S) in
    let e ≔ canonical_inverse_equiv (S .fst .fst) (Sum (Without (S .fst .fst) s) Unit) (point_split_equiv (S .fst .fst) dS s) in
    (finite_sets_path (suc. n) (finite_plus_point n (finite_remove_point n u) .fst) S e,
     pathover_of_eq (BookFiniteSetsAt (suc. n)) (T ↦ T .fst .fst) (finite_plus_point n (finite_remove_point n u) .fst) S
       (finite_sets_path (suc. n) (finite_plus_point n (finite_remove_point n u) .fst) S e) (inr. star.) s
       (refl s))

{` xca:n-is-ptd-n+1. The type of n-element sets is equivalent to the type of
   pointed (n+1)-element sets. `}
def finite_pointed_equiv (n : Nat) : Equiv (BookFiniteSetsAt n) (PointedFiniteSetsAt (suc. n))
  ≔ quasi_inverse_equiv (BookFiniteSetsAt n) (PointedFiniteSetsAt (suc. n)) (finite_plus_point n) (finite_remove_point n)
      (finite_remove_plus n) (finite_plus_remove n)

{` exa:fix1subSGn. The Σ_{m+1}-set X(A, !) ≔ A is transitive: its action type is
   the type of pointed (m+1)-element sets, equivalent to the connected type of
   m-element sets. Any k : Fin (m+1) gives (X, k) : Sub(Σ_{m+1}). `}
def fixed_point_gset_transitive (m : Nat) : IsTransitive (symmetric_group (suc. m)) (standard_symmetric_gset (suc. m))
  ≔ connected_action_type_transitive (symmetric_group (suc. m)) (standard_symmetric_gset (suc. m))
      (connected_equiv (BookFiniteSetsAt m) (PointedFiniteSetsAt (suc. m)) (finite_pointed_equiv m)
        .map (bg_connected (symmetric_group m)))

def fixed_point_subgroup (m : Nat) (k : Fin (suc. m)) : Subgroups (symmetric_group (suc. m))
  ≔ (standard_symmetric_gset (suc. m), k, fixed_point_gset_transitive m)

{` The symmetries picked out by (X, k) are the π with π · k = k (lem:E-preserves-symms). `}
def fixed_point_subgroup_symmetries (m : Nat) (k : Fin (suc. m)) (g : USym (symmetric_group (suc. m)))
  : Product
      (Id (Fin (suc. m)) (gset_usym_act (symmetric_group (suc. m)) (standard_symmetric_gset (suc. m)) g k) k
        → SymmetryPickedOut (symmetric_group (suc. m)) (subgroup_to_mono (symmetric_group (suc. m)) (fixed_point_subgroup m k)) g)
      (SymmetryPickedOut (symmetric_group (suc. m)) (subgroup_to_mono (symmetric_group (suc. m)) (fixed_point_subgroup m k)) g
        → Id (Fin (suc. m)) (gset_usym_act (symmetric_group (suc. m)) (standard_symmetric_gset (suc. m)) g k) k)
  ≔ mono_preserves_symmetries (symmetric_group (suc. m)) (fixed_point_subgroup m k)
      (subgroup_to_mono (symmetric_group (suc. m)) (fixed_point_subgroup m k))
      (refl (subgroup_to_mono (symmetric_group (suc. m)) (fixed_point_subgroup m k))) g

{` The underlying group of (X, k) is (identified with) Σ_m, via xca:n-is-ptd-n+1
   and Fin (m+1) ∖ {k} ≃ Fin m. `}
def fixed_point_subgroup_pointed_equiv (m : Nat) (k : Fin (suc. m))
  : BookPointedEquiv (BG (subgroup_group (symmetric_group (suc. m)) (fixed_point_subgroup m k))) (BG (symmetric_group m))
  ≔ ((finite_remove_point m,
      finite_sets_path m (shape (symmetric_group m))
        (finite_remove_point m (shape (symmetric_group (suc. m)), k))
        (canonical_inverse_equiv (Without (Fin (suc. m)) k) (Fin m) (without_fin_equiv m k))),
     book_equivalence (PointedFiniteSetsAt (suc. m)) (BookFiniteSetsAt m)
       (quasi_inverse_equiv (PointedFiniteSetsAt (suc. m)) (BookFiniteSetsAt m) (finite_remove_point m) (finite_plus_point m)
         (finite_plus_remove m) (finite_remove_plus m)) .equiv)

def fixed_point_subgroup_group_path (m : Nat) (k : Fin (suc. m))
  : Id Group (subgroup_group (symmetric_group (suc. m)) (fixed_point_subgroup m k)) (symmetric_group m)
  ≔ group_path_from_pointed_equiv (subgroup_group (symmetric_group (suc. m)) (fixed_point_subgroup m k)) (symmetric_group m)
      (fixed_point_subgroup_pointed_equiv m k)
