export "418-cyclic-group-images"

{` Chapter 4, xca:CG2isSG2, xca:RmloopCGm and the footnote of
   ex:cyclicgroups on C_2 (group.tex 536-540, 653-663). `}

{` A cyclic permutation of Fin 2 moves 0, hence is the swap. `}
def iterate_fixed (A : Type) (f : A → A) (x : A) (p : Id A (f x) x) (n : Nat) : Id A (iterate A f n x) x
  ≔ match n [
  | zero. ↦ refl x
  | suc. n ↦ concat A (f (iterate A f n x)) (f x) x (refl f (iterate_fixed A f x p n)) p ]

def equiv_inverse_fixed (A : Type) (e : Equiv A A) (x : A) (p : Id A (e .map x) x)
  : Id A (equiv_inverse_map A A e x) x
  ≔ concat A (equiv_inverse_map A A e x) (equiv_inverse_map A A e (e .map x)) x
      (refl (equiv_inverse_map A A e) (inverse A (e .map x) x p)) (equiv_retraction A A e x)

def permutation_power_fixed (A : Type) (e : Equiv A A) (x : A) (p : Id A (e .map x) x) (z : Int)
  : Id A (permutation_power A e z x) x
  ≔ match z [
  | pos. n ↦ iterate_fixed A (e .map) x p n
  | neg. n ↦ iterate_fixed A (equiv_inverse_map A A e) x (equiv_inverse_fixed A e x p) (suc. n) ]

def fin2_cyclic_moves (t : Equiv (Fin two) (Fin two)) (c : Cyclic (Fin two) t)
  (p : Id (Fin two) (t .map fin2_zero) fin2_zero) : Empty
  ≔ mere_rec (OrbitWitness (Fin two) t fin2_zero fin2_one) Empty empty_prop
      (w ↦ fin2_zero_ne_one (inverse (Fin two) fin2_one fin2_zero
        (concat (Fin two) fin2_one (permutation_power (Fin two) t (w .fst) fin2_zero) fin2_zero
          (w .snd) (permutation_power_fixed (Fin two) t fin2_zero p (w .fst)))))
      (c .snd fin2_zero fin2_one)

def fin2_cyclic_value (t : Equiv (Fin two) (Fin two)) (c : Cyclic (Fin two) t)
  : Id (Fin two) (t .map fin2_zero) fin2_one
  ≔ fin2_distinct_other fin2_zero (t .map fin2_zero)
      (p ↦ fin2_cyclic_moves t c (inverse (Fin two) fin2_zero (t .map fin2_zero) p))

def fin2_cyclic_is_swap (t : Equiv (Fin two) (Fin two)) (c : Cyclic (Fin two) t)
  : Id (Equiv (Fin two) (Fin two)) fin2_swap_equiv t
  ≔ concat (Equiv (Fin two) (Fin two)) fin2_swap_equiv (fin2_automorphism (t .map fin2_zero)) t
      (refl fin2_automorphism (inverse (Fin two) (t .map fin2_zero) fin2_one (fin2_cyclic_value t c)))
      (fin2_automorphism_eta t)

{` xca:CG2isSG2. The cycle structures on 2 form a contractible set; hence
   the set truncation of R_2⁻¹(2) is contractible (power_fiber_cycle_structures). `}
def cycle_structures_two_contractible : BookIsContr (CycleStructuresOn (suc. zero.) (shape (symmetric_group two)))
  ≔ let c0 ≔ finite_fin_cycle (suc. zero.) in
    let P ≔ ((t ↦ Mere (Id Permutations (c0 .fst) (standard_set two, t))) : Equiv (Fin two) (Fin two) → Type) in
    ((finite_fin_successor (suc. zero.), mere (Id Permutations (c0 .fst) (c0 .fst)) (refl (c0 .fst))),
     y ↦ subtype_equal (Equiv (Fin two) (Fin two)) P (t ↦ mere_isprop (Id Permutations (c0 .fst) (standard_set two, t)))
       (finite_fin_successor (suc. zero.), mere (Id Permutations (c0 .fst) (c0 .fst)) (refl (c0 .fst))) y
       (concat (Equiv (Fin two) (Fin two)) (finite_fin_successor (suc. zero.)) fin2_swap_equiv (y .fst)
         (inverse (Equiv (Fin two) (Fin two)) fin2_swap_equiv (finite_fin_successor (suc. zero.))
           (fin2_cyclic_is_swap (finite_fin_successor (suc. zero.)) (finite_fin_successor_cyclic (suc. zero.))))
         (fin2_cyclic_is_swap (y .fst) (structure_cyclic (suc. zero.) (standard_set two) (y .fst) (y .snd)))))

def rm_two_fiber_contractible (C : CircleSignature)
  : BookIsContr (SetTrunc (BookFiber (C .carrier) (BookFiniteSetsAt two) (power_finset_map C (suc. zero.))
      (shape (symmetric_group two))))
  ≔ book_contractibility_equiv (CycleStructuresOn (suc. zero.) (shape (symmetric_group two)))
      (SetTrunc (BookFiber (C .carrier) (BookFiniteSetsAt two) (power_finset_map C (suc. zero.)) (shape (symmetric_group two))))
      (canonical_inverse_equiv
        (SetTrunc (BookFiber (C .carrier) (BookFiniteSetsAt two) (power_finset_map C (suc. zero.)) (shape (symmetric_group two))))
        (CycleStructuresOn (suc. zero.) (shape (symmetric_group two)))
        (power_fiber_cycle_structures C (suc. zero.) (shape (symmetric_group two))))
      .map cycle_structures_two_contractible

{` "This reflects that C_2 and Σ_2 can be identified": every 2-element set
   carries exactly one cycle structure, so prj : Cyc_2 → FinSet_2 is an
   equivalence (contractible fibers) and C_2 = Σ_2. `}
def cycle_structures_two_all (X : BookFiniteSetsAt two) : BookIsContr (CycleStructuresOn (suc. zero.) X)
  ≔ mere_rec (Id (BookFiniteSetsAt two) (shape (symmetric_group two)) X) (BookIsContr (CycleStructuresOn (suc. zero.) X))
      (book_iscontr_isprop (CycleStructuresOn (suc. zero.) X))
      (p ↦ transport (BookFiniteSetsAt two) (Y ↦ BookIsContr (CycleStructuresOn (suc. zero.) Y))
        (shape (symmetric_group two)) X p cycle_structures_two_contractible)
      (bg_connected (symmetric_group two) .snd (shape (symmetric_group two)) X)

def cycle_forget_two_equiv : BookIsEquiv (CycFin (suc. zero.)) (BookFiniteSetsAt two) (cycle_forget_set (suc. zero.))
  ≔ X ↦ book_contractibility_equiv (CycleStructuresOn (suc. zero.) X)
      (BookFiber (CycFin (suc. zero.)) (BookFiniteSetsAt two) (cycle_forget_set (suc. zero.)) X)
      (canonical_inverse_equiv (BookFiber (CycFin (suc. zero.)) (BookFiniteSetsAt two) (cycle_forget_set (suc. zero.)) X)
        (CycleStructuresOn (suc. zero.) X) (cycle_forget_fiber_equiv (suc. zero.) X))
      .map (cycle_structures_two_all X)

def cyclic_two_symmetric_two_path : Id Group (cyclic_group_fin (suc. zero.)) (symmetric_group two)
  ≔ group_path_from_pointed_equiv (cyclic_group_fin (suc. zero.)) (symmetric_group two)
      (cycle_forget_pointed (suc. zero.), cycle_forget_two_equiv)

{` ex:cyclicgroups, footnote: C_2 has exactly one nontrivial symmetry f
   (the generator), and f² is the identity. `}
def cyclic_fin_eval (n : Nat) (g : USym (cyclic_group_fin n)) : Fin (suc. n)
  ≔ cycle_path_evaluate (finite_fin_cycle n) (finite_fin_cycle n) (g .fst) (inr. star.)

def cycle_eval_fin_zero (n : Nat) (p : Id Cycles (finite_fin_cycle n) (finite_fin_cycle n)) : Fin (suc. n)
  ≔ cycle_path_evaluate (finite_fin_cycle n) (finite_fin_cycle n) p (inr. star.)

def cyclic_fin_eval_injective (n : Nat) (g h : USym (cyclic_group_fin n))
  (e : Id (Fin (suc. n)) (cyclic_fin_eval n g) (cyclic_fin_eval n h)) : Id (USym (cyclic_group_fin n)) g h
  ≔ equivalence_injective (USym (cyclic_group_fin n)) (Fin (suc. n)) (cyclic_group_fin_usym_equiv n) g h e

def cyclic_fin_eval_mul (n : Nat) (g h : USym (cyclic_group_fin n))
  : Id (Fin (suc. n)) (cyclic_fin_eval n (usym_mul (cyclic_group_fin n) g h))
      (cycle_path_evaluate (finite_fin_cycle n) (finite_fin_cycle n) (g .fst) (cyclic_fin_eval n h))
  ≔ concat (Fin (suc. n)) (cyclic_fin_eval n (usym_mul (cyclic_group_fin n) g h))
      (cycle_path_evaluate (finite_fin_cycle n) (finite_fin_cycle n)
        (concat Cycles (finite_fin_cycle n) (finite_fin_cycle n) (finite_fin_cycle n) (h .fst) (g .fst)) (inr. star.))
      (cycle_path_evaluate (finite_fin_cycle n) (finite_fin_cycle n) (g .fst) (cyclic_fin_eval n h))
      (refl (cycle_eval_fin_zero n)
        (map_path_concat (CycFin n) Cycles (u ↦ u .fst) (cycfin_point n) (cycfin_point n) (cycfin_point n) h g))
      (cycle_path_evaluation_concat (finite_fin_cycle n) (finite_fin_cycle n) (finite_fin_cycle n)
        (h .fst) (g .fst) (inr. star.))


def cyclic_two_generator_value
  : Id (Fin two) (cyclic_fin_eval (suc. zero.) (cyclic_fin_generator (suc. zero.))) fin2_one
  ≔ concat (Fin two) (cyclic_fin_eval (suc. zero.) (cyclic_fin_generator (suc. zero.)))
      (finite_fin_successor (suc. zero.) .map fin2_zero) fin2_one
      (cycle_generating_loop_action (finite_fin_cycle (suc. zero.)) fin2_zero)
      (fin2_cyclic_value (finite_fin_successor (suc. zero.)) (finite_fin_successor_cyclic (suc. zero.)))

def cyclic_two_unit_value
  : Id (Fin two) (cyclic_fin_eval (suc. zero.) (usym_unit (cyclic_group_fin (suc. zero.)))) fin2_zero
  ≔ finite_cycle_loop_refl (suc. zero.)

def cyclic_two_generator_nontrivial
  (p : Id (USym (cyclic_group_fin (suc. zero.))) (cyclic_fin_generator (suc. zero.)) (usym_unit (cyclic_group_fin (suc. zero.))))
  : Empty
  ≔ fin2_zero_ne_one
      (calc
        fin2_zero = cyclic_fin_eval (suc. zero.) (usym_unit (cyclic_group_fin (suc. zero.)))
          by inverse (Fin two) (cyclic_fin_eval (suc. zero.) (usym_unit (cyclic_group_fin (suc. zero.)))) fin2_zero
            cyclic_two_unit_value
        = cyclic_fin_eval (suc. zero.) (cyclic_fin_generator (suc. zero.))
          by refl (cyclic_fin_eval (suc. zero.))
            (inverse (USym (cyclic_group_fin (suc. zero.))) (cyclic_fin_generator (suc. zero.))
              (usym_unit (cyclic_group_fin (suc. zero.))) p)
        = fin2_one by cyclic_two_generator_value ∎)

def cyclic_two_generator_squared
  : Id (USym (cyclic_group_fin (suc. zero.)))
      (usym_mul (cyclic_group_fin (suc. zero.)) (cyclic_fin_generator (suc. zero.)) (cyclic_fin_generator (suc. zero.)))
      (usym_unit (cyclic_group_fin (suc. zero.)))
  ≔ let G ≔ cyclic_group_fin (suc. zero.) in let g ≔ cyclic_fin_generator (suc. zero.) in
    let s ≔ finite_fin_successor (suc. zero.) in
    let ev ≔ ((x ↦ cycle_path_evaluate (finite_fin_cycle (suc. zero.)) (finite_fin_cycle (suc. zero.))
      (cycle_generating_loop (finite_fin_cycle (suc. zero.))) x) : Fin two → Fin two) in
    cyclic_fin_eval_injective (suc. zero.) (usym_mul G g g) (usym_unit G)
      (calc
        cyclic_fin_eval (suc. zero.) (usym_mul G g g) = ev (cyclic_fin_eval (suc. zero.) g)
          by cyclic_fin_eval_mul (suc. zero.) g g
        = s .map (cyclic_fin_eval (suc. zero.) g)
          by cycle_generating_loop_action (finite_fin_cycle (suc. zero.)) (cyclic_fin_eval (suc. zero.) g)
        = s .map fin2_one by refl (s .map) cyclic_two_generator_value
        = fin2_swap_equiv .map fin2_one
          by refl ((e ↦ e .map fin2_one) : Equiv (Fin two) (Fin two) → Fin two)
            (inverse (Equiv (Fin two) (Fin two)) fin2_swap_equiv s
              (fin2_cyclic_is_swap s (finite_fin_successor_cyclic (suc. zero.))))
        = fin2_zero by refl fin2_zero
        = cyclic_fin_eval (suc. zero.) (usym_unit G)
          by inverse (Fin two) (cyclic_fin_eval (suc. zero.) (usym_unit G)) fin2_zero cyclic_two_unit_value ∎)

def cyclic_two_cases_at (f : USym (cyclic_group_fin (suc. zero.))) (b : Fin two)
  : Id (Fin two) (cyclic_fin_eval (suc. zero.) f) b
    → Sum (Id (USym (cyclic_group_fin (suc. zero.))) f (usym_unit (cyclic_group_fin (suc. zero.))))
        (Id (USym (cyclic_group_fin (suc. zero.))) f (cyclic_fin_generator (suc. zero.)))
  ≔ match b [
  | inr. u ↦ e ↦ inl. (cyclic_fin_eval_injective (suc. zero.) f (usym_unit (cyclic_group_fin (suc. zero.)))
      (concat (Fin two) (cyclic_fin_eval (suc. zero.) f) (inr. u) (cyclic_fin_eval (suc. zero.) (usym_unit (cyclic_group_fin (suc. zero.))))
        e (concat (Fin two) (inr. u) fin2_zero (cyclic_fin_eval (suc. zero.) (usym_unit (cyclic_group_fin (suc. zero.))))
          (fin2_inr_path u star.)
          (inverse (Fin two) (cyclic_fin_eval (suc. zero.) (usym_unit (cyclic_group_fin (suc. zero.)))) fin2_zero
            cyclic_two_unit_value))))
  | inl. (inr. u) ↦ e ↦ inr. (cyclic_fin_eval_injective (suc. zero.) f (cyclic_fin_generator (suc. zero.))
      (concat (Fin two) (cyclic_fin_eval (suc. zero.) f) (inl. (inr. u)) (cyclic_fin_eval (suc. zero.) (cyclic_fin_generator (suc. zero.)))
        e (concat (Fin two) (inl. (inr. u)) fin2_one (cyclic_fin_eval (suc. zero.) (cyclic_fin_generator (suc. zero.)))
          (fin2_inl_path u star.)
          (inverse (Fin two) (cyclic_fin_eval (suc. zero.) (cyclic_fin_generator (suc. zero.))) fin2_one
            cyclic_two_generator_value))))
  | inl. (inl. v) ↦ match v [] ]

def cyclic_two_cases (f : USym (cyclic_group_fin (suc. zero.)))
  : Sum (Id (USym (cyclic_group_fin (suc. zero.))) f (usym_unit (cyclic_group_fin (suc. zero.))))
      (Id (USym (cyclic_group_fin (suc. zero.))) f (cyclic_fin_generator (suc. zero.)))
  ≔ cyclic_two_cases_at f (cyclic_fin_eval (suc. zero.) f) (refl (cyclic_fin_eval (suc. zero.) f))

{` xca:RmloopCGm. The symmetries of sh_{C'_m} in BC'_m are the permutations
   of m generated by R_m(loop) = s: USym(C'_m) ≃ Σ(σ : m = m) ‖Σ(k : ℤ) sᵏ = σ‖.
   The equivalence is the composite of transport along C'_m = C_m
   (cyclic_image_path) and σ ↦ Ω(prj)(σ): Ω(prj) is injective (a symmetry of a
   cycle is determined by its underlying permutation) and every symmetry of
   C_m is a power of the generator, which prj sends to s. `}
def SuccessorGenerated (n : Nat) : Type
  ≔ Σ (USym (symmetric_group (suc. n)))
      (σ ↦ Mere (Σ Int (k ↦ Id (USym (symmetric_group (suc. n)))
        (loop_power (BookFiniteSetsAt (suc. n)) (shape (symmetric_group (suc. n))) (finite_successor_symmetry n) k) σ)))

def successor_generated_set (n : Nat) : isSet (SuccessorGenerated n)
  ≔ sigma_set (USym (symmetric_group (suc. n)))
      (σ ↦ Mere (Σ Int (k ↦ Id (USym (symmetric_group (suc. n)))
        (loop_power (BookFiniteSetsAt (suc. n)) (shape (symmetric_group (suc. n))) (finite_successor_symmetry n) k) σ)))
      (usym_set (symmetric_group (suc. n)))
      (σ ↦ prop_is_set (Mere (Σ Int (k ↦ Id (USym (symmetric_group (suc. n)))
          (loop_power (BookFiniteSetsAt (suc. n)) (shape (symmetric_group (suc. n))) (finite_successor_symmetry n) k) σ)))
        (mere_isprop (Σ Int (k ↦ Id (USym (symmetric_group (suc. n)))
          (loop_power (BookFiniteSetsAt (suc. n)) (shape (symmetric_group (suc. n))) (finite_successor_symmetry n) k) σ))))

def forget_hom_power (n : Nat) (z : Int)
  : Id (USym (symmetric_group (suc. n)))
      (usym_hom (cyclic_group_fin n) (symmetric_group (suc. n)) (cyclic_forget_hom n) (cycle_group_power (finite_fin_cycle n) z))
      (loop_power (BookFiniteSetsAt (suc. n)) (shape (symmetric_group (suc. n))) (finite_successor_symmetry n) z)
  ≔ concat (USym (symmetric_group (suc. n)))
      (usym_hom (cyclic_group_fin n) (symmetric_group (suc. n)) (cyclic_forget_hom n) (cycle_group_power (finite_fin_cycle n) z))
      (loop_power (BookFiniteSetsAt (suc. n)) (shape (symmetric_group (suc. n)))
        (usym_hom (cyclic_group_fin n) (symmetric_group (suc. n)) (cyclic_forget_hom n) (cyclic_fin_generator n)) z)
      (loop_power (BookFiniteSetsAt (suc. n)) (shape (symmetric_group (suc. n))) (finite_successor_symmetry n) z)
      (loops_map_power (BG (cyclic_group_fin n)) (BG (symmetric_group (suc. n))) (cycle_forget_pointed n)
        (cyclic_fin_generator n) z)
      (refl ((r ↦ loop_power (BookFiniteSetsAt (suc. n)) (shape (symmetric_group (suc. n))) r z)
          : USym (symmetric_group (suc. n)) → USym (symmetric_group (suc. n)))
        (forget_hom_generator n))

def forget_to_generated (n : Nat) (g : USym (cyclic_group_fin n)) : SuccessorGenerated n
  ≔ let S ≔ USym (symmetric_group (suc. n)) in
    let h ≔ usym_hom (cyclic_group_fin n) (symmetric_group (suc. n)) (cyclic_forget_hom n) in
    let pw ≔ ((k ↦ loop_power (BookFiniteSetsAt (suc. n)) (shape (symmetric_group (suc. n))) (finite_successor_symmetry n) k)
      : Int → S) in
    (h g, mere_rec (Σ Int (z ↦ Id (USym (cyclic_group_fin n)) (cycle_group_power (finite_fin_cycle n) z) g))
      (Mere (Σ Int (k ↦ Id S (pw k) (h g)))) (mere_isprop (Σ Int (k ↦ Id S (pw k) (h g))))
      (w ↦ mere (Σ Int (k ↦ Id S (pw k) (h g)))
        (w .fst, concat S (pw (w .fst)) (h (cycle_group_power (finite_fin_cycle n) (w .fst))) (h g)
          (inverse S (h (cycle_group_power (finite_fin_cycle n) (w .fst))) (pw (w .fst)) (forget_hom_power n (w .fst)))
          (refl h (w .snd))))
      (cycle_group_symmetries_are_powers (finite_fin_cycle n) g))

def forget_ap_injective (n : Nat) (g h : USym (cyclic_group_fin n))
  (e : Id (USym (symmetric_group (suc. n))) (refl (cycle_forget_set n) g) (refl (cycle_forget_set n) h))
  : Id (USym (cyclic_group_fin n)) g h
  ≔ let c0 ≔ finite_fin_cycle n in
    let tr ≔ ((r ↦ r .fst .fst .trr (inr. star.)) : USym (symmetric_group (suc. n)) → Fin (suc. n)) in
    equivalence_injective (USym (cyclic_group_fin n)) (Id Cycles c0 c0)
      (automorphism_group_usym_equiv Cycles cycles_groupoid c0) g h
      (equivalence_injective (Id Cycles c0 c0) (Fin (suc. n))
        (native_equivalence (Id Cycles c0 c0) (Fin (suc. n)) (cycle_automorphisms_evaluation c0 (inr. star.)))
        (g .fst) (h .fst) (refl tr e))

def forget_hom_injective (n : Nat) (g h : USym (cyclic_group_fin n))
  (e : Id (USym (symmetric_group (suc. n)))
    (usym_hom (cyclic_group_fin n) (symmetric_group (suc. n)) (cyclic_forget_hom n) g)
    (usym_hom (cyclic_group_fin n) (symmetric_group (suc. n)) (cyclic_forget_hom n) h))
  : Id (USym (cyclic_group_fin n)) g h
  ≔ let S ≔ USym (symmetric_group (suc. n)) in
    let pt ≔ shape (symmetric_group (suc. n)) in
    forget_ap_injective n g h
      (calc
        refl (cycle_forget_set n) g = usym_hom (cyclic_group_fin n) (symmetric_group (suc. n)) (cyclic_forget_hom n) g
          by inverse S (usym_hom (cyclic_group_fin n) (symmetric_group (suc. n)) (cyclic_forget_hom n) g)
            (refl (cycle_forget_set n) g)
            (loop_conjugate_at_refl (BookFiniteSetsAt (suc. n)) pt (refl (cycle_forget_set n) g))
        = usym_hom (cyclic_group_fin n) (symmetric_group (suc. n)) (cyclic_forget_hom n) h by e
        = refl (cycle_forget_set n) h
          by loop_conjugate_at_refl (BookFiniteSetsAt (suc. n)) pt (refl (cycle_forget_set n) h) ∎)

def book_fiber_prop_of_injective (A B : Type) (hB : isSet B) (f : A → B) (inj : PathReflecting A B f) (b : B)
  : isProp (BookFiber A B f b)
  ≔ u v ↦
    let p ≔ inj (u .fst) (v .fst) (concat B (f (u .fst)) b (f (v .fst)) (inverse B b (f (u .fst)) (u .snd)) (v .snd)) in
    (p, pathover_of_eq A (a ↦ Id B b (f a)) (u .fst) (v .fst) p (u .snd) (v .snd)
      (hB b (f (v .fst)) (transport A (a ↦ Id B b (f a)) (u .fst) (v .fst) p (u .snd)) (v .snd)))

def forget_generated_injective (n : Nat) : PathReflecting (USym (cyclic_group_fin n)) (SuccessorGenerated n) (forget_to_generated n)
  ≔ g h e ↦ forget_hom_injective n g h (refl ((y ↦ y .fst) : SuccessorGenerated n → USym (symmetric_group (suc. n))) e)

def forget_generated_surjective (n : Nat) : Surjective (USym (cyclic_group_fin n)) (SuccessorGenerated n) (forget_to_generated n)
  ≔ y ↦
    let S ≔ USym (symmetric_group (suc. n)) in
    let pw ≔ ((k ↦ loop_power (BookFiniteSetsAt (suc. n)) (shape (symmetric_group (suc. n))) (finite_successor_symmetry n) k)
      : Int → S) in
    let F ≔ BookFiber (USym (cyclic_group_fin n)) (SuccessorGenerated n) (forget_to_generated n) y in
    mere_rec (Σ Int (k ↦ Id S (pw k) (y .fst))) (Mere F) (mere_isprop F)
      (w ↦ mere F (cycle_group_power (finite_fin_cycle n) (w .fst),
        subtype_equal S (σ ↦ Mere (Σ Int (k ↦ Id S (pw k) σ))) (σ ↦ mere_isprop (Σ Int (k ↦ Id S (pw k) σ)))
          y (forget_to_generated n (cycle_group_power (finite_fin_cycle n) (w .fst)))
          (concat S (y .fst) (pw (w .fst))
            (usym_hom (cyclic_group_fin n) (symmetric_group (suc. n)) (cyclic_forget_hom n) (cycle_group_power (finite_fin_cycle n) (w .fst)))
            (inverse S (pw (w .fst)) (y .fst) (w .snd))
            (inverse S (usym_hom (cyclic_group_fin n) (symmetric_group (suc. n)) (cyclic_forget_hom n)
                (cycle_group_power (finite_fin_cycle n) (w .fst))) (pw (w .fst))
              (forget_hom_power n (w .fst))))))
      (y .snd)

def cyclic_generated_equiv (n : Nat) : BookEquiv (USym (cyclic_group_fin n)) (SuccessorGenerated n)
  ≔ embedding_surjection_equiv native_truncation (USym (cyclic_group_fin n)) (SuccessorGenerated n) (forget_to_generated n)
      (book_fiber_prop_of_injective (USym (cyclic_group_fin n)) (SuccessorGenerated n) (successor_generated_set n)
        (forget_to_generated n) (forget_generated_injective n))
      (forget_generated_surjective n)

def cyclic_image_symmetries (C : CircleSignature) (n : Nat)
  : Equiv (USym (cyclic_image_group C n)) (SuccessorGenerated n)
  ≔ compose_equiv (USym (cyclic_image_group C n)) (USym (cyclic_group_fin n)) (SuccessorGenerated n)
      (transport_equiv (USym (cyclic_image_group C n)) (USym (cyclic_group_fin n))
        (refl USym (cyclic_image_path C n)))
      (native_equivalence (USym (cyclic_group_fin n)) (SuccessorGenerated n) (cyclic_generated_equiv n))

{` ex:cyclicgroups, footnote: for m > 2, C_m is new; e.g. C_3 cannot be
   identified with Σ_3, since C_3 has 3 symmetries and Σ_3 has 3! = 6. `}
def cyclic_three_symmetric_three_differ
  (p : Id Group (cyclic_group_fin (suc. (suc. zero.))) (symmetric_group (suc. two))) : Empty
  ≔ let C3 ≔ cyclic_group_fin (suc. (suc. zero.)) in let S3 ≔ symmetric_group (suc. two) in
    nat_encode (suc. (suc. (suc. zero.))) (factorial (suc. two))
      (calc
        (suc. (suc. (suc. zero.)) : Nat) = group_card C3 (cyclic_group_fin_finite (suc. (suc. zero.)))
          by inverse Nat (group_card C3 (cyclic_group_fin_finite (suc. (suc. zero.)))) (suc. (suc. (suc. zero.)))
            (cyclic_group_fin_card (suc. (suc. zero.)))
        = group_card S3 (symmetric_group_finite (suc. two))
          by cardinality_equiv (USym C3) (USym S3) (transport_equiv (USym C3) (USym S3) (refl USym p))
            (cyclic_group_fin_finite (suc. (suc. zero.))) (symmetric_group_finite (suc. two))
        = factorial (suc. two) by symmetric_group_card (suc. two) ∎)
