export "241-cycle-generators"

{` rem:thenonuniquenessofgeneratorsofmodulararithmetic1 on the book's literal
   standard m-cycle (bn m, s): transfer along (Fin m, s) = (Z/m, s). `}
def cycle_generators_family (p : Permutations) : Type ≔ CycleGenerators (p .fst .fst) (p .snd)

def fin_cycle_generators_equiv (n : Nat)
  : Equiv (CycleGenerators (Fin (suc. n)) (finite_fin_successor n)) (CoprimeResidues (suc. n))
  ≔ compose_equiv (CycleGenerators (Fin (suc. n)) (finite_fin_successor n))
      (CycleGenerators (Remainder (suc. n)) (modular_successor_equiv n)) (CoprimeResidues (suc. n))
      (id_to_equiv (CycleGenerators (Fin (suc. n)) (finite_fin_successor n))
        (CycleGenerators (Remainder (suc. n)) (modular_successor_equiv n))
        (refl cycle_generators_family (refl ((c ↦ c .fst) : Cycles → Permutations) (fin_remainder_cycle_path n))))
      (standard_cycle_generators_equiv n)

{` Cycle structures on a type: permutations making it a cycle. `}
def CycleStructures (X : Type) : Type ≔ Σ (Equiv X X) (Cyclic X)

{` A cycle on a set with suc j elements has period subgroup (suc j)Z. `}
def finite_cycle_periods_multiples (c : Cycles) (j : Nat) (h : Mere (Id Type (c .fst .fst .fst) (Fin (suc. j))))
  : Id (Subtypes Int) (CyclePeriods c) (Multiples (suc. j))
  ≔ let X ≔ c .fst .fst .fst in
    let finite : IsFinite X ≔ trunc_map native_truncation (Id Type X (Fin (suc. j))) (Σ Nat (m ↦ Id Type X (Fin m)))
      (p ↦ (suc. j, p)) h in
    let mn ≔ finite_cycle_minimum c finite in
    let card : Id Nat (cardinality X finite) (suc. j)
      ≔ mere_rec (Id Type X (Fin (suc. j))) (Id Nat (cardinality X finite) (suc. j)) (nat_set (cardinality X finite) (suc. j))
          (p ↦ cardinality_from_path X finite (suc. j) p) h in
    let same : Id Nat (mn .fst) j
      ≔ refl nat_pred (concat Nat (suc. (mn .fst)) (cardinality X finite) (suc. j)
          (inverse Nat (cardinality X finite) (suc. (mn .fst)) (finite_cycle_cardinality c finite)) card) in
    concat (Subtypes Int) (CyclePeriods c) (Multiples (suc. (mn .fst))) (Multiples (suc. j))
      (least_cycle_periods_multiples c (mn .fst) (mn .snd))
      (refl ((k ↦ Multiples (suc. k)) : Nat → Subtypes Int) same)

def cycles_period_inclusion (c d : Cycles) (H : Subtypes Int)
  (p : Id (Subtypes Int) (CyclePeriods c) H) (q : Id (Subtypes Int) (CyclePeriods d) H)
  : PeriodInclusion (c .fst .fst .fst) (d .fst .fst .fst) (c .fst .snd) (d .fst .snd)
  ≔ z r ↦ transport (Subtypes Int) (K ↦ K z .fst) H (CyclePeriods d) (inverse (Subtypes Int) (CyclePeriods d) H q)
      (transport (Subtypes Int) (K ↦ K z .fst) (CyclePeriods c) H p r)

{` Automorphisms of Fin(j+1) fixing 0 = inr star. `}
def FixedAutomorphisms (j : Nat) : Type
  ≔ Σ (Equiv (Fin (suc. j)) (Fin (suc. j))) (e ↦ Id (Fin (suc. j)) (e .map (inr. star.)) (inr. star.))

def conjugate_equiv (X : Type) (s e : Equiv X X) : Equiv X X
  ≔ compose_equiv X X X (canonical_inverse_equiv X X e) (compose_equiv X X X s e)

def conjugate_step (X : Type) (s e : Equiv X X) (x : X)
  : Id X (e .map (s .map x)) (conjugate_equiv X s e .map (e .map x))
  ≔ refl ((y ↦ e .map (s .map y)) : X → X)
      (inverse X (equiv_inverse_map X X e (e .map x)) x (equiv_retraction X X e x))

def fin_structure_cycle (j : Nat) (u : CycleStructures (Fin (suc. j))) : Cycles
  ≔ (((Fin (suc. j), fin_set (suc. j)), u .fst), u .snd)

def fin_structure_periods (j : Nat) (u : CycleStructures (Fin (suc. j)))
  : Id (Subtypes Int) (CyclePeriods (fin_structure_cycle j u)) (Multiples (suc. j))
  ≔ finite_cycle_periods_multiples (fin_structure_cycle j u) j
      (mere (Id Type (Fin (suc. j)) (Fin (suc. j))) (refl (Fin (suc. j))))

def fin_standard_periods (j : Nat) : Id (Subtypes Int) (CyclePeriods (finite_fin_cycle j)) (Multiples (suc. j))
  ≔ finite_cycle_periods_multiples (finite_fin_cycle j) j
      (mere (Id Type (Fin (suc. j)) (Fin (suc. j))) (refl (Fin (suc. j))))

def fin_structure_pointed (j : Nat) (u : CycleStructures (Fin (suc. j)))
  : BookIsContr (PointedCycleEquivalences (Fin (suc. j)) (Fin (suc. j)) (finite_fin_successor j) (u .fst) (inr. star.) (inr. star.))
  ≔ pointed_cycle_equivalences_contractible (Fin (suc. j)) (Fin (suc. j)) (fin_set (suc. j)) (fin_set (suc. j))
      (finite_fin_successor j) (u .fst) (finite_fin_successor_cyclic j) (u .snd)
      (cycles_period_inclusion (finite_fin_cycle j) (fin_structure_cycle j u) (Multiples (suc. j))
        (fin_standard_periods j) (fin_structure_periods j u))
      (cycles_period_inclusion (fin_structure_cycle j u) (finite_fin_cycle j) (Multiples (suc. j))
        (fin_structure_periods j u) (fin_standard_periods j))
      (inr. star.) (inr. star.)

def pointed_cycle_equivalence_fixed (j : Nat) (t : Equiv (Fin (suc. j)) (Fin (suc. j)))
  (w : PointedCycleEquivalences (Fin (suc. j)) (Fin (suc. j)) (finite_fin_successor j) t (inr. star.) (inr. star.))
  : FixedAutomorphisms j
  ≔ ((w .fst .fst .fst, w .snd), w .fst .snd)

{` A cycle structure t on Fin(j+1) corresponds to the unique pointed
   isomorphism (Fin(j+1), s, 0) → (Fin(j+1), t, 0); conversely t = e s e⁻¹. `}
def cycle_structures_fixed_equiv (j : Nat) : Equiv (CycleStructures (Fin (suc. j))) (FixedAutomorphisms j)
  ≔ let F ≔ Fin (suc. j) in let s ≔ finite_fin_successor j in
    let to ≔ ((u ↦ pointed_cycle_equivalence_fixed j (u .fst) (fin_structure_pointed j u .center))
      : CycleStructures F → FixedAutomorphisms j) in
    let from ≔ ((v ↦ (conjugate_equiv F s (v .fst),
        cyclic_transfer F F s (conjugate_equiv F s (v .fst)) (v .fst) (conjugate_step F s (v .fst))
          (finite_fin_successor_cyclic j)))
      : FixedAutomorphisms j → CycleStructures F) in
    quasi_inverse_equiv (CycleStructures F) (FixedAutomorphisms j) to from
      (u ↦ let w ≔ fin_structure_pointed j u .center in
        let e ≔ to u .fst in
        subtype_equal (Equiv F F) (Cyclic F) (cyclic_prop F) (from (to u)) u
          (equiv_path F F (conjugate_equiv F s e) (u .fst)
            (funext F (_ ↦ F) (conjugate_equiv F s e .map) (u .fst .map)
              (x ↦ concat F (e .map (s .map (equiv_inverse_map F F e x)))
                (u .fst .map (e .map (equiv_inverse_map F F e x))) (u .fst .map x)
                (w .fst .fst .snd (equiv_inverse_map F F e x))
                (refl (u .fst .map) (equiv_counit F F e x))))))
      (v ↦ let t ≔ conjugate_equiv F s (v .fst) in
        let contr ≔ fin_structure_pointed j (from v) in
        let wv : PointedCycleEquivalences F F s t (inr. star.) (inr. star.)
          ≔ (((v .fst .map, conjugate_step F s (v .fst)), v .snd), v .fst .equiv) in
        refl ((w ↦ pointed_cycle_equivalence_fixed j t w)
            : PointedCycleEquivalences F F s t (inr. star.) (inr. star.) → FixedAutomorphisms j)
          (contr .contract wv))

{` Automorphisms fixing the added point are automorphisms of Fin j. `}
def fixed_automorphisms_restriction (j : Nat) : Equiv (FixedAutomorphisms j) (Equiv (Fin j) (Fin j))
  ≔ let A ≔ Fin j in let F ≔ Fin (suc. j) in
    let P ≔ Product F (Equiv A A) in
    let E ≔ permutation_option_equiv A (fin_decidable_equality j) in
    let e1 ≔ subtype_induced_equiv (Equiv F F) P E
      (e ↦ Id F (e .map (inr. star.)) (inr. star.)) (u ↦ Id F (u .fst) (inr. star.))
      (e ↦ fin_set (suc. j) (e .map (inr. star.)) (inr. star.)) (u ↦ fin_set (suc. j) (u .fst) (inr. star.))
      (e p ↦ p)
      (u p ↦ concat F (equiv_inverse_map (Equiv F F) P E u .map (inr. star.)) (u .fst) (inr. star.)
        (equiv_counit (Equiv F F) P E u .fst) p) in
    let e2 ≔ quasi_inverse_equiv (Σ P (u ↦ Id F (u .fst) (inr. star.))) (Equiv A A)
      (v ↦ v .fst .snd) (a ↦ ((inr. star., a), refl (inr. star. : F)))
      (v ↦ subtype_equal P (u ↦ Id F (u .fst) (inr. star.)) (u ↦ fin_set (suc. j) (u .fst) (inr. star.))
        ((inr. star., v .fst .snd), refl (inr. star. : F)) v
        (inverse F (v .fst .fst) (inr. star.) (v .snd), refl (v .fst .snd)))
      (a ↦ refl a) in
    compose_equiv (FixedAutomorphisms j) (Σ P (u ↦ Id F (u .fst) (inr. star.))) (Equiv A A) e1 e2

{` The cyclic orderings of a set with j+1 elements: there are j! of them. `}
def cycle_structures_fin_count (j : Nat) : Equiv (CycleStructures (Fin (suc. j))) (Fin (factorial j))
  ≔ compose_equiv (CycleStructures (Fin (suc. j))) (Equiv (Fin j) (Fin j)) (Fin (factorial j))
      (compose_equiv (CycleStructures (Fin (suc. j))) (FixedAutomorphisms j) (Equiv (Fin j) (Fin j))
        (cycle_structures_fixed_equiv j) (fixed_automorphisms_restriction j))
      (fin_automorphisms_equiv j)

def cycle_structures_finite (X : Type) (j : Nat) (h : Mere (Id Type X (Fin (suc. j)))) : IsFinite (CycleStructures X)
  ≔ trunc_map native_truncation (Id Type X (Fin (suc. j))) (Σ Nat (m ↦ Id Type (CycleStructures X) (Fin m)))
      (p ↦ (factorial j, concat Type (CycleStructures X) (CycleStructures (Fin (suc. j))) (Fin (factorial j))
        (refl CycleStructures p)
        (ua (CycleStructures (Fin (suc. j))) (Fin (factorial j)) (cycle_structures_fin_count j)))) h

def cycle_structures_cardinality (X : Type) (j : Nat) (h : Mere (Id Type X (Fin (suc. j))))
  (hf : IsFinite (CycleStructures X)) : Id Nat (cardinality (CycleStructures X) hf) (factorial j)
  ≔ mere_rec (Id Type X (Fin (suc. j))) (Id Nat (cardinality (CycleStructures X) hf) (factorial j))
      (nat_set (cardinality (CycleStructures X) hf) (factorial j))
      (p ↦ cardinality_from_path (CycleStructures X) hf (factorial j)
        (concat Type (CycleStructures X) (CycleStructures (Fin (suc. j))) (Fin (factorial j))
          (refl CycleStructures p)
          (ua (CycleStructures (Fin (suc. j))) (Fin (factorial j)) (cycle_structures_fin_count j)))) h
