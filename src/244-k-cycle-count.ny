export "243-k-cycle-supports"

{` The k-cycles with a prescribed support P. `}
def KCycleFiber (A : Type) (j : Nat) (P : Subtypes A) : Type
  ≔ Σ (KCyclePermutations A j) (s ↦ Id (Subtypes A) P (permutation_support A (s .fst)))

def extension_enumeration (A : Type) (hA : isSet A) (j : Nat) (P : Subtypes A) (dP : (x : A) → Decidable (P x .fst))
  (hP : Mere (Id Type (SubtypeCarrier A P) (Fin (suc. (suc. j)))))
  (t : Equiv (SubtypeCarrier A P) (SubtypeCarrier A P)) (ct : Cyclic (SubtypeCarrier A P) t)
  (s0 : SubtypeCarrier A P) : KCycleEnumeration A j (subset_extension A P dP t)
  ≔ let C ≔ SubtypeCarrier A P in let R ≔ Remainder (suc. (suc. j)) in
    let sk ≔ modular_successor_equiv (suc. j) in
    let c : Cycles ≔ (((C, subtype_carrier_set A hA P), t), ct) in
    let H ≔ Multiples (suc. (suc. j)) in
    let w ≔ pointed_cycle_equivalences_contractible R C (remainder_set (suc. (suc. j))) (subtype_carrier_set A hA P) sk t
      (modular_successor_cyclic (suc. j)) ct
      (cycles_period_inclusion (finite_standard_cycle (suc. j)) c H (finite_standard_periods (suc. j))
        (finite_cycle_periods_multiples c (suc. j) hP))
      (cycles_period_inclusion c (finite_standard_cycle (suc. j)) H (finite_cycle_periods_multiples c (suc. j) hP)
        (finite_standard_periods (suc. j)))
      (remainder_at (suc. j) zero. star.) s0 .center in
    let e : Equiv R C ≔ (w .fst .fst .fst, w .snd) in
    let σ ≔ subset_extension A P dP t in
    ((i ↦ e .map i .fst),
     ((i i' p ↦ equivalence_injective R C e i i' (subtype_equal A (x ↦ P x .fst) (x ↦ P x .snd) (e .map i) (e .map i') p)),
      ((i ↦ concat A (σ .map (e .map i .fst)) (t .map (e .map i) .fst) (e .map (modular_successor (suc. j) i) .fst)
          (subset_extension_in A P dP (t .map) (e .map i .fst) (e .map i .snd))
          (refl ((y ↦ y .fst) : C → A)
            (inverse C (e .map (modular_successor (suc. j) i)) (t .map (e .map i)) (w .fst .fst .snd i)))),
       (x no ↦ subset_extension_out A P dP (t .map) x
         (p ↦ no (equiv_inverse_map R C e (x, p))
           (refl ((y ↦ y .fst) : C → A) (inverse C (e .map (equiv_inverse_map R C e (x, p))) (x, p) (equiv_counit R C e (x, p)))))))))

def extension_is_kcycle (A : Type) (hA : isSet A) (j : Nat) (P : Subtypes A) (dP : (x : A) → Decidable (P x .fst))
  (hP : Mere (Id Type (SubtypeCarrier A P) (Fin (suc. (suc. j)))))
  (t : Equiv (SubtypeCarrier A P) (SubtypeCarrier A P)) (ct : Cyclic (SubtypeCarrier A P) t)
  : IsKCycle A j (subset_extension A P dP t)
  ≔ trunc_map native_truncation (SubtypeCarrier A P) (KCycleEnumeration A j (subset_extension A P dP t))
      (extension_enumeration A hA j P dP hP t ct) (ct .fst)

def extension_support_path (A : Type) (hA : isSet A) (j : Nat) (P : Subtypes A) (dP : (x : A) → Decidable (P x .fst))
  (hP : Mere (Id Type (SubtypeCarrier A P) (Fin (suc. (suc. j)))))
  (t : Equiv (SubtypeCarrier A P) (SubtypeCarrier A P)) (ct : Cyclic (SubtypeCarrier A P) t)
  : Id (Subtypes A) P (permutation_support A (subset_extension A P dP t))
  ≔ let C ≔ SubtypeCarrier A P in
    let c : Cycles ≔ (((C, subtype_carrier_set A hA P), t), ct) in
    let σ ≔ subset_extension A P dP t in
    inclusion_antisym A P (permutation_support A σ)
      (x p q ↦ finite_cycle_moves c j hP (x, p)
        (subtype_equal A (y ↦ P y .fst) (y ↦ P y .snd) (t .map (x, p)) (x, p)
          (concat A (t .map (x, p) .fst) (σ .map x) x
            (inverse A (σ .map x) (t .map (x, p) .fst) (subset_extension_in A P dP (t .map) x p)) q)))
      (x m ↦ match dP x [
        | inl. p ↦ p
        | inr. n ↦ absurd (P x .fst) (m (subset_extension_out A P dP (t .map) x n)) ])

{` For a decidable k-element subset P, the k-cycles with support P are the
   cycle structures on P: restrict, respectively extend by the identity. `}
def kcycle_fiber_equiv (A : Type) (hA : isSet A) (d : DecidableEquality A) (j : Nat) (P : Subtypes A)
  (dP : (x : A) → Decidable (P x .fst)) (hP : Mere (Id Type (SubtypeCarrier A P) (Fin (suc. (suc. j)))))
  : Equiv (KCycleFiber A j P) (CycleStructures (SubtypeCarrier A P))
  ≔ let C ≔ SubtypeCarrier A P in
    let to ≔ ((u ↦ let iff ≔ moved_iff_of_path A (u .fst .fst) P (u .snd) in
        (moved_restriction A (u .fst .fst) P iff, moved_restriction_cyclic A hA d j (u .fst .fst) (u .fst .snd) P iff))
      : KCycleFiber A j P → CycleStructures C) in
    let from ≔ ((v ↦ ((subset_extension A P dP (v .fst), extension_is_kcycle A hA j P dP hP (v .fst) (v .snd)),
        extension_support_path A hA j P dP hP (v .fst) (v .snd)))
      : CycleStructures C → KCycleFiber A j P) in
    quasi_inverse_equiv (KCycleFiber A j P) (CycleStructures C) to from
      (u ↦ let σ ≔ u .fst .fst in
        let iff ≔ moved_iff_of_path A σ P (u .snd) in
        let restr ≔ moved_restriction A σ P iff in
        let σ' ≔ subset_extension A P dP restr in
        let same ≔ ((x ↦ match dP x [
            | inl. p ↦ subset_extension_in A P dP (restr .map) x p
            | inr. n ↦ concat A (σ' .map x) x (σ .map x) (subset_extension_out A P dP (restr .map) x n)
                (match d (σ .map x) x [
                  | inl. q ↦ inverse A (σ .map x) x q
                  | inr. m ↦ absurd (Id A x (σ .map x)) (n (iff .snd x m)) ]) ])
          : (x : A) → Id A (σ' .map x) (σ .map x)) in
        subtype_equal (KCyclePermutations A j) (s ↦ Id (Subtypes A) P (permutation_support A (s .fst)))
          (s ↦ subtypes_set A P (permutation_support A (s .fst))) (from (to u)) u
          (subtype_equal (Equiv A A) (IsKCycle A j) (s ↦ mere_isprop (KCycleEnumeration A j s)) (from (to u) .fst) (u .fst)
            (equiv_path A A σ' σ (funext A (_ ↦ A) (σ' .map) (σ .map) same))))
      (v ↦ let σ ≔ subset_extension A P dP (v .fst) in
        let iff ≔ moved_iff_of_path A σ P (extension_support_path A hA j P dP hP (v .fst) (v .snd)) in
        let restr ≔ moved_restriction A σ P iff in
        subtype_equal (Equiv C C) (Cyclic C) (cyclic_prop C) (to (from v)) v
          (equiv_path C C restr (v .fst)
            (funext C (_ ↦ C) (restr .map) (v .fst .map)
              (y ↦ subtype_equal A (x ↦ P x .fst) (x ↦ P x .snd) (restr .map y) (v .fst .map y)
                (subset_extension_in A P dP (v .fst .map) (y .fst) (y .snd))))))

{` Every k-cycle is determined by its support, a k-element subset, and a
   cycle structure on it. `}
def kcycle_support_map (A : Type) (hA : isSet A) (d : DecidableEquality A) (j : Nat) (s : KCyclePermutations A j)
  : KSubsets A (suc. (suc. j))
  ≔ (permutation_support A (s .fst),
     moved_size A hA d j (s .fst) (s .snd) (permutation_support A (s .fst)) ((x m ↦ m), (x m ↦ m)))

def kcycle_support_decomposition (A : Type) (hA : isSet A) (d : DecidableEquality A) (j : Nat)
  : Equiv (KCyclePermutations A j)
      (Σ (KSubsets A (suc. (suc. j))) (S ↦ CycleStructures (SubtypeCarrier A (S .fst))))
  ≔ let K ≔ KSubsets A (suc. (suc. j)) in let KCP ≔ KCyclePermutations A j in
    let f ≔ kcycle_support_map A hA d j in
    let M ≔ ((P ↦ Mere (Id Type (SubtypeCarrier A P) (Fin (suc. (suc. j))))) : Subtypes A → Type) in
    compose_equiv KCP (Σ K (S ↦ BookFiber KCP K f S)) (Σ K (S ↦ CycleStructures (SubtypeCarrier A (S .fst))))
      (canonical_inverse_equiv (Σ K (S ↦ BookFiber KCP K f S)) KCP (sum_of_fibers_equiv KCP K f))
      (family_equiv K (S ↦ BookFiber KCP K f S) (S ↦ CycleStructures (SubtypeCarrier A (S .fst)))
        (S ↦ compose_equiv (BookFiber KCP K f S) (KCycleFiber A j (S .fst)) (CycleStructures (SubtypeCarrier A (S .fst)))
          (family_equiv KCP (s ↦ Id K S (f s)) (s ↦ Id (Subtypes A) (S .fst) (permutation_support A (s .fst)))
            (s ↦ subtype_path_equiv (Subtypes A) M (P ↦ mere_isprop (Id Type (SubtypeCarrier A P) (Fin (suc. (suc. j))))) S (f s)))
          (kcycle_fiber_equiv A hA d j (S .fst)
            (subset_member_decidable A hA d (S .fst) (suc. (suc. j)) (S .snd)) (S .snd))))

def k_cycle_decomposition_finite (A : Type) (ha : IsFinite A) (j : Nat)
  : IsFinite (Σ (KSubsets A (suc. (suc. j))) (S ↦ CycleStructures (SubtypeCarrier A (S .fst))))
  ≔ finite_sigma (KSubsets A (suc. (suc. j))) (ksubsets_finite A ha (suc. (suc. j)))
      (S ↦ CycleStructures (SubtypeCarrier A (S .fst)))
      (S ↦ cycle_structures_finite (SubtypeCarrier A (S .fst)) (suc. j) (S .snd))

def k_cycle_permutations_finite (A : Type) (ha : IsFinite A) (j : Nat) : IsFinite (KCyclePermutations A j)
  ≔ finite_of_equiv (KCyclePermutations A j) (Σ (KSubsets A (suc. (suc. j))) (S ↦ CycleStructures (SubtypeCarrier A (S .fst))))
      (kcycle_support_decomposition A (finite_sethood A ha) (finite_decidable_equality A ha) j)
      (k_cycle_decomposition_finite A ha j)

def fin_cardinality (m : Nat) : Id Nat (cardinality (Fin m) (fin_is_finite m)) m
  ≔ cardinality_from_path (Fin m) (fin_is_finite m) m (refl (Fin m))

{` The unlabeled exercise after xca:factorial, second part: a finite set of
   cardinality n has binom(n,k)·(k-1)! k-cycle permutations, for k = j+2 ≥ 2. `}
def k_cycle_permutations_cardinality (A : Type) (ha : IsFinite A) (j : Nat) (hf : IsFinite (KCyclePermutations A j))
  : Id Nat (cardinality (KCyclePermutations A j) hf) (mul (binomial (cardinality A ha) (suc. (suc. j))) (factorial (suc. j)))
  ≔ let K ≔ KSubsets A (suc. (suc. j)) in
    let hK ≔ ksubsets_finite A ha (suc. (suc. j)) in
    let CS ≔ ((S ↦ CycleStructures (SubtypeCarrier A (S .fst))) : K → Type) in
    let T ≔ Σ K CS in let hT ≔ k_cycle_decomposition_finite A ha j in
    let Y ≔ Fin (factorial (suc. j)) in
    let goal ≔ Id Nat (cardinality (KCyclePermutations A j) hf) (mul (binomial (cardinality A ha) (suc. (suc. j))) (factorial (suc. j))) in
    mere_rec ((S : K) → Equiv (CS S) Y) goal
      (nat_set (cardinality (KCyclePermutations A j) hf) (mul (binomial (cardinality A ha) (suc. (suc. j))) (factorial (suc. j))))
      (E ↦ calc
        cardinality (KCyclePermutations A j) hf = cardinality T hT
          by cardinality_equiv (KCyclePermutations A j) T
            (kcycle_support_decomposition A (finite_sethood A ha) (finite_decidable_equality A ha) j) hf hT
        = mul (cardinality K hK) (cardinality Y (fin_is_finite (factorial (suc. j))))
          by cardinality_equinumerous_sum K Y CS hK (fin_is_finite (factorial (suc. j))) E hT
        = mul (binomial (cardinality A ha) (suc. (suc. j))) (cardinality Y (fin_is_finite (factorial (suc. j))))
          by refl ((x ↦ mul x (cardinality Y (fin_is_finite (factorial (suc. j))))) : Nat → Nat)
            (ksubsets_cardinality A ha (suc. (suc. j)) hK)
        = mul (binomial (cardinality A ha) (suc. (suc. j))) (factorial (suc. j))
          by refl (mul (binomial (cardinality A ha) (suc. (suc. j)))) (fin_cardinality (factorial (suc. j))) ∎)
      (finite_choice K hK (S ↦ Equiv (CS S) Y)
        (S ↦ trunc_map native_truncation (Id Type (SubtypeCarrier A (S .fst)) (Fin (suc. (suc. j)))) (Equiv (CS S) Y)
          (p ↦ compose_equiv (CS S) (CycleStructures (Fin (suc. (suc. j)))) Y
            (id_to_equiv (CS S) (CycleStructures (Fin (suc. (suc. j)))) (refl CycleStructures p))
            (cycle_structures_fin_count (suc. j)))
          (S .snd)))
