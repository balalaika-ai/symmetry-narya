export "1723-blass-sizes"

{` The hypothesis of Blass's Theorem 6 (choicefin.tex:301): ‖X → BC_n‖₀ is
   contractible for every set X and every positive n. BC_n is the component
   Cyc_n of the standard n-cycle in Cycles (CycleComponent n, module 92;
   index n = m+1 is the cycle with m+1 elements). `}
def CyclicTorsorsTrivial : Type
  ≔ (X : SetTypes) (n : Nat) → BookIsContr (SetTrunc (X .fst → CycleComponent (suc. n)))

{` An injective endomap of an (n+2)-element set A under which every point
   reaches every other point is a permutation whose orbit relation is total,
   i.e. a cycle; it lies in the component Cyc_{n+2}. `}
def bsix_permutation (A : Type) (hA : isSet A) (f : A → A) (inj : PathReflecting A A f)
  (surj : Surjective A A f) : Equiv A A
  ≔ native_equivalence A A
      (native_embedding_surjection_equiv A A f (path_reflecting_set_embedding A A hA f inj) surj)

def bsix_permutation_map (A : Type) (hA : isSet A) (f : A → A) (inj : PathReflecting A A f)
  (surj : Surjective A A f) : Id (A → A) (bsix_permutation A hA f inj surj .map) f
  ≔ refl f

def bsix_fin_path_point (N : Nat) (A : Type) (p : Mere (Id Type (Fin (suc. N)) A)) : Mere A
  ≔ trunc_map native_truncation (Id Type (Fin (suc. N)) A) A
      (q ↦ transport Type (Y ↦ Y) (Fin (suc. N)) A q (inr. star.)) p

def bsix_cyclic (n : Nat) (A : Type) (hA : isSet A) (p : Mere (Id Type (Fin (suc. (suc. n))) A))
  (f : A → A) (inj : PathReflecting A A f) (tr : BsixTransitive A f)
  : Cyclic A (bsix_permutation A hA f inj (bsix_injective_surjective (suc. (suc. n)) A p f inj))
  ≔ (bsix_fin_path_point (suc. n) A p,
      x y ↦ trunc_map native_truncation (Σ Nat (i ↦ Id A y (iterate A f i x)))
        (OrbitWitness A (bsix_permutation A hA f inj (bsix_injective_surjective (suc. (suc. n)) A p f inj)) x y)
        (w ↦ (pos. (w .fst), w .snd)) (tr x y))

def bsix_cycle (n : Nat) (A : Type) (hA : isSet A) (p : Mere (Id Type (Fin (suc. (suc. n))) A))
  (f : A → A) (inj : PathReflecting A A f) (tr : BsixTransitive A f) : Cycles
  ≔ (((A, hA), bsix_permutation A hA f inj (bsix_injective_surjective (suc. (suc. n)) A p f inj)),
      bsix_cyclic n A hA p f inj tr)

def bsix_cycle_component (n : Nat) (A : Type) (hA : isSet A) (p : Mere (Id Type (Fin (suc. (suc. n))) A))
  (f : A → A) (inj : PathReflecting A A f) (tr : BsixTransitive A f) : CycleComponent (suc. (suc. n))
  ≔ let N : Nat ≔ suc. (suc. n) in
    let c ≔ bsix_cycle n A hA p f inj tr in
    let fin : IsFinite A ≔ trunc_map native_truncation (Id Type (Fin N) A) (Σ Nat (m ↦ Id Type A (Fin m)))
      (q ↦ (N, inverse Type (Fin N) A q)) p in
    let cls ≔ finite_cycle_classification c fin in
    let cardN : Id Nat (cardinality A fin) N
      ≔ mere_rec (Id Type (Fin N) A) (Id Nat (cardinality A fin) N) (nat_set (cardinality A fin) N)
          (q ↦ cardinality_from_path A fin N (inverse Type (Fin N) A q)) p in
    let keq : Id Nat (cls .fst) (suc. n)
      ≔ refl nat_pred (concat Nat (suc. (cls .fst)) (cardinality A fin) N
          (inverse Nat (cardinality A fin) (suc. (cls .fst)) (finite_cycle_cardinality c fin)) cardN) in
    let mp : Mere (Id Cycles c (finite_standard_cycle (suc. n)))
      ≔ transport Nat (k ↦ Mere (Id Cycles c (finite_standard_cycle k))) (cls .fst) (suc. n) keq (cls .snd) in
    (c, trunc_map native_truncation (Id Cycles c (finite_standard_cycle (suc. n)))
          (Id Cycles (finite_standard_cycle (suc. n)) c) (inverse Cycles c (finite_standard_cycle (suc. n))) mp)

def bsix_cycle_component_carrier (n : Nat) (A : Type) (hA : isSet A) (p : Mere (Id Type (Fin (suc. (suc. n))) A))
  (f : A → A) (inj : PathReflecting A A f) (tr : BsixTransitive A f)
  : Id Type (bsix_cycle_component n A hA p f inj tr .fst .fst .fst .fst) A
  ≔ refl A

{` The base point 0 of the standard cycle, carried along an identification
   of the base of Cyc_m with another point. `}
def bsix_standard_zero (n : Nat) : principal_cycle (suc. n) .fst .fst .fst ≔ remainder_at n zero. star.

def bsix_component_transport (n : Nat) (u : CycleComponent (suc. n))
  (e : Id (CycleComponent (suc. n)) (principal_component_point (suc. n)) u) : u .fst .fst .fst .fst
  ≔ transport (CycleComponent (suc. n)) (v ↦ v .fst .fst .fst .fst) (principal_component_point (suc. n)) u e
      (bsix_standard_zero n)

{` The cyclic part of the proof: over a set Z of indices z with an
   (n+2)-element set A(z) and a transitive injective endomap, the hypothesis
   makes the induced map Z → Cyc_{n+2} merely constant, which gives a section. `}
def bsix_cyclic_sections (H : CyclicTorsorsTrivial) (n : Nat) (Z : SetTypes) (A : Z .fst → Type)
  (hA : (z : Z .fst) → isSet (A z)) (p : (z : Z .fst) → Mere (Id Type (Fin (suc. (suc. n))) (A z)))
  (f : (z : Z .fst) → A z → A z) (inj : (z : Z .fst) → PathReflecting (A z) (A z) (f z))
  (tr : (z : Z .fst) → BsixTransitive (A z) (f z)) : Mere ((z : Z .fst) → A z)
  ≔ let F : Z .fst → CycleComponent (suc. (suc. n)) ≔ z ↦ bsix_cycle_component n (A z) (hA z) (p z) (f z) (inj z) (tr z) in
    trunc_map native_truncation
      ((z : Z .fst) → Id (CycleComponent (suc. (suc. n))) (principal_component_point (suc. (suc. n))) (F z))
      ((z : Z .fst) → A z)
      (e z ↦ bsix_component_transport (suc. n) (F z) (e z))
      (contractible_set_trunc_constant (Z .fst) (CycleComponent (suc. (suc. n))) (principal_component_point (suc. (suc. n)))
        (H Z (suc. n)) F)
