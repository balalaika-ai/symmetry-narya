export "210-truncation-smallness"
export "186-chapter-two-remarks"

{` rem:cycle-vs-cycle: every permutation of a set is the sum of its orbits,
   each of which is a cycle; the index set is the orbit quotient. `}
def orbit_class (A : Type) (e : Equiv A A) (x : A) : OrbitQuotient A e
  ≔ quotient_class A (orbit_relation A e) x

def orbit_class_step (A : Type) (e : Equiv A A) (x : A)
  : Id (OrbitQuotient A e) (orbit_class A e x) (orbit_class A e (e .map x))
  ≔ quotient_encode A (orbit_relation A e) x (e .map x)
      (mere (OrbitWitness A e x (e .map x)) (pos. (suc. zero.), refl (e .map x)))

def orbit_class_back (A : Type) (e : Equiv A A) (x : A)
  : Id (OrbitQuotient A e) (orbit_class A e x) (orbit_class A e (equiv_inverse_map A A e x))
  ≔ inverse (OrbitQuotient A e) (orbit_class A e (equiv_inverse_map A A e x)) (orbit_class A e x)
      (concat (OrbitQuotient A e) (orbit_class A e (equiv_inverse_map A A e x))
        (orbit_class A e (e .map (equiv_inverse_map A A e x))) (orbit_class A e x)
        (orbit_class_step A e (equiv_inverse_map A A e x))
        (refl (orbit_class A e) (equiv_counit A A e x)))

{` The elements of one orbit O, as the book fiber of the class map. `}
def OrbitCarrier (A : Type) (e : Equiv A A) (O : OrbitQuotient A e) : Type
  ≔ BookFiber A (OrbitQuotient A e) (orbit_class A e) O

def orbit_carrier_set (A : Type) (hA : isSet A) (e : Equiv A A) (O : OrbitQuotient A e) : isSet (OrbitCarrier A e O)
  ≔ sigma_set A (x ↦ Id (OrbitQuotient A e) O (orbit_class A e x)) hA
      (x ↦ prop_is_set (Id (OrbitQuotient A e) O (orbit_class A e x))
        (quotient_set A (orbit_relation A e) O (orbit_class A e x)))

def orbit_restriction (A : Type) (e : Equiv A A) (O : OrbitQuotient A e)
  : Equiv (OrbitCarrier A e O) (OrbitCarrier A e O)
  ≔ let Q ≔ OrbitQuotient A e in
    subtype_induced_equiv A A e (x ↦ Id Q O (orbit_class A e x)) (x ↦ Id Q O (orbit_class A e x))
      (x ↦ quotient_set A (orbit_relation A e) O (orbit_class A e x))
      (x ↦ quotient_set A (orbit_relation A e) O (orbit_class A e x))
      (x p ↦ concat Q O (orbit_class A e x) (orbit_class A e (e .map x)) p (orbit_class_step A e x))
      (x p ↦ concat Q O (orbit_class A e x) (orbit_class A e (equiv_inverse_map A A e x)) p (orbit_class_back A e x))

def orbit_restriction_power (A : Type) (e : Equiv A A) (O : OrbitQuotient A e) (z : Int) (u : OrbitCarrier A e O)
  : Id A (permutation_power (OrbitCarrier A e O) (orbit_restriction A e O) z u .fst) (permutation_power A e z (u .fst))
  ≔ permutation_power_intertwine (OrbitCarrier A e O) A (orbit_restriction A e O) e (v ↦ v .fst)
      (v ↦ refl (e .map (v .fst))) z u

{` Each orbit, with the restricted permutation, is a cycle. `}
def orbit_cyclic (A : Type) (e : Equiv A A) (O : OrbitQuotient A e)
  : Cyclic (OrbitCarrier A e O) (orbit_restriction A e O)
  ≔ let Q ≔ OrbitQuotient A e in let R ≔ orbit_relation A e in
    let F ≔ OrbitCarrier A e O in
    (quotient_surjective A R O,
     u v ↦ mere_rec (OrbitWitness A e (u .fst) (v .fst)) (SameOrbit F (orbit_restriction A e O) u v)
       (same_orbit_prop F (orbit_restriction A e O) u v)
       (w ↦ mere (OrbitWitness F (orbit_restriction A e O) u v) (w .fst,
         subtype_equal A (x ↦ Id Q O (orbit_class A e x)) (x ↦ quotient_set A R O (orbit_class A e x))
           v (permutation_power F (orbit_restriction A e O) (w .fst) u)
           (concat A (v .fst) (permutation_power A e (w .fst) (u .fst))
             (permutation_power F (orbit_restriction A e O) (w .fst) u .fst)
             (w .snd)
             (inverse A (permutation_power F (orbit_restriction A e O) (w .fst) u .fst)
               (permutation_power A e (w .fst) (u .fst)) (orbit_restriction_power A e O (w .fst) u)))))
       (quotient_effective A R (u .fst) (v .fst) .map
         (concat Q (orbit_class A e (u .fst)) O (orbit_class A e (v .fst))
           (inverse Q O (orbit_class A e (u .fst)) (u .snd)) (v .snd))))

def orbit_cycle (A : Type) (hA : isSet A) (e : Equiv A A) (O : OrbitQuotient A e) : Cycles
  ≔ (((OrbitCarrier A e O, orbit_carrier_set A hA e O), orbit_restriction A e O), orbit_cyclic A e O)

{` The sum of a family of permutations indexed by a set. `}
def permutation_sum (Q : SetTypes) (C : Q .fst → Permutations) : Permutations
  ≔ ((Σ (Q .fst) (q ↦ C q .fst .fst),
      sigma_set (Q .fst) (q ↦ C q .fst .fst) (Q .snd) (q ↦ C q .fst .snd)),
     family_equiv (Q .fst) (q ↦ C q .fst .fst) (q ↦ C q .fst .fst) (q ↦ C q .snd))

{` Decomposition: (A, e) is isomorphic to the sum over its orbit set of
   the cycles formed by the orbits. `}
def permutation_orbit_decomposition (A : Type) (hA : isSet A) (e : Equiv A A)
  : PermutationIsomorphisms
      (permutation_sum (OrbitQuotient A e, quotient_set A (orbit_relation A e)) (O ↦ orbit_cycle A hA e O .fst))
      ((A, hA), e)
  ≔ (sum_of_fibers_equiv A (OrbitQuotient A e) (orbit_class A e), w ↦ refl (e .map (w .snd .fst)))

def permutation_orbit_decomposition_path (A : Type) (hA : isSet A) (e : Equiv A A)
  : Id Permutations
      (permutation_sum (OrbitQuotient A e, quotient_set A (orbit_relation A e)) (O ↦ orbit_cycle A hA e O .fst))
      ((A, hA), e)
  ≔ equiv_inverse_map
      (Id Permutations
        (permutation_sum (OrbitQuotient A e, quotient_set A (orbit_relation A e)) (O ↦ orbit_cycle A hA e O .fst))
        ((A, hA), e))
      (PermutationIsomorphisms
        (permutation_sum (OrbitQuotient A e, quotient_set A (orbit_relation A e)) (O ↦ orbit_cycle A hA e O .fst))
        ((A, hA), e))
      (permutation_paths_equiv
        (permutation_sum (OrbitQuotient A e, quotient_set A (orbit_relation A e)) (O ↦ orbit_cycle A hA e O .fst))
        ((A, hA), e))
      (permutation_orbit_decomposition A hA e)

{` A cycle consists of a single orbit: its orbit set is contractible,
   so the decomposition has exactly one summand. `}
def cycle_single_orbit (c : Cycles) : BookIsContr (OrbitQuotient (c .fst .fst .fst) (c .fst .snd))
  ≔ cyclic_quotient_contractible (c .fst .fst .fst) (c .fst .snd) (c .snd)
