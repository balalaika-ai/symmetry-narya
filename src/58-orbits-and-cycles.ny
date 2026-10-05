export "57-permutation-powers"

{` def:connected-by-t: existence is truncated, and the witness path has
   the book's direction y = t^n(x). `}
def OrbitWitness (A : Type) (e : Equiv A A) (x y : A) : Type
  ≔ Σ Int (n ↦ Id A y (permutation_power A e n x))
def SameOrbit (A : Type) (e : Equiv A A) (x y : A) : Type ≔ Mere (OrbitWitness A e x y)
def same_orbit_prop (A : Type) (e : Equiv A A) (x y : A) : isProp (SameOrbit A e x y)
  ≔ mere_isprop (OrbitWitness A e x y)

def orbit_witness_reverse (A : Type) (e : Equiv A A) (x y : A) (w : OrbitWitness A e x y)
  : OrbitWitness A e y x
  ≔ (int_neg (w .fst), calc
      x = permutation_power A e (int_neg (w .fst)) (permutation_power A e (w .fst) x)
        by permutation_power_inverse A e (w .fst) x
      = permutation_power A e (int_neg (w .fst)) y
        by refl (permutation_power A e (int_neg (w .fst))) (w .snd) ∎)

def orbit_witness_compose (A : Type) (e : Equiv A A) (x y z : A)
  (v : OrbitWitness A e x y) (w : OrbitWitness A e y z) : OrbitWitness A e x z
  ≔ (int_add (v .fst) (w .fst), calc
      z = permutation_power A e (w .fst) y by w .snd
      = permutation_power A e (w .fst) (permutation_power A e (v .fst) x)
        by refl (permutation_power A e (w .fst)) (v .snd)
      = permutation_power A e (int_add (v .fst) (w .fst)) x
        by permutation_power_add A e (v .fst) (w .fst) x ∎)

def same_orbit_refl (A : Type) (e : Equiv A A) (x : A) : SameOrbit A e x x
  ≔ mere (OrbitWitness A e x x) (int_zero, refl x)
def same_orbit_sym (A : Type) (e : Equiv A A) (x y : A) : SameOrbit A e x y → SameOrbit A e y x
  ≔ mere_rec (OrbitWitness A e x y) (SameOrbit A e y x) (same_orbit_prop A e y x)
      (w ↦ mere (OrbitWitness A e y x) (orbit_witness_reverse A e x y w))
def same_orbit_trans (A : Type) (e : Equiv A A) (x y z : A)
  (v : SameOrbit A e x y) (w : SameOrbit A e y z) : SameOrbit A e x z
  ≔ mere_rec (OrbitWitness A e x y) (SameOrbit A e x z) (same_orbit_prop A e x z)
      (v ↦ mere_rec (OrbitWitness A e y z) (SameOrbit A e x z) (same_orbit_prop A e x z)
        (w ↦ mere (OrbitWitness A e x z) (orbit_witness_compose A e x y z v w)) w) v

def orbit_relation (A : Type) (e : Equiv A A) : EquivalenceRelation A
  ≔ ((x y ↦ (SameOrbit A e x y, same_orbit_prop A e x y)),
      same_orbit_refl A e, same_orbit_sym A e, same_orbit_trans A e)
def OrbitQuotient (A : Type) (e : Equiv A A) : Type ≔ Quotient A (orbit_relation A e)

def Cyclic (A : Type) (e : Equiv A A) : Type
  ≔ Product (Mere A) ((x y : A) → SameOrbit A e x y)
def cyclic_prop (A : Type) (e : Equiv A A) : isProp (Cyclic A e)
  ≔ product_prop (Mere A) ((x y : A) → SameOrbit A e x y) (mere_isprop A)
      (pi_prop A (x ↦ (y : A) → SameOrbit A e x y)
        (x ↦ pi_prop A (SameOrbit A e x) (same_orbit_prop A e x)))

{` def:Cyc, using native equivalences and the already defined set universe. `}
def Cycles : Type ≔ Σ Permutations (p ↦ Cyclic (p .fst .fst) (p .snd))

def cyclic_orbit_surjective (A : Type) (e : Equiv A A) (h : Cyclic A e) (x : A)
  : Surjective Int A (n ↦ permutation_power A e n x) ≔ h .snd x

def cyclic_from_orbit_surjective (A : Type) (e : Equiv A A) (x : A)
  (h : Surjective Int A (n ↦ permutation_power A e n x)) : Cyclic A e
  ≔ (mere A x, y z ↦ same_orbit_trans A e y x z (same_orbit_sym A e x y (h y)) (h z))

def orbit_quotient_contract_at (A : Type) (e : Equiv A A)
  (h : (x y : A) → SameOrbit A e x y) (x : A) : BookIsContr (OrbitQuotient A e)
  ≔ (quotient_class A (orbit_relation A e) x,
      z ↦ mere_rec (BookFiber A (OrbitQuotient A e) (quotient_class A (orbit_relation A e)) z)
        (Id (OrbitQuotient A e) (quotient_class A (orbit_relation A e) x) z)
        (quotient_set A (orbit_relation A e) (quotient_class A (orbit_relation A e) x) z)
        (w ↦ concat (OrbitQuotient A e) (quotient_class A (orbit_relation A e) x)
          (quotient_class A (orbit_relation A e) (w .fst)) z
          (quotient_encode A (orbit_relation A e) x (w .fst) (h x (w .fst)))
          (inverse (OrbitQuotient A e) z (quotient_class A (orbit_relation A e) (w .fst)) (w .snd)))
        (quotient_surjective A (orbit_relation A e) z))

def cyclic_quotient_contractible (A : Type) (e : Equiv A A) (h : Cyclic A e)
  : BookIsContr (OrbitQuotient A e)
  ≔ mere_rec A (BookIsContr (OrbitQuotient A e)) (book_iscontr_isprop (OrbitQuotient A e))
      (orbit_quotient_contract_at A e (h .snd)) (h .fst)

def contractible_quotient_cyclic (A : Type) (e : Equiv A A) (h : BookIsContr (OrbitQuotient A e))
  : Cyclic A e
  ≔ (mere_rec (BookFiber A (OrbitQuotient A e) (quotient_class A (orbit_relation A e)) (h .center))
      (Mere A) (mere_isprop A) (w ↦ mere A (w .fst)) (quotient_surjective A (orbit_relation A e) (h .center)),
      x y ↦ quotient_effective A (orbit_relation A e) x y .map
        (concat (OrbitQuotient A e) (quotient_class A (orbit_relation A e) x) (h .center)
          (quotient_class A (orbit_relation A e) y)
          (inverse (OrbitQuotient A e) (h .center) (quotient_class A (orbit_relation A e) x)
            (h .contract (quotient_class A (orbit_relation A e) x)))
          (h .contract (quotient_class A (orbit_relation A e) y))))

def cyclic_quotient_equiv (A : Type) (e : Equiv A A) : Equiv (Cyclic A e) (BookIsContr (OrbitQuotient A e))
  ≔ iff_equiv (Cyclic A e) (BookIsContr (OrbitQuotient A e)) (cyclic_prop A e)
      (book_iscontr_isprop (OrbitQuotient A e)) (cyclic_quotient_contractible A e) (contractible_quotient_cyclic A e)

def integer_successor_cyclic : Cyclic Int int_succ_equiv
  ≔ (mere Int int_zero, x y ↦ mere (OrbitWitness Int int_succ_equiv x y)
      (int_sub y x, calc
        y = int_add (int_sub y x) x by int_sub_add y x
        = int_add x (int_sub y x) by int_add_comm (int_sub y x) x ∎))

def infinite_cycle : Cycles ≔ (((Int, int_set), int_succ_equiv), integer_successor_cyclic)

def orbit_power (A : Type) (e : Equiv A A) (x : A) (n : Int)
  : SameOrbit A e x (permutation_power A e n x)
  ≔ mere (OrbitWitness A e x (permutation_power A e n x)) (n, refl (permutation_power A e n x))

def same_orbit_map (A B : Type) (e : Equiv A A) (f : Equiv B B) (h : A → B)
  (step : (x : A) → Id B (h (e .map x)) (f .map (h x))) (x y : A)
  : SameOrbit A e x y → SameOrbit B f (h x) (h y)
  ≔ mere_rec (OrbitWitness A e x y) (SameOrbit B f (h x) (h y)) (same_orbit_prop B f (h x) (h y))
      (w ↦ mere (OrbitWitness B f (h x) (h y)) (w .fst,
        concat B (h y) (h (permutation_power A e (w .fst) x)) (permutation_power B f (w .fst) (h x))
          (refl h (w .snd)) (permutation_power_intertwine A B e f h step (w .fst) x)))

def cyclic_transfer (A B : Type) (e : Equiv A A) (f : Equiv B B) (h : Equiv A B)
  (step : (x : A) → Id B (h .map (e .map x)) (f .map (h .map x))) (c : Cyclic A e)
  : Cyclic B f
  ≔ (mere_rec A (Mere B) (mere_isprop B) (x ↦ mere B (h .map x)) (c .fst),
      y z ↦ refl (SameOrbit B f) (equiv_counit A B h y) (equiv_counit A B h z) .trr
        (same_orbit_map A B e f (h .map) step (equiv_inverse_map A B h y) (equiv_inverse_map A B h z)
          (c .snd (equiv_inverse_map A B h y) (equiv_inverse_map A B h z))))
