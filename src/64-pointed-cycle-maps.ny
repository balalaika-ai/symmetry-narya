export "63-maps-of-cycles"

def power_equality_difference (A : Type) (e : Equiv A A) (n k : Int) (x : A)
  (p : Id A (permutation_power A e n x) (permutation_power A e k x))
  : Id A (permutation_power A e (int_sub n k) x) x
  ≔ calc
      permutation_power A e (int_sub n k) x = permutation_power A e (int_neg k) (permutation_power A e n x)
        by permutation_power_add A e n (int_neg k) x
      = permutation_power A e (int_neg k) (permutation_power A e k x) by refl (permutation_power A e (int_neg k)) p
      = x by permutation_power_inverse A e k x ∎

def power_difference_equality (A : Type) (e : Equiv A A) (n k : Int) (x : A)
  (p : Id A (permutation_power A e (int_sub n k) x) x)
  : Id A (permutation_power A e n x) (permutation_power A e k x)
  ≔ equivalence_injective A A (permutation_power_equiv A e (int_neg k))
      (permutation_power A e n x) (permutation_power A e k x) (calc
        permutation_power A e (int_neg k) (permutation_power A e n x)
        = permutation_power A e (int_sub n k) x by permutation_power_add A e n (int_neg k) x
        = x by p
        = permutation_power A e (int_neg k) (permutation_power A e k x) by permutation_power_inverse A e k x ∎)

def period_inclusion_power_equality (A B : Type) (ha : isSet A) (e : Equiv A A) (f : Equiv B B)
  (c : Cyclic A e) (inc : PeriodInclusion A B e f) (a : A) (b : B) (n k : Int)
  (p : Id A (permutation_power A e n a) (permutation_power A e k a))
  : Id B (permutation_power B f n b) (permutation_power B f k b)
  ≔ power_difference_equality B f n k b
      (inc (int_sub n k) (cycle_period_from_point A ha e c a (int_sub n k)
        (power_equality_difference A e n k a p)) (refl b))

def weakly_constant_rec_value (A B : Type) (f : A → B) (hb : isSet B) (h : WeaklyConstant A B f)
  (t : Mere A) (a : A) : Id B (weakly_constant_rec A B f hb h t) (f a)
  ≔ refl (weakly_constant_rec A B f hb h) (mere_isprop A t (mere A a))

def orbit_image_constant (A B : Type) (ha : isSet A) (e : Equiv A A) (f : Equiv B B)
  (c : Cyclic A e) (inc : PeriodInclusion A B e f) (a : A) (b : B) (x : A)
  : WeaklyConstant (OrbitWitness A e a x) B (w ↦ permutation_power B f (w .fst) b)
  ≔ u v ↦ period_inclusion_power_equality A B ha e f c inc a b (u .fst) (v .fst)
      (concat A (permutation_power A e (u .fst) a) x (permutation_power A e (v .fst) a)
        (inverse A x (permutation_power A e (u .fst) a) (u .snd)) (v .snd))

def orbit_image (A B : Type) (ha : isSet A) (hb : isSet B) (e : Equiv A A) (f : Equiv B B)
  (c : Cyclic A e) (inc : PeriodInclusion A B e f) (a : A) (b : B) (x : A) : B
  ≔ weakly_constant_rec (OrbitWitness A e a x) B (w ↦ permutation_power B f (w .fst) b) hb
      (orbit_image_constant A B ha e f c inc a b x) (c .snd a x)

def orbit_image_value (A B : Type) (ha : isSet A) (hb : isSet B) (e : Equiv A A) (f : Equiv B B)
  (c : Cyclic A e) (inc : PeriodInclusion A B e f) (a : A) (b : B) (x : A) (w : OrbitWitness A e a x)
  : Id B (orbit_image A B ha hb e f c inc a b x) (permutation_power B f (w .fst) b)
  ≔ weakly_constant_rec_value (OrbitWitness A e a x) B (w ↦ permutation_power B f (w .fst) b) hb
      (orbit_image_constant A B ha e f c inc a b x) (c .snd a x) w

def orbit_witness_succ (A : Type) (e : Equiv A A) (a x : A) (w : OrbitWitness A e a x)
  : OrbitWitness A e a (e .map x)
  ≔ (int_succ (w .fst), calc
      e .map x = e .map (permutation_power A e (w .fst) a) by refl (e .map) (w .snd)
      = permutation_power A e (int_succ (w .fst)) a by permutation_power_succ A e (w .fst) a ∎)

def orbit_image_commutes (A B : Type) (ha : isSet A) (hb : isSet B) (e : Equiv A A) (f : Equiv B B)
  (c : Cyclic A e) (inc : PeriodInclusion A B e f) (a : A) (b : B)
  : Commutes A B e f (orbit_image A B ha hb e f c inc a b)
  ≔ x ↦ mere_rec (OrbitWitness A e a x)
      (Id B (orbit_image A B ha hb e f c inc a b (e .map x)) (f .map (orbit_image A B ha hb e f c inc a b x)))
      (hb (orbit_image A B ha hb e f c inc a b (e .map x)) (f .map (orbit_image A B ha hb e f c inc a b x)))
      (w ↦ calc
        orbit_image A B ha hb e f c inc a b (e .map x) = permutation_power B f (int_succ (w .fst)) b
          by orbit_image_value A B ha hb e f c inc a b (e .map x) (orbit_witness_succ A e a x w)
        = f .map (permutation_power B f (w .fst) b) by permutation_power_succ B f (w .fst) b
        = f .map (orbit_image A B ha hb e f c inc a b x)
          by refl (f .map) (orbit_image_value A B ha hb e f c inc a b x w) ∎) (c .snd a x)

def pointed_cycle_map (A B : Type) (ha : isSet A) (hb : isSet B) (e : Equiv A A) (f : Equiv B B)
  (c : Cyclic A e) (inc : PeriodInclusion A B e f) (a : A) (b : B) : PointedPermutationMaps A B e f a b
  ≔ ((orbit_image A B ha hb e f c inc a b, orbit_image_commutes A B ha hb e f c inc a b),
      orbit_image_value A B ha hb e f c inc a b a (int_zero, refl a))

def pointed_cycle_maps_contractible (A B : Type) (ha : isSet A) (hb : isSet B) (e : Equiv A A) (f : Equiv B B)
  (c : Cyclic A e) (inc : PeriodInclusion A B e f) (a : A) (b : B)
  : BookIsContr (PointedPermutationMaps A B e f a b)
  ≔ (pointed_cycle_map A B ha hb e f c inc a b,
      pointed_cycle_maps_prop A B hb e f c a b (pointed_cycle_map A B ha hb e f c inc a b))

def PointedCycleEquivalences (A B : Type) (e : Equiv A A) (f : Equiv B B) (a : A) (b : B) : Type
  ≔ Σ (PointedPermutationMaps A B e f a b) (h ↦ isEquiv A B (h .fst .fst))

def pointed_cycle_equivalences_contractible (A B : Type) (ha : isSet A) (hb : isSet B)
  (e : Equiv A A) (f : Equiv B B) (c : Cyclic A e) (d : Cyclic B f)
  (inc : PeriodInclusion A B e f) (back : PeriodInclusion B A f e) (a : A) (b : B)
  : BookIsContr (PointedCycleEquivalences A B e f a b)
  ≔ let h ≔ pointed_cycle_map A B ha hb e f c inc a b in
    let center : PointedCycleEquivalences A B e f a b
      ≔ (h, cycle_map_equiv A B ha hb e f c d (h .fst) back .equiv) in
    (center, sigma_prop (PointedPermutationMaps A B e f a b) (h ↦ isEquiv A B (h .fst .fst))
      (pointed_cycle_maps_prop A B hb e f c a b) (h ↦ isequiv_isprop A B (h .fst .fst)) center)
