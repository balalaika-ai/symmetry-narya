export "62-cycle-periods"

def Commutes (A B : Type) (e : Equiv A A) (f : Equiv B B) (h : A → B) : Type
  ≔ (x : A) → Id B (h (e .map x)) (f .map (h x))
def PermutationMap (A B : Type) (e : Equiv A A) (f : Equiv B B) : Type
  ≔ Σ (A → B) (Commutes A B e f)
def commutes_prop (A B : Type) (hb : isSet B) (e : Equiv A A) (f : Equiv B B) (h : A → B)
  : isProp (Commutes A B e f h)
  ≔ pi_prop A (x ↦ Id B (h (e .map x)) (f .map (h x))) (x ↦ hb (h (e .map x)) (f .map (h x)))

def cycle_map_value_unique (A B : Type) (hb : isSet B) (e : Equiv A A) (f : Equiv B B) (c : Cyclic A e)
  (h k : PermutationMap A B e f) (x : A) (p : Id B (h .fst x) (k .fst x)) (y : A)
  : Id B (h .fst y) (k .fst y)
  ≔ mere_rec (OrbitWitness A e x y) (Id B (h .fst y) (k .fst y)) (hb (h .fst y) (k .fst y))
      (w ↦ calc
        h .fst y = h .fst (permutation_power A e (w .fst) x) by refl (h .fst) (w .snd)
        = permutation_power B f (w .fst) (h .fst x) by permutation_power_intertwine A B e f (h .fst) (h .snd) (w .fst) x
        = permutation_power B f (w .fst) (k .fst x) by refl (permutation_power B f (w .fst)) p
        = k .fst (permutation_power A e (w .fst) x) by permutation_power_intertwine A B e f (k .fst) (k .snd) (w .fst) x
        = k .fst y by refl (k .fst) (w .snd) ∎) (c .snd x y)

def cycle_map_ext (A B : Type) (hb : isSet B) (e : Equiv A A) (f : Equiv B B) (c : Cyclic A e)
  (h k : PermutationMap A B e f) (x : A) (p : Id B (h .fst x) (k .fst x))
  : Id (PermutationMap A B e f) h k
  ≔ subtype_equal (A → B) (Commutes A B e f) (commutes_prop A B hb e f) h k
      (funext A (_ ↦ B) (h .fst) (k .fst) (cycle_map_value_unique A B hb e f c h k x p))

def PointedPermutationMaps (A B : Type) (e : Equiv A A) (f : Equiv B B) (x : A) (y : B) : Type
  ≔ Σ (PermutationMap A B e f) (h ↦ Id B (h .fst x) y)

def pointed_cycle_maps_prop (A B : Type) (hb : isSet B) (e : Equiv A A) (f : Equiv B B)
  (c : Cyclic A e) (x : A) (y : B) : isProp (PointedPermutationMaps A B e f x y)
  ≔ h k ↦ subtype_equal (PermutationMap A B e f) (g ↦ Id B (g .fst x) y) (g ↦ hb (g .fst x) y) h k
      (cycle_map_ext A B hb e f c (h .fst) (k .fst) x
        (concat B (h .fst .fst x) y (k .fst .fst x) (h .snd) (inverse B (k .fst .fst x) y (k .snd))))

def cycle_map_surjective_from_point (A B : Type) (e : Equiv A A) (f : Equiv B B) (d : Cyclic B f)
  (h : PermutationMap A B e f) (x : A) : Surjective A B (h .fst)
  ≔ y ↦ trunc_map native_truncation (OrbitWitness B f (h .fst x) y) (BookFiber A B (h .fst) y)
      (w ↦ (permutation_power A e (w .fst) x,
        concat B y (permutation_power B f (w .fst) (h .fst x)) (h .fst (permutation_power A e (w .fst) x))
          (w .snd) (inverse B (h .fst (permutation_power A e (w .fst) x)) (permutation_power B f (w .fst) (h .fst x))
            (permutation_power_intertwine A B e f (h .fst) (h .snd) (w .fst) x)))) (d .snd (h .fst x) y)

{` xca:map-of-cycles (ii). Nonemptiness is eliminated only into a proposition. `}
def cycle_map_surjective (A B : Type) (e : Equiv A A) (f : Equiv B B) (c : Cyclic A e) (d : Cyclic B f)
  (h : PermutationMap A B e f) : Surjective A B (h .fst)
  ≔ y ↦ mere_rec A (Mere (BookFiber A B (h .fst) y)) (mere_isprop (BookFiber A B (h .fst) y))
      (x ↦ cycle_map_surjective_from_point A B e f d h x y) (c .fst)

{` xca:map-of-cycles (i). `}
def cycle_map_period_inclusion (A B : Type) (hb : isSet B) (e : Equiv A A) (f : Equiv B B)
  (c : Cyclic A e) (d : Cyclic B f) (h : PermutationMap A B e f) : PeriodInclusion A B e f
  ≔ n p ↦ mere_rec A (PowerPeriod B f n) (power_period_prop B hb f n)
      (x ↦ cycle_period_from_point B hb f d (h .fst x) n (calc
        permutation_power B f n (h .fst x) = h .fst (permutation_power A e n x)
          by permutation_power_intertwine A B e f (h .fst) (h .snd) n x
        = h .fst x by refl (h .fst) (p (refl x)) ∎)) (c .fst)

{` xca:map-of-cycles (iii). `}
def cycle_map_injective (A B : Type) (ha : isSet A) (hb : isSet B) (e : Equiv A A) (f : Equiv B B)
  (c : Cyclic A e) (d : Cyclic B f) (h : PermutationMap A B e f) (back : PeriodInclusion B A f e)
  : PathReflecting A B (h .fst)
  ≔ x y p ↦ mere_rec (OrbitWitness A e x y) (Id A x y) (ha x y)
      (w ↦ let q ≔ cycle_period_from_point B hb f d (h .fst x) (w .fst) (calc
          permutation_power B f (w .fst) (h .fst x) = h .fst (permutation_power A e (w .fst) x)
            by permutation_power_intertwine A B e f (h .fst) (h .snd) (w .fst) x
          = h .fst y by refl (h .fst) (w .snd)
          = h .fst x by p ∎) in
        calc
          x = permutation_power A e (w .fst) x by back (w .fst) q (refl x)
          = y by w .snd ∎) (c .snd x y)

def cycle_map_equiv (A B : Type) (ha : isSet A) (hb : isSet B) (e : Equiv A A) (f : Equiv B B)
  (c : Cyclic A e) (d : Cyclic B f) (h : PermutationMap A B e f) (back : PeriodInclusion B A f e)
  : Equiv A B
  ≔ set_bijection_equiv A B hb (h .fst) (cycle_map_injective A B ha hb e f c d h back)
      (cycle_map_surjective A B e f c d h)
