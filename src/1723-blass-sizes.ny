export "1722-blass-orbits"

{` Sizes needed in the proof of Blass's Theorem 6, for an (n+1)-element set A
   and a fixed-point-free endomap f: if f is not injective, its image has at
   most n elements; if f is injective, it has at most n orbits; if f is
   injective but not transitive (not a single orbit), every orbit has at most
   n elements. Each is proved on Fin (n+1) and transported. `}

def BsixImage (A : Type) (f : A → A) : Type ≔ Σ A (z ↦ Mere (BookFiber A A f z))

def BsixOrbits (A : Type) (f : A → A) (mper : (x : A) → Mere (BsixPeriod A f x)) (dA : DecidableEquality A) : Type
  ≔ Quotient A (bsix_reach_relation A f mper dA)

def bsix_orbit_class (A : Type) (f : A → A) (mper : (x : A) → Mere (BsixPeriod A f x)) (dA : DecidableEquality A)
  : A → BsixOrbits A f mper dA
  ≔ quotient_class A (bsix_reach_relation A f mper dA)

def BsixOrbitElements (A : Type) (f : A → A) (mper : (x : A) → Mere (BsixPeriod A f x)) (dA : DecidableEquality A)
  (o : BsixOrbits A f mper dA) : Type
  ≔ BookFiber A (BsixOrbits A f mper dA) (bsix_orbit_class A f mper dA) o

def BsixTransitive (A : Type) (f : A → A) : Type ≔ (y z : A) → BsixReach A f y z

{` Image of a non-injective endomap of Fin (n+1). `}
def bsix_fin_image_bound (n : Nat) (f : Fin (suc. n) → Fin (suc. n))
  (ninj : PathReflecting (Fin (suc. n)) (Fin (suc. n)) f → Empty)
  : CardBound n (BsixImage (Fin (suc. n)) f)
  ≔ bsix_decidable_subset_bound n (z ↦ Mere (BookFiber (Fin (suc. n)) (Fin (suc. n)) f z))
      (z ↦ mere_isprop (BookFiber (Fin (suc. n)) (Fin (suc. n)) f z))
      (z ↦ decidable_mere (BookFiber (Fin (suc. n)) (Fin (suc. n)) f z)
        (fin_sigma_decidable (suc. n) (y ↦ Id (Fin (suc. n)) z (f y)) (y ↦ fin_decidable_equality (suc. n) z (f y))))
      (all ↦ ninj (bsix_fin_surjective_injective (suc. n) f all))

{` Orbits of an injective fixed-point-free endomap of Fin (n+1): a section
   of the class map is injective, and it misses x or f(x) (they lie in the
   same orbit), so the orbit count is at most n. `}
def bsix_fin_orbits_bound (n : Nat) (f : Fin (suc. n) → Fin (suc. n))
  (fpf : (y : Fin (suc. n)) → Id (Fin (suc. n)) (f y) y → Empty)
  (mper : (x : Fin (suc. n)) → Mere (BsixPeriod (Fin (suc. n)) f x)) (dA : DecidableEquality (Fin (suc. n)))
  : CardBound n (BsixOrbits (Fin (suc. n)) f mper dA)
  ≔ let F ≔ Fin (suc. n) in
    let R ≔ bsix_reach_relation F f mper dA in
    let O ≔ BsixOrbits F f mper dA in
    let q ≔ bsix_orbit_class F f mper dA in
    let dO ≔ quotient_decidable_equality F R (bsix_reach_relation_decidable F f mper dA) in
    let sec : (o : O) → BookFiber F O q o
      ≔ o ↦ fin_surjection_section (suc. n) O q dO (quotient_surjective F R) o in
    mere_rec (Σ Nat (k ↦ Id Type O (Fin k))) (CardBound n O) (card_bound_prop n O)
      (w ↦
        let k ≔ w .fst in
        let back : Fin k → O ≔ j ↦ id_to_equiv (Fin k) O (inverse Type O (Fin k) (w .snd)) .map j in
        let g : Fin k → F ≔ j ↦ sec (back j) .fst in
        let backinj : PathReflecting (Fin k) O back
          ≔ equivalence_injective (Fin k) O (id_to_equiv (Fin k) O (inverse Type O (Fin k) (w .snd))) in
        let ginj : PathReflecting (Fin k) F g
          ≔ j j' e ↦ backinj j j'
              (concat O (back j) (q (g j)) (back j') (sec (back j) .snd)
                (concat O (q (g j)) (q (g j')) (back j') (map_path F O q (g j) (g j') e)
                  (inverse O (back j') (q (g j')) (sec (back j') .snd)))) in
        let x0 : F ≔ inr. star. in
        let missing : ((i : F) → Id Bool (bsix_image_bool k (suc. n) g i) true.) → Empty
          ≔ all ↦
            let u ≔ decision_bool_reflect (Σ (Fin k) (j ↦ Id F x0 (g j))) (bsix_image_decidable k (suc. n) g x0) (all x0) in
            let v ≔ decision_bool_reflect (Σ (Fin k) (j ↦ Id F (f x0) (g j))) (bsix_image_decidable k (suc. n) g (f x0))
              (all (f x0)) in
            let same : Id O (q x0) (q (f x0)) ≔ quotient_encode F R x0 (f x0) (bsix_reach_step F f x0) in
            let ji : Id (Fin k) (u .fst) (v .fst)
              ≔ backinj (u .fst) (v .fst)
                  (concat O (back (u .fst)) (q (g (u .fst))) (back (v .fst)) (sec (back (u .fst)) .snd)
                    (concat O (q (g (u .fst))) (q x0) (back (v .fst))
                      (map_path F O q (g (u .fst)) x0 (inverse F x0 (g (u .fst)) (u .snd)))
                      (concat O (q x0) (q (f x0)) (back (v .fst)) same
                        (concat O (q (f x0)) (q (g (v .fst))) (back (v .fst))
                          (map_path F O q (f x0) (g (v .fst)) (v .snd))
                          (inverse O (back (v .fst)) (q (g (v .fst))) (sec (back (v .fst)) .snd)))))) in
            fpf x0 (concat F (f x0) (g (v .fst)) x0 (v .snd)
              (concat F (g (v .fst)) (g (u .fst)) x0
                (map_path (Fin k) F g (v .fst) (u .fst) (inverse (Fin k) (u .fst) (v .fst) ji))
                (inverse F x0 (g (u .fst)) (u .snd)))) in
        let tc ≔ true_count (suc. n) (bsix_image_bool k (suc. n) g) in
        (k, (transport Nat (c ↦ Le c n) tc k (bsix_image_count k (suc. n) g ginj)
              (bsix_bool_subset_bound n (bsix_image_bool k (suc. n) g) missing .snd .fst),
            mere (Id Type (Fin k) O) (inverse Type O (Fin k) (w .snd)))))
      (finite_quotient F (fin_is_finite (suc. n)) R (bsix_reach_relation_decidable F f mper dA))

{` Each orbit of an endomap of Fin (n+1) that is not transitive is a proper
   decidable subset. `}
def bsix_fin_orbit_elements_bound (n : Nat) (f : Fin (suc. n) → Fin (suc. n))
  (mper : (x : Fin (suc. n)) → Mere (BsixPeriod (Fin (suc. n)) f x)) (dA : DecidableEquality (Fin (suc. n)))
  (ntr : BsixTransitive (Fin (suc. n)) f → Empty) (o : BsixOrbits (Fin (suc. n)) f mper dA)
  : CardBound n (BsixOrbitElements (Fin (suc. n)) f mper dA o)
  ≔ let F ≔ Fin (suc. n) in
    let R ≔ bsix_reach_relation F f mper dA in
    let O ≔ BsixOrbits F f mper dA in
    let q ≔ bsix_orbit_class F f mper dA in
    let dO ≔ quotient_decidable_equality F R (bsix_reach_relation_decidable F f mper dA) in
    bsix_decidable_subset_bound n (a ↦ Id O o (q a)) (a ↦ quotient_set F R o (q a)) (a ↦ dO o (q a))
      (all ↦ ntr (y z ↦ quotient_effective F R y z .map
        (concat O (q y) o (q z) (inverse O o (q y) (all y)) (all z))))

{` Transport to an arbitrary (n+1)-element set. `}
def BsixImageBounds (n : Nat) (B : Type) : Type
  ≔ (f : B → B) → (PathReflecting B B f → Empty) → CardBound n (BsixImage B f)

def BsixOrbitsBounds (n : Nat) (B : Type) : Type
  ≔ (f : B → B) → ((y : B) → Id B (f y) y → Empty) → (mper : (x : B) → Mere (BsixPeriod B f x))
    → (dB : DecidableEquality B) → CardBound n (BsixOrbits B f mper dB)

def BsixOrbitElementsBounds (n : Nat) (B : Type) : Type
  ≔ (f : B → B) → (mper : (x : B) → Mere (BsixPeriod B f x)) → (dB : DecidableEquality B)
    → (BsixTransitive B f → Empty) → (o : BsixOrbits B f mper dB) → CardBound n (BsixOrbitElements B f mper dB o)

def bsix_image_bound (n : Nat) (A : Type) (p : Mere (Id Type (Fin (suc. n)) A)) (f : A → A)
  (ninj : PathReflecting A A f → Empty) : CardBound n (BsixImage A f)
  ≔ mere_rec (Id Type (Fin (suc. n)) A) (CardBound n (BsixImage A f)) (card_bound_prop n (BsixImage A f))
      (r ↦ transport Type (BsixImageBounds n) (Fin (suc. n)) A r (bsix_fin_image_bound n) f ninj) p

def bsix_orbits_bound (n : Nat) (A : Type) (p : Mere (Id Type (Fin (suc. n)) A)) (f : A → A)
  (fpf : (y : A) → Id A (f y) y → Empty) (mper : (x : A) → Mere (BsixPeriod A f x)) (dA : DecidableEquality A)
  : CardBound n (BsixOrbits A f mper dA)
  ≔ mere_rec (Id Type (Fin (suc. n)) A) (CardBound n (BsixOrbits A f mper dA)) (card_bound_prop n (BsixOrbits A f mper dA))
      (r ↦ transport Type (BsixOrbitsBounds n) (Fin (suc. n)) A r (bsix_fin_orbits_bound n) f fpf mper dA) p

def bsix_orbit_elements_bound (n : Nat) (A : Type) (p : Mere (Id Type (Fin (suc. n)) A)) (f : A → A)
  (mper : (x : A) → Mere (BsixPeriod A f x)) (dA : DecidableEquality A) (ntr : BsixTransitive A f → Empty)
  (o : BsixOrbits A f mper dA) : CardBound n (BsixOrbitElements A f mper dA o)
  ≔ mere_rec (Id Type (Fin (suc. n)) A) (CardBound n (BsixOrbitElements A f mper dA o))
      (card_bound_prop n (BsixOrbitElements A f mper dA o))
      (r ↦ transport Type (BsixOrbitElementsBounds n) (Fin (suc. n)) A r (bsix_fin_orbit_elements_bound n) f mper dA ntr o) p
