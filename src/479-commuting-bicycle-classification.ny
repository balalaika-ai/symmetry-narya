export "478-commuting-bicycles"

{` Corrected form of the exercise at group.tex 2146 (second part). The map
   Cyc × Cyc → Bicyc, ((X,t),(Y,u)) ↦ (X × Y, t × id, id × u), is an
   equivalence onto the SPLIT commuting bicycles: commuting bicycles
   (Z, a, b) such that aⁿ(bᵐ z) = z implies aⁿ z = z. (By module 478 it is not
   onto all commuting bicycles: (Bool, not, not) is commuting but not split.)
   The inverse sends (Z, a, b) to the cycles (Z/⟨b⟩, ā) and (Z/⟨a⟩, b̄) of
   orbits, with the induced permutations (set quotients of module 41). `}

{` Orbit quotients: classes, prop-valued induction, induced maps. `}
def bicycle_orbit_class (A : Type) (e : Equiv A A) (x : A) : OrbitQuotient A e
  ≔ quotient_class A (orbit_relation A e) x

def bicycle_orbit_set (A : Type) (e : Equiv A A) : isSet (OrbitQuotient A e)
  ≔ quotient_set A (orbit_relation A e)

def bicycle_orbit_ind_prop (A : Type) (e : Equiv A A) (P : OrbitQuotient A e → Type)
  (hP : (z : OrbitQuotient A e) → isProp (P z)) (base : (x : A) → P (bicycle_orbit_class A e x))
  (z : OrbitQuotient A e) : P z
  ≔ mere_rec (BookFiber A (OrbitQuotient A e) (bicycle_orbit_class A e) z) (P z) (hP z)
      (w ↦ transport (OrbitQuotient A e) P (bicycle_orbit_class A e (w .fst)) z
        (inverse (OrbitQuotient A e) z (bicycle_orbit_class A e (w .fst)) (w .snd)) (base (w .fst)))
      (quotient_surjective A (orbit_relation A e) z)

def bicycle_orbit_class_power (A : Type) (e : Equiv A A) (x : A) (n : Int)
  : Id (OrbitQuotient A e) (bicycle_orbit_class A e x) (bicycle_orbit_class A e (permutation_power A e n x))
  ≔ quotient_encode A (orbit_relation A e) x (permutation_power A e n x) (orbit_power A e x n)

def bicycle_orbit_induced (A : Type) (e : Equiv A A) (f : A → A) (hf : Commutes A A e e f)
  : OrbitQuotient A e → OrbitQuotient A e
  ≔ quotient_rec A (OrbitQuotient A e) (orbit_relation A e) (bicycle_orbit_set A e)
      (x ↦ bicycle_orbit_class A e (f x))
      (x y r ↦ quotient_encode A (orbit_relation A e) (f x) (f y) (same_orbit_map A A e e f hf x y r))

def bicycle_orbit_induced_equiv (A : Type) (e : Equiv A A) (g : Equiv A A) (hg : Commutes A A e e (g .map))
  : Equiv (OrbitQuotient A e) (OrbitQuotient A e)
  ≔ let Q ≔ OrbitQuotient A e in
    let ginv ≔ equiv_inverse_map A A g in
    let hginv : Commutes A A e e ginv ≔ bicycle_commutes_inverse A A e e g hg in
    let F ≔ bicycle_orbit_induced A e (g .map) hg in
    let G ≔ bicycle_orbit_induced A e ginv hginv in
    quasi_inverse_equiv Q Q F G
      (bicycle_orbit_ind_prop A e (z ↦ Id Q (G (F z)) z) (z ↦ bicycle_orbit_set A e (G (F z)) z)
        (x ↦ refl (bicycle_orbit_class A e) (equiv_retraction A A g x)))
      (bicycle_orbit_ind_prop A e (z ↦ Id Q (F (G z)) z) (z ↦ bicycle_orbit_set A e (F (G z)) z)
        (x ↦ refl (bicycle_orbit_class A e) (equiv_counit A A g x)))

def bicycle_orbit_induced_power (A : Type) (e : Equiv A A) (g : Equiv A A) (hg : Commutes A A e e (g .map))
  (n : Int) (x : A)
  : Id (OrbitQuotient A e) (bicycle_orbit_class A e (permutation_power A g n x))
      (permutation_power (OrbitQuotient A e) (bicycle_orbit_induced_equiv A e g hg) n (bicycle_orbit_class A e x))
  ≔ permutation_power_intertwine A (OrbitQuotient A e) g (bicycle_orbit_induced_equiv A e g hg) (bicycle_orbit_class A e)
      (y ↦ refl (bicycle_orbit_class A e (g .map y))) n x

{` The cycle (Z/⟨b⟩, ā) of a commuting bicycle (Z, a, b). `}
def commuting_orbit_generator (B : Bicycles) (hc : IsCommutingBicycle B)
  : Equiv (OrbitQuotient (bicycle_carrier B) (bicycle_b B)) (OrbitQuotient (bicycle_carrier B) (bicycle_b B))
  ≔ bicycle_orbit_induced_equiv (bicycle_carrier B) (bicycle_b B) (bicycle_a B) hc

def commuting_orbit_word (B : Bicycles) (hc : IsCommutingBicycle B) (z : bicycle_carrier B) (l : List (Sum Int Int))
  : SameOrbit (OrbitQuotient (bicycle_carrier B) (bicycle_b B)) (commuting_orbit_generator B hc)
      (bicycle_orbit_class (bicycle_carrier B) (bicycle_b B) z)
      (bicycle_orbit_class (bicycle_carrier B) (bicycle_b B) (bicycle_word_map B l z))
  ≔ let Z ≔ bicycle_carrier B in
    let Q ≔ OrbitQuotient Z (bicycle_b B) in
    let t ≔ commuting_orbit_generator B hc in
    let cl ≔ bicycle_orbit_class Z (bicycle_b B) in
    match l [
    | nil. ↦ same_orbit_refl Q t (cl z)
    | cons. (inl. n) k ↦ same_orbit_trans Q t (cl z) (cl (bicycle_word_map B k z))
        (cl (permutation_power Z (bicycle_a B) n (bicycle_word_map B k z)))
        (commuting_orbit_word B hc z k)
        (transport Q (ξ ↦ SameOrbit Q t (cl (bicycle_word_map B k z)) ξ)
          (permutation_power Q t n (cl (bicycle_word_map B k z)))
          (cl (permutation_power Z (bicycle_a B) n (bicycle_word_map B k z)))
          (inverse Q (cl (permutation_power Z (bicycle_a B) n (bicycle_word_map B k z)))
            (permutation_power Q t n (cl (bicycle_word_map B k z)))
            (bicycle_orbit_induced_power Z (bicycle_b B) (bicycle_a B) hc n (bicycle_word_map B k z)))
          (orbit_power Q t (cl (bicycle_word_map B k z)) n))
    | cons. (inr. n) k ↦ transport Q (ξ ↦ SameOrbit Q t (cl z) ξ)
        (cl (bicycle_word_map B k z)) (cl (permutation_power Z (bicycle_b B) n (bicycle_word_map B k z)))
        (bicycle_orbit_class_power Z (bicycle_b B) (bicycle_word_map B k z) n)
        (commuting_orbit_word B hc z k) ]

def commuting_orbit_cyclic (B : Bicycles) (hc : IsCommutingBicycle B)
  : Cyclic (OrbitQuotient (bicycle_carrier B) (bicycle_b B)) (commuting_orbit_generator B hc)
  ≔ let Z ≔ bicycle_carrier B in
    let Q ≔ OrbitQuotient Z (bicycle_b B) in
    let t ≔ commuting_orbit_generator B hc in
    let cl ≔ bicycle_orbit_class Z (bicycle_b B) in
    (mere_rec Z (Mere Q) (mere_isprop Q) (z ↦ mere Q (cl z)) (bicycle_connectivity B .fst),
     bicycle_orbit_ind_prop Z (bicycle_b B) (ξ ↦ (η : Q) → SameOrbit Q t ξ η)
       (ξ ↦ pi_prop Q (η ↦ SameOrbit Q t ξ η) (η ↦ same_orbit_prop Q t ξ η))
       (z ↦ bicycle_orbit_ind_prop Z (bicycle_b B) (η ↦ SameOrbit Q t (cl z) η) (η ↦ same_orbit_prop Q t (cl z) η)
         (z' ↦ mere_rec (BicycleWordFrom Z (bicycle_a B) (bicycle_b B) z z') (SameOrbit Q t (cl z) (cl z'))
           (same_orbit_prop Q t (cl z) (cl z'))
           (w ↦ transport Q (ξ ↦ SameOrbit Q t (cl z) ξ) (cl (bicycle_word_map B (w .fst) z)) (cl z')
             (inverse Q (cl z') (cl (bicycle_word_map B (w .fst) z)) (refl cl (w .snd)))
             (commuting_orbit_word B hc z (w .fst)))
           (bicycle_connectivity B .snd z z'))))

def commuting_orbit_cycle (B : Bicycles) (hc : IsCommutingBicycle B) : Cycles
  ≔ (((OrbitQuotient (bicycle_carrier B) (bicycle_b B), bicycle_orbit_set (bicycle_carrier B) (bicycle_b B)),
      commuting_orbit_generator B hc), commuting_orbit_cyclic B hc)

{` Swapping a and b. `}
def bicycle_word_swap (l : List (Sum Int Int)) : List (Sum Int Int)
  ≔ match l [
  | nil. ↦ nil.
  | cons. (inl. n) k ↦ cons. (inr. n) (bicycle_word_swap k)
  | cons. (inr. n) k ↦ cons. (inl. n) (bicycle_word_swap k) ]

def bicycle_word_swap_meaning (X : Type) (a b : Equiv X X) (l : List (Sum Int Int)) (x : X)
  : Id X (bicycle_meaning_map X b a (bicycle_word_swap l) x) (bicycle_meaning_map X a b l x)
  ≔ match l [
  | nil. ↦ refl x
  | cons. (inl. n) k ↦ refl (permutation_power X a n) (bicycle_word_swap_meaning X a b k x)
  | cons. (inr. n) k ↦ refl (permutation_power X b n) (bicycle_word_swap_meaning X a b k x) ]

def bicycle_swap (B : Bicycles) : Bicycles
  ≔ let X ≔ bicycle_carrier B in let a ≔ bicycle_a B in let b ≔ bicycle_b B in
    mkbicycle (bicycle_set B) b a
      (bicycle_connectivity B .fst,
       x x' ↦ mere_rec (BicycleWordFrom X a b x x') (Mere (BicycleWordFrom X b a x x'))
         (mere_isprop (BicycleWordFrom X b a x x'))
         (w ↦ mere (BicycleWordFrom X b a x x') (bicycle_word_swap (w .fst),
           concat X x' (bicycle_meaning_map X a b (w .fst) x) (bicycle_meaning_map X b a (bicycle_word_swap (w .fst)) x)
             (w .snd) (inverse X (bicycle_meaning_map X b a (bicycle_word_swap (w .fst)) x) (bicycle_meaning_map X a b (w .fst) x)
               (bicycle_word_swap_meaning X a b (w .fst) x))))
         (bicycle_connectivity B .snd x x'))

def bicycle_swap_commuting (B : Bicycles) (hc : IsCommutingBicycle B) : IsCommutingBicycle (bicycle_swap B)
  ≔ x ↦ inverse (bicycle_carrier B) (bicycle_a B .map (bicycle_b B .map x)) (bicycle_b B .map (bicycle_a B .map x)) (hc x)

{` The split condition. `}
def IsSplitBicycle (B : Bicycles) : Type
  ≔ (z : bicycle_carrier B) (n m : Int)
    → Id (bicycle_carrier B) (permutation_power (bicycle_carrier B) (bicycle_a B) n
          (permutation_power (bicycle_carrier B) (bicycle_b B) m z)) z
    → Id (bicycle_carrier B) (permutation_power (bicycle_carrier B) (bicycle_a B) n z) z

def is_split_bicycle_prop (B : Bicycles) : isProp (IsSplitBicycle B)
  ≔ let Z ≔ bicycle_carrier B in
    let a ≔ bicycle_a B in let b ≔ bicycle_b B in
    pi_prop Z (z ↦ (n m : Int) → Id Z (permutation_power Z a n (permutation_power Z b m z)) z → Id Z (permutation_power Z a n z) z)
      (z ↦ pi_prop Int (n ↦ (m : Int) → Id Z (permutation_power Z a n (permutation_power Z b m z)) z → Id Z (permutation_power Z a n z) z)
        (n ↦ pi_prop Int (m ↦ Id Z (permutation_power Z a n (permutation_power Z b m z)) z → Id Z (permutation_power Z a n z) z)
          (m ↦ pi_prop (Id Z (permutation_power Z a n (permutation_power Z b m z)) z) (_ ↦ Id Z (permutation_power Z a n z) z)
            (_ ↦ bicycle_carrier_set B (permutation_power Z a n z) z))))

def SplitCommutingBicycles : Type ≔ Σ Bicycles (B ↦ Product (IsCommutingBicycle B) (IsSplitBicycle B))

def split_commuting_prop (B : Bicycles) : isProp (Product (IsCommutingBicycle B) (IsSplitBicycle B))
  ≔ product_prop (IsCommutingBicycle B) (IsSplitBicycle B) (is_commuting_bicycle_prop B) (is_split_bicycle_prop B)

{` Litmus: (Bool, not, not) is not split. `}
def bool_double_not_split (h : IsSplitBicycle bool_double_bicycle) : Empty
  ≔ bool_not_no_fixed_point false. (h false. (pos. (suc. zero.)) (pos. (suc. zero.)) (refl (false. : Bool)))

{` The product bicycle is split. `}
def cycle_product_bicycle_split (c d : Cycles) : IsSplitBicycle (cycle_product_bicycle c d)
  ≔ let X ≔ cycle_carrier_type c in let Y ≔ cycle_carrier_type d in
    let t ≔ cycle_generator c in let u ≔ cycle_generator d in
    let P ≔ Product X Y in
    let A ≔ product_bicycle_a c d in let Bm ≔ product_bicycle_b c d in
    z n m h ↦
      let value : Id P (permutation_power P A n (permutation_power P Bm m z))
            (permutation_power X t n (z .fst), permutation_power Y u m (z .snd))
        ≔ concat P (permutation_power P A n (permutation_power P Bm m z))
            (permutation_power P A n (z .fst, permutation_power Y u m (z .snd)))
            (permutation_power X t n (z .fst), permutation_power Y u m (z .snd))
            (refl (permutation_power P A n) (product_right_power X Y u m (z .fst) (z .snd)))
            (product_left_power X Y t n (z .fst) (permutation_power Y u m (z .snd))) in
      let fixed : Id X (permutation_power X t n (z .fst)) (z .fst)
        ≔ (concat P (permutation_power X t n (z .fst), permutation_power Y u m (z .snd))
            (permutation_power P A n (permutation_power P Bm m z)) z
            (inverse P (permutation_power P A n (permutation_power P Bm m z))
              (permutation_power X t n (z .fst), permutation_power Y u m (z .snd)) value) h) .fst in
      concat P (permutation_power P A n z) (permutation_power X t n (z .fst), z .snd) z
        (product_left_power X Y t n (z .fst) (z .snd)) (fixed, refl (z .snd))

{` The map φ : Z → Z/⟨b⟩ × Z/⟨a⟩, z ↦ ([z], [z]), is an isomorphism of
   bicycles onto the product bicycle, for split commuting bicycles. `}
def commuting_orbit_cycle_pair (B : Bicycles) (hc : IsCommutingBicycle B) : Product Cycles Cycles
  ≔ (commuting_orbit_cycle B hc, commuting_orbit_cycle (bicycle_swap B) (bicycle_swap_commuting B hc))

def commuting_orbit_map (B : Bicycles) (hc : IsCommutingBicycle B) (z : bicycle_carrier B)
  : Product (OrbitQuotient (bicycle_carrier B) (bicycle_b B)) (OrbitQuotient (bicycle_carrier B) (bicycle_a B))
  ≔ (bicycle_orbit_class (bicycle_carrier B) (bicycle_b B) z, bicycle_orbit_class (bicycle_carrier B) (bicycle_a B) z)

def commuting_orbit_map_injective (B : Bicycles) (hc : IsCommutingBicycle B) (hs : IsSplitBicycle B)
  : PathReflecting (bicycle_carrier B)
      (Product (OrbitQuotient (bicycle_carrier B) (bicycle_b B)) (OrbitQuotient (bicycle_carrier B) (bicycle_a B)))
      (commuting_orbit_map B hc)
  ≔ let Z ≔ bicycle_carrier B in let a ≔ bicycle_a B in let b ≔ bicycle_b B in
    z z' p ↦
      mere_rec (OrbitWitness Z b z z') (Id Z z z') (bicycle_carrier_set B z z')
        (vb ↦ mere_rec (OrbitWitness Z a z z') (Id Z z z') (bicycle_carrier_set B z z')
          (va ↦ let n ≔ va .fst in let m ≔ vb .fst in
            let back : Id Z (permutation_power Z a (int_neg n) (permutation_power Z b m z)) z
              ≔ calc
                  permutation_power Z a (int_neg n) (permutation_power Z b m z)
                  = permutation_power Z a (int_neg n) z'
                    by refl (permutation_power Z a (int_neg n)) (inverse Z z' (permutation_power Z b m z) (vb .snd))
                  = permutation_power Z a (int_neg n) (permutation_power Z a n z)
                    by refl (permutation_power Z a (int_neg n)) (va .snd)
                  = z by permutation_power_inverse Z a n z ∎ in
            let fix : Id Z (permutation_power Z a (int_neg n) z) z ≔ hs z (int_neg n) m back in
            calc
              z = permutation_power Z a n (permutation_power Z a (int_neg n) z)
                by inverse Z (permutation_power Z a n (permutation_power Z a (int_neg n) z)) z
                  (permutation_power_inverse_other Z a n z)
              = permutation_power Z a n z by refl (permutation_power Z a n) fix
              = z' by inverse Z z' (permutation_power Z a n z) (va .snd) ∎)
          (quotient_effective Z (orbit_relation Z a) z z' .map (p .snd)))
        (quotient_effective Z (orbit_relation Z b) z z' .map (p .fst))

{` Every pair of classes ([z₁]_b, [⟦ℓ⟧z₁]_a) is hit, by list induction. `}
def commuting_orbit_word_preimage (B : Bicycles) (hc : IsCommutingBicycle B) (z1 : bicycle_carrier B)
  (l : List (Sum Int Int))
  : Σ (bicycle_carrier B) (w ↦ Product
      (Id (OrbitQuotient (bicycle_carrier B) (bicycle_b B))
        (bicycle_orbit_class (bicycle_carrier B) (bicycle_b B) w) (bicycle_orbit_class (bicycle_carrier B) (bicycle_b B) z1))
      (Id (OrbitQuotient (bicycle_carrier B) (bicycle_a B))
        (bicycle_orbit_class (bicycle_carrier B) (bicycle_a B) w)
        (bicycle_orbit_class (bicycle_carrier B) (bicycle_a B) (bicycle_word_map B l z1))))
  ≔ let Z ≔ bicycle_carrier B in let a ≔ bicycle_a B in let b ≔ bicycle_b B in
    let Qb ≔ OrbitQuotient Z b in let Qa ≔ OrbitQuotient Z a in
    let clb ≔ bicycle_orbit_class Z b in let cla ≔ bicycle_orbit_class Z a in
    let hc' ≔ bicycle_swap_commuting B hc in
    match l [
    | nil. ↦ (z1, (refl (clb z1), refl (cla z1)))
    | cons. (inl. n) k ↦
        let r ≔ commuting_orbit_word_preimage B hc z1 k in
        (r .fst, (r .snd .fst,
          concat Qa (cla (r .fst)) (cla (bicycle_word_map B k z1)) (cla (permutation_power Z a n (bicycle_word_map B k z1)))
            (r .snd .snd) (bicycle_orbit_class_power Z a (bicycle_word_map B k z1) n)))
    | cons. (inr. n) k ↦
        let r ≔ commuting_orbit_word_preimage B hc z1 k in
        let bbar ≔ bicycle_orbit_induced_equiv Z a b hc' in
        (permutation_power Z b n (r .fst),
         (concat Qb (clb (permutation_power Z b n (r .fst))) (clb (r .fst)) (clb z1)
            (inverse Qb (clb (r .fst)) (clb (permutation_power Z b n (r .fst))) (bicycle_orbit_class_power Z b (r .fst) n))
            (r .snd .fst),
          calc
            cla (permutation_power Z b n (r .fst))
            = permutation_power Qa bbar n (cla (r .fst)) by bicycle_orbit_induced_power Z a b hc' n (r .fst)
            = permutation_power Qa bbar n (cla (bicycle_word_map B k z1)) by refl (permutation_power Qa bbar n) (r .snd .snd)
            = cla (permutation_power Z b n (bicycle_word_map B k z1))
              by inverse Qa (cla (permutation_power Z b n (bicycle_word_map B k z1)))
                (permutation_power Qa bbar n (cla (bicycle_word_map B k z1)))
                (bicycle_orbit_induced_power Z a b hc' n (bicycle_word_map B k z1)) ∎)) ]

def commuting_orbit_map_surjective (B : Bicycles) (hc : IsCommutingBicycle B)
  : Surjective (bicycle_carrier B)
      (Product (OrbitQuotient (bicycle_carrier B) (bicycle_b B)) (OrbitQuotient (bicycle_carrier B) (bicycle_a B)))
      (commuting_orbit_map B hc)
  ≔ let Z ≔ bicycle_carrier B in let a ≔ bicycle_a B in let b ≔ bicycle_b B in
    let Qb ≔ OrbitQuotient Z b in let Qa ≔ OrbitQuotient Z a in
    let clb ≔ bicycle_orbit_class Z b in let cla ≔ bicycle_orbit_class Z a in
    let P ≔ Product Qb Qa in
    let F ≔ BookFiber Z P (commuting_orbit_map B hc) in
    pq ↦ bicycle_orbit_ind_prop Z b (ξ ↦ (η : Qa) → Mere (F (ξ, η)))
      (ξ ↦ pi_prop Qa (η ↦ Mere (F (ξ, η))) (η ↦ mere_isprop (F (ξ, η))))
      (z1 ↦ bicycle_orbit_ind_prop Z a (η ↦ Mere (F (clb z1, η))) (η ↦ mere_isprop (F (clb z1, η)))
        (z2 ↦ mere_rec (BicycleWordFrom Z a b z1 z2) (Mere (F (clb z1, cla z2))) (mere_isprop (F (clb z1, cla z2)))
          (w ↦ let r ≔ commuting_orbit_word_preimage B hc z1 (w .fst) in
            mere (F (clb z1, cla z2)) (r .fst,
              (inverse Qb (clb (r .fst)) (clb z1) (r .snd .fst),
               concat Qa (cla z2) (cla (bicycle_word_map B (w .fst) z1)) (cla (r .fst))
                 (refl cla (w .snd)) (inverse Qa (cla (r .fst)) (cla (bicycle_word_map B (w .fst) z1)) (r .snd .snd)))))
          (bicycle_connectivity B .snd z1 z2)))
      (pq .fst) (pq .snd)

def commuting_orbit_iso (B : Bicycles) (hc : IsCommutingBicycle B) (hs : IsSplitBicycle B)
  : BicycleIsomorphisms B
      (cycle_product_bicycle (commuting_orbit_cycle_pair B hc .fst) (commuting_orbit_cycle_pair B hc .snd))
  ≔ let Z ≔ bicycle_carrier B in let a ≔ bicycle_a B in let b ≔ bicycle_b B in
    let Qb ≔ OrbitQuotient Z b in let Qa ≔ OrbitQuotient Z a in
    let P ≔ Product Qb Qa in
    (set_bijection_equiv Z P
        (sigma_set Qb (_ ↦ Qa) (bicycle_orbit_set Z b) (_ ↦ bicycle_orbit_set Z a))
        (commuting_orbit_map B hc) (commuting_orbit_map_injective B hc hs) (commuting_orbit_map_surjective B hc),
      (z ↦ (refl (bicycle_orbit_class Z b (a .map z)),
            inverse Qa (bicycle_orbit_class Z a z) (bicycle_orbit_class Z a (a .map z))
              (bicycle_orbit_class_power Z a z (pos. (suc. zero.)))),
       z ↦ (inverse Qb (bicycle_orbit_class Z b z) (bicycle_orbit_class Z b (b .map z))
              (bicycle_orbit_class_power Z b z (pos. (suc. zero.))),
            refl (bicycle_orbit_class Z a (b .map z)))))

{` The cycles of a product bicycle are the factors: (X × Y)/⟨id × u⟩ ≃ X via
   the first projection (commuting with t), and (X × Y)/⟨t × id⟩ ≃ Y. `}
def product_orbit_first_respects (c d : Cycles)
  : Respects (Product (cycle_carrier_type c) (cycle_carrier_type d)) (cycle_carrier_type c)
      (orbit_relation (Product (cycle_carrier_type c) (cycle_carrier_type d)) (product_bicycle_b c d)) (p ↦ p .fst)
  ≔ let X ≔ cycle_carrier_type c in let Y ≔ cycle_carrier_type d in let P ≔ Product X Y in
    p p' r ↦ mere_rec (OrbitWitness P (product_bicycle_b c d) p p') (Id X (p .fst) (p' .fst)) (cycle_carrier_is_set c (p .fst) (p' .fst))
      (w ↦ inverse X (p' .fst) (p .fst)
        (concat P p' (permutation_power P (product_bicycle_b c d) (w .fst) p) (p .fst, permutation_power Y (cycle_generator d) (w .fst) (p .snd))
          (w .snd) (product_right_power X Y (cycle_generator d) (w .fst) (p .fst) (p .snd)) .fst)) r

def product_orbit_first_reflects (c d : Cycles) (p p' : Product (cycle_carrier_type c) (cycle_carrier_type d))
  (q : Id (cycle_carrier_type c) (p .fst) (p' .fst))
  : Rel (Product (cycle_carrier_type c) (cycle_carrier_type d))
      (orbit_relation (Product (cycle_carrier_type c) (cycle_carrier_type d)) (product_bicycle_b c d)) p p'
  ≔ let X ≔ cycle_carrier_type c in let Y ≔ cycle_carrier_type d in let P ≔ Product X Y in
    mere_rec (OrbitWitness Y (cycle_generator d) (p .snd) (p' .snd)) (SameOrbit P (product_bicycle_b c d) p p')
      (same_orbit_prop P (product_bicycle_b c d) p p')
      (w ↦ mere (OrbitWitness P (product_bicycle_b c d) p p') (w .fst,
        concat P p' (p .fst, permutation_power Y (cycle_generator d) (w .fst) (p .snd))
          (permutation_power P (product_bicycle_b c d) (w .fst) p)
          (inverse X (p .fst) (p' .fst) q, w .snd)
          (inverse P (permutation_power P (product_bicycle_b c d) (w .fst) p) (p .fst, permutation_power Y (cycle_generator d) (w .fst) (p .snd))
            (product_right_power X Y (cycle_generator d) (w .fst) (p .fst) (p .snd)))))
      (d .snd .snd (p .snd) (p' .snd))

def product_first_surjective (c d : Cycles)
  : Surjective (Product (cycle_carrier_type c) (cycle_carrier_type d)) (cycle_carrier_type c) (p ↦ p .fst)
  ≔ x ↦ mere_rec (cycle_carrier_type d)
      (Mere (BookFiber (Product (cycle_carrier_type c) (cycle_carrier_type d)) (cycle_carrier_type c) (p ↦ p .fst) x))
      (mere_isprop (BookFiber (Product (cycle_carrier_type c) (cycle_carrier_type d)) (cycle_carrier_type c) (p ↦ p .fst) x))
      (y ↦ mere (BookFiber (Product (cycle_carrier_type c) (cycle_carrier_type d)) (cycle_carrier_type c) (p ↦ p .fst) x)
        ((x, y), refl x))
      (d .snd .fst)

def product_orbit_first_equiv (c d : Cycles)
  : Equiv (OrbitQuotient (Product (cycle_carrier_type c) (cycle_carrier_type d)) (product_bicycle_b c d)) (cycle_carrier_type c)
  ≔ quotient_presentation_equiv (Product (cycle_carrier_type c) (cycle_carrier_type d)) (cycle_carrier_type c)
      (orbit_relation (Product (cycle_carrier_type c) (cycle_carrier_type d)) (product_bicycle_b c d))
      (cycle_carrier_is_set c) (p ↦ p .fst) (product_orbit_first_respects c d) (product_orbit_first_reflects c d)
      (product_first_surjective c d)

def product_orbit_first_path (c d : Cycles)
  : Id Cycles (commuting_orbit_cycle (cycle_product_bicycle c d) (cycle_product_bicycle_commuting c d)) c
  ≔ let X ≔ cycle_carrier_type c in let Y ≔ cycle_carrier_type d in let P ≔ Product X Y in
    let Bp ≔ cycle_product_bicycle c d in
    equiv_inverse_map (Id Cycles (commuting_orbit_cycle Bp (cycle_product_bicycle_commuting c d)) c)
      (PermutationIsomorphisms (commuting_orbit_cycle Bp (cycle_product_bicycle_commuting c d) .fst) (c .fst))
      (cycle_paths_equiv (commuting_orbit_cycle Bp (cycle_product_bicycle_commuting c d)) c)
      (product_orbit_first_equiv c d,
       bicycle_orbit_ind_prop P (product_bicycle_b c d)
         (ξ ↦ Id X (product_orbit_first_equiv c d .map (commuting_orbit_generator Bp (cycle_product_bicycle_commuting c d) .map ξ))
           (cycle_generator c .map (product_orbit_first_equiv c d .map ξ)))
         (ξ ↦ cycle_carrier_is_set c
           (product_orbit_first_equiv c d .map (commuting_orbit_generator Bp (cycle_product_bicycle_commuting c d) .map ξ))
           (cycle_generator c .map (product_orbit_first_equiv c d .map ξ)))
         (p ↦ refl (cycle_generator c .map (p .fst))))

def product_orbit_second_respects (c d : Cycles)
  : Respects (Product (cycle_carrier_type c) (cycle_carrier_type d)) (cycle_carrier_type d)
      (orbit_relation (Product (cycle_carrier_type c) (cycle_carrier_type d)) (product_bicycle_a c d)) (p ↦ p .snd)
  ≔ let X ≔ cycle_carrier_type c in let Y ≔ cycle_carrier_type d in let P ≔ Product X Y in
    p p' r ↦ mere_rec (OrbitWitness P (product_bicycle_a c d) p p') (Id Y (p .snd) (p' .snd)) (cycle_carrier_is_set d (p .snd) (p' .snd))
      (w ↦ inverse Y (p' .snd) (p .snd)
        (concat P p' (permutation_power P (product_bicycle_a c d) (w .fst) p) (permutation_power X (cycle_generator c) (w .fst) (p .fst), p .snd)
          (w .snd) (product_left_power X Y (cycle_generator c) (w .fst) (p .fst) (p .snd)) .snd)) r

def product_orbit_second_reflects (c d : Cycles) (p p' : Product (cycle_carrier_type c) (cycle_carrier_type d))
  (q : Id (cycle_carrier_type d) (p .snd) (p' .snd))
  : Rel (Product (cycle_carrier_type c) (cycle_carrier_type d))
      (orbit_relation (Product (cycle_carrier_type c) (cycle_carrier_type d)) (product_bicycle_a c d)) p p'
  ≔ let X ≔ cycle_carrier_type c in let Y ≔ cycle_carrier_type d in let P ≔ Product X Y in
    mere_rec (OrbitWitness X (cycle_generator c) (p .fst) (p' .fst)) (SameOrbit P (product_bicycle_a c d) p p')
      (same_orbit_prop P (product_bicycle_a c d) p p')
      (w ↦ mere (OrbitWitness P (product_bicycle_a c d) p p') (w .fst,
        concat P p' (permutation_power X (cycle_generator c) (w .fst) (p .fst), p .snd)
          (permutation_power P (product_bicycle_a c d) (w .fst) p)
          (w .snd, inverse Y (p .snd) (p' .snd) q)
          (inverse P (permutation_power P (product_bicycle_a c d) (w .fst) p) (permutation_power X (cycle_generator c) (w .fst) (p .fst), p .snd)
            (product_left_power X Y (cycle_generator c) (w .fst) (p .fst) (p .snd)))))
      (c .snd .snd (p .fst) (p' .fst))

def product_second_surjective (c d : Cycles)
  : Surjective (Product (cycle_carrier_type c) (cycle_carrier_type d)) (cycle_carrier_type d) (p ↦ p .snd)
  ≔ y ↦ mere_rec (cycle_carrier_type c)
      (Mere (BookFiber (Product (cycle_carrier_type c) (cycle_carrier_type d)) (cycle_carrier_type d) (p ↦ p .snd) y))
      (mere_isprop (BookFiber (Product (cycle_carrier_type c) (cycle_carrier_type d)) (cycle_carrier_type d) (p ↦ p .snd) y))
      (x ↦ mere (BookFiber (Product (cycle_carrier_type c) (cycle_carrier_type d)) (cycle_carrier_type d) (p ↦ p .snd) y)
        ((x, y), refl y))
      (c .snd .fst)

def product_orbit_second_equiv (c d : Cycles)
  : Equiv (OrbitQuotient (Product (cycle_carrier_type c) (cycle_carrier_type d)) (product_bicycle_a c d)) (cycle_carrier_type d)
  ≔ quotient_presentation_equiv (Product (cycle_carrier_type c) (cycle_carrier_type d)) (cycle_carrier_type d)
      (orbit_relation (Product (cycle_carrier_type c) (cycle_carrier_type d)) (product_bicycle_a c d))
      (cycle_carrier_is_set d) (p ↦ p .snd) (product_orbit_second_respects c d) (product_orbit_second_reflects c d)
      (product_second_surjective c d)

def product_orbit_second_path (c d : Cycles)
  : Id Cycles (commuting_orbit_cycle (bicycle_swap (cycle_product_bicycle c d))
      (bicycle_swap_commuting (cycle_product_bicycle c d) (cycle_product_bicycle_commuting c d))) d
  ≔ let X ≔ cycle_carrier_type c in let Y ≔ cycle_carrier_type d in let P ≔ Product X Y in
    let Bs ≔ bicycle_swap (cycle_product_bicycle c d) in
    let hs ≔ bicycle_swap_commuting (cycle_product_bicycle c d) (cycle_product_bicycle_commuting c d) in
    equiv_inverse_map (Id Cycles (commuting_orbit_cycle Bs hs) d)
      (PermutationIsomorphisms (commuting_orbit_cycle Bs hs .fst) (d .fst))
      (cycle_paths_equiv (commuting_orbit_cycle Bs hs) d)
      (product_orbit_second_equiv c d,
       bicycle_orbit_ind_prop P (product_bicycle_a c d)
         (ξ ↦ Id Y (product_orbit_second_equiv c d .map (commuting_orbit_generator Bs hs .map ξ))
           (cycle_generator d .map (product_orbit_second_equiv c d .map ξ)))
         (ξ ↦ cycle_carrier_is_set d
           (product_orbit_second_equiv c d .map (commuting_orbit_generator Bs hs .map ξ))
           (cycle_generator d .map (product_orbit_second_equiv c d .map ξ)))
         (p ↦ refl (cycle_generator d .map (p .snd))))

{` The corrected statement: Cyc × Cyc ≃ split commuting bicycles, with
   underlying map ((X,t),(Y,u)) ↦ (X × Y, t × id, id × u). `}
def cycles_to_split_bicycles (cd : Product Cycles Cycles) : SplitCommutingBicycles
  ≔ (cycle_product_bicycle (cd .fst) (cd .snd),
      (cycle_product_bicycle_commuting (cd .fst) (cd .snd), cycle_product_bicycle_split (cd .fst) (cd .snd)))

def split_bicycles_to_cycles (S : SplitCommutingBicycles) : Product Cycles Cycles
  ≔ commuting_orbit_cycle_pair (S .fst) (S .snd .fst)

def cycles_split_bicycles_roundtrip (cd : Product Cycles Cycles)
  : Id (Product Cycles Cycles) (split_bicycles_to_cycles (cycles_to_split_bicycles cd)) cd
  ≔ (product_orbit_first_path (cd .fst) (cd .snd), product_orbit_second_path (cd .fst) (cd .snd))

def split_bicycles_cycles_roundtrip (S : SplitCommutingBicycles)
  : Id SplitCommutingBicycles (cycles_to_split_bicycles (split_bicycles_to_cycles S)) S
  ≔ subtype_equal Bicycles (B ↦ Product (IsCommutingBicycle B) (IsSplitBicycle B)) split_commuting_prop
      (cycles_to_split_bicycles (split_bicycles_to_cycles S)) S
      (inverse Bicycles (S .fst) (cycles_to_split_bicycles (split_bicycles_to_cycles S) .fst)
        (bicycle_path_from_iso (S .fst) (cycles_to_split_bicycles (split_bicycles_to_cycles S) .fst)
          (commuting_orbit_iso (S .fst) (S .snd .fst) (S .snd .snd))))

def cycle_pairs_split_bicycles_equiv : Equiv (Product Cycles Cycles) SplitCommutingBicycles
  ≔ quasi_inverse_equiv (Product Cycles Cycles) SplitCommutingBicycles
      cycles_to_split_bicycles split_bicycles_to_cycles cycles_split_bicycles_roundtrip split_bicycles_cycles_roundtrip

def cycle_pairs_split_bicycles_book_equiv : BookEquiv (Product Cycles Cycles) SplitCommutingBicycles
  ≔ book_equivalence (Product Cycles Cycles) SplitCommutingBicycles cycle_pairs_split_bicycles_equiv
