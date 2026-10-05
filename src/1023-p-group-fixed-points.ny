export "1022-gset-orbit-partition"
export "1003-finite-sum-congruences"

{` Chapter 10, lem:fixedptsize (fingp.tex 111): a group G of cardinality
   p^n acting on a finite set X. Every orbit of a non-fixed point has
   cardinality dividing p^n and different from 1, hence divisible by p
   (p prime), so p divides the number of non-fixed points and
   |X(sh_G)| ≡ |X^G| (mod p). The book's statement is the case p | |X|.

   Deviations: the hypotheses "n positive" and "X non-empty" of the printed
   lemma are not needed (for n = 0 every point is fixed; the empty G-set has
   no fixed points and p | 0); they are kept in the literal statement
   fixed_point_size. The finiteness of X^G ≔ Π_{z:BG} X(z), taken for
   granted in the book, is proved: X^G ≃ {x | ∀g, g·x = x} by evaluation at
   sh_G (module 563), a decidable subset of X(sh_G). `}

def gset_orbit_quotient_decidable_equality (G : Group) (hG : IsFiniteGroup G) (X : GSet G)
  (dX : DecidableEquality (gset_underlying G X)) : DecidableEquality (GSetOrbitQuotient G X)
  ≔ quotient_decidable_equality (gset_underlying G X) (gset_orbit_equivalence G X)
      (gset_orbit_relation_decidable G hG X dX)

def gset_nonfixed_fiber_finite (G : Group) (hG : IsFiniteGroup G) (X : GSet G) (hX : IsFiniteGSet G X)
  (q : GSetOrbitQuotient G X) : IsFinite (GSetNonFixedFiber G X q)
  ≔ let Y ≔ gset_underlying G X in
    let R ≔ gset_orbit_equivalence G X in
    let dQ ≔ gset_orbit_quotient_decidable_equality G hG X (finite_decidable_equality Y hX) in
    finite_decidable_subset (GSetNonFixedPoints G X) (gset_nonfixed_points_finite G hG X hX)
      (u ↦ Id (GSetOrbitQuotient G X) q (gset_nonfixed_class G X u))
      (u ↦ quotient_set Y R q (gset_nonfixed_class G X u))
      (u ↦ dQ q (gset_nonfixed_class G X u))

{` Over the class of x the fiber has cardinality divisible by p. `}
def p_group_fiber_divisible_at (p : Nat) (hp : NatIsPrime p) (n : Nat) (G : Group) (hG : IsFiniteGroup G)
  (hc : Id Nat (group_card G hG) (nat_power p n)) (X : GSet G) (hX : IsFiniteGSet G X) (x : gset_underlying G X)
  : NatDivides p (cardinality
      (GSetNonFixedFiber G X (quotient_class (gset_underlying G X) (gset_orbit_equivalence G X) x))
      (gset_nonfixed_fiber_finite G hG X hX (quotient_class (gset_underlying G X) (gset_orbit_equivalence G X) x)))
  ≔ let Y ≔ gset_underlying G X in
    let R ≔ gset_orbit_equivalence G X in
    let W ≔ GSetNonFixedFiber G X (quotient_class Y R x) in
    let hW ≔ gset_nonfixed_fiber_finite G hG X hX (quotient_class Y R x) in
    match gset_fixed_decidable G hG X (finite_decidable_equality Y hX) x [
    | inl. f ↦ transport Nat (NatDivides p) zero. (cardinality W hW)
        (inverse Nat (cardinality W hW) zero.
          (finite_empty_cardinality W hW (gset_nonfixed_fiber_fixed_empty G X x f)))
        (nat_divides_zero p)
    | inr. nf ↦
      let O ≔ GSetOrbitSet G X x in
      let hO ≔ gset_orbit_set_finite G hG X hX x in
      let d ≔ cardinality O hO in
      let dv : NatDivides d (nat_power p n)
        ≔ transport Nat (NatDivides d) (group_card G hG) (nat_power p n) hc (gset_orbit_card_divides G hG X hX x) in
      let pd : NatDivides p d
        ≔ prime_power_divisor_nontrivial p hp n d dv (e ↦ nf (gset_orbit_card_one_fixed G hG X hX x e)) in
      transport Nat (NatDivides p) d (cardinality W hW)
        (inverse Nat (cardinality W hW) d (cardinality_equiv W O (gset_nonfixed_fiber_orbit_equiv G X x nf) hW hO)) pd ]

{` p divides the number of non-fixed points. `}
def p_group_nonfixed_divisible (p : Nat) (hp : NatIsPrime p) (n : Nat) (G : Group) (hG : IsFiniteGroup G)
  (hc : Id Nat (group_card G hG) (nat_power p n)) (X : GSet G) (hX : IsFiniteGSet G X)
  : NatDivides p (cardinality (GSetNonFixedPoints G X) (gset_nonfixed_points_finite G hG X hX))
  ≔ let Y ≔ gset_underlying G X in
    let R ≔ gset_orbit_equivalence G X in
    let Q ≔ GSetOrbitQuotient G X in
    let hQ ≔ gset_orbit_quotient_finite G hG X hX in
    let F : Q → Type ≔ GSetNonFixedFiber G X in
    let hF : (q : Q) → IsFinite (F q) ≔ gset_nonfixed_fiber_finite G hG X hX in
    let N ≔ GSetNonFixedPoints G X in
    let hN ≔ gset_nonfixed_points_finite G hG X hX in
    let E ≔ gset_nonfixed_sum_equiv G X in
    let hS ≔ finite_of_equiv (Σ Q F) N E hN in
    transport Nat (NatDivides p) (cardinality (Σ Q F) hS) (cardinality N hN) (cardinality_equiv (Σ Q F) N E hS hN)
      (cardinality_sigma_divisible Q hQ F hF hS p
        (q ↦ mere_rec (BookFiber Y Q (quotient_class Y R) q) (NatDivides p (cardinality (F q) (hF q)))
          (nat_divides_prop p (cardinality (F q) (hF q)))
          (w ↦ transport Q (q' ↦ NatDivides p (cardinality (F q') (hF q'))) (quotient_class Y R (w .fst)) q
            (inverse Q q (quotient_class Y R (w .fst)) (w .snd))
            (p_group_fiber_divisible_at p hp n G hG hc X hX (w .fst)))
          (quotient_surjective Y R q)))

{` |X(sh_G)| ≡ |X^G| (mod p) for |G| = p^n, in the form
   |X(sh_G)| = |fixed points| + k·p. `}
def p_group_fixed_point_congruence (p : Nat) (hp : NatIsPrime p) (n : Nat) (G : Group) (hG : IsFiniteGroup G)
  (hc : Id Nat (group_card G hG) (nat_power p n)) (X : GSet G) (hX : IsFiniteGSet G X)
  : NatCongruent p (gset_card G X hX) (cardinality (GSetFixedPoints G X) (gset_fixed_points_finite G hG X hX))
  ≔ let nF ≔ cardinality (GSetFixedPoints G X) (gset_fixed_points_finite G hG X hX) in
    let nN ≔ cardinality (GSetNonFixedPoints G X) (gset_nonfixed_points_finite G hG X hX) in
    mere_rec (Σ Nat (k ↦ Id Nat nN (mul k p))) (NatCongruent p (gset_card G X hX) nF)
      (nat_congruent_prop p (gset_card G X hX) nF)
      (w ↦ nat_congruent_intro p (gset_card G X hX) nF (w .fst)
        (concat Nat (gset_card G X hX) (add nF nN) (add nF (mul (w .fst) p))
          (gset_fixed_split_card G hG X hX) (refl (add nF) (w .snd))))
      (p_group_nonfixed_divisible p hp n G hG hc X hX)

{` The core of lem:fixedptsize: p | |X(sh_G)| ⇒ p | |fixed points|. `}
def p_group_fixed_points_divisible (p : Nat) (hp : NatIsPrime p) (n : Nat) (G : Group) (hG : IsFiniteGroup G)
  (hc : Id Nat (group_card G hG) (nat_power p n)) (X : GSet G) (hX : IsFiniteGSet G X)
  (hd : NatDivides p (gset_card G X hX))
  : NatDivides p (cardinality (GSetFixedPoints G X) (gset_fixed_points_finite G hG X hX))
  ≔ nat_congruent_divides p (cardinality (GSetFixedPoints G X) (gset_fixed_points_finite G hG X hX)) (gset_card G X hX)
      (nat_congruent_sym p (gset_card G X hX) (cardinality (GSetFixedPoints G X) (gset_fixed_points_finite G hG X hX))
        (p_group_fixed_point_congruence p hp n G hG hc X hX))
      hd

{` X^G ≔ Π_{z:BG} X(z) is finite with the same cardinality as the fixed points. `}
def invariant_maps_finite (G : Group) (hG : IsFiniteGroup G) (X : GSet G) (hX : IsFiniteGSet G X)
  : IsFinite (InvariantMaps G X)
  ≔ finite_of_equiv (InvariantMaps G X) (GSetFixedPoints G X) (invariant_maps_fixed_equiv G X)
      (gset_fixed_points_finite G hG X hX)

def invariant_maps_card (G : Group) (hG : IsFiniteGroup G) (X : GSet G) (hX : IsFiniteGSet G X)
  : Id Nat (cardinality (InvariantMaps G X) (invariant_maps_finite G hG X hX))
      (cardinality (GSetFixedPoints G X) (gset_fixed_points_finite G hG X hX))
  ≔ cardinality_equiv (InvariantMaps G X) (GSetFixedPoints G X) (invariant_maps_fixed_equiv G X)
      (invariant_maps_finite G hG X hX) (gset_fixed_points_finite G hG X hX)

{` lem:fixedptsize, as printed (with the unused hypotheses n > 0 and X
   non-empty): if |G| = p^n and p | |X(sh_G)| then X^G is finite and p
   divides its cardinality. `}
def fixed_point_size (p : Nat) (hp : NatIsPrime p) (n : Nat) (hn : Lt zero. n) (G : Group) (hG : IsFiniteGroup G)
  (hc : Id Nat (group_card G hG) (nat_power p n)) (X : GSet G) (hne : Mere (gset_underlying G X))
  (hX : IsFiniteGSet G X) (hd : NatDivides p (gset_card G X hX))
  : Σ (IsFinite (InvariantMaps G X)) (h ↦ NatDivides p (cardinality (InvariantMaps G X) h))
  ≔ (invariant_maps_finite G hG X hX,
     transport Nat (NatDivides p) (cardinality (GSetFixedPoints G X) (gset_fixed_points_finite G hG X hX))
       (cardinality (InvariantMaps G X) (invariant_maps_finite G hG X hX))
       (inverse Nat (cardinality (InvariantMaps G X) (invariant_maps_finite G hG X hX))
         (cardinality (GSetFixedPoints G X) (gset_fixed_points_finite G hG X hX)) (invariant_maps_card G hG X hX))
       (p_group_fixed_points_divisible p hp n G hG hc X hX hd))

{` A finite type of non-zero cardinality is inhabited. `}
def fingp_fin_nonzero_inhabited (A : Type) (n : Nat) : Not (Id Nat n zero.) → Id Type (Fin n) A → Mere A
  ≔ match n [
  | zero. ↦ e _ ↦ absurd (Mere A) (e (refl (zero. : Nat)))
  | suc. k ↦ _ r ↦ mere A (id_to_equiv (Fin (suc. k)) A r .map (inr. star.)) ]

def finite_card_nonzero_inhabited (A : Type) (h : IsFinite A) (ne : Not (Id Nat (cardinality A h) zero.)) : Mere A
  ≔ mere_rec (Id Type A (Fin (cardinality A h))) (Mere A) (mere_isprop A)
      (q ↦ fingp_fin_nonzero_inhabited A (cardinality A h) ne (inverse Type A (Fin (cardinality A h)) q))
      (cardinality_spec A h)

{` If p does not divide |X(sh_G)| there is a fixed point (used for Sylow). `}
def p_group_fixed_point_exists (p : Nat) (hp : NatIsPrime p) (n : Nat) (G : Group) (hG : IsFiniteGroup G)
  (hc : Id Nat (group_card G hG) (nat_power p n)) (X : GSet G) (hX : IsFiniteGSet G X)
  (nd : Not (NatDivides p (gset_card G X hX))) : Mere (GSetFixedPoints G X)
  ≔ let hF ≔ gset_fixed_points_finite G hG X hX in
    finite_card_nonzero_inhabited (GSetFixedPoints G X) hF
      (z ↦ nd (nat_congruent_divides p (gset_card G X hX) (cardinality (GSetFixedPoints G X) hF)
        (p_group_fixed_point_congruence p hp n G hG hc X hX)
        (transport Nat (NatDivides p) zero. (cardinality (GSetFixedPoints G X) hF)
          (inverse Nat (cardinality (GSetFixedPoints G X) hF) zero. z) (nat_divides_zero p))))
