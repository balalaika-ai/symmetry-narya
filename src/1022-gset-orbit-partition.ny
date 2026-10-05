export "1021-lagrange-counting"
export "563-gset-fixed-points"

{` Chapter 10, sec. Cauchy's theorem, the counting behind lem:fixedptsize:
   for a finite group G and a finite G-set X, the underlying set X(sh_G)
   splits into the fixed points and the non-fixed points, the orbit
   relation on X(sh_G) is decidable, the non-fixed points are the sum of
   the fibers of the class map into the (finite) set of orbits, every such
   fiber is empty or the underlying set of the orbit X_[x] of a non-fixed
   point x, and |X_[x](sh_G)| · |G_x| = |G| with |X_[x](sh_G)| = 1 only
   for fixed x. The orbits are the classes of the equivalence relation
   ‖(sh_G, x) = (sh_G, y)‖, the orbit G-subset of module 503. `}

{` A decidable family splits a type into a sum. `}
def fingp_split_to (A : Type) (P : A → Type) (a : A) (da : Decidable (P a))
  : Sum (Σ A P) (Σ A (b ↦ Not (P b)))
  ≔ match da [ inl. p ↦ inl. (a, p) | inr. np ↦ inr. (a, np) ]

def fingp_split_from (A : Type) (P : A → Type) : Sum (Σ A P) (Σ A (b ↦ Not (P b))) → A
  ≔ [ inl. u ↦ u .fst | inr. u ↦ u .fst ]

def fingp_split_from_to (A : Type) (P : A → Type) (a : A) (da : Decidable (P a))
  : Id A (fingp_split_from A P (fingp_split_to A P a da)) a
  ≔ match da [ inl. p ↦ refl a | inr. np ↦ refl a ]

def fingp_split_to_in (A : Type) (P : A → Type) (hP : (b : A) → isProp (P b)) (a : A) (da : Decidable (P a)) (p : P a)
  : Id (Sum (Σ A P) (Σ A (b ↦ Not (P b)))) (fingp_split_to A P a da) (inl. (a, p))
  ≔ match da [
    | inl. p' ↦ inl. (refl a, hP a p' p)
    | inr. np ↦ absurd (Id (Sum (Σ A P) (Σ A (b ↦ Not (P b)))) (inr. (a, np)) (inl. (a, p))) (np p) ]

def fingp_split_to_out (A : Type) (P : A → Type) (a : A) (da : Decidable (P a)) (np : Not (P a))
  : Id (Sum (Σ A P) (Σ A (b ↦ Not (P b)))) (fingp_split_to A P a da) (inr. (a, np))
  ≔ match da [
    | inl. p ↦ absurd (Id (Sum (Σ A P) (Σ A (b ↦ Not (P b)))) (inl. (a, p)) (inr. (a, np))) (np p)
    | inr. np' ↦ inr. (refl a, negation_prop (P a) np' np) ]

def fingp_decidable_split_equiv (A : Type) (P : A → Type) (hP : (b : A) → isProp (P b))
  (d : (b : A) → Decidable (P b)) : Equiv A (Sum (Σ A P) (Σ A (b ↦ Not (P b))))
  ≔ quasi_inverse_equiv A (Sum (Σ A P) (Σ A (b ↦ Not (P b))))
      (a ↦ fingp_split_to A P a (d a)) (fingp_split_from A P)
      (a ↦ fingp_split_from_to A P a (d a))
      [ inl. u ↦ fingp_split_to_in A P hP (u .fst) (d (u .fst)) (u .snd)
      | inr. u ↦ fingp_split_to_out A P (u .fst) (d (u .fst)) (u .snd) ]

{` Fixed and non-fixed points of the action on X(sh_G). GSetFixedPoints
   (module 563) is X^G under evaluation at sh_G (invariant_maps_fixed_equiv). `}
def GSetNonFixedPoints (G : Group) (X : GSet G) : Type
  ≔ Σ (gset_underlying G X) (x ↦ Not ((g : USym G) → Id (gset_underlying G X) (gset_usym_act G X g x) x))

def gset_fixed_decidable (G : Group) (hG : IsFiniteGroup G) (X : GSet G)
  (dX : DecidableEquality (gset_underlying G X)) (x : gset_underlying G X)
  : Decidable ((g : USym G) → Id (gset_underlying G X) (gset_usym_act G X g x) x)
  ≔ finite_quantifiers (USym G) hG (g ↦ Id (gset_underlying G X) (gset_usym_act G X g x) x)
      (g ↦ gset_underlying_set G X (gset_usym_act G X g x) x) (g ↦ dX (gset_usym_act G X g x) x) .fst

def gset_fixed_points_finite (G : Group) (hG : IsFiniteGroup G) (X : GSet G) (hX : IsFiniteGSet G X)
  : IsFinite (GSetFixedPoints G X)
  ≔ finite_decidable_subset (gset_underlying G X) hX
      (x ↦ (g : USym G) → Id (gset_underlying G X) (gset_usym_act G X g x) x) (gset_fixed_points_prop G X)
      (gset_fixed_decidable G hG X (finite_decidable_equality (gset_underlying G X) hX))

def gset_nonfixed_points_finite (G : Group) (hG : IsFiniteGroup G) (X : GSet G) (hX : IsFiniteGSet G X)
  : IsFinite (GSetNonFixedPoints G X)
  ≔ let Y ≔ gset_underlying G X in
    let Fx : Y → Type ≔ x ↦ (g : USym G) → Id Y (gset_usym_act G X g x) x in
    let d ≔ gset_fixed_decidable G hG X (finite_decidable_equality Y hX) in
    finite_decidable_subset Y hX (x ↦ Not (Fx x)) (x ↦ negation_prop (Fx x))
      (x ↦ match d x [ inl. f ↦ inr. (nf ↦ nf f) | inr. nf ↦ inl. nf ])

{` |X(sh_G)| = |X^G| + |non-fixed points|. `}
def gset_fixed_split_card (G : Group) (hG : IsFiniteGroup G) (X : GSet G) (hX : IsFiniteGSet G X)
  : Id Nat (gset_card G X hX)
      (add (cardinality (GSetFixedPoints G X) (gset_fixed_points_finite G hG X hX))
           (cardinality (GSetNonFixedPoints G X) (gset_nonfixed_points_finite G hG X hX)))
  ≔ let Y ≔ gset_underlying G X in
    let Fx : Y → Type ≔ x ↦ (g : USym G) → Id Y (gset_usym_act G X g x) x in
    let hF ≔ gset_fixed_points_finite G hG X hX in
    let hN ≔ gset_nonfixed_points_finite G hG X hX in
    let hS ≔ finite_sum (GSetFixedPoints G X) (GSetNonFixedPoints G X) hF hN in
    concat Nat (gset_card G X hX) (cardinality (Sum (GSetFixedPoints G X) (GSetNonFixedPoints G X)) hS)
      (add (cardinality (GSetFixedPoints G X) hF) (cardinality (GSetNonFixedPoints G X) hN))
      (cardinality_equiv Y (Sum (GSetFixedPoints G X) (GSetNonFixedPoints G X))
        (fingp_decidable_split_equiv Y Fx (gset_fixed_points_prop G X)
          (gset_fixed_decidable G hG X (finite_decidable_equality Y hX))) hX hS)
      (cardinality_sum (GSetFixedPoints G X) (GSetNonFixedPoints G X) hF hN hS)

{` The orbit relation x ~ y ⇔ ‖(sh_G, x) = (sh_G, y)‖ (membership of y in
   the orbit G-subset [(sh_G, x)]_0 of module 503). `}
def gset_orbit_equivalence (G : Group) (X : GSet G) : EquivalenceRelation (gset_underlying G X)
  ≔ let T ≔ ActionType G X in
    (x y ↦ orbit_subset G X (shape G, x) (shape G) y,
     x ↦ mere (Id T (shape G, x) (shape G, x)) (refl (shape G, x)),
     x y r ↦ mere_rec (Id T (shape G, x) (shape G, y)) (Mere (Id T (shape G, y) (shape G, x)))
       (mere_isprop (Id T (shape G, y) (shape G, x)))
       (q ↦ mere (Id T (shape G, y) (shape G, x)) (inverse T (shape G, x) (shape G, y) q)) r,
     x y w r s ↦ mere_rec (Id T (shape G, x) (shape G, y)) (Mere (Id T (shape G, x) (shape G, w)))
       (mere_isprop (Id T (shape G, x) (shape G, w)))
       (q ↦ mere_rec (Id T (shape G, y) (shape G, w)) (Mere (Id T (shape G, x) (shape G, w)))
         (mere_isprop (Id T (shape G, x) (shape G, w)))
         (q' ↦ mere (Id T (shape G, x) (shape G, w)) (concat T (shape G, x) (shape G, y) (shape G, w) q q')) s) r)

{` x ~ y ⇔ ∃ g, y = g · x. `}
def gset_orbit_relation_transporter (G : Group) (X : GSet G) (x y : gset_underlying G X)
  (r : Rel (gset_underlying G X) (gset_orbit_equivalence G X) x y) : Mere (GSetTransporter G X x y)
  ≔ let T ≔ ActionType G X in
    mere_rec (Id T (shape G, x) (shape G, y)) (Mere (GSetTransporter G X x y)) (mere_isprop (GSetTransporter G X x y))
      (q ↦ let a ≔ action_type_path_equiv G X (shape G, x) (shape G, y) .map q in
        mere (GSetTransporter G X x y)
          (a .fst, inverse (gset_underlying G X) (gset_usym_act G X (a .fst) x) y (a .snd)))
      r

def gset_transporter_orbit_relation (G : Group) (X : GSet G) (x y : gset_underlying G X)
  (t : GSetTransporter G X x y) : Rel (gset_underlying G X) (gset_orbit_equivalence G X) x y
  ≔ mere (Id (ActionType G X) (shape G, x) (shape G, y))
      (action_type_path G X (shape G) (shape G) x y (t .fst)
        (inverse (gset_underlying G X) y (gset_usym_act G X (t .fst) x) (t .snd)))

def gset_orbit_relation_decidable (G : Group) (hG : IsFiniteGroup G) (X : GSet G)
  (dX : DecidableEquality (gset_underlying G X)) : DecidableRelation (gset_underlying G X) (gset_orbit_equivalence G X)
  ≔ x y ↦
    let Y ≔ gset_underlying G X in
    match finite_quantifiers (USym G) hG (g ↦ Id Y y (gset_usym_act G X g x))
      (g ↦ gset_underlying_set G X y (gset_usym_act G X g x)) (g ↦ dX y (gset_usym_act G X g x)) .snd [
    | inl. t ↦ inl. (mere_rec (GSetTransporter G X x y) (Rel Y (gset_orbit_equivalence G X) x y)
        (mere_isprop (Id (ActionType G X) (shape G, x) (shape G, y)))
        (gset_transporter_orbit_relation G X x y) t)
    | inr. no ↦ inr. (r ↦ no (gset_orbit_relation_transporter G X x y r)) ]

{` The set of orbits, as the quotient of X(sh_G) by the orbit relation, is finite. `}
def GSetOrbitQuotient (G : Group) (X : GSet G) : Type
  ≔ Quotient (gset_underlying G X) (gset_orbit_equivalence G X)

def gset_orbit_quotient_finite (G : Group) (hG : IsFiniteGroup G) (X : GSet G) (hX : IsFiniteGSet G X)
  : IsFinite (GSetOrbitQuotient G X)
  ≔ finite_quotient (gset_underlying G X) hX (gset_orbit_equivalence G X)
      (gset_orbit_relation_decidable G hG X (finite_decidable_equality (gset_underlying G X) hX))

{` The orbit of a fixed point is a singleton, so points in the orbit of a
   non-fixed point are not fixed. `}
def gset_fixed_orbit_trivial (G : Group) (X : GSet G) (x y : gset_underlying G X)
  (f : (g : USym G) → Id (gset_underlying G X) (gset_usym_act G X g x) x)
  (r : Rel (gset_underlying G X) (gset_orbit_equivalence G X) x y) : Id (gset_underlying G X) y x
  ≔ let Y ≔ gset_underlying G X in
    mere_rec (GSetTransporter G X x y) (Id Y y x) (gset_underlying_set G X y x)
      (t ↦ concat Y y (gset_usym_act G X (t .fst) x) x (t .snd) (f (t .fst)))
      (gset_orbit_relation_transporter G X x y r)

def gset_orbit_nonfixed (G : Group) (X : GSet G) (x y : gset_underlying G X)
  (nf : Not ((g : USym G) → Id (gset_underlying G X) (gset_usym_act G X g x) x))
  (r : Rel (gset_underlying G X) (gset_orbit_equivalence G X) x y)
  : Not ((g : USym G) → Id (gset_underlying G X) (gset_usym_act G X g y) y)
  ≔ fy ↦ nf (transport (gset_underlying G X) (w ↦ (g : USym G) → Id (gset_underlying G X) (gset_usym_act G X g w) w)
      y x (inverse (gset_underlying G X) x y
        (gset_fixed_orbit_trivial G X y x fy (gset_orbit_equivalence G X .symmetric x y r))) fy)

{` The class map of the non-fixed points into the set of orbits. `}
def gset_nonfixed_class (G : Group) (X : GSet G) (u : GSetNonFixedPoints G X) : GSetOrbitQuotient G X
  ≔ quotient_class (gset_underlying G X) (gset_orbit_equivalence G X) (u .fst)

def GSetNonFixedFiber (G : Group) (X : GSet G) (q : GSetOrbitQuotient G X) : Type
  ≔ BookFiber (GSetNonFixedPoints G X) (GSetOrbitQuotient G X) (gset_nonfixed_class G X) q

{` The underlying set of the orbit through x: X_[x](sh_G) = Σ_y ‖(sh_G, x) = (sh_G, y)‖. `}
def GSetOrbitSet (G : Group) (X : GSet G) (x : gset_underlying G X) : Type
  ≔ orbit_gset G X (shape G, x) (shape G) .fst

{` Over the class of a fixed point the fiber is empty. `}
def gset_nonfixed_fiber_fixed_empty (G : Group) (X : GSet G) (x : gset_underlying G X)
  (f : (g : USym G) → Id (gset_underlying G X) (gset_usym_act G X g x) x)
  (w : GSetNonFixedFiber G X (quotient_class (gset_underlying G X) (gset_orbit_equivalence G X) x)) : Empty
  ≔ let Y ≔ gset_underlying G X in
    let R ≔ gset_orbit_equivalence G X in
    let r : Rel Y R x (w .fst .fst) ≔ quotient_effective Y R x (w .fst .fst) .map (w .snd) in
    w .fst .snd (transport Y (v ↦ (g : USym G) → Id Y (gset_usym_act G X g v) v) x (w .fst .fst)
      (inverse Y (w .fst .fst) x (gset_fixed_orbit_trivial G X x (w .fst .fst) f r)) f)

{` Over the class of a non-fixed point x the fiber is the orbit X_[x](sh_G). `}
def gset_nonfixed_fiber_orbit_equiv (G : Group) (X : GSet G) (x : gset_underlying G X)
  (nf : Not ((g : USym G) → Id (gset_underlying G X) (gset_usym_act G X g x) x))
  : Equiv (GSetNonFixedFiber G X (quotient_class (gset_underlying G X) (gset_orbit_equivalence G X) x))
      (GSetOrbitSet G X x)
  ≔ let Y ≔ gset_underlying G X in
    let R ≔ gset_orbit_equivalence G X in
    let Q ≔ GSetOrbitQuotient G X in
    let c ≔ quotient_class Y R in
    let Fx : Y → Type ≔ v ↦ (g : USym G) → Id Y (gset_usym_act G X g v) v in
    let W ≔ GSetNonFixedFiber G X (c x) in
    let O ≔ GSetOrbitSet G X x in
    quasi_inverse_equiv W O
      (w ↦ (w .fst .fst, quotient_effective Y R x (w .fst .fst) .map (w .snd)))
      (o ↦ ((o .fst, gset_orbit_nonfixed G X x (o .fst) nf (o .snd)), quotient_encode Y R x (o .fst) (o .snd)))
      (w ↦ subtype_equal (GSetNonFixedPoints G X) (u ↦ Id Q (c x) (gset_nonfixed_class G X u))
        (u ↦ quotient_set Y R (c x) (gset_nonfixed_class G X u))
        ((w .fst .fst, gset_orbit_nonfixed G X x (w .fst .fst) nf (quotient_effective Y R x (w .fst .fst) .map (w .snd))),
         quotient_encode Y R x (w .fst .fst) (quotient_effective Y R x (w .fst .fst) .map (w .snd))) w
        (subtype_equal Y (v ↦ Not (Fx v)) (v ↦ negation_prop (Fx v))
          (w .fst .fst, gset_orbit_nonfixed G X x (w .fst .fst) nf (quotient_effective Y R x (w .fst .fst) .map (w .snd)))
          (w .fst) (refl (w .fst .fst))))
      (o ↦ subtype_equal Y (v ↦ Rel Y R x v) (v ↦ R .predicate x v .snd)
        (o .fst, quotient_effective Y R x (o .fst) .map (quotient_encode Y R x (o .fst) (o .snd))) o (refl (o .fst)))

{` The non-fixed points are the sum of these fibers (lem:sum-of-fibers). `}
def gset_nonfixed_sum_equiv (G : Group) (X : GSet G)
  : Equiv (Σ (GSetOrbitQuotient G X) (GSetNonFixedFiber G X)) (GSetNonFixedPoints G X)
  ≔ sum_of_fibers_equiv (GSetNonFixedPoints G X) (GSetOrbitQuotient G X) (gset_nonfixed_class G X)

{` The orbit set is finite and |X_[x](sh_G)| · |G_x| = |G| (Lagrange for
   the orbit subgroup (X_[x], x) of module 508). `}
def gset_orbit_set_decidable_equality (G : Group) (X : GSet G) (dX : DecidableEquality (gset_underlying G X))
  (x : gset_underlying G X) : DecidableEquality (GSetOrbitSet G X x)
  ≔ let Y ≔ gset_underlying G X in
    let R ≔ gset_orbit_equivalence G X in
    u v ↦ match dX (u .fst) (v .fst) [
      | inl. p ↦ inl. (subtype_equal Y (y ↦ Rel Y R x y) (y ↦ R .predicate x y .snd) u v p)
      | inr. np ↦ inr. (e ↦ np (refl ((o ↦ o .fst) : GSetOrbitSet G X x → Y) e)) ]

def gset_orbit_subgroup_finite (G : Group) (hG : IsFiniteGroup G) (X : GSet G) (hX : IsFiniteGSet G X)
  (x : gset_underlying G X) : IsFiniteGroup (subgroup_group G (orbit_subgroup G X x))
  ≔ subgroup_group_finite G hG (orbit_subgroup G X x)
      (gset_orbit_set_decidable_equality G X (finite_decidable_equality (gset_underlying G X) hX) x)

def gset_orbit_set_finite (G : Group) (hG : IsFiniteGroup G) (X : GSet G) (hX : IsFiniteGSet G X)
  (x : gset_underlying G X) : IsFinite (GSetOrbitSet G X x)
  ≔ subgroup_gset_finite G hG (orbit_subgroup G X x) (gset_orbit_subgroup_finite G hG X hX x)

def gset_orbit_card_divides (G : Group) (hG : IsFiniteGroup G) (X : GSet G) (hX : IsFiniteGSet G X)
  (x : gset_underlying G X) : NatDivides (cardinality (GSetOrbitSet G X x) (gset_orbit_set_finite G hG X hX x)) (group_card G hG)
  ≔ lagrange_index_divides G hG (orbit_subgroup G X x) (gset_orbit_subgroup_finite G hG X hX x)

{` A point whose orbit has exactly one element is fixed. `}
def gset_orbit_card_one_fixed (G : Group) (hG : IsFiniteGroup G) (X : GSet G) (hX : IsFiniteGSet G X)
  (x : gset_underlying G X)
  (e : Id Nat (cardinality (GSetOrbitSet G X x) (gset_orbit_set_finite G hG X hX x)) (suc. zero.))
  : (g : USym G) → Id (gset_underlying G X) (gset_usym_act G X g x) x
  ≔ g ↦
    let Y ≔ gset_underlying G X in
    let O ≔ GSetOrbitSet G X x in
    let c ≔ finite_card_one_contractible O (gset_orbit_set_finite G hG X hX x) e in
    let o1 : O ≔ (gset_usym_act G X g x, gset_transporter_orbit_relation G X x (gset_usym_act G X g x)
      (g, refl (gset_usym_act G X g x))) in
    let o2 : O ≔ (x, gset_orbit_equivalence G X .reflexive x) in
    refl ((o ↦ o .fst) : O → Y)
      (contractible_prop O (native_contraction O c) o1 o2)
