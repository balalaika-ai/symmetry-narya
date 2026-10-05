export "1701-choice-sections"

{` Theorem after pri:ac (Diaconescu / Goodman–Myhill): AC implies LEM.
   The book's quotient 2/∼ with (0 ∼ 1) = P is module 41's set quotient
   (an image, not a HIT) of the following equivalence relation, where the
   relation between distinct booleans is P by definition. `}
def diaconescu_relation (P : Type) (hP : isProp P) (x y : Bool) : PropTypes
  ≔ match x, y [
  | false., false. ↦ (Unit, unit_prop)
  | true., true. ↦ (Unit, unit_prop)
  | false., true. ↦ (P, hP)
  | true., false. ↦ (P, hP) ]

def diaconescu_reflexive (P : Type) (hP : isProp P) (x : Bool) : diaconescu_relation P hP x x .fst
  ≔ match x [ false. ↦ star. | true. ↦ star. ]

def diaconescu_symmetric (P : Type) (hP : isProp P) (x y : Bool)
  (r : diaconescu_relation P hP x y .fst) : diaconescu_relation P hP y x .fst
  ≔ match x, y [
  | false., false. ↦ star.
  | true., true. ↦ star.
  | false., true. ↦ r
  | true., false. ↦ r ]

def diaconescu_transitive (P : Type) (hP : isProp P) (x y z : Bool)
  (r : diaconescu_relation P hP x y .fst) (s : diaconescu_relation P hP y z .fst)
  : diaconescu_relation P hP x z .fst
  ≔ match x, y, z [
  | false., false., false. ↦ star.
  | false., false., true. ↦ s
  | false., true., false. ↦ star.
  | false., true., true. ↦ r
  | true., false., false. ↦ r
  | true., false., true. ↦ star.
  | true., true., false. ↦ s
  | true., true., true. ↦ star. ]

def diaconescu_equivalence (P : Type) (hP : isProp P) : EquivalenceRelation Bool
  ≔ (diaconescu_relation P hP, diaconescu_reflexive P hP, diaconescu_symmetric P hP,
      diaconescu_transitive P hP)

def DiaconescuQuotient (P : Type) (hP : isProp P) : Type ≔ Quotient Bool (diaconescu_equivalence P hP)

def diaconescu_class (P : Type) (hP : isProp P) : Bool → DiaconescuQuotient P hP
  ≔ quotient_class Bool (diaconescu_equivalence P hP)

{` Litmus: in the quotient, [0] = [1] holds exactly when P does. `}
def diaconescu_classes_path_equiv (P : Type) (hP : isProp P)
  : Equiv (Id (DiaconescuQuotient P hP) (diaconescu_class P hP false.) (diaconescu_class P hP true.)) P
  ≔ quotient_effective Bool (diaconescu_equivalence P hP) false. true.

def choice_bool_decidable_equality : DecidableEquality Bool
  ≔ x y ↦ match x, y [
  | false., false. ↦ inl. (refl (false. : Bool))
  | true., true. ↦ inl. (refl (true. : Bool))
  | false., true. ↦ inr. (bool_encode false. true.)
  | true., false. ↦ inr. (bool_encode true. false.) ]

{` The case analysis of the proof, for a section s of the quotient map q
   (q ∘ s = id): decide whether s([0]) = s([1]). `}
def diaconescu_decide (P : Type) (hP : isProp P)
  (t : MapSection Bool (DiaconescuQuotient P hP) (diaconescu_class P hP)) : Decidable P
  ≔ let Q ≔ DiaconescuQuotient P hP in
    let q ≔ diaconescu_class P hP in
    let s ≔ t .fst in
    let back : (z : Q) → Id Q (q (s z)) z
      ≔ z ↦ happly Q (_ ↦ Q) (compose Q Bool Q q s) (identity Q) (t .snd) z in
    match choice_bool_decidable_equality (s (q false.)) (s (q true.)) [
    | inl. e ↦ inl. (diaconescu_classes_path_equiv P hP .map
        (concat Q (q false.) (q (s (q false.))) (q true.)
          (inverse Q (q (s (q false.))) (q false.) (back (q false.)))
          (concat Q (q (s (q false.))) (q (s (q true.))) (q true.)
            (map_path Bool Q q (s (q false.)) (s (q true.)) e) (back (q true.)))))
    | inr. ne ↦ inr. (p ↦ ne (map_path Q Bool s (q false.) (q true.)
        (quotient_encode Bool (diaconescu_equivalence P hP) false. true. p))) ]

def diaconescu_quotient_set (P : Type) (hP : isProp P) : SetTypes
  ≔ (DiaconescuQuotient P hP, quotient_set Bool (diaconescu_equivalence P hP))

def choice_implies_excluded_middle (ac : AxiomOfChoice) : ExcludedMiddle
  ≔ P hP ↦ mere_rec (MapSection Bool (DiaconescuQuotient P hP) (diaconescu_class P hP)) (Decidable P)
      (decidability_prop P hP) (diaconescu_decide P hP)
      (choice_splits_surjections ac (diaconescu_quotient_set P hP) (Bool, bool_set)
        (diaconescu_class P hP) (quotient_surjective Bool (diaconescu_equivalence P hP)))
