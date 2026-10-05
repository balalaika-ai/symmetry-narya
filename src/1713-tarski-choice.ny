export "1712-tarski-tournaments"

{` Theorem of Tarski: AC(2) implies AC(4). The set [A]² of 2-element subsets
   of A is KSubsets A 2 of module 178 (prop-valued subsets whose carrier is
   merely Fin 2); Y = Σ_{x:X} [P(x)]² is a set carrying the family of 2-element
   sets y ↦ (elements of the subset y). `}
def tarski_ksubsets_set (A : Type) (k : Nat) : isSet (KSubsets A k)
  ≔ sigma_set (Subtypes A) (S ↦ Mere (Id Type (SubtypeCarrier A S) (Fin k))) (subtypes_set A)
      (S ↦ prop_is_set (Mere (Id Type (SubtypeCarrier A S) (Fin k))) (mere_isprop (Id Type (SubtypeCarrier A S) (Fin k))))

def tarski_subset_family (A : Type) (sA : isSet A) (S : KSubsets A two) : FiniteSetsAt two
  ≔ ((SubtypeCarrier A (S .fst),
        sigma_set A (t ↦ S .fst t .fst) sA (t ↦ prop_is_set (S .fst t .fst) (S .fst t .snd))),
      trunc_map native_truncation (Id Type (SubtypeCarrier A (S .fst)) (Fin two))
        (Id Type (Fin two) (SubtypeCarrier A (S .fst)))
        (inverse Type (SubtypeCarrier A (S .fst)) (Fin two)) (S .snd))

{` A choice of an element in every 2-element subset of A. `}
def TarskiChoice (A : Type) : Type ≔ (S : KSubsets A two) → SubtypeCarrier A (S .fst)

{` The 2-element subset {a, b} for a ≠ b. `}
def tarski_pair (A : Type) (sA : isSet A) (a b : A) (ne : Not (Id A a b)) : Subtypes A
  ≔ z ↦ (Sum (Id A z a) (Id A z b),
      disjoint_sum_prop (Id A z a) (Id A z b) (sA z a) (sA z b)
        (p q ↦ ne (concat A a z b (inverse A z a p) q)))

def tarski_pair_side (A : Type) (a b z : A) (e : Sum (Id A z a) (Id A z b)) : Bool
  ≔ match e [ inl. _ ↦ false. | inr. _ ↦ true. ]

def tarski_pair_point (A : Type) (sA : isSet A) (a b : A) (ne : Not (Id A a b))
  : Bool → SubtypeCarrier A (tarski_pair A sA a b ne)
  ≔ [ false. ↦ (a, inl. (refl a)) | true. ↦ (b, inr. (refl b)) ]

def tarski_pair_roundtrip (A : Type) (sA : isSet A) (a b : A) (ne : Not (Id A a b)) (z : A)
  (e : Sum (Id A z a) (Id A z b))
  : Id (SubtypeCarrier A (tarski_pair A sA a b ne)) (tarski_pair_point A sA a b ne (tarski_pair_side A a b z e)) (z, e)
  ≔ match e [
  | inl. p ↦ subtype_equal A (t ↦ tarski_pair A sA a b ne t .fst) (t ↦ tarski_pair A sA a b ne t .snd)
      (a, inl. (refl a)) (z, inl. p) (inverse A z a p)
  | inr. q ↦ subtype_equal A (t ↦ tarski_pair A sA a b ne t .fst) (t ↦ tarski_pair A sA a b ne t .snd)
      (b, inr. (refl b)) (z, inr. q) (inverse A z b q) ]

def tarski_pair_bool_equiv (A : Type) (sA : isSet A) (a b : A) (ne : Not (Id A a b))
  : Equiv (SubtypeCarrier A (tarski_pair A sA a b ne)) Bool
  ≔ quasi_inverse_equiv (SubtypeCarrier A (tarski_pair A sA a b ne)) Bool
      (w ↦ tarski_pair_side A a b (w .fst) (w .snd)) (tarski_pair_point A sA a b ne)
      (w ↦ tarski_pair_roundtrip A sA a b ne (w .fst) (w .snd))
      [ false. ↦ refl (false. : Bool) | true. ↦ refl (true. : Bool) ]

def tarski_pair_subset (A : Type) (sA : isSet A) (a b : A) (ne : Not (Id A a b)) : KSubsets A two
  ≔ (tarski_pair A sA a b ne,
      mere (Id Type (SubtypeCarrier A (tarski_pair A sA a b ne)) (Fin two))
        (concat Type (SubtypeCarrier A (tarski_pair A sA a b ne)) Bool (Fin two)
          (ua (SubtypeCarrier A (tarski_pair A sA a b ne)) Bool (tarski_pair_bool_equiv A sA a b ne))
          (inverse Type (Fin two) Bool fin_two_path)))

{` {b, a} = {a, b} as 2-element subsets. `}
def tarski_pair_subset_swap (A : Type) (sA : isSet A) (a b : A) (ne : Not (Id A a b)) (ne' : Not (Id A b a))
  : Id (KSubsets A two) (tarski_pair_subset A sA b a ne') (tarski_pair_subset A sA a b ne)
  ≔ subtype_equal (Subtypes A) (S ↦ Mere (Id Type (SubtypeCarrier A S) (Fin two)))
      (S ↦ mere_isprop (Id Type (SubtypeCarrier A S) (Fin two)))
      (tarski_pair_subset A sA b a ne') (tarski_pair_subset A sA a b ne)
      (funext A (_ ↦ PropTypes) (tarski_pair A sA b a ne') (tarski_pair A sA a b ne)
        (z ↦ proposition_extensionality (tarski_pair A sA b a ne' z) (tarski_pair A sA a b ne z)
          (sum_swap (Id A z b) (Id A z a)) (sum_swap (Id A z a) (Id A z b))))

{` The tournament of a choice function: a beats b iff a is chosen from {a, b}. `}
def tarski_winner (A : Type) (sA : isSet A) (c : TarskiChoice A) (a b : A) (ne : Not (Id A a b)) : A
  ≔ c (tarski_pair_subset A sA a b ne) .fst

def tarski_winner_member (A : Type) (sA : isSet A) (c : TarskiChoice A) (a b : A) (ne : Not (Id A a b))
  : Sum (Id A (tarski_winner A sA c a b ne) a) (Id A (tarski_winner A sA c a b ne) b)
  ≔ c (tarski_pair_subset A sA a b ne) .snd

def tarski_winner_swap (A : Type) (sA : isSet A) (c : TarskiChoice A) (a b : A) (ne : Not (Id A a b))
  (ne' : Not (Id A b a))
  : Id A (tarski_winner A sA c b a ne') (tarski_winner A sA c a b ne)
  ≔ map_path (KSubsets A two) A (S ↦ c S .fst) (tarski_pair_subset A sA b a ne') (tarski_pair_subset A sA a b ne)
      (tarski_pair_subset_swap A sA a b ne ne')

def tarski_beats_at (A : Type) (sA : isSet A) (d : DecidableEquality A) (c : TarskiChoice A) (a b : A)
  (x : Decidable (Id A a b)) : Bool
  ≔ match x [
  | inl. _ ↦ false.
  | inr. ne ↦ decision_bool (Id A (tarski_winner A sA c a b ne) a) (d (tarski_winner A sA c a b ne) a) ]

def tarski_beats (A : Type) (sA : isSet A) (d : DecidableEquality A) (c : TarskiChoice A) (a b : A) : Bool
  ≔ tarski_beats_at A sA d c a b (d a b)

def tarski_decision_false (X : Type) (d : Decidable X) (n : Not X) : Id Bool (decision_bool X d) false.
  ≔ match d [ inl. x ↦ absurd (Id Bool true. false.) (n x) | inr. _ ↦ refl (false. : Bool) ]

def tarski_beats_irreflexive_at (A : Type) (sA : isSet A) (d : DecidableEquality A) (c : TarskiChoice A) (a : A)
  (x : Decidable (Id A a a)) : Id Bool (tarski_beats_at A sA d c a a x) false.
  ≔ match x [ inl. _ ↦ refl (false. : Bool) | inr. ne ↦ absurd (Id Bool (tarski_beats_at A sA d c a a (inr. ne)) false.) (ne (refl a)) ]

def tarski_beats_at_ne (A : Type) (sA : isSet A) (d : DecidableEquality A) (c : TarskiChoice A) (a b : A)
  (ne : Not (Id A a b)) (x : Decidable (Id A a b))
  : Id Bool (tarski_beats_at A sA d c a b x)
      (decision_bool (Id A (tarski_winner A sA c a b ne) a) (d (tarski_winner A sA c a b ne) a))
  ≔ match x [
  | inl. p ↦ absurd (Id Bool false. (decision_bool (Id A (tarski_winner A sA c a b ne) a) (d (tarski_winner A sA c a b ne) a)))
      (ne p)
  | inr. ne' ↦ map_path (Not (Id A a b)) Bool
      (n ↦ decision_bool (Id A (tarski_winner A sA c a b n) a) (d (tarski_winner A sA c a b n) a))
      ne' ne (negation_prop (Id A a b) ne' ne) ]

def tarski_beats_antisymmetric (A : Type) (sA : isSet A) (d : DecidableEquality A) (c : TarskiChoice A)
  (a b : A) (ne : Not (Id A a b))
  : Id Bool (tarski_beats A sA d c b a) (bool_not (tarski_beats A sA d c a b))
  ≔ let ne' : Not (Id A b a) ≔ p ↦ ne (inverse A b a p) in
    let w ≔ tarski_winner A sA c a b ne in
    let w' ≔ tarski_winner A sA c b a ne' in
    let sw : Id A w' w ≔ tarski_winner_swap A sA c a b ne ne' in
    let ab : Id Bool (tarski_beats A sA d c a b) (decision_bool (Id A w a) (d w a))
      ≔ tarski_beats_at_ne A sA d c a b ne (d a b) in
    let ba : Id Bool (tarski_beats A sA d c b a) (decision_bool (Id A w' b) (d w' b))
      ≔ tarski_beats_at_ne A sA d c b a ne' (d b a) in
    match tarski_winner_member A sA c a b ne [
    | inl. p ↦
        let x : Id Bool (tarski_beats A sA d c b a) false.
          ≔ concat Bool (tarski_beats A sA d c b a) (decision_bool (Id A w' b) (d w' b)) false. ba
              (tarski_decision_false (Id A w' b) (d w' b)
                (q ↦ ne (concat A a w' b (inverse A w' a (concat A w' w a sw p)) q))) in
        let y : Id Bool (tarski_beats A sA d c a b) true.
          ≔ concat Bool (tarski_beats A sA d c a b) (decision_bool (Id A w a) (d w a)) true. ab
              (decision_bool_true (Id A w a) (d w a) p) in
        concat Bool (tarski_beats A sA d c b a) false. (bool_not (tarski_beats A sA d c a b)) x
          (inverse Bool (bool_not (tarski_beats A sA d c a b)) false.
            (map_path Bool Bool bool_not (tarski_beats A sA d c a b) true. y))
    | inr. q ↦
        let x : Id Bool (tarski_beats A sA d c b a) true.
          ≔ concat Bool (tarski_beats A sA d c b a) (decision_bool (Id A w' b) (d w' b)) true. ba
              (decision_bool_true (Id A w' b) (d w' b) (concat A w' w b sw q)) in
        let y : Id Bool (tarski_beats A sA d c a b) false.
          ≔ concat Bool (tarski_beats A sA d c a b) (decision_bool (Id A w a) (d w a)) false. ab
              (tarski_decision_false (Id A w a) (d w a) (r ↦ ne (concat A a w b (inverse A w a r) q))) in
        concat Bool (tarski_beats A sA d c b a) true. (bool_not (tarski_beats A sA d c a b)) x
          (inverse Bool (bool_not (tarski_beats A sA d c a b)) true.
            (map_path Bool Bool bool_not (tarski_beats A sA d c a b) false. y)) ]

def tarski_beats_tournament (A : Type) (sA : isSet A) (d : DecidableEquality A) (c : TarskiChoice A)
  : TarskiTournament A (tarski_beats A sA d c)
  ≔ (a ↦ tarski_beats_irreflexive_at A sA d c a (d a a), tarski_beats_antisymmetric A sA d c)

{` The canonical element of a 4-element set chosen from its 2-element subsets. `}
def tarski_choose (A : Type) (sA : isSet A) (h : Mere (Id Type (Fin quartet_four) A)) (c : TarskiChoice A) : A
  ≔ let fin : IsFinite A
      ≔ trunc_map native_truncation (Id Type (Fin quartet_four) A) (Σ Nat (n ↦ Id Type A (Fin n)))
          (p ↦ (quartet_four, inverse Type (Fin quartet_four) A p)) h in
    let d ≔ finite_decidable_equality A fin in
    tarski_select A h (tarski_ops_finite A fin) (tarski_beats A sA d c) (tarski_beats_tournament A sA d c)

{` Theorem (Tarski): AC(2) implies AC(4). Choose an element of every
   2-element subset of every P(x) by AC(2) over Y = Σ_x [P(x)]², then select
   an element of each P(x) canonically. `}
def tarski_choice_two_four (c2 : ChoiceOfSize two) : ChoiceOfSize quartet_four
  ≔ X P ne ↦
    let A : X .fst → Type ≔ x ↦ P x .fst .fst in
    let Y : SetTypes
      ≔ (Σ (X .fst) (x ↦ KSubsets (A x) two),
          sigma_set (X .fst) (x ↦ KSubsets (A x) two) (X .snd) (x ↦ tarski_ksubsets_set (A x) two)) in
    let E : Y .fst → FiniteSetsAt two ≔ y ↦ tarski_subset_family (A (y .fst)) (P (y .fst) .fst .snd) (y .snd) in
    trunc_map native_truncation ((y : Y .fst) → E y .fst .fst) ((x : X .fst) → A x)
      (g x ↦ tarski_choose (A x) (P x .fst .snd) (P x .snd) (S ↦ g (x, S)))
      (c2 Y E (y ↦ quartet_sized_point (suc. zero.) (E y .fst .fst) (E y .snd)))

{` Litmus: the 2-element subset {0, 3} of Fin 4 contains 3 and not 1. `}
def tarski_pair_example_member
  : tarski_pair (Fin quartet_four) (fin_set quartet_four) quartet_e0 quartet_e3 quartet_e0_ne_e3 quartet_e3 .fst
  ≔ inr. (refl quartet_e3)
def tarski_pair_example_nonmember
  : Not (tarski_pair (Fin quartet_four) (fin_set quartet_four) quartet_e0 quartet_e3 quartet_e0_ne_e3 quartet_e1 .fst)
  ≔ [ inl. p ↦ quartet_ne quartet_e1 quartet_e0 (refl (false. : Bool)) p
    | inr. q ↦ quartet_ne quartet_e1 quartet_e3 (refl (false. : Bool)) q ]
