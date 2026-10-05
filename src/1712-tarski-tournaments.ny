export "1711-quartet-partitions"

{` Theorem of Tarski (AC(2) ⇒ AC(4)), combinatorial part. A choice of an
   element in each 2-element subset of a 4-element set A is a tournament on A
   ("a beats b" when a is chosen from {a, b}). From it one element of A is
   selected canonically, by a rule defined uniformly from decidable equality
   and the boolean universal quantifier of A (no enumeration of A is chosen):
   the vertex that beats nobody if there is one, else the vertex beaten by
   nobody if there is one, else the vertex with exactly one win whose beaten
   vertex also has exactly one win. On 4 vertices this is the book's rule
   (the unique minimum of q_x, the complement of a 3-element minimum set, or
   the chosen element of a 2-element minimum set). `}
def TarskiQuantifierSpec (T : Type) (all : (T → Bool) → Bool) (Q : T → Bool) : Type
  ≔ Product (Id Bool (all Q) true. → (x : T) → Id Bool (Q x) true.)
      (((x : T) → Id Bool (Q x) true.) → Id Bool (all Q) true.)

def TarskiQuantifier (T : Type) : Type
  ≔ Σ ((T → Bool) → Bool) (all ↦ (Q : T → Bool) → TarskiQuantifierSpec T all Q)

def TarskiOps (T : Type) : Type ≔ Product (DecidableEquality T) (TarskiQuantifier T)

def tarski_quantifier_spec_prop (T : Type) (all : (T → Bool) → Bool) (Q : T → Bool)
  : isProp (TarskiQuantifierSpec T all Q)
  ≔ product_prop (Id Bool (all Q) true. → (x : T) → Id Bool (Q x) true.)
      (((x : T) → Id Bool (Q x) true.) → Id Bool (all Q) true.)
      (pi_prop (Id Bool (all Q) true.) (_ ↦ (x : T) → Id Bool (Q x) true.)
        (_ ↦ pi_prop T (x ↦ Id Bool (Q x) true.) (x ↦ bool_set (Q x) true.)))
      (pi_prop ((x : T) → Id Bool (Q x) true.) (_ ↦ Id Bool (all Q) true.) (_ ↦ bool_set (all Q) true.))

def tarski_quantifier_prop (T : Type) : isProp (TarskiQuantifier T)
  ≔ u v ↦ subtype_equal ((T → Bool) → Bool) (all ↦ (Q : T → Bool) → TarskiQuantifierSpec T all Q)
      (all ↦ pi_prop (T → Bool) (Q ↦ TarskiQuantifierSpec T all Q) (Q ↦ tarski_quantifier_spec_prop T all Q)) u v
      (funext (T → Bool) (_ ↦ Bool) (u .fst) (v .fst)
        (Q ↦ quartet_bool_iff (u .fst Q) (v .fst Q)
          (e ↦ v .snd Q .snd (u .snd Q .fst e)) (e ↦ u .snd Q .snd (v .snd Q .fst e))))

def tarski_ops_prop (T : Type) (sT : isSet T) : isProp (TarskiOps T)
  ≔ product_prop (DecidableEquality T) (TarskiQuantifier T) (decidable_equality_prop T sT) (tarski_quantifier_prop T)

{` The operations on Fin 4 (computing) and on any finite type (from
   finite_decidable_equality and finite_quantifiers of chapter 2). `}
def tarski_ops_fin : TarskiOps (Fin quartet_four)
  ≔ (fin_decidable_equality quartet_four, (quartet_all, Q ↦ (quartet_all_sound Q, quartet_all_complete Q)))

def tarski_forall_decision (A : Type) (h : IsFinite A) (Q : A → Bool) : Decidable ((x : A) → Id Bool (Q x) true.)
  ≔ finite_quantifiers A h (x ↦ Id Bool (Q x) true.) (x ↦ bool_set (Q x) true.) (x ↦ bool_true_decidable (Q x)) .fst

def tarski_ops_finite (A : Type) (h : IsFinite A) : TarskiOps A
  ≔ (finite_decidable_equality A h,
      (Q ↦ decision_bool ((x : A) → Id Bool (Q x) true.) (tarski_forall_decision A h Q),
       Q ↦ (decision_bool_reflect ((x : A) → Id Bool (Q x) true.) (tarski_forall_decision A h Q),
            decision_bool_true ((x : A) → Id Bool (Q x) true.) (tarski_forall_decision A h Q))))

{` The selection rule. W a b = true means that a beats b. `}
def tarski_all (T : Type) (o : TarskiOps T) (Q : T → Bool) : Bool ≔ o .snd .fst Q
def tarski_any (T : Type) (o : TarskiOps T) (Q : T → Bool) : Bool ≔ bool_not (o .snd .fst (x ↦ bool_not (Q x)))
def tarski_eqb (T : Type) (o : TarskiOps T) (x y : T) : Bool ≔ decision_bool (Id T x y) (o .fst x y)

def tarski_sink (T : Type) (o : TarskiOps T) (W : T → T → Bool) (a : T) : Bool
  ≔ tarski_all T o (b ↦ bool_not (W a b))
def tarski_source (T : Type) (o : TarskiOps T) (W : T → T → Bool) (a : T) : Bool
  ≔ tarski_all T o (b ↦ bool_not (W b a))
def tarski_one_win (T : Type) (o : TarskiOps T) (W : T → T → Bool) (a : T) : Bool
  ≔ quartet_and (tarski_any T o (b ↦ W a b))
      (tarski_all T o (b ↦ tarski_all T o (b' ↦
        quartet_or (bool_not (quartet_and (W a b) (W a b'))) (tarski_eqb T o b b'))))

def tarski_selected (T : Type) (o : TarskiOps T) (W : T → T → Bool) (a : T) : Bool
  ≔ quartet_or (tarski_sink T o W a)
      (quartet_or (quartet_and (bool_not (tarski_any T o (tarski_sink T o W))) (tarski_source T o W a))
        (quartet_and (bool_not (tarski_any T o (tarski_sink T o W)))
          (quartet_and (bool_not (tarski_any T o (tarski_source T o W)))
            (quartet_and (tarski_one_win T o W a)
              (tarski_any T o (b ↦ quartet_and (W a b) (tarski_one_win T o W b)))))))

{` Tournaments: irreflexive, and exactly one of a, b beats the other. `}
def TarskiTournament (T : Type) (W : T → T → Bool) : Type
  ≔ Product ((a : T) → Id Bool (W a a) false.)
      ((a b : T) → Not (Id T a b) → Id Bool (W b a) (bool_not (W a b)))

{` The tournament on Fin 4 with results t_ij for i < j. `}
def tarski_table (t01 t02 t03 t12 t13 t23 : Bool) : Fin quartet_four → Fin quartet_four → Bool
  ≔ quartet_cases (_ ↦ Fin quartet_four → Bool)
      (quartet_cases (_ ↦ Bool) false. t01 t02 t03)
      (quartet_cases (_ ↦ Bool) (bool_not t01) false. t12 t13)
      (quartet_cases (_ ↦ Bool) (bool_not t02) (bool_not t12) false. t23)
      (quartet_cases (_ ↦ Bool) (bool_not t03) (bool_not t13) (bool_not t23) false.)

def tarski_table_of (W : Fin quartet_four → Fin quartet_four → Bool) : Fin quartet_four → Fin quartet_four → Bool
  ≔ tarski_table (W quartet_e0 quartet_e1) (W quartet_e0 quartet_e2) (W quartet_e0 quartet_e3)
      (W quartet_e1 quartet_e2) (W quartet_e1 quartet_e3) (W quartet_e2 quartet_e3)

def tarski_table_eq (W : Fin quartet_four → Fin quartet_four → Bool) (tw : TarskiTournament (Fin quartet_four) W)
  : Id (Fin quartet_four → Fin quartet_four → Bool) (tarski_table_of W) W
  ≔ let F ≔ Fin quartet_four in
    let irr ≔ tw .fst in
    let anti ≔ tw .snd in
    let lower : (a b : F) → Not (Id F a b) → Id Bool (bool_not (W a b)) (W b a)
      ≔ a b n ↦ inverse Bool (W b a) (bool_not (W a b)) (anti a b n) in
    let diag : (a : F) → Id Bool false. (W a a) ≔ a ↦ inverse Bool (W a a) false. (irr a) in
    funext2 F (_ ↦ F) (_ _ ↦ Bool) (tarski_table_of W) W
      (quartet_cases (a ↦ (b : F) → Id Bool (tarski_table_of W a b) (W a b))
        (quartet_cases (b ↦ Id Bool (tarski_table_of W quartet_e0 b) (W quartet_e0 b))
          (diag quartet_e0) (refl (W quartet_e0 quartet_e1)) (refl (W quartet_e0 quartet_e2))
          (refl (W quartet_e0 quartet_e3)))
        (quartet_cases (b ↦ Id Bool (tarski_table_of W quartet_e1 b) (W quartet_e1 b))
          (lower quartet_e0 quartet_e1 (quartet_ne quartet_e0 quartet_e1 (refl (false. : Bool))))
          (diag quartet_e1) (refl (W quartet_e1 quartet_e2)) (refl (W quartet_e1 quartet_e3)))
        (quartet_cases (b ↦ Id Bool (tarski_table_of W quartet_e2 b) (W quartet_e2 b))
          (lower quartet_e0 quartet_e2 (quartet_ne quartet_e0 quartet_e2 (refl (false. : Bool))))
          (lower quartet_e1 quartet_e2 (quartet_ne quartet_e1 quartet_e2 (refl (false. : Bool))))
          (diag quartet_e2) (refl (W quartet_e2 quartet_e3)))
        (quartet_cases (b ↦ Id Bool (tarski_table_of W quartet_e3 b) (W quartet_e3 b))
          (lower quartet_e0 quartet_e3 (quartet_ne quartet_e0 quartet_e3 (refl (false. : Bool))))
          (lower quartet_e1 quartet_e3 (quartet_ne quartet_e1 quartet_e3 (refl (false. : Bool))))
          (lower quartet_e2 quartet_e3 (quartet_ne quartet_e2 quartet_e3 (refl (false. : Bool))))
          (diag quartet_e3)))

{` The rule on Fin 4, the first selected vertex, and the check that it is
   the only selected vertex. `}
def tarski_sel_fin (W : Fin quartet_four → Fin quartet_four → Bool) (a : Fin quartet_four) : Bool
  ≔ tarski_selected (Fin quartet_four) tarski_ops_fin W a

def tarski_pick (b0 b1 b2 : Bool) : Fin quartet_four
  ≔ match b0 [
  | true. ↦ quartet_e0
  | false. ↦ match b1 [ true. ↦ quartet_e1 | false. ↦ match b2 [ true. ↦ quartet_e2 | false. ↦ quartet_e3 ] ] ]

def tarski_find (W : Fin quartet_four → Fin quartet_four → Bool) : Fin quartet_four
  ≔ tarski_pick (tarski_sel_fin W quartet_e0) (tarski_sel_fin W quartet_e1) (tarski_sel_fin W quartet_e2)

def tarski_check (W : Fin quartet_four → Fin quartet_four → Bool) : Bool
  ≔ quartet_and (tarski_sel_fin W (tarski_find W))
      (quartet_all (a ↦ quartet_or (bool_not (tarski_sel_fin W a)) (quartet_eqb a (tarski_find W))))

def tarski_all2 (g : Bool → Bool) : Bool ≔ quartet_and (g false.) (g true.)

def tarski_all2_sound (g : Bool → Bool) (e : Id Bool (tarski_all2 g) true.) : (b : Bool) → Id Bool (g b) true.
  ≔ [ false. ↦ quartet_and_left (g false.) (g true.) e | true. ↦ quartet_and_right (g false.) (g true.) e ]

def tarski_g5 (a b c d e : Bool) : Bool ≔ tarski_all2 (f ↦ tarski_check (tarski_table a b c d e f))
def tarski_g4 (a b c d : Bool) : Bool ≔ tarski_all2 (e ↦ tarski_g5 a b c d e)
def tarski_g3 (a b c : Bool) : Bool ≔ tarski_all2 (d ↦ tarski_g4 a b c d)
def tarski_g2 (a b : Bool) : Bool ≔ tarski_all2 (c ↦ tarski_g3 a b c)
def tarski_g1 (a : Bool) : Bool ≔ tarski_all2 (b ↦ tarski_g2 a b)
def tarski_all_tables : Bool ≔ tarski_all2 tarski_g1

{` The exhaustive check over all 64 tournaments on Fin 4, by computation. `}
def tarski_all_tables_true : Id Bool tarski_all_tables true. ≔ refl (true. : Bool)

def tarski_check_tables (a b c d e f : Bool) : Id Bool (tarski_check (tarski_table a b c d e f)) true.
  ≔ tarski_all2_sound (f ↦ tarski_check (tarski_table a b c d e f))
      (tarski_all2_sound (e ↦ tarski_g5 a b c d e)
        (tarski_all2_sound (d ↦ tarski_g4 a b c d)
          (tarski_all2_sound (c ↦ tarski_g3 a b c)
            (tarski_all2_sound (b ↦ tarski_g2 a b)
              (tarski_all2_sound tarski_g1 tarski_all_tables_true a) b) c) d) e) f

def tarski_check_tournament (W : Fin quartet_four → Fin quartet_four → Bool) (tw : TarskiTournament (Fin quartet_four) W)
  : Id Bool (tarski_check W) true.
  ≔ transport (Fin quartet_four → Fin quartet_four → Bool) (V ↦ Id Bool (tarski_check V) true.)
      (tarski_table_of W) W (tarski_table_eq W tw)
      (tarski_check_tables (W quartet_e0 quartet_e1) (W quartet_e0 quartet_e2) (W quartet_e0 quartet_e3)
        (W quartet_e1 quartet_e2) (W quartet_e1 quartet_e3) (W quartet_e2 quartet_e3))

def tarski_unique_fin (W : Fin quartet_four → Fin quartet_four → Bool) (tw : TarskiTournament (Fin quartet_four) W)
  : isContr (Σ (Fin quartet_four) (a ↦ Id Bool (tarski_sel_fin W a) true.))
  ≔ let F ≔ Fin quartet_four in
    let v ≔ tarski_find W in
    let rest ≔ quartet_all (a ↦ quartet_or (bool_not (tarski_sel_fin W a)) (quartet_eqb a v)) in
    let ch ≔ tarski_check_tournament W tw in
    let c1 : Id Bool (tarski_sel_fin W v) true. ≔ quartet_and_left (tarski_sel_fin W v) rest ch in
    let c2 ≔ quartet_all_sound (a ↦ quartet_or (bool_not (tarski_sel_fin W a)) (quartet_eqb a v))
      (quartet_and_right (tarski_sel_fin W v) rest ch) in
    (center ≔ (v, c1),
     contract ≔ u ↦ subtype_equal F (a ↦ Id Bool (tarski_sel_fin W a) true.) (a ↦ bool_set (tarski_sel_fin W a) true.)
       u (v, c1)
       (match quartet_or_cases (bool_not (tarski_sel_fin W (u .fst))) (quartet_eqb (u .fst) v) (c2 (u .fst)) [
        | inl. n ↦ absurd (Id F (u .fst) v) (quartet_not_true (tarski_sel_fin W (u .fst)) n (u .snd))
        | inr. q ↦ quartet_eqb_sound (u .fst) v q ]))

{` Exactly one vertex is selected, for every tournament on every 4-element
   set and any choice of the (propositional) operations. `}
def TarskiUnique (T : Type) : Type
  ≔ (o : TarskiOps T) (W : T → T → Bool) → TarskiTournament T W
    → isContr (Σ T (a ↦ Id Bool (tarski_selected T o W a) true.))

def tarski_unique_prop (T : Type) : isProp (TarskiUnique T)
  ≔ pi_prop (TarskiOps T) (o ↦ (W : T → T → Bool) → TarskiTournament T W
      → isContr (Σ T (a ↦ Id Bool (tarski_selected T o W a) true.)))
      (o ↦ pi_prop (T → T → Bool) (W ↦ TarskiTournament T W → isContr (Σ T (a ↦ Id Bool (tarski_selected T o W a) true.)))
        (W ↦ pi_prop (TarskiTournament T W) (_ ↦ isContr (Σ T (a ↦ Id Bool (tarski_selected T o W a) true.)))
          (_ ↦ iscontr_isprop (Σ T (a ↦ Id Bool (tarski_selected T o W a) true.)))))

def tarski_unique_fin_all : TarskiUnique (Fin quartet_four)
  ≔ o W tw ↦ transport (TarskiOps (Fin quartet_four))
      (o' ↦ isContr (Σ (Fin quartet_four) (a ↦ Id Bool (tarski_selected (Fin quartet_four) o' W a) true.)))
      tarski_ops_fin o (tarski_ops_prop (Fin quartet_four) (fin_set quartet_four) tarski_ops_fin o)
      (tarski_unique_fin W tw)

def tarski_unique (A : Type) (h : Mere (Id Type (Fin quartet_four) A)) : TarskiUnique A
  ≔ quartet_transfer TarskiUnique A (tarski_unique_prop A) tarski_unique_fin_all h

def tarski_select (A : Type) (h : Mere (Id Type (Fin quartet_four) A)) (o : TarskiOps A)
  (W : A → A → Bool) (tw : TarskiTournament A W) : A
  ≔ tarski_unique A h o W tw .center .fst

{` Litmus checks: in the transitive tournament 0 > 1 > 2 > 3 the vertex 3
   (score 0) is selected; with scores (2, 2, 1, 1), where 2 beats 3, the
   vertex 2 is selected (the chosen element of the minimum set {2, 3}); with
   scores (3, 1, 1, 1) the source 0 is selected. `}
def tarski_example_transitive
  : Id (Fin quartet_four) (tarski_find (tarski_table true. true. true. true. true. true.)) quartet_e3
  ≔ refl quartet_e3
def tarski_example_two_two_one_one
  : Id (Fin quartet_four) (tarski_find (tarski_table true. true. false. true. true. true.)) quartet_e2
  ≔ refl quartet_e2
def tarski_example_source
  : Id (Fin quartet_four) (tarski_find (tarski_table true. true. true. true. false. true.)) quartet_e0
  ≔ refl quartet_e0
