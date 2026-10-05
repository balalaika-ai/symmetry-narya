export "456-sign-inversions"

{` Chapter 4, proof of lem:parityequiv (group.tex:1490): the book's
   Venn-diagram argument for transitivity of the parity relation. For
   sections f1, f2, f3 of P : E → BΣ_2, E_ij = {f_i = f_j}, F_ij = {f_i ≠ f_j},
   D = {f1 = f2 = f3} and E'_ij = E_ij \ D; subsets are Boolean predicates
   and cardinalities are finite_true_count (Card F_ij is the cardinality of
   ParityDisagreement, parity_disagreement_count). We prove the covering
   E12 ∪ E23 ∪ E13 = E, the disjoint decomposition F_ij = E'_ik ⊔ E'_jk as a
   count, the identity Card F12 + Card F13 + Card F23 = 2(Card E'12 +
   Card E'13 + Card E'23), and its two consequences (transitivity and "at
   least one F_ij is even"). Module 451 proves transitivity by the xor
   cocycle instead. `}

def bool_and_comm (b c : Bool) : Id Bool (bool_and b c) (bool_and c b)
  ≔ match b, c [
  | false., false. ↦ refl (false. : Bool)
  | false., true. ↦ refl (false. : Bool)
  | true., false. ↦ refl (false. : Bool)
  | true., true. ↦ refl (true. : Bool) ]

def bool_and_not_xor (b c : Bool) : Id Bool (bool_and b c) (bool_and (bool_not (bool_xor b c)) b)
  ≔ match b, c [
  | false., false. ↦ refl (false. : Bool)
  | false., true. ↦ refl (false. : Bool)
  | true., false. ↦ refl (false. : Bool)
  | true., true. ↦ refl (true. : Bool) ]

def bool_and_not_left_xor (x y : Bool) : Id Bool (bool_and (bool_not x) y) (bool_and (bool_not x) (bool_xor x y))
  ≔ match x [ false. ↦ refl y | true. ↦ refl (false. : Bool) ]

{` Counting a subset by splitting it along a second predicate. `}
def true_count_split_step (X Y : Nat) (u v : Bool)
  : Id Nat (add (add X Y) (bool_to_nat u))
      (add (add X (bool_to_nat (bool_and u v))) (add Y (bool_to_nat (bool_and u (bool_not v)))))
  ≔ match u, v [
  | false., _ ↦ refl (add X Y)
  | true., true. ↦ inverse Nat (add (suc. X) Y) (suc. (add X Y)) (add_suc_left X Y)
  | true., false. ↦ refl (suc. (add X Y)) ]

def true_count_split (n : Nat) (b c : Fin n → Bool)
  : Id Nat (true_count n b)
      (add (true_count n (e ↦ bool_and (b e) (c e))) (true_count n (e ↦ bool_and (b e) (bool_not (c e)))))
  ≔ match n [
  | zero. ↦ refl (zero. : Nat)
  | suc. m ↦
      let X ≔ true_count m (a ↦ bool_and (b (inl. a)) (c (inl. a))) in
      let Y ≔ true_count m (a ↦ bool_and (b (inl. a)) (bool_not (c (inl. a)))) in
      concat Nat (true_count (suc. m) b) (add (add X Y) (bool_to_nat (b (inr. star.))))
        (add (true_count (suc. m) (e ↦ bool_and (b e) (c e))) (true_count (suc. m) (e ↦ bool_and (b e) (bool_not (c e)))))
        (refl ((z ↦ add z (bool_to_nat (b (inr. star.)))) : Nat → Nat) (true_count_split m (a ↦ b (inl. a)) (a ↦ c (inl. a))))
        (true_count_split_step X Y (b (inr. star.)) (c (inr. star.))) ]

def FiniteTrueCountSplit (A : Type) : Type
  ≔ (hA : IsFinite A) (b c : A → Bool) →
      Id Nat (finite_true_count A hA b)
        (add (finite_true_count A hA (e ↦ bool_and (b e) (c e))) (finite_true_count A hA (e ↦ bool_and (b e) (bool_not (c e)))))

def finite_true_count_split_prop (A : Type) : isProp (FiniteTrueCountSplit A)
  ≔ pi_prop (IsFinite A) (hA ↦ (b c : A → Bool) →
      Id Nat (finite_true_count A hA b)
        (add (finite_true_count A hA (e ↦ bool_and (b e) (c e))) (finite_true_count A hA (e ↦ bool_and (b e) (bool_not (c e))))))
      (hA ↦ pi_prop (A → Bool) (b ↦ (c : A → Bool) →
        Id Nat (finite_true_count A hA b)
          (add (finite_true_count A hA (e ↦ bool_and (b e) (c e))) (finite_true_count A hA (e ↦ bool_and (b e) (bool_not (c e))))))
        (b ↦ pi_prop (A → Bool) (c ↦
          Id Nat (finite_true_count A hA b)
            (add (finite_true_count A hA (e ↦ bool_and (b e) (c e))) (finite_true_count A hA (e ↦ bool_and (b e) (bool_not (c e))))))
          (c ↦ nat_set (finite_true_count A hA b)
            (add (finite_true_count A hA (e ↦ bool_and (b e) (c e))) (finite_true_count A hA (e ↦ bool_and (b e) (bool_not (c e))))))))

def fin_true_count_split (n : Nat) : FiniteTrueCountSplit (Fin n)
  ≔ hA b c ↦
    let bc : Fin n → Bool ≔ e ↦ bool_and (b e) (c e) in
    let bnc : Fin n → Bool ≔ e ↦ bool_and (b e) (bool_not (c e)) in
    calc finite_true_count (Fin n) hA b
      = true_count n b by finite_true_count_fin n hA b
      = add (true_count n bc) (true_count n bnc) by true_count_split n b c
      = add (finite_true_count (Fin n) hA bc) (finite_true_count (Fin n) hA bnc)
        by refl add (inverse Nat (finite_true_count (Fin n) hA bc) (true_count n bc) (finite_true_count_fin n hA bc))
          (inverse Nat (finite_true_count (Fin n) hA bnc) (true_count n bnc) (finite_true_count_fin n hA bnc)) ∎

def finite_true_count_split (E : Type) (hE : IsFinite E) : FiniteTrueCountSplit E
  ≔ finite_ind_prop FiniteTrueCountSplit finite_true_count_split_prop fin_true_count_split E hE

{` The Venn regions. parity_venn_part a b c = Card E'_ab relative to c: the
   points where a and b agree and c differs from them. `}
def parity_venn_part (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (a b c : LocalSections E P) : Nat
  ≔ finite_true_count E hE (e ↦ bool_and (bool_not (parity_differ E P a b e)) (parity_differ E P a c e))

{` Of the three values at any point, two agree: E12 ∪ E23 ∪ E13 = E. `}
def parity_venn_cover (E : Type) (P : E → BookFiniteSetsAt two) (a b c : LocalSections E P) (e : E)
  : Sum (Id (P e .fst .fst) (a e) (b e)) (Sum (Id (P e .fst .fst) (b e) (c e)) (Id (P e .fst .fst) (a e) (c e)))
  ≔ let X ≔ P e .fst .fst in let h ≔ two_set_two_element (P e) in
    let d ≔ two_element_decidable_equality X h in
    match d (a e) (b e) [
    | inl. p ↦ inl. p
    | inr. nab ↦ match d (b e) (c e) [
      | inl. q ↦ inr. (inl. q)
      | inr. nbc ↦ inr. (inr. (two_element_ne_ne X h (a e) (b e) (c e) nab (r ↦ nbc (inverse X (c e) (b e) r)))) ] ]

{` F_ab = E'_ac ⊔ E'_bc (as a count). `}
def parity_venn_split (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (a b c : LocalSections E P)
  : Id Nat (finite_true_count E hE (parity_differ E P a b)) (add (parity_venn_part E hE P a c b) (parity_venn_part E hE P b c a))
  ≔ let d ≔ parity_differ E P in
    calc finite_true_count E hE (d a b)
      = add (finite_true_count E hE (e ↦ bool_and (d a b e) (d a c e))) (finite_true_count E hE (e ↦ bool_and (d a b e) (bool_not (d a c e))))
        by finite_true_count_split E hE hE (d a b) (d a c)
      = add (parity_venn_part E hE P b c a) (parity_venn_part E hE P a c b)
        by refl add
          (finite_true_count_homotopy E hE (e ↦ bool_and (d a b e) (d a c e)) (e ↦ bool_and (bool_not (d b c e)) (d b a e))
            (e ↦ let X ≔ P e .fst .fst in let h ≔ two_set_two_element (P e) in
              calc bool_and (d a b e) (d a c e)
                = bool_and (bool_not (bool_xor (d a b e) (d a c e))) (d a b e) by bool_and_not_xor (d a b e) (d a c e)
                = bool_and (bool_not (bool_xor (d b a e) (d a c e))) (d b a e)
                  by refl ((x ↦ bool_and (bool_not (bool_xor x (d a c e))) x) : Bool → Bool) (two_differ_symm X h (a e) (b e))
                = bool_and (bool_not (d b c e)) (d b a e)
                  by refl ((x ↦ bool_and (bool_not x) (d b a e)) : Bool → Bool)
                    (inverse Bool (d b c e) (bool_xor (d b a e) (d a c e)) (two_differ_cocycle X h (b e) (a e) (c e))) ∎))
          (finite_true_count_homotopy E hE (e ↦ bool_and (d a b e) (bool_not (d a c e))) (e ↦ bool_and (bool_not (d a c e)) (d a b e))
            (e ↦ bool_and_comm (d a b e) (bool_not (d a c e))))
      = add (parity_venn_part E hE P a c b) (parity_venn_part E hE P b c a)
        by add_comm (parity_venn_part E hE P b c a) (parity_venn_part E hE P a c b) ∎

{` E'_ab does not depend on the order of a and b. `}
def parity_venn_part_swap (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (a b c : LocalSections E P)
  : Id Nat (parity_venn_part E hE P a b c) (parity_venn_part E hE P b a c)
  ≔ let d ≔ parity_differ E P in
    finite_true_count_homotopy E hE (e ↦ bool_and (bool_not (d a b e)) (d a c e)) (e ↦ bool_and (bool_not (d b a e)) (d b c e))
      (e ↦ let X ≔ P e .fst .fst in let h ≔ two_set_two_element (P e) in
        calc bool_and (bool_not (d a b e)) (d a c e)
          = bool_and (bool_not (d a b e)) (bool_xor (d a b e) (d a c e)) by bool_and_not_left_xor (d a b e) (d a c e)
          = bool_and (bool_not (d b a e)) (bool_xor (d b a e) (d a c e))
            by refl ((x ↦ bool_and (bool_not x) (bool_xor x (d a c e))) : Bool → Bool) (two_differ_symm X h (a e) (b e))
          = bool_and (bool_not (d b a e)) (d b c e)
            by refl (bool_and (bool_not (d b a e)))
              (inverse Bool (d b c e) (bool_xor (d b a e) (d a c e)) (two_differ_cocycle X h (b e) (a e) (c e))) ∎)

def parity_venn_algebra (a b c : Nat)
  : Id Nat (add (add (add b c) (add a c)) (add a b)) (add (add (add a b) c) (add (add a b) c))
  ≔ calc add (add (add b c) (add a c)) (add a b)
      = add (add (add b a) (add c c)) (add a b) by refl ((z ↦ add z (add a b)) : Nat → Nat) (add_interchange b c a c)
      = add (add (add b a) (add a b)) (add c c) by add_swap_tail (add b a) (add c c) (add a b)
      = add (add (add a b) (add a b)) (add c c) by refl ((z ↦ add (add z (add a b)) (add c c)) : Nat → Nat) (add_comm b a)
      = add (add (add a b) c) (add (add a b) c)
        by inverse Nat (add (add (add a b) c) (add (add a b) c)) (add (add (add a b) (add a b)) (add c c))
          (add_interchange (add a b) c (add a b) c) ∎

def parity_disagreement_card (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f g : LocalSections E P) : Nat
  ≔ cardinality (ParityDisagreement E P f g) (parity_disagreement_finite E hE P f g)

{` Card(F12) + Card(F13) + Card(F23) = 2(Card(E'12) + Card(E'13) + Card(E'23)). `}
def parity_venn_count (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f1 f2 f3 : LocalSections E P)
  : Id Nat (add (add (parity_disagreement_card E hE P f1 f2) (parity_disagreement_card E hE P f1 f3)) (parity_disagreement_card E hE P f2 f3))
      (add (add (add (parity_venn_part E hE P f1 f2 f3) (parity_venn_part E hE P f1 f3 f2)) (parity_venn_part E hE P f2 f3 f1))
        (add (add (parity_venn_part E hE P f1 f2 f3) (parity_venn_part E hE P f1 f3 f2)) (parity_venn_part E hE P f2 f3 f1)))
  ≔ let v ≔ parity_venn_part E hE P in
    let a ≔ v f1 f2 f3 in let b ≔ v f1 f3 f2 in let c ≔ v f2 f3 f1 in
    let c12 : Id Nat (parity_disagreement_card E hE P f1 f2) (add b c)
      ≔ concat Nat (parity_disagreement_card E hE P f1 f2) (finite_true_count E hE (parity_differ E P f1 f2)) (add b c)
          (parity_disagreement_count E hE P f1 f2) (parity_venn_split E hE P f1 f2 f3) in
    let c13 : Id Nat (parity_disagreement_card E hE P f1 f3) (add a c)
      ≔ calc parity_disagreement_card E hE P f1 f3
          = finite_true_count E hE (parity_differ E P f1 f3) by parity_disagreement_count E hE P f1 f3
          = add a (v f3 f2 f1) by parity_venn_split E hE P f1 f3 f2
          = add a c by refl (add a) (parity_venn_part_swap E hE P f3 f2 f1) ∎ in
    let c23 : Id Nat (parity_disagreement_card E hE P f2 f3) (add a b)
      ≔ calc parity_disagreement_card E hE P f2 f3
          = finite_true_count E hE (parity_differ E P f2 f3) by parity_disagreement_count E hE P f2 f3
          = add (v f2 f1 f3) (v f3 f1 f2) by parity_venn_split E hE P f2 f3 f1
          = add a b by refl add (parity_venn_part_swap E hE P f2 f1 f3) (parity_venn_part_swap E hE P f3 f1 f2) ∎ in
    concat Nat (add (add (parity_disagreement_card E hE P f1 f2) (parity_disagreement_card E hE P f1 f3)) (parity_disagreement_card E hE P f2 f3))
      (add (add (add b c) (add a c)) (add a b)) (add (add (add a b) c) (add (add a b) c))
      (refl ((p q r ↦ add (add p q) r) : Nat → Nat → Nat → Nat) c12 c13 c23)
      (parity_venn_algebra a b c)

{` The parities of the three counts xor to false. `}
def parity_venn_odd (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f1 f2 f3 : LocalSections E P)
  : Id Bool (bool_xor (bool_xor (parity_odd E hE P f1 f2) (parity_odd E hE P f1 f3)) (parity_odd E hE P f2 f3)) false.
  ≔ let k12 ≔ parity_disagreement_card E hE P f1 f2 in
    let k13 ≔ parity_disagreement_card E hE P f1 f3 in
    let k23 ≔ parity_disagreement_card E hE P f2 f3 in
    let x ≔ add (add (parity_venn_part E hE P f1 f2 f3) (parity_venn_part E hE P f1 f3 f2)) (parity_venn_part E hE P f2 f3 f1) in
    calc bool_xor (bool_xor (nat_odd k12) (nat_odd k13)) (nat_odd k23)
      = bool_xor (nat_odd (add k12 k13)) (nat_odd k23)
        by refl ((y ↦ bool_xor y (nat_odd k23)) : Bool → Bool) (inverse Bool (nat_odd (add k12 k13)) (bool_xor (nat_odd k12) (nat_odd k13)) (nat_odd_add k12 k13))
      = nat_odd (add (add k12 k13) k23) by inverse Bool (nat_odd (add (add k12 k13) k23)) (bool_xor (nat_odd (add k12 k13)) (nat_odd k23)) (nat_odd_add (add k12 k13) k23)
      = nat_odd (add x x) by refl nat_odd (parity_venn_count E hE P f1 f2 f3)
      = false. by nat_odd_double x ∎

{` "If two of the F_ij have an even number of elements, then so does the
   third": transitivity of ∼ from the count. `}
def parity_venn_transitive (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f1 f2 f3 : LocalSections E P)
  (r12 : ParityRelated E hE P f1 f2) (r23 : ParityRelated E hE P f2 f3) : ParityRelated E hE P f1 f3
  ≔ let o12 ≔ parity_odd E hE P f1 f2 in let o13 ≔ parity_odd E hE P f1 f3 in let o23 ≔ parity_odd E hE P f2 f3 in
    parity_related_of_odd E hE P f1 f3
      (calc o13 = bool_xor (bool_xor false. o13) false. by inverse Bool (bool_xor o13 false.) o13 (bool_xor_false_right o13)
        = bool_xor (bool_xor o12 o13) o23
          by refl ((p q ↦ bool_xor (bool_xor p o13) q) : Bool → Bool → Bool)
            (inverse Bool o12 false. (parity_odd_of_related E hE P f1 f2 r12)) (inverse Bool o23 false. (parity_odd_of_related E hE P f2 f3 r23))
        = false. by parity_venn_odd E hE P f1 f2 f3 ∎)

{` "At least one of the F_ij has even cardinality". `}
def parity_venn_one_even_step (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f1 f2 f3 : LocalSections E P)
  (u v w : Bool) (qu : Id Bool (parity_odd E hE P f1 f2) u) (qv : Id Bool (parity_odd E hE P f1 f3) v) (qw : Id Bool (parity_odd E hE P f2 f3) w)
  (x : Id Bool (bool_xor (bool_xor u v) w) false.)
  : Sum (ParityRelated E hE P f1 f2) (Sum (ParityRelated E hE P f1 f3) (ParityRelated E hE P f2 f3))
  ≔ match u, v, w [
  | false., _, _ ↦ inl. (parity_related_of_odd E hE P f1 f2 qu)
  | true., false., _ ↦ inr. (inl. (parity_related_of_odd E hE P f1 f3 qv))
  | true., true., false. ↦ inr. (inr. (parity_related_of_odd E hE P f2 f3 qw))
  | true., true., true. ↦ match bool_encode true. false. x [] ]

def parity_venn_one_even (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f1 f2 f3 : LocalSections E P)
  : Sum (ParityRelated E hE P f1 f2) (Sum (ParityRelated E hE P f1 f3) (ParityRelated E hE P f2 f3))
  ≔ let o12 ≔ parity_odd E hE P f1 f2 in let o13 ≔ parity_odd E hE P f1 f3 in let o23 ≔ parity_odd E hE P f2 f3 in
    parity_venn_one_even_step E hE P f1 f2 f3 o12 o13 o23 (refl o12) (refl o13) (refl o23) (parity_venn_odd E hE P f1 f2 f3)
