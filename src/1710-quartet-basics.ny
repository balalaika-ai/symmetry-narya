export "1704-sets-cover"

{` Infrastructure for the choice theorems about 4-element sets
   (thm:lAC-2-3-4 and the theorem of Tarski in choicefin.tex): the standard
   4-element set Fin 4 with named elements and case analysis, boolean
   connectives, and the transfer of propositions from Fin 4 to every
   4-element set along a mere identification. `}
def quartet_four : Nat ≔ suc. (suc. (suc. (suc. zero.)))
def quartet_three : Nat ≔ suc. (suc. (suc. zero.))

{` The elements 0, 1, 2, 3 of Fin 4 in the naming of fin_below_equiv. `}
def quartet_e0 : Fin quartet_four ≔ inr. star.
def quartet_e1 : Fin quartet_four ≔ inl. (inr. star.)
def quartet_e2 : Fin quartet_four ≔ inl. (inl. (inr. star.))
def quartet_e3 : Fin quartet_four ≔ inl. (inl. (inl. (inr. star.)))

def quartet_cases (P : Fin quartet_four → Type) (p0 : P quartet_e0) (p1 : P quartet_e1)
  (p2 : P quartet_e2) (p3 : P quartet_e3) : (x : Fin quartet_four) → P x
  ≔ [
  | inr. u ↦ match u [ star. ↦ p0 ]
  | inl. y ↦ match y [
    | inr. u ↦ match u [ star. ↦ p1 ]
    | inl. z ↦ match z [
      | inr. u ↦ match u [ star. ↦ p2 ]
      | inl. w ↦ match w [
        | inr. u ↦ match u [ star. ↦ p3 ]
        | inl. e ↦ match e [] ] ] ] ]

{` The elements 0, 1, 2 of Fin 3 and case analysis on Fin 3. `}
def quartet_t0 : Fin quartet_three ≔ inr. star.
def quartet_t1 : Fin quartet_three ≔ inl. (inr. star.)
def quartet_t2 : Fin quartet_three ≔ inl. (inl. (inr. star.))

def quartet_trio_cases (P : Fin quartet_three → Type) (p0 : P quartet_t0) (p1 : P quartet_t1)
  (p2 : P quartet_t2) : (x : Fin quartet_three) → P x
  ≔ [
  | inr. u ↦ match u [ star. ↦ p0 ]
  | inl. y ↦ match y [
    | inr. u ↦ match u [ star. ↦ p1 ]
    | inl. z ↦ match z [
      | inr. u ↦ match u [ star. ↦ p2 ]
      | inl. e ↦ match e [] ] ] ]

{` Boolean equality test on Fin 4 and its soundness. `}
def quartet_eqb (x y : Fin quartet_four) : Bool
  ≔ decision_bool (Id (Fin quartet_four) x y) (fin_decidable_equality quartet_four x y)

def quartet_eqb_sound (x y : Fin quartet_four) (e : Id Bool (quartet_eqb x y) true.) : Id (Fin quartet_four) x y
  ≔ decision_bool_reflect (Id (Fin quartet_four) x y) (fin_decidable_equality quartet_four x y) e

def quartet_ne (x y : Fin quartet_four) (e : Id Bool (quartet_eqb x y) false.) : Not (Id (Fin quartet_four) x y)
  ≔ p ↦ bool_encode true. false.
      (concat Bool true. (quartet_eqb x y) false.
        (inverse Bool (quartet_eqb x y) true.
          (decision_bool_true (Id (Fin quartet_four) x y) (fin_decidable_equality quartet_four x y) p)) e)

{` A value differing from every element other than d is d. `}
def quartet_pin (y d : Fin quartet_four)
  (h : (z : Fin quartet_four) → Not (Id (Fin quartet_four) z d) → Not (Id (Fin quartet_four) y z))
  : Id (Fin quartet_four) y d
  ≔ match fin_decidable_equality quartet_four y d [
  | inl. p ↦ p
  | inr. n ↦ absurd (Id (Fin quartet_four) y d) (h y n (refl y)) ]

{` Boolean connectives and their laws. `}
def quartet_and (a b : Bool) : Bool ≔ match a [ false. ↦ false. | true. ↦ b ]
def quartet_or (a b : Bool) : Bool ≔ match a [ false. ↦ b | true. ↦ true. ]

def quartet_and_left (a b : Bool) (e : Id Bool (quartet_and a b) true.) : Id Bool a true.
  ≔ match a [ false. ↦ absurd (Id Bool false. true.) (bool_encode false. true. e) | true. ↦ refl (true. : Bool) ]

def quartet_and_right (a b : Bool) (e : Id Bool (quartet_and a b) true.) : Id Bool b true.
  ≔ match a [ false. ↦ absurd (Id Bool b true.) (bool_encode false. true. e) | true. ↦ e ]

def quartet_and_intro (a b : Bool) (ea : Id Bool a true.) (eb : Id Bool b true.) : Id Bool (quartet_and a b) true.
  ≔ match a [ false. ↦ absurd (Id Bool false. true.) (bool_encode false. true. ea) | true. ↦ eb ]

def quartet_or_cases (a b : Bool) (e : Id Bool (quartet_or a b) true.)
  : Sum (Id Bool a true.) (Id Bool b true.)
  ≔ match a [ false. ↦ inr. e | true. ↦ inl. (refl (true. : Bool)) ]

def quartet_not_true (a : Bool) (e : Id Bool (bool_not a) true.) : Id Bool a true. → Empty
  ≔ match a [ false. ↦ p ↦ bool_encode false. true. p | true. ↦ _ ↦ bool_encode false. true. e ]

{` Two booleans with the same truth condition are equal. `}
def quartet_bool_iff (a b : Bool) (f : Id Bool a true. → Id Bool b true.) (g : Id Bool b true. → Id Bool a true.)
  : Id Bool a b
  ≔ match a, b [
  | false., false. ↦ refl (false. : Bool)
  | true., true. ↦ refl (true. : Bool)
  | false., true. ↦ absurd (Id Bool false. true.) (bool_encode false. true. (g (refl (true. : Bool))))
  | true., false. ↦ absurd (Id Bool true. false.) (bool_encode false. true. (f (refl (true. : Bool)))) ]

{` A boolean different from v is not v. `}
def quartet_bool_other (u v : Bool) (n : Not (Id Bool u v)) : Id Bool u (bool_not v)
  ≔ match u, v [
  | false., false. ↦ absurd (Id Bool false. true.) (n (refl (false. : Bool)))
  | true., true. ↦ absurd (Id Bool true. false.) (n (refl (true. : Bool)))
  | false., true. ↦ refl (false. : Bool)
  | true., false. ↦ refl (true. : Bool) ]

{` The universal quantifier over Fin 4 as a boolean, with its specification. `}
def quartet_all (Q : Fin quartet_four → Bool) : Bool
  ≔ quartet_and (Q quartet_e0) (quartet_and (Q quartet_e1) (quartet_and (Q quartet_e2) (Q quartet_e3)))

def quartet_all_sound (Q : Fin quartet_four → Bool) (e : Id Bool (quartet_all Q) true.)
  : (x : Fin quartet_four) → Id Bool (Q x) true.
  ≔ let r1 ≔ quartet_and_right (Q quartet_e0) (quartet_and (Q quartet_e1) (quartet_and (Q quartet_e2) (Q quartet_e3))) e in
    let r2 ≔ quartet_and_right (Q quartet_e1) (quartet_and (Q quartet_e2) (Q quartet_e3)) r1 in
    quartet_cases (x ↦ Id Bool (Q x) true.)
      (quartet_and_left (Q quartet_e0) (quartet_and (Q quartet_e1) (quartet_and (Q quartet_e2) (Q quartet_e3))) e)
      (quartet_and_left (Q quartet_e1) (quartet_and (Q quartet_e2) (Q quartet_e3)) r1)
      (quartet_and_left (Q quartet_e2) (Q quartet_e3) r2)
      (quartet_and_right (Q quartet_e2) (Q quartet_e3) r2)

def quartet_all_complete (Q : Fin quartet_four → Bool) (h : (x : Fin quartet_four) → Id Bool (Q x) true.)
  : Id Bool (quartet_all Q) true.
  ≔ quartet_and_intro (Q quartet_e0) (quartet_and (Q quartet_e1) (quartet_and (Q quartet_e2) (Q quartet_e3)))
      (h quartet_e0)
      (quartet_and_intro (Q quartet_e1) (quartet_and (Q quartet_e2) (Q quartet_e3)) (h quartet_e1)
        (quartet_and_intro (Q quartet_e2) (Q quartet_e3) (h quartet_e2) (h quartet_e3)))

{` Transfer of a proposition about Fin 4 to every 4-element type. `}
def quartet_transfer (Φ : Type → Type) (A : Type) (hA : isProp (Φ A)) (base : Φ (Fin quartet_four))
  (h : Mere (Id Type (Fin quartet_four) A)) : Φ A
  ≔ mere_rec (Id Type (Fin quartet_four) A) (Φ A) hA (p ↦ transport Type Φ (Fin quartet_four) A p base) h

{` A type merely identified with Fin k is a set; with Fin (k+1) it is inhabited. `}
def quartet_sized_set (k : Nat) (T : Type) (h : Mere (Id Type (Fin k) T)) : isSet T
  ≔ mere_rec (Id Type (Fin k) T) (isSet T) (isset_isprop T)
      (p ↦ transport Type isSet (Fin k) T p (fin_set k)) h

def quartet_sized_point (k : Nat) (T : Type) (h : Mere (Id Type (Fin (suc. k)) T)) : Mere T
  ≔ trunc_map native_truncation (Id Type (Fin (suc. k)) T) T
      (p ↦ transport Type (S ↦ S) (Fin (suc. k)) T p (inr. star.)) h

def quartet_sized (k : Nat) (T : Type) (h : Mere (Id Type (Fin k) T)) : FiniteSetsAt k
  ≔ ((T, quartet_sized_set k T h), h)

{` Litmus: the named elements are distinct and the test decides them. `}
def quartet_e0_ne_e3 : Not (Id (Fin quartet_four) quartet_e0 quartet_e3)
  ≔ quartet_ne quartet_e0 quartet_e3 (refl (false. : Bool))
def quartet_all_example : Id Bool (quartet_all (x ↦ quartet_eqb x x)) true. ≔ refl (true. : Bool)
