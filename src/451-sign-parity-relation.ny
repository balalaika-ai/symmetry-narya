export "450-sign-parity-basics"

{` Chapter 4, sec:sign-homomorphism: the parity relation (definition at
   group.tex:1473) and lem:parityequiv. E is a finite set and P : E → BΣ_2 a
   family of two-element sets; BΣ_2 is BookFiniteSetsAt two, the classifying
   type of symmetric_group two. `}

def two_set_two_element (T : BookFiniteSetsAt two) : TwoElement (T .fst .fst)
  ≔ trunc_map native_truncation (Id SetTypes (Fin two, fin_set two) (T .fst)) (Id Type (Fin two) (T .fst .fst))
      (p ↦ p .fst) (T .snd)

{` The set Π_{e:E} P(e). `}
def LocalSections (E : Type) (P : E → BookFiniteSetsAt two) : Type ≔ (e : E) → P e .fst .fst

def local_sections_set (E : Type) (P : E → BookFiniteSetsAt two) : isSet (LocalSections E P)
  ≔ pi_set E (e ↦ P e .fst .fst) (e ↦ P e .fst .snd)

def bool_decide_false (b : Bool) : Decidable (Id Bool b false.)
  ≔ match b [ false. ↦ inl. (refl (false. : Bool)) | true. ↦ inr. (q ↦ bool_encode true. false. q) ]

def decidable_not (X : Type) (d : Decidable X) : Decidable (Not X)
  ≔ match d [ inl. x ↦ inr. (n ↦ n x) | inr. n ↦ inl. n ]

{` The subset { e : E | f(e) ≠ g(e) }; it is finite because two-element sets
   have decidable equality (footnote of the definition). `}
def ParityDisagreement (E : Type) (P : E → BookFiniteSetsAt two) (f g : LocalSections E P) : Type
  ≔ Σ E (e ↦ Not (Id (P e .fst .fst) (f e) (g e)))

def parity_disagreement_finite (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f g : LocalSections E P)
  : IsFinite (ParityDisagreement E P f g)
  ≔ finite_decidable_subset E hE (e ↦ Not (Id (P e .fst .fst) (f e) (g e)))
      (e ↦ negation_prop (Id (P e .fst .fst) (f e) (g e)))
      (e ↦ decidable_not (Id (P e .fst .fst) (f e) (g e))
        (two_element_decidable_equality (P e .fst .fst) (two_set_two_element (P e)) (f e) (g e)))

{` Definition (group.tex:1473): f ∼ g iff the disagreement subset has an even
   number of elements. `}
def ParityRelated (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f g : LocalSections E P) : Type
  ≔ IsEvenNat (cardinality (ParityDisagreement E P f g) (parity_disagreement_finite E hE P f g))

def parity_related_prop (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f g : LocalSections E P)
  : isProp (ParityRelated E hE P f g)
  ≔ is_even_nat_prop (cardinality (ParityDisagreement E P f g) (parity_disagreement_finite E hE P f g))

{` The parity of the disagreement, false = even. `}
def parity_odd (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f g : LocalSections E P) : Bool
  ≔ nat_odd (cardinality (ParityDisagreement E P f g) (parity_disagreement_finite E hE P f g))

def parity_related_iff (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f g : LocalSections E P)
  : Equiv (ParityRelated E hE P f g) (Id Bool (parity_odd E hE P f g) false.)
  ≔ is_even_nat_iff (cardinality (ParityDisagreement E P f g) (parity_disagreement_finite E hE P f g))

{` Footnote: the parity relation is decidable. `}
def parity_related_decidable (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f g : LocalSections E P)
  : Decidable (ParityRelated E hE P f g)
  ≔ let e ≔ parity_related_iff E hE P f g in
    match bool_decide_false (parity_odd E hE P f g) [
    | inl. q ↦ inl. (equiv_inverse_map (ParityRelated E hE P f g) (Id Bool (parity_odd E hE P f g) false.) e q)
    | inr. n ↦ inr. (r ↦ n (e .map r)) ]

def parity_differ (E : Type) (P : E → BookFiniteSetsAt two) (f g : LocalSections E P) : E → Bool
  ≔ e ↦ two_differ (P e .fst .fst) (two_set_two_element (P e)) (f e) (g e)

def parity_disagreement_count (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f g : LocalSections E P)
  : Id Nat (cardinality (ParityDisagreement E P f g) (parity_disagreement_finite E hE P f g))
      (finite_true_count E hE (parity_differ E P f g))
  ≔ cardinality_equiv (ParityDisagreement E P f g) (Σ E (e ↦ Id Bool (parity_differ E P f g e) true.))
      (family_equiv E (e ↦ Not (Id (P e .fst .fst) (f e) (g e))) (e ↦ Id Bool (parity_differ E P f g e) true.)
        (e ↦ iff_equiv (Not (Id (P e .fst .fst) (f e) (g e))) (Id Bool (parity_differ E P f g e) true.)
          (negation_prop (Id (P e .fst .fst) (f e) (g e))) (bool_set (parity_differ E P f g e) true.)
          (two_differ_ne (P e .fst .fst) (two_set_two_element (P e)) (f e) (g e))
          (two_differ_true (P e .fst .fst) (two_set_two_element (P e)) (f e) (g e))))
      (parity_disagreement_finite E hE P f g) (finite_true_subset E hE (parity_differ E P f g))

def parity_odd_count (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f g : LocalSections E P)
  : Id Bool (parity_odd E hE P f g) (nat_odd (finite_true_count E hE (parity_differ E P f g)))
  ≔ refl nat_odd (parity_disagreement_count E hE P f g)

{` The cocycle law: parity(f, h) = parity(f, g) xor parity(g, h). `}
def parity_odd_cocycle (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f g h : LocalSections E P)
  : Id Bool (parity_odd E hE P f h) (bool_xor (parity_odd E hE P f g) (parity_odd E hE P g h))
  ≔ let dfg ≔ parity_differ E P f g in let dgh ≔ parity_differ E P g h in
    calc parity_odd E hE P f h
      = nat_odd (finite_true_count E hE (parity_differ E P f h)) by parity_odd_count E hE P f h
      = nat_odd (finite_true_count E hE (e ↦ bool_xor (dfg e) (dgh e)))
        by refl nat_odd (finite_true_count_homotopy E hE (parity_differ E P f h) (e ↦ bool_xor (dfg e) (dgh e))
          (e ↦ two_differ_cocycle (P e .fst .fst) (two_set_two_element (P e)) (f e) (g e) (h e)))
      = bool_xor (nat_odd (finite_true_count E hE dfg)) (nat_odd (finite_true_count E hE dgh))
        by finite_true_count_xor E hE hE dfg dgh
      = bool_xor (parity_odd E hE P f g) (parity_odd E hE P g h)
        by bool_xor_path (nat_odd (finite_true_count E hE dfg)) (parity_odd E hE P f g)
          (nat_odd (finite_true_count E hE dgh)) (parity_odd E hE P g h)
          (inverse Bool (parity_odd E hE P f g) (nat_odd (finite_true_count E hE dfg)) (parity_odd_count E hE P f g))
          (inverse Bool (parity_odd E hE P g h) (nat_odd (finite_true_count E hE dgh)) (parity_odd_count E hE P g h)) ∎

def parity_odd_refl (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f : LocalSections E P)
  : Id Bool (parity_odd E hE P f f) false.
  ≔ concat Bool (parity_odd E hE P f f) (nat_odd (finite_true_count E hE (parity_differ E P f f))) false.
      (parity_odd_count E hE P f f)
      (refl nat_odd (finite_true_count_false E hE (parity_differ E P f f)
        (e ↦ two_differ_refl (P e .fst .fst) (two_set_two_element (P e)) (f e))))

def parity_odd_symm (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f g : LocalSections E P)
  : Id Bool (parity_odd E hE P f g) (parity_odd E hE P g f)
  ≔ calc parity_odd E hE P f g
      = nat_odd (finite_true_count E hE (parity_differ E P f g)) by parity_odd_count E hE P f g
      = nat_odd (finite_true_count E hE (parity_differ E P g f))
        by refl nat_odd (finite_true_count_homotopy E hE (parity_differ E P f g) (parity_differ E P g f)
          (e ↦ two_differ_symm (P e .fst .fst) (two_set_two_element (P e)) (f e) (g e)))
      = parity_odd E hE P g f
        by inverse Bool (parity_odd E hE P g f) (nat_odd (finite_true_count E hE (parity_differ E P g f)))
          (parity_odd_count E hE P g f) ∎

def parity_related_of_odd (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f g : LocalSections E P)
  (q : Id Bool (parity_odd E hE P f g) false.) : ParityRelated E hE P f g
  ≔ equiv_inverse_map (ParityRelated E hE P f g) (Id Bool (parity_odd E hE P f g) false.) (parity_related_iff E hE P f g) q

def parity_odd_of_related (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f g : LocalSections E P)
  (r : ParityRelated E hE P f g) : Id Bool (parity_odd E hE P f g) false.
  ≔ parity_related_iff E hE P f g .map r

{` lem:parityequiv, first part: ∼ is an equivalence relation. `}
def parity_relation (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) : EquivalenceRelation (LocalSections E P)
  ≔ ((f g ↦ (ParityRelated E hE P f g, parity_related_prop E hE P f g)),
      (f ↦ parity_related_of_odd E hE P f f (parity_odd_refl E hE P f)),
      (f g r ↦ parity_related_of_odd E hE P g f
        (concat Bool (parity_odd E hE P g f) (parity_odd E hE P f g) false.
          (parity_odd_symm E hE P g f) (parity_odd_of_related E hE P f g r))),
      (f g h r s ↦ parity_related_of_odd E hE P f h
        (calc parity_odd E hE P f h
          = bool_xor (parity_odd E hE P f g) (parity_odd E hE P g h) by parity_odd_cocycle E hE P f g h
          = bool_xor false. false. by bool_xor_path (parity_odd E hE P f g) false. (parity_odd E hE P g h) false.
              (parity_odd_of_related E hE P f g r) (parity_odd_of_related E hE P g h s)
          = false. by refl (false. : Bool) ∎)))

{` The quotient (Π_{e:E} P(e))/∼. `}
def ParityQuotient (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) : Type
  ≔ Quotient (LocalSections E P) (parity_relation E hE P)

def parity_class (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f : LocalSections E P)
  : ParityQuotient E hE P
  ≔ quotient_class (LocalSections E P) (parity_relation E hE P) f

def parity_quotient_set (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) : isSet (ParityQuotient E hE P)
  ≔ quotient_set (LocalSections E P) (parity_relation E hE P)

def parity_class_path (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f g : LocalSections E P)
  (q : Id Bool (parity_odd E hE P f g) false.)
  : Id (ParityQuotient E hE P) (parity_class E hE P f) (parity_class E hE P g)
  ≔ quotient_encode (LocalSections E P) (parity_relation E hE P) f g (parity_related_of_odd E hE P f g q)

def parity_class_path_odd (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f g : LocalSections E P)
  (p : Id (ParityQuotient E hE P) (parity_class E hE P f) (parity_class E hE P g))
  : Id Bool (parity_odd E hE P f g) false.
  ≔ parity_odd_of_related E hE P f g
      (quotient_effective (LocalSections E P) (parity_relation E hE P) f g .map p)

{` The class of f measured against a base section f0, as a Boolean. `}
def parity_quotient_map (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f0 : LocalSections E P)
  : ParityQuotient E hE P → Bool
  ≔ quotient_rec (LocalSections E P) Bool (parity_relation E hE P) bool_set (f ↦ parity_odd E hE P f f0)
      (f g r ↦ calc parity_odd E hE P f f0
        = bool_xor (parity_odd E hE P f g) (parity_odd E hE P g f0) by parity_odd_cocycle E hE P f g f0
        = bool_xor false. (parity_odd E hE P g f0)
          by refl ((x ↦ bool_xor x (parity_odd E hE P g f0)) : Bool → Bool) (parity_odd_of_related E hE P f g r)
        = parity_odd E hE P g f0 by refl (parity_odd E hE P g f0) ∎)

{` Flipping a section at one point e0 of E. `}
def two_flip_at (A : Type) (h : TwoElement A) (x : A) (D : Type) (d : Decidable D) : A
  ≔ match d [ inl. _ ↦ two_element_other A h x | inr. _ ↦ x ]

def two_flip_at_differ (A : Type) (h : TwoElement A) (x : A) (D : Type) (d : Decidable D)
  : Id Bool (two_differ A h (two_flip_at A h x D d) x) (bool_not (decision_differ D d))
  ≔ match d [
  | inl. _ ↦ two_differ_ne A h (two_element_other A h x) x (two_element_other_ne A h x)
  | inr. _ ↦ two_differ_refl A h x ]

def local_section_flip (E : Type) (dE : DecidableEquality E) (P : E → BookFiniteSetsAt two) (f : LocalSections E P) (e0 : E)
  : LocalSections E P
  ≔ e ↦ two_flip_at (P e .fst .fst) (two_set_two_element (P e)) (f e) (Id E e e0) (dE e e0)

def decision_not_differ_iff (D : Type) (hD : isProp D) (d : Decidable D)
  : Equiv (Id Bool (bool_not (decision_differ D d)) true.) D
  ≔ match d [
  | inl. p ↦ iff_equiv (Id Bool true. true.) D (bool_set true. true.) hD (_ ↦ p) (_ ↦ refl (true. : Bool))
  | inr. n ↦ iff_equiv (Id Bool false. true.) D (bool_set false. true.) hD
      (q ↦ absurd D (bool_encode false. true. q)) (p ↦ absurd (Id Bool false. true.) (n p)) ]

def parity_odd_flip (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f : LocalSections E P) (e0 : E)
  : Id Bool (parity_odd E hE P (local_section_flip E (finite_decidable_equality E hE) P f e0) f) true.
  ≔ let dE ≔ finite_decidable_equality E hE in
    let g ≔ local_section_flip E dE P f e0 in
    let b : E → Bool ≔ e ↦ bool_not (decision_differ (Id E e e0) (dE e e0)) in
    calc parity_odd E hE P g f
      = nat_odd (finite_true_count E hE (parity_differ E P g f)) by parity_odd_count E hE P g f
      = nat_odd (finite_true_count E hE b)
        by refl nat_odd (finite_true_count_homotopy E hE (parity_differ E P g f) b
          (e ↦ two_flip_at_differ (P e .fst .fst) (two_set_two_element (P e)) (f e) (Id E e e0) (dE e e0)))
      = nat_odd (suc. zero.)
        by refl nat_odd (finite_true_count_single E hE b e0
          (e ↦ decision_not_differ_iff (Id E e e0) (finite_sethood E hE e e0) (dE e e0)))
      = true. by refl (true. : Bool) ∎

{` Given a base section f0 and a point e0, the inverse of parity_quotient_map. `}
def parity_quotient_section (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f0 : LocalSections E P) (e0 : E)
  : Bool → ParityQuotient E hE P
  ≔ [ false. ↦ parity_class E hE P f0
    | true. ↦ parity_class E hE P (local_section_flip E (finite_decidable_equality E hE) P f0 e0) ]

def parity_quotient_section_at (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f0 : LocalSections E P) (e0 : E)
  (f : LocalSections E P) (b : Bool) (q : Id Bool (parity_odd E hE P f f0) b)
  : Id (ParityQuotient E hE P) (parity_quotient_section E hE P f0 e0 b) (parity_class E hE P f)
  ≔ let g ≔ local_section_flip E (finite_decidable_equality E hE) P f0 e0 in
    match b [
    | false. ↦ parity_class_path E hE P f0 f
        (concat Bool (parity_odd E hE P f0 f) (parity_odd E hE P f f0) false. (parity_odd_symm E hE P f0 f) q)
    | true. ↦ parity_class_path E hE P g f
        (calc parity_odd E hE P g f
          = bool_xor (parity_odd E hE P g f0) (parity_odd E hE P f0 f) by parity_odd_cocycle E hE P g f0 f
          = bool_xor true. true. by bool_xor_path (parity_odd E hE P g f0) true. (parity_odd E hE P f0 f) true.
              (parity_odd_flip E hE P f0 e0)
              (concat Bool (parity_odd E hE P f0 f) (parity_odd E hE P f f0) true. (parity_odd_symm E hE P f0 f) q)
          = false. by refl (false. : Bool) ∎) ]

def parity_quotient_inverse_equiv (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f0 : LocalSections E P) (e0 : E)
  : Equiv (ParityQuotient E hE P) Bool
  ≔ quasi_inverse_equiv (ParityQuotient E hE P) Bool (parity_quotient_map E hE P f0)
      (parity_quotient_section E hE P f0 e0)
      (quotient_prop_induction (LocalSections E P) (parity_relation E hE P)
        (z ↦ Id (ParityQuotient E hE P) (parity_quotient_section E hE P f0 e0 (parity_quotient_map E hE P f0 z)) z)
        (z ↦ parity_quotient_set E hE P (parity_quotient_section E hE P f0 e0 (parity_quotient_map E hE P f0 z)) z)
        (f ↦ parity_quotient_section_at E hE P f0 e0 f (parity_odd E hE P f f0) (refl (parity_odd E hE P f f0))))
      [ false. ↦ parity_odd_refl E hE P f0
      | true. ↦ parity_odd_flip E hE P f0 e0 ]

{` For E nonempty, the class map measured against any base section is an
   equivalence (ParityQuotient E hE P) ≃ Bool. `}
def parity_quotient_equiv (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f0 : LocalSections E P) (ne : Mere E)
  : Equiv (ParityQuotient E hE P) Bool
  ≔ (parity_quotient_map E hE P f0,
      mere_rec E (isEquiv (ParityQuotient E hE P) Bool (parity_quotient_map E hE P f0))
        (isequiv_isprop (ParityQuotient E hE P) Bool (parity_quotient_map E hE P f0))
        (e0 ↦ parity_quotient_inverse_equiv E hE P f0 e0 .equiv) ne)

{` The identification of Fin 2 = {0, 1} with Bool used throughout: 0 ↦ false
   (even, +1) and 1 ↦ true (odd, −1). In Fin 2, 0 = inr star. `}
def fin_two_parity : Fin two → Bool ≔ [ inl. _ ↦ true. | inr. _ ↦ false. ]

def parity_fin_two : Bool → Fin two ≔ [ false. ↦ inr. star. | true. ↦ inl. (inr. star.) ]

def fin_two_parity_equiv : Equiv (Fin two) Bool
  ≔ quasi_inverse_equiv (Fin two) Bool fin_two_parity parity_fin_two
      [ inl. (inl. e) ↦ match e []
      | inl. (inr. u) ↦ inl. (inr. (unit_prop star. u))
      | inr. u ↦ inr. (unit_prop star. u) ]
      [ false. ↦ refl (false. : Bool) | true. ↦ refl (true. : Bool) ]

def local_sections_mere (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) : Mere (LocalSections E P)
  ≔ finite_choice E hE (e ↦ P e .fst .fst) (e ↦ two_element_mere_point (P e .fst .fst) (two_set_two_element (P e)))

{` lem:parityequiv, second part: for E nonempty the quotient is a
   two-element set. `}
def parity_quotient_two_element (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (ne : Mere E)
  : TwoElement (ParityQuotient E hE P)
  ≔ mere_rec (LocalSections E P) (TwoElement (ParityQuotient E hE P)) (two_element_prop (ParityQuotient E hE P))
      (f0 ↦ mere (Id Type (Fin two) (ParityQuotient E hE P))
        (ua (Fin two) (ParityQuotient E hE P)
          (compose_equiv (Fin two) Bool (ParityQuotient E hE P) fin_two_parity_equiv
            (canonical_inverse_equiv (ParityQuotient E hE P) Bool (parity_quotient_equiv E hE P f0 ne)))))
      (local_sections_mere E hE P)

{` The quotient as a point of BΣ_2 (for E nonempty). `}
def two_element_bsigma_two (S : SetTypes) (h : TwoElement (S .fst)) : BookFiniteSetsAt two
  ≔ (S, trunc_map native_truncation (Id Type (Fin two) (S .fst)) (Id SetTypes (Fin two, fin_set two) S)
      (p ↦ subtype_equal Type isSet isset_isprop (Fin two, fin_set two) S p) h)

def parity_quotient_bsigma_two (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (ne : Mere E)
  : BookFiniteSetsAt two
  ≔ two_element_bsigma_two (ParityQuotient E hE P, parity_quotient_set E hE P) (parity_quotient_two_element E hE P ne)

{` lem:parityequiv, third part: for E empty the quotient is contractible, a
   one-element set. `}
def parity_quotient_empty_contractible (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (no : Not (Mere E))
  : BookIsContr (ParityQuotient E hE P)
  ≔ let f0 : LocalSections E P ≔ e ↦ absurd (P e .fst .fst) (no (mere E e)) in
    (parity_class E hE P f0,
      quotient_prop_induction (LocalSections E P) (parity_relation E hE P)
        (z ↦ Id (ParityQuotient E hE P) (parity_class E hE P f0) z)
        (z ↦ parity_quotient_set E hE P (parity_class E hE P f0) z)
        (f ↦ refl (parity_class E hE P)
          (funext E (e ↦ P e .fst .fst) f0 f (e ↦ absurd (Id (P e .fst .fst) (f0 e) (f e)) (no (mere E e))))))

def parity_quotient_empty_one_element (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (no : Not (Mere E))
  : Id Type (ParityQuotient E hE P) (Fin (suc. zero.))
  ≔ ua (ParityQuotient E hE P) (Fin (suc. zero.))
      (compose_equiv (ParityQuotient E hE P) Unit (Fin (suc. zero.))
        (contractible_unit_equiv (ParityQuotient E hE P)
          (native_contraction (ParityQuotient E hE P) (parity_quotient_empty_contractible E hE P no)))
        (canonical_inverse_equiv (Fin (suc. zero.)) Unit fin_one_equiv))

{` Proof remark of lem:parityequiv: the quotient has at most two elements,
   i.e. of three sections two are related. `}
def parity_quotient_at_most_two (E : Type) (hE : IsFinite E) (P : E → BookFiniteSetsAt two) (f1 f2 f3 : LocalSections E P)
  : Sum (ParityRelated E hE P f1 f2) (Sum (ParityRelated E hE P f2 f3) (ParityRelated E hE P f1 f3))
  ≔ let o12 ≔ parity_odd E hE P f1 f2 in let o23 ≔ parity_odd E hE P f2 f3 in
    let step : (b c : Bool) → Id Bool o12 b → Id Bool o23 c →
        Sum (ParityRelated E hE P f1 f2) (Sum (ParityRelated E hE P f2 f3) (ParityRelated E hE P f1 f3))
      ≔ b c qb qc ↦ match b, c [
        | false., _ ↦ inl. (parity_related_of_odd E hE P f1 f2 qb)
        | true., false. ↦ inr. (inl. (parity_related_of_odd E hE P f2 f3 qc))
        | true., true. ↦ inr. (inr. (parity_related_of_odd E hE P f1 f3
            (calc parity_odd E hE P f1 f3 = bool_xor o12 o23 by parity_odd_cocycle E hE P f1 f2 f3
              = bool_xor true. true. by bool_xor_path o12 true. o23 true. qb qc
              = false. by refl (false. : Bool) ∎))) ] in
    step o12 o23 (refl o12) (refl o23)

{` Litmus checks with E = Fin 1 and E = Fin 2 and the constant family at the
   standard two-element set: for Fin 1 the constant sections at 0 and 1 are not
   related (one disagreement); for Fin 2 they are related (two disagreements). `}
def parity_constant_family (E : Type) : E → BookFiniteSetsAt two ≔ _ ↦ shape (symmetric_group two)

def fin_two_zero_ne_one (p : Id (Fin two) (inr. star.) (inl. (inr. star.))) : Empty
  ≔ sum_encode (Fin (suc. zero.)) Unit (inr. star.) (inl. (inr. star.)) p

def parity_litmus_differ (E : Type) (e : E)
  : Id Bool (parity_differ E (parity_constant_family E) (_ ↦ inr. star.) (_ ↦ inl. (inr. star.)) e) true.
  ≔ two_differ_ne (Fin two) (two_set_two_element (shape (symmetric_group two))) (inr. star.) (inl. (inr. star.))
      fin_two_zero_ne_one

def parity_litmus_fin_odd (n : Nat) (hE : IsFinite (Fin n))
  : Id Bool (parity_odd (Fin n) hE (parity_constant_family (Fin n)) (_ ↦ inr. star.) (_ ↦ inl. (inr. star.)))
      (nat_odd (true_count n (_ ↦ true.)))
  ≔ let P ≔ parity_constant_family (Fin n) in
    let d ≔ parity_differ (Fin n) P (_ ↦ inr. star.) (_ ↦ inl. (inr. star.)) in
    calc parity_odd (Fin n) hE P (_ ↦ inr. star.) (_ ↦ inl. (inr. star.))
      = nat_odd (finite_true_count (Fin n) hE d) by parity_odd_count (Fin n) hE P (_ ↦ inr. star.) (_ ↦ inl. (inr. star.))
      = nat_odd (finite_true_count (Fin n) hE (_ ↦ true.))
        by refl nat_odd (finite_true_count_homotopy (Fin n) hE d (_ ↦ true.) (parity_litmus_differ (Fin n)))
      = nat_odd (true_count n (_ ↦ true.)) by refl nat_odd (finite_true_count_fin n hE (_ ↦ true.)) ∎

def parity_litmus_one_not_related
  (r : ParityRelated (Fin (suc. zero.)) (fin_is_finite (suc. zero.)) (parity_constant_family (Fin (suc. zero.)))
    (_ ↦ inr. star.) (_ ↦ inl. (inr. star.))) : Empty
  ≔ bool_encode true. false.
      (concat Bool true. (parity_odd (Fin (suc. zero.)) (fin_is_finite (suc. zero.)) (parity_constant_family (Fin (suc. zero.)))
          (_ ↦ inr. star.) (_ ↦ inl. (inr. star.))) false.
        (inverse Bool (parity_odd (Fin (suc. zero.)) (fin_is_finite (suc. zero.)) (parity_constant_family (Fin (suc. zero.)))
          (_ ↦ inr. star.) (_ ↦ inl. (inr. star.))) true. (parity_litmus_fin_odd (suc. zero.) (fin_is_finite (suc. zero.))))
        (parity_odd_of_related (Fin (suc. zero.)) (fin_is_finite (suc. zero.)) (parity_constant_family (Fin (suc. zero.)))
          (_ ↦ inr. star.) (_ ↦ inl. (inr. star.)) r))

def parity_litmus_two_related
  : ParityRelated (Fin two) (fin_is_finite two) (parity_constant_family (Fin two)) (_ ↦ inr. star.) (_ ↦ inl. (inr. star.))
  ≔ parity_related_of_odd (Fin two) (fin_is_finite two) (parity_constant_family (Fin two)) (_ ↦ inr. star.) (_ ↦ inl. (inr. star.))
      (parity_litmus_fin_odd two (fin_is_finite two))

{` For E = Fin 1 the two classes are distinct, for E = Fin 2 they coincide. `}
def parity_litmus_one_classes_differ
  (p : Id (ParityQuotient (Fin (suc. zero.)) (fin_is_finite (suc. zero.)) (parity_constant_family (Fin (suc. zero.))))
    (parity_class (Fin (suc. zero.)) (fin_is_finite (suc. zero.)) (parity_constant_family (Fin (suc. zero.))) (_ ↦ inr. star.))
    (parity_class (Fin (suc. zero.)) (fin_is_finite (suc. zero.)) (parity_constant_family (Fin (suc. zero.))) (_ ↦ inl. (inr. star.))))
  : Empty
  ≔ parity_litmus_one_not_related
      (quotient_effective (LocalSections (Fin (suc. zero.)) (parity_constant_family (Fin (suc. zero.))))
        (parity_relation (Fin (suc. zero.)) (fin_is_finite (suc. zero.)) (parity_constant_family (Fin (suc. zero.))))
        (_ ↦ inr. star.) (_ ↦ inl. (inr. star.)) .map p)

def parity_litmus_two_classes_equal
  : Id (ParityQuotient (Fin two) (fin_is_finite two) (parity_constant_family (Fin two)))
      (parity_class (Fin two) (fin_is_finite two) (parity_constant_family (Fin two)) (_ ↦ inr. star.))
      (parity_class (Fin two) (fin_is_finite two) (parity_constant_family (Fin two)) (_ ↦ inl. (inr. star.)))
  ≔ quotient_encode (LocalSections (Fin two) (parity_constant_family (Fin two)))
      (parity_relation (Fin two) (fin_is_finite two) (parity_constant_family (Fin two)))
      (_ ↦ inr. star.) (_ ↦ inl. (inr. star.)) parity_litmus_two_related
