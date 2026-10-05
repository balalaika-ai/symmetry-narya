export "666-pullbacks"
export "36-cardinality-arithmetic"
export "160-logic-notations"

{` Chapter 8 (congp.tex), section "The pullback": def:intersectionand
   unionofsets (line 443) and xca:intersectionpullbackofsets with its second
   item xca:cardinalityintersectionunion (line 447).

   A subset of S is a family of propositions P : Subtypes S (module 21); the
   subset as a type is SubtypeCarrier S P = Σ_{s:S} P(s), included into S by
   the first projection. `}

{` def:intersectionand unionofsets. A ∩ B is given by P(s) × Q(s) and A ∪ B
   by P(s) ∨ Q(s), the propositional truncation of P(s) + Q(s)
   (Disjunction, module 160). The book writes "A(s) ∨ B(s)" for the union;
   the families are P and Q. `}
def SubsetIntersection (S : Type) (P Q : Subtypes S) : Subtypes S
  ≔ s ↦ (Product (P s .fst) (Q s .fst), product_prop (P s .fst) (Q s .fst) (P s .snd) (Q s .snd))

def SubsetUnion (S : Type) (P Q : Subtypes S) : Subtypes S ≔ s ↦ Disjunction (P s) (Q s)

def subset_inclusion (S : Type) (P : Subtypes S) : SubtypeCarrier S P → S ≔ x ↦ x .fst

{` xca:intersectionpullbackofsets (1). The pullback A ×_S B of the two
   inclusions (def:pullback, module 666) maps by an equivalence to A ∩ B.
   The map sends ((a, p), (b, q), r : a = b) to (b, (r_*(p), q)). The
   statement holds for every type S (the book assumes a set). `}
def SubsetPullback (S : Type) (P Q : Subtypes S) : Type
  ≔ TypePullback (SubtypeCarrier S P) (SubtypeCarrier S Q) S (subset_inclusion S P) (subset_inclusion S Q)

def subset_pullback_to_intersection (S : Type) (P Q : Subtypes S) (t : SubsetPullback S P Q)
  : SubtypeCarrier S (SubsetIntersection S P Q)
  ≔ (t .fst .snd .fst,
     (transport S (s ↦ P s .fst) (t .fst .fst .fst) (t .fst .snd .fst) (t .snd) (t .fst .fst .snd),
      t .fst .snd .snd))

def subset_intersection_to_pullback (S : Type) (P Q : Subtypes S) (u : SubtypeCarrier S (SubsetIntersection S P Q))
  : SubsetPullback S P Q
  ≔ (((u .fst, u .snd .fst), (u .fst, u .snd .snd)), refl (u .fst))

def subset_intersection_roundtrip (S : Type) (P Q : Subtypes S) (u : SubtypeCarrier S (SubsetIntersection S P Q))
  : Id (SubtypeCarrier S (SubsetIntersection S P Q))
      (subset_pullback_to_intersection S P Q (subset_intersection_to_pullback S P Q u)) u
  ≔ (refl (u .fst),
     (P (u .fst) .snd (transport S (s ↦ P s .fst) (u .fst) (u .fst) (refl (u .fst)) (u .snd .fst)) (u .snd .fst),
      refl (u .snd .snd)))

def subset_pullback_roundtrip_at (S : Type) (P Q : Subtypes S) (s : S) (p : P s .fst)
  : (t : S) (r : Id S s t) (q : Q t .fst)
    → Id (SubsetPullback S P Q)
        (subset_intersection_to_pullback S P Q (subset_pullback_to_intersection S P Q (((s, p), (t, q)), r)))
        (((s, p), (t, q)), r)
  ≔ J S s
      (t r ↦ (q : Q t .fst)
        → Id (SubsetPullback S P Q)
            (subset_intersection_to_pullback S P Q (subset_pullback_to_intersection S P Q (((s, p), (t, q)), r)))
            (((s, p), (t, q)), r))
      (q ↦ (((refl s, P s .snd (transport S (x ↦ P x .fst) s s (refl s) p) p), (refl s, refl q)), refl (refl s)))

def subset_pullback_intersection_equiv (S : Type) (P Q : Subtypes S)
  : Equiv (SubsetPullback S P Q) (SubtypeCarrier S (SubsetIntersection S P Q))
  ≔ quasi_inverse_equiv (SubsetPullback S P Q) (SubtypeCarrier S (SubsetIntersection S P Q))
      (subset_pullback_to_intersection S P Q) (subset_intersection_to_pullback S P Q)
      (t ↦ subset_pullback_roundtrip_at S P Q (t .fst .fst .fst) (t .fst .fst .snd) (t .fst .snd .fst) (t .snd)
        (t .fst .snd .snd))
      (subset_intersection_roundtrip S P Q)

def subset_pullback_intersection_book_equiv (S : Type) (P Q : Subtypes S)
  : BookEquiv (SubsetPullback S P Q) (SubtypeCarrier S (SubsetIntersection S P Q))
  ≔ book_equivalence (SubsetPullback S P Q) (SubtypeCarrier S (SubsetIntersection S P Q))
      (subset_pullback_intersection_equiv S P Q)

{` xca:intersectionpullbackofsets (2), xca:cardinalityintersectionunion.
   As printed (S finite, A and B arbitrary subsets) the cardinalities of A,
   B, A ∪ B and A ∩ B need not be defined: Card is only defined for finite
   types, and a subset of a finite set is finite exactly when it is
   decidable (subset_finite_decidable_equiv below), so for S = 1 the claim
   that all subsets are finite is excluded middle
   (all_unit_subsets_finite_lem). The corrected statement assumes that A and
   B are decidable subsets of the finite set S; then A ∪ B and A ∩ B are
   decidable too and |A| + |B| = |A ∪ B| + |A ∩ B|. `}
def pbg_product_decidable (A B : Type) (da : Decidable A) (db : Decidable B) : Decidable (Product A B)
  ≔ match da [
  | inl. a ↦ match db [ inl. b ↦ inl. (a, b) | inr. nb ↦ inr. (u ↦ nb (u .snd)) ]
  | inr. na ↦ inr. (u ↦ na (u .fst)) ]

def pbg_disjunction_decidable (A B : Type) (da : Decidable A) (db : Decidable B) : Decidable (Mere (Sum A B))
  ≔ match da [
  | inl. a ↦ inl. (mere (Sum A B) (inl. a))
  | inr. na ↦ match db [
    | inl. b ↦ inl. (mere (Sum A B) (inr. b))
    | inr. nb ↦ inr. (mere_rec (Sum A B) Empty empty_prop [ inl. a ↦ na a | inr. b ↦ nb b ]) ] ]

def subset_intersection_decidable (S : Type) (P Q : Subtypes S)
  (dP : (s : S) → Decidable (P s .fst)) (dQ : (s : S) → Decidable (Q s .fst))
  : (s : S) → Decidable (SubsetIntersection S P Q s .fst)
  ≔ s ↦ pbg_product_decidable (P s .fst) (Q s .fst) (dP s) (dQ s)

def subset_union_decidable (S : Type) (P Q : Subtypes S)
  (dP : (s : S) → Decidable (P s .fst)) (dQ : (s : S) → Decidable (Q s .fst))
  : (s : S) → Decidable (SubsetUnion S P Q s .fst)
  ≔ s ↦ pbg_disjunction_decidable (P s .fst) (Q s .fst) (dP s) (dQ s)

{` Pointwise: for propositions P, Q with P decidable,
   P + Q ≃ (P ∨ Q) + (P × Q). `}
def pbg_or_extract (P Q : Type) (hQ : isProp Q) (np : Not P) (t : Mere (Sum P Q)) : Q
  ≔ mere_rec (Sum P Q) Q hQ [ inl. p ↦ absurd Q (np p) | inr. q ↦ q ] t

def pbg_split_to (P Q : Type) (dP : Decidable P) (x : Sum P Q) : Sum (Mere (Sum P Q)) (Product P Q)
  ≔ match x [
  | inl. p ↦ inl. (mere (Sum P Q) (inl. p))
  | inr. q ↦ match dP [
    | inl. p ↦ inr. (p, q)
    | inr. _ ↦ inl. (mere (Sum P Q) (inr. q)) ] ]

def pbg_split_from (P Q : Type) (hQ : isProp Q) (dP : Decidable P) (y : Sum (Mere (Sum P Q)) (Product P Q)) : Sum P Q
  ≔ match y [
  | inl. t ↦ match dP [
    | inl. p ↦ inl. p
    | inr. np ↦ inr. (pbg_or_extract P Q hQ np t) ]
  | inr. pq ↦ inr. (pq .snd) ]

def pbg_split_from_to (P Q : Type) (hP : isProp P) (hQ : isProp Q) (dP : Decidable P) (x : Sum P Q)
  : Id (Sum P Q) (pbg_split_from P Q hQ dP (pbg_split_to P Q dP x)) x
  ≔ match x [
  | inl. p ↦ match dP [
    | inl. p' ↦ refl ((z ↦ inl. z) : P → Sum P Q) (hP p' p)
    | inr. np ↦ absurd (Id (Sum P Q) (inr. (pbg_or_extract P Q hQ np (mere (Sum P Q) (inl. p)))) (inl. p)) (np p) ]
  | inr. q ↦ match dP [
    | inl. p ↦ refl (inr. q : Sum P Q)
    | inr. np ↦ refl ((z ↦ inr. z) : Q → Sum P Q) (hQ (pbg_or_extract P Q hQ np (mere (Sum P Q) (inr. q))) q) ] ]

def pbg_split_to_from (P Q : Type) (hP : isProp P) (hQ : isProp Q) (dP : Decidable P)
  (y : Sum (Mere (Sum P Q)) (Product P Q))
  : Id (Sum (Mere (Sum P Q)) (Product P Q)) (pbg_split_to P Q dP (pbg_split_from P Q hQ dP y)) y
  ≔ match y [
  | inl. t ↦ match dP [
    | inl. p ↦ refl ((z ↦ inl. z) : Mere (Sum P Q) → Sum (Mere (Sum P Q)) (Product P Q))
        (mere_isprop (Sum P Q) (mere (Sum P Q) (inl. p)) t)
    | inr. np ↦ refl ((z ↦ inl. z) : Mere (Sum P Q) → Sum (Mere (Sum P Q)) (Product P Q))
        (mere_isprop (Sum P Q) (mere (Sum P Q) (inr. (pbg_or_extract P Q hQ np t))) t) ]
  | inr. pq ↦ match dP [
    | inl. p ↦ refl ((z ↦ inr. z) : Product P Q → Sum (Mere (Sum P Q)) (Product P Q))
        (product_prop P Q hP hQ (p, pq .snd) pq)
    | inr. np ↦ absurd (Id (Sum (Mere (Sum P Q)) (Product P Q))
        (inl. (mere (Sum P Q) (inr. (pq .snd)))) (inr. pq)) (np (pq .fst)) ] ]

def pbg_split_equiv (P Q : Type) (hP : isProp P) (hQ : isProp Q) (dP : Decidable P)
  : Equiv (Sum P Q) (Sum (Mere (Sum P Q)) (Product P Q))
  ≔ quasi_inverse_equiv (Sum P Q) (Sum (Mere (Sum P Q)) (Product P Q))
      (pbg_split_to P Q dP) (pbg_split_from P Q hQ dP)
      (pbg_split_from_to P Q hP hQ dP) (pbg_split_to_from P Q hP hQ dP)

{` A + B ≃ (A ∪ B) + (A ∩ B) as types, for P decidable. `}
def subset_sum_union_intersection_equiv (S : Type) (P Q : Subtypes S) (dP : (s : S) → Decidable (P s .fst))
  : Equiv (Sum (SubtypeCarrier S P) (SubtypeCarrier S Q))
      (Sum (SubtypeCarrier S (SubsetUnion S P Q)) (SubtypeCarrier S (SubsetIntersection S P Q)))
  ≔ let F : S → Type ≔ s ↦ Sum (P s .fst) (Q s .fst) in
    let G : S → Type ≔ s ↦ Sum (SubsetUnion S P Q s .fst) (SubsetIntersection S P Q s .fst) in
    compose_equiv (Sum (SubtypeCarrier S P) (SubtypeCarrier S Q)) (Σ S F)
      (Sum (SubtypeCarrier S (SubsetUnion S P Q)) (SubtypeCarrier S (SubsetIntersection S P Q)))
      (canonical_inverse_equiv (Σ S F) (Sum (SubtypeCarrier S P) (SubtypeCarrier S Q))
        (sigma_sum_equiv S (s ↦ P s .fst) (s ↦ Q s .fst)))
      (compose_equiv (Σ S F) (Σ S G)
        (Sum (SubtypeCarrier S (SubsetUnion S P Q)) (SubtypeCarrier S (SubsetIntersection S P Q)))
        (family_equiv S F G (s ↦ pbg_split_equiv (P s .fst) (Q s .fst) (P s .snd) (Q s .snd) (dP s)))
        (sigma_sum_equiv S (s ↦ SubsetUnion S P Q s .fst) (s ↦ SubsetIntersection S P Q s .fst)))

def subset_finite (S : Type) (hS : IsFinite S) (P : Subtypes S) (dP : (s : S) → Decidable (P s .fst))
  : IsFinite (SubtypeCarrier S P)
  ≔ finite_decidable_subset S hS (s ↦ P s .fst) (s ↦ P s .snd) dP

{` xca:cardinalityintersectionunion, corrected: for decidable subsets A, B
   of a finite set S, Card(A) + Card(B) = Card(A ∪ B) + Card(A ∩ B), with
   the finiteness of the four subsets derived (subset_finite). `}
def subset_cardinality_union_intersection (S : Type) (hS : IsFinite S) (P Q : Subtypes S)
  (dP : (s : S) → Decidable (P s .fst)) (dQ : (s : S) → Decidable (Q s .fst))
  : Id Nat
      (add (cardinality (SubtypeCarrier S P) (subset_finite S hS P dP))
        (cardinality (SubtypeCarrier S Q) (subset_finite S hS Q dQ)))
      (add (cardinality (SubtypeCarrier S (SubsetUnion S P Q))
             (subset_finite S hS (SubsetUnion S P Q) (subset_union_decidable S P Q dP dQ)))
        (cardinality (SubtypeCarrier S (SubsetIntersection S P Q))
             (subset_finite S hS (SubsetIntersection S P Q) (subset_intersection_decidable S P Q dP dQ))))
  ≔ let A ≔ SubtypeCarrier S P in
    let B ≔ SubtypeCarrier S Q in
    let U ≔ SubtypeCarrier S (SubsetUnion S P Q) in
    let I ≔ SubtypeCarrier S (SubsetIntersection S P Q) in
    let hA ≔ subset_finite S hS P dP in
    let hB ≔ subset_finite S hS Q dQ in
    let hU ≔ subset_finite S hS (SubsetUnion S P Q) (subset_union_decidable S P Q dP dQ) in
    let hI ≔ subset_finite S hS (SubsetIntersection S P Q) (subset_intersection_decidable S P Q dP dQ) in
    let hAB ≔ finite_sum A B hA hB in
    let hUI ≔ finite_sum U I hU hI in
    calc
      add (cardinality A hA) (cardinality B hB)
      = cardinality (Sum A B) hAB
        by inverse Nat (cardinality (Sum A B) hAB) (add (cardinality A hA) (cardinality B hB))
          (cardinality_sum A B hA hB hAB)
      = cardinality (Sum U I) hUI
        by cardinality_equiv (Sum A B) (Sum U I) (subset_sum_union_intersection_equiv S P Q dP) hAB hUI
      = add (cardinality U hU) (cardinality I hI) by cardinality_sum U I hU hI hUI ∎

{` For a finite set S, a subset is finite if and only if it is decidable;
   both are propositions, so this is an equivalence. `}
def subset_finite_decidable (S : Type) (hS : IsFinite S) (P : Subtypes S) (h : IsFinite (SubtypeCarrier S P))
  : (s : S) → Decidable (P s .fst)
  ≔ s ↦
    let E ≔ SubtypeCarrier S P in
    let R : E → Type ≔ x ↦ Id S (x .fst) s in
    match finite_quantifiers E h R (x ↦ finite_sethood S hS (x .fst) s)
            (x ↦ finite_decidable_equality S hS (x .fst) s) .snd [
    | inl. t ↦ inl. (mere_rec (Σ E R) (P s .fst) (P s .snd)
        (w ↦ transport S (y ↦ P y .fst) (w .fst .fst) s (w .snd) (w .fst .snd)) t)
    | inr. no ↦ inr. (p ↦ no (mere (Σ E R) ((s, p), refl s))) ]

def subset_finite_decidable_equiv (S : Type) (hS : IsFinite S) (P : Subtypes S)
  : Equiv (IsFinite (SubtypeCarrier S P)) ((s : S) → Decidable (P s .fst))
  ≔ iff_equiv (IsFinite (SubtypeCarrier S P)) ((s : S) → Decidable (P s .fst))
      (isfinite_prop (SubtypeCarrier S P))
      (pi_prop S (s ↦ Decidable (P s .fst)) (s ↦ decidability_prop (P s .fst) (P s .snd)))
      (subset_finite_decidable S hS P) (subset_finite S hS P)

{` Why the printed hypothesis does not suffice: the subset {* | P} of the
   finite set 1 is finite exactly when the proposition P is decidable, so
   "every subset of a finite set is finite" (needed for the printed
   statement to typecheck) already implies excluded middle. `}
def unit_subset (P : PropTypes) : Subtypes Unit ≔ _ ↦ P

def all_unit_subsets_finite_lem (h : (P : PropTypes) → IsFinite (SubtypeCarrier Unit (unit_subset P)))
  : ExcludedMiddle
  ≔ P hP ↦ subset_finite_decidable Unit finite_unit (unit_subset (P, hP)) (h (P, hP)) star.

{` Litmus checks. In Bool, A = {true}, B = {false}: the intersection is
   empty and the union is everything, so 1 + 1 = 2 + 0; and A ∩ A ≃ A by
   the pullback equivalence, whose map computes. `}
def bool_true_subset : Subtypes Bool ≔ b ↦ (Id Bool b true., bool_set b true.)
def bool_false_subset : Subtypes Bool ≔ b ↦ (Id Bool b false., bool_set b false.)

def pbg_bool_eq_decidable (b c : Bool) : Decidable (Id Bool b c)
  ≔ match b, c [
  | false., false. ↦ inl. (refl (false. : Bool))
  | true., true. ↦ inl. (refl (true. : Bool))
  | false., true. ↦ inr. (bool_encode false. true.)
  | true., false. ↦ inr. (bool_encode true. false.) ]

def pbg_bool_finite : IsFinite Bool
  ≔ finite_from_equiv Bool (suc. (suc. zero.)) (canonical_inverse_equiv (Fin (suc. (suc. zero.))) Bool fin_two_equiv)

def subset_litmus_cardinality
  : Id Nat (add (cardinality (SubtypeCarrier Bool bool_true_subset) (subset_finite Bool pbg_bool_finite bool_true_subset (b ↦ pbg_bool_eq_decidable b true.)))
              (cardinality (SubtypeCarrier Bool bool_false_subset) (subset_finite Bool pbg_bool_finite bool_false_subset (b ↦ pbg_bool_eq_decidable b false.))))
      (add (cardinality (SubtypeCarrier Bool (SubsetUnion Bool bool_true_subset bool_false_subset))
             (subset_finite Bool pbg_bool_finite (SubsetUnion Bool bool_true_subset bool_false_subset)
               (subset_union_decidable Bool bool_true_subset bool_false_subset (b ↦ pbg_bool_eq_decidable b true.)
                 (b ↦ pbg_bool_eq_decidable b false.))))
        (cardinality (SubtypeCarrier Bool (SubsetIntersection Bool bool_true_subset bool_false_subset))
             (subset_finite Bool pbg_bool_finite (SubsetIntersection Bool bool_true_subset bool_false_subset)
               (subset_intersection_decidable Bool bool_true_subset bool_false_subset (b ↦ pbg_bool_eq_decidable b true.)
                 (b ↦ pbg_bool_eq_decidable b false.)))))
  ≔ subset_cardinality_union_intersection Bool pbg_bool_finite bool_true_subset bool_false_subset
      (b ↦ pbg_bool_eq_decidable b true.) (b ↦ pbg_bool_eq_decidable b false.)

def subset_litmus_pullback_map
  : Id Bool (subset_pullback_to_intersection Bool bool_true_subset bool_true_subset
      (((true., refl (true. : Bool)), (true., refl (true. : Bool))), refl (true. : Bool)) .fst) true.
  ≔ refl (true. : Bool)

def pbg_bool_inter : Subtypes Bool ≔ SubsetIntersection Bool bool_true_subset bool_false_subset
def pbg_bool_union : Subtypes Bool ≔ SubsetUnion Bool bool_true_subset bool_false_subset

def pbg_bool_inter_empty (u : SubtypeCarrier Bool pbg_bool_inter) : Empty
  ≔ bool_encode true. false.
      (concat Bool true. (u .fst) false. (inverse Bool (u .fst) true. (u .snd .fst)) (u .snd .snd))

def pbg_bool_inter_empty_equiv : Equiv (SubtypeCarrier Bool pbg_bool_inter) Empty
  ≔ quasi_inverse_equiv (SubtypeCarrier Bool pbg_bool_inter) Empty pbg_bool_inter_empty
      (absurd (SubtypeCarrier Bool pbg_bool_inter))
      (u ↦ absurd (Id (SubtypeCarrier Bool pbg_bool_inter)
        (absurd (SubtypeCarrier Bool pbg_bool_inter) (pbg_bool_inter_empty u)) u) (pbg_bool_inter_empty u))
      (e ↦ match e [])

def pbg_bool_union_point (b : Bool) : SubtypeCarrier Bool pbg_bool_union
  ≔ match b [
  | true. ↦ (true., mere (Sum (Id Bool true. true.) (Id Bool true. false.)) (inl. (refl (true. : Bool))))
  | false. ↦ (false., mere (Sum (Id Bool false. true.) (Id Bool false. false.)) (inr. (refl (false. : Bool)))) ]

def pbg_bool_union_point_fst (b : Bool) : Id Bool (pbg_bool_union_point b .fst) b
  ≔ match b [ true. ↦ refl (true. : Bool) | false. ↦ refl (false. : Bool) ]

def pbg_bool_union_equiv : Equiv (SubtypeCarrier Bool pbg_bool_union) Bool
  ≔ quasi_inverse_equiv (SubtypeCarrier Bool pbg_bool_union) Bool (u ↦ u .fst) pbg_bool_union_point
      (u ↦ subtype_equal Bool (b ↦ pbg_bool_union b .fst) (b ↦ pbg_bool_union b .snd)
        (pbg_bool_union_point (u .fst)) u (pbg_bool_union_point_fst (u .fst)))
      pbg_bool_union_point_fst

def subset_litmus_intersection_card
  : Id Nat (cardinality (SubtypeCarrier Bool pbg_bool_inter)
      (subset_finite Bool pbg_bool_finite pbg_bool_inter
        (subset_intersection_decidable Bool bool_true_subset bool_false_subset (b ↦ pbg_bool_eq_decidable b true.)
          (b ↦ pbg_bool_eq_decidable b false.)))) zero.
  ≔ cardinality_from_path (SubtypeCarrier Bool pbg_bool_inter)
      (subset_finite Bool pbg_bool_finite pbg_bool_inter
        (subset_intersection_decidable Bool bool_true_subset bool_false_subset (b ↦ pbg_bool_eq_decidable b true.)
          (b ↦ pbg_bool_eq_decidable b false.))) zero.
      (ua (SubtypeCarrier Bool pbg_bool_inter) Empty pbg_bool_inter_empty_equiv)

def subset_litmus_union_card
  : Id Nat (cardinality (SubtypeCarrier Bool pbg_bool_union)
      (subset_finite Bool pbg_bool_finite pbg_bool_union
        (subset_union_decidable Bool bool_true_subset bool_false_subset (b ↦ pbg_bool_eq_decidable b true.)
          (b ↦ pbg_bool_eq_decidable b false.)))) (suc. (suc. zero.))
  ≔ cardinality_from_path (SubtypeCarrier Bool pbg_bool_union)
      (subset_finite Bool pbg_bool_finite pbg_bool_union
        (subset_union_decidable Bool bool_true_subset bool_false_subset (b ↦ pbg_bool_eq_decidable b true.)
          (b ↦ pbg_bool_eq_decidable b false.))) (suc. (suc. zero.))
      (ua (SubtypeCarrier Bool pbg_bool_union) (Fin (suc. (suc. zero.)))
        (compose_equiv (SubtypeCarrier Bool pbg_bool_union) Bool (Fin (suc. (suc. zero.)))
          pbg_bool_union_equiv (canonical_inverse_equiv (Fin (suc. (suc. zero.))) Bool fin_two_equiv)))
