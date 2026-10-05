export "31-natural-order"

def Below (n : Nat) : Type ≔ Σ Nat (k ↦ Lt k n)
def below_succ (n : Nat) (p : Below n) : Below (suc. n) ≔ (suc. (p .fst), p .snd)

def below_predecessor (n : Nat) (k : Nat) (h : Lt k (suc. n)) : Sum (Below n) Unit
  ≔ match k [ zero. ↦ inr. star. | suc. k ↦ inl. (k, h) ]

def below_successor (n : Nat) : Sum (Below n) Unit → Below (suc. n)
  ≔ [ inl. p ↦ below_succ n p | inr. u ↦ (zero., star.) ]

def below_roundtrip (n : Nat) (k : Nat) (h : Lt k (suc. n))
  : Id (Below (suc. n)) (below_successor n (below_predecessor n k h)) (k, h)
  ≔ match k [
  | zero. ↦ (refl zero., unit_prop star. h)
  | suc. k ↦ refl (suc. k, h) ]

def below_successor_equiv (n : Nat) : Equiv (Sum (Below n) Unit) (Below (suc. n))
  ≔ quasi_inverse_equiv (Sum (Below n) Unit) (Below (suc. n)) (below_successor n)
      (p ↦ below_predecessor n (p .fst) (p .snd))
      [ inl. p ↦ refl (inl. p) | inr. u ↦ inr. (unit_prop star. u) ]
      (p ↦ below_roundtrip n (p .fst) (p .snd))

def fin_below_equiv (n : Nat) : Equiv (Fin n) (Below n)
  ≔ match n [
  | zero. ↦ quasi_inverse_equiv Empty (Below zero.)
      (x ↦ match x []) (p ↦ p .snd) (x ↦ match x []) (p ↦ match p .snd [])
  | suc. n ↦ compose_equiv (Fin (suc. n)) (Sum (Below n) Unit) (Below (suc. n))
      (sum_equiv (Fin n) Unit (Below n) Unit (fin_below_equiv n) (identity_equiv Unit))
      (below_successor_equiv n) ]

{` The strict inequality here uses exactly the book's positive-difference witnesses. `}
def fin_book_below_equiv (n : Nat) : Equiv (Fin n) (Σ Nat (k ↦ BookLt k n))
  ≔ compose_equiv (Fin n) (Below n) (Σ Nat (k ↦ BookLt k n)) (fin_below_equiv n)
      (family_equiv Nat (k ↦ Lt k n) (k ↦ BookLt k n) (k ↦ lt_book_equiv k n))

def DecidableEquality (A : Type) : Type ≔ (x y : A) → Decidable (Id A x y)

def sum_decidable_equality (A B : Type) (dA : DecidableEquality A) (dB : DecidableEquality B)
  : DecidableEquality (Sum A B)
  ≔ x y ↦ match x, y [
  | inl. a, inl. b ↦ match dA a b [
      inl. p ↦ inl. (inl. p) | inr. h ↦ inr. (p ↦ h (sum_encode A B (inl. a) (inl. b) p)) ]
  | inl. a, inr. b ↦ inr. (p ↦ sum_encode A B (inl. a) (inr. b) p)
  | inr. a, inl. b ↦ inr. (p ↦ sum_encode A B (inr. a) (inl. b) p)
  | inr. a, inr. b ↦ match dB a b [
      inl. p ↦ inl. (inr. p) | inr. h ↦ inr. (p ↦ h (sum_encode A B (inr. a) (inr. b) p)) ] ]

def fin_decidable_equality (n : Nat) : DecidableEquality (Fin n)
  ≔ match n [
  | zero. ↦ x y ↦ match x []
  | suc. n ↦ sum_decidable_equality (Fin n) Unit (fin_decidable_equality n) (x y ↦ inl. (unit_prop x y)) ]

def decidable_equality_prop (A : Type) (h : isSet A) : isProp (DecidableEquality A)
  ≔ pi_prop A (x ↦ (y : A) → Decidable (Id A x y))
      (x ↦ pi_prop A (y ↦ Decidable (Id A x y)) (y ↦ decidability_prop (Id A x y) (h x y)))

{` def:is-finite, with the constructed native truncation. `}
def IsFinite (A : Type) : Type ≔ Mere (Σ Nat (n ↦ Id Type A (Fin n)))
def CardinalityWitness (A : Type) : Type ≔ Σ Nat (n ↦ Mere (Id Type A (Fin n)))

def cardinality_witness_unique (A : Type) (u v : CardinalityWitness A) : Id Nat (u .fst) (v .fst)
  ≔ mere_rec (Id Type A (Fin (u .fst))) (Id Nat (u .fst) (v .fst)) (nat_set (u .fst) (v .fst))
      (p ↦ mere_rec (Id Type A (Fin (v .fst))) (Id Nat (u .fst) (v .fst)) (nat_set (u .fst) (v .fst))
        (q ↦ fin_path_cardinality (u .fst) (v .fst)
          (concat Type (Fin (u .fst)) A (Fin (v .fst)) (inverse Type A (Fin (u .fst)) p) q)) (v .snd)) (u .snd)

def cardinality_witness_prop (A : Type) : isProp (CardinalityWitness A)
  ≔ u v ↦ subtype_equal Nat (n ↦ Mere (Id Type A (Fin n))) (n ↦ mere_isprop (Id Type A (Fin n))) u v
      (cardinality_witness_unique A u v)

def finite_cardinality_witness (A : Type) (h : IsFinite A) : CardinalityWitness A
  ≔ mere_rec (Σ Nat (n ↦ Id Type A (Fin n))) (CardinalityWitness A) (cardinality_witness_prop A)
      (p ↦ (p .fst, mere (Id Type A (Fin (p .fst))) (p .snd))) h

def cardinality_witness_finite (A : Type) (p : CardinalityWitness A) : IsFinite A
  ≔ mere_rec (Id Type A (Fin (p .fst))) (IsFinite A) (mere_isprop (Σ Nat (n ↦ Id Type A (Fin n))))
      (q ↦ mere (Σ Nat (n ↦ Id Type A (Fin n))) (p .fst, q)) (p .snd)

{` lem:maxonefinitetype, both clauses, including an equivalence of propositions. `}
def finite_witness_equiv (A : Type) : Equiv (IsFinite A) (CardinalityWitness A)
  ≔ iff_equiv (IsFinite A) (CardinalityWitness A) (mere_isprop (Σ Nat (n ↦ Id Type A (Fin n))))
      (cardinality_witness_prop A) (finite_cardinality_witness A) (cardinality_witness_finite A)

def cardinality (A : Type) (h : IsFinite A) : Nat ≔ finite_cardinality_witness A h .fst
def cardinality_spec (A : Type) (h : IsFinite A) : Mere (Id Type A (Fin (cardinality A h)))
  ≔ finite_cardinality_witness A h .snd

def cardinality_from_path (A : Type) (h : IsFinite A) (n : Nat) (p : Id Type A (Fin n))
  : Id Nat (cardinality A h) n
  ≔ cardinality_witness_unique A (finite_cardinality_witness A h) (n, mere (Id Type A (Fin n)) p)

def finite_sethood (A : Type) (h : IsFinite A) : isSet A
  ≔ mere_rec (Σ Nat (n ↦ Id Type A (Fin n))) (isSet A) (isset_isprop A)
      (p ↦ transport Type isSet (Fin (p .fst)) A (inverse Type A (Fin (p .fst)) (p .snd)) (fin_set (p .fst))) h

{` xca:finsets-decidable. No representative or enumeration is chosen from truncation. `}
def finite_decidable_equality (A : Type) (h : IsFinite A) : DecidableEquality A
  ≔ mere_rec (Σ Nat (n ↦ Id Type A (Fin n))) (DecidableEquality A)
      (decidable_equality_prop A (finite_sethood A h))
      (p ↦ transport Type DecidableEquality (Fin (p .fst)) A
        (inverse Type A (Fin (p .fst)) (p .snd)) (fin_decidable_equality (p .fst))) h

def FiniteSets : Type ≔ Σ SetTypes (S ↦ IsFinite (S .fst))
def FiniteSetsAt (n : Nat) : Type ≔ Σ SetTypes (S ↦ Mere (Id Type (Fin n) (S .fst)))
def Card (S : FiniteSets) : Nat ≔ cardinality (S .fst .fst) (S .snd)

def fin_is_finite (n : Nat) : IsFinite (Fin n)
  ≔ mere (Σ Nat (m ↦ Id Type (Fin n) (Fin m))) (n, refl (Fin n))

def standard_finite_set (n : Nat) : FiniteSets ≔ ((Fin n, fin_set n), fin_is_finite n)

def standard_cardinality (n : Nat) : Id Nat (Card (standard_finite_set n)) n
  ≔ cardinality_from_path (Fin n) (fin_is_finite n) n (refl (Fin n))

def finite_sets_groupoid : isGroupoid FiniteSets
  ≔ hlevel_to_groupoid FiniteSets
      (subtype_hlevel (suc. (suc. zero.)) SetTypes (S ↦ IsFinite (S .fst))
        (groupoid_to_hlevel SetTypes sets_groupoid)
        (S ↦ mere_isprop (Σ Nat (n ↦ Id Type (S .fst) (Fin n)))))

def mere_inverse_equiv (A B : Type) : Equiv (Mere (Id Type A B)) (Mere (Id Type B A))
  ≔ iff_equiv (Mere (Id Type A B)) (Mere (Id Type B A))
      (mere_isprop (Id Type A B)) (mere_isprop (Id Type B A))
      (trunc_map native_truncation (Id Type A B) (Id Type B A) (inverse Type A B))
      (trunc_map native_truncation (Id Type B A) (Id Type A B) (inverse Type B A))

def finite_sets_components : Equiv FiniteSets (Σ Nat FiniteSetsAt)
  ≔ let W ≔ (Σ SetTypes (S ↦ CardinalityWitness (S .fst))) in
    let V ≔ (Σ Nat (n ↦ Σ SetTypes (S ↦ Mere (Id Type (S .fst) (Fin n))))) in
    compose_equiv FiniteSets W (Σ Nat FiniteSetsAt)
      (family_equiv SetTypes (S ↦ IsFinite (S .fst)) (S ↦ CardinalityWitness (S .fst)) (S ↦ finite_witness_equiv (S .fst)))
      (compose_equiv W V (Σ Nat FiniteSetsAt)
        (sigma_comm SetTypes Nat (S n ↦ Mere (Id Type (S .fst) (Fin n))))
        (family_equiv Nat (n ↦ Σ SetTypes (S ↦ Mere (Id Type (S .fst) (Fin n)))) FiniteSetsAt
          (n ↦ family_equiv SetTypes (S ↦ Mere (Id Type (S .fst) (Fin n)))
            (S ↦ Mere (Id Type (Fin n) (S .fst))) (S ↦ mere_inverse_equiv (S .fst) (Fin n)))))
