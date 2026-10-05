export "29-propositional-truncation"

{` def:finiteset, with the exact right-hand unit summand. `}
def Fin (n : Nat) : Type ≔ match n [ zero. ↦ Empty | suc. n ↦ Sum (Fin n) Unit ]

def fin_set (n : Nat) : isSet (Fin n)
  ≔ match n [ zero. ↦ empty_set | suc. n ↦ sum_set (Fin n) Unit (fin_set n) unit_set ]

def fin_one_equiv : Equiv (Fin (suc. zero.)) Unit
  ≔ quasi_inverse_equiv (Fin (suc. zero.)) Unit
      [ inl. x ↦ absurd Unit x | inr. u ↦ u ] (u ↦ inr. u)
      [ inl. x ↦ match x [] | inr. u ↦ refl (inr. u : Fin (suc. zero.)) ] (u ↦ refl u)

def fin_two_to_bool : Fin (suc. (suc. zero.)) → Bool
  ≔ [ inl. x ↦ false. | inr. u ↦ true. ]

def bool_to_fin_two : Bool → Fin (suc. (suc. zero.))
  ≔ [ false. ↦ inl. (inr. star.) | true. ↦ inr. star. ]

def fin_two_roundtrip (x : Fin (suc. (suc. zero.)))
  : Id (Fin (suc. (suc. zero.))) (bool_to_fin_two (fin_two_to_bool x)) x
  ≔ match x [
  | inl. (inl. e) ↦ match e []
  | inl. (inr. u) ↦ inl. (inr. (unit_prop star. u))
  | inr. u ↦ inr. (unit_prop star. u) ]

def fin_two_equiv : Equiv (Fin (suc. (suc. zero.))) Bool
  ≔ quasi_inverse_equiv (Fin (suc. (suc. zero.))) Bool fin_two_to_bool bool_to_fin_two
      fin_two_roundtrip [ false. ↦ false. | true. ↦ true. ]

{` Removing a point from a type; the second component is a proposition. `}
def Without (A : Type) (a : A) : Type ≔ Σ A (x ↦ Id A x a → Empty)

def without_ext (A : Type) (a : A) (u v : Without A a) (p : Id A (u .fst) (v .fst))
  : Id (Without A a) u v
  ≔ equiv_inverse_map (Id (Without A a) u v) (Id A (u .fst) (v .fst))
      (subtype_path_equiv A (x ↦ Id A x a → Empty) (x ↦ negation_prop (Id A x a)) u v) p

def without_equiv (A B : Type) (e : Equiv A B) (a : A)
  : Equiv (Without A a) (Without B (e .map a))
  ≔ sigma_equivalences A B (x ↦ Id A x a → Empty) (y ↦ Id B y (e .map a) → Empty) e
      (x ↦ iff_equiv (Id A x a → Empty) (Id B (e .map x) (e .map a) → Empty)
        (negation_prop (Id A x a)) (negation_prop (Id B (e .map x) (e .map a)))
        (nx p ↦ nx (equivalence_injective A B e x a p))
        (ny p ↦ ny (map_path A B (e .map) x a p)))

def without_last_to (A : Type) (x : Sum A Unit) (h : Id (Sum A Unit) x (inr. star.) → Empty) : A
  ≔ match x [ inl. a ↦ a | inr. u ↦ absurd A (h (inr. (unit_prop u star.))) ]

def without_last_from (A : Type) (a : A) : Without (Sum A Unit) (inr. star.)
  ≔ (inl. a, p ↦ sum_encode A Unit (inl. a) (inr. star.) p)

def without_last_eta (A : Type) (x : Sum A Unit) (h : Id (Sum A Unit) x (inr. star.) → Empty)
  : Id (Without (Sum A Unit) (inr. star.)) (without_last_from A (without_last_to A x h)) (x, h)
  ≔ match x [
  | inl. a ↦ without_ext (Sum A Unit) (inr. star.) (without_last_from A a) (inl. a, h) (refl (inl. a))
  | inr. u ↦ match h (inr. (unit_prop u star.)) [] ]

def without_last_equiv (A : Type) : Equiv (Without (Sum A Unit) (inr. star.)) A
  ≔ quasi_inverse_equiv (Without (Sum A Unit) (inr. star.)) A
      (t ↦ without_last_to A (t .fst) (t .snd)) (without_last_from A)
      (t ↦ without_last_eta A (t .fst) (t .snd)) (a ↦ refl a)

def without_inl_to (A : Type) (a : A) (x : Sum A Unit)
  (h : Id (Sum A Unit) x (inl. a) → Empty) : Sum (Without A a) Unit
  ≔ match x [ inl. b ↦ inl. (b, p ↦ h (inl. p)) | inr. u ↦ inr. u ]

def without_inl_from (A : Type) (a : A) : Sum (Without A a) Unit → Without (Sum A Unit) (inl. a)
  ≔ [ inl. t ↦ (inl. (t .fst), p ↦ t .snd (sum_encode A Unit (inl. (t .fst)) (inl. a) p))
    | inr. u ↦ (inr. u, p ↦ sum_encode A Unit (inr. u) (inl. a) p) ]

def without_inl_eta (A : Type) (a : A) (x : Sum A Unit)
  (h : Id (Sum A Unit) x (inl. a) → Empty)
  : Id (Without (Sum A Unit) (inl. a)) (without_inl_from A a (without_inl_to A a x h)) (x, h)
  ≔ match x [
  | inl. b ↦ without_ext (Sum A Unit) (inl. a)
      (without_inl_from A a (without_inl_to A a (inl. b) h)) (inl. b, h) (refl (inl. b))
  | inr. u ↦ without_ext (Sum A Unit) (inl. a)
      (without_inl_from A a (inr. u)) (inr. u, h) (refl (inr. u)) ]

def without_inl_beta (A : Type) (a : A) (t : Sum (Without A a) Unit)
  : Id (Sum (Without A a) Unit)
      (without_inl_to A a (without_inl_from A a t .fst) (without_inl_from A a t .snd)) t
  ≔ match t [
  | inl. u ↦ inl. (without_ext A a
      (u .fst, p ↦ u .snd (sum_encode A Unit (inl. (u .fst)) (inl. a) (inl. p))) u (refl (u .fst)))
  | inr. u ↦ refl (inr. u) ]

def without_inl_equiv (A : Type) (a : A)
  : Equiv (Without (Sum A Unit) (inl. a)) (Sum (Without A a) Unit)
  ≔ quasi_inverse_equiv (Without (Sum A Unit) (inl. a)) (Sum (Without A a) Unit)
      (t ↦ without_inl_to A a (t .fst) (t .snd)) (without_inl_from A a)
      (t ↦ without_inl_eta A a (t .fst) (t .snd)) (without_inl_beta A a)

{` Removing any point from Fin(n+1) leaves n elements. Recursion decreases n. `}
def without_fin_equiv (n : Nat) (a : Fin (suc. n)) : Equiv (Without (Fin (suc. n)) a) (Fin n)
  ≔ match a [
  | inr. u ↦ match u [ star. ↦ without_last_equiv (Fin n) ]
  | inl. x ↦ match n [
      | zero. ↦ match x []
      | suc. n ↦ compose_equiv
          (Without (Sum (Fin (suc. n)) Unit) (inl. x)) (Sum (Without (Fin (suc. n)) x) Unit) (Fin (suc. n))
          (without_inl_equiv (Fin (suc. n)) x)
          (sum_equiv (Without (Fin (suc. n)) x) Unit (Fin n) Unit
            (without_fin_equiv n x) (identity_equiv Unit)) ] ]

def fin_cancel_successor (n m : Nat) (e : Equiv (Fin (suc. n)) (Fin (suc. m)))
  : Equiv (Fin n) (Fin m)
  ≔ let a : Fin (suc. n) ≔ inr. star. in
    compose_equiv (Fin n) (Without (Fin (suc. m)) (e .map a)) (Fin m)
      (compose_equiv (Fin n) (Without (Fin (suc. n)) a) (Without (Fin (suc. m)) (e .map a))
        (canonical_inverse_equiv (Without (Fin (suc. n)) a) (Fin n) (without_last_equiv (Fin n)))
        (without_equiv (Fin (suc. n)) (Fin (suc. m)) e a))
      (without_fin_equiv m (e .map a))

def fin_equiv_cardinality (n m : Nat) (e : Equiv (Fin n) (Fin m)) : Id Nat n m
  ≔ match n, m [
  | zero., zero. ↦ zero.
  | zero., suc. m ↦ match equiv_inverse_map Empty (Fin (suc. m)) e (inr. star.) []
  | suc. n, zero. ↦ match e .map (inr. star.) []
  | suc. n, suc. m ↦ suc. (fin_equiv_cardinality n m (fin_cancel_successor n m e)) ]

def fin_path_cardinality (n m : Nat) (p : Id Type (Fin n) (Fin m)) : Id Nat n m
  ≔ fin_equiv_cardinality n m (id_to_equiv (Fin n) (Fin m) p)
