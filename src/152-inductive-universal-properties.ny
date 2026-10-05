export "151-equivalence-exercises"

{` xca:True-univ-prop: evaluation at the element of the unit type is an
   equivalence in the book's sense. The native equivalence is
   unit_evaluation_equiv, whose map is exactly f |-> f star. `}
def true_universal_property (X : Type) : BookIsEquiv (Unit → X) X (f ↦ f star.)
  ≔ book_equivalence (Unit → X) X (unit_evaluation_equiv X) .equiv

{` xca:bin-sum-univ-prop, with e given by precomposition with inl and inr. `}
def sum_restrict (X Y Z : Type) (h : Sum X Y → Z) : Product (X → Z) (Y → Z)
  ≔ (x ↦ h (inl. x), y ↦ h (inr. y))

def sum_restrict_elim (X Y Z : Type) (h : Sum X Y → Z)
  : Id (Sum X Y → Z) (sum_elim X Y Z (sum_restrict X Y Z h .fst) (sum_restrict X Y Z h .snd)) h
  ≔ funext (Sum X Y) (_ ↦ Z)
      (sum_elim X Y Z (sum_restrict X Y Z h .fst) (sum_restrict X Y Z h .snd)) h
      [ inl. x ↦ refl (h (inl. x)) | inr. y ↦ refl (h (inr. y)) ]

def sum_universal_property (X Y Z : Type)
  : Equiv (Sum X Y → Z) (Product (X → Z) (Y → Z))
  ≔ quasi_inverse_equiv (Sum X Y → Z) (Product (X → Z) (Y → Z))
      (sum_restrict X Y Z) (fg ↦ sum_elim X Y Z (fg .fst) (fg .snd))
      (sum_restrict_elim X Y Z) (fg ↦ refl fg)

def book_sum_universal_property (X Y Z : Type)
  : BookIsEquiv (Sum X Y → Z) (Product (X → Z) (Y → Z)) (sum_restrict X Y Z)
  ≔ book_equivalence (Sum X Y → Z) (Product (X → Z) (Y → Z)) (sum_universal_property X Y Z) .equiv

{` exa:nnn: the wrapped copy of Nat with constructor minus. The destructor
   computes judgmentally on constructors; the other composite is proved by
   induction, and both maps are equivalences. `}
def NegNat : Type ≔ data [ minus. (_ : Nat) ]

def negnat_value : NegNat → Nat ≔ [ minus. n ↦ n ]

def negnat_value_minus (n : Nat) : Id Nat (negnat_value (minus. n)) n ≔ refl n

def negnat_minus_value (m : NegNat) : Id NegNat (minus. (negnat_value m)) m
  ≔ match m [ minus. n ↦ refl (minus. n : NegNat) ]

def negnat_constructor_equiv : Equiv Nat NegNat
  ≔ quasi_inverse_equiv Nat NegNat (n ↦ minus. n) negnat_value negnat_value_minus negnat_minus_value

def negnat_destructor_equiv : Equiv NegNat Nat
  ≔ quasi_inverse_equiv NegNat Nat negnat_value (n ↦ minus. n) negnat_minus_value negnat_value_minus
