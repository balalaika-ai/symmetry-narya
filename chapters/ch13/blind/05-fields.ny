import "01-abstract-rings"

{` Blind statements, chapter 13 (fields.tex), the field definitions after
   sec:mixring. A "commutative ring" is a BlindAbsRing; the predicates are
   stated on all abstract rings since their formulas do not use
   commutativity, and commutativity enters through isNonTrivialCRing. `}

{` isNonTrivialCRing(R): R is non-trivial (0 ≠ 1) and commutative. `}
def BlindIsNonTrivialCRing (R : BlindAbsRing) : Type
  ≔ Product (BlindAbsRingNonTrivial R) (BlindAbsRingCommutative R)

{` isInvertible(e) ≔ ‖Σ a : R, (e·a = 1) × (a·e = 1)‖. `}
def BlindIsInvertible (R : BlindAbsRing) (e : R .add .carrier) : Type
  ≔ Mere (Σ (R .add .carrier) (a ↦
      Product (Id (R .add .carrier) (R .mul e a) (R .one)) (Id (R .add .carrier) (R .mul a e) (R .one))))

{` Theorem: isNonTrivialCRing(R) → ¬ isInvertible(0), for every ring R. `}
def blind_zero_not_invertible : Type
  ≔ (R : BlindAbsRing) → BlindIsNonTrivialCRing R → Not (BlindIsInvertible R (R .add .unit))

{` isField(R) ≔ isNonTrivialCRing(R) × isContr(Σ x : R, ¬ isInvertible(x)). `}
def BlindIsField (R : BlindAbsRing) : Type
  ≔ Product (BlindIsNonTrivialCRing R)
      (BookIsContr (Σ (R .add .carrier) (x ↦ Not (BlindIsInvertible R x))))

{` "Equivalently, [a nontrivial commutative ring] R is a field if and only
   if every non-invertible element is equal to zero." `}
def blind_field_iff_noninvertible_zero : Type
  ≔ (R : BlindAbsRing) → BlindIsNonTrivialCRing R →
      Product
        (BlindIsField R → (x : R .add .carrier) → Not (BlindIsInvertible R x) → Id (R .add .carrier) x (R .add .unit))
        (((x : R .add .carrier) → Not (BlindIsInvertible R x) → Id (R .add .carrier) x (R .add .unit)) → BlindIsField R)

{` A field: an abstract ring with isField. `}
def BlindField : Type ≔ Σ BlindAbsRing BlindIsField

{` isDiscreteField(R) ≔ isField(R) × Π a : R, ‖(a = 0) ⨿ isInvertible(a)‖. `}
def BlindIsDiscreteField (R : BlindAbsRing) : Type
  ≔ Product (BlindIsField R)
      ((a : R .add .carrier) → Mere (Sum (Id (R .add .carrier) a (R .add .unit)) (BlindIsInvertible R a)))

{` isLocalRing(R) ≔ isNonTrivialCRing(R) ×
   Π a b : R, isInvertible(a + b) → ‖isInvertible(a) ⨿ isInvertible(b)‖. `}
def BlindIsLocalRing (R : BlindAbsRing) : Type
  ≔ Product (BlindIsNonTrivialCRing R)
      ((a b : R .add .carrier) → BlindIsInvertible R (R .add .mul a b) →
         Mere (Sum (BlindIsInvertible R a) (BlindIsInvertible R b)))

{` isHeytingField(R) ≔ isField(R) × isLocalRing(R). `}
def BlindIsHeytingField (R : BlindAbsRing) : Type
  ≔ Product (BlindIsField R) (BlindIsLocalRing R)
