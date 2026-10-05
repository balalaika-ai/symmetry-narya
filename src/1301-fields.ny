export "1300-abstract-rings"

{` Chapter 13 (fields.tex 1239-1276): invertible elements, the theorem that
   0 is not invertible in a non-trivial commutative ring, fields (in the
   book's sense: the non-invertible elements form a contractible type),
   discrete fields, local rings and Heyting fields.

   The book states these for a commutative ring R with elements, i.e. for
   abstract rings (def:abstractring). IsInvertible is defined for every
   abstract ring (the definition does not use commutativity); the
   predicates that the book writes with isNonTrivialCRing(R) carry that
   hypothesis explicitly. Truncations ‖-‖ are Mere (module 29), isContr is
   BookIsContr. `}

def IsNonTrivialCRing (R : AbstractRing) : Type ≔ Product (IsCommutativeRing R) (IsNonTrivialRing R)

def InverseWitness (R : AbstractRing) (e : R .carrier) : Type
  ≔ Σ (R .carrier) (a ↦ Product (Id (R .carrier) (R .mul e a) (R .one)) (Id (R .carrier) (R .mul a e) (R .one)))

{` isInvertible(e) ≔ ‖Σ (a : R) (e · a = 1) × (a · e = 1)‖. `}
def IsInvertible (R : AbstractRing) (e : R .carrier) : Type ≔ Mere (InverseWitness R e)

def is_invertible_prop (R : AbstractRing) (e : R .carrier) : isProp (IsInvertible R e)
  ≔ mere_isprop (InverseWitness R e)

def invertible_intro (R : AbstractRing) (e a : R .carrier)
  (p : Id (R .carrier) (R .mul e a) (R .one)) (q : Id (R .carrier) (R .mul a e) (R .one))
  : IsInvertible R e
  ≔ mere (InverseWitness R e) (a, (p, q))

def one_invertible (R : AbstractRing) : IsInvertible R (R .one)
  ≔ invertible_intro R (R .one) (R .one) (ring_mul_one_left R (R .one)) (ring_mul_one_left R (R .one))

{` The theorem after the definition (fields.tex 1244), with the book's
   proof: from a · 0 = 1 and a · 0 = 0 we get 0 = 1. The second version
   drops the (unused) commutativity hypothesis. `}
def zero_not_invertible_any (R : AbstractRing) (h : IsNonTrivialRing R) : Not (IsInvertible R (R .zero))
  ≔ t ↦ mere_rec (InverseWitness R (R .zero)) Empty empty_prop
      (w ↦ h (concat (R .carrier) (R .zero) (R .mul (w .fst) (R .zero)) (R .one)
                (inverse (R .carrier) (R .mul (w .fst) (R .zero)) (R .zero) (ring_mul_zero_right R (w .fst)))
                (w .snd .snd)))
      t

def zero_not_invertible (R : AbstractRing) (h : IsNonTrivialCRing R) : Not (IsInvertible R (R .zero))
  ≔ zero_not_invertible_any R (h .snd)

def NonInvertibles (R : AbstractRing) : Type ≔ Σ (R .carrier) (x ↦ Not (IsInvertible R x))

{` isField(R) ≔ isNonTrivialCRing(R) × isContr(Σ (x : R) ¬ isInvertible(x)). `}
def IsField (R : AbstractRing) : Type ≔ Product (IsNonTrivialCRing R) (BookIsContr (NonInvertibles R))

def Field : Type ≔ Σ AbstractRing IsField

def field_ring (K : Field) : AbstractRing ≔ K .fst

def field_carrier (K : Field) : Type ≔ K .fst .carrier

def non_invertibles_path (R : AbstractRing) (u v : NonInvertibles R) (p : Id (R .carrier) (u .fst) (v .fst))
  : Id (NonInvertibles R) u v
  ≔ subtype_equal (R .carrier) (x ↦ Not (IsInvertible R x)) (x ↦ negation_prop (IsInvertible R x)) u v p

{` "Equivalently, R is a field if and only if every non-invertible element
   is equal to zero" (for a non-trivial commutative ring R). Both
   directions. `}
def NonInvertiblesAreZero (R : AbstractRing) : Type
  ≔ (x : R .carrier) → Not (IsInvertible R x) → Id (R .carrier) x (R .zero)

def field_non_invertible_zero (R : AbstractRing) (h : IsField R) : NonInvertiblesAreZero R
  ≔ x nx ↦
    let c ≔ h .snd in
    let z : NonInvertibles R ≔ (R .zero, zero_not_invertible R (h .fst)) in
    let u : NonInvertibles R ≔ (x, nx) in
    let q : Id (NonInvertibles R) u z
      ≔ concat (NonInvertibles R) u (c .center) z
          (inverse (NonInvertibles R) (c .center) u (c .contract u)) (c .contract z) in
    refl ((w ↦ w .fst) : NonInvertibles R → R .carrier) q

def field_from_non_invertible_zero (R : AbstractRing) (h : IsNonTrivialCRing R) (k : NonInvertiblesAreZero R)
  : IsField R
  ≔ (h,
     (center ≔ (R .zero, zero_not_invertible R h),
      contract ≔ u ↦ non_invertibles_path R (R .zero, zero_not_invertible R h) u
        (inverse (R .carrier) (u .fst) (R .zero) (k (u .fst) (u .snd)))))

def field_iff_non_invertible_zero (R : AbstractRing)
  : Product (IsField R → Product (IsNonTrivialCRing R) (NonInvertiblesAreZero R))
      (Product (IsNonTrivialCRing R) (NonInvertiblesAreZero R) → IsField R)
  ≔ (h ↦ (h .fst, field_non_invertible_zero R h), t ↦ field_from_non_invertible_zero R (t .fst) (t .snd))

{` Discrete fields: isField(R) × Π (a : R) ‖(a = 0) + isInvertible(a)‖. `}
def IsDiscreteField (R : AbstractRing) : Type
  ≔ Product (IsField R) ((a : R .carrier) → Mere (Sum (Id (R .carrier) a (R .zero)) (IsInvertible R a)))

{` Local rings: isNonTrivialCRing(R) × Π a b, isInvertible(a + b) →
   ‖isInvertible(a) + isInvertible(b)‖. `}
def IsLocalRing (R : AbstractRing) : Type
  ≔ Product (IsNonTrivialCRing R)
      ((a b : R .carrier) → IsInvertible R (R .add a b) → Mere (Sum (IsInvertible R a) (IsInvertible R b)))

{` Heyting fields: isField(R) × isLocalRing(R). `}
def IsHeytingField (R : AbstractRing) : Type ≔ Product (IsField R) (IsLocalRing R)

{` In a field, every non-zero element is "apart" from being non-invertible:
   an element that is not zero is not non-invertible (¬¬-invertible). This
   is the strongest constructive reading available without discreteness. `}
def field_nonzero_not_non_invertible (R : AbstractRing) (h : IsField R) (x : R .carrier)
  (nz : Not (Id (R .carrier) x (R .zero))) : Not (Not (IsInvertible R x))
  ≔ nx ↦ nz (field_non_invertible_zero R h x nx)
