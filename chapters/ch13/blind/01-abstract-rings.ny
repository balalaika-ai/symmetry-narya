export "../../../src/701-abstract-homomorphisms"

{` Blind statements, chapter 13 (fields.tex), sec:abstrings.
   The group data of an abstract ring are the AbstractGroup fields
   (unit = 0, mul = +, inv = -); the monoid data are one (1) and mul (·). `}

{` def:abstractring, laws (a) and (b): DistrLaws(R, ·, +), the left
   distributive law a·(b+c) = a·b + a·c and the right distributive law
   (a+b)·c = a·c + b·c. `}
def BlindDistrLaws (R : Type) (mul add : R → R → R) : Type
  ≔ Product
      ((a b c : R) → Id R (mul a (add b c)) (add (mul a b) (mul a c)))
      ((a b c : R) → Id R (mul (add a b) c) (add (mul a c) (mul b c)))

{` def:abstractring. An abstract ring: an abstract group (R,0,+,-) and a
   monoid (R,1,·) on the same underlying set, with the distributive laws.
   MonoidLaws (module 700) includes isSet R (not:GroupLaws). `}
def BlindAbsRing : Type ≔ sig (
  add : AbstractGroup,
  one : add .carrier,
  mul : add .carrier → add .carrier → add .carrier,
  monoid : MonoidLaws (add .carrier) one mul,
  distr : BlindDistrLaws (add .carrier) mul (add .mul))

{` The (multiplicative) monoid (R,1,·) of an abstract ring. `}
def blind_absring_monoid (R : BlindAbsRing) : Monoid
  ≔ (R .add .carrier, R .one, R .mul, R .monoid)

{` def:abstractring: non-trivial means 0 ≠ 1. `}
def BlindAbsRingNonTrivial (R : BlindAbsRing) : Type
  ≔ Not (Id (R .add .carrier) (R .add .unit) (R .one))

{` def:abstractring: commutative means a·b = b·a for all a, b : R. `}
def BlindAbsRingCommutative (R : BlindAbsRing) : Type
  ≔ (a b : R .add .carrier) → Id (R .add .carrier) (R .mul a b) (R .mul b a)

{` def:typering. The type of abstract rings as the literal iterated Σ
   Σ (R,0,+,-) : Group^abs, Σ e : R, Σ μ : R → R → R,
   MonoidLaws(R,e,μ) × DistrLaws(R,μ,+). `}
def BlindTypeRing : Type
  ≔ Σ AbstractGroup (G ↦
      Σ (G .carrier) (e ↦
        Σ (G .carrier → G .carrier → G .carrier) (μ ↦
          Product (MonoidLaws (G .carrier) e μ) (BlindDistrLaws (G .carrier) μ (G .mul)))))

{` def:typering. The type of commutative rings: as BlindTypeRing with the
   additional property Π a b : R, μ(a,b) = μ(b,a). `}
def BlindTypeCommRing : Type
  ≔ Σ AbstractGroup (G ↦
      Σ (G .carrier) (e ↦
        Σ (G .carrier → G .carrier → G .carrier) (μ ↦
          Product (MonoidLaws (G .carrier) e μ)
            (Product (BlindDistrLaws (G .carrier) μ (G .mul))
              ((a b : G .carrier) → Id (G .carrier) (μ a b) (μ b a))))))

{` xca:ring-group-abelian. For every abstract ring, its additive group is
   abelian. `}
def blind_ring_group_abelian : Type
  ≔ (R : BlindAbsRing) → IsAbstractAbelian (R .add)

{` def:ringhom. f preserves the monoid structure (R,1_R,·_R) → (S,1_S,·_S):
   f(1_R) = 1_S and f(s·s') = f(s)·f(s') (as in MonoidHom, rem:monoid-hom). `}
def BlindIsRingMonoidHom (R S : BlindAbsRing) (f : R .add .carrier → S .add .carrier) : Type
  ≔ Product (Id (S .add .carrier) (f (R .one)) (S .one))
      ((s s' : R .add .carrier) → Id (S .add .carrier) (f (R .mul s s')) (S .mul (f s) (f s')))

{` def:ringhom. An abstract ring homomorphism: an abstract homomorphism of
   the additive groups that is a monoid homomorphism of the multiplicative
   monoids. `}
def BlindAbsRingHom (R S : BlindAbsRing) : Type
  ≔ Σ (AbstractHom (R .add) (S .add)) (f ↦ BlindIsRingMonoidHom R S (f .fst))
