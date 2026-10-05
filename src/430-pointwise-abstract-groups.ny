export "403-abstract-groups"
export "406-symmetric-group-three"

{` Chapter 4, section "Abstract groups" (group.tex 800-930).

   The observations before def:abstractgroup, for an arbitrary type A and
   a : A. The book's product h · g ≔ trans(g)(h) follows g first, so it is
   concat g h; the operations are those of usym_mul (module 400) for an
   arbitrary loop space. `}
def loop_space_mul (A : Type) (a : A) (h g : Id A a a) : Id A a a ≔ concat A a a a g h

{` The book's e⁻¹ ≡ e and e · g ≡ g are judgmental because symm and trans
   are defined by path induction in the book; in Narya's HOTT they are the
   identifications inverse_refl and concat_p1 (no regularity). `}
def loop_space_inverse_unit (A : Type) (a : A) : Id (Id A a a) (inverse A a a (refl a)) (refl a)
  ≔ inverse_refl A a

def loop_space_unit_mul (A : Type) (a : A) (g : Id A a a)
  : Id (Id A a a) (loop_space_mul A a (refl a) g) g
  ≔ concat_p1 A a a g

{` The four laws (right unit, left unit, associativity, inverses) hold in
   a = a (xca:path-groupoid-laws); when a = a is a set they are
   propositions (abstract_group_laws_prop) and a = a is an abstract group.
   This motivates def:abstractgroup. `}
def loop_space_group_laws (A : Type) (a : A) (h : isSet (Id A a a))
  : AbstractGroupLaws (Id A a a) (refl a) (loop_space_mul A a) (inverse A a a)
  ≔ (h,
     g ↦ concat_1p A a a g,
     g ↦ concat_p1 A a a g,
     g1 g2 g3 ↦ concat_assoc A a a a a g3 g2 g1,
     g ↦ concat_inverse_left A a a g)

def loop_space_abstract_group (A : Type) (a : A) (h : isSet (Id A a a)) : AbstractGroup
  ≔ (Id A a a, refl a, loop_space_mul A a, inverse A a a, loop_space_group_laws A a h)

{` Litmus: lem:idtypesgiveabstractgroups is the instance a ≔ sh_G. `}
def abstr_is_loop_space_group (G : Group)
  : Id AbstractGroup (abstr G) (loop_space_abstract_group (BG G .carrier) (shape G) (usym_set G))
  ≔ refl (abstr G)

{` The remark after def:abstractgroup: the proofs of the laws are part of
   the data, but any two choices give the same abstract group. `}
def abstract_group_laws_irrelevant (S : Type) (e : S) (mul : S → S → S) (inv : S → S)
  (l l' : AbstractGroupLaws S e mul inv)
  : Id AbstractGroup (S, e, mul, inv, l) (S, e, mul, inv, l')
  ≔ (refl S, refl e, refl mul, refl inv, abstract_group_laws_prop S e mul inv l l')

{` xca:abstract-group-of-maps. For an abstract group G with underlying set
   S and a type X, the functions X → S with the pointwise operations form an
   abstract group. The set hypothesis on X is not needed (X → S is a set
   because S is); abstract_group_of_maps is the printed version for a set X. `}
def pointwise_mul (G : AbstractGroup) (X : Type) (f g : X → G .carrier) : X → G .carrier
  ≔ x ↦ G .mul (f x) (g x)

def pointwise_inv (G : AbstractGroup) (X : Type) (f : X → G .carrier) : X → G .carrier
  ≔ x ↦ G .inv (f x)

def pointwise_group_laws (G : AbstractGroup) (X : Type)
  : AbstractGroupLaws (X → G .carrier) (_ ↦ G .unit) (pointwise_mul G X) (pointwise_inv G X)
  ≔ let S ≔ G .carrier in let L ≔ G .laws in
    (pi_set X (_ ↦ S) (_ ↦ abstract_group_set G),
     f ↦ funext X (_ ↦ S) (pointwise_mul G X f (_ ↦ G .unit)) f (x ↦ L .unit_right (f x)),
     f ↦ funext X (_ ↦ S) (pointwise_mul G X (_ ↦ G .unit) f) f (x ↦ L .unit_left (f x)),
     f1 f2 f3 ↦ funext X (_ ↦ S) (pointwise_mul G X f1 (pointwise_mul G X f2 f3))
       (pointwise_mul G X (pointwise_mul G X f1 f2) f3) (x ↦ L .assoc (f1 x) (f2 x) (f3 x)),
     f ↦ funext X (_ ↦ S) (pointwise_mul G X f (pointwise_inv G X f)) (_ ↦ G .unit)
       (x ↦ L .inv_right (f x)))

def pointwise_abstract_group (G : AbstractGroup) (X : Type) : AbstractGroup
  ≔ (X → G .carrier, _ ↦ G .unit, pointwise_mul G X, pointwise_inv G X, pointwise_group_laws G X)

def abstract_group_of_maps (G : AbstractGroup) (X : SetTypes) : AbstractGroup
  ≔ pointwise_abstract_group G (X .fst)

{` Litmus: the neutral element is the constant function x ↦ e and the
   product is computed pointwise, both judgmentally as printed. `}
def abstract_group_of_maps_unit (G : AbstractGroup) (X : SetTypes)
  : Id (X .fst → G .carrier) (abstract_group_of_maps G X .unit) (_ ↦ G .unit)
  ≔ refl (abstract_group_of_maps G X .unit)

def abstract_group_of_maps_mul (G : AbstractGroup) (X : SetTypes) (f g : X .fst → G .carrier) (x : X .fst)
  : Id (G .carrier) (abstract_group_of_maps G X .mul f g x) (G .mul (f x) (g x))
  ≔ refl (G .mul (f x) (g x))

{` "abelian if and only if G is". The forward direction holds for every X. `}
def pointwise_abelian (G : AbstractGroup) (X : Type) (h : IsAbstractAbelian G)
  : IsAbstractAbelian (pointwise_abstract_group G X)
  ≔ f g ↦ funext X (_ ↦ G .carrier) (pointwise_mul G X f g) (pointwise_mul G X g f) (x ↦ h (f x) (g x))

{` The converse holds when X is merely inhabited: evaluate the commutation
   of the constant functions at a point of X. `}
def pointwise_abelian_reflect (G : AbstractGroup) (X : Type) (m : Mere X)
  (h : IsAbstractAbelian (pointwise_abstract_group G X)) : IsAbstractAbelian G
  ≔ g g' ↦ mere_rec X (Id (G .carrier) (G .mul g g') (G .mul g' g))
      (abstract_group_set G (G .mul g g') (G .mul g' g))
      (x ↦ refl ((φ ↦ φ x) : (X → G .carrier) → G .carrier) (h (_ ↦ g) (_ ↦ g'))) m

def abstract_group_of_maps_abelian_iff (G : AbstractGroup) (X : SetTypes) (m : Mere (X .fst))
  : Product (IsAbstractAbelian G → IsAbstractAbelian (abstract_group_of_maps G X))
      (IsAbstractAbelian (abstract_group_of_maps G X) → IsAbstractAbelian G)
  ≔ (pointwise_abelian G (X .fst), pointwise_abelian_reflect G (X .fst) m)

{` The printed "only if" fails for X = ∅: Empty → S is contractible, so the
   group of maps is abelian, while abstr(Σ_3) is not (module 406). `}
def empty_set_type : SetTypes ≔ (Empty, empty_set)

def empty_maps_abelian (G : AbstractGroup) : IsAbstractAbelian (abstract_group_of_maps G empty_set_type)
  ≔ f g ↦ funext Empty (_ ↦ G .carrier) (pointwise_mul G Empty f g) (pointwise_mul G Empty g f)
      (x ↦ match x [])

def abstract_group_of_maps_abelian_converse_fails
  (h : (G : AbstractGroup) (X : SetTypes) → IsAbstractAbelian (abstract_group_of_maps G X) → IsAbstractAbelian G)
  : Empty
  ≔ symmetric_group_three_not_abelian
      (h (abstr (symmetric_group three)) empty_set_type (empty_maps_abelian (abstr (symmetric_group three))))
