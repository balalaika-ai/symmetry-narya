export "01-groups"

{` Blind statements, chapter 4, section "Abstract groups". `}

{` def:abstractgroup. The laws are split off so that the remark on their
   uniqueness and the lemma below can refer to them. `}
def BlindAbstractGroupLaws (S : Type) (e : S) (mul : S → S → S) (inv : S → S) : Type
  ≔ sig (
    runit : (g : S) → Id S (mul g e) g,
    lunit : (g : S) → Id S (mul e g) g,
    assoc : (g1 g2 g3 : S) → Id S (mul g1 (mul g2 g3)) (mul (mul g1 g2) g3),
    invlaw : (g : S) → Id S (mul g (inv g)) e)

def BlindAbstractGroup : Type
  ≔ sig (
    carrier : Type,
    is_set : isSet carrier,
    unit : carrier,
    mul : carrier → carrier → carrier,
    inv : carrier → carrier,
    laws : BlindAbstractGroupLaws carrier unit mul inv)

def BlindAbstractIsAb (A : BlindAbstractGroup) : Type
  ≔ (g h : A .carrier) → Id (A .carrier) (A .mul g h) (A .mul h g)

{` Remark after def:abstractgroup: the equations are propositions. `}
def blind_rem_abstract_laws_prop : Type
  ≔ (S : Type) (hS : isSet S) (e : S) (mul : S → S → S) (inv : S → S) →
    isProp (BlindAbstractGroupLaws S e mul inv)

{` lem:idtypesgiveabstractgroups: e = refl, g^{-1} = symm g,
   h·g = trans(g)(h) = concat g h. `}
def blind_usym_mul (G : BlindGroup) (h g : BlindUSym G) : BlindUSym G
  ≔ concat (blind_B G .fst) (blind_shape G) (blind_shape G) (blind_shape G) g h
def blind_usym_inv (G : BlindGroup) (g : BlindUSym G) : BlindUSym G
  ≔ inverse (blind_B G .fst) (blind_shape G) (blind_shape G) g
def blind_usym_unit (G : BlindGroup) : BlindUSym G ≔ refl (blind_shape G)

def blind_lem_idtypes_abstract_groups : Type
  ≔ (G : BlindGroup) →
    Product (isSet (BlindUSym G))
      (BlindAbstractGroupLaws (BlindUSym G) (blind_usym_unit G) (blind_usym_mul G) (blind_usym_inv G))

{` def:abstrG, parametrized by the lemma. `}
def blind_abstr (h : blind_lem_idtypes_abstract_groups) (G : BlindGroup) : BlindAbstractGroup
  ≔ (BlindUSym G, h G .fst, blind_usym_unit G, blind_usym_mul G, blind_usym_inv G, h G .snd)

{` xca:abstract-group-of-maps: pointwise structure on X → S (inverse also
   pointwise); it is abelian iff the original group is. Stated for any
   set X; the abelian equivalence is literally for every X (it fails for
   empty X, see the corrected variant, which assumes X merely inhabited). `}
def blind_pointwise_mul (A : BlindAbstractGroup) (X : Type) (f g : X → A .carrier) : X → A .carrier
  ≔ x ↦ A .mul (f x) (g x)

def blind_xca_abstract_group_of_maps : Type
  ≔ (A : BlindAbstractGroup) (X : Type) (hX : isSet X) →
    Σ (BlindAbstractGroupLaws (X → A .carrier) (_ ↦ A .unit) (blind_pointwise_mul A X) (f ↦ x ↦ A .inv (f x))) (laws ↦
      BlindIff
        (BlindAbstractIsAb (X → A .carrier, pi_set X (_ ↦ A .carrier) (_ ↦ A .is_set), _ ↦ A .unit,
          blind_pointwise_mul A X, f ↦ x ↦ A .inv (f x), laws))
        (BlindAbstractIsAb A))

def blind_xca_abstract_group_of_maps_corrected : Type
  ≔ (A : BlindAbstractGroup) (X : Type) (hX : isSet X) (x0 : Mere X) →
    Σ (BlindAbstractGroupLaws (X → A .carrier) (_ ↦ A .unit) (blind_pointwise_mul A X) (f ↦ x ↦ A .inv (f x))) (laws ↦
      BlindIff
        (BlindAbstractIsAb (X → A .carrier, pi_set X (_ ↦ A .carrier) (_ ↦ A .is_set), _ ↦ A .unit,
          blind_pointwise_mul A X, f ↦ x ↦ A .inv (f x), laws))
        (BlindAbstractIsAb A))
