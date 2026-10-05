export "403-abstract-groups"

{` Chapter 7 (absgroup.tex), sec:monoids. Monoids (def:monoid), the named
   laws UnitLaws, AssocLaw, MonoidLaws, InverseLaw and GroupLaws displayed
   before def:type-abstrgp, the iterated Σ-form of the type of abstract
   groups (def:type-abstrgp), and the basic algebra of abstract groups
   used throughout the chapter.

   The record AbstractGroup of module 403 is the type of abstract groups;
   its laws record AbstractGroupLaws lists the same five components as
   GroupLaws (isSet, the two unit laws, associativity, the inverse law);
   group_laws_equiv and abstract_group_sigma_equiv identify the record
   with the book's iterated Σ (both round trips are refl). `}

def UnitLaws (S : Type) (e : S) (mul : S → S → S) : Type
  ≔ (g : S) → Product (Id S (mul g e) g) (Id S (mul e g) g)

def AssocLaw (S : Type) (mul : S → S → S) : Type
  ≔ (g1 g2 g3 : S) → Id S (mul g1 (mul g2 g3)) (mul (mul g1 g2) g3)

def MonoidLaws (S : Type) (e : S) (mul : S → S → S) : Type
  ≔ Product (isSet S) (Product (UnitLaws S e mul) (AssocLaw S mul))

def InverseLaw (S : Type) (e : S) (mul : S → S → S) (inv : S → S) : Type
  ≔ (g : S) → Id S (mul g (inv g)) e

def GroupLaws (S : Type) (e : S) (mul : S → S → S) (inv : S → S) : Type
  ≔ Product (MonoidLaws S e mul) (InverseLaw S e mul inv)

{` def:monoid. A monoid is a set S with a unit e and a multiplication
   satisfying the unit and associativity laws (the monoid laws, isSet
   included). `}
def Monoid : Type ≔ sig (
  carrier : Type,
  unit : carrier,
  mul : carrier → carrier → carrier,
  laws : MonoidLaws carrier unit mul)

def monoid_set (M : Monoid) : isSet (M .carrier) ≔ M .laws .fst

def monoid_unit_right (M : Monoid) (g : M .carrier) : Id (M .carrier) (M .mul g (M .unit)) g
  ≔ M .laws .snd .fst g .fst

def monoid_unit_left (M : Monoid) (g : M .carrier) : Id (M .carrier) (M .mul (M .unit) g) g
  ≔ M .laws .snd .fst g .snd

def monoid_assoc (M : Monoid) (g1 g2 g3 : M .carrier)
  : Id (M .carrier) (M .mul g1 (M .mul g2 g3)) (M .mul (M .mul g1 g2) g3)
  ≔ M .laws .snd .snd g1 g2 g3

{` The monoid laws are a proposition (the laws are equations in a set). `}
def monoid_laws_prop (S : Type) (e : S) (mul : S → S → S) : isProp (MonoidLaws S e mul)
  ≔ u v ↦ let hS ≔ u .fst in
    (isset_isprop S (u .fst) (v .fst),
     (pi_prop S (g ↦ Product (Id S (mul g e) g) (Id S (mul e g) g))
        (g ↦ product_prop (Id S (mul g e) g) (Id S (mul e g) g) (hS (mul g e) g) (hS (mul e g) g))
        (u .snd .fst) (v .snd .fst),
      pi_prop S (g1 ↦ (g2 g3 : S) → Id S (mul g1 (mul g2 g3)) (mul (mul g1 g2) g3))
        (g1 ↦ pi_prop S (g2 ↦ (g3 : S) → Id S (mul g1 (mul g2 g3)) (mul (mul g1 g2) g3))
          (g2 ↦ pi_prop S (g3 ↦ Id S (mul g1 (mul g2 g3)) (mul (mul g1 g2) g3))
            (g3 ↦ hS (mul g1 (mul g2 g3)) (mul (mul g1 g2) g3))))
        (u .snd .snd) (v .snd .snd)))

def group_laws_prop (S : Type) (e : S) (mul : S → S → S) (inv : S → S) : isProp (GroupLaws S e mul inv)
  ≔ u v ↦
    (monoid_laws_prop S e mul (u .fst) (v .fst),
     pi_prop S (g ↦ Id S (mul g (inv g)) e) (g ↦ u .fst .fst (mul g (inv g)) e) (u .snd) (v .snd))

{` The record of laws of module 403 is the book's GroupLaws. `}
def group_laws_from_record (S : Type) (e : S) (mul : S → S → S) (inv : S → S)
  (l : AbstractGroupLaws S e mul inv) : GroupLaws S e mul inv
  ≔ ((l .carrier_set, (g ↦ (l .unit_right g, l .unit_left g), l .assoc)), l .inv_right)

def group_laws_to_record (S : Type) (e : S) (mul : S → S → S) (inv : S → S)
  (t : GroupLaws S e mul inv) : AbstractGroupLaws S e mul inv
  ≔ (carrier_set ≔ t .fst .fst,
     unit_right ≔ g ↦ t .fst .snd .fst g .fst,
     unit_left ≔ g ↦ t .fst .snd .fst g .snd,
     assoc ≔ t .fst .snd .snd,
     inv_right ≔ t .snd)

def group_laws_equiv (S : Type) (e : S) (mul : S → S → S) (inv : S → S)
  : Equiv (AbstractGroupLaws S e mul inv) (GroupLaws S e mul inv)
  ≔ quasi_inverse_equiv (AbstractGroupLaws S e mul inv) (GroupLaws S e mul inv)
      (group_laws_from_record S e mul inv) (group_laws_to_record S e mul inv)
      (l ↦ refl l) (t ↦ refl t)

{` def:type-abstrgp. The book's type of abstract groups,
   Σ(S : U) Σ(e : S) Σ(μ : S → S → S) Σ(ι : S → S) GroupLaws(S, e, μ, ι). `}
def AbstractGroupSigma : Type
  ≔ Σ Type (S ↦ Σ S (e ↦ Σ (S → S → S) (mul ↦ Σ (S → S) (inv ↦ GroupLaws S e mul inv))))

def abstract_group_to_sigma (G : AbstractGroup) : AbstractGroupSigma
  ≔ (G .carrier, (G .unit, (G .mul, (G .inv, group_laws_from_record (G .carrier) (G .unit) (G .mul) (G .inv) (G .laws)))))

def abstract_group_from_sigma (t : AbstractGroupSigma) : AbstractGroup
  ≔ (t .fst, t .snd .fst, t .snd .snd .fst, t .snd .snd .snd .fst,
     group_laws_to_record (t .fst) (t .snd .fst) (t .snd .snd .fst) (t .snd .snd .snd .fst) (t .snd .snd .snd .snd))

def abstract_group_sigma_equiv : Equiv AbstractGroup AbstractGroupSigma
  ≔ quasi_inverse_equiv AbstractGroup AbstractGroupSigma abstract_group_to_sigma abstract_group_from_sigma
      (G ↦ refl G) (t ↦ refl t)

{` The underlying monoid of an abstract group (rem:monoid-hom). `}
def abstract_group_monoid (G : AbstractGroup) : Monoid
  ≔ (G .carrier, G .unit, G .mul, group_laws_from_record (G .carrier) (G .unit) (G .mul) (G .inv) (G .laws) .fst)

{` Basic algebra of an abstract group G = (S, e, μ, ι). The book writes
   g · h for μ(g)(h) = G .mul g h. `}

{` xca:left-inv-involution, first half (in the orientation g⁻¹ · g = e). `}
def ag_inv_left (G : AbstractGroup) (g : G .carrier) : Id (G .carrier) (G .mul (G .inv g) g) (G .unit)
  ≔ let S ≔ G .carrier in let m ≔ G .mul in let L ≔ G .laws in
    let h ≔ G .inv g in let ih ≔ G .inv h in
    calc
      m h g = m (m h g) (G .unit) by inverse S (m (m h g) (G .unit)) (m h g) (L .unit_right (m h g))
      = m (m h g) (m h ih) by refl (m (m h g)) (inverse S (m h ih) (G .unit) (L .inv_right h))
      = m (m (m h g) h) ih by L .assoc (m h g) h ih
      = m (m h (m g h)) ih
        by refl ((x ↦ m x ih) : S → S) (inverse S (m h (m g h)) (m (m h g) h) (L .assoc h g h))
      = m (m h (G .unit)) ih by refl ((x ↦ m (m h x) ih) : S → S) (L .inv_right g)
      = m h ih by refl ((x ↦ m x ih) : S → S) (L .unit_right h)
      = G .unit by L .inv_right h ∎

{` Uniqueness of inverses: a right inverse h of g is ι(g). `}
def ag_inv_unique_right (G : AbstractGroup) (g h : G .carrier) (p : Id (G .carrier) (G .mul g h) (G .unit))
  : Id (G .carrier) h (G .inv g)
  ≔ let S ≔ G .carrier in let m ≔ G .mul in let L ≔ G .laws in let e ≔ G .unit in
    let ig ≔ G .inv g in
    calc
      h = m e h by inverse S (m e h) h (L .unit_left h)
      = m (m ig g) h by refl ((x ↦ m x h) : S → S) (inverse S (m ig g) e (ag_inv_left G g))
      = m ig (m g h) by inverse S (m ig (m g h)) (m (m ig g) h) (L .assoc ig g h)
      = m ig e by refl (m ig) p
      = ig by L .unit_right ig ∎

{` A left inverse h of g is ι(g). `}
def ag_inv_unique_left (G : AbstractGroup) (g h : G .carrier) (p : Id (G .carrier) (G .mul h g) (G .unit))
  : Id (G .carrier) h (G .inv g)
  ≔ let S ≔ G .carrier in let m ≔ G .mul in let L ≔ G .laws in let e ≔ G .unit in
    let ig ≔ G .inv g in
    calc
      h = m h e by inverse S (m h e) h (L .unit_right h)
      = m h (m g ig) by refl (m h) (inverse S (m g ig) e (L .inv_right g))
      = m (m h g) ig by L .assoc h g ig
      = m e ig by refl ((x ↦ m x ig) : S → S) p
      = ig by L .unit_left ig ∎

{` xca:left-inv-involution, second half: g = (g⁻¹)⁻¹. `}
def ag_inv_involution (G : AbstractGroup) (g : G .carrier) : Id (G .carrier) g (G .inv (G .inv g))
  ≔ ag_inv_unique_left G (G .inv g) g (G .laws .inv_right g)

def ag_inv_inv (G : AbstractGroup) (g : G .carrier) : Id (G .carrier) (G .inv (G .inv g)) g
  ≔ inverse (G .carrier) g (G .inv (G .inv g)) (ag_inv_involution G g)

{` (a · b)⁻¹ = b⁻¹ · a⁻¹. `}
def ag_inv_mul (G : AbstractGroup) (a b : G .carrier)
  : Id (G .carrier) (G .inv (G .mul a b)) (G .mul (G .inv b) (G .inv a))
  ≔ let S ≔ G .carrier in let m ≔ G .mul in let L ≔ G .laws in let e ≔ G .unit in
    let ia ≔ G .inv a in let ib ≔ G .inv b in
    let p : Id S (m (m a b) (m ib ia)) e
      ≔ calc
          m (m a b) (m ib ia) = m a (m b (m ib ia))
            by inverse S (m a (m b (m ib ia))) (m (m a b) (m ib ia)) (L .assoc a b (m ib ia))
          = m a (m (m b ib) ia) by refl (m a) (L .assoc b ib ia)
          = m a (m e ia) by refl ((x ↦ m a (m x ia)) : S → S) (L .inv_right b)
          = m a ia by refl (m a) (L .unit_left ia)
          = e by L .inv_right a ∎ in
    inverse S (m ib ia) (G .inv (m a b)) (ag_inv_unique_right G (m a b) (m ib ia) p)

{` e⁻¹ = e. `}
def ag_inv_unit (G : AbstractGroup) : Id (G .carrier) (G .inv (G .unit)) (G .unit)
  ≔ inverse (G .carrier) (G .unit) (G .inv (G .unit))
      (ag_inv_unique_right G (G .unit) (G .unit) (G .laws .unit_right (G .unit)))

{` Uniqueness of the unit: a left (or right) unit for μ is e. `}
def ag_unit_unique_left (G : AbstractGroup) (u : G .carrier) (h : (g : G .carrier) → Id (G .carrier) (G .mul u g) g)
  : Id (G .carrier) u (G .unit)
  ≔ concat (G .carrier) u (G .mul u (G .unit)) (G .unit)
      (inverse (G .carrier) (G .mul u (G .unit)) u (G .laws .unit_right u)) (h (G .unit))

def ag_unit_unique_right (G : AbstractGroup) (u : G .carrier) (h : (g : G .carrier) → Id (G .carrier) (G .mul g u) g)
  : Id (G .carrier) u (G .unit)
  ≔ concat (G .carrier) u (G .mul (G .unit) u) (G .unit)
      (inverse (G .carrier) (G .mul (G .unit) u) u (G .laws .unit_left u)) (h (G .unit))

{` An idempotent is the unit: u · u = u implies u = e. `}
def ag_idempotent_unit (G : AbstractGroup) (u : G .carrier) (h : Id (G .carrier) (G .mul u u) u)
  : Id (G .carrier) u (G .unit)
  ≔ let S ≔ G .carrier in let m ≔ G .mul in let L ≔ G .laws in let iu ≔ G .inv u in
    calc
      u = m u (G .unit) by inverse S (m u (G .unit)) u (L .unit_right u)
      = m u (m u iu) by refl (m u) (inverse S (m u iu) (G .unit) (L .inv_right u))
      = m (m u u) iu by L .assoc u u iu
      = m u iu by refl ((x ↦ m x iu) : S → S) h
      = G .unit by L .inv_right u ∎

{` Cancellation. `}
def ag_cancel_left (G : AbstractGroup) (a b c : G .carrier) (p : Id (G .carrier) (G .mul a b) (G .mul a c))
  : Id (G .carrier) b c
  ≔ let S ≔ G .carrier in let m ≔ G .mul in let L ≔ G .laws in let e ≔ G .unit in
    let ia ≔ G .inv a in
    calc
      b = m e b by inverse S (m e b) b (L .unit_left b)
      = m (m ia a) b by refl ((x ↦ m x b) : S → S) (inverse S (m ia a) e (ag_inv_left G a))
      = m ia (m a b) by inverse S (m ia (m a b)) (m (m ia a) b) (L .assoc ia a b)
      = m ia (m a c) by refl (m ia) p
      = m (m ia a) c by L .assoc ia a c
      = m e c by refl ((x ↦ m x c) : S → S) (ag_inv_left G a)
      = c by L .unit_left c ∎

def ag_cancel_right (G : AbstractGroup) (a b c : G .carrier) (p : Id (G .carrier) (G .mul b a) (G .mul c a))
  : Id (G .carrier) b c
  ≔ let S ≔ G .carrier in let m ≔ G .mul in let L ≔ G .laws in let e ≔ G .unit in
    let ia ≔ G .inv a in
    calc
      b = m b e by inverse S (m b e) b (L .unit_right b)
      = m b (m a ia) by refl (m b) (inverse S (m a ia) e (L .inv_right a))
      = m (m b a) ia by L .assoc b a ia
      = m (m c a) ia by refl ((x ↦ m x ia) : S → S) p
      = m c (m a ia) by inverse S (m c (m a ia)) (m (m c a) ia) (L .assoc c a ia)
      = m c e by refl (m c) (L .inv_right a)
      = c by L .unit_right c ∎

{` g⁻¹ · (g · x) = x and g · (g⁻¹ · x) = x; x · g · g⁻¹ = x and x · g⁻¹ · g = x. `}
def ag_mul_inv_cancel_left (G : AbstractGroup) (g x : G .carrier)
  : Id (G .carrier) (G .mul (G .inv g) (G .mul g x)) x
  ≔ let S ≔ G .carrier in let m ≔ G .mul in let L ≔ G .laws in let ig ≔ G .inv g in
    calc
      m ig (m g x) = m (m ig g) x by L .assoc ig g x
      = m (G .unit) x by refl ((y ↦ m y x) : S → S) (ag_inv_left G g)
      = x by L .unit_left x ∎

def ag_mul_cancel_inv_left (G : AbstractGroup) (g x : G .carrier)
  : Id (G .carrier) (G .mul g (G .mul (G .inv g) x)) x
  ≔ let S ≔ G .carrier in let m ≔ G .mul in let L ≔ G .laws in let ig ≔ G .inv g in
    calc
      m g (m ig x) = m (m g ig) x by L .assoc g ig x
      = m (G .unit) x by refl ((y ↦ m y x) : S → S) (L .inv_right g)
      = x by L .unit_left x ∎

def ag_mul_inv_cancel_right (G : AbstractGroup) (x g : G .carrier)
  : Id (G .carrier) (G .mul (G .mul x g) (G .inv g)) x
  ≔ let S ≔ G .carrier in let m ≔ G .mul in let L ≔ G .laws in let ig ≔ G .inv g in
    calc
      m (m x g) ig = m x (m g ig) by inverse S (m x (m g ig)) (m (m x g) ig) (L .assoc x g ig)
      = m x (G .unit) by refl (m x) (L .inv_right g)
      = x by L .unit_right x ∎

def ag_mul_cancel_inv_right (G : AbstractGroup) (x g : G .carrier)
  : Id (G .carrier) (G .mul (G .mul x (G .inv g)) g) x
  ≔ let S ≔ G .carrier in let m ≔ G .mul in let L ≔ G .laws in let ig ≔ G .inv g in
    calc
      m (m x ig) g = m x (m ig g) by inverse S (m x (m ig g)) (m (m x ig) g) (L .assoc x ig g)
      = m x (G .unit) by refl (m x) (ag_inv_left G g)
      = x by L .unit_right x ∎

{` Left and right multiplication by g are equivalences of S. `}
def ag_mul_left_equiv (G : AbstractGroup) (g : G .carrier) : Equiv (G .carrier) (G .carrier)
  ≔ quasi_inverse_equiv (G .carrier) (G .carrier) (x ↦ G .mul g x) (x ↦ G .mul (G .inv g) x)
      (x ↦ ag_mul_inv_cancel_left G g x) (x ↦ ag_mul_cancel_inv_left G g x)

def ag_mul_right_equiv (G : AbstractGroup) (g : G .carrier) : Equiv (G .carrier) (G .carrier)
  ≔ quasi_inverse_equiv (G .carrier) (G .carrier) (x ↦ G .mul x g) (x ↦ G .mul x (G .inv g))
      (x ↦ ag_mul_inv_cancel_right G x g) (x ↦ ag_mul_cancel_inv_right G x g)

{` Litmus: in abstr(G) the unit is refl and the product g · h is
   concat h g (module 400 convention), definitionally. `}
def ag_abstr_mul_litmus (G : Group) (g h : USym G)
  : Id (USym G) (abstr G .mul g h) (concat (BG G .carrier) (shape G) (shape G) (shape G) h g)
  ≔ refl (abstr G .mul g h)
