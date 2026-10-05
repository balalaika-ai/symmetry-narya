export "401-group-homomorphisms"

{` Chapter 4, section "Abstract groups" (group.tex).

   def:abstractgroup. The laws are grouped as in absgroup.tex
   (GroupLaws = MonoidLaws × InverseLaw, with isSet(S) among the monoid
   laws); the unit law (a) is split into its two halves. The book's
   product g₁ · g₂ is mul g₁ g₂. `}
def AbstractGroupLaws (S : Type) (e : S) (mul : S → S → S) (inv : S → S) : Type ≔ sig (
  carrier_set : isSet S,
  unit_right : (g : S) → Id S (mul g e) g,
  unit_left : (g : S) → Id S (mul e g) g,
  assoc : (g1 g2 g3 : S) → Id S (mul g1 (mul g2 g3)) (mul (mul g1 g2) g3),
  inv_right : (g : S) → Id S (mul g (inv g)) e)

def AbstractGroup : Type ≔ sig (
  carrier : Type,
  unit : carrier,
  mul : carrier → carrier → carrier,
  inv : carrier → carrier,
  laws : AbstractGroupLaws carrier unit mul inv)

{` The remark after def:abstractgroup: the laws are a proposition. `}
def abstract_group_laws_prop (S : Type) (e : S) (mul : S → S → S) (inv : S → S)
  : isProp (AbstractGroupLaws S e mul inv)
  ≔ u v ↦ let hS ≔ u .carrier_set in
    (isset_isprop S (u .carrier_set) (v .carrier_set),
     pi_prop S (g ↦ Id S (mul g e) g) (g ↦ hS (mul g e) g) (u .unit_right) (v .unit_right),
     pi_prop S (g ↦ Id S (mul e g) g) (g ↦ hS (mul e g) g) (u .unit_left) (v .unit_left),
     pi_prop S (g1 ↦ (g2 g3 : S) → Id S (mul g1 (mul g2 g3)) (mul (mul g1 g2) g3))
       (g1 ↦ pi_prop S (g2 ↦ (g3 : S) → Id S (mul g1 (mul g2 g3)) (mul (mul g1 g2) g3))
         (g2 ↦ pi_prop S (g3 ↦ Id S (mul g1 (mul g2 g3)) (mul (mul g1 g2) g3))
           (g3 ↦ hS (mul g1 (mul g2 g3)) (mul (mul g1 g2) g3))))
       (u .assoc) (v .assoc),
     pi_prop S (g ↦ Id S (mul g (inv g)) e) (g ↦ hS (mul g (inv g)) e) (u .inv_right) (v .inv_right))

def abstract_group_set (G : AbstractGroup) : isSet (G .carrier) ≔ G .laws .carrier_set

{` lem:idtypesgiveabstractgroups. USym G with e ≔ refl, g⁻¹ ≔ symm g and
   h · g ≔ trans(g)(h) = concat g h (usym_mul of module 400). Unit laws:
   g · e = concat refl g = g (concat_1p) and e · g = concat g refl = g
   (concat_p1); the book's judgmental e · g ≡ g is the identification
   concat_p1 here (Narya's J has a typal β-rule). `}
def usym_abstract_laws (G : Group) : AbstractGroupLaws (USym G) (usym_unit G) (usym_mul G) (usym_inv G)
  ≔ let A ≔ BG G .carrier in let a ≔ shape G in
    (usym_set G,
     g ↦ concat_1p A a a g,
     g ↦ concat_p1 A a a g,
     g1 g2 g3 ↦ concat_assoc A a a a a g3 g2 g1,
     g ↦ concat_inverse_left A a a g)

{` def:abstrG. abstr(G), the abstract group associated to G. `}
def abstr (G : Group) : AbstractGroup
  ≔ (USym G, usym_unit G, usym_mul G, usym_inv G, usym_abstract_laws G)

{` Abstract homomorphisms as in absgroup.tex def:abstrisfunctor:
   functions preserving multiplication. `}
def IsAbstractHom (G H : AbstractGroup) (f : G .carrier → H .carrier) : Type
  ≔ (s s' : G .carrier) → Id (H .carrier) (f (G .mul s s')) (H .mul (f s) (f s'))

def is_abstract_hom_prop (G H : AbstractGroup) (f : G .carrier → H .carrier) : isProp (IsAbstractHom G H f)
  ≔ pi_prop (G .carrier) (s ↦ (s' : G .carrier) → Id (H .carrier) (f (G .mul s s')) (H .mul (f s) (f s')))
      (s ↦ pi_prop (G .carrier) (s' ↦ Id (H .carrier) (f (G .mul s s')) (H .mul (f s) (f s')))
        (s' ↦ abstract_group_set H (f (G .mul s s')) (H .mul (f s) (f s'))))

def AbstractHom (G H : AbstractGroup) : Type ≔ Σ (G .carrier → H .carrier) (IsAbstractHom G H)

{` rem:first-abs-hom: USym f is an abstract homomorphism abstr(G) → abstr(H). `}
def abstr_hom (G H : Group) (f : GroupHom G H) : AbstractHom (abstr G) (abstr H)
  ≔ (usym_hom G H f, s s' ↦ usym_hom_mul G H f s s')

{` Abelian abstract groups; isAb(G) of def:abgp is literally
   IsAbstractAbelian (abstr G). `}
def IsAbstractAbelian (G : AbstractGroup) : Type
  ≔ (g h : G .carrier) → Id (G .carrier) (G .mul g h) (G .mul h g)

def abelian_abstr (G : Group) : Id Type (IsAbelian G) (IsAbstractAbelian (abstr G)) ≔ refl (IsAbelian G)
