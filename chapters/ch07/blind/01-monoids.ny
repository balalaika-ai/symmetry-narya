export "../../../src/403-abstract-groups"

{` Blind statements, chapter 7, section "Monoids and abstract groups" (absgroup.tex). `}

{` The propositions UnitLaws, AssocLaw, MonoidLaws, InverseLaw, GroupLaws
   (not:GroupLaws). The multiplication μ is curried: μ(g)(h) = g · h. `}
def BlindUnitLaws (S : Type) (e : S) (mu : S → S → S) : Type
  ≔ (g : S) → Product (Id S (mu g e) g) (Id S (mu e g) g)

def BlindAssocLaw (S : Type) (mu : S → S → S) : Type
  ≔ (g1 g2 g3 : S) → Id S (mu g1 (mu g2 g3)) (mu (mu g1 g2) g3)

def BlindMonoidLaws (S : Type) (e : S) (mu : S → S → S) : Type
  ≔ Product (isSet S) (Product (BlindUnitLaws S e mu) (BlindAssocLaw S mu))

def BlindInverseLaw (S : Type) (e : S) (mu : S → S → S) (iota : S → S) : Type
  ≔ (g : S) → Id S (mu g (iota g)) e

def BlindGroupLaws (S : Type) (e : S) (mu : S → S → S) (iota : S → S) : Type
  ≔ Product (BlindMonoidLaws S e mu) (BlindInverseLaw S e mu iota)

{` def:monoid. `}
def BlindMonoid : Type ≔ sig (
  carrier : Type,
  unit : carrier,
  mul : carrier → carrier → carrier,
  laws : BlindMonoidLaws carrier unit mul)

{` exa:monoid: lists over a set S with the empty list and concatenation
   (append, module 01) form a monoid; in particular S* is a set. `}
def blind_exa_monoid : Type
  ≔ (S : Type) (hS : isSet S) → BlindMonoidLaws (List S) nil. (append S)

{` def:type-abstrgp: Σ S Σ e Σ μ Σ ι GroupLaws(S,e,μ,ι), as a record. `}
def BlindAbsGroup : Type ≔ sig (
  carrier : Type,
  unit : carrier,
  mul : carrier → carrier → carrier,
  inv : carrier → carrier,
  laws : BlindGroupLaws carrier unit mul inv)

def blind_ag_set (G : BlindAbsGroup) : isSet (G .carrier) ≔ G .laws .fst .fst
def blind_ag_runit (G : BlindAbsGroup) (g : G .carrier) : Id (G .carrier) (G .mul g (G .unit)) g
  ≔ G .laws .fst .snd .fst g .fst
def blind_ag_lunit (G : BlindAbsGroup) (g : G .carrier) : Id (G .carrier) (G .mul (G .unit) g) g
  ≔ G .laws .fst .snd .fst g .snd
def blind_ag_assoc (G : BlindAbsGroup) (g1 g2 g3 : G .carrier)
  : Id (G .carrier) (G .mul g1 (G .mul g2 g3)) (G .mul (G .mul g1 g2) g3)
  ≔ G .laws .fst .snd .snd g1 g2 g3
def blind_ag_rinv (G : BlindAbsGroup) (g : G .carrier) : Id (G .carrier) (G .mul g (G .inv g)) (G .unit)
  ≔ G .laws .snd g

{` The underlying monoid of an abstract group. `}
def blind_ag_monoid (G : BlindAbsGroup) : BlindMonoid ≔ (G .carrier, G .unit, G .mul, G .laws .fst)

{` Helper (proof needed by later definitions, cf. xca:left-inv-involution):
   g⁻¹ · g = e, by k ≔ (g⁻¹)⁻¹ = e·k = (g·g⁻¹)·k = g·(g⁻¹·k) = g·e = g. `}
def blind_ag_inv_inv (G : BlindAbsGroup) (g : G .carrier) : Id (G .carrier) (G .inv (G .inv g)) g
  ≔ let S ≔ G .carrier in let h ≔ G .inv g in let k ≔ G .inv h in
    calc
      k = G .mul (G .unit) k by inverse S (G .mul (G .unit) k) k (blind_ag_lunit G k)
      = G .mul (G .mul g h) k by refl ((x ↦ G .mul x k) : S → S) (inverse S (G .mul g h) (G .unit) (blind_ag_rinv G g))
      = G .mul g (G .mul h k) by inverse S (G .mul g (G .mul h k)) (G .mul (G .mul g h) k) (blind_ag_assoc G g h k)
      = G .mul g (G .unit) by refl (G .mul g) (blind_ag_rinv G h)
      = g by blind_ag_runit G g ∎

def blind_ag_linv (G : BlindAbsGroup) (g : G .carrier) : Id (G .carrier) (G .mul (G .inv g) g) (G .unit)
  ≔ let S ≔ G .carrier in
    concat S (G .mul (G .inv g) g) (G .mul (G .inv g) (G .inv (G .inv g))) (G .unit)
      (refl (G .mul (G .inv g)) (inverse S (G .inv (G .inv g)) g (blind_ag_inv_inv G g)))
      (blind_ag_rinv G (G .inv g))

{` def:abstrG (chapter 4) for this record: abstr(G) = (USym G, refl, ·, ⁻¹)
   with g · h = usym_mul G g h (= concat h g), laws of module 403. `}
def blind_abstr (G : Group) : BlindAbsGroup
  ≔ let L ≔ usym_abstract_laws G in
    (USym G, usym_unit G, usym_mul G, usym_inv G,
     ((L .carrier_set, (g ↦ (L .unit_right g, L .unit_left g), L .assoc)), L .inv_right))

{` rem:inverses-as-property, property (axiom:mere-inverse): for all g
   there exists h with e = g · h. `}
def BlindMereInverse (S : Type) (e : S) (mu : S → S → S) : Type
  ≔ (g : S) → Mere (Σ S (h ↦ Id S e (mu g h)))

{` lem:group-inv-operation: under the monoid laws and the mere-inverse
   property there is a unique inverse function with the law of inverses
   (contractible type of such functions). `}
def blind_lem_group_inv_operation : Type
  ≔ (S : Type) (e : S) (mu : S → S → S) (laws : BlindMonoidLaws S e mu)
    (minv : BlindMereInverse S e mu)
    → BookIsContr (Σ (S → S) (iota ↦ BlindInverseLaw S e mu iota))

{` rem:abs-iso: an isomorphism of abstract groups is an equivalence f : S ≃ S'
   with e' = f(e) and μ'(f(s), f(t)) = f(μ(s,t)). `}
def BlindIsAbsIso (G H : BlindAbsGroup) (f : G .carrier → H .carrier) : Type
  ≔ Product (BookIsEquiv (G .carrier) (H .carrier) f)
      (Product (Id (H .carrier) (H .unit) (f (G .unit)))
        ((s t : G .carrier) → Id (H .carrier) (H .mul (f s) (f t)) (f (G .mul s t))))

def BlindAbsIso (G H : BlindAbsGroup) : Type ≔ Σ (G .carrier → H .carrier) (BlindIsAbsIso G H)

{` rem:abs-iso, claim: applying univalence to an isomorphism yields an
   identification of abstract groups (whose underlying transport is f). `}
def blind_rem_abs_iso : Type
  ≔ (G H : BlindAbsGroup) (f : BlindAbsIso G H)
    → Σ (Id BlindAbsGroup G H) (p ↦
        (s : G .carrier) → Id (H .carrier) (transport BlindAbsGroup (K ↦ K .carrier) G H p s) (f .fst s))

{` xca (absgroup.tex 215), "perform the abovementioned analysis":
   G = G' is equivalent to the type of p : S = S' with e' = p(e) and
   μ'(p(s), p(t)) = p(μ(s,t)), p(-) being transport along p. `}
def blind_xca_abs_iso_analysis : Type
  ≔ (G H : BlindAbsGroup)
    → BookEquiv (Id BlindAbsGroup G H)
        (Σ (Id Type (G .carrier) (H .carrier)) (p ↦
          let tr ≔ transport Type (X ↦ X) (G .carrier) (H .carrier) p in
          Product (Id (H .carrier) (H .unit) (tr (G .unit)))
            ((s t : G .carrier) → Id (H .carrier) (H .mul (tr s) (tr t)) (tr (G .mul s t)))))

{` xca:op-abs-group: G^op ≔ (S, e, μ^op, ι) is an abstract group and ι is
   an isomorphism G ≅ G^op. `}
def blind_op_mul (G : BlindAbsGroup) (a b : G .carrier) : G .carrier ≔ G .mul b a

def blind_xca_op_abs_group : Type
  ≔ (G : BlindAbsGroup)
    → Σ (BlindGroupLaws (G .carrier) (G .unit) (blind_op_mul G) (G .inv)) (l ↦
        BlindIsAbsIso G (G .carrier, G .unit, blind_op_mul G, G .inv, l) (G .inv))

{` xca:conj: conj^g(s) ≔ (g · s) · g⁻¹ preserves the group structure and is
   an equivalence, i.e. it is an isomorphism G ≅ G (rem:abs-iso). `}
def blind_conj (G : BlindAbsGroup) (g s : G .carrier) : G .carrier ≔ G .mul (G .mul g s) (G .inv g)

def blind_xca_conj : Type
  ≔ (G : BlindAbsGroup) (g : G .carrier) → BlindIsAbsIso G G (blind_conj G g)

{` xca:left-inv-involution. `}
def blind_xca_left_inv_involution : Type
  ≔ (G : BlindAbsGroup) (g : G .carrier)
    → Product (Id (G .carrier) (G .unit) (G .mul (G .inv g) g)) (Id (G .carrier) g (G .inv (G .inv g)))

{` xca:typemonoidisgroupoid. `}
def blind_xca_typemonoidisgroupoid : Type ≔ Product (isGroupoid BlindMonoid) (isGroupoid BlindAbsGroup)

{` xca:cheapgroup. A sheargroup: a set S, e : S, * : S → S → S with
   e*a = a, a*a = e, c*(b*a) = bar(c * bar b) * a, where bar a ≔ a*e. `}
def blind_shear_bar (S : Type) (e : S) (star : S → S → S) (a : S) : S ≔ star a e

def BlindShearGroup : Type ≔ sig (
  carrier : Type,
  is_set : isSet carrier,
  unit : carrier,
  op : carrier → carrier → carrier,
  law1 : (a : carrier) → Id carrier (op unit a) a,
  law2 : (a : carrier) → Id carrier (op a a) unit,
  law3 : (a b c : carrier) → Id carrier (op c (op b a))
    (op (blind_shear_bar carrier unit op (op c (blind_shear_bar carrier unit op b))) a))

def blind_xca_cheapgroup : Type ≔ BookEquiv BlindAbsGroup BlindShearGroup

{` xca (absgroup.tex 277), Furstenberg groups: a nonempty set with ∘ such that
   (a∘c)∘(b∘c) = a∘b and for all a, c there is b with a∘b = c. `}
def BlindFurstenbergGroup : Type ≔ sig (
  carrier : Type,
  is_set : isSet carrier,
  nonempty : Mere carrier,
  op : carrier → carrier → carrier,
  law1 : (a b c : carrier) → Id carrier (op (op a c) (op b c)) (op a b),
  law2 : (a c : carrier) → Mere (Σ carrier (b ↦ Id carrier (op a b) c)))

def blind_xca_furstenberg : Type ≔ BookEquiv BlindFurstenbergGroup BlindAbsGroup
