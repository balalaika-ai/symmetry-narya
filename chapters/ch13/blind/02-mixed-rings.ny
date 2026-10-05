import "01-abstract-rings"
import "../../../src/404-group-examples"

{` Blind statements, chapter 13 (fields.tex), sec:mixring. A mixed ring is
   based on a concrete group R; Hom(R,R) is GroupHom R R and the
   composition g ∘ f of homomorphisms is group_hom_compose R R R f g. `}

{` def:mixring, RingProps(R,1_R,ℓ,r) (named in def:typemixring):
   (unit laws) ℓ_{1_R} = id = r_{1_R}; the book prints id_G, a typo for
   id_R (there is no G here).
   (coherence law) (USym ℓ_g)(h) = (USym r_h)(g) for all g, h : USym R.
   (associativity law) printed as ℓ ∘ r = r ∘ ℓ, which is ill-typed
   (ℓ, r : USym R → Hom(R,R) do not compose); stated in the intended
   pointwise reading ℓ_g ∘ r_h = r_h ∘ ℓ_g for all g, h : USym R
   (cf. the preceding text: a·(-·b) = (a·-)·b). `}
def BlindRingProps (R : Group) (one : USym R) (l r : USym R → GroupHom R R) : Type ≔ sig (
  unit_left : Id (GroupHom R R) (l one) (group_hom_id R),
  unit_right : Id (GroupHom R R) (r one) (group_hom_id R),
  coherence : (g h : USym R) → Id (USym R) (usym_hom R R (l g) h) (usym_hom R R (r h) g),
  assoc : (g h : USym R) →
    Id (GroupHom R R) (group_hom_compose R R R (r h) (l g)) (group_hom_compose R R R (l g) (r h)))

{` def:mixring. A mixed ring (R, 1_R, ℓ, r). `}
def BlindMixRing : Type ≔ sig (
  grp : Group,
  one : USym grp,
  l : USym grp → GroupHom grp grp,
  r : USym grp → GroupHom grp grp,
  props : BlindRingProps grp one l r)

{` def:mixring: commutative means ℓ = r. `}
def BlindMixRingCommutative (R : BlindMixRing) : Type
  ≔ Id (USym (R .grp) → GroupHom (R .grp) (R .grp)) (R .l) (R .r)

{` def:mixring: non-trivial means 1_R ≠ refl_{sh_R}. `}
def BlindMixRingNonTrivial (R : BlindMixRing) : Type
  ≔ Not (Id (USym (R .grp)) (R .one) (usym_unit (R .grp)))

{` Footnote to def:mixring: the group of a mixed ring is abelian. `}
def blind_mixring_group_abelian : Type
  ≔ (R : BlindMixRing) → IsAbelian (R .grp)

{` Example after def:mixring. Z is circle_group C for any circle C. The map
   Bℓ_g : S¹ → S¹ is circle recursion with Bℓ_g(base) = base, Bℓ_g(loop) = g.
   The circle signature only gives Bℓ_g(base) = base propositionally, so the
   book's "pointed by reflexivity" becomes the inverse of that beta path. `}
def blind_circle_ell_map (C : CircleSignature) (g : USym (circle_group C)) : C .carrier → C .carrier
  ≔ circle_rec C (C .carrier) (C .base, g)

def blind_circle_ell (C : CircleSignature) (g : USym (circle_group C))
  : GroupHom (circle_group C) (circle_group C)
  ≔ mkhom (circle_group C) (circle_group C)
      (blind_circle_ell_map C g,
       inverse (C .carrier) (blind_circle_ell_map C g (C .base)) (C .base)
         (circle_rec_beta C (C .carrier) (C .base, g) .fst))

{` Example after def:mixring, its claim: with 1_Z ≔ loop and r ≔ ℓ, the
   unit, coherence and associativity laws hold, and (Z, 1_Z, ℓ, r) is a
   non-trivial commutative ring. The printed tuple (Z,1_Z,ℓ,!) is a typo
   for (Z,1_Z,ℓ,ℓ). `}
def blind_mixring_integers : Type
  ≔ (C : CircleSignature) →
      Σ (BlindRingProps (circle_group C) (C .loop) (blind_circle_ell C) (blind_circle_ell C)) (p ↦
        Product
          (BlindMixRingNonTrivial (circle_group C, C .loop, blind_circle_ell C, blind_circle_ell C, p))
          (BlindMixRingCommutative (circle_group C, C .loop, blind_circle_ell C, blind_circle_ell C, p)))

{` def:typemixring. The type of (mixed) rings as the literal iterated Σ
   Σ R : Group, Σ 1_R : USym R, Σ ℓ, r : USym R → Hom(R,R), RingProps. `}
def BlindTypeMixRing : Type
  ≔ Σ Group (R ↦
      Σ (USym R) (one ↦
        Σ (USym R → GroupHom R R) (l ↦
          Σ (USym R → GroupHom R R) (r ↦ BlindRingProps R one l r))))

{` def:typemixring. Commutative (mixed) rings: RingProps × (ℓ = r). `}
def BlindTypeMixCommRing : Type
  ≔ Σ Group (R ↦
      Σ (USym R) (one ↦
        Σ (USym R → GroupHom R R) (l ↦
          Σ (USym R → GroupHom R R) (r ↦
            Product (BlindRingProps R one l r) (Id (USym R → GroupHom R R) l r)))))

{` xca:Rmixring->URabstring. The multiplication · is not specified in the
   exercise (marked TBD); we take g·h ≔ (USym ℓ_g)(h), the abbreviation
   introduced after def:mixring (equal to (USym r_h)(g) by coherence). `}
def blind_mixring_mul (R : BlindMixRing) (g h : USym (R .grp)) : USym (R .grp)
  ≔ usym_hom (R .grp) (R .grp) (R .l g) h

{` xca:Rmixring->URabstring. USym R is an abstract ring with additive group
   abstr(R) and multiplicative monoid (USym R, 1_R, ·): the monoid laws and
   the distributive laws hold, so (abstr R, 1_R, ·, -, -) : BlindAbsRing. `}
def blind_mixring_abstract_ring : Type
  ≔ (R : BlindMixRing) →
      Product (MonoidLaws (USym (R .grp)) (R .one) (blind_mixring_mul R))
        (BlindDistrLaws (USym (R .grp)) (blind_mixring_mul R) (abstr (R .grp) .mul))
