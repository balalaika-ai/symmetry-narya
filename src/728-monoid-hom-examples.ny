export "701-abstract-homomorphisms"
export "721-mere-inverses"

{` Chapter 7 (absgroup.tex), sec:abshom: the footnote ft:monoid-hom,
   rem:monoid-hom (homomorphisms of monoids form a set), and litmus checks
   for xca:onlymult-hom and xca:abshomcomposition (proved in module 701).

   ft:monoid-hom. M is the monoid {0, 1} under multiplication, encoded as
   Bool with 0 = false, 1 = true (unit true, x · y = x ∧ y); the trivial
   monoid 1 is Unit. h : 1 → M, h(*) = 0, preserves multiplication but not
   the unit, and M is not (the monoid of) an abstract group: an inverse of
   0 would give 0 = 0 · 0⁻¹ = 1. `}

def two_element_monoid_mul (a b : Bool) : Bool ≔ match a [ false. ↦ false. | true. ↦ b ]

def two_element_monoid_laws : MonoidLaws Bool true. two_element_monoid_mul
  ≔ (bool_set,
     (g ↦ (match g [ false. ↦ refl (false. : Bool) | true. ↦ refl (true. : Bool) ], refl g),
      g1 g2 g3 ↦ match g1 [
        | false. ↦ refl (false. : Bool)
        | true. ↦ refl (two_element_monoid_mul g2 g3) ]))

def two_element_monoid : Monoid ≔ (Bool, true., two_element_monoid_mul, two_element_monoid_laws)

def unit_monoid_laws : MonoidLaws Unit star. (_ _ ↦ star.)
  ≔ (unit_set,
     (g ↦ (match g [ star. ↦ refl (star. : Unit) ], match g [ star. ↦ refl (star. : Unit) ]),
      _ _ _ ↦ refl (star. : Unit)))

def unit_monoid : Monoid ≔ (Unit, star., _ _ ↦ star., unit_monoid_laws)

def monoid_footnote_map (x : Unit) : Bool ≔ false.

def monoid_footnote_map_mul (s s' : Unit)
  : Id Bool (monoid_footnote_map (unit_monoid .mul s s'))
      (two_element_monoid .mul (monoid_footnote_map s) (monoid_footnote_map s'))
  ≔ refl (false. : Bool)

def monoid_footnote_map_not_unit (p : Id Bool (monoid_footnote_map (unit_monoid .unit)) (two_element_monoid .unit)) : Empty
  ≔ bool_encode false. true. p

{` Hence h is not a monoid homomorphism, and the monoid analogue of
   xca:onlymult-hom is false. `}
def monoid_footnote_map_not_monoid_hom (f : MonoidHom unit_monoid two_element_monoid)
  (p : Id (Unit → Bool) (f .fst) monoid_footnote_map) : Empty
  ≔ monoid_footnote_map_not_unit
      (concat Bool (monoid_footnote_map star.) (f .fst star.) true.
        (inverse Bool (f .fst star.) (monoid_footnote_map star.) (refl ((k ↦ k star.) : (Unit → Bool) → Bool) p))
        (f .snd .fst))

def monoid_mul_preserving_not_unit_preserving
  (h : (M N : Monoid) (f : M .carrier → N .carrier)
    → ((s s' : M .carrier) → Id (N .carrier) (f (M .mul s s')) (N .mul (f s) (f s')))
    → Id (N .carrier) (f (M .unit)) (N .unit))
  : Empty
  ≔ monoid_footnote_map_not_unit (h unit_monoid two_element_monoid monoid_footnote_map monoid_footnote_map_mul)

{` M cannot be extended to an abstract group: an inverse x of 0 gives
   0 = 0 · x = 1; so there is no inverse operation, not even mere
   inverses. `}
def two_element_monoid_zero_inverse (x : Bool) (p : Id Bool (two_element_monoid_mul false. x) true.)
  : Id Bool false. true.
  ≔ p

def two_element_monoid_no_inverse (inv : Bool → Bool) (law : InverseLaw Bool true. two_element_monoid_mul inv) : Empty
  ≔ bool_encode false. true. (two_element_monoid_zero_inverse (inv false.) (law false.))

def two_element_monoid_no_mere_inverses (mi : MereInverses Bool true. two_element_monoid_mul) : Empty
  ≔ mere_rec (BookFiber Bool Bool (two_element_monoid_mul false.) true.) Empty empty_prop
      (u ↦ bool_encode false. true. (inverse Bool true. false. (u .snd))) (mi false.)

def two_element_monoid_not_abstract_group (G : AbstractGroup)
  (p : Id Monoid (abstract_group_monoid G) two_element_monoid) : Empty
  ≔ two_element_monoid_no_mere_inverses
      (transport Monoid MonoidMereInverses (abstract_group_monoid G) two_element_monoid p
        (inverse_operation_mere_inverses (G .carrier) (G .unit) (G .mul) (G .inv) (G .laws .inv_right)))

{` rem:monoid-hom: the homomorphisms of monoids form a set. `}
def monoid_hom_set (M N : Monoid) : isSet (MonoidHom M N)
  ≔ let S ≔ M .carrier in let T ≔ N .carrier in let hT ≔ monoid_set N in
    sigma_set (S → T) (f ↦ Product (Id T (f (M .unit)) (N .unit)) ((s s' : S) → Id T (f (M .mul s s')) (N .mul (f s) (f s'))))
      (pi_set S (_ ↦ T) (_ ↦ hT))
      (f ↦ prop_is_set (Product (Id T (f (M .unit)) (N .unit)) ((s s' : S) → Id T (f (M .mul s s')) (N .mul (f s) (f s'))))
        (product_prop (Id T (f (M .unit)) (N .unit)) ((s s' : S) → Id T (f (M .mul s s')) (N .mul (f s) (f s')))
          (hT (f (M .unit)) (N .unit))
          (pi_prop S (s ↦ (s' : S) → Id T (f (M .mul s s')) (N .mul (f s) (f s')))
            (s ↦ pi_prop S (s' ↦ Id T (f (M .mul s s')) (N .mul (f s) (f s')))
              (s' ↦ hT (f (M .mul s s')) (N .mul (f s) (f s')))))))

{` Litmus for MonoidHom: the unit map 1 → M, * ↦ 1, is a monoid
   homomorphism. `}
def unit_monoid_hom_to_two : MonoidHom unit_monoid two_element_monoid
  ≔ (_ ↦ true., (refl (true. : Bool), _ _ ↦ refl (true. : Bool)))

{` Litmus for xca:onlymult-hom, xca:abshomcomposition and rem:monoid-hom:
   in an abelian group inversion preserves multiplication; for the
   integers this is negation, whose values, unit and inverse equations and
   self-composition are computed. `}
def abelian_inverse_hom (G : AbstractGroup) (hab : IsAbstractAbelian G) : AbstractHom G G
  ≔ (G .inv, s s' ↦ concat (G .carrier) (G .inv (G .mul s s')) (G .mul (G .inv s') (G .inv s)) (G .mul (G .inv s) (G .inv s'))
       (ag_inv_mul G s s') (hab (G .inv s') (G .inv s)))

def int_add_abelian : IsAbstractAbelian int_add_abstract_group ≔ x y ↦ int_add_comm x y

def int_negation_hom : AbstractHom int_add_abstract_group int_add_abstract_group
  ≔ abelian_inverse_hom int_add_abstract_group int_add_abelian

def int_negation_hom_litmus
  : Id Int (int_negation_hom .fst (pos. (suc. (suc. zero.)))) (neg. (suc. zero.))
  ≔ refl (neg. (suc. zero.) : Int)

def int_negation_preserves_unit
  : Id Int (int_negation_hom .fst int_zero) int_zero
  ≔ abstract_hom_preserves_unit int_add_abstract_group int_add_abstract_group (int_negation_hom .fst) (int_negation_hom .snd)

def int_negation_preserves_inv (s : Int)
  : Id Int (int_negation_hom .fst (int_neg s)) (int_neg (int_negation_hom .fst s))
  ≔ abstract_hom_preserves_inv int_add_abstract_group int_add_abstract_group (int_negation_hom .fst) (int_negation_hom .snd) s

def int_negation_twice_litmus
  : Id Int (abstract_hom_compose int_add_abstract_group int_add_abstract_group int_add_abstract_group
        int_negation_hom int_negation_hom .fst (neg. (suc. (suc. zero.))))
      (neg. (suc. (suc. zero.)))
  ≔ refl (neg. (suc. (suc. zero.)) : Int)

def int_negation_twice_identity
  : Id (AbstractHom int_add_abstract_group int_add_abstract_group)
      (abstract_endo_monoid int_add_abstract_group .mul int_negation_hom int_negation_hom)
      (abstract_endo_monoid int_add_abstract_group .unit)
  ≔ abstract_hom_ext int_add_abstract_group int_add_abstract_group
      (abstract_endo_monoid int_add_abstract_group .mul int_negation_hom int_negation_hom)
      (abstract_hom_id int_add_abstract_group) int_neg_neg

def int_negation_monoid_hom_unit
  : Id Int (abstract_hom_monoid_hom int_add_abstract_group int_add_abstract_group int_negation_hom .fst (pos. (suc. zero.)))
      (neg. zero.)
  ≔ refl (neg. zero. : Int)

{` Litmus: Hom(G, G) is a monoid with unit id_G and product f₁ ∘ f₀
   (both by computation). `}
def group_endo_monoid_unit_litmus (G : Group) : Id (GroupHom G G) (group_endo_monoid G .unit) (group_hom_id G)
  ≔ refl (group_hom_id G)

def group_endo_monoid_mul_litmus (G : Group) (f1 f0 : GroupHom G G)
  : Id (GroupHom G G) (group_endo_monoid G .mul f1 f0) (group_hom_compose G G G f0 f1)
  ≔ refl (group_hom_compose G G G f0 f1)
