export "417-cyclic-groups"
export "407-group-family-products"

{` Chapter 4, ex:productofgroups, xca:klein-not-cyclic, ex:bigproductofgroups,
   xca:bigproductfunext, def:abgp and exer:first examples (group.tex 665-757). `}

{` ex:productofgroups, footnote: B(G × H) ≡ BG × BH pointed at (sh_G, sh_H). `}
def product_group_classifying (G H : Group)
  : Id Pointed (BG (product_group G H)) (Product (BG G .carrier) (BG H .carrier), (shape G, shape H))
  ≔ refl (BG (product_group G H))

{` Symmetries of products are pairs of symmetries; composition is componentwise. `}
def product_group_mul_fst (G H : Group) (g h : USym (product_group G H))
  : Id (USym G) (usym_mul (product_group G H) g h .fst) (usym_mul G (g .fst) (h .fst))
  ≔ map_path_concat (Product (BG G .carrier) (BG H .carrier)) (BG G .carrier) (u ↦ u .fst)
      (shape G, shape H) (shape G, shape H) (shape G, shape H) h g

def product_group_mul_snd (G H : Group) (g h : USym (product_group G H))
  : Id (USym H) (usym_mul (product_group G H) g h .snd) (usym_mul H (g .snd) (h .snd))
  ≔ map_path_concat (Product (BG G .carrier) (BG H .carrier)) (BG H .carrier) (u ↦ u .snd)
      (shape G, shape H) (shape G, shape H) (shape G, shape H) h g

def product_symmetries_ext (G H : Group) (g h : USym (product_group G H))
  (p : Id (USym G) (g .fst) (h .fst)) (q : Id (USym H) (g .snd) (h .snd)) : Id (USym (product_group G H)) g h
  ≔ equivalence_injective (USym (product_group G H)) (Product (USym G) (USym H)) (product_group_usym_equiv G H) g h (p, q)

{` The Klein four-group Σ_2 × Σ_2 has four symmetries. `}
def klein_four_group : Group ≔ product_group (symmetric_group two) (symmetric_group two)

def klein_usym_equiv : Equiv (USym klein_four_group) (Fin (mul two two))
  ≔ compose_equiv (USym klein_four_group) (Product (USym (symmetric_group two)) (USym (symmetric_group two)))
      (Fin (mul two two)) (product_group_usym_equiv (symmetric_group two) (symmetric_group two))
      (compose_equiv (Product (USym (symmetric_group two)) (USym (symmetric_group two))) (Product (Fin two) (Fin two))
        (Fin (mul two two))
        (product_equiv (USym (symmetric_group two)) (USym (symmetric_group two)) (Fin two) (Fin two)
          sigma2_usym_equiv sigma2_usym_equiv)
        (fin_product_equiv two two))

def klein_finite : IsFiniteGroup klein_four_group
  ≔ mere (Σ Nat (k ↦ Id Type (USym klein_four_group) (Fin k)))
      (mul two two, ua (USym klein_four_group) (Fin (mul two two)) klein_usym_equiv)

def klein_card : Id Nat (group_card klein_four_group klein_finite) (suc. (suc. (suc. (suc. zero.))))
  ≔ cardinality_from_path (USym klein_four_group) klein_finite (mul two two)
      (ua (USym klein_four_group) (Fin (mul two two)) klein_usym_equiv)

{` xca:klein-not-cyclic. Every symmetry of the Klein four-group squares to
   the identity, while the generator of C_4 does not; this property transports
   along identifications of groups. `}
def ExponentTwo (G : Group) : Type ≔ (g : USym G) → Id (USym G) (usym_mul G g g) (usym_unit G)

def unit_square (G : Group) : Id (USym G) (usym_mul G (usym_unit G) (usym_unit G)) (usym_unit G)
  ≔ concat_p1 (BG G .carrier) (shape G) (shape G) (refl (shape G))

def sigma2_exponent_two : ExponentTwo (symmetric_group two)
  ≔ g ↦ match sigma2_cases g [
  | inl. p ↦ transport (USym (symmetric_group two))
      (x ↦ Id (USym (symmetric_group two)) (usym_mul (symmetric_group two) x x) (usym_unit (symmetric_group two)))
      (usym_unit (symmetric_group two)) g (inverse (USym (symmetric_group two)) g (usym_unit (symmetric_group two)) p)
      (unit_square (symmetric_group two))
  | inr. p ↦ transport (USym (symmetric_group two))
      (x ↦ Id (USym (symmetric_group two)) (usym_mul (symmetric_group two) x x) (usym_unit (symmetric_group two)))
      sigma2_swap g (inverse (USym (symmetric_group two)) g sigma2_swap p) sigma2_swap_squared ]

def product_exponent_two (G H : Group) (hG : ExponentTwo G) (hH : ExponentTwo H) : ExponentTwo (product_group G H)
  ≔ g ↦ product_symmetries_ext G H (usym_mul (product_group G H) g g) (usym_unit (product_group G H))
      (concat (USym G) (usym_mul (product_group G H) g g .fst) (usym_mul G (g .fst) (g .fst)) (usym_unit G)
        (product_group_mul_fst G H g g) (hG (g .fst)))
      (concat (USym H) (usym_mul (product_group G H) g g .snd) (usym_mul H (g .snd) (g .snd)) (usym_unit H)
        (product_group_mul_snd G H g g) (hH (g .snd)))

def klein_exponent_two : ExponentTwo klein_four_group
  ≔ product_exponent_two (symmetric_group two) (symmetric_group two) sigma2_exponent_two sigma2_exponent_two

def three_nat : Nat ≔ suc. (suc. (suc. zero.))

def cyclic_four_generator_square_value
  : Id Nat (cyclic_group_eval three_nat
      (usym_mul (cyclic_group (suc. three_nat)) (cycle_group_generator (principal_cycle (suc. three_nat)))
        (cycle_group_generator (principal_cycle (suc. three_nat)))) .fst) (suc. (suc. zero.))
  ≔ let g ≔ cycle_group_generator (principal_cycle (suc. three_nat)) in
    let R ≔ Remainder (suc. three_nat) in
    refl ((r ↦ r .fst) : R → Nat)
      (concat R (cyclic_group_eval three_nat (usym_mul (cyclic_group (suc. three_nat)) g g))
        (modular_add three_nat (cyclic_group_eval three_nat g) (cyclic_group_eval three_nat g))
        (modular_add three_nat (modular_successor three_nat (modular_zero three_nat))
          (modular_successor three_nat (modular_zero three_nat)))
        (cyclic_group_eval_mul three_nat g g)
        (refl ((r ↦ modular_add three_nat r r) : R → R) (cyclic_group_eval_generator three_nat)))

def cyclic_four_not_exponent_two (h : ExponentTwo (cyclic_group (suc. three_nat))) : Empty
  ≔ let g ≔ cycle_group_generator (principal_cycle (suc. three_nat)) in
    let G ≔ cyclic_group (suc. three_nat) in
    nat_encode (suc. (suc. zero.)) zero.
      (calc
        (suc. (suc. zero.) : Nat) = cyclic_group_eval three_nat (usym_mul G g g) .fst
          by inverse Nat (cyclic_group_eval three_nat (usym_mul G g g) .fst) (suc. (suc. zero.))
            cyclic_four_generator_square_value
        = cyclic_group_eval three_nat (usym_unit G) .fst
          by refl ((x ↦ cyclic_group_eval three_nat x .fst) : USym G → Nat) (h g)
        = (zero. : Nat)
          by refl ((r ↦ r .fst) : Remainder (suc. three_nat) → Nat) (cyclic_group_eval_unit three_nat) ∎)

def klein_not_cyclic (p : Id Group (cyclic_group_fin three_nat) klein_four_group) : Empty
  ≔ cyclic_four_not_exponent_two
      (transport Group ExponentTwo klein_four_group (cyclic_group (suc. three_nat))
        (inverse Group (cyclic_group (suc. three_nat)) klein_four_group
          (concat Group (cyclic_group (suc. three_nat)) (cyclic_group_fin three_nat) klein_four_group
            (inverse Group (cyclic_group_fin three_nat) (cyclic_group (suc. three_nat)) (cyclic_group_fin_path three_nat))
            p))
        klein_exponent_two)

{` xca:bigproductfunext (ii): for S = Bool the product of a family is the
   binary product, by the pointed equivalence f ↦ (f(false), f(true)). `}
def bool_finite : IsFinite Bool
  ≔ finite_of_equiv Bool (Fin two) (canonical_inverse_equiv (Fin two) Bool fin_two_equiv) (fin_is_finite two)

def bool_family_pair (G : Bool → Group) (f : (b : Bool) → BG (G b) .carrier)
  : Product (BG (G false.) .carrier) (BG (G true.) .carrier)
  ≔ (f false., f true.)

def bool_family_unpair (G : Bool → Group) (u : Product (BG (G false.) .carrier) (BG (G true.) .carrier))
  : (b : Bool) → BG (G b) .carrier
  ≔ [ false. ↦ u .fst | true. ↦ u .snd ]

def bool_family_product_path (G : Bool → Group)
  : Id Group (family_product_group Bool bool_finite G) (product_group (G false.) (G true.))
  ≔ let A ≔ (b : Bool) → BG (G b) .carrier in
    let P ≔ Product (BG (G false.) .carrier) (BG (G true.) .carrier) in
    group_path_from_pointed_equiv (family_product_group Bool bool_finite G) (product_group (G false.) (G true.))
      ((bool_family_pair G, refl (shape (G false.), shape (G true.))),
       book_quasi_inverse_equiv A P (bool_family_pair G) (bool_family_unpair G)
         (f ↦ funext Bool (b ↦ BG (G b) .carrier) (bool_family_unpair G (bool_family_pair G f)) f
           [ false. ↦ refl (f false.) | true. ↦ refl (f true.) ])
         (u ↦ refl u) .equiv)

{` xca:bigproductfunext, footnote: for an arbitrary (possibly infinite)
   family, the component of the base point s ↦ sh_{G(s)} in Π_s BG(s) is a
   pointed connected groupoid; for finite S it is the product of
   ex:bigproductofgroups (rem:symmetriesofnonconnectedgroupoids). `}
def component_product_group (S : Type) (G : S → Group) : Group
  ≔ automorphism_group ((s : S) → BG (G s) .carrier) (groupoid_pi S (s ↦ BG (G s) .carrier) (s ↦ bg_groupoid (G s)))
      (s ↦ shape (G s))

def component_product_usym_equiv (S : Type) (G : S → Group)
  : Equiv (USym (component_product_group S G)) ((s : S) → USym (G s))
  ≔ compose_equiv (USym (component_product_group S G))
      (Id ((s : S) → BG (G s) .carrier) (s ↦ shape (G s)) (s ↦ shape (G s))) ((s : S) → USym (G s))
      (automorphism_group_usym_equiv ((s : S) → BG (G s) .carrier)
        (groupoid_pi S (s ↦ BG (G s) .carrier) (s ↦ bg_groupoid (G s))) (s ↦ shape (G s)))
      (function_extensionality S (s ↦ BG (G s) .carrier) (s ↦ shape (G s)) (s ↦ shape (G s)))

def family_product_component_path (S : Type) (hS : IsFinite S) (G : S → Group)
  : Id Group (family_product_group S hS G) (component_product_group S G)
  ≔ pcg_automorphism_path (family_product_group S hS G .classifying)

{` def:abgp, preceding prose: Z is abelian (loops of the circle commute;
   loopⁿ loopᵐ = loop^{n+m} = loop^{m+n} = loopᵐ loopⁿ, circle_power_mul). `}
def circle_group_is_abelian (C : CircleSignature) : IsAbelian (circle_group C)
  ≔ g h ↦ circle_loops_commute C h g

{` exer:first examples: Σ_2 is abelian (sigma2_abelian, module 412), Σ_3 is
   not (symmetric_group_three_not_abelian, module 406), and products of
   abelian groups are abelian. `}
def product_abelian (G H : Group) (hG : IsAbelian G) (hH : IsAbelian H) : IsAbelian (product_group G H)
  ≔ g h ↦ product_symmetries_ext G H (usym_mul (product_group G H) g h) (usym_mul (product_group G H) h g)
      (calc
        usym_mul (product_group G H) g h .fst = usym_mul G (g .fst) (h .fst) by product_group_mul_fst G H g h
        = usym_mul G (h .fst) (g .fst) by hG (g .fst) (h .fst)
        = usym_mul (product_group G H) h g .fst
          by inverse (USym G) (usym_mul (product_group G H) h g .fst) (usym_mul G (h .fst) (g .fst))
            (product_group_mul_fst G H h g) ∎)
      (calc
        usym_mul (product_group G H) g h .snd = usym_mul H (g .snd) (h .snd) by product_group_mul_snd G H g h
        = usym_mul H (h .snd) (g .snd) by hH (g .snd) (h .snd)
        = usym_mul (product_group G H) h g .snd
          by inverse (USym H) (usym_mul (product_group G H) h g .snd) (usym_mul H (h .snd) (g .snd))
            (product_group_mul_snd G H h g) ∎)

def klein_abelian : IsAbelian klein_four_group
  ≔ product_abelian (symmetric_group two) (symmetric_group two) sigma2_abelian sigma2_abelian
