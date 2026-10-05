export "406-symmetric-group-three"
export "127-symmetries-of-circle"
export "420-group-products-abelian"

{` Chapter 12 (abelian.tex), basic structure of the type of abelian groups.
   The definitions IsAbelian and AbelianGroup ≔ Σ Group IsAbelian are those of
   chapter 4 (def:abgp, module 400); this module adds accessors, identity
   types, and litmus examples. Book products are written in the book's
   order: usym_mul G g h = g·h = concat h g. `}

def abgroup_group (A : AbelianGroup) : Group ≔ A .fst

def abgroup_commutes (A : AbelianGroup) : IsAbelian (A .fst) ≔ A .snd

def mk_abelian_group (G : Group) (h : IsAbelian G) : AbelianGroup ≔ (G, h)

{` Identifications of abelian groups are identifications of the underlying
   groups (IsAbelian is a proposition). `}
def abelian_group_path_equiv (A B : AbelianGroup)
  : Equiv (Id AbelianGroup A B) (Id Group (A .fst) (B .fst))
  ≔ subtype_path_equiv Group IsAbelian is_abelian_prop A B

def abelian_group_path (A B : AbelianGroup) (p : Id Group (A .fst) (B .fst)) : Id AbelianGroup A B
  ≔ subtype_equal Group IsAbelian is_abelian_prop A B p

def abelian_group_groupoid : isGroupoid AbelianGroup
  ≔ hlevel_to_groupoid AbelianGroup
      (subtype_hlevel (suc. (suc. zero.)) Group IsAbelian (groupoid_to_hlevel Group group_groupoid) is_abelian_prop)

{` Abelianness is invariant under identifications of groups. `}
def abelian_transport (G H : Group) (p : Id Group G H) (h : IsAbelian G) : IsAbelian H
  ≔ transport Group IsAbelian G H p h

{` Litmus: groups whose symmetries form a contractible type are abelian. `}
def contractible_usym_abelian (G : Group) (h : BookIsContr (USym G)) : IsAbelian G
  ≔ g k ↦ contractible_prop (USym G) (native_contraction (USym G) h) (usym_mul G g k) (usym_mul G k g)

def unit_group_abelian : IsAbelian unit_group ≔ contractible_usym_abelian unit_group unit_group_usym_contractible

def trivial_group_abelian : IsAbelian trivial_group
  ≔ contractible_usym_abelian trivial_group trivial_group_usym_contractible

{` Litmus: Z (the circle group of any circle) is abelian, from cor:S1groupoid
   (circle_group_is_abelian of module 420). `}
def circle_group_abelian (C : CircleSignature) : IsAbelian (circle_group C)
  ≔ circle_group_is_abelian C

def circle_abelian_group (C : CircleSignature) : AbelianGroup ≔ (circle_group C, circle_group_abelian C)

{` Litmus: Σ₃ is not abelian (module 406), so it does not underlie an abelian group. `}
def sigma3_no_abelian_structure (A : AbelianGroup) (p : Id Group (A .fst) (symmetric_group three)) : Empty
  ≔ symmetric_group_three_not_abelian (abelian_transport (A .fst) (symmetric_group three) p (A .snd))

{` Products (aliases of chapter 4, module 420): the projections of a product
   of symmetries are the products of the projections, and symmetries of a
   product are determined by their projections. `}
def product_usym_mul_fst (G H : Group) (g k : USym (product_group G H))
  : Id (USym G) (usym_mul (product_group G H) g k .fst) (usym_mul G (g .fst) (k .fst))
  ≔ product_group_mul_fst G H g k

def product_usym_mul_snd (G H : Group) (g k : USym (product_group G H))
  : Id (USym H) (usym_mul (product_group G H) g k .snd) (usym_mul H (g .snd) (k .snd))
  ≔ product_group_mul_snd G H g k

def product_usym_path (G H : Group) (r s : USym (product_group G H))
  (p : Id (USym G) (r .fst) (s .fst)) (q : Id (USym H) (r .snd) (s .snd)) : Id (USym (product_group G H)) r s
  ≔ product_symmetries_ext G H r s p q

{` Litmus: a product of abelian groups is abelian (exer:first examples,
   product_abelian of module 420). This is the direct sum G ⊕ H of
   sec:direct-sums (module 1221). `}
def product_group_abelian (G H : Group) (hG : IsAbelian G) (hH : IsAbelian H) : IsAbelian (product_group G H)
  ≔ product_abelian G H hG hH

def abelian_product (A B : AbelianGroup) : AbelianGroup
  ≔ (product_group (A .fst) (B .fst), product_group_abelian (A .fst) (B .fst) (A .snd) (B .snd))

{` Litmus: Z × Z is abelian. `}
def circle_square_abelian_group (C : CircleSignature) : AbelianGroup
  ≔ abelian_product (circle_abelian_group C) (circle_abelian_group C)

{` Litmus: Σ₃ × 1 is not abelian, so the converse of product_group_abelian
   needs both factors. `}
def product_abelian_left (G H : Group) (h : IsAbelian (product_group G H)) : IsAbelian G
  ≔ g k ↦
    let e ≔ product_group_usym_equiv G H in
    let gg ≔ equiv_inverse_map (USym (product_group G H)) (Product (USym G) (USym H)) e (g, usym_unit H) in
    let kk ≔ equiv_inverse_map (USym (product_group G H)) (Product (USym G) (USym H)) e (k, usym_unit H) in
    calc
      usym_mul G g k = usym_mul G (gg .fst) (kk .fst) by refl (usym_mul G g k)
      = usym_mul (product_group G H) gg kk .fst
        by inverse (USym G) (usym_mul (product_group G H) gg kk .fst) (usym_mul G (gg .fst) (kk .fst))
          (product_usym_mul_fst G H gg kk)
      = usym_mul (product_group G H) kk gg .fst by refl ((r ↦ r .fst) : USym (product_group G H) → USym G) (h gg kk)
      = usym_mul G (kk .fst) (gg .fst) by product_usym_mul_fst G H kk gg
      = usym_mul G k g by refl (usym_mul G k g) ∎

def sigma3_unit_not_abelian (h : IsAbelian (product_group (symmetric_group three) unit_group)) : Empty
  ≔ symmetric_group_three_not_abelian (product_abelian_left (symmetric_group three) unit_group h)
