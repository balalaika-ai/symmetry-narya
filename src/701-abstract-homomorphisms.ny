export "700-monoids-and-group-laws"

{` Chapter 7 (absgroup.tex), sec:abshom. Abstract homomorphisms
   (def:abstrisfunctor: IsAbstractHom, AbstractHom and abstr_hom are in
   module 403), xca:onlymult-hom, the footnote to def:abstrisfunctor
   (homomorphisms are determined by their underlying functions),
   rem:monoid-hom, xca:abshomcomposition, and isomorphisms of abstract
   groups (rem:abs-iso). `}

{` xca:onlymult-hom. A function preserving multiplication preserves the
   unit and inverses. `}
def abstract_hom_preserves_unit (G H : AbstractGroup) (f : G .carrier → H .carrier) (hf : IsAbstractHom G H f)
  : Id (H .carrier) (f (G .unit)) (H .unit)
  ≔ let T ≔ H .carrier in let e ≔ G .unit in
    ag_idempotent_unit H (f e)
      (concat T (H .mul (f e) (f e)) (f (G .mul e e)) (f e)
        (inverse T (f (G .mul e e)) (H .mul (f e) (f e)) (hf e e))
        (refl f (G .laws .unit_right e)))

def abstract_hom_preserves_inv (G H : AbstractGroup) (f : G .carrier → H .carrier) (hf : IsAbstractHom G H f)
  (s : G .carrier)
  : Id (H .carrier) (f (G .inv s)) (H .inv (f s))
  ≔ let T ≔ H .carrier in let is ≔ G .inv s in
    ag_inv_unique_right H (f s) (f is)
      (concat T (H .mul (f s) (f is)) (f (G .mul s is)) (H .unit)
        (inverse T (f (G .mul s is)) (H .mul (f s) (f is)) (hf s is))
        (concat T (f (G .mul s is)) (f (G .unit)) (H .unit)
          (refl f (G .laws .inv_right s)) (abstract_hom_preserves_unit G H f hf)))

{` Footnote to def:abstrisfunctor: absHom(G, H) is a set, and a
   homomorphism is determined by its underlying function. `}
def abstract_hom_set (G H : AbstractGroup) : isSet (AbstractHom G H)
  ≔ sigma_set (G .carrier → H .carrier) (IsAbstractHom G H)
      (pi_set (G .carrier) (_ ↦ H .carrier) (_ ↦ abstract_group_set H))
      (f ↦ prop_is_set (IsAbstractHom G H f) (is_abstract_hom_prop G H f))

def abstract_hom_fun_path_equiv (G H : AbstractGroup) (φ ψ : AbstractHom G H)
  : Equiv (Id (AbstractHom G H) φ ψ) (Id (G .carrier → H .carrier) (φ .fst) (ψ .fst))
  ≔ subtype_path_equiv (G .carrier → H .carrier) (IsAbstractHom G H) (is_abstract_hom_prop G H) φ ψ

def abstract_hom_ext (G H : AbstractGroup) (φ ψ : AbstractHom G H)
  (h : (s : G .carrier) → Id (H .carrier) (φ .fst s) (ψ .fst s))
  : Id (AbstractHom G H) φ ψ
  ≔ subtype_equal (G .carrier → H .carrier) (IsAbstractHom G H) (is_abstract_hom_prop G H) φ ψ
      (funext (G .carrier) (_ ↦ H .carrier) (φ .fst) (ψ .fst) h)

{` xca:abshomcomposition. Identity and composition; abstract_hom_compose
   G H K φ ψ is ψ ∘ φ (φ first, as group_hom_compose). `}
def abstract_hom_id (G : AbstractGroup) : AbstractHom G G
  ≔ (x ↦ x, s s' ↦ refl (G .mul s s'))

def abstract_hom_compose (G H K : AbstractGroup) (φ : AbstractHom G H) (ψ : AbstractHom H K) : AbstractHom G K
  ≔ (x ↦ ψ .fst (φ .fst x),
     s s' ↦ concat (K .carrier) (ψ .fst (φ .fst (G .mul s s'))) (ψ .fst (H .mul (φ .fst s) (φ .fst s')))
       (K .mul (ψ .fst (φ .fst s)) (ψ .fst (φ .fst s')))
       (refl (ψ .fst) (φ .snd s s')) (ψ .snd (φ .fst s) (φ .fst s')))

def abstract_hom_compose_id_left (G H : AbstractGroup) (φ : AbstractHom G H)
  : Id (AbstractHom G H) (abstract_hom_compose G G H (abstract_hom_id G) φ) φ
  ≔ abstract_hom_ext G H (abstract_hom_compose G G H (abstract_hom_id G) φ) φ (s ↦ refl (φ .fst s))

def abstract_hom_compose_id_right (G H : AbstractGroup) (φ : AbstractHom G H)
  : Id (AbstractHom G H) (abstract_hom_compose G H H φ (abstract_hom_id H)) φ
  ≔ abstract_hom_ext G H (abstract_hom_compose G H H φ (abstract_hom_id H)) φ (s ↦ refl (φ .fst s))

def abstract_hom_compose_assoc (G H K L : AbstractGroup) (φ : AbstractHom G H) (ψ : AbstractHom H K)
  (χ : AbstractHom K L)
  : Id (AbstractHom G L) (abstract_hom_compose G K L (abstract_hom_compose G H K φ ψ) χ)
      (abstract_hom_compose G H L φ (abstract_hom_compose H K L ψ χ))
  ≔ abstract_hom_ext G L (abstract_hom_compose G K L (abstract_hom_compose G H K φ ψ) χ)
      (abstract_hom_compose G H L φ (abstract_hom_compose H K L ψ χ)) (s ↦ refl (χ .fst (ψ .fst (φ .fst s))))

{` xca:abshomcomposition: abstr(id_G) = id_abstr(G) and
   abstr(f₁ f₀) = abstr(f₁) abstr(f₀). `}
def abstr_hom_id (G : Group)
  : Id (AbstractHom (abstr G) (abstr G)) (abstr_hom G G (group_hom_id G)) (abstract_hom_id (abstr G))
  ≔ abstract_hom_ext (abstr G) (abstr G) (abstr_hom G G (group_hom_id G)) (abstract_hom_id (abstr G))
      (usym_hom_id G)

def abstr_hom_compose (G0 G1 G2 : Group) (f0 : GroupHom G0 G1) (f1 : GroupHom G1 G2)
  : Id (AbstractHom (abstr G0) (abstr G2)) (abstr_hom G0 G2 (group_hom_compose G0 G1 G2 f0 f1))
      (abstract_hom_compose (abstr G0) (abstr G1) (abstr G2) (abstr_hom G0 G1 f0) (abstr_hom G1 G2 f1))
  ≔ abstract_hom_ext (abstr G0) (abstr G2) (abstr_hom G0 G2 (group_hom_compose G0 G1 G2 f0 f1))
      (abstract_hom_compose (abstr G0) (abstr G1) (abstr G2) (abstr_hom G0 G1 f0) (abstr_hom G1 G2 f1))
      (loops_map_compose_pointwise (BG G0) (BG G1) (BG G2) (hom_B G0 G1 f0) (hom_B G1 G2 f1))

{` xca:abshomcomposition: Hom(G, G) and absHom(G, G) are monoids under
   composition (the product f₁ · f₀ is f₁ ∘ f₀). `}
def group_endo_monoid (G : Group) : Monoid
  ≔ (GroupHom G G, group_hom_id G, f1 f0 ↦ group_hom_compose G G G f0 f1,
     (group_hom_set G G,
      (f ↦ (group_hom_id_compose G G f, group_hom_compose_id G G f),
       f1 f2 f3 ↦ group_hom_compose_assoc G G G G f3 f2 f1)))

def abstract_endo_monoid (G : AbstractGroup) : Monoid
  ≔ (AbstractHom G G, abstract_hom_id G, φ1 φ0 ↦ abstract_hom_compose G G G φ0 φ1,
     (abstract_hom_set G G,
      (φ ↦ (abstract_hom_compose_id_left G G φ, abstract_hom_compose_id_right G G φ),
       φ1 φ2 φ3 ↦ abstract_hom_compose_assoc G G G G φ3 φ2 φ1)))

{` abstr : Hom(G, G) → absHom(abstr G, abstr G) preserves the monoid
   structures. `}
def abstr_hom_endo_unit (G : Group)
  : Id (AbstractHom (abstr G) (abstr G)) (abstr_hom G G (group_endo_monoid G .unit)) (abstract_endo_monoid (abstr G) .unit)
  ≔ abstr_hom_id G

def abstr_hom_endo_mul (G : Group) (f1 f0 : GroupHom G G)
  : Id (AbstractHom (abstr G) (abstr G)) (abstr_hom G G (group_endo_monoid G .mul f1 f0))
      (abstract_endo_monoid (abstr G) .mul (abstr_hom G G f1) (abstr_hom G G f0))
  ≔ abstr_hom_compose G G G f0 f1

{` rem:monoid-hom. Homomorphisms of monoids preserve the unit and the
   multiplication. `}
def MonoidHom (M N : Monoid) : Type
  ≔ Σ (M .carrier → N .carrier) (f ↦
      Product (Id (N .carrier) (f (M .unit)) (N .unit))
        ((s s' : M .carrier) → Id (N .carrier) (f (M .mul s s')) (N .mul (f s) (f s'))))

{` rem:monoid-hom: an abstract homomorphism is a homomorphism of the
   underlying monoids. `}
def abstract_hom_monoid_hom (G H : AbstractGroup) (φ : AbstractHom G H)
  : MonoidHom (abstract_group_monoid G) (abstract_group_monoid H)
  ≔ (φ .fst, (abstract_hom_preserves_unit G H (φ .fst) (φ .snd), φ .snd))

{` rem:abs-iso. An isomorphism of abstract groups is an equivalence of
   the underlying sets preserving multiplication (by xca:onlymult-hom it
   then preserves the unit; abstract_iso_equations_equiv adds the unit
   equation as printed). `}
def AbstractIso (G H : AbstractGroup) : Type
  ≔ Σ (Equiv (G .carrier) (H .carrier)) (f ↦ IsAbstractHom G H (f .map))

def abstract_iso_hom (G H : AbstractGroup) (φ : AbstractIso G H) : AbstractHom G H ≔ (φ .fst .map, φ .snd)

def AbstractIsoEquations (G H : AbstractGroup) : Type
  ≔ Σ (Equiv (G .carrier) (H .carrier)) (f ↦
      Product (Id (H .carrier) (H .unit) (f .map (G .unit)))
        ((s t : G .carrier) → Id (H .carrier) (H .mul (f .map s) (f .map t)) (f .map (G .mul s t))))

def abstract_iso_equations_equiv (G H : AbstractGroup) : Equiv (AbstractIso G H) (AbstractIsoEquations G H)
  ≔ let S ≔ G .carrier in let T ≔ H .carrier in
    family_equiv (Equiv S T) (f ↦ IsAbstractHom G H (f .map))
      (f ↦ Product (Id T (H .unit) (f .map (G .unit)))
        ((s t : S) → Id T (H .mul (f .map s) (f .map t)) (f .map (G .mul s t))))
      (f ↦ iff_equiv (IsAbstractHom G H (f .map))
        (Product (Id T (H .unit) (f .map (G .unit))) ((s t : S) → Id T (H .mul (f .map s) (f .map t)) (f .map (G .mul s t))))
        (is_abstract_hom_prop G H (f .map))
        (product_prop (Id T (H .unit) (f .map (G .unit)))
          ((s t : S) → Id T (H .mul (f .map s) (f .map t)) (f .map (G .mul s t)))
          (abstract_group_set H (H .unit) (f .map (G .unit)))
          (pi_prop S (s ↦ (t : S) → Id T (H .mul (f .map s) (f .map t)) (f .map (G .mul s t)))
            (s ↦ pi_prop S (t ↦ Id T (H .mul (f .map s) (f .map t)) (f .map (G .mul s t)))
              (t ↦ abstract_group_set H (H .mul (f .map s) (f .map t)) (f .map (G .mul s t))))))
        (h ↦ (inverse T (f .map (G .unit)) (H .unit) (abstract_hom_preserves_unit G H (f .map) h),
              s t ↦ inverse T (f .map (G .mul s t)) (H .mul (f .map s) (f .map t)) (h s t)))
        (u ↦ s t ↦ inverse T (H .mul (f .map s) (f .map t)) (f .map (G .mul s t)) (u .snd s t)))

def abstract_iso_id (G : AbstractGroup) : AbstractIso G G
  ≔ (identity_equiv (G .carrier), s s' ↦ refl (G .mul s s'))

def abstract_iso_compose (G H K : AbstractGroup) (φ : AbstractIso G H) (ψ : AbstractIso H K) : AbstractIso G K
  ≔ (compose_equiv (G .carrier) (H .carrier) (K .carrier) (φ .fst) (ψ .fst),
     abstract_hom_compose G H K (abstract_iso_hom G H φ) (abstract_iso_hom H K ψ) .snd)

{` The inverse of an isomorphism is an isomorphism. `}
def abstract_iso_inverse (G H : AbstractGroup) (φ : AbstractIso G H) : AbstractIso H G
  ≔ let S ≔ G .carrier in let T ≔ H .carrier in let f ≔ φ .fst in
    let g ≔ equiv_inverse_map S T f in
    (canonical_inverse_equiv S T f,
     t t' ↦ equivalence_injective S T f (g (H .mul t t')) (G .mul (g t) (g t'))
       (calc
          f .map (g (H .mul t t')) = H .mul t t' by equiv_counit S T f (H .mul t t')
          = H .mul (f .map (g t)) (f .map (g t'))
            by inverse T (H .mul (f .map (g t)) (f .map (g t'))) (H .mul t t')
              (refl (H .mul) (equiv_counit S T f t) (equiv_counit S T f t'))
          = f .map (G .mul (g t) (g t'))
            by inverse T (f .map (G .mul (g t) (g t'))) (H .mul (f .map (g t)) (f .map (g t'))) (φ .snd (g t) (g t')) ∎))
