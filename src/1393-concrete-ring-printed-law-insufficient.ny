export "1350-concrete-rings"
export "486-universe-not-groupoid"
export "431-homomorphism-remarks"

{` Chapter 13, def:ring (fields.tex 1143): the book prints only one unit law ("ev ∘ USym(μ ∘ 1_R)(loop) = B id_R,
   ≈ TBD"); the other unit law and the associative law are TBD. This module shows that the printed data and law
   do not suffice for xca:Rconcring->URabstring, which is why module 1350 completes the laws: for R = ℤ × ℤ,
   1_R = the first inclusion and μ = (Hom(ℤ, Hom(R, R)) at the symmetry of id_R) ∘ (first projection), the
   printed unit law holds but a · 1 ≠ a for a = (refl, loop) (a · b ≔ USym(ev ∘ USym μ (a))(b)). `}

{` Generic: if ev turns products into pointwise products, ev(refl) acts trivially. `}
def evaluation_unit_trivial (G H : Group) (ev : USym H → GroupHom G G)
  (hmul : (p q : USym H) (b : USym G)
    → Id (USym G) (usym_hom G G (ev (usym_mul H p q)) b) (usym_mul G (usym_hom G G (ev p) b) (usym_hom G G (ev q) b)))
  (b : USym G) : Id (USym G) (usym_hom G G (ev (usym_unit H)) b) (usym_unit G)
  ≔ let U ≔ USym G in let y ≔ usym_hom G G (ev (usym_unit H)) b in
    ag_idempotent_unit (abstr G) y
      (calc
         usym_mul G y y = usym_hom G G (ev (usym_mul H (usym_unit H) (usym_unit H))) b
           by inverse U (usym_hom G G (ev (usym_mul H (usym_unit H) (usym_unit H))) b) (usym_mul G y y)
             (hmul (usym_unit H) (usym_unit H) b)
         = y by map_path (USym H) U (p ↦ usym_hom G G (ev p) b) (usym_mul H (usym_unit H) (usym_unit H)) (usym_unit H)
             (usym_abstract_laws H .unit_left (usym_unit H)) ∎)

{` Generic: with ev, μ and a with USym μ (a) = refl, a · b = refl for all b. `}
def evaluation_kernel_trivial (G H : Group) (μ : GroupHom G H) (ev : USym H → GroupHom G G)
  (hmul : (p q : USym H) (b : USym G)
    → Id (USym G) (usym_hom G G (ev (usym_mul H p q)) b) (usym_mul G (usym_hom G G (ev p) b) (usym_hom G G (ev q) b)))
  (a : USym G) (ha : Id (USym H) (usym_hom G H μ a) (usym_unit H)) (b : USym G)
  : Id (USym G) (usym_hom G G (ev (usym_hom G H μ a)) b) (usym_unit G)
  ≔ concat (USym G) (usym_hom G G (ev (usym_hom G H μ a)) b) (usym_hom G G (ev (usym_unit H)) b) (usym_unit G)
      (map_path (USym H) (USym G) (p ↦ usym_hom G G (ev p) b) (usym_hom G H μ a) (usym_unit H) ha)
      (evaluation_unit_trivial G H ev hmul b)

{` The data. `}
def ce_group (C : CircleSignature) : AbelianGroup
  ≔ (product_group (circle_group C) (circle_group C),
     product_group_abelian (circle_group C) (circle_group C) (circle_group_abelian C) (circle_group_abelian C))

def ce_hom_group (C : CircleSignature) : Group ≔ abelian_hom_group (ce_group C .fst) (ce_group C)

def ce_one (C : CircleSignature) : GroupHom (circle_group C) (ce_group C .fst)
  ≔ product_group_incl1 (circle_group C) (circle_group C)

def ce_sigma (C : CircleSignature) : USym (ce_hom_group C)
  ≔ equiv_inverse_map (USym (ce_hom_group C)) (GroupHom (ce_group C .fst) (ce_group C .fst))
      (abelian_hom_usym_equiv (ce_group C .fst) (ce_group C)) (group_hom_id (ce_group C .fst))

def ce_mu (C : CircleSignature) : GroupHom (ce_group C .fst) (ce_hom_group C)
  ≔ group_hom_compose (ce_group C .fst) (circle_group C) (ce_hom_group C) (product_group_proj1 (circle_group C) (circle_group C))
      (circle_group_hom_from_symmetry C (ce_hom_group C) (ce_sigma C))

{` USym μ (x) = USym(loop ↦ σ)(x₁). `}
def ce_mu_usym (C : CircleSignature) (x : USym (ce_group C .fst))
  : Id (USym (ce_hom_group C)) (usym_hom (ce_group C .fst) (ce_hom_group C) (ce_mu C) x)
      (usym_hom (circle_group C) (ce_hom_group C) (circle_group_hom_from_symmetry C (ce_hom_group C) (ce_sigma C)) (x .fst))
  ≔ let Z ≔ circle_group C in let R ≔ ce_group C .fst in let H ≔ ce_hom_group C in
    let f ≔ circle_group_hom_from_symmetry C H (ce_sigma C) in
    concat (USym H) (usym_hom R H (ce_mu C) x) (usym_hom Z H f (usym_hom R Z (product_group_proj1 Z Z) x))
      (usym_hom Z H f (x .fst))
      (refl ((φ ↦ φ x) : (USym R → USym H) → USym H) (usym_hom_compose R Z H (product_group_proj1 Z Z) f))
      (map_path (USym Z) (USym H) (usym_hom Z H f) (usym_hom R Z (product_group_proj1 Z Z) x) (x .fst)
        (product_group_proj1_usym Z Z x))

{` Generic form of the printed unit law for μ = f ∘ p with p ∘ 1_R fixing l and f(l) = σ, ev(σ) = id. `}
def printed_unit_law_through (Z R H : Group) (ev : USym H → GroupHom R R) (σ : USym H)
  (hσ : Id (GroupHom R R) (ev σ) (group_hom_id R)) (one : GroupHom Z R) (p : GroupHom R Z) (f : GroupHom Z H)
  (l : USym Z) (hp : Id (USym Z) (usym_hom R Z p (usym_hom Z R one l)) l) (hf : Id (USym H) (usym_hom Z H f l) σ)
  : Id (GroupHom R R) (ev (usym_hom Z H (group_hom_compose Z R H one (group_hom_compose R Z H p f)) l)) (group_hom_id R)
  ≔ let μ ≔ group_hom_compose R Z H p f in
    calc
      ev (usym_hom Z H (group_hom_compose Z R H one μ) l) = ev (usym_hom R H μ (usym_hom Z R one l))
        by map_path (USym H) (GroupHom R R) ev (usym_hom Z H (group_hom_compose Z R H one μ) l)
          (usym_hom R H μ (usym_hom Z R one l))
          (refl ((φ ↦ φ l) : (USym Z → USym H) → USym H) (usym_hom_compose Z R H one μ))
      = ev (usym_hom Z H f (usym_hom R Z p (usym_hom Z R one l)))
        by map_path (USym H) (GroupHom R R) ev (usym_hom R H μ (usym_hom Z R one l))
          (usym_hom Z H f (usym_hom R Z p (usym_hom Z R one l)))
          (refl ((φ ↦ φ (usym_hom Z R one l)) : (USym R → USym H) → USym H) (usym_hom_compose R Z H p f))
      = ev (usym_hom Z H f l)
        by map_path (USym Z) (GroupHom R R) (x ↦ ev (usym_hom Z H f x)) (usym_hom R Z p (usym_hom Z R one l)) l hp
      = ev σ by map_path (USym H) (GroupHom R R) ev (usym_hom Z H f l) σ hf
      = group_hom_id R by hσ ∎

def ce_proj_one (C : CircleSignature)
  : Id (USym (circle_group C))
      (usym_hom (ce_group C .fst) (circle_group C) (product_group_proj1 (circle_group C) (circle_group C))
        (usym_hom (circle_group C) (ce_group C .fst) (ce_one C) (C .loop)))
      (C .loop)
  ≔ let Z ≔ circle_group C in
    concat (USym Z) (usym_hom (ce_group C .fst) Z (product_group_proj1 Z Z) (usym_hom Z (ce_group C .fst) (ce_one C) (C .loop)))
      (usym_hom Z (ce_group C .fst) (ce_one C) (C .loop) .fst) (C .loop)
      (product_group_proj1_usym Z Z (usym_hom Z (ce_group C .fst) (ce_one C) (C .loop)))
      (refl ((u ↦ u .fst) : USym (product_group Z Z) → USym Z) (product_group_incl1_usym Z Z (C .loop)))

{` hom_of_symmetry ∘ (its inverse) = id, generically (keeps the instance below cheap). `}
def hom_of_symmetry_section (G : Group) (H : AbelianGroup) (f : GroupHom G (H .fst))
  : Id (GroupHom G (H .fst))
      (hom_of_symmetry G H (equiv_inverse_map (USym (abelian_hom_group G H)) (GroupHom G (H .fst)) (abelian_hom_usym_equiv G H) f)) f
  ≔ equiv_counit (USym (abelian_hom_group G H)) (GroupHom G (H .fst)) (abelian_hom_usym_equiv G H) f

{` The printed unit law, in the form of module 1350: ev(USym(μ ∘ 1_R)(loop)) = id_R. `}
def ce_unit_law (C : CircleSignature)
  : Id (GroupHom (ce_group C .fst) (ce_group C .fst))
      (hom_of_symmetry (ce_group C .fst) (ce_group C)
        (usym_hom (circle_group C) (ce_hom_group C)
          (group_hom_compose (circle_group C) (ce_group C .fst) (ce_hom_group C) (ce_one C) (ce_mu C)) (circle_group_loop C)))
      (group_hom_id (ce_group C .fst))
  ≔ printed_unit_law_through (circle_group C) (ce_group C .fst) (ce_hom_group C) (hom_of_symmetry (ce_group C .fst) (ce_group C))
      (ce_sigma C)
      (hom_of_symmetry_section (ce_group C .fst) (ce_group C) (group_hom_id (ce_group C .fst)))
      (ce_one C) (product_group_proj1 (circle_group C) (circle_group C))
      (circle_group_hom_from_symmetry C (ce_hom_group C) (ce_sigma C)) (C .loop) (ce_proj_one C)
      (circle_group_hom_from_symmetry_loop C (ce_hom_group C) (ce_sigma C))

def ce_element (C : CircleSignature) : USym (ce_group C .fst) ≔ (refl (C .base), C .loop)

def ce_element_kernel (C : CircleSignature)
  : Id (USym (ce_hom_group C)) (usym_hom (ce_group C .fst) (ce_hom_group C) (ce_mu C) (ce_element C)) (usym_unit (ce_hom_group C))
  ≔ concat (USym (ce_hom_group C)) (usym_hom (ce_group C .fst) (ce_hom_group C) (ce_mu C) (ce_element C))
      (usym_hom (circle_group C) (ce_hom_group C) (circle_group_hom_from_symmetry C (ce_hom_group C) (ce_sigma C)) (refl (C .base)))
      (usym_unit (ce_hom_group C))
      (ce_mu_usym C (ce_element C))
      (usym_hom_unit (circle_group C) (ce_hom_group C) (circle_group_hom_from_symmetry C (ce_hom_group C) (ce_sigma C)))

{` The right unit law a · 1 = a fails at a = (refl, loop). `}
def ce_right_unit_fails (C : CircleSignature)
  (h : Id (USym (ce_group C .fst))
         (usym_hom (ce_group C .fst) (ce_group C .fst)
           (hom_of_symmetry (ce_group C .fst) (ce_group C) (usym_hom (ce_group C .fst) (ce_hom_group C) (ce_mu C) (ce_element C)))
           (usym_hom (circle_group C) (ce_group C .fst) (ce_one C) (circle_group_loop C)))
         (ce_element C))
  : Empty
  ≔ let R ≔ ce_group C .fst in
    let one ≔ usym_hom (circle_group C) R (ce_one C) (circle_group_loop C) in
    let t ≔ concat (USym R) (ce_element C)
        (usym_hom R R (hom_of_symmetry R (ce_group C) (usym_hom R (ce_hom_group C) (ce_mu C) (ce_element C))) one)
        (usym_unit R)
        (inverse (USym R)
          (usym_hom R R (hom_of_symmetry R (ce_group C) (usym_hom R (ce_hom_group C) (ce_mu C) (ce_element C))) one)
          (ce_element C) h)
        (evaluation_kernel_trivial R (ce_hom_group C) (ce_mu C) (hom_of_symmetry R (ce_group C))
          (abelian_hom_usym_mul R (ce_group C)) (ce_element C) (ce_element_kernel C) one) in
    circle_loop_not_refl C (refl ((u ↦ u .snd) : USym R → Id (C .carrier) (C .base) (C .base)) t)
