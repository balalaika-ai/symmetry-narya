export "1219-abelian-hom-abstract"

{` Chapter 12, sec:direct-sums (abelian.tex 940-946), running text: "a sum
   of abelian groups is rarely abelian ... But a very similar construction
   works to produce sums of abelian groups". For two abelian groups the sum
   in abelian groups is the product G × H (the direct sum G ⊕ H): for an
   abelian group K, homomorphisms G × H → K correspond to pairs of
   homomorphisms G → K, H → K, by restriction along the inclusions
   g ↦ (g, e) and h ↦ (e, h), with inverse (φ, ψ) ↦ ((g, h) ↦ φ(g)ψ(h)).
   (The non-abelian sum Z ∨ Z = F₂ is chapter 8: circle_sum_not_abelian,
   free_bool_group_not_abelian.) Proved for abstract homomorphisms and
   transferred with lem:homomabstrconcr (abstr_hom_equiv, module 710). `}

{` The inclusions on symmetries. `}
def direct_sum_incl_left (G H : Group) (g : USym G) : USym (product_group G H) ≔ (g, usym_unit H)

def direct_sum_incl_right (G H : Group) (h : USym H) : USym (product_group G H) ≔ (usym_unit G, h)

def direct_sum_incl_left_mul (G H : Group) (g g' : USym G)
  : Id (USym (product_group G H)) (direct_sum_incl_left G H (usym_mul G g g'))
      (usym_mul (product_group G H) (direct_sum_incl_left G H g) (direct_sum_incl_left G H g'))
  ≔ product_usym_path G H (direct_sum_incl_left G H (usym_mul G g g'))
      (usym_mul (product_group G H) (direct_sum_incl_left G H g) (direct_sum_incl_left G H g'))
      (inverse (USym G) (usym_mul (product_group G H) (direct_sum_incl_left G H g) (direct_sum_incl_left G H g') .fst)
        (usym_mul G g g') (product_usym_mul_fst G H (direct_sum_incl_left G H g) (direct_sum_incl_left G H g')))
      (inverse (USym H) (usym_mul (product_group G H) (direct_sum_incl_left G H g) (direct_sum_incl_left G H g') .snd)
        (usym_unit H)
        (concat (USym H) (usym_mul (product_group G H) (direct_sum_incl_left G H g) (direct_sum_incl_left G H g') .snd)
          (usym_mul H (usym_unit H) (usym_unit H)) (usym_unit H)
          (product_usym_mul_snd G H (direct_sum_incl_left G H g) (direct_sum_incl_left G H g'))
          (usym_abstract_laws H .unit_right (usym_unit H))))

def direct_sum_incl_right_mul (G H : Group) (h h' : USym H)
  : Id (USym (product_group G H)) (direct_sum_incl_right G H (usym_mul H h h'))
      (usym_mul (product_group G H) (direct_sum_incl_right G H h) (direct_sum_incl_right G H h'))
  ≔ product_usym_path G H (direct_sum_incl_right G H (usym_mul H h h'))
      (usym_mul (product_group G H) (direct_sum_incl_right G H h) (direct_sum_incl_right G H h'))
      (inverse (USym G) (usym_mul (product_group G H) (direct_sum_incl_right G H h) (direct_sum_incl_right G H h') .fst)
        (usym_unit G)
        (concat (USym G) (usym_mul (product_group G H) (direct_sum_incl_right G H h) (direct_sum_incl_right G H h') .fst)
          (usym_mul G (usym_unit G) (usym_unit G)) (usym_unit G)
          (product_usym_mul_fst G H (direct_sum_incl_right G H h) (direct_sum_incl_right G H h'))
          (usym_abstract_laws G .unit_right (usym_unit G))))
      (inverse (USym H) (usym_mul (product_group G H) (direct_sum_incl_right G H h) (direct_sum_incl_right G H h') .snd)
        (usym_mul H h h') (product_usym_mul_snd G H (direct_sum_incl_right G H h) (direct_sum_incl_right G H h')))

{` Every symmetry of G × H is (g, e)·(e, h). `}
def direct_sum_decompose (G H : Group) (r : USym (product_group G H))
  : Id (USym (product_group G H))
      (usym_mul (product_group G H) (direct_sum_incl_left G H (r .fst)) (direct_sum_incl_right G H (r .snd))) r
  ≔ let a ≔ direct_sum_incl_left G H (r .fst) in let b ≔ direct_sum_incl_right G H (r .snd) in
    product_usym_path G H (usym_mul (product_group G H) a b) r
      (concat (USym G) (usym_mul (product_group G H) a b .fst) (usym_mul G (r .fst) (usym_unit G)) (r .fst)
        (product_usym_mul_fst G H a b) (usym_abstract_laws G .unit_right (r .fst)))
      (concat (USym H) (usym_mul (product_group G H) a b .snd) (usym_mul H (usym_unit H) (r .snd)) (r .snd)
        (product_usym_mul_snd G H a b) (usym_abstract_laws H .unit_left (r .snd)))

{` Restriction along the two inclusions. `}
def direct_sum_restrict (G H K : Group) (f : AbstractHom (abstr (product_group G H)) (abstr K))
  : Product (AbstractHom (abstr G) (abstr K)) (AbstractHom (abstr H) (abstr K))
  ≔ (((g ↦ f .fst (direct_sum_incl_left G H g)),
      g g' ↦ concat (USym K) (f .fst (direct_sum_incl_left G H (usym_mul G g g')))
        (f .fst (usym_mul (product_group G H) (direct_sum_incl_left G H g) (direct_sum_incl_left G H g')))
        (usym_mul K (f .fst (direct_sum_incl_left G H g)) (f .fst (direct_sum_incl_left G H g')))
        (refl (f .fst) (direct_sum_incl_left_mul G H g g'))
        (f .snd (direct_sum_incl_left G H g) (direct_sum_incl_left G H g'))),
     ((h ↦ f .fst (direct_sum_incl_right G H h)),
      h h' ↦ concat (USym K) (f .fst (direct_sum_incl_right G H (usym_mul H h h')))
        (f .fst (usym_mul (product_group G H) (direct_sum_incl_right G H h) (direct_sum_incl_right G H h')))
        (usym_mul K (f .fst (direct_sum_incl_right G H h)) (f .fst (direct_sum_incl_right G H h')))
        (refl (f .fst) (direct_sum_incl_right_mul G H h h'))
        (f .snd (direct_sum_incl_right G H h) (direct_sum_incl_right G H h'))))

{` (φ, ψ) ↦ ((g, h) ↦ φ(g)ψ(h)), a homomorphism because K is abelian. `}
def direct_sum_combine (G H K : Group) (hK : IsAbelian K)
  (φψ : Product (AbstractHom (abstr G) (abstr K)) (AbstractHom (abstr H) (abstr K)))
  : AbstractHom (abstr (product_group G H)) (abstr K)
  ≔ let φ ≔ φψ .fst in let ψ ≔ φψ .snd in let P ≔ product_group G H in
    ((r ↦ usym_mul K (φ .fst (r .fst)) (ψ .fst (r .snd))),
     r s ↦ calc
       usym_mul K (φ .fst (usym_mul P r s .fst)) (ψ .fst (usym_mul P r s .snd))
         = usym_mul K (φ .fst (usym_mul G (r .fst) (s .fst))) (ψ .fst (usym_mul H (r .snd) (s .snd)))
         by refl (usym_mul K) (refl (φ .fst) (product_usym_mul_fst G H r s)) (refl (ψ .fst) (product_usym_mul_snd G H r s))
       = usym_mul K (usym_mul K (φ .fst (r .fst)) (φ .fst (s .fst))) (usym_mul K (ψ .fst (r .snd)) (ψ .fst (s .snd)))
         by refl (usym_mul K) (φ .snd (r .fst) (s .fst)) (ψ .snd (r .snd) (s .snd))
       = usym_mul K (usym_mul K (φ .fst (r .fst)) (ψ .fst (r .snd))) (usym_mul K (φ .fst (s .fst)) (ψ .fst (s .snd)))
         by abelian_interchange K hK (φ .fst (r .fst)) (φ .fst (s .fst)) (ψ .fst (r .snd)) (ψ .fst (s .snd)) ∎)

def direct_sum_abstract_equiv (G H K : Group) (hK : IsAbelian K)
  : Equiv (AbstractHom (abstr (product_group G H)) (abstr K))
      (Product (AbstractHom (abstr G) (abstr K)) (AbstractHom (abstr H) (abstr K)))
  ≔ let P ≔ product_group G H in
    quasi_inverse_equiv (AbstractHom (abstr P) (abstr K))
      (Product (AbstractHom (abstr G) (abstr K)) (AbstractHom (abstr H) (abstr K)))
      (direct_sum_restrict G H K) (direct_sum_combine G H K hK)
      (f ↦ abstract_hom_ext (abstr P) (abstr K) (direct_sum_combine G H K hK (direct_sum_restrict G H K f)) f
        (r ↦ concat (USym K)
          (usym_mul K (f .fst (direct_sum_incl_left G H (r .fst))) (f .fst (direct_sum_incl_right G H (r .snd))))
          (f .fst (usym_mul P (direct_sum_incl_left G H (r .fst)) (direct_sum_incl_right G H (r .snd)))) (f .fst r)
          (inverse (USym K) (f .fst (usym_mul P (direct_sum_incl_left G H (r .fst)) (direct_sum_incl_right G H (r .snd))))
            (usym_mul K (f .fst (direct_sum_incl_left G H (r .fst))) (f .fst (direct_sum_incl_right G H (r .snd))))
            (f .snd (direct_sum_incl_left G H (r .fst)) (direct_sum_incl_right G H (r .snd))))
          (refl (f .fst) (direct_sum_decompose G H r))))
      (φψ ↦ let φ ≔ φψ .fst in let ψ ≔ φψ .snd in
        (abstract_hom_ext (abstr G) (abstr K) (direct_sum_restrict G H K (direct_sum_combine G H K hK φψ) .fst) φ
          (g ↦ concat (USym K) (usym_mul K (φ .fst g) (ψ .fst (usym_unit H))) (usym_mul K (φ .fst g) (usym_unit K)) (φ .fst g)
            (refl (usym_mul K (φ .fst g)) (abstract_hom_preserves_unit (abstr H) (abstr K) (ψ .fst) (ψ .snd)))
            (usym_abstract_laws K .unit_right (φ .fst g))),
         abstract_hom_ext (abstr H) (abstr K) (direct_sum_restrict G H K (direct_sum_combine G H K hK φψ) .snd) ψ
          (h ↦ concat (USym K) (usym_mul K (φ .fst (usym_unit G)) (ψ .fst h)) (usym_mul K (usym_unit K) (ψ .fst h)) (ψ .fst h)
            (refl ((u ↦ usym_mul K u (ψ .fst h)) : USym K → USym K)
              (abstract_hom_preserves_unit (abstr G) (abstr K) (φ .fst) (φ .snd)))
            (usym_abstract_laws K .unit_left (ψ .fst h)))))

{` The universal property of the direct sum G ⊕ H = G × H among abelian
   groups: Hom(G × H, K) ≃ Hom(G, K) × Hom(H, K) for abelian K (G, H any
   groups; for abelian G, H this says G × H is the sum in AbCat). `}
def direct_sum_hom_equiv (G H K : Group) (hK : IsAbelian K)
  : Equiv (GroupHom (product_group G H) K) (Product (GroupHom G K) (GroupHom H K))
  ≔ let P ≔ product_group G H in
    compose_equiv (GroupHom P K) (AbstractHom (abstr P) (abstr K)) (Product (GroupHom G K) (GroupHom H K))
      (abstr_hom_equiv P K)
      (compose_equiv (AbstractHom (abstr P) (abstr K))
        (Product (AbstractHom (abstr G) (abstr K)) (AbstractHom (abstr H) (abstr K)))
        (Product (GroupHom G K) (GroupHom H K))
        (direct_sum_abstract_equiv G H K hK)
        (product_equiv (AbstractHom (abstr G) (abstr K)) (AbstractHom (abstr H) (abstr K)) (GroupHom G K) (GroupHom H K)
          (canonical_inverse_equiv (GroupHom G K) (AbstractHom (abstr G) (abstr K)) (abstr_hom_equiv G K))
          (canonical_inverse_equiv (GroupHom H K) (AbstractHom (abstr H) (abstr K)) (abstr_hom_equiv H K))))

{` On symmetries, the components of the image of f are f restricted along
   the inclusions (after abstraction). `}
def direct_sum_restrict_value (G H K : Group) (f : AbstractHom (abstr (product_group G H)) (abstr K)) (g : USym G)
  : Id (USym K) (direct_sum_restrict G H K f .fst .fst g) (f .fst (g, usym_unit H))
  ≔ refl (f .fst (g, usym_unit H))

def direct_sum_abelian_group (A B : AbelianGroup) : AbelianGroup ≔ abelian_product A B
