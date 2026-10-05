export "701-abstract-homomorphisms"
export "406-symmetric-group-three"

{` Chapter 7 (absgroup.tex), xca:abs-homgroup. For f, g : absHom(H, G)
   the pointwise product (f ·_G g)(t) ≔ f(t) ·_G g(t).

   As printed ("G is abelian iff any f · g is a homomorphism", for given
   G and H) the "if" direction is false: for the trivial group H every
   pointwise product of homomorphisms H → G is a homomorphism (all of
   them are constant at e), also for the non-abelian G = abstr Σ_3.
   Formalized: (1) G abelian ⇒ every pointwise product f · g of
   homomorphisms H → G is a homomorphism, for every H; (2) conversely, if
   id_G · id_G (s ↦ s · s) is a homomorphism G → G then G is abelian, so G
   is abelian iff all pointwise products are homomorphisms for H ≔ G (or
   for all H); (3) the counterexample for H trivial. `}

def abstract_hom_pointwise_mul (H G : AbstractGroup) (f g : AbstractHom H G) (t : H .carrier) : G .carrier
  ≔ G .mul (f .fst t) (g .fst t)

{` (ab)(cd) = (ac)(bd) in an abelian group. `}
def abstract_abelian_interchange (G : AbstractGroup) (hab : IsAbstractAbelian G) (a b c d : G .carrier)
  : Id (G .carrier) (G .mul (G .mul a b) (G .mul c d)) (G .mul (G .mul a c) (G .mul b d))
  ≔ let S ≔ G .carrier in let m ≔ G .mul in let L ≔ G .laws in
    calc
      m (m a b) (m c d) = m a (m b (m c d)) by inverse S (m a (m b (m c d))) (m (m a b) (m c d)) (L .assoc a b (m c d))
      = m a (m (m b c) d) by refl (m a) (L .assoc b c d)
      = m a (m (m c b) d) by refl ((x ↦ m a (m x d)) : S → S) (hab b c)
      = m a (m c (m b d)) by refl (m a) (inverse S (m c (m b d)) (m (m c b) d) (L .assoc c b d))
      = m (m a c) (m b d) by L .assoc a c (m b d) ∎

{` (1) If G is abelian, every pointwise product is a homomorphism. `}
def abelian_pointwise_mul_hom (H G : AbstractGroup) (hab : IsAbstractAbelian G) (f g : AbstractHom H G)
  : IsAbstractHom H G (abstract_hom_pointwise_mul H G f g)
  ≔ t t' ↦
    let S ≔ G .carrier in let m ≔ G .mul in
    concat S (m (f .fst (H .mul t t')) (g .fst (H .mul t t'))) (m (m (f .fst t) (f .fst t')) (m (g .fst t) (g .fst t')))
      (m (m (f .fst t) (g .fst t)) (m (f .fst t') (g .fst t')))
      (refl m (f .snd t t') (g .snd t t'))
      (abstract_abelian_interchange G hab (f .fst t) (f .fst t') (g .fst t) (g .fst t'))

{` (2) If s ↦ s · s is a homomorphism G → G, then G is abelian:
   (st)(st) = (ss)(tt) cancels to ts = st. `}
def square_hom_abelian (G : AbstractGroup) (h : IsAbstractHom G G (s ↦ G .mul s s)) : IsAbstractAbelian G
  ≔ x y ↦
    let S ≔ G .carrier in let m ≔ G .mul in let L ≔ G .laws in
    let s ≔ y in let t ≔ x in
    let p1 : Id S (m s (m t (m s t))) (m s (m s (m t t)))
      ≔ calc
          m s (m t (m s t)) = m (m s t) (m s t) by L .assoc s t (m s t)
          = m (m s s) (m t t) by h s t
          = m s (m s (m t t)) by inverse S (m s (m s (m t t))) (m (m s s) (m t t)) (L .assoc s s (m t t)) ∎ in
    let p2 : Id S (m t (m s t)) (m s (m t t)) ≔ ag_cancel_left G s (m t (m s t)) (m s (m t t)) p1 in
    let p3 : Id S (m (m t s) t) (m (m s t) t)
      ≔ calc
          m (m t s) t = m t (m s t) by inverse S (m t (m s t)) (m (m t s) t) (L .assoc t s t)
          = m s (m t t) by p2
          = m (m s t) t by L .assoc s t t ∎ in
    ag_cancel_right G t (m t s) (m s t) p3

def pointwise_products_hom_abelian (G : AbstractGroup)
  (h : (f g : AbstractHom G G) → IsAbstractHom G G (abstract_hom_pointwise_mul G G f g)) : IsAbstractAbelian G
  ≔ square_hom_abelian G (h (abstract_hom_id G) (abstract_hom_id G))

def pointwise_products_hom_all_abelian (G : AbstractGroup)
  (h : (H : AbstractGroup) (f g : AbstractHom H G) → IsAbstractHom H G (abstract_hom_pointwise_mul H G f g))
  : IsAbstractAbelian G
  ≔ pointwise_products_hom_abelian G (h G)

{` The corrected exercise: G is abelian iff all pointwise products of
   endomorphisms of G are homomorphisms. `}
def abelian_iff_pointwise_products_hom (G : AbstractGroup)
  : Product (IsAbstractAbelian G → (f g : AbstractHom G G) → IsAbstractHom G G (abstract_hom_pointwise_mul G G f g))
      (((f g : AbstractHom G G) → IsAbstractHom G G (abstract_hom_pointwise_mul G G f g)) → IsAbstractAbelian G)
  ≔ (hab ↦ abelian_pointwise_mul_hom G G hab, pointwise_products_hom_abelian G)

{` (3) The trivial abstract group, and the counterexample to the printed
   "if" direction for a fixed H. `}
def unit_abstract_group_laws : AbstractGroupLaws Unit star. (_ _ ↦ star.) (_ ↦ star.)
  ≔ (unit_set,
     g ↦ match g [ star. ↦ refl (star. : Unit) ],
     g ↦ match g [ star. ↦ refl (star. : Unit) ],
     _ _ _ ↦ refl (star. : Unit),
     _ ↦ refl (star. : Unit))

def unit_abstract_group : AbstractGroup ≔ (Unit, star., _ _ ↦ star., _ ↦ star., unit_abstract_group_laws)

def unit_pointwise_mul_hom (G : AbstractGroup) (f g : AbstractHom unit_abstract_group G)
  : IsAbstractHom unit_abstract_group G (abstract_hom_pointwise_mul unit_abstract_group G f g)
  ≔ let S ≔ G .carrier in let m ≔ G .mul in
    let u ≔ m (f .fst star.) (g .fst star.) in
    let pu : Id S u (G .unit)
      ≔ concat S u (m (G .unit) (G .unit)) (G .unit)
          (refl m (abstract_hom_preserves_unit unit_abstract_group G (f .fst) (f .snd))
            (abstract_hom_preserves_unit unit_abstract_group G (g .fst) (g .snd)))
          (G .laws .unit_right (G .unit)) in
    let q : Id S u (m u u)
      ≔ inverse S (m u u) u (concat S (m u u) (m u (G .unit)) u (refl (m u) pu) (G .laws .unit_right u)) in
    t t' ↦ match t [ star. ↦ match t' [ star. ↦ q ] ]

def pointwise_products_hom_fixed_domain_fails
  (h : ((f g : AbstractHom unit_abstract_group (abstr (symmetric_group three)))
        → IsAbstractHom unit_abstract_group (abstr (symmetric_group three))
            (abstract_hom_pointwise_mul unit_abstract_group (abstr (symmetric_group three)) f g))
     → IsAbstractAbelian (abstr (symmetric_group three)))
  : Empty
  ≔ symmetric_group_three_not_abelian (h (unit_pointwise_mul_hom (abstr (symmetric_group three))))

{` Litmus: in abstr Σ_3 the squaring map s ↦ s · s is not a homomorphism. `}
def sigma3_square_not_hom
  (h : IsAbstractHom (abstr (symmetric_group three)) (abstr (symmetric_group three))
    (s ↦ abstr (symmetric_group three) .mul s s)) : Empty
  ≔ symmetric_group_three_not_abelian (square_hom_abelian (abstr (symmetric_group three)) h)
