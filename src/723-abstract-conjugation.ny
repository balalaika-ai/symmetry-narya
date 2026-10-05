export "702-abstract-group-identity"
export "406-symmetric-group-three"
export "721-mere-inverses"

{` Chapter 7 (absgroup.tex), xca:conj and the first two paragraphs of
   ex:conjhom (the connection with inner automorphisms is module 730).

   conj^g(s) ≔ g·s·g⁻¹, bracketed (g·s)·g⁻¹ (the bracketing of usym
   conjugation in module 437). It preserves multiplication, is an
   equivalence, hence an isomorphism G ≅ G, and gives by univalence the
   identification conj^g : G = G. The instance displayed in xca:conj,
   g·(s·s')·g⁻¹ = (g·s·g⁻¹)·(g·s·g⁻¹), has s instead of s' in the last
   factor; it is false as printed (abstract_conj_printed_instance_fails)
   and the intended instance is abstract_conj_mul. `}

def abstract_conj (G : AbstractGroup) (g s : G .carrier) : G .carrier ≔ G .mul (G .mul g s) (G .inv g)

{` g·(s·s')·g⁻¹ = (g·s·g⁻¹)·(g·s'·g⁻¹). `}
def abstract_conj_mul (G : AbstractGroup) (g s s' : G .carrier)
  : Id (G .carrier) (abstract_conj G g (G .mul s s')) (G .mul (abstract_conj G g s) (abstract_conj G g s'))
  ≔ let S ≔ G .carrier in let m ≔ G .mul in let L ≔ G .laws in let ig ≔ G .inv g in
    calc
      m (m g (m s s')) ig = m (m (m g s) s') ig by refl ((x ↦ m x ig) : S → S) (L .assoc g s s')
      = m (m g s) (m s' ig) by inverse S (m (m g s) (m s' ig)) (m (m (m g s) s') ig) (L .assoc (m g s) s' ig)
      = m (m g s) (m (m ig (m g s')) ig)
        by refl ((x ↦ m (m g s) (m x ig)) : S → S) (inverse S (m ig (m g s')) s' (ag_mul_inv_cancel_left G g s'))
      = m (m g s) (m ig (m (m g s') ig))
        by refl (m (m g s)) (inverse S (m ig (m (m g s') ig)) (m (m ig (m g s')) ig) (L .assoc ig (m g s') ig))
      = m (m (m g s) ig) (m (m g s') ig) by L .assoc (m g s) ig (m (m g s') ig) ∎

def abstract_conj_hom (G : AbstractGroup) (g : G .carrier) : AbstractHom G G
  ≔ (abstract_conj G g, s s' ↦ abstract_conj_mul G g s s')

{` conj^g is an equivalence: left multiplication by g followed by right
   multiplication by g⁻¹ (its map is conj^g by computation). `}
def abstract_conj_equiv (G : AbstractGroup) (g : G .carrier) : Equiv (G .carrier) (G .carrier)
  ≔ compose_equiv (G .carrier) (G .carrier) (G .carrier) (ag_mul_left_equiv G g) (ag_mul_right_equiv G (G .inv g))

def abstract_conj_iso (G : AbstractGroup) (g : G .carrier) : AbstractIso G G
  ≔ (abstract_conj_equiv G g, s s' ↦ abstract_conj_mul G g s s')

{` The identification conj^g : G = G. `}
def abstract_conj_path (G : AbstractGroup) (g : G .carrier) : Id AbstractGroup G G
  ≔ abstract_group_path_from_iso G G (abstract_conj_iso G g)

def abstract_conj_path_transport (G : AbstractGroup) (g s : G .carrier)
  : Id (G .carrier) (abstract_conj_path G g .carrier .trr s) (abstract_conj G g s)
  ≔ refl (abstract_conj G g s)

{` conj^g ∘ conj^{g⁻¹} = id. `}
def abstract_conj_inverse_right (G : AbstractGroup) (g x : G .carrier)
  : Id (G .carrier) (abstract_conj G g (abstract_conj G (G .inv g) x)) x
  ≔ let S ≔ G .carrier in let m ≔ G .mul in let L ≔ G .laws in let ig ≔ G .inv g in
    calc
      m (m g (m (m ig x) (G .inv ig))) ig = m (m g (m (m ig x) g)) ig
        by refl ((y ↦ m (m g (m (m ig x) y)) ig) : S → S) (ag_inv_inv G g)
      = m (m (m g (m ig x)) g) ig by refl ((y ↦ m y ig) : S → S) (L .assoc g (m ig x) g)
      = m g (m ig x) by ag_mul_inv_cancel_right G (m g (m ig x)) g
      = x by ag_mul_cancel_inv_left G g x ∎

{` The printed instance is false: in the integers with g = s = 0 and
   s' = 1 it says 1 = 0. `}
def abstract_conj_printed_instance_fails
  (h : (G : AbstractGroup) (g s s' : G .carrier)
    → Id (G .carrier) (abstract_conj G g (G .mul s s')) (G .mul (abstract_conj G g s) (abstract_conj G g s)))
  : Empty
  ≔ int_encode (pos. (suc. zero.)) int_zero (h int_add_abstract_group int_zero int_zero (pos. (suc. zero.)))

{` ex:conjhom, transport along an identification obtained from an
   isomorphism φ : G ≅ G'. In the family X ↦ absHom(H, X) it is
   postcomposition with φ; in the family X ↦ absHom(X, K) it is
   precomposition with φ⁻¹: the transported homomorphism takes x to f(y)
   for any y with φ(y) = x. Both are read off the canonical dependent
   identification (liftr) over the carrier component ua(φ). `}
def abstract_iso_transport_postcompose (H G G' : AbstractGroup) (φ : AbstractIso G G') (f : AbstractHom H G)
  (h : H .carrier)
  : Id (G' .carrier)
      (transport AbstractGroup (X ↦ AbstractHom H X) G G' (abstract_group_path_from_iso G G' φ) f .fst h)
      (φ .fst .map (f .fst h))
  ≔ inverse (G' .carrier) (φ .fst .map (f .fst h))
      (transport AbstractGroup (X ↦ AbstractHom H X) G G' (abstract_group_path_from_iso G G' φ) f .fst h)
      (refl ((X ↦ AbstractHom H X) : AbstractGroup → Type) (abstract_group_path_from_iso G G' φ) .liftr f
        .fst (refl h) .unglue)

def abstract_iso_transport_postcompose_hom (H G G' : AbstractGroup) (φ : AbstractIso G G') (f : AbstractHom H G)
  : Id (AbstractHom H G')
      (transport AbstractGroup (X ↦ AbstractHom H X) G G' (abstract_group_path_from_iso G G' φ) f)
      (abstract_hom_compose H G G' f (abstract_iso_hom G G' φ))
  ≔ abstract_hom_ext H G'
      (transport AbstractGroup (X ↦ AbstractHom H X) G G' (abstract_group_path_from_iso G G' φ) f)
      (abstract_hom_compose H G G' f (abstract_iso_hom G G' φ))
      (abstract_iso_transport_postcompose H G G' φ f)

def abstract_iso_transport_precompose (H H' K : AbstractGroup) (ψ : AbstractIso H H') (f : AbstractHom H K)
  (x : H' .carrier) (y : H .carrier) (q : Id (H' .carrier) (ψ .fst .map y) x)
  : Id (K .carrier)
      (transport AbstractGroup (X ↦ AbstractHom X K) H H' (abstract_group_path_from_iso H H' ψ) f .fst x)
      (f .fst y)
  ≔ let x2 : ua (H .carrier) (H' .carrier) (ψ .fst) y x ≔ (unglue ≔ q) in
    inverse (K .carrier) (f .fst y)
      (transport AbstractGroup (X ↦ AbstractHom X K) H H' (abstract_group_path_from_iso H H' ψ) f .fst x)
      (refl ((X ↦ AbstractHom X K) : AbstractGroup → Type) (abstract_group_path_from_iso H H' ψ) .liftr f .fst x2)

{` ex:conjhom: transport along conj^g : G = G in X ↦ absHom(H, X) is
   postcomposition with conj^g. `}
def abstract_conj_transport_postcompose (H G : AbstractGroup) (g : G .carrier) (f : AbstractHom H G)
  : Id (AbstractHom H G) (transport AbstractGroup (X ↦ AbstractHom H X) G G (abstract_conj_path G g) f)
      (abstract_hom_compose H G G f (abstract_conj_hom G g))
  ≔ abstract_iso_transport_postcompose_hom H G G (abstract_conj_iso G g) f

{` ex:conjhom, "similarly for elements in H": transport along
   conj^h : H = H in X ↦ absHom(X, K) is precomposition with the inverse
   (conj^h)⁻¹ = conj^{h⁻¹}, i.e. f ↦ f ∘ conj^{h⁻¹}. `}
def abstract_conj_transport_precompose (H K : AbstractGroup) (h : H .carrier) (f : AbstractHom H K)
  : Id (AbstractHom H K) (transport AbstractGroup (X ↦ AbstractHom X K) H H (abstract_conj_path H h) f)
      (abstract_hom_compose H H K (abstract_conj_hom H (H .inv h)) f)
  ≔ abstract_hom_ext H K (transport AbstractGroup (X ↦ AbstractHom X K) H H (abstract_conj_path H h) f)
      (abstract_hom_compose H H K (abstract_conj_hom H (H .inv h)) f)
      (x ↦ abstract_iso_transport_precompose H H K (abstract_conj_iso H h) f x (abstract_conj H (H .inv h) x)
        (abstract_conj_inverse_right H h x))

{` Litmus: in an abelian group conjugation is the identity; in the
   integers conj^1(2) = 2 by computation; in abstr Σ_3 conj^τ moves σ. `}
def abstract_conj_abelian (G : AbstractGroup) (hab : IsAbstractAbelian G) (g s : G .carrier)
  : Id (G .carrier) (abstract_conj G g s) s
  ≔ let S ≔ G .carrier in let m ≔ G .mul in
    concat S (m (m g s) (G .inv g)) (m (m s g) (G .inv g)) s
      (refl ((x ↦ m x (G .inv g)) : S → S) (hab g s)) (ag_mul_inv_cancel_right G s g)

def abstract_conj_int_litmus
  : Id Int (abstract_conj int_add_abstract_group (pos. (suc. zero.)) (pos. (suc. (suc. zero.)))) (pos. (suc. (suc. zero.)))
  ≔ refl (pos. (suc. (suc. zero.)) : Int)

def abstract_conj_fixed_commutes (G : AbstractGroup) (g s : G .carrier) (p : Id (G .carrier) (abstract_conj G g s) s)
  : Id (G .carrier) (G .mul g s) (G .mul s g)
  ≔ let S ≔ G .carrier in let m ≔ G .mul in
    concat S (m g s) (m (abstract_conj G g s) g) (m s g)
      (inverse S (m (m (m g s) (G .inv g)) g) (m g s) (ag_mul_cancel_inv_right G (m g s) g))
      (refl ((x ↦ m x g) : S → S) p)

def abstract_conj_sigma3_moves
  (p : Id (USym (symmetric_group three)) (abstract_conj (abstr (symmetric_group three)) sigma3_tau sigma3_sigma) sigma3_sigma)
  : Empty
  ≔ sigma3_tau_sigma_noncommuting
      (inverse (USym (symmetric_group three)) (usym_mul (symmetric_group three) sigma3_tau sigma3_sigma)
        (usym_mul (symmetric_group three) sigma3_sigma sigma3_tau)
        (abstract_conj_fixed_commutes (abstr (symmetric_group three)) sigma3_tau sigma3_sigma p))
