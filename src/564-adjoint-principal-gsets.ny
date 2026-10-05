export "563-gset-fixed-points"
export "506-trivial-groups"
export "435-circle-group-homomorphisms"
export "437-conjugation-inner-automorphisms"
export "405-integer-group"

{` Chapter 5 (actions.tex), sec:gsets: the principal torsor and the G-sets
   P_y (def:principaltorsor, eq:pathsp), the adjoint G-set and the free loop
   space (def:adjointrep, ft:adjoint-transport), Hom(H, G) as an
   (H × G)-set and a G-set (ex:HomHGasGset), Ad_G = Hom(Z, G)
   (xca:HomZGvsAdG), G abelian iff Ad_G = triv_G(USym G)
   (xca:Ad-triv-abelian), G trivial iff Ad_G = P_G (xca:Ad-princ-trivial). `}

{` def:principaltorsor. "We've seen this family before": P_G is the family
   of the universal covering of def:universalcover (path_cover_family),
   and so is every P_y (refl). `}
def principal_gset_universal_cover (G : Group)
  : Id (GSet G) (principal_gset G) (path_cover_family (BG G .carrier) (bg_groupoid G) (shape G))
  ≔ refl (principal_gset G)

def gset_paths_universal_cover (G : Group) (y : BG G .carrier)
  : Id (GSet G) (gset_paths G y) (path_cover_family (BG G .carrier) (bg_groupoid G) y)
  ≔ refl (gset_paths G y)

{` eq:pathsp. Applying P_- to q : y = y' gives the equivalence
   P_y(z) ≃ P_{y'}(z), sending p : y = z to p q⁻¹ (concat q⁻¹ p) at every z
   (gset_paths_transport, module 504, typal). `}
def gset_paths_map_equiv (G : Group) (y y' : BG G .carrier) (q : Id (BG G .carrier) y y') (z : BG G .carrier)
  : Equiv (Id (BG G .carrier) y z) (Id (BG G .carrier) y' z)
  ≔ gset_path_equiv G (gset_paths G y) (gset_paths G y') .map (map_path (BG G .carrier) (GSet G) (gset_paths G) y y' q) z

def gset_paths_map_equiv_value (G : Group) (y y' : BG G .carrier) (q : Id (BG G .carrier) y y') (z : BG G .carrier)
  (p : Id (BG G .carrier) y z)
  : Id (Id (BG G .carrier) y' z) (gset_paths_map_equiv G y y' q z .map p)
      (concat (BG G .carrier) y' y z (inverse (BG G .carrier) y y' q) p)
  ≔ gset_paths_transport G y y' z q p

{` def:adjointrep. Σ_{z:BG} Ad_G(z) ≡ Σ_{z:BG} (z = z) is equivalent to the
   free loop space S¹ → BG, for every circle C (lem:freeloopspace); under
   this equivalence the first projection corresponds to evaluation at base. `}
def adjoint_free_loops_equiv (G : Group) (C : CircleSignature)
  : Equiv (ActionType G (adjoint_gset G)) (C .carrier → BG G .carrier)
  ≔ canonical_inverse_equiv (C .carrier → BG G .carrier) (ActionType G (adjoint_gset G))
      (circle_universal_property C (BG G .carrier))

{` The inverse is f ↦ (f(base), ap_f(loop)), so its first component is
   evaluation at base (refl), and the map evaluated at base is the first
   projection (typal, the base computation of the circle). `}
def adjoint_free_loops_inverse_fst (G : Group) (C : CircleSignature) (f : C .carrier → BG G .carrier)
  : Id (BG G .carrier)
      (equiv_inverse_map (ActionType G (adjoint_gset G)) (C .carrier → BG G .carrier) (adjoint_free_loops_equiv G C) f .fst)
      (f (C .base))
  ≔ refl (f (C .base))

def adjoint_free_loops_base (G : Group) (C : CircleSignature) (u : ActionType G (adjoint_gset G))
  : Id (BG G .carrier) (adjoint_free_loops_equiv G C .map u (C .base)) (u .fst)
  ≔ circle_rec_beta C (BG G .carrier) u .fst

def adjoint_free_loops_projection (G : Group) (C : CircleSignature)
  : Id (ActionType G (adjoint_gset G) → BG G .carrier)
      (u ↦ adjoint_free_loops_equiv G C .map u (C .base)) (u ↦ u .fst)
  ≔ funext (ActionType G (adjoint_gset G)) (_ ↦ BG G .carrier)
      (u ↦ adjoint_free_loops_equiv G C .map u (C .base)) (u ↦ u .fst)
      (adjoint_free_loops_base G C)

{` ex:HomHGasGset. Hom(H, G)(x, y) ≔ Hom(mkgroup(BH÷, x), mkgroup(BG÷, y))
   (group_at, module 437) is an (H × G)-set (B(H × G) ≡ BH × BG); its
   restriction to G is Hom(H, G)(y) ≔ Hom(H, G)(sh_H, y), which is the
   restriction along the inclusion G → H × G (refl). `}
def group_hom_pair_gset (H G : Group) : GSet (product_group H G)
  ≔ xy ↦ (GroupHom (group_at H (xy .fst)) (group_at G (xy .snd)),
      group_hom_set (group_at H (xy .fst)) (group_at G (xy .snd)))

def group_hom_gset (H G : Group) : GSet G ≔ y ↦ group_hom_pair_gset H G (shape H, y)

def group_hom_gset_restrict (H G : Group)
  : Id (GSet G) (group_hom_gset H G)
      (gset_restrict G (product_group H G) (product_group_incl2 H G) (group_hom_pair_gset H G))
  ≔ refl (group_hom_gset H G)

{` The underlying set of Hom(H, G) is Hom(H, G) (record eta for groups). `}
def group_hom_gset_underlying (H G : Group) : Id Type (gset_underlying G (group_hom_gset H G)) (GroupHom H G)
  ≔ refl (GroupHom H G)

{` "Hom(H, G)(x, y) ≡ Copy_mkgroup(Σ_{f : BH÷ → BG÷} (y = f(x)))": a
   homomorphism is a one-field record around such a pointed map. `}
def group_hom_pair_unfold (H G : Group) (x : BG H .carrier) (y : BG G .carrier)
  : Equiv (GroupHom (group_at H x) (group_at G y))
      (Σ (BG H .carrier → BG G .carrier) (f ↦ Id (BG G .carrier) y (f x)))
  ≔ group_hom_classifying_equiv (group_at H x) (group_at G y)

{` xca:HomZGvsAdG. For Z = mkgroup(S¹, base) (any circle C), Hom(Z, G)(y) ≃
   Ad_G(y) by f ↦ Ω(Bf)(loop) (ex:Zinitial, module 435), hence an
   identification of G-sets Ad_G = Hom(Z, G). The book's hint (contract
   away Σ_z Σ_{p:z=z} (y = z)) is the content of module 435's
   pointed_circle_universal_property. `}
def hom_z_adjoint_equiv (C : CircleSignature) (G : Group) (y : BG G .carrier)
  : Equiv (group_hom_gset (circle_group C) G y .fst) (adjoint_gset G y .fst)
  ≔ circle_group_hom_ev C (group_at G y)

def hom_z_adjoint_value (C : CircleSignature) (G : Group) (y : BG G .carrier)
  (f : GroupHom (circle_group C) (group_at G y))
  : Id (Id (BG G .carrier) y y) (hom_z_adjoint_equiv C G y .map f)
      (usym_hom (circle_group C) (group_at G y) f (circle_group_loop C))
  ≔ refl (usym_hom (circle_group C) (group_at G y) f (circle_group_loop C))

def hom_z_adjoint_path (C : CircleSignature) (G : Group)
  : Id (GSet G) (group_hom_gset (circle_group C) G) (adjoint_gset G)
  ≔ gset_path_from_equivs G (group_hom_gset (circle_group C) G) (adjoint_gset G) (y ↦ hom_z_adjoint_equiv C G y)

def adjoint_hom_z_path (C : CircleSignature) (G : Group)
  : Id (GSet G) (adjoint_gset G) (group_hom_gset (circle_group C) G)
  ≔ inverse (GSet G) (group_hom_gset (circle_group C) G) (adjoint_gset G) (hom_z_adjoint_path C G)

{` The identification transports f to f(loop) at every y. `}
def hom_z_adjoint_path_transport (C : CircleSignature) (G : Group) (y : BG G .carrier)
  (f : GroupHom (circle_group C) (group_at G y))
  : Id (Id (BG G .carrier) y y)
      (gset_path_transport G (group_hom_gset (circle_group C) G) (adjoint_gset G) (hom_z_adjoint_path C G) y f)
      (usym_hom (circle_group C) (group_at G y) f (circle_group_loop C))
  ≔ gset_path_from_equivs_transport G (group_hom_gset (circle_group C) G) (adjoint_gset G)
      (w ↦ hom_z_adjoint_equiv C G w) y f

{` The instance for the integers Z = integer_group (the constructed circle). `}
def adjoint_hom_integer_path (G : Group) : Id (GSet G) (adjoint_gset G) (group_hom_gset integer_group G)
  ≔ adjoint_hom_z_path constructed_circle G

{` xca:Ad-triv-abelian. For abelian G, conjugation is trivial:
   g ·_{Ad} h = g h g⁻¹ = h. `}
def adjoint_abelian_conj_trivial (G : Group) (hab : IsAbelian G) (g h : USym G)
  : Id (USym G) (gset_usym_act G (adjoint_gset G) g h) h
  ≔ let B ≔ BG G .carrier in
    let s ≔ shape G in
    calc
      gset_usym_act G (adjoint_gset G) g h
      = usym_mul G g (usym_mul G h (usym_inv G g)) by adjoint_gset_usym_act G g h
      = concat B s s s (concat B s s s h (inverse B s s g)) g
        by refl ((r ↦ concat B s s s r g) : USym G → USym G) (hab h (usym_inv G g))
      = h by gset_cancel_path B s s h g ∎

{` The G-set z ↦ (Ad_G(z) → USym G); for abelian G the identity of USym G
   is a fixed point of its action (transport in a function family,
   lem:trp-in-function-type). `}
def adjoint_to_usym_gset (G : Group) : GSet G
  ≔ z ↦ (Id (BG G .carrier) z z → USym G,
      pi_set (Id (BG G .carrier) z z) (_ ↦ USym G) (_ ↦ usym_set G))

def adjoint_to_usym_fix (G : Group) (hab : IsAbelian G) (g : USym G)
  : Id (USym G → USym G) (gset_usym_act G (adjoint_to_usym_gset G) g (u ↦ u)) (u ↦ u)
  ≔ let B ≔ BG G .carrier in
    let s ≔ shape G in
    funext (USym G) (_ ↦ USym G) (gset_usym_act G (adjoint_to_usym_gset G) g (u ↦ u)) (u ↦ u)
      (q ↦ calc
        gset_usym_act G (adjoint_to_usym_gset G) g (u ↦ u) q
        = transport B (_ ↦ USym G) s s g (transport B (z ↦ Id B z z) s s (inverse B s s g) q)
          by transport_function_family B (z ↦ Id B z z) (_ ↦ USym G) s s g (u ↦ u) q
        = transport B (z ↦ Id B z z) s s (inverse B s s g) q
          by transport_constant B (USym G) s s g (transport B (z ↦ Id B z z) s s (inverse B s s g) q)
        = q by adjoint_abelian_conj_trivial G hab (usym_inv G g) q ∎)

{` For abelian G: the invariant family z ↦ (Ad_G(z) → USym G) extending the
   identity consists of equivalences, giving Ad_G = triv_G(USym G). `}
def abelian_adjoint_family (G : Group) (hab : IsAbelian G) : (z : BG G .carrier) → Id (BG G .carrier) z z → USym G
  ≔ gset_fixed_point_extension G (adjoint_to_usym_gset G) (u ↦ u) (adjoint_to_usym_fix G hab)

def abelian_adjoint_family_equiv (G : Group) (hab : IsAbelian G) (z : BG G .carrier)
  : isEquiv (Id (BG G .carrier) z z) (USym G) (abelian_adjoint_family G hab z)
  ≔ let B ≔ BG G .carrier in
    let s ≔ abelian_adjoint_family G hab in
    connected_based_elim native_truncation B (bg_connected G) (shape G)
      (w ↦ isEquiv (Id B w w) (USym G) (s w)) (w ↦ isequiv_isprop (Id B w w) (USym G) (s w))
      (transport (USym G → USym G) (isEquiv (USym G) (USym G)) (u ↦ u) (s (shape G))
        (inverse (USym G → USym G) (s (shape G)) (u ↦ u)
          (gset_fixed_point_extension_beta G (adjoint_to_usym_gset G) (u ↦ u) (adjoint_to_usym_fix G hab)))
        (identity_equiv (USym G) .equiv))
      z

def abelian_adjoint_trivial_path (G : Group) (hab : IsAbelian G)
  : Id (GSet G) (adjoint_gset G) (gset_trivial G (USym G, usym_set G))
  ≔ gset_path_from_equivs G (adjoint_gset G) (gset_trivial G (USym G, usym_set G))
      (z ↦ (abelian_adjoint_family G hab z, abelian_adjoint_family_equiv G hab z))

{` Conversely, Ad_G = triv_G(USym G) makes conjugation trivial
   (equivariance of the transport, rem:map-of-Gsets), so G is abelian. `}
def adjoint_trivial_path_conj (G : Group) (e : Id (GSet G) (adjoint_gset G) (gset_trivial G (USym G, usym_set G)))
  (g h : USym G) : Id (USym G) (usym_mul G g (usym_mul G h (usym_inv G g))) h
  ≔ let T ≔ gset_trivial G (USym G, usym_set G) in
    let φ ≔ gset_path_equiv G (adjoint_gset G) T .map e (shape G) in
    let f ≔ gset_path_to_hom G (adjoint_gset G) T e in
    concat (USym G) (usym_mul G g (usym_mul G h (usym_inv G g))) (gset_usym_act G (adjoint_gset G) g h) h
      (inverse (USym G) (gset_usym_act G (adjoint_gset G) g h) (usym_mul G g (usym_mul G h (usym_inv G g)))
        (adjoint_gset_usym_act G g h))
      (equivalence_injective (USym G) (USym G) φ (gset_usym_act G (adjoint_gset G) g h) h
        (concat (USym G) (f (shape G) (gset_usym_act G (adjoint_gset G) g h)) (gset_usym_act G T g (f (shape G) h))
          (f (shape G) h)
          (gset_hom_equivariant G (adjoint_gset G) T f g h)
          (gset_trivial_act G (USym G, usym_set G) (shape G) (shape G) g (f (shape G) h))))

def adjoint_trivial_path_abelian (G : Group) (e : Id (GSet G) (adjoint_gset G) (gset_trivial G (USym G, usym_set G)))
  : IsAbelian G
  ≔ let B ≔ BG G .carrier in
    let s ≔ shape G in
    g h ↦ inverse (USym G) (usym_mul G h g) (usym_mul G g h)
      (calc
        concat B s s s g h
        = concat B s s s g (concat B s s s (concat B s s s (inverse B s s g) h) g)
          by refl (concat B s s s g)
            (inverse (USym G) (usym_mul G g (usym_mul G h (usym_inv G g))) h (adjoint_trivial_path_conj G e g h))
        = concat B s s s (concat B s s s g (concat B s s s (inverse B s s g) h)) g
          by inverse (USym G) (concat B s s s (concat B s s s g (concat B s s s (inverse B s s g) h)) g)
            (concat B s s s g (concat B s s s (concat B s s s (inverse B s s g) h) g))
            (concat_assoc B s s s s g (concat B s s s (inverse B s s g) h) g)
        = concat B s s s h g
          by refl ((r ↦ concat B s s s r g) : USym G → USym G) (concat_left_right_inverse B s s s g h) ∎)

def adjoint_trivial_iff_abelian (G : Group)
  : Product (IsAbelian G → Id (GSet G) (adjoint_gset G) (gset_trivial G (USym G, usym_set G)))
      (Id (GSet G) (adjoint_gset G) (gset_trivial G (USym G, usym_set G)) → IsAbelian G)
  ≔ (abelian_adjoint_trivial_path G, adjoint_trivial_path_abelian G)

{` Litmus: Σ_3 is not abelian, so Ad_{Σ_3} ≠ triv(USym Σ_3). `}
def sigma3_adjoint_not_trivial
  (e : Id (GSet (symmetric_group three)) (adjoint_gset (symmetric_group three))
         (gset_trivial (symmetric_group three) (USym (symmetric_group three), usym_set (symmetric_group three))))
  : Empty
  ≔ symmetric_group_three_not_abelian (adjoint_trivial_path_abelian (symmetric_group three) e)

{` xca:Ad-princ-trivial. If BG is contractible (G trivial), Ad_G(z) and
   P_G(z) are contractible, hence equivalent. `}
def trivial_adjoint_principal_path (G : Group) (h : IsTrivialGroup G)
  : Id (GSet G) (adjoint_gset G) (principal_gset G)
  ≔ let B ≔ BG G .carrier in
    let hp : isProp B ≔ contractible_prop B (native_contraction B h) in
    gset_path_from_equivs G (adjoint_gset G) (principal_gset G)
      (z ↦ (_ ↦ hp (shape G) z,
            contractible_map_equiv (Id B z z) (Id B (shape G) z) (_ ↦ hp (shape G) z)
              (book_contraction (Id B z z) (prop_paths_contractible B hp z z))
              (book_contraction (Id B (shape G) z) (prop_paths_contractible B hp (shape G) z))))

{` Conversely, transporting the invariant map z ↦ refl_z of Ad_G along
   Ad_G = P_G gives a contraction z ↦ (sh_G = z) of BG. `}
def adjoint_principal_path_trivial (G : Group) (e : Id (GSet G) (adjoint_gset G) (principal_gset G))
  : IsTrivialGroup G
  ≔ (shape G, z ↦ gset_path_to_hom G (adjoint_gset G) (principal_gset G) e z (refl z))

{` With the book's "G is the trivial group" (G = TG, module 506). `}
def adjoint_principal_iff_trivial (G : Group)
  : Product (Id Group G trivial_group → Id (GSet G) (adjoint_gset G) (principal_gset G))
      (Id (GSet G) (adjoint_gset G) (principal_gset G) → Id Group G trivial_group)
  ≔ (p ↦ trivial_adjoint_principal_path G (path_trivial_group G p),
     e ↦ trivial_group_path G (adjoint_principal_path_trivial G e))

{` Litmus: for the unit group Ad = P; for Σ_3 (not abelian, hence not
   trivial) Ad ≠ P. `}
def unit_group_adjoint_principal : Id (GSet unit_group) (adjoint_gset unit_group) (principal_gset unit_group)
  ≔ trivial_adjoint_principal_path unit_group unit_contraction

def sigma3_adjoint_not_principal
  (e : Id (GSet (symmetric_group three)) (adjoint_gset (symmetric_group three)) (principal_gset (symmetric_group three)))
  : Empty
  ≔ let S3 ≔ symmetric_group three in
    let c ≔ is_trivial_group_usym_contractible S3 (adjoint_principal_path_trivial S3 e) in
    let hp ≔ contractible_prop (USym S3) (native_contraction (USym S3) c) in
    symmetric_group_three_not_abelian (g h ↦ hp (usym_mul S3 g h) (usym_mul S3 h g))
