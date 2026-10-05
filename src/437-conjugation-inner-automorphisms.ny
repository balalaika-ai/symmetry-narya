export "431-homomorphism-remarks"

{` exa:conj-concrete and def:inner-autos (group.tex 1361-1408). `}

{` The group mkgroup(BG÷, y): the classifying type of G pointed at y. `}
def group_at (G : Group) (y : BG G .carrier) : Group ≔ mkgroup (BG G .carrier, y, bg_connected G, bg_groupoid G)

{` Binn(sh_G) ≡ G (record eta), and USym(mkgroup(BG÷, y)) ≡ (y = y) (the
   footnote of exa:conj-concrete). `}
def group_at_shape (G : Group) : Id Group (group_at G (shape G)) G ≔ refl G

def group_at_usym (G : Group) (y : BG G .carrier) : Id Type (USym (group_at G y)) (Id (BG G .carrier) y y)
  ≔ refl (Id (BG G .carrier) y y)

{` exa:conj-concrete: for p : sh_G = y, (id_BG, p⁻¹) : BG ≃* (BG÷, y) is a
   pointed equivalence, hence an isomorphism G ≅ mkgroup(BG÷, y) and an
   identification of groups (remark:groupsasunivalenttype). `}
def conj_pointed_map (G : Group) (y : BG G .carrier) (p : Id (BG G .carrier) (shape G) y)
  : BookPointedMap (BG G) (BG (group_at G y))
  ≔ (identity (BG G .carrier), inverse (BG G .carrier) (shape G) y p)

def conj_pointed_equiv (G : Group) (y : BG G .carrier) (p : Id (BG G .carrier) (shape G) y)
  : BookPointedEquiv (BG G) (BG (group_at G y))
  ≔ (conj_pointed_map G y p, identity_book_equiv (BG G .carrier) .equiv)

def conj_hom (G : Group) (y : BG G .carrier) (p : Id (BG G .carrier) (shape G) y) : GroupHom G (group_at G y)
  ≔ mkhom G (group_at G y) (conj_pointed_map G y p)

def conj_iso (G : Group) (y : BG G .carrier) (p : Id (BG G .carrier) (shape G) y) : GroupIso G (group_at G y)
  ≔ (conj_hom G y p, identity_book_equiv (BG G .carrier) .equiv)

def conj_group_path (G : Group) (y : BG G .carrier) (p : Id (BG G .carrier) (shape G) y) : Id Group G (group_at G y)
  ≔ group_path_from_iso G (group_at G y) (conj_iso G y p)

{` USym(mkhom(id_BG, p⁻¹)) = Ω(id_BG, p⁻¹) is conjugation g ↦ p g p⁻¹ in the
   book's notation (first p⁻¹, then g, then p; loop_conjugate of module 85
   in concatenation order). The book obtains this by path induction on p;
   here it is inverse_inverse (Ω(id, p⁻¹)(g) = p⁻¹⁻¹ ... literally). `}
def conj_usym (G : Group) (y : BG G .carrier) (p : Id (BG G .carrier) (shape G) y) (g : USym G)
  : Id (Id (BG G .carrier) y y) (usym_hom G (group_at G y) (conj_hom G y p) g)
      (loop_conjugate (BG G .carrier) (shape G) y p g)
  ≔ let A ≔ BG G .carrier in
    refl (concat A y (shape G) y (inverse A (shape G) y p))
      (refl (concat A (shape G) (shape G) y g) (inverse_inverse A (shape G) y p))

def conj_usym_function (G : Group) (y : BG G .carrier) (p : Id (BG G .carrier) (shape G) y)
  : Id (USym G → Id (BG G .carrier) y y) (usym_hom G (group_at G y) (conj_hom G y p))
      (g ↦ loop_conjugate (BG G .carrier) (shape G) y p g)
  ≔ funext (USym G) (_ ↦ Id (BG G .carrier) y y) (usym_hom G (group_at G y) (conj_hom G y p))
      (g ↦ loop_conjugate (BG G .carrier) (shape G) y p g) (conj_usym G y p)

{` It is transport in the family z ↦ (z = z) along p, hence an
   equivalence (sh_G = sh_G) ≃ (y = y) (cf. xca:trp-in-a/x=b/x). `}
def conj_usym_transport (G : Group) (y : BG G .carrier) (p : Id (BG G .carrier) (shape G) y) (g : USym G)
  : Id (Id (BG G .carrier) y y) (transport (BG G .carrier) (z ↦ Id (BG G .carrier) z z) (shape G) y p g)
      (usym_hom G (group_at G y) (conj_hom G y p) g)
  ≔ let A ≔ BG G .carrier in
    concat (Id A y y) (transport A (z ↦ Id A z z) (shape G) y p g) (loop_conjugate A (shape G) y p g)
      (usym_hom G (group_at G y) (conj_hom G y p) g)
      (loop_transport_conjugate A (shape G) y p g)
      (inverse (Id A y y) (usym_hom G (group_at G y) (conj_hom G y p) g) (loop_conjugate A (shape G) y p g)
        (conj_usym G y p g))

def conj_usym_equiv (G : Group) (y : BG G .carrier) (p : Id (BG G .carrier) (shape G) y)
  : Equiv (USym G) (Id (BG G .carrier) y y)
  ≔ equiv_change_map (USym G) (Id (BG G .carrier) y y)
      (transport_equiv (USym G) (Id (BG G .carrier) y y) (refl ((z ↦ Id (BG G .carrier) z z) : BG G .carrier → Type) p))
      (usym_hom G (group_at G y) (conj_hom G y p)) (conj_usym_transport G y p)

{` The special case y ≡ sh_G: conjugation by p : USym G is g ↦ p·g·p⁻¹ in
   usym_mul notation, judgmentally. `}
def conj_at_shape_usym (G : Group) (p g : USym G)
  : Id (USym G) (usym_hom G G (conj_hom G (shape G) p) g) (usym_mul G (usym_mul G p g) (usym_inv G p))
  ≔ conj_usym G (shape G) p g

{` Litmus: in an abelian group conjugation is trivial. `}
def conj_abelian_trivial (G : Group) (hab : IsAbelian G) (p g : USym G)
  : Id (USym G) (usym_hom G G (conj_hom G (shape G) p) g) g
  ≔ let L ≔ usym_abstract_laws G in
    calc
      usym_hom G G (conj_hom G (shape G) p) g
      = usym_mul G (usym_mul G p g) (usym_inv G p) by conj_at_shape_usym G p g
      = usym_mul G (usym_mul G g p) (usym_inv G p)
        by refl ((q ↦ usym_mul G q (usym_inv G p)) : USym G → USym G) (hab p g)
      = usym_mul G g (usym_mul G p (usym_inv G p))
        by inverse (USym G) (usym_mul G g (usym_mul G p (usym_inv G p))) (usym_mul G (usym_mul G g p) (usym_inv G p))
          (L .assoc g p (usym_inv G p))
      = usym_mul G g (usym_unit G) by refl (usym_mul G g) (L .inv_right p)
      = g by L .unit_right g ∎

{` Litmus: in Σ_3 conjugation by τ = (0 1) moves σ = (1 2). `}
def loop_conjugate_fixed_commutes_right (A : Type) (a : A) (g h : Id A a a)
  (e : Id (Id A a a) (concat A a a a (inverse A a a h) (concat A a a a g h)) g)
  : Id (Id A a a) (concat A a a a h g) (concat A a a a g h)
  ≔ let L ≔ Id A a a in
    calc
      concat A a a a h g
      = concat A a a a h (concat A a a a (inverse A a a h) (concat A a a a g h))
        by refl (concat A a a a h) (inverse L (concat A a a a (inverse A a a h) (concat A a a a g h)) g e)
      = concat A a a a (concat A a a a h (inverse A a a h)) (concat A a a a g h)
        by inverse L (concat A a a a (concat A a a a h (inverse A a a h)) (concat A a a a g h))
          (concat A a a a h (concat A a a a (inverse A a a h) (concat A a a a g h)))
          (concat_assoc A a a a a h (inverse A a a h) (concat A a a a g h))
      = concat A a a a (refl a) (concat A a a a g h)
        by refl ((q ↦ concat A a a a q (concat A a a a g h)) : L → L) (concat_inverse_right A a a h)
      = concat A a a a g h by concat_1p A a a (concat A a a a g h) ∎

def conj_sigma3_moves_sigma
  (e : Id (USym (symmetric_group three))
    (usym_hom (symmetric_group three) (symmetric_group three) (conj_hom (symmetric_group three) (shape (symmetric_group three)) sigma3_tau)
      sigma3_sigma)
    sigma3_sigma) : Empty
  ≔ let S ≔ symmetric_group three in let A ≔ BG S .carrier in let a ≔ shape S in
    sigma3_tau_sigma_noncommuting
      (loop_conjugate_fixed_commutes_right A a sigma3_sigma sigma3_tau
        (concat (USym S) (loop_conjugate A a a sigma3_tau sigma3_sigma)
          (usym_hom S S (conj_hom S a sigma3_tau) sigma3_sigma) sigma3_sigma
          (inverse (USym S) (usym_hom S S (conj_hom S a sigma3_tau) sigma3_sigma)
            (loop_conjugate A a a sigma3_tau sigma3_sigma) (conj_usym S a sigma3_tau sigma3_sigma))
          e))

{` def:inner-autos. Binn : BG →* BAut(G), y ↦ mkgroup(BG÷, y), with the
   truncation component ‖G = mkgroup(BG÷, y)‖ from connectedness of BG and
   the identifications of exa:conj-concrete ("the codomain of Binn is
   correct"). The book's p_inn ≔ refl_G becomes the component path whose
   first component is refl_G (judgmentally); the truncation components
   differ as terms of a proposition. `}
def inn_component_witness (G : Group) (y : BG G .carrier) : Mere (Id Group G (group_at G y))
  ≔ mere_rec (Id (BG G .carrier) (shape G) y) (Mere (Id Group G (group_at G y))) (mere_isprop (Id Group G (group_at G y)))
      (p ↦ mere (Id Group G (group_at G y)) (conj_group_path G y p)) (bg_connected G .snd (shape G) y)

def inn_classifying_map (G : Group) (y : BG G .carrier) : BG (group_aut G) .carrier
  ≔ (group_at G y, inn_component_witness G y)

def inn_point (G : Group)
  : Id (BG (group_aut G) .carrier) (shape (group_aut G)) (inn_classifying_map G (shape G))
  ≔ component_path Group G (component_point Group G) (inn_classifying_map G (shape G)) (refl G)

def inn (G : Group) : GroupHom G (group_aut G) ≔ mkhom G (group_aut G) (inn_classifying_map G, inn_point G)

{` Litmus: Binn(y) is mkgroup(BG÷, y), Binn(sh_G) is G, the pointing path
   has first component refl_G, all judgmentally. `}
def inn_value (G : Group) (y : BG G .carrier)
  : Id Group (hom_function G (group_aut G) (inn G) y .fst) (group_at G y)
  ≔ refl (group_at G y)

def inn_value_shape (G : Group) : Id Group (hom_function G (group_aut G) (inn G) (shape G) .fst) G
  ≔ refl G

def inn_point_fst (G : Group) : Id (Id Group G G) (hom_point G (group_aut G) (inn G) .fst) (refl G)
  ≔ refl (refl G)

{` USym(inn)(g), as an identification G = G in Group, is ap_{y ↦ mkgroup(BG÷,y)}(g);
   its shape component is g itself (judgmentally). `}
def inn_usym_fst (G : Group) (g : USym G)
  : Id (Id Group G G) (usym_hom G (group_aut G) (inn G) g .fst) (refl (group_at G) g)
  ≔ let P ≔ NativeComponent Group G in
    let k ≔ inn_classifying_map G in
    concat (Id Group G G) (usym_hom G (group_aut G) (inn G) g .fst)
      (pointed_loop_conjugate Group G G (refl G) (refl (group_at G) g))
      (refl (group_at G) g)
      (map_path_loop_conjugate P Group (u ↦ u .fst) (component_point Group G) (k (shape G)) (inn_point G) (refl k g))
      (loop_conjugate_at_refl Group G (refl (group_at G) g))

def inn_group_path_shape (G : Group) (g : USym G)
  : Id (USym G) (refl (group_at G) g .classifying .point) g
  ≔ refl g

{` Litmus: transporting a symmetry h of G along the identification
   USym(inn)(g) : G = G (in the family USym over Group) is conjugation
   h ↦ g·h·g⁻¹. Hence inn of an abelian group acts trivially, and in Σ_3
   USym(inn)(τ) is not the neutral element (it moves σ). `}
def inn_usym_acts_by_conjugation (G : Group) (g h : USym G)
  : Id (USym G) (transport Group USym G G (usym_hom G (group_aut G) (inn G) g .fst) h)
      (usym_mul G (usym_mul G g h) (usym_inv G g))
  ≔ concat (USym G) (transport Group USym G G (usym_hom G (group_aut G) (inn G) g .fst) h)
      (transport Group USym G G (refl (group_at G) g) h)
      (usym_mul G (usym_mul G g h) (usym_inv G g))
      (J (Id Group G G) (usym_hom G (group_aut G) (inn G) g .fst)
        (r _ ↦ Id (USym G) (transport Group USym G G (usym_hom G (group_aut G) (inn G) g .fst) h)
          (transport Group USym G G r h))
        (refl (transport Group USym G G (usym_hom G (group_aut G) (inn G) g .fst) h))
        (refl (group_at G) g) (inn_usym_fst G g))
      (loop_transport_conjugate (BG G .carrier) (shape G) (shape G) g h)

def inn_abelian_acts_trivially (G : Group) (hab : IsAbelian G) (g h : USym G)
  : Id (USym G) (transport Group USym G G (usym_hom G (group_aut G) (inn G) g .fst) h) h
  ≔ concat (USym G) (transport Group USym G G (usym_hom G (group_aut G) (inn G) g .fst) h)
      (usym_mul G (usym_mul G g h) (usym_inv G g)) h
      (inn_usym_acts_by_conjugation G g h)
      (concat (USym G) (usym_mul G (usym_mul G g h) (usym_inv G g)) (usym_hom G G (conj_hom G (shape G) g) h) h
        (inverse (USym G) (usym_hom G G (conj_hom G (shape G) g) h) (usym_mul G (usym_mul G g h) (usym_inv G g))
          (conj_at_shape_usym G g h))
        (conj_abelian_trivial G hab g h))

def inn_sigma3_tau_nontrivial
  (e : Id (USym (group_aut (symmetric_group three)))
    (usym_hom (symmetric_group three) (group_aut (symmetric_group three)) (inn (symmetric_group three)) sigma3_tau)
    (usym_unit (group_aut (symmetric_group three)))) : Empty
  ≔ let S ≔ symmetric_group three in
    let r ≔ usym_hom S (group_aut S) (inn S) sigma3_tau .fst in
    let e1 : Id (Id Group S S) r (refl S)
      ≔ refl ((q ↦ q .fst) : USym (group_aut S) → Id Group S S) e in
    let t1 : Id (USym S) (transport Group USym S S r sigma3_sigma) (transport Group USym S S (refl S) sigma3_sigma)
      ≔ J (Id Group S S) r (q _ ↦ Id (USym S) (transport Group USym S S r sigma3_sigma) (transport Group USym S S q sigma3_sigma))
          (refl (transport Group USym S S r sigma3_sigma)) (refl S) e1 in
    conj_sigma3_moves_sigma
      (calc
        usym_hom S S (conj_hom S (shape S) sigma3_tau) sigma3_sigma
        = usym_mul S (usym_mul S sigma3_tau sigma3_sigma) (usym_inv S sigma3_tau)
          by conj_at_shape_usym S sigma3_tau sigma3_sigma
        = transport Group USym S S r sigma3_sigma
          by inverse (USym S) (transport Group USym S S r sigma3_sigma)
            (usym_mul S (usym_mul S sigma3_tau sigma3_sigma) (usym_inv S sigma3_tau))
            (inn_usym_acts_by_conjugation S sigma3_tau sigma3_sigma)
        = transport Group USym S S (refl S) sigma3_sigma by t1
        = sigma3_sigma by transport_refl Group USym S sigma3_sigma ∎)
