export "01-monoids"
export "../../../src/437-conjugation-inner-automorphisms"

{` Blind statements, chapter 7, section "Abstract homomorphisms". `}

{` def:abstrisfunctor. `}
def BlindIsAbsHom (G H : BlindAbsGroup) (f : G .carrier → H .carrier) : Type
  ≔ (s s' : G .carrier) → Id (H .carrier) (f (G .mul s s')) (H .mul (f s) (f s'))

def BlindAbsHom (G H : BlindAbsGroup) : Type ≔ Σ (G .carrier → H .carrier) (BlindIsAbsHom G H)

{` abstr : Hom(G,H) → Hom^abs(abstr G, abstr H), f ↦ (USym f, !) (lem:grouphomomaxioms). `}
def blind_abstr_hom (G H : Group) (f : GroupHom G H) : BlindAbsHom (blind_abstr G) (blind_abstr H)
  ≔ (usym_hom G H f, s s' ↦ usym_hom_mul G H f s s')

{` def:abstrisfunctor, footnote: the hom condition is a proposition, hence
   Hom^abs(G,H) is a set ("the set of homomorphisms"). `}
def blind_def_abstrisfunctor_prop : Type
  ≔ (G H : BlindAbsGroup) → Product ((f : G .carrier → H .carrier) → isProp (BlindIsAbsHom G H f)) (isSet (BlindAbsHom G H))

{` xca:onlymult-hom. `}
def blind_xca_onlymult_hom : Type
  ≔ (G H : BlindAbsGroup) (f : G .carrier → H .carrier) (hf : BlindIsAbsHom G H f)
    → Product (Id (H .carrier) (f (G .unit)) (H .unit))
        ((s : G .carrier) → Id (H .carrier) (f (G .inv s)) (H .inv (f s)))

{` rem:monoid-hom: homomorphisms of monoids preserve the unit and the multiplication. `}
def BlindMonoidHom (M N : BlindMonoid) : Type
  ≔ Σ (M .carrier → N .carrier) (f ↦
      Product (Id (N .carrier) (f (M .unit)) (N .unit))
        ((s s' : M .carrier) → Id (N .carrier) (f (M .mul s s')) (N .mul (f s) (f s'))))

{` rem:monoid-hom, claim: an abstract homomorphism defines a homomorphism of
   the underlying monoids (with the same underlying function). `}
def blind_rem_monoid_hom : Type
  ≔ (G H : BlindAbsGroup) (f : BlindAbsHom G H)
    → Σ (BlindMonoidHom (blind_ag_monoid G) (blind_ag_monoid H)) (k ↦
        Id (G .carrier → H .carrier) (k .fst) (f .fst))

{` ft:monoid-hom: M = {1, 0} with ordinary multiplication (Bool, true = 1,
   and), the trivial monoid 1 (Unit) and h(-) ≔ 0 preserve multiplication but
   not the unit; M admits no inverse operation. `}
def blind_bool_mul (a b : Bool) : Bool ≔ match a [ false. ↦ false. | true. ↦ b ]

def blind_bool_monoid : BlindMonoid
  ≔ (Bool, true., blind_bool_mul,
     (bool_set,
      ([ false. ↦ (refl (false. : Bool), refl (false. : Bool)) | true. ↦ (refl (true. : Bool), refl (true. : Bool)) ],
       [ false. ↦ _ _ ↦ refl (false. : Bool) | true. ↦ b c ↦ refl (blind_bool_mul b c) ])))

def blind_unit_monoid : BlindMonoid
  ≔ (Unit, star., (_ _ ↦ star.),
     ((x y ↦ prop_is_set Unit unit_prop x y),
      ([ star. ↦ (refl (star. : Unit), refl (star. : Unit)) ], (_ _ _ ↦ refl (star. : Unit)))))

def blind_ft_monoid_hom : Type
  ≔ Product
      (Product
        ((s s' : Unit) → Id Bool ((_ ↦ false.) (blind_unit_monoid .mul s s'))
          (blind_bool_monoid .mul ((_ ↦ false.) s) ((_ ↦ false.) s')))
        (Not (Id Bool ((_ ↦ false.) (star. : Unit)) true.)))
      (Not (Σ (Bool → Bool) (iota ↦ BlindInverseLaw Bool true. blind_bool_mul iota)))

{` Identity and composite abstract homomorphisms (the composite needs the
   one-line proof of xca:abshomcomposition (1)). `}
def blind_abshom_id (G : BlindAbsGroup) : BlindAbsHom G G
  ≔ (s ↦ s, s s' ↦ refl (G .mul s s'))

def blind_abshom_compose (G1 G2 G3 : BlindAbsGroup) (f0 : BlindAbsHom G1 G2) (f1 : BlindAbsHom G2 G3)
  : BlindAbsHom G1 G3
  ≔ (s ↦ f1 .fst (f0 .fst s),
     s s' ↦ concat (G3 .carrier) (f1 .fst (f0 .fst (G1 .mul s s'))) (f1 .fst (G2 .mul (f0 .fst s) (f0 .fst s')))
       (G3 .mul (f1 .fst (f0 .fst s)) (f1 .fst (f0 .fst s')))
       (refl (f1 .fst) (f0 .snd s s')) (f1 .snd (f0 .fst s) (f0 .fst s')))

{` xca:abshomcomposition: composites of abstract homomorphisms are
   homomorphisms; abstr(id_G) = id and abstr(f1 f0) = abstr(f1) abstr(f0)
   (as underlying functions, which determine homomorphisms); Hom(G,G) and
   Hom^abs(G,G) are monoids under composition (product f1 · f0 ≔ f1 ∘ f0). `}
def blind_xca_abshomcomposition : Type
  ≔ Product
      ((G1 G2 G3 : BlindAbsGroup) (f0 : BlindAbsHom G1 G2) (f1 : BlindAbsHom G2 G3)
        → BlindIsAbsHom G1 G3 (s ↦ f1 .fst (f0 .fst s)))
    (Product
      ((G : Group) → Id (USym G → USym G) (blind_abstr_hom G G (group_hom_id G) .fst) (blind_abshom_id (blind_abstr G) .fst))
    (Product
      ((G0 G1 G2 : Group) (f0 : GroupHom G0 G1) (f1 : GroupHom G1 G2)
        → Id (USym G0 → USym G2) (blind_abstr_hom G0 G2 (group_hom_compose G0 G1 G2 f0 f1) .fst)
            (s ↦ blind_abstr_hom G1 G2 f1 .fst (blind_abstr_hom G0 G1 f0 .fst s)))
      (Product
        ((G : Group) → BlindMonoidLaws (GroupHom G G) (group_hom_id G) (f1 f0 ↦ group_hom_compose G G G f0 f1))
        ((G : BlindAbsGroup) → BlindMonoidLaws (BlindAbsHom G G) (blind_abshom_id G) (f1 f0 ↦ blind_abshom_compose G G G f0 f1)))))

{` ex:conjhom. (1) conj^g is an abstract homomorphism G → G (xca:conj).
   (2) Transport along any identification p : G = G whose underlying
   transport is conj^g (as produced from the isomorphism conj^g,
   rem:abs-iso) acts on Hom^abs(H,G) by postcomposition with conj^g. `}
def blind_ex_conjhom_hom : Type
  ≔ (G : BlindAbsGroup) (g : G .carrier) → BlindIsAbsHom G G (blind_conj G g)

def blind_ex_conjhom_post : Type
  ≔ (G H : BlindAbsGroup) (g : G .carrier) (p : Id BlindAbsGroup G G)
    (hp : (s : G .carrier) → Id (G .carrier) (transport BlindAbsGroup (K ↦ K .carrier) G G p s) (blind_conj G g s))
    (f : BlindAbsHom H G)
    → Id (H .carrier → G .carrier) (transport BlindAbsGroup (K ↦ BlindAbsHom H K) G G p f .fst)
        (t ↦ blind_conj G g (f .fst t))

{` (3) "Similarly for elements in H, giving rise to precomposition with
   conjugation by h": transport along conj^h : H = H in the first argument.
   Literal reading: precomposition with conj^h. Corrected: transport in the
   contravariant argument is precomposition with the inverse, conj^{h⁻¹}. `}
def blind_ex_conjhom_pre : Type
  ≔ (G H : BlindAbsGroup) (h : H .carrier) (p : Id BlindAbsGroup H H)
    (hp : (s : H .carrier) → Id (H .carrier) (transport BlindAbsGroup (K ↦ K .carrier) H H p s) (blind_conj H h s))
    (f : BlindAbsHom H G)
    → Id (H .carrier → G .carrier) (transport BlindAbsGroup (K ↦ BlindAbsHom K G) H H p f .fst)
        (t ↦ f .fst (blind_conj H h t))

def blind_ex_conjhom_pre_corrected : Type
  ≔ (G H : BlindAbsGroup) (h : H .carrier) (p : Id BlindAbsGroup H H)
    (hp : (s : H .carrier) → Id (H .carrier) (transport BlindAbsGroup (K ↦ K .carrier) H H p s) (blind_conj H h s))
    (f : BlindAbsHom H G)
    → Id (H .carrier → G .carrier) (transport BlindAbsGroup (K ↦ BlindAbsHom K G) H H p f .fst)
        (t ↦ f .fst (blind_conj H (H .inv h) t))

{` (4) abstr(Binn)(g) = Ω(id_BG, g⁻¹) = conj^g: the symmetry Ω(id_BG, g⁻¹)
   (USym of the homomorphism (id, g⁻¹) : G → mkgroup(BG÷, sh_G) ≡ G,
   conj_hom of module 437) is conj^g, and the identification of abstract
   groups obtained by applying abstr to Binn(g) : G = G has transport conj^g. `}
def blind_ex_conjhom_inner : Type
  ≔ (G : Group) (g : USym G)
    → Product
        (Id (USym G → USym G) (usym_hom G G (conj_hom G (shape G) g)) (blind_conj (blind_abstr G) g))
        ((s : USym G) → Id (USym G)
          (transport BlindAbsGroup (K ↦ K .carrier) (blind_abstr G) (blind_abstr G)
            (map_path Group BlindAbsGroup blind_abstr G G (usym_hom G (group_aut G) (inn G) g .fst)) s)
          (blind_conj (blind_abstr G) g s))

{` xca:abs-homgroup, literally for fixed H and G: G is abelian iff every
   pointwise product of homomorphisms H → G is a homomorphism. This fails
   for H trivial; the corrected version quantifies over all H. `}
def BlindAbsIsAbelian (G : BlindAbsGroup) : Type
  ≔ (g h : G .carrier) → Id (G .carrier) (G .mul g h) (G .mul h g)

def blind_xca_abs_homgroup : Type
  ≔ (G H : BlindAbsGroup)
    → Product (BlindAbsIsAbelian G
                → (f g : BlindAbsHom H G) → BlindIsAbsHom H G (t ↦ G .mul (f .fst t) (g .fst t)))
        (((f g : BlindAbsHom H G) → BlindIsAbsHom H G (t ↦ G .mul (f .fst t) (g .fst t)))
          → BlindAbsIsAbelian G)

def blind_xca_abs_homgroup_corrected : Type
  ≔ (G : BlindAbsGroup)
    → Product (BlindAbsIsAbelian G
                → (H : BlindAbsGroup) (f g : BlindAbsHom H G) → BlindIsAbsHom H G (t ↦ G .mul (f .fst t) (g .fst t)))
        (((H : BlindAbsGroup) (f g : BlindAbsHom H G) → BlindIsAbsHom H G (t ↦ G .mul (f .fst t) (g .fst t)))
          → BlindAbsIsAbelian G)
