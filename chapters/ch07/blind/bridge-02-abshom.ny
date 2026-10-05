export "bridge-00-core"
export "02-abshom"
export "../../../src/728-monoid-hom-examples"
export "../../../src/729-pointwise-hom-products"
export "../../../src/730-inner-conjugation-abstr"
export "../../../src/731-conj-precompose-counterexample"

{` Bridges for absgroup.tex, sec:abshom (blind file 02-abshom). `}

{` def:abstrisfunctor and its footnote. `}
def bridge_def_abstrisfunctor_prop : blind_def_abstrisfunctor_prop
  ≔ G H ↦ (f ↦ is_abstract_hom_prop (bridge_ag7 G) (bridge_ag7 H) f, abstract_hom_set (bridge_ag7 G) (bridge_ag7 H))

{` xca:onlymult-hom. `}
def bridge_xca_onlymult_hom : blind_xca_onlymult_hom
  ≔ G H f hf ↦ (abstract_hom_preserves_unit (bridge_ag7 G) (bridge_ag7 H) f hf,
                s ↦ abstract_hom_preserves_inv (bridge_ag7 G) (bridge_ag7 H) f hf s)

{` rem:monoid-hom. `}
def bridge_def_monoid_hom (M N : BlindMonoid)
  : Id Type (BlindMonoidHom M N) (MonoidHom (bridge_def_monoid .map M) (bridge_def_monoid .map N))
  ≔ refl (BlindMonoidHom M N)

def bridge_rem_monoid_hom : blind_rem_monoid_hom
  ≔ G H f ↦ (abstract_hom_monoid_hom (bridge_ag7 G) (bridge_ag7 H) f, refl (f .fst))

def bridge_ft_monoid_hom : blind_ft_monoid_hom
  ≔ ((s s' ↦ monoid_footnote_map_mul s s', monoid_footnote_map_not_unit),
     u ↦ monoid_footnote_map_not_unit (two_element_monoid_zero_inverse (u .fst false.) (u .snd false.)))

{` xca:abshomcomposition. `}
def bridge_def_abshom_id (G : BlindAbsGroup) : Id (AbstractHom (bridge_ag7 G) (bridge_ag7 G)) (blind_abshom_id G) (abstract_hom_id (bridge_ag7 G))
  ≔ refl (abstract_hom_id (bridge_ag7 G))

def bridge_def_abshom_compose (G1 G2 G3 : BlindAbsGroup) (f0 : BlindAbsHom G1 G2) (f1 : BlindAbsHom G2 G3)
  : Id (AbstractHom (bridge_ag7 G1) (bridge_ag7 G3)) (blind_abshom_compose G1 G2 G3 f0 f1)
      (abstract_hom_compose (bridge_ag7 G1) (bridge_ag7 G2) (bridge_ag7 G3) f0 f1)
  ≔ refl (abstract_hom_compose (bridge_ag7 G1) (bridge_ag7 G2) (bridge_ag7 G3) f0 f1)

def bridge_xca_abshomcomposition : blind_xca_abshomcomposition
  ≔ (G1 G2 G3 f0 f1 ↦ abstract_hom_compose (bridge_ag7 G1) (bridge_ag7 G2) (bridge_ag7 G3) f0 f1 .snd,
     (G ↦ refl ((φ ↦ φ .fst) : AbstractHom (abstr G) (abstr G) → (USym G → USym G)) (abstr_hom_id G),
      (G0 G1 G2 f0 f1 ↦ refl ((φ ↦ φ .fst) : AbstractHom (abstr G0) (abstr G2) → (USym G0 → USym G2))
                          (abstr_hom_compose G0 G1 G2 f0 f1),
       (G ↦ group_endo_monoid G .laws,
        G ↦ abstract_endo_monoid (bridge_ag7 G) .laws))))

{` ex:conjhom. Identifications of abstract groups with the same carrier
   transport are equal (paths are isomorphisms, determined by their maps). `}
def bridge_ag_path_ext (G H : AbstractGroup) (p q : Id AbstractGroup G H)
  (h : (s : G .carrier) → Id (H .carrier) (p .carrier .trr s) (q .carrier .trr s))
  : Id (Id AbstractGroup G H) p q
  ≔ equivalence_injective (Id AbstractGroup G H) (AbstractIso G H) (abstract_group_path_iso_equiv G H) p q
      (abstract_iso_path G H (abstract_group_path_to_iso G H p) (abstract_group_path_to_iso G H q)
        (funext (G .carrier) (_ ↦ H .carrier) (s ↦ p .carrier .trr s) (s ↦ q .carrier .trr s) h))

def bridge_ex_conjhom_hom : blind_ex_conjhom_hom ≔ G g ↦ abstract_conj_mul (bridge_ag7 G) g

def bridge_ex_conjhom_post : blind_ex_conjhom_post
  ≔ G H g p hp f ↦
    let G' ≔ bridge_ag7 G in let H' ≔ bridge_ag7 H in
    let T : Id AbstractGroup G' G' → (H .carrier → G .carrier)
      ≔ q ↦ transport AbstractGroup (K ↦ AbstractHom H' K) G' G' q f .fst in
    let e : Id (Id AbstractGroup G' G') (refl bridge_ag7 p) (abstract_conj_path G' g)
      ≔ bridge_ag_path_ext G' G' (refl bridge_ag7 p) (abstract_conj_path G' g) hp in
    concat (H .carrier → G .carrier) (T (refl bridge_ag7 p)) (T (abstract_conj_path G' g)) (t ↦ blind_conj G g (f .fst t))
      (refl T e)
      (refl ((φ ↦ φ .fst) : AbstractHom H' G' → (H .carrier → G .carrier))
        (abstract_conj_transport_postcompose H' G' g f))

def bridge_ex_conjhom_pre_corrected : blind_ex_conjhom_pre_corrected
  ≔ G H h p hp f ↦
    let G' ≔ bridge_ag7 G in let H' ≔ bridge_ag7 H in
    let T : Id AbstractGroup H' H' → (H .carrier → G .carrier)
      ≔ q ↦ transport AbstractGroup (K ↦ AbstractHom K G') H' H' q f .fst in
    let e : Id (Id AbstractGroup H' H') (refl bridge_ag7 p) (abstract_conj_path H' h)
      ≔ bridge_ag_path_ext H' H' (refl bridge_ag7 p) (abstract_conj_path H' h) hp in
    concat (H .carrier → G .carrier) (T (refl bridge_ag7 p)) (T (abstract_conj_path H' h))
      (t ↦ f .fst (blind_conj H (H .inv h) t))
      (refl T e)
      (refl ((φ ↦ φ .fst) : AbstractHom H' G' → (H .carrier → G .carrier))
        (abstract_conj_transport_precompose H' G' h f))

{` The literal reading (precomposition with conj^h) is refuted: the
   counterexample of module 731 (abstr Σ₃, h a 3-cycle, f = id). `}
def bridge_ex_conjhom_pre_refuted (L : blind_ex_conjhom_pre) : Empty
  ≔ abstract_conj_transport_precompose_printed_fails
      (H K x f ↦ L (bridge_ag7_inv K) (bridge_ag7_inv H) x
        (refl bridge_ag7_inv (abstract_conj_path H x)) (s ↦ refl (abstract_conj H x s)) f)

def bridge_ex_conjhom_inner : blind_ex_conjhom_inner
  ≔ G g ↦ (refl ((φ ↦ φ .fst) : AbstractHom (abstr G) (abstr G) → (USym G → USym G))
             (abstr_conj_hom_is_abstract_conj G g),
           s ↦ inn_usym_acts_by_conjugation G g s)

{` xca:abs-homgroup: the literal statement (fixed H) is refuted by our
   counterexample (H trivial, G = abstr Σ₃); the corrected one is ours. `}
def bridge_xca_abs_homgroup_refuted (L : blind_xca_abs_homgroup) : Empty
  ≔ pointwise_products_hom_fixed_domain_fails
      (L (bridge_ag7_inv (abstr (symmetric_group three))) (bridge_ag7_inv unit_abstract_group) .snd)

def bridge_xca_abs_homgroup_corrected : blind_xca_abs_homgroup_corrected
  ≔ G ↦ (hab H f g ↦ abelian_pointwise_mul_hom (bridge_ag7 H) (bridge_ag7 G) hab f g,
         h ↦ square_hom_abelian (bridge_ag7 G) (h G (blind_abshom_id G) (blind_abshom_id G)))
