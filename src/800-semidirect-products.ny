export "436-maps-from-classifying-types"

{` Chapter 8 (congp.tex), section "Semidirect products" (sec:Semidirect-products),
   lines 1–60 and 277–289: the semidirect product G ⋉ H of a group G and an
   action H : BG → Group of G in groups (def:action), the homomorphisms
   p, s, j, the trivial action, and actions on a fixed group given by
   homomorphisms G → Aut(H).

   Conventions as in chapter 4: concat p q follows p, then q; the book's
   composite q · p is concat p q; usym_mul G g h = g · h = concat h g. The
   acted-on group of H is H(sh_G); the book's "(sh_G, sh_H)" is
   (sh_G, sh_{H(sh_G)}). `}

{` def:semidirect-product. The classifying type Σ_{t:BG} BH(t) and its
   base point (sh_G, sh_{H(sh_G)}). `}
def semidirect_classifying_type (G : Group) (H : BG G .carrier → Group) : Type
  ≔ Σ (BG G .carrier) (t ↦ BG (H t) .carrier)

def semidirect_shape (G : Group) (H : BG G .carrier → Group) : semidirect_classifying_type G H
  ≔ (shape G, shape (H (shape G)))

{` Footnote of def:semidirect-product: Σ_{t:BG} BH(t) is a groupoid by
   lem:level-n-utils (sum), and connected by xca:connected-trivia-1. `}
def semidirect_classifying_groupoid (G : Group) (H : BG G .carrier → Group)
  : isGroupoid (semidirect_classifying_type G H)
  ≔ hlevel_to_groupoid (semidirect_classifying_type G H)
      (hlevel_sigma (suc. (suc. (suc. zero.))) (BG G .carrier) (t ↦ BG (H t) .carrier)
        (groupoid_to_hlevel (BG G .carrier) (bg_groupoid G))
        (t ↦ groupoid_to_hlevel (BG (H t) .carrier) (bg_groupoid (H t))))

def semidirect_classifying_connected (G : Group) (H : BG G .carrier → Group)
  : Connected (semidirect_classifying_type G H)
  ≔ native_connected_sigma (BG G .carrier) (t ↦ BG (H t) .carrier) (bg_connected G)
      (t ↦ bg_connected (H t))

{` def:semidirect-product. G ⋉ H ≔ mkgroup (Σ_{t:BG} BH(t)), pointed at
   (sh_G, sh_{H(sh_G)}). `}
def semidirect_product (G : Group) (H : BG G .carrier → Group) : Group
  ≔ mkgroup (semidirect_classifying_type G H, semidirect_shape G H,
      semidirect_classifying_connected G H, semidirect_classifying_groupoid G H)

def semidirect_product_classifying (G : Group) (H : BG G .carrier → Group)
  : Id Pointed (BG (semidirect_product G H))
      (Σ (BG G .carrier) (t ↦ BG (H t) .carrier), (shape G, shape (H (shape G))))
  ≔ refl (BG (semidirect_product G H))

{` "If the action of G is trivial, then H(t) ≡ H(sh_G) for all t, so
   G ⋉ H ≡ G × H(sh_G)". With the trivial action t ↦ K the pointed
   classifying types (Σ vs Product = Σ over a constant family), the
   symmetries and their multiplication agree judgmentally; the two groups
   differ only in the proofs of connectedness and of being a groupoid
   (connected_sigma vs connected_product), which are propositions, so the
   groups are identified by a path whose carrier and point components
   are refl. `}
def semidirect_trivial_classifying (G K : Group)
  : Id Pointed (BG (semidirect_product G (_ ↦ K))) (BG (product_group G K))
  ≔ refl (BG (product_group G K))

def semidirect_trivial_usym (G K : Group)
  : Id Type (USym (semidirect_product G (_ ↦ K))) (USym (product_group G K))
  ≔ refl (USym (product_group G K))

def semidirect_trivial_usym_mul (G K : Group) (g h : USym (product_group G K))
  : Id (USym (product_group G K)) (usym_mul (semidirect_product G (_ ↦ K)) g h) (usym_mul (product_group G K) g h)
  ≔ refl (usym_mul (product_group G K) g h)

def semidirect_trivial_product_path (G K : Group)
  : Id Group (semidirect_product G (_ ↦ K)) (product_group G K)
  ≔ (classifying ≔
      (refl (BG (product_group G K) .carrier), refl (shape G, shape K),
       connected_prop (BG (product_group G K) .carrier) (semidirect_classifying_connected G (_ ↦ K))
         (bg_connected (product_group G K)),
       isgroupoid_isprop (BG (product_group G K) .carrier) (semidirect_classifying_groupoid G (_ ↦ K))
         (bg_groupoid (product_group G K))))

{` "If the group being acted on is fixed, say H : Group, then an action of G
   on H is given by a homomorphism from G to Aut(H)." A homomorphism
   φ : G → Aut(H) = Aut_Group(H) (group_aut, module 402) gives the action
   t ↦ Bφ(t) (forgetting the component), together with the identification
   H = H(sh_G) given by the pointing path of Bφ. `}
def hom_aut_action (G H : Group) (φ : GroupHom G (group_aut H)) : BG G .carrier → Group
  ≔ t ↦ hom_function G (group_aut H) φ t .fst

def hom_aut_action_point (G H : Group) (φ : GroupHom G (group_aut H))
  : Id Group H (hom_aut_action G H φ (shape G))
  ≔ hom_point G (group_aut H) φ .fst

{` Conversely every action H' : BG → Group together with an identification
   H = H'(sh_G) arises from a unique homomorphism G → Aut(H): the two types
   are equivalent (xca:ptd-conn-to-comp, module 436, BG being connected). `}
def hom_aut_action_equiv (G H : Group)
  : Equiv (GroupHom G (group_aut H)) (Σ (BG G .carrier → Group) (A ↦ Id Group H (A (shape G))))
  ≔ quasi_inverse_equiv (GroupHom G (group_aut H)) (BookPointedMap (BG G) (Group, H))
      (φ ↦ component_project (BG G) Group H (hom_B G (group_aut H) φ))
      (k ↦ mkhom G (group_aut H) (component_lift (BG G) (bg_connected G) Group H k))
      (φ ↦ (classifying_map ≔ component_lift_project (BG G) (bg_connected G) Group H (hom_B G (group_aut H) φ)))
      (k ↦ component_project_lift (BG G) (bg_connected G) Group H k)

def hom_aut_action_equiv_map (G H : Group) (φ : GroupHom G (group_aut H))
  : Id (Σ (BG G .carrier → Group) (A ↦ Id Group H (A (shape G))))
      (hom_aut_action_equiv G H .map φ) (hom_aut_action G H φ, hom_aut_action_point G H φ)
  ≔ refl (hom_aut_action G H φ, hom_aut_action_point G H φ)

{` The semidirect product of G with H along φ : G → Aut(H). `}
def semidirect_product_hom (G H : Group) (φ : GroupHom G (group_aut H)) : Group
  ≔ semidirect_product G (hom_aut_action G H φ)

{` Lines 277–282. p ≔ mkgroup fst : G ⋉ H → G, s : G → G ⋉ H,
   t ↦ (t, sh_{H(t)}), and j : H(sh_G) → G ⋉ H, u ↦ (sh_G, u), all
   pointed by reflexivity ("made from basepoint-preserving maps"). `}
def semidirect_projection (G : Group) (H : BG G .carrier → Group) : GroupHom (semidirect_product G H) G
  ≔ mkhom (semidirect_product G H) G (u ↦ u .fst, refl (shape G))

def semidirect_section (G : Group) (H : BG G .carrier → Group) : GroupHom G (semidirect_product G H)
  ≔ mkhom G (semidirect_product G H) (t ↦ (t, shape (H t)), refl (semidirect_shape G H))

def semidirect_inclusion (G : Group) (H : BG G .carrier → Group)
  : GroupHom (H (shape G)) (semidirect_product G H)
  ≔ mkhom (H (shape G)) (semidirect_product G H) (u ↦ (shape G, u), refl (semidirect_shape G H))

{` "The map s is a section of p in the sense that p ∘ s = id_G." The
   underlying functions agree judgmentally; the pointing paths are
   concat refl refl and refl. `}
def semidirect_projection_section (G : Group) (H : BG G .carrier → Group)
  : Id (GroupHom G G)
      (group_hom_compose G (semidirect_product G H) G (semidirect_section G H) (semidirect_projection G H))
      (group_hom_id G)
  ≔ (classifying_map ≔
      (refl (identity (BG G .carrier)), concat_p1 (BG G .carrier) (shape G) (shape G) (refl (shape G))))

def semidirect_projection_section_usym (G : Group) (H : BG G .carrier → Group) (g : USym G)
  : Id (USym G)
      (usym_hom (semidirect_product G H) G (semidirect_projection G H)
        (usym_hom G (semidirect_product G H) (semidirect_section G H) g)) g
  ≔ let GH ≔ semidirect_product G H in
    let s ≔ semidirect_section G H in
    let p ≔ semidirect_projection G H in
    calc
      usym_hom GH G p (usym_hom G GH s g) = usym_hom G G (group_hom_compose G GH G s p) g
        by inverse (USym G) (usym_hom G G (group_hom_compose G GH G s p) g) (usym_hom GH G p (usym_hom G GH s g))
             (usym_hom_compose G GH G s p (refl g))
      = usym_hom G G (group_hom_id G) g
        by refl ((k ↦ usym_hom G G k g) : GroupHom G G → USym G) (semidirect_projection_section G H)
      = g by usym_hom_id G g ∎
