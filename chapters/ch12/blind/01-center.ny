{` Blind statements for chapter 12 (abelian.tex), section "Center of a group" (sec:center-group). `}
export "../../../src/403-abstract-groups"
export "../../../src/404-group-examples"
export "../../../src/200-truncation-structures"

{` Helper: logical equivalence (used for "if and only if"). `}
def BlindIff (A B : Type) : Type ≔ Product (A → B) (B → A)

{` Helper: (A = A) is a groupoid when A is a groupoid (univalence: (A = A) ≃ (A ≃ A)). Needed only to form
   the automorphism group Aut_{(BG÷ = BG÷)}(refl). `}
def blind_universe_loops_groupoid (A : Type) (hA : isGroupoid A) : isGroupoid (Id Type A A)
  ≔ hlevel_to_groupoid (Id Type A A)
      (hlevel_equiv (suc. (suc. (suc. zero.))) (Equiv A A) (Id Type A A)
        (canonical_inverse_equiv (Id Type A A) (Equiv A A) (univalence_equiv A A))
        (equiv_hlevel (suc. (suc. zero.)) A A (groupoid_to_hlevel A hA)))

{` Center (abelian.tex:23). Z(G) ≔ Aut_{(BG÷ = BG÷)}(refl_{BG÷}); its classifying type is the component of
   refl in BG÷ = BG÷, pointed at (refl, !). `}
def BlindCenter (G : Group) : Group
  ≔ automorphism_group (Id Type (BG G .carrier) (BG G .carrier))
      (blind_universe_loops_groupoid (BG G .carrier) (bg_groupoid G)) (refl (BG G .carrier))

{` ev_{sh_G} : (BG÷ = BG÷) → BG÷, φ ↦ φ(sh_G) (coercion of φ to a function = transport). `}
def blind_center_ev (G : Group) (φ : Id Type (BG G .carrier) (BG G .carrier)) : BG G .carrier
  ≔ φ .trr (shape G)

{` ev(refl) = sh_G. In the book this holds judgmentally; in Narya transport along refl is the identity only
   up to a path (transport_refl). `}
def blind_center_ev_refl (G : Group) : Id (BG G .carrier) (shape G) (blind_center_ev G (refl (BG G .carrier)))
  ≔ inverse (BG G .carrier) (blind_center_ev G (refl (BG G .carrier))) (shape G)
      (transport_refl Type (X ↦ X) (BG G .carrier) (shape G))

{` The homomorphism ζ_G : Hom(Z(G), G), Bζ_G ≔ ev_{sh_G} restricted to the component, pointed by ev(refl) = sh_G. `}
def blind_center_inc_B (G : Group) : BookPointedMap (BG (BlindCenter G)) (BG G)
  ≔ ((u ↦ blind_center_ev G (u .fst)), blind_center_ev_refl G)

def blind_center_inc (G : Group) : GroupHom (BlindCenter G) G ≔ mkhom (BlindCenter G) G (blind_center_inc_B G)

{` lemma:center-is-subgroup (abelian.tex:78). Bζ_G : BZ(G)÷ → BG÷ is a covering (all fibers are sets). `}
def blind_center_is_subgroup : Type
  ≔ (G : Group)
    → IsCovering (BG (BlindCenter G) .carrier) (BG G .carrier) (hom_function (BlindCenter G) G (blind_center_inc G))

{` lemma:center-inc-inj-on-paths (abelian.tex:117). abstr(ζ_G) : USym Z(G) → USym G is an injection
   (book def:injection: all fibers are propositions). `}
def blind_center_inc_inj_on_paths : Type
  ≔ (G : Group)
    → IsEmbedding (USym (BlindCenter G)) (USym G) (abstr_hom (BlindCenter G) G (blind_center_inc G) .fst)

{` lemma:center-inc-surj-on-paths (abelian.tex:126). If g : USym G commutes with every h, the fiber of
   ap_{Bζ_G} at g has an element. Since ev(refl) = sh_G is only a path here, ap_{Bζ_G} is read as Ω(Bζ_G) = usym_hom
   (conjugation of ap by the pointing path, which is ap itself when the pointing path is refl as in the book). `}
def blind_center_inc_surj_on_paths : Type
  ≔ (G : Group) (g : USym G)
    → ((h : USym G) → Id (USym G) (usym_mul G g h) (usym_mul G h g))
    → BookFiber (USym (BlindCenter G)) (USym G) (usym_hom (BlindCenter G) G (blind_center_inc G)) g

{` def:abelian-groups (abelian.tex:208). G is abelian iff ζ_G is an isomorphism of groups. `}
def blind_abelian_iff_center_iso : Type
  ≔ (G : Group) → BlindIff (IsAbelian G) (IsGroupIso (BlindCenter G) G (blind_center_inc G))
