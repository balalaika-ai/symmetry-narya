export "01-center"
export "../../../src/1202-group-center"
export "../../../src/410-pointed-connected-groupoids"

{` Bridges for abelian.tex, sec:center-group (blocks 23, 78, 117, 126, 208).

   BlindCenter G and our group_center G are automorphism_group on the same groupoid at the same point; they
   differ only in the proof that (BG÷ = BG÷) is a groupoid, so BG of both is the same pointed type by refl and
   the groups are equal (bridge_def_center). The blind evaluation map is ours by refl. The blind pointing path
   ev(refl) = sh_G is inverse (inverse (refl BG÷ .liftr sh_G)) (via transport_refl), ours is
   refl BG÷ .liftr sh_G; the two agree by inverse_inverse, hence the two homomorphisms Z(G) → G agree as
   pointed maps and their Ω agree pointwise. `}

{` Definition (abelian.tex:23). `}
def bridge_def_center (G : Group) : Id Group (group_center G) (BlindCenter G)
  ≔ equiv_inverse_map (Id Group (group_center G) (BlindCenter G)) (Id Pointed (BG (group_center G)) (BG (BlindCenter G)))
      (group_path_pointed_equiv (group_center G) (BlindCenter G)) (refl (BG (group_center G)))

def bridge_def_center_bg (G : Group) : Id Pointed (BG (group_center G)) (BG (BlindCenter G)) ≔ refl (BG (group_center G))

def bridge_def_center_ev (G : Group) (φ : BG (group_center G) .carrier)
  : Id (BG G .carrier) (center_evaluation G φ) (blind_center_ev G (φ .fst))
  ≔ refl (center_evaluation G φ)

def bridge_def_center_point (G : Group)
  : Id (Id (BG G .carrier) (shape G) (center_evaluation G (shape (group_center G))))
      (center_evaluation_point G) (blind_center_ev_refl G)
  ≔ inverse (Id (BG G .carrier) (shape G) (center_evaluation G (shape (group_center G))))
      (blind_center_ev_refl G) (center_evaluation_point G)
      (inverse_inverse (BG G .carrier) (shape G) (center_evaluation G (shape (group_center G))) (center_evaluation_point G))

def bridge_def_center_inc (G : Group)
  : Id (BookPointedMap (BG (group_center G)) (BG G)) (hom_B (group_center G) G (center_inclusion G)) (blind_center_inc_B G)
  ≔ map_path (Id (BG G .carrier) (shape G) (center_evaluation G (shape (group_center G))))
      (BookPointedMap (BG (group_center G)) (BG G)) (r ↦ (center_evaluation G, r))
      (center_evaluation_point G) (blind_center_ev_refl G) (bridge_def_center_point G)

def bridge_center_usym (G : Group) (p : USym (group_center G))
  : Id (USym G) (usym_hom (group_center G) G (center_inclusion G) p) (usym_hom (BlindCenter G) G (blind_center_inc G) p)
  ≔ map_path (BookPointedMap (BG (group_center G)) (BG G)) (USym G) (k ↦ loops_map (BG (group_center G)) (BG G) k p)
      (hom_B (group_center G) G (center_inclusion G)) (blind_center_inc_B G) (bridge_def_center_inc G)

{` lemma:center-is-subgroup (abelian.tex:78). The two maps BZ(G)÷ → BG÷ are equal by refl. `}
def bridge_center_is_subgroup : blind_center_is_subgroup ≔ G ↦ center_inclusion_covering G

def bridge_center_is_subgroup_converse (b : blind_center_is_subgroup) (G : Group)
  : IsCovering (BG (group_center G) .carrier) (BG G .carrier) (center_evaluation G)
  ≔ b G

{` lemma:center-inc-inj-on-paths (abelian.tex:117). `}
def bridge_center_inc_inj_on_paths : blind_center_inc_inj_on_paths
  ≔ G ↦ transport (USym (group_center G) → USym G) (IsEmbedding (USym (group_center G)) (USym G))
      (usym_hom (group_center G) G (center_inclusion G)) (usym_hom (BlindCenter G) G (blind_center_inc G))
      (funext (USym (group_center G)) (_ ↦ USym G) (usym_hom (group_center G) G (center_inclusion G))
        (usym_hom (BlindCenter G) G (blind_center_inc G)) (bridge_center_usym G))
      (center_inclusion_injective G)

{` lemma:center-inc-surj-on-paths (abelian.tex:126). The fiber of ours is moved along bridge_center_usym. `}
def bridge_center_fiber (G : Group) (g : USym G)
  (fib : BookFiber (USym (group_center G)) (USym G) (usym_hom (group_center G) G (center_inclusion G)) g)
  : BookFiber (USym (BlindCenter G)) (USym G) (usym_hom (BlindCenter G) G (blind_center_inc G)) g
  ≔ (fib .fst,
     concat (USym G) g (usym_hom (group_center G) G (center_inclusion G) (fib .fst))
       (usym_hom (BlindCenter G) G (blind_center_inc G) (fib .fst)) (fib .snd) (bridge_center_usym G (fib .fst)))

def bridge_center_inc_surj_on_paths : blind_center_inc_surj_on_paths
  ≔ G g hg ↦ bridge_center_fiber G g (center_inclusion_central_fiber G g hg)

{` def:abelian-groups (abelian.tex:208). IsGroupIso only sees the underlying map, which is ours by refl. `}
def bridge_abelian_iff_center_iso : blind_abelian_iff_center_iso
  ≔ G ↦ (abelian_center_inclusion_iso G, center_iso_abelian G)

def bridge_abelian_iff_center_iso_converse (b : blind_abelian_iff_center_iso) (G : Group)
  : BookEquiv (IsAbelian G) (IsGroupIso (group_center G) G (center_inclusion G))
  ≔ book_equivalence (IsAbelian G) (IsGroupIso (group_center G) G (center_inclusion G))
      (iff_equiv (IsAbelian G) (IsGroupIso (group_center G) G (center_inclusion G)) (is_abelian_prop G)
        (is_group_iso_prop (group_center G) G (center_inclusion G)) (b G .fst) (b G .snd))
