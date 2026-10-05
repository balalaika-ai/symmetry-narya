export "05-homs"
export "../../../src/500-gsets"

{` Blind statements, chapter 7, section "Actions, from abstract to concrete and back". `}

{` lem:actionsconcr2abstr. a_X(g) ≔ X(g), the identification X(sh) = X(sh) in
   the component of Set (a symmetry in Σ_{X(sh)}). `}
def blind_gset_sym (G : Group) (X : GSet G) (g : USym G) : USym (permutation_group (X (shape G)))
  ≔ component_path SetTypes (X (shape G)) (component_point SetTypes (X (shape G))) (component_point SetTypes (X (shape G)))
      (map_path (BG G .carrier) SetTypes X (shape G) (shape G) g)

def blind_gset_sym_hom (G : Group) (X : GSet G)
  : BlindIsAbsHom (blind_abstr G) (blind_perm_group (X (shape G))) (blind_gset_sym G X)
  ≔ g h ↦ permutation_symmetries_ext (X (shape G)) (blind_gset_sym G X (usym_mul G g h))
      (usym_mul (permutation_group (X (shape G))) (blind_gset_sym G X g) (blind_gset_sym G X h))
      (x ↦ concat (X (shape G) .fst) (gset_usym_act G X (usym_mul G g h) x)
         (gset_usym_act G X g (gset_usym_act G X h x))
         (permutation_action (X (shape G)) (usym_mul (permutation_group (X (shape G))) (blind_gset_sym G X g) (blind_gset_sym G X h)) x)
         (gset_act_mul G X g h x)
         (inverse (X (shape G) .fst)
           (permutation_action (X (shape G)) (usym_mul (permutation_group (X (shape G))) (blind_gset_sym G X g) (blind_gset_sym G X h)) x)
           (gset_usym_act G X g (gset_usym_act G X h x))
           (permutation_action_mul (X (shape G)) (blind_gset_sym G X g) (blind_gset_sym G X h) x)))

def blind_ev_sh (G : Group) (X : GSet G) : BlindAbsGSet (blind_abstr G)
  ≔ (X (shape G), (blind_gset_sym G X, blind_gset_sym_hom G X))

def blind_lem_actionsconcr2abstr : Type
  ≔ (G : Group) → BookIsEquiv (GSet G) (BlindAbsGSet (blind_abstr G)) (blind_ev_sh G)

{` ex:HomHGasGset (chapter 5) restricted to G: Hom(H,G)(z) ≔ Hom(H, mkgroup(BG÷, z)). `}
def blind_hom_gset (H G : Group) : GSet G
  ≔ z ↦ (GroupHom H (group_at G z), group_hom_set H (group_at G z))

{` ex:abstrandconj (1): transport along p : sh_G = z in Hom(H,G)(-) is
   postcomposition with mkgroup(id_BG, p⁻¹) : Hom(G, mkgroup(BG÷, z)). `}
def blind_ex_abstrandconj_transport : Type
  ≔ (H G : Group) (z : BG G .carrier) (p : Id (BG G .carrier) (shape G) z) (f : GroupHom H G)
    → Id (GroupHom H (group_at G z)) (gset_act G (blind_hom_gset H G) (shape G) z p f)
        (group_hom_compose H G (group_at G z) f (conj_hom G z p))

{` ex:abstrandconj (2) / lem:abstrandconj: under abstr : Hom(H,G) ≃ Hom^abs(abstr H, abstr G),
   the action of g : USym G on the G-set Hom(H,G) (through ev_sh) becomes
   postcomposition with conj^g. `}
def BlindHomConjCompat (H G : Group) : Type
  ≔ (g : USym G) (f : GroupHom H G)
    → Id (USym H → USym G)
        (blind_abstr_hom H G (blind_gset_act (blind_abstr G) (blind_ev_sh G (blind_hom_gset H G)) g f) .fst)
        (s ↦ blind_conj (blind_abstr G) g (usym_hom H G f s))

def blind_ex_abstrandconj_action : Type ≔ (H G : Group) → BlindHomConjCompat H G

{` lem:abstrandconj: the equivalence sends the G-set Hom(H,G) to the
   abstr(G)-set Hom^abs(abstr H, abstr G) with the conjugation action, i.e.
   abstr is a bijection Hom(H,G) ≃ Hom^abs(abstr H, abstr G) that turns the
   action of ev_sh(Hom(H,G)) into postcomposition with conj^g. `}
def blind_lem_abstrandconj : Type
  ≔ (H G : Group)
    → Product (BookIsEquiv (GroupHom H G) (BlindAbsHom (blind_abstr H) (blind_abstr G)) (blind_abstr_hom H G))
        (BlindHomConjCompat H G)

{` xca:f^*-abs(f)^*: ev_sh ∘ f^* = abstr(f)^* ∘ ev_sh. `}
def blind_xca_restrict_abs : Type
  ≔ (G H : Group) (f : GroupHom G H) (Y : GSet H)
    → Id (BlindAbsGSet (blind_abstr G)) (blind_ev_sh G (gset_restrict G H f Y))
        (blind_phi_star (blind_abstr G) (blind_abstr H) (blind_abstr_hom G H f) (blind_ev_sh H Y))

{` xca:f_!-abs(f)_!: ev_sh ∘ f_! = abstr(f)_! ∘ ev_sh (abstr(f)_! with any
   data of xca:phi_!-OK). `}
def blind_xca_induce_abs : Type
  ≔ (G H : Group) (f : GroupHom G H)
    (ok : (X : BlindAbsGSet (blind_abstr G)) → BlindPhiShriekOK (blind_abstr G) (blind_abstr H) (blind_abstr_hom G H f) X)
    (X : GSet G)
    → Id (BlindAbsGSet (blind_abstr H)) (blind_ev_sh H (gset_induce G H f X))
        (blind_phi_shriek (blind_abstr G) (blind_abstr H) (blind_abstr_hom G H f) ok (blind_ev_sh G X))
