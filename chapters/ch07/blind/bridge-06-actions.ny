export "bridge-00-core"
export "06-actions"
export "../../../src/751-hom-gset-conjugation"
export "../../../src/752-restriction-comparison"

{` Bridges for absgroup.tex, sec:Gsetsabstrconcr (blind file
   06-actions), without xca:f_!-abs(f)_! (bridge-06b-induction). `}

{` lem:actionsconcr2abstr. The blind a_X(g) = X(g) and our a_X (abstr of
   the classified action) act in the same way, so ev agrees up to a path. `}
def bridge_ev_path (G : Group) (X : GSet G) : Id (AbstractGSet (abstr G)) (blind_ev_sh G X) (ev_gset G X)
  ≔ (refl (X (shape G)),
     agset_structure_ext (abstr G) (X (shape G)) (blind_ev_sh G X .snd) (ev_gset G X .snd)
       (g x ↦ inverse (X (shape G) .fst) (agset_act (abstr G) (ev_gset G X) g x) (gset_usym_act G X g x)
         (ev_gset_act G X g x)))

def bridge_lem_actionsconcr2abstr : blind_lem_actionsconcr2abstr
  ≔ G ↦ bridge_book_equiv_homotopic (GSet G) (AbstractGSet (abstr G))
      (book_equivalence (GSet G) (AbstractGSet (abstr G)) (gset_abstract_gset_equiv G))
      (blind_ev_sh G)
      (X ↦ inverse (AbstractGSet (abstr G)) (blind_ev_sh G X) (ev_gset G X) (bridge_ev_path G X))

{` ex:abstrandconj. The blind G-set Hom(H, G) is ours (group_hom_gset). `}
def bridge_def_hom_gset (H G : Group) : Id (GSet G) (blind_hom_gset H G) (group_hom_gset H G)
  ≔ refl (group_hom_gset H G)

def bridge_ex_abstrandconj_transport : blind_ex_abstrandconj_transport
  ≔ H G z p f ↦ hom_gset_conj_transport H G z p f

def bridge_hom_conj_compat (H G : Group) : BlindHomConjCompat H G
  ≔ g f ↦ let AH ≔ abstr H in let AG ≔ abstr G in let cg ≔ conj_hom G (shape G) g in
    refl ((φ ↦ φ .fst) : AbstractHom AH AG → (USym H → USym G))
      (calc
        abstr_hom H G (gset_usym_act G (group_hom_gset H G) g f)
        = abstr_hom H G (group_hom_compose H G G f cg)
          by refl (abstr_hom H G) (hom_gset_conj_transport H G (shape G) g f)
        = abstract_hom_compose AH AG AG (abstr_hom H G f) (abstr_hom G G cg)
          by abstr_hom_compose H G G f cg
        = abstract_hom_compose AH AG AG (abstr_hom H G f) (abstract_conj_hom AG g)
          by refl (abstract_hom_compose AH AG AG (abstr_hom H G f)) (abstr_conj_hom_is_abstract_conj G g) ∎)

def bridge_ex_abstrandconj_action : blind_ex_abstrandconj_action ≔ H G ↦ bridge_hom_conj_compat H G

{` lem:abstrandconj. `}
def bridge_lem_abstrandconj : blind_lem_abstrandconj
  ≔ H G ↦ (abstr_hom_is_equiv H G, bridge_hom_conj_compat H G)

{` Converse direction for lem:abstrandconj: the blind data give our
   identification of abstr(G)-sets. `}
def bridge_lem_abstrandconj_converse (H G : Group) (b : blind_lem_abstrandconj)
  : Id (AbstractGSet (abstr G)) (ev_gset G (group_hom_gset H G)) (hom_gset_conj_agset (abstr H) (abstr G))
  ≔ agset_path_from_iso (abstr G) (ev_gset G (group_hom_gset H G)) (hom_gset_conj_agset (abstr H) (abstr G))
      (native_equivalence (GroupHom H G) (AbstractHom (abstr H) (abstr G)) (abstr_hom H G, b H G .fst),
       g f ↦ abstract_hom_ext (abstr H) (abstr G)
         (abstr_hom H G (agset_act (abstr G) (ev_gset G (group_hom_gset H G)) g f))
         (agset_act (abstr G) (hom_gset_conj_agset (abstr H) (abstr G)) g (abstr_hom H G f))
         (s ↦ concat (USym G) (usym_hom H G (agset_act (abstr G) (ev_gset G (group_hom_gset H G)) g f) s)
            (usym_hom H G (gset_usym_act G (group_hom_gset H G) g f) s)
            (abstract_conj (abstr G) g (usym_hom H G f s))
            (refl ((k ↦ usym_hom H G k s) : GroupHom H G → USym G) (ev_gset_act G (group_hom_gset H G) g f))
            (b H G .snd g f (refl s))))

{` xca:f^*-abs(f)^*. The blind φ^* is ours (agset_restrict) by refl. `}
def bridge_def_phi_star_06 (G H : BlindAbsGroup) (phi : BlindAbsHom G H) (Y : BlindAbsGSet H)
  : Id (AbstractGSet (bridge_ag7 G)) (blind_phi_star G H phi Y) (agset_restrict (bridge_ag7 G) (bridge_ag7 H) phi Y)
  ≔ refl (agset_restrict (bridge_ag7 G) (bridge_ag7 H) phi Y)

def bridge_xca_restrict_abs : blind_xca_restrict_abs
  ≔ G H f Y ↦ let A ≔ AbstractGSet (abstr G) in
    let R : AbstractGSet (abstr H) → A ≔ W ↦ agset_restrict (abstr G) (abstr H) (abstr_hom G H f) W in
    concat A (blind_ev_sh G (gset_restrict G H f Y)) (ev_gset G (gset_restrict G H f Y)) (R (blind_ev_sh H Y))
      (bridge_ev_path G (gset_restrict G H f Y))
      (concat A (ev_gset G (gset_restrict G H f Y)) (R (ev_gset H Y)) (R (blind_ev_sh H Y))
        (restrict_ev_path G H f Y)
        (refl R (inverse (AbstractGSet (abstr H)) (blind_ev_sh H Y) (ev_gset H Y) (bridge_ev_path H Y))))
