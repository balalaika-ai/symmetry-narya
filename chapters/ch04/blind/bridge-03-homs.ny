export "bridge-00-core"
export "../../../src/437-conjugation-inner-automorphisms"
export "../../../src/436-maps-from-classifying-types"
export "../../../src/435-circle-group-homomorphisms"

{` Bridges for group.tex, section "Homomorphisms" (blind file
   03-homs.ny), except ex:groups-morphisms and the remark after it
   (bridge-03b-hom-examples.ny). The definition bridges (Hom, loops map,
   USym of a homomorphism, isomorphisms, identity, composition) are in
   bridge-00-core.ny; the blind loops map differs from ours by
   reassociation (bridge_loops_map). `}

{` rem:homom-eqs (line 932): ours (homom_eqs_unit/inv/mul) are map_path_inverse
   and map_path_concat; the unit law holds by refl. `}
def bridge_rem_homom_eqs : blind_rem_homom_eqs
  ≔ G B k ↦ let A ≔ blind_B G .fst in let s ≔ blind_shape G in
    (refl (refl (k s)),
     (g ↦ map_path_inverse A B k s s g,
      g g' ↦ map_path_concat A B k s s s g g'))

{` rem:loops-map (line 1009). `}
def bridge_rem_loops_map_refl : blind_rem_loops_map_refl
  ≔ A B a f ↦ concat (Id A a a → Id B (f a) (f a))
      (blind_loops_map (A, a) (B, f a) (f, refl (f a))) (loops_map (A, a) (B, f a) (f, refl (f a)))
      (map_path A B f a a)
      (bridge_def_loops_map (A, a) (B, f a) (f, refl (f a)))
      (loops_map_refl_pointing A B f a)

{` lem:grouphomomaxioms (line 1022) and rem:first-abs-hom (line 1341). `}
def bridge_lem_grouphomomaxioms : blind_lem_grouphomomaxioms
  ≔ G H f ↦
    let G' ≔ bridge_g G in let H' ≔ bridge_g H in let f' ≔ bridge_h G H f in
    let u ≔ blind_usym_hom G H f in let v ≔ usym_hom G' H' f' in
    let b ≔ bridge_usym_hom G H f in
    (concat (USym H') (u (usym_unit G')) (v (usym_unit G')) (usym_unit H') (b (usym_unit G')) (usym_hom_unit G' H' f'),
     (g ↦ concat (USym H') (u (usym_inv G' g)) (v (usym_inv G' g)) (usym_inv H' (u g)) (b (usym_inv G' g))
            (concat (USym H') (v (usym_inv G' g)) (usym_inv H' (v g)) (usym_inv H' (u g)) (usym_hom_inv G' H' f' g)
              (refl (usym_inv H') (inverse (USym H') (u g) (v g) (b g)))),
      g g' ↦ concat (USym H') (u (usym_mul G' g' g)) (v (usym_mul G' g' g)) (usym_mul H' (u g') (u g))
            (b (usym_mul G' g' g))
            (concat (USym H') (v (usym_mul G' g' g)) (usym_mul H' (v g') (v g)) (usym_mul H' (u g') (u g))
              (usym_hom_mul G' H' f' g' g)
              (refl (usym_mul H') (inverse (USym H') (u g') (v g') (b g')) (inverse (USym H') (u g) (v g) (b g))))))

{` def:groupisomorphism (line 1043), footnote: Iso(G, H) is a set. `}
def bridge_iso_is_set : blind_iso_is_set
  ≔ G H ↦ hlevel_two_to_set (BlindIso G H)
      (hlevel_equiv (suc. (suc. zero.)) (GroupIso (bridge_g G) (bridge_g H)) (BlindIso G H)
        (canonical_inverse_equiv (BlindIso G H) (GroupIso (bridge_g G) (bridge_g H)) (bridge_def_iso G H))
        (set_to_hlevel_two (GroupIso (bridge_g G) (bridge_g H)) (group_iso_set (bridge_g G) (bridge_g H))))

{` def:identity-group-homomorphism (line 1050). `}
def bridge_id_hom_is_iso : blind_id_hom_is_iso ≔ G ↦ group_hom_id_iso (bridge_g G)

{` remark:groupsasunivalenttype (line 1056). `}
def bridge_rem_groups_univalent : blind_rem_groups_univalent
  ≔ G H ↦ book_equivalence (Id BlindGroup G H) (BlindIso G H)
      (compose_equiv (Id BlindGroup G H) (Id Group (bridge_g G) (bridge_g H)) (BlindIso G H) (bridge_group_paths G H)
        (compose_equiv (Id Group (bridge_g G) (bridge_g H)) (GroupIso (bridge_g G) (bridge_g H)) (BlindIso G H)
          (group_path_iso_equiv (bridge_g G) (bridge_g H))
          (canonical_inverse_equiv (BlindIso G H) (GroupIso (bridge_g G) (bridge_g H)) (bridge_def_iso G H))))

{` rem:Bf-convention (line 1084). Ours (group_hom_induction) holds by record
   eta; for the blind Copy type the inverse is defined by matching. `}
def bridge_bf_convention_inv (G H : BlindGroup) (T : BlindHom G H → Type)
  (g : (k : BookPointedMap (blind_BG G) (blind_BG H)) → T (blind_mkhom G H k)) : (f : BlindHom G H) → T f
  ≔ [ copy. k ↦ g k ]

def bridge_bf_convention_eta (G H : BlindGroup) (T : BlindHom G H → Type) (φ : (f : BlindHom G H) → T f)
  : (f : BlindHom G H) → Id (T f) (bridge_bf_convention_inv G H T (k ↦ φ (blind_mkhom G H k)) f) (φ f)
  ≔ [ copy. k ↦ refl (φ (blind_mkhom G H k)) ]

def bridge_rem_bf_convention : blind_rem_bf_convention
  ≔ G H T ↦ book_quasi_inverse_equiv ((f : BlindHom G H) → T f)
      ((k : BookPointedMap (blind_BG G) (blind_BG H)) → T (blind_mkhom G H k))
      (φ ↦ k ↦ φ (blind_mkhom G H k)) (bridge_bf_convention_inv G H T)
      (φ ↦ funext (BlindHom G H) T (bridge_bf_convention_inv G H T (k ↦ φ (blind_mkhom G H k))) φ
        (bridge_bf_convention_eta G H T φ))
      (g ↦ refl g) .equiv

{` lem:hom-is-set (line 1111). `}
def bridge_lem_hom_is_set : blind_lem_hom_is_set
  ≔ G H ↦ hlevel_two_to_set (BlindHom G H)
      (hlevel_equiv (suc. (suc. zero.)) (GroupHom (bridge_g G) (bridge_g H)) (BlindHom G H)
        (canonical_inverse_equiv (BlindHom G H) (GroupHom (bridge_g G) (bridge_g H)) (bridge_def_hom G H))
        (set_to_hlevel_two (GroupHom (bridge_g G) (bridge_g H)) (group_hom_set (bridge_g G) (bridge_g H))))

{` def:loops-compose (line 1240). `}
def bridge_loops_compose : blind_loops_compose
  ≔ X Y Z f g ↦
    let fg ≔ book_pointed_compose X Y Z f g in
    let bf ≔ blind_loops_map X Y f in let bg ≔ blind_loops_map Y Z g in
    let of ≔ loops_map X Y f in let og ≔ loops_map Y Z g in
    concat (Loop X → Loop Z) (blind_loops_map X Z fg) (l ↦ og (of l)) (l ↦ bg (bf l))
      (concat (Loop X → Loop Z) (blind_loops_map X Z fg) (loops_map X Z fg) (l ↦ og (of l))
        (bridge_def_loops_map X Z fg) (loops_map_compose X Y Z f g))
      (funext (Loop X) (_ ↦ Loop Z) (l ↦ og (of l)) (l ↦ bg (bf l))
        (l ↦ concat (Loop Z) (og (of l)) (og (bf l)) (bg (bf l))
          (refl og (inverse (Loop Y) (bf l) (of l) (bridge_loops_map X Y f l)))
          (inverse (Loop Z) (bg (bf l)) (og (bf l)) (bridge_loops_map Y Z g (bf l)))))

{` cor:USym-compose (line 1261). `}
def bridge_cor_usym_compose : blind_cor_usym_compose
  ≔ G H K φ ψ ↦ bridge_loops_compose (blind_BG G) (blind_BG H) (blind_BG K) (blind_Bhom G H φ) (blind_Bhom H K ψ)

{` ex:Zinitial (line 1270): ours circle_hom_ev has map loops_map f loop;
   the blind map differs pointwise by bridge_loops_map. `}
def bridge_ex_Zinitial : blind_ex_Zinitial
  ≔ C G ↦ book_equivalence (BookPointedMap (circle_pointed C) (blind_BG G)) (BlindUSym G)
      (equiv_change_map (BookPointedMap (circle_pointed C) (blind_BG G)) (BlindUSym G) (circle_hom_ev C (bridge_g G))
        (blind_ev C G)
        (f ↦ inverse (BlindUSym G) (blind_ev C G f) (loops_map (circle_pointed C) (blind_BG G) f (C .loop))
          (bridge_loops_map (circle_pointed C) (blind_BG G) f (C .loop)))) .equiv

{` lem:Znatural (line 1295). `}
def bridge_lem_Znatural : blind_lem_Znatural
  ≔ C G H f u ↦
    let Z ≔ circle_group C in let G' ≔ bridge_g G in let H' ≔ bridge_g H in
    let u' ≔ bridge_h (blind_ZZ C) G u in let f' ≔ bridge_h G H f in
    let uf ≔ blind_hom_compose (blind_ZZ C) G H u f in
    concat (USym H') (blind_ev_hom C H uf) (usym_hom G' H' f' (usym_hom Z G' u' (C .loop)))
      (blind_usym_hom G H f (blind_ev_hom C G u))
      (concat (USym H') (blind_ev_hom C H uf) (usym_hom Z H' (bridge_h (blind_ZZ C) H uf) (C .loop))
        (usym_hom G' H' f' (usym_hom Z G' u' (C .loop)))
        (bridge_usym_hom (blind_ZZ C) H uf (C .loop))
        (circle_group_hom_ev_natural C G' H' f' u'))
      (concat (USym H') (usym_hom G' H' f' (usym_hom Z G' u' (C .loop))) (usym_hom G' H' f' (blind_ev_hom C G u))
        (blind_usym_hom G H f (blind_ev_hom C G u))
        (refl (usym_hom G' H' f') (inverse (USym G') (blind_ev_hom C G u) (usym_hom Z G' u' (C .loop))
          (bridge_usym_hom (blind_ZZ C) G u (C .loop))))
        (inverse (USym H') (blind_usym_hom G H f (blind_ev_hom C G u)) (usym_hom G' H' f' (blind_ev_hom C G u))
          (bridge_usym_hom G H f (blind_ev_hom C G u))))

{` xca:BGtotype (line 1329). BlindHom G (blind_Aut A hA a) is GroupHom
   (bridge_g G) (automorphism_group A hA a) up to the Copy wrapper. `}
def bridge_xca_BGtotype : blind_xca_BGtotype
  ≔ G A hA ↦
    let G' ≔ bridge_g G in
    let T2 ≔ BGToTypeTwo G' A in
    (book_equivalence (BGToTypeOne G' A) T2 (canonical_inverse_equiv T2 (BGToTypeOne G' A) (bg_to_type_two_one G' A)),
     (book_equivalence T2 T2 (identity_equiv T2),
      book_equivalence (BGToTypeThree G' A) (Σ A (a ↦ BlindHom G (blind_Aut A hA a)))
        (compose_equiv (BGToTypeThree G' A) (BGToTypeFour G' A hA) (Σ A (a ↦ BlindHom G (blind_Aut A hA a)))
          (bg_to_type_three_four G' A hA)
          (family_equiv A (a ↦ GroupHom G' (automorphism_group A hA a)) (a ↦ BlindHom G (blind_Aut A hA a))
            (a ↦ canonical_inverse_equiv (BlindHom G (blind_Aut A hA a)) (GroupHom G' (automorphism_group A hA a))
              (bridge_def_hom G (blind_Aut A hA a)))))))

{` exa:conj-concrete (line 1361): blind_regroup G y is group_at (bridge_g G) y
   and blind_conj_map is conj_pointed_map, on the nose. `}
def bridge_def_regroup (G : BlindGroup) (y : blind_B G .fst)
  : Id Group (bridge_g (blind_regroup G y)) (group_at (bridge_g G) y) ≔ refl (group_at (bridge_g G) y)

def bridge_exa_conj_iso : blind_exa_conj_iso ≔ G y p ↦ conj_iso (bridge_g G) y p .snd

def bridge_exa_conj_identification : blind_exa_conj_identification
  ≔ G y p ↦ bridge_gpath G (blind_regroup G y) (conj_group_path (bridge_g G) y p)

def bridge_exa_conj_formula : blind_exa_conj_formula
  ≔ G y p ↦
    let G' ≔ bridge_g G in
    let h ≔ blind_mkhom G (blind_regroup G y) (blind_conj_map G y p) in
    concat (USym G' → Id (BG G' .carrier) y y) (blind_usym_hom G (blind_regroup G y) h)
      (usym_hom G' (group_at G' y) (conj_hom G' y p))
      (g ↦ loop_conjugate (BG G' .carrier) (shape G') y p g)
      (bridge_def_usym_hom G (blind_regroup G y) h)
      (conj_usym_function G' y p)

{` def:inner-autos (line 1395). The blind Aut(G) lives on the component of
   BlindGroup, ours (group_aut) on that of Group; Bridge: the two groups
   are identified (bridge_aut, then automorphism_group_equiv_path along
   bridge_def_group), and the classifying maps agree pointwise: after
   matching on copy., bridge_g (Binn y) is group_at G y by refl. `}
def bridge_def_inn_aut_group (h : blind_xca_typegroup_groupoid) (G : BlindGroup)
  : Id Group (bridge_g (blind_AutGroup h G)) (group_aut (bridge_g G))
  ≔ concat Group (bridge_g (blind_AutGroup h G)) (automorphism_group BlindGroup h G) (group_aut (bridge_g G))
      (bridge_aut BlindGroup h G)
      (automorphism_group_equiv_path BlindGroup Group h group_groupoid bridge_def_group G)

def bridge_def_inn (h : blind_xca_typegroup_groupoid)
  : (G : BlindGroup) (y : blind_B G .fst) →
    Id Group (bridge_g (blind_Bhom G (blind_AutGroup h G) (blind_inn h G) .fst y .fst)) (inn_classifying_map (bridge_g G) y .fst)
  ≔ [ copy. X ↦ y ↦ refl (group_at (bridge_g (blind_mkgroup X)) y) ]
