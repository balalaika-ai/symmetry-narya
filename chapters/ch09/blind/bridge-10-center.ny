export "10-center"
export "../../../src/958-center-as-abelian-group"
export "../../../src/959-homs-modulo-conjugation"
export "../../../src/957-outer-automorphisms-simple"

{` Bridges for symmetry.tex, def:center and thm:hom-mod-conj (blind file 10-center); both for 1-groups,
   as ours. `}

{` Definition bridges: the blind Bunch, bunch, Z(G), BZ(G), B²Z(G) are ours by refl. `}
def bridge_def_bunch : Id Type BlindBunch Bunch ≔ refl Bunch

def bridge_def_bunch_of (G : Group) : Id Bunch (blind_bunch G) (bunch G) ≔ refl (bunch G)

def bridge_def_center (G : Group) : Id Type (BlindCenter G) (CenterFixedPoints G) ≔ refl (CenterFixedPoints G)

def bridge_def_BZ (G : Group) : Id Pointed (blind_BZ_pointed G) (CenterClassifying G, center_classifying_point G)
  ≔ refl ((CenterClassifying G, center_classifying_point G) : Pointed)

def bridge_def_B2Z (G : Group) : Id Pointed (blind_B2Z_pointed G) (BTwoCenter G, btwo_center_point G)
  ≔ refl ((BTwoCenter G, btwo_center_point G) : Pointed)

{` A pointed equivalence (P, p0) ≃ Ω(Y) from any equivalence P ≃ Ω(Y): postcompose with right concatenation by
   the inverse of the image of p0. `}
def bridge9w_pointed_loops_equiv (P : Type) (p0 : P) (Y : Pointed) (e : Equiv P (Loop Y))
  : BookPointedEquiv (P, p0) (Omega Y)
  ≔ let A ≔ Y .carrier in let y ≔ Y .point in
    let q ≔ inverse A y y (e .map p0) in
    let d ≔ compose_equiv P (Loop Y) (Loop Y) e (ch9w2_concat_right_equiv A y y y q) in
    ((d .map, inverse (Loop Y) (concat A y y y (e .map p0) q) (refl y) (concat_inverse_right A y y (e .map p0))),
     book_equivalence P (Loop Y) d .equiv)

{` def:center. `}
def bridge_center_adjoint_fixed : blind_center_adjoint_fixed ≔ G ↦ center_fixed_points_adjoint G

def bridge_center_aut_id : blind_center_aut_id
  ≔ G ↦ canonical_inverse_equiv (Id (BG G .carrier → BG G .carrier) (identity (BG G .carrier)) (identity (BG G .carrier)))
      (CenterFixedPoints G) (center_identity_loops_equiv G)

def bridge_center_loops_BZ : blind_center_loops_BZ
  ≔ G ↦ bridge9w_pointed_loops_equiv (CenterFixedPoints G) (z ↦ refl z) (CenterClassifying G, center_classifying_point G)
      (canonical_inverse_equiv (USym (center_fun_group G)) (CenterFixedPoints G) (center_fun_loops_equiv G))

def bridge_BZ_loops_B2Z : blind_BZ_loops_B2Z
  ≔ G ↦ bridge9w_pointed_loops_equiv (CenterClassifying G) (center_classifying_point G) (BTwoCenter G, btwo_center_point G)
      (canonical_inverse_equiv (Id (BTwoCenter G) (btwo_center_point G) (btwo_center_point G)) (CenterClassifying G)
        (btwo_center_loops_equiv G))

def bridge_B2Z_connected : blind_B2Z_connected ≔ G ↦ btwo_center_connected G

def bridge_center_abelian_group : blind_center_abelian_group
  ≔ G ↦ (center_classifying_connected G, (center_classifying_groupoid G, center_fun_abelian G))

{` thm:hom-mod-conj. The blind BInn(H) (sum over Group of ‖bunch(H) = bunch(K)‖₀) and ours (Img(inn), module 956)
   are equivalent over Group. `}
def bridge9w_binn_fiber_equiv (H K : Group)
  : Equiv (SetTrunc (Id Bunch (bunch H) (bunch K))) (SetTrunc (Id Type (BG K .carrier) (BG H .carrier)))
  ≔ ch9w2_set_trunc_equiv (Id Bunch (bunch H) (bunch K)) (Id Type (BG K .carrier) (BG H .carrier))
      (compose_equiv (Id Bunch (bunch H) (bunch K)) (Id Type (BG H .carrier) (BG K .carrier)) (Id Type (BG K .carrier) (BG H .carrier))
        (bunch_path_equiv (bunch H) (bunch K)) (inverse_path_equiv Type (BG H .carrier) (BG K .carrier)))

def bridge9w_binn_equiv (H : Group)
  : Equiv (BlindBInnSym H) (Σ Group (K ↦ SetTrunc (Id Type (BG K .carrier) (BG H .carrier))))
  ≔ family_equiv Group (K ↦ SetTrunc (Id Bunch (bunch H) (bunch K))) (K ↦ SetTrunc (Id Type (BG K .carrier) (BG H .carrier)))
      (bridge9w_binn_fiber_equiv H)

def bridge_def_binn_sym (H : Group) : Equiv (BlindBInnSym H) (BG (inner_aut_group H) .carrier)
  ≔ compose_equiv (BlindBInnSym H) (Σ Group (K ↦ SetTrunc (Id Type (BG K .carrier) (BG H .carrier)))) (BG (inner_aut_group H) .carrier)
      (bridge9w_binn_equiv H)
      (canonical_inverse_equiv (BG (inner_aut_group H) .carrier) (Σ Group (K ↦ SetTrunc (Id Type (BG K .carrier) (BG H .carrier))))
        (inner_aut_classifying_equiv_group H))

def bridge_hom_mod_conj_fiber : blind_hom_mod_conj_fiber
  ≔ G H ↦ ch9w2_set_trunc_equiv (GroupHom G H) (BookPointedMap (BG G) (BG H))
      (quasi_inverse_equiv (GroupHom G H) (BookPointedMap (BG G) (BG H)) (f ↦ hom_B G H f) (k ↦ mkhom G H k)
        (f ↦ refl f) (k ↦ refl k))

def bridge_hom_mod_conj : blind_hom_mod_conj
  ≔ G H ↦
    let XG ≔ BG G .carrier in let XH ≔ BG H .carrier in
    let BI ≔ BG (inner_aut_group H) .carrier in
    let W ≔ Σ Group (K ↦ SetTrunc (Id Type (BG K .carrier) XH)) in
    let P : W → Type ≔ w ↦ SetTrunc (GroupHom G (w .fst)) in
    let A ≔ ActionType (inner_aut_group H) (hom_conj_gset G H) in
    let B ≔ Σ (BlindBInnSym H) (blind_hom_mod_conj_family G H) in
    let e1 ≔ sigma_pullback_equiv BI W (inner_aut_classifying_equiv_group H) P in
    let e2 ≔ sigma_pullback_equiv (BlindBInnSym H) W (bridge9w_binn_equiv H) P in
    book_equivalence (SetTrunc (XG → XH)) (SetTrunc B)
      (compose_equiv (SetTrunc (XG → XH)) (SetTrunc A) (SetTrunc B) (hom_mod_conj_equiv G H)
        (ch9w2_set_trunc_equiv A B
          (compose_equiv A (Σ W P) B e1 (canonical_inverse_equiv B (Σ W P) e2))))
