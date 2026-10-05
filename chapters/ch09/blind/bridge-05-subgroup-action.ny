export "05-subgroup-action"
export "../../../src/971-quaternion-all-normal"

{` Bridges for subgroups.tex, sec:actiononsub (blind file 05-subgroup-action), blocks 1200, 1217, 1249,
   1264, 1268, 1282, 1295 and the first half of 1311 (the Σ_3 orbit count is in bridge-05b-sigma3). The blind
   Mono(G) and Sub(G) G-sets are ours by refl (bridge-00-core). `}

{` Definition (subgroups.tex:1200). `}
def bridge_mono_gset_underlying : blind_mono_gset_underlying ≔ G ↦ monos_gset_underlying G

{` rem:action-Mono(G): the blind mkgroup(id_BG, p⁻¹) is our group_at_move. `}
def bridge_def_shape_move (G : Group) (z z' : BG G .carrier) (p : Id (BG G .carrier) z z')
  : Id (GroupHom (group_at G z) (group_at G z')) (blind_shape_move G z z' p) (group_at_move G z z' p)
  ≔ refl (group_at_move G z z' p)

def bridge_action_mono : blind_action_mono
  ≔ G z z' p x ↦
    refl ((u ↦ (u .fst, u .snd .fst)) : GroupMonos (group_at G z') → Σ Group (H ↦ GroupHom H (group_at G z')))
      (monos_gset_act G z z' p x)

{` lem:conj-abstract / xca:conj-abstract. The blind abstract monos are our AbstractMonosInto (abstr G); the
   equivalence is ours (concrete_abstract_monos_equiv, map (H, f) ↦ (abstr H, abstr f)); equivariance on (H, φ). `}
def bridge_def_abs_monos (G : Group) : Id Type (BlindAbsMonos G) (AbstractMonosInto (abstr G))
  ≔ refl (AbstractMonosInto (abstr G))

def bridge9w_conj_equivariant (G : Group) (g : USym G) (m : GroupMonos G)
  : Id (BlindAbsMonoData G)
      (blind_abs_mono_data G (concrete_to_abstract_mono G (gset_usym_act G (monos_gset G) g m)))
      (blind_abs_conj_act G g (blind_abs_mono_data G (concrete_to_abstract_mono G m)))
  ≔ let AG ≔ abstr G in let H ≔ m .fst in let f ≔ m .snd .fst in
    let cg ≔ conj_hom G (shape G) g in
    let D ≔ BlindAbsMonoData G in
    let dat : GroupMonos G → D ≔ x ↦ blind_abs_mono_data G (concrete_to_abstract_mono G x) in
    let A ≔ AbstractHom (abstr H) AG in
    concat D (dat (gset_usym_act G (monos_gset G) g m)) (dat (monos_conjugate G (shape G) (shape G) g m))
      (blind_abs_conj_act G g (dat m))
      (refl dat (monos_gset_usym_act G g m))
      (refl ((φ ↦ (abstr H, φ)) : A → D)
        (concat A (abstr_hom H G (group_hom_compose H G G f cg))
          (abstract_hom_compose (abstr H) AG AG (abstr_hom H G f) (abstr_hom G G cg))
          (abstract_hom_compose (abstr H) AG AG (abstr_hom H G f) (abstract_conj_hom AG g))
          (abstr_hom_compose H G G f cg)
          (refl (abstract_hom_compose (abstr H) AG AG (abstr_hom H G f)) (abstr_conj_hom_is_abstract_conj G g))))

def bridge_conj_abstract : blind_conj_abstract
  ≔ G ↦ (concrete_abstract_monos_equiv G, g x ↦ bridge9w_conj_equivariant G g x)

{` rem:typeofsubgpstrivifab (block 1268). (a) G abelian iff conj^g = id for all g. `}
def bridge_abelian_iff_conj_trivial : blind_abelian_iff_conj_trivial ≔ G ↦ abelian_iff_conj_identity G

{` Corrected: abelian ⇒ Mono(G) trivial; Q8 is a counterexample to the converse. `}
def bridge_mono_gset_trivial_iff_abelian_corrected : blind_mono_gset_trivial_iff_abelian_corrected
  ≔ G hab ↦ abelian_monos_trivial G hab

def bridge_mono_gset_trivial_counterexample : blind_mono_gset_trivial_counterexample
  ≔ (quaternion_monos_trivial, quaternion_not_abelian)

{` The literal iff statements are FALSE (Q8: all subgroups normal, not abelian). `}
def bridge_mono_gset_trivial_iff_abelian_refuted : Not blind_mono_gset_trivial_iff_abelian
  ≔ B ↦ quaternion_not_abelian (B quaternion_group .fst quaternion_monos_trivial)

def bridge9w_abs_monos_trivial_q8 (g : USym quaternion_group) (x : BlindAbsMonos quaternion_group)
  : Id (BlindAbsMonoData quaternion_group)
      (blind_abs_conj_act quaternion_group g (blind_abs_mono_data quaternion_group x)) (blind_abs_mono_data quaternion_group x)
  ≔ let G ≔ quaternion_group in
    let M ≔ GroupMonos G in let A ≔ AbstractMonosInto (abstr G) in
    let D ≔ BlindAbsMonoData G in
    let e ≔ concrete_abstract_monos_equiv G in
    let m ≔ equiv_inverse_map M A e x in
    let c : Id A (e .map m) x ≔ equiv_counit M A e x in
    let dat : A → D ≔ y ↦ blind_abs_mono_data G y in
    let cj : A → D ≔ y ↦ blind_abs_conj_act G g (blind_abs_mono_data G y) in
    calc
      cj x = cj (e .map m) by refl cj (inverse A (e .map m) x c)
      = dat (e .map (gset_usym_act G (monos_gset G) g m))
        by inverse D (dat (e .map (gset_usym_act G (monos_gset G) g m))) (cj (e .map m)) (bridge9w_conj_equivariant G g m)
      = dat (e .map m) by refl ((y ↦ dat (e .map y)) : M → D) (quaternion_monos_trivial g m)
      = dat x by refl dat c ∎

def bridge_abs_monos_trivial_iff_abelian_refuted : Not blind_abs_monos_trivial_iff_abelian
  ≔ B ↦ quaternion_not_abelian (B quaternion_group .fst bridge9w_abs_monos_trivial_q8)

{` Definition (subgroups.tex:1282) and the text after it. `}
def bridge_sub_gset_underlying : blind_sub_gset_underlying ≔ G ↦ subgroups_gset_underlying G

def bridge_sub_gset_action : blind_sub_gset_action
  ≔ G z z' p S ↦
    refl ((u ↦ (u .gset, u .point)) : Subgroups (group_at G z') → Σ (GSet G) (X ↦ X z' .fst))
      (subgroups_gset_act G z z' p S)

{` Definition (subgroups.tex:1295): E is ours (monos_to_subgroups), an equivalence at every z. `}
def bridge_def_E (G : Group) : Id (GSetHom G (monos_gset G) (subgroups_gset G)) (blind_E G) (monos_to_subgroups G)
  ≔ refl (monos_to_subgroups G)

def bridge_E_equiv : blind_E_equiv
  ≔ G z ↦ book_equivalence (monos_gset G z .fst) (subgroups_gset G z .fst) (monos_to_subgroups_equiv G z) .equiv

def bridge_E_at_shape : blind_E_at_shape ≔ G ↦ refl (mono_to_subgroup G)

{` xca:Sub(Sigma3) (1). `}
def bridge_sub_transitive_iff_trivial : blind_sub_transitive_iff_trivial ≔ G ↦ subgroups_transitive_iff_trivial G
