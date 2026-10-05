export "07-intersections"
export "../../../src/992-conjugate-counterexamples"

{` Bridges for lem:thereisaconjugate (subgroups.tex:1840, blind file 07-intersections). The blind H-fixed
   points are ours (IsSubgroupFixedPoint, module 913) by refl; the corrected conjugate (H, F, g then Bf_pt) is our
   conjugate_mono. The literal statement (pointing g⁻¹ then Bf_pt) is FALSE: counterexample Σ_3 acting on Fin 3,
   H = T_0 the stabilizer of 0, g = (0 1 2), x = 2. `}

def bridge_def_is_h_fixed (G : Group) (X : GSet G) (m : GroupMonos G) (x : gset_underlying G X)
  : Id Type (BlindIsHFixed G X (m .fst) (m .snd .fst) x) (IsSubgroupFixedPoint G X m x)
  ≔ refl (IsSubgroupFixedPoint G X m x)

def bridge_def_conjugate_hom_corrected (G : Group) (g : USym G) (m : GroupMonos G)
  : Id (GroupHom (m .fst) G) (blind_conjugate_hom_corrected G (m .fst) (m .snd .fst) g) (conjugate_mono G g m .snd .fst)
  ≔ refl (conjugate_mono G g m .snd .fst)

{` The literal conjugate is our conjugate by g⁻¹. `}
def bridge_def_conjugate_hom (G : Group) (g : USym G) (m : GroupMonos G)
  : Id (GroupHom (m .fst) G) (blind_conjugate_hom G (m .fst) (m .snd .fst) g) (conjugate_mono G (usym_inv G g) m .snd .fst)
  ≔ refl (conjugate_mono G (usym_inv G g) m .snd .fst)

def bridge_thereisaconjugate_corrected : blind_thereisaconjugate_corrected
  ≔ G X x g m ↦ conjugate_fixed_point_iff G X x g m

{` The literal statement is refuted in src (module 992, thereisaconjugate_printed is blind_thereisaconjugate by
   definition): Σ_3 acting on Fin 3, H = T_0, g = (0 1 2), x = 2. `}
def bridge_thereisaconjugate_refuted : Not blind_thereisaconjugate ≔ thereisaconjugate_printed_refuted
