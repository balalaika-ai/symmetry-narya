export "04-ev-sections"
export "../../../src/1331-pointed-map-identifications"

{` Bridges for fields.tex, sections of ev (blocks 281, 315, 362, 372). blind_ev_id is
   identity_path_evaluation by refl (happly i x ≡ i (refl x)), so a blind section (s, hs) is literally an
   IdentityPathEvSection. The blind statements of 281 and 372 assert only the existence of some map
   (f÷ = f'÷) → (f = f'); ours is a specific map. blind_rho is concat_1p, and the blind parts 2-3 of
   xca:ev-section-loopsA are ev_section_i and ev_section_whisker_refl verbatim (up to η). `}

def bridge_def_ev_id (A : Pointed)
  : Id (Id (A .carrier → A .carrier) (identity (A .carrier)) (identity (A .carrier)) → Loop A)
      (blind_ev_id A) (identity_path_evaluation A)
  ≔ refl (identity_path_evaluation A)

{` con:Id-(B->*A) (fields.tex:281). `}
def bridge_con_Id_B_ptd_A : blind_con_Id_B_ptd_A
  ≔ A s hs B f f' e ↦ pointed_map_path_from_underlying A (s, hs) B f f' e

{` con:ev-section-loopsA (fields.tex:315). `}
def bridge_con_ev_section_loopsA : blind_con_ev_section_loopsA
  ≔ A ↦ (loops_ev_section A, loops_ev_section_beta A)

{` xca:ev-section-loopsA (fields.tex:362). `}
def bridge_def_rho (A : Type) (a x : A) (q : Id A a x)
  : Id (Id (Id A a x) (concat A a a x (refl a) q) q) (blind_rho A a x q) (concat_1p A a x q)
  ≔ refl (concat_1p A a x q)

def bridge_xca_ev_section_rho : blind_xca_ev_section_rho ≔ A a x q ↦ concat_1p A a x q

def bridge_xca_ev_section_i : blind_xca_ev_section_i ≔ A a p β ↦ ev_section_i A a p β

def bridge_xca_ev_section_loopsA : blind_xca_ev_section_loopsA ≔ A a α ↦ ev_section_whisker_refl A a α

{` cor:Id-(B->*loopsA) (fields.tex:372). `}
def bridge_cor_Id_B_ptd_loopsA : blind_cor_Id_B_ptd_loopsA
  ≔ A B f f' e ↦ loops_pointed_map_path_from_underlying A B f f' e
