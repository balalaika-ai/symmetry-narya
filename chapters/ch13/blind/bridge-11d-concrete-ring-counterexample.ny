export "bridge-11a-concrete-ring-def"
export "../../../src/1393-concrete-ring-printed-law-insufficient"
export "../../../src/223-constructed-circle"

{` Bridges, xca:Rconcring->URabstring (1222), literal statement refuted. With only the printed unit law as
   hypothesis the blind statement is false: module 1393 gives data (R = ℤ × ℤ) satisfying the printed law with
   a · 1 ≠ a. The argument is first made for arbitrary data (cheap to check), then instantiated. `}

def b11d_refute_generic (C : CircleSignature) (D : BlindConcRingData C) (u : BlindConcRingUnitLaw C D)
  (a : USym (D .grp .fst))
  (ha : Id (USym (abelian_hom_group (D .grp .fst) (D .grp)))
          (usym_hom (D .grp .fst) (abelian_hom_group (D .grp .fst) (D .grp)) (D .mu) a)
          (usym_unit (abelian_hom_group (D .grp .fst) (D .grp))))
  (ne : Not (Id (USym (D .grp .fst)) a (usym_unit (D .grp .fst))))
  (h : (D : BlindConcRingData C) → BlindConcRingUnitLaw C D
       → Product
           (MonoidLaws (USym (D .grp .fst)) (usym_hom (blind_Z C) (D .grp .fst) (D .one) (C .loop)) (blind_concring_mul C D))
           (BlindDistrLaws (USym (D .grp .fst)) (blind_concring_mul C D) (usym_mul (D .grp .fst))))
  : Empty
  ≔ let R ≔ D .grp .fst in let H ≔ abelian_hom_group R (D .grp) in
    let one ≔ usym_hom (blind_Z C) R (D .one) (C .loop) in
    let ev ≔ hom_of_symmetry R (D .grp) in
    ne (concat (USym R) a (usym_hom R R (ev (usym_hom R H (D .mu) a)) one) (usym_unit R)
         (concat (USym R) a (blind_concring_mul C D a one) (usym_hom R R (ev (usym_hom R H (D .mu) a)) one)
           (inverse (USym R) (blind_concring_mul C D a one) a (h D u .fst .snd .fst a .fst))
           (b11a_mul_value C D a one))
         (evaluation_kernel_trivial R H (D .mu) ev (abelian_hom_usym_mul R (D .grp)) a ha one))

def b11d_ce_data (C : CircleSignature) : BlindConcRingData C ≔ (ce_group C, ce_one C, ce_mu C)

def b11d_ce_element_nontrivial (C : CircleSignature)
  (p : Id (USym (ce_group C .fst)) (ce_element C) (usym_unit (ce_group C .fst))) : Empty
  ≔ circle_loop_not_refl C
      (refl ((v ↦ v .snd) : USym (ce_group C .fst) → Id (C .carrier) (C .base) (C .base)) p)

def bridge_xca_Rconcring_URabstring_refuted_at (C : CircleSignature)
  (h : (D : BlindConcRingData C) → BlindConcRingUnitLaw C D
       → Product
           (MonoidLaws (USym (D .grp .fst)) (usym_hom (blind_Z C) (D .grp .fst) (D .one) (C .loop)) (blind_concring_mul C D))
           (BlindDistrLaws (USym (D .grp .fst)) (blind_concring_mul C D) (usym_mul (D .grp .fst))))
  : Empty
  ≔ b11d_refute_generic C (b11d_ce_data C) (b11_unit_law_from C (b11d_ce_data C) (ce_unit_law C))
      (ce_element C) (ce_element_kernel C) (b11d_ce_element_nontrivial C) h

def bridge_xca_Rconcring_URabstring_negation : Not blind_xca_Rconcring_URabstring
  ≔ h ↦ bridge_xca_Rconcring_URabstring_refuted_at constructed_circle (h constructed_circle)
