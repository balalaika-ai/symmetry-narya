export "05-homs"
export "../../../src/745-sigma-two-cyclic-two-isos"

{` Bridges bridge for xca:SG2=SG2-contractible (absgroup.tex 1160): the
   blind C_2 is cyclic_group_fin 1, ours cyclic_group 2; they are identified
   by cyclic_group_fin_path (module 404), along which our
   sigma_two_cyclic_two_isos_contractible is transported. `}

def bridge_xca_sg2_c2_contractible : blind_xca_sg2_c2_contractible
  ≔ let one : Nat ≔ suc. zero. in
    transport Group (K ↦ BookIsContr (GroupIso (symmetric_group two) K)) (cyclic_group two) (cyclic_group_fin one)
      (inverse Group (cyclic_group_fin one) (cyclic_group two) (cyclic_group_fin_path one))
      sigma_two_cyclic_two_isos_contractible
