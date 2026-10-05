export "03-abelian-sc2types"
export "../../../src/1205-abelian-sc2-equivalence"

{` Bridges for abelian.tex, thm:abelian-groups-weq-sc2types (block 409). BlindBB is our BB and BlindUUsc2
   (the proof's U_*^{=2}) is our SimplyConnectedTwoType, both by refl. The statement's codomain (simply connected
   with a 2-type carrier) is equivalent to ours fibrewise: both structures are propositions, a connected type whose
   loop type is a groupoid has groupoid path types everywhere (sc2_two_type), and conversely. `}

def bridge_def_bb (G : Group) : Id Pointed (BlindBB G) (BB G) ≔ refl (BB G)

def bridge_def_uusc2 : Id Type BlindUUsc2 SimplyConnectedTwoType ≔ refl SimplyConnectedTwoType

def bridge_sc2_to_blind (X : Pointed) (s : SC2Structure X)
  : Product (BlindIsSimplyConnected X) (HLevel (suc. (suc. (suc. (suc. zero.)))) (X .carrier))
  ≔ ((s .fst, s .snd .fst),
     x y ↦ groupoid_to_hlevel (Id (X .carrier) x y) (sc2_two_type (X, s) x y))

def bridge_sc2_of_blind (X : Pointed) (b : Product (BlindIsSimplyConnected X) (HLevel (suc. (suc. (suc. (suc. zero.)))) (X .carrier)))
  : SC2Structure X
  ≔ (b .fst .fst, (b .fst .snd, hlevel_to_groupoid (Loop X) (b .snd (X .point) (X .point))))

def bridge_def_sc2_structure (X : Pointed)
  : Equiv (SC2Structure X) (Product (BlindIsSimplyConnected X) (HLevel (suc. (suc. (suc. (suc. zero.)))) (X .carrier)))
  ≔ iff_equiv (SC2Structure X) (Product (BlindIsSimplyConnected X) (HLevel (suc. (suc. (suc. (suc. zero.)))) (X .carrier)))
      (sc2_structure_prop X)
      (product_prop (BlindIsSimplyConnected X) (HLevel (suc. (suc. (suc. (suc. zero.)))) (X .carrier))
        (simply_connected_prop X) (hlevel_isprop (suc. (suc. (suc. (suc. zero.)))) (X .carrier)))
      (bridge_sc2_to_blind X) (bridge_sc2_of_blind X)

def bridge_def_sc2_types : Equiv SimplyConnectedTwoType BlindSimplyConnectedTwoTypes
  ≔ family_equiv Pointed SC2Structure
      (X ↦ Product (BlindIsSimplyConnected X) (HLevel (suc. (suc. (suc. (suc. zero.)))) (X .carrier)))
      bridge_def_sc2_structure

{` thm:abelian-groups-weq-sc2types (abelian.tex:409), both codomains. `}
def bridge_abelian_groups_weq_sc2types : blind_abelian_groups_weq_sc2types
  ≔ book_equivalence AbelianGroup BlindSimplyConnectedTwoTypes
      (compose_equiv AbelianGroup SimplyConnectedTwoType BlindSimplyConnectedTwoTypes abelian_groups_sc2_equiv
        bridge_def_sc2_types)

def bridge_abelian_groups_weq_sc2types_proof_codomain : blind_abelian_groups_weq_sc2types_proof_codomain
  ≔ abelian_groups_sc2_book_equiv
