export "bridge-00-core"
export "06-infinity-groups"
export "../../../src/485-infinity-groups"
export "../../../src/423-group-points-and-automorphisms"

{` Bridges for group.tex, section "∞-groups" (blind file
   06-infinity-groups.ny). As for groups, the blind U^{>0}_* is a nested Σ
   and the blind ∞-groups and their homomorphisms are Copy types; ours are
   records. Round trips are refl (after matching on copy.). `}

{` def:inftygps (line 2347). `}
def bridge_ptc (X : BlindPtConnTypes) : PointedConnectedType ≔ (X .fst, X .snd .fst, X .snd .snd)
def bridge_ptc_inv (X : PointedConnectedType) : BlindPtConnTypes ≔ (X .carrier, (X .point, X .connected))

def bridge_def_ptconn_types : Equiv BlindPtConnTypes PointedConnectedType
  ≔ quasi_inverse_equiv BlindPtConnTypes PointedConnectedType bridge_ptc bridge_ptc_inv (X ↦ refl X) (X ↦ refl X)

def bridge_ig (G : BlindInfGroup) : InftyGroup ≔ mk_infty_group (bridge_ptc (blind_inf_clf G))
def bridge_ig_inv (G : InftyGroup) : BlindInfGroup ≔ blind_inf_mkgroup (bridge_ptc_inv (infty_group_B G))

def bridge_ig_eta : (G : BlindInfGroup) → Id BlindInfGroup (bridge_ig_inv (bridge_ig G)) G
  ≔ [ copy. X ↦ refl (blind_inf_mkgroup X) ]

def bridge_def_infgroup : Equiv BlindInfGroup InftyGroup
  ≔ quasi_inverse_equiv BlindInfGroup InftyGroup bridge_ig bridge_ig_inv bridge_ig_eta (G ↦ refl G)

{` def:classifyingspace (line 2371). `}
def bridge_def_inf_BG (G : BlindInfGroup) : Id Pointed (blind_inf_BG G) (infty_BG (bridge_ig G)) ≔ refl (blind_inf_BG G)

def bridge_def_inf_shape (G : BlindInfGroup) : Id (blind_inf_clf G .fst) (blind_inf_shape G) (infty_shape (bridge_ig G))
  ≔ refl (blind_inf_shape G)

{` Line 2378: the automorphism ∞-group is ours on the nose. `}
def bridge_def_inf_aut (A : Type) (a : A) : Id InftyGroup (bridge_ig (blind_inf_Aut A a)) (infty_automorphism_group A a)
  ≔ refl (infty_automorphism_group A a)

{` rem:autinfgp (line 2389). `}
def bridge_rem_universe_set_component_groupoid : blind_rem_universe_set_component_groupoid
  ≔ S ↦ universe_set_component_groupoid (S .fst) (S .snd)

def bridge_def_group_to_infgroup (G : BlindGroup)
  : Id InftyGroup (bridge_ig (blind_group_to_infgroup G)) (group_to_infty_group (bridge_g G))
  ≔ refl (group_to_infty_group (bridge_g G))

def bridge_rem_group_infgroup_injection : blind_rem_group_infgroup_injection
  ≔ G H ↦
    let tG ≔ blind_group_to_infgroup G in let tH ≔ blind_group_to_infgroup H in
    let Q ≔ equivalence_on_paths BlindInfGroup InftyGroup bridge_def_infgroup tG tH in
    let f ≔ map_path BlindGroup BlindInfGroup blind_group_to_infgroup G H in
    let ours : Equiv (Id BlindGroup G H) (Id InftyGroup (group_to_infty_group (bridge_g G)) (group_to_infty_group (bridge_g H)))
      ≔ compose_equiv (Id BlindGroup G H) (Id Group (bridge_g G) (bridge_g H))
          (Id InftyGroup (group_to_infty_group (bridge_g G)) (group_to_infty_group (bridge_g H)))
          (bridge_group_paths G H) (group_infty_paths_equiv (bridge_g G) (bridge_g H)) in
    book_equivalence (Id BlindGroup G H) (Id BlindInfGroup tG tH)
      (equiv_change_map (Id BlindGroup G H) (Id BlindInfGroup tG tH)
        (compose_equiv (Id BlindGroup G H) (Id InftyGroup (bridge_ig tG) (bridge_ig tH)) (Id BlindInfGroup tG tH)
          ours (canonical_inverse_equiv (Id BlindInfGroup tG tH) (Id InftyGroup (bridge_ig tG) (bridge_ig tH)) Q))
        f
        (p ↦ equiv_retraction (Id BlindInfGroup tG tH) (Id InftyGroup (bridge_ig tG) (bridge_ig tH)) Q (f p))) .equiv

{` Line 2400: homomorphisms of ∞-groups. `}
def bridge_def_infhom (G H : BlindInfGroup) : Equiv (BlindInfHom G H) (InftyGroupHom (bridge_ig G) (bridge_ig H))
  ≔ quasi_inverse_equiv (BlindInfHom G H) (InftyGroupHom (bridge_ig G) (bridge_ig H))
      (f ↦ mk_infty_hom (bridge_ig G) (bridge_ig H) (blind_inf_Bhom G H f))
      (f ↦ blind_inf_mkhom G H (infty_hom_B (bridge_ig G) (bridge_ig H) f))
      [ copy. k ↦ refl (blind_inf_mkhom G H k) ] (f ↦ refl f)

{` Line 779, "similarly for ∞-groups". `}
def bridge_xca_change_basepoint_inf : blind_xca_change_basepoint_inf
  ≔ X b ↦ let Y : BlindPtConnTypes ≔ (X .fst, (b, X .snd .snd)) in
    let T ≔ Id BlindInfGroup (blind_inf_mkgroup X) (blind_inf_mkgroup Y) in
    mere_rec (Id InftyGroup (mk_infty_group (bridge_ptc X)) (mk_infty_group (bridge_ptc Y))) (Mere T) (mere_isprop T)
      (p ↦ mere T (refl bridge_ig_inv p))
      (infty_group_points_merely_equal (X .fst) (X .snd .fst) b (X .snd .snd))
