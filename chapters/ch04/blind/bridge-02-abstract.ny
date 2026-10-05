export "bridge-00-core"
export "../../../src/430-pointwise-abstract-groups"

{` Bridges for group.tex, section "Abstract groups" (blind file
   02-abstract.ny). The blind abstract group keeps isSet as a separate
   field and its laws without it; ours keeps isSet among the laws (as in
   absgroup.tex). Field orders and orientations otherwise agree. `}

def bridge_laws_to (S : Type) (e : S) (mul : S → S → S) (inv : S → S) (hS : isSet S)
  (l : BlindAbstractGroupLaws S e mul inv) : AbstractGroupLaws S e mul inv
  ≔ (hS, l .runit, l .lunit, l .assoc, l .invlaw)

def bridge_laws_from (S : Type) (e : S) (mul : S → S → S) (inv : S → S)
  (l : AbstractGroupLaws S e mul inv) : BlindAbstractGroupLaws S e mul inv
  ≔ (l .unit_right, l .unit_left, l .assoc, l .inv_right)

def bridge_ag (A : BlindAbstractGroup) : AbstractGroup
  ≔ (A .carrier, A .unit, A .mul, A .inv, bridge_laws_to (A .carrier) (A .unit) (A .mul) (A .inv) (A .is_set) (A .laws))

def bridge_ag_inv (G : AbstractGroup) : BlindAbstractGroup
  ≔ (G .carrier, G .laws .carrier_set, G .unit, G .mul, G .inv, bridge_laws_from (G .carrier) (G .unit) (G .mul) (G .inv) (G .laws))

{` def:abstractgroup (line 850). `}
def bridge_def_abstract_group : Equiv BlindAbstractGroup AbstractGroup
  ≔ quasi_inverse_equiv BlindAbstractGroup AbstractGroup bridge_ag bridge_ag_inv (A ↦ refl A) (G ↦ refl G)

def bridge_def_abstract_isab (A : BlindAbstractGroup) : Id Type (BlindAbstractIsAb A) (IsAbstractAbelian (bridge_ag A))
  ≔ refl (BlindAbstractIsAb A)

{` Line 875. `}
def bridge_rem_abstract_laws_prop : blind_rem_abstract_laws_prop
  ≔ S hS e mul inv u v ↦ refl (bridge_laws_from S e mul inv)
      (abstract_group_laws_prop S e mul inv (bridge_laws_to S e mul inv hS u) (bridge_laws_to S e mul inv hS v))

{` lem:idtypesgiveabstractgroups (line 883): the blind operations are ours
   on the nose. `}
def bridge_lem_idtypes_abstract_groups : blind_lem_idtypes_abstract_groups
  ≔ G ↦ (usym_set (bridge_g G),
      bridge_laws_from (USym (bridge_g G)) (usym_unit (bridge_g G)) (usym_mul (bridge_g G)) (usym_inv (bridge_g G))
        (usym_abstract_laws (bridge_g G)))

{` def:abstrG (line 896): equal to ours up to the (propositional) laws. `}
def bridge_def_abstr (h : blind_lem_idtypes_abstract_groups) (G : BlindGroup)
  : Id AbstractGroup (bridge_ag (blind_abstr h G)) (abstr (bridge_g G))
  ≔ abstract_group_laws_irrelevant (USym (bridge_g G)) (usym_unit (bridge_g G)) (usym_mul (bridge_g G)) (usym_inv (bridge_g G))
      (bridge_ag (blind_abstr h G) .laws) (usym_abstract_laws (bridge_g G))

{` xca:abstract-group-of-maps (line 908). The literal statement is refuted
   by ours (X = ∅, G = abstr Σ₃); the corrected one (X merely inhabited) is
   ours. `}
def bridge_xca_abstract_group_of_maps_refuted : Not blind_xca_abstract_group_of_maps
  ≔ h ↦ abstract_group_of_maps_abelian_converse_fails
      (G X ab ↦ h (bridge_ag_inv G) (X .fst) (X .snd) .snd .fst ab)

def bridge_xca_abstract_group_of_maps_corrected : blind_xca_abstract_group_of_maps_corrected
  ≔ A X hX x0 ↦
    (bridge_laws_from (X → A .carrier) (_ ↦ A .unit) (blind_pointwise_mul A X) (f ↦ x ↦ A .inv (f x))
       (pointwise_group_laws (bridge_ag A) X),
     (pointwise_abelian_reflect (bridge_ag A) X x0, pointwise_abelian (bridge_ag A) X))
