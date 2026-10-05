export "bridge-00-core"
export "../../../src/720-list-monoids"
export "../../../src/722-opposite-abstract-groups"
export "../../../src/723-abstract-conjugation"
export "../../../src/724-sheargroups"
export "../../../src/725-furstenberg-groups"
export "../../../src/726-monoid-groupoid"

{` Bridges for absgroup.tex, sec:monoids (blind file 01-monoids). `}

{` exa:monoid. `}
def bridge_exa_monoid : blind_exa_monoid ≔ S hS ↦ list_monoid_laws S hS

{` rem:inverses-as-property: the property axiom:mere-inverse is ours. `}
def bridge_def_mere_inverse (S : Type) (e : S) (mu : S → S → S)
  : Id Type (BlindMereInverse S e mu) (MereInverses S e mu)
  ≔ refl (MereInverses S e mu)

{` lem:group-inv-operation. `}
def bridge_lem_group_inv_operation : blind_lem_group_inv_operation
  ≔ S e mu laws minv ↦ group_inv_operation_contractible S e mu laws minv

{` rem:abs-iso. An isomorphism in our sense gives the blind (printed) form. `}
def bridge_is_abs_iso_of (G H : AbstractGroup) (φ : AbstractIso G H)
  : BlindIsAbsIso (bridge_ag7_inv G) (bridge_ag7_inv H) (φ .fst .map)
  ≔ (book_equivalence (G .carrier) (H .carrier) (φ .fst) .equiv,
     (inverse (H .carrier) (φ .fst .map (G .unit)) (H .unit) (abstract_hom_preserves_unit G H (φ .fst .map) (φ .snd)),
      s t ↦ inverse (H .carrier) (φ .fst .map (G .mul s t)) (H .mul (φ .fst .map s) (φ .fst .map t)) (φ .snd s t)))

def bridge_iso_of_blind (G H : BlindAbsGroup) (f : BlindAbsIso G H) : AbstractIso (bridge_ag7 G) (bridge_ag7 H)
  ≔ (native_equivalence (G .carrier) (H .carrier) (f .fst, f .snd .fst),
     s t ↦ inverse (H .carrier) (H .mul (f .fst s) (f .fst t)) (f .fst (G .mul s t)) (f .snd .snd .snd s t))

def bridge_rem_abs_iso : blind_rem_abs_iso
  ≔ G H f ↦ (refl bridge_ag7_inv (abstract_group_path_from_iso (bridge_ag7 G) (bridge_ag7 H) (bridge_iso_of_blind G H f)),
             s ↦ refl (f .fst s))

{` The exercise after rem:abs-iso (the analysis). `}
def bridge_xca_abs_iso_analysis : blind_xca_abs_iso_analysis
  ≔ G H ↦ book_equivalence (Id BlindAbsGroup G H) (AbstractGroupPathEquations (bridge_ag7 G) (bridge_ag7 H))
      (compose_equiv (Id BlindAbsGroup G H) (Id AbstractGroup (bridge_ag7 G) (bridge_ag7 H))
        (AbstractGroupPathEquations (bridge_ag7 G) (bridge_ag7 H))
        (bridge_ag_paths G H) (abstract_group_path_equations_equiv (bridge_ag7 G) (bridge_ag7 H)))

{` xca:op-abs-group. `}
def bridge_xca_op_abs_group : blind_xca_op_abs_group
  ≔ G ↦ let G' ≔ bridge_ag7 G in
    (group_laws_from_record (G .carrier) (G .unit) (abstract_op_mul G') (G .inv) (abstract_op_laws G'),
     bridge_is_abs_iso_of G' (abstract_op_group G') (abstract_op_iso G'))

{` xca:conj. `}
def bridge_xca_conj : blind_xca_conj
  ≔ G g ↦ bridge_is_abs_iso_of (bridge_ag7 G) (bridge_ag7 G) (abstract_conj_iso (bridge_ag7 G) g)

{` xca:left-inv-involution. `}
def bridge_xca_left_inv_involution : blind_xca_left_inv_involution
  ≔ G g ↦ (ag_inv_left_book (bridge_ag7 G) g, ag_inv_involution (bridge_ag7 G) g)

{` xca:typemonoidisgroupoid. `}
def bridge_groupoid_transfer (A B : Type) (e : Equiv A B) (h : isGroupoid A) : isGroupoid B
  ≔ hlevel_to_groupoid B (hlevel_equiv (suc. (suc. (suc. zero.))) A B e (groupoid_to_hlevel A h))

def bridge_xca_typemonoidisgroupoid : blind_xca_typemonoidisgroupoid
  ≔ (bridge_groupoid_transfer Monoid BlindMonoid (canonical_inverse_equiv BlindMonoid Monoid bridge_def_monoid)
       monoid_groupoid,
     bridge_groupoid_transfer AbstractGroup BlindAbsGroup
       (canonical_inverse_equiv BlindAbsGroup AbstractGroup bridge_def_abs_group) abstract_group_groupoid)

{` xca:cheapgroup: the blind sheargroup is ours (fields regrouped). `}
def bridge_shear (X : ShearGroup) : BlindShearGroup
  ≔ (X .carrier, X .laws .carrier_set, X .unit, X .op, X .laws .unit_left, X .laws .self_inverse, X .laws .shear)

def bridge_shear_inv (X : BlindShearGroup) : ShearGroup
  ≔ (X .carrier, X .unit, X .op,
     (carrier_set ≔ X .is_set, unit_left ≔ X .law1, self_inverse ≔ X .law2, shear ≔ X .law3))

def bridge_def_shear_group : Equiv ShearGroup BlindShearGroup
  ≔ quasi_inverse_equiv ShearGroup BlindShearGroup bridge_shear bridge_shear_inv (X ↦ refl X) (X ↦ refl X)

def bridge_xca_cheapgroup : blind_xca_cheapgroup
  ≔ book_equivalence BlindAbsGroup BlindShearGroup
      (compose_equiv BlindAbsGroup AbstractGroup BlindShearGroup bridge_def_abs_group
        (compose_equiv AbstractGroup ShearGroup BlindShearGroup abstract_shear_equiv bridge_def_shear_group))

{` The exercise on Furstenberg groups. `}
def bridge_furstenberg (X : BlindFurstenbergGroup) : FurstenbergGroup
  ≔ (X .carrier, X .op,
     (carrier_set ≔ X .is_set, inhabited ≔ X .nonempty, cancel ≔ X .law1, solution ≔ X .law2))

def bridge_furstenberg_inv (X : FurstenbergGroup) : BlindFurstenbergGroup
  ≔ (X .carrier, X .laws .carrier_set, X .laws .inhabited, X .op, X .laws .cancel, X .laws .solution)

def bridge_def_furstenberg_group : Equiv BlindFurstenbergGroup FurstenbergGroup
  ≔ quasi_inverse_equiv BlindFurstenbergGroup FurstenbergGroup bridge_furstenberg bridge_furstenberg_inv
      (X ↦ refl X) (X ↦ refl X)

def bridge_xca_furstenberg : blind_xca_furstenberg
  ≔ book_equivalence BlindFurstenbergGroup BlindAbsGroup
      (compose_equiv BlindFurstenbergGroup FurstenbergGroup BlindAbsGroup bridge_def_furstenberg_group
        (compose_equiv FurstenbergGroup AbstractGroup BlindAbsGroup furstenberg_abstract_equiv
          (canonical_inverse_equiv BlindAbsGroup AbstractGroup bridge_def_abs_group)))
