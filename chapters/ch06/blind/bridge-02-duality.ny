import "bridge-00-core"
import "bridge-01-wild-cats"
import "../../../src/607-terminal-initial-objects"
import "../../../src/608-opposite-involution"
import "../../../src/609-monos-and-epis"
import "../../../src/687-group-monomorphisms"

{` Bridges for cats.tex, section "Abstract notions and duality"
   (blind file 02). `}

{` The categories of sets and of groups are ours on the nose. `}
def bridge_def_set_precat_cat : Id Precat (bridge_p blind_set_precat) (category_precat SetCat)
  ≔ refl (category_precat SetCat)

def bridge_def_group_precat : Id Precat (bridge_p blind_group_precat) (category_precat GroupCat)
  ≔ refl (category_precat GroupCat)

{` def:terminal-obj, def:initial-obj. `}
def bridge_def_terminal (C : BlindWildPrecat) (t : C .ob)
  : Id Type (BlindIsTerminal C t) (IsTerminalObj (bridge_w C) t) ≔ refl (BlindIsTerminal C t)

def bridge_def_initial (C : BlindWildPrecat) (i : C .ob)
  : Id Type (BlindIsInitial C i) (IsInitialObj (bridge_w C) i) ≔ refl (BlindIsInitial C i)

{` xca:terminal-prop. `}
def bridge_xca_terminal_prop : blind_xca_terminal_prop ≔ C u ↦ terminal_objects_prop (bridge_w C) u

{` xca:unit-ptd-types. `}
def bridge_xca_unit_ptd_types : blind_xca_unit_ptd_types ≔ pointed_unit_zero_object

{` lem:op-idem. The blind involution is ours conjugated by the record
   translation; the identification (C^op)^op = C is ours transported by
   bridge_w_inv. `}
def bridge_op_op_path (C : BlindWildPrecat) : Id BlindWildPrecat (blind_op (blind_op C)) C
  ≔ refl bridge_w_inv (opposite_opposite_path (bridge_w C))

def bridge_lem_op_idem : blind_lem_op_idem
  ≔ (book_quasi_inverse_equiv BlindWildPrecat BlindWildPrecat blind_op blind_op bridge_op_op_path bridge_op_op_path
       .equiv,
     bridge_op_op_path)

{` def:mono-in-cat, def:epi-in-cat. `}
def bridge_def_mono (C : BlindWildPrecat) (a b : C .ob) (f : C .hom a b)
  : Id Type (BlindIsMono C a b f) (IsMono (bridge_w C) a b f) ≔ refl (BlindIsMono C a b f)

def bridge_def_epi (C : BlindWildPrecat) (a b : C .ob) (f : C .hom a b)
  : Id Type (BlindIsEpi C a b f) (IsEpi (bridge_w C) a b f) ≔ refl (BlindIsEpi C a b f)

{` xca:mono-cat-grp. `}
def bridge_xca_mono_cat_grp : blind_xca_mono_cat_grp ≔ G H f ↦ group_mono_iff_usym_injective G H f

{` xca:monos-epis-sets-types. `}
def bridge_xca_monos_types : blind_xca_monos_types
  ≔ A B f ↦ (type_mono_embedding_equiv A B f .map,
             equiv_inverse_map (IsMono TypeWild A B f) (IsEmbedding A B f) (type_mono_embedding_equiv A B f))

def bridge_xca_epis_sets : blind_xca_epis_sets
  ≔ A B f ↦ (set_epi_surjective_equiv A B f .map,
             equiv_inverse_map (IsEpi (SetCat .wild) A B f) (Surjective (A .fst) (B .fst) f)
               (set_epi_surjective_equiv A B f))

{` xca:monos-epis-preorder. `}
def bridge_xca_monos_epis_preorder : blind_xca_monos_epis_preorder
  ≔ C a b f ↦ preorder_arrow_mono_epi (bridge_pre C) a b f
