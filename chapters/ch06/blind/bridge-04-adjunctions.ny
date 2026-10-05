import "bridge-00-core"
import "bridge-01-wild-cats"
import "../../../src/610-preorder-functors-and-adjoints"
import "../../../src/611-fraction-order-rounding"
import "../../../src/613-subtype-image-adjunctions"
import "../../../src/614-truncation-functor"
import "../../../src/615-basepoint-functors"
import "../../../src/663-sigma-pi-adjunctions"
import "../../../src/664-set-sigma-pi-adjunctions"

{` Bridges for cats.tex, section "Adjunctions" (blind file 04).
   The record translation BlindRightAdjoint ↔ RightAdjointData is in the
   core (bridge_radj, bridge_def_right_adjoint). For a given left adjoint F
   with blind functor laws, our RightAdjointData for the same actions on
   objects and arrows gives the blind natural isomorphism field by field
   (the field types only involve the actions of F on objects and arrows). `}

def bridge_def_adjunction (C D : BlindWildPrecat)
  : Equiv (BlindAdjunction C D) (WildAdjunction (bridge_w C) (bridge_w D))
  ≔ quasi_inverse_equiv (BlindAdjunction C D) (WildAdjunction (bridge_w C) (bridge_w D))
      (A ↦ (bridge_f C D (A .left), bridge_radj C D (A .left) (A .right, A .adj)))
      (A ↦ (bridge_f_inv C D (A .left), bridge_radj_inv C D (bridge_f_inv C D (A .left)) (A .right_adjoint) .fst,
            bridge_radj_inv C D (bridge_f_inv C D (A .left)) (A .right_adjoint) .snd))
      (A ↦ refl A) (A ↦ refl A)

{` xca:adj-triangles. `}
def bridge_xca_adj_triangles : blind_xca_adj_triangles
  ≔ C D A ↦
    (c ↦ adjunction_triangle_left (bridge_w C) (bridge_w D) (bridge_f C D (A .left))
           (bridge_radj C D (A .left) (A .right, A .adj)) c,
     d ↦ adjunction_triangle_right (bridge_w C) (bridge_w D) (bridge_f C D (A .left))
           (bridge_radj C D (A .left) (A .right, A .adj)) d)

{` xca:adj-from-triangles. Our adjunction_from_triangles has transposition
   α(f) = G(f) ∘ η_c (triangle_transpose), as the blind statement. `}
def bridge_triangle_data (C D : BlindWildPrecat) (F : BlindWildFunctor C D) (G : BlindWildFunctor D C)
  (eta : BlindNatTrans C C (blind_functor_id C) (blind_functor_comp C D C G F))
  (eps : BlindNatTrans D D (blind_functor_comp D C D F G) (blind_functor_id D))
  (t1 : (c : C .ob) → Id (D .hom (F .fob c) (F .fob c))
     (D .comp (F .fob c) (F .fob (G .fob (F .fob c))) (F .fob c)
        (eps .fst (F .fob c)) (F .fhom c (G .fob (F .fob c)) (eta .fst c)))
     (D .idn (F .fob c)))
  (t2 : (d : D .ob) → Id (C .hom (G .fob d) (G .fob d))
     (C .comp (G .fob d) (G .fob (F .fob (G .fob d))) (G .fob d)
        (G .fhom (F .fob (G .fob d)) d (eps .fst d)) (eta .fst (G .fob d)))
     (C .idn (G .fob d)))
  : RightAdjointData (bridge_w C) (bridge_w D) (bridge_f C D F)
  ≔ adjunction_from_triangles (bridge_w C) (bridge_w D) (bridge_f C D F)
      (right ≔ bridge_f D C G,
       unit ≔ bridge_nt C C (blind_functor_id C) (blind_functor_comp C D C G F) eta,
       counit ≔ bridge_nt D D (blind_functor_comp D C D F G) (blind_functor_id D) eps,
       triangle_left ≔ t1,
       triangle_right ≔ t2)

def bridge_xca_adj_from_triangles : blind_xca_adj_from_triangles
  ≔ C D F G eta eps t1 t2 ↦
    (bridge_triangle_data C D F G eta eps t1 t2 .transpose_iso,
     (bridge_triangle_data C D F G eta eps t1 t2 .natural_right,
      c c' d f ↦ bridge_triangle_data C D F G eta eps t1 t2 .natural_left c c' f d))

{` ex:trunc-adj. `}
def bridge_ex_trunc_adj : blind_ex_trunc_adj
  ≔ k tl ↦ (trunc_right_adjoint k .transpose_iso,
            (trunc_right_adjoint k .natural_right, c c' d f ↦ trunc_right_adjoint k .natural_left c c' f d))

{` ex:pt-unpt-adj (corrected). Ours has the same transposition
   (restriction along inl); the left-naturality square is refl on both
   sides (it only evaluates f_+ at inl), the rest is ours. `}
def bridge_ex_pt_unpt_adj_corrected : blind_ex_pt_unpt_adj_corrected
  ≔ pl ↦ (plus_forget_right_adjoint .transpose_iso,
          (plus_forget_right_adjoint .natural_right,
           A A' X f ↦ refl ((g ↦ x ↦ g .fst (inl. (f x))) : BookPointedMap (plus_pointed A) X → A' → X .carrier)))

{` ex:Sigma-Pi-adj. The blind families of sets/types are ours on the nose. `}
def bridge_def_family_set_precat (A : Type) : Id Precat (bridge_p (blind_family_set_precat A)) (FamilySetPrecat A)
  ≔ refl (FamilySetPrecat A)

def bridge_def_family_wild_precat (A : Type) : Id WildPrecat (bridge_w (blind_family_wild_precat A)) (FamilyWild A)
  ≔ refl (FamilyWild A)

def bridge_ex_sigma_pi_adj_sets : blind_ex_sigma_pi_adj_sets
  ≔ A B f ll ↦
    let R ≔ set_family_sum_right_adjoint A B f in
    let S ≔ set_family_product_right_adjoint A B f in
    ((R .transpose, (R .transpose_iso, (R .natural_right, c c' d g ↦ R .natural_left c c' g d))),
     (S .transpose, (S .transpose_iso, (S .natural_right, c c' d g ↦ S .natural_left c c' g d))))

def bridge_ex_sigma_pi_adj_types : blind_ex_sigma_pi_adj_types
  ≔ A B f ↦
    let R ≔ family_sum_right_adjoint A B f in
    let S ≔ family_product_right_adjoint A B f in
    ((R .transpose, (R .transpose_iso, (R .natural_right, c c' d g ↦ R .natural_left c c' g d))),
     (S .transpose, (S .transpose_iso, (S .natural_right, c c' d g ↦ S .natural_left c c' g d))))

def bridge_ex_sigma_pi_adj_terminal : blind_ex_sigma_pi_adj_terminal
  ≔ A ↦
    let R ≔ family_total_right_adjoint A in
    let S ≔ family_pi_right_adjoint A in
    ((R .transpose, (R .transpose_iso, (R .natural_right, c c' d g ↦ R .natural_left c c' g d))),
     (S .transpose, (S .transpose_iso, (S .natural_right, c c' d g ↦ S .natural_left c c' g d))))

{` rem:adj-in-posets. `}
def bridge_rem_adj_in_posets : blind_rem_adj_in_posets
  ≔ P Q F G ↦
    (A ↦ preorder_adjunction_iff (bridge_pre P) (bridge_pre Q) (bridge_f (P .fst .fst) (Q .fst .fst) F)
           (bridge_radj (P .fst .fst) (Q .fst .fst) F (G, A)),
     h ↦ bridge_radj_inv (P .fst .fst) (Q .fst .fst) F
           (preorder_right_adjoint_from_iff (bridge_pre P) (bridge_pre Q) (bridge_f (P .fst .fst) (Q .fst .fst) F)
              (bridge_f (Q .fst .fst) (P .fst .fst) G) h) .snd)

def bridge_def_frac_le (x y : BlindFrac) : Id Type (blind_frac_le x y) (FracLe x y) ≔ refl (blind_frac_le x y)

def bridge_rem_adj_floor_ceil : blind_rem_adj_floor_ceil
  ≔ (frac_ceiling, (frac_floor, (frac_ceiling_iff, frac_floor_iff)))

def bridge_rem_adj_subsets : blind_rem_adj_subsets
  ≔ A B f ↦ (subtype_exists_preimage_iff A B f, (Q P ↦ subtype_preimage_forall_iff A B f Q P))
