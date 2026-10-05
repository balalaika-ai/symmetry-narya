{` Bridges for chapter 5, blind file 01-gsets, part 2: ex:S2-acts-on-C3, xca:AutC3, xca:not-normal and
   xca:lagrange-if-subgr-not-normal (whose blind statement is in 02-subgroups). `}
export "02-subgroups"
import "../../../src/562-gset-transitivity-finiteness"
import "../../../src/568-s2-acts-on-c3"
import "../../../src/572-s2-c3-identification"
import "../../../src/574-s2-aut-c3"
import "../../../src/566-wedge-circle-gsets"

def bridge_bool_code : Bool → Type ≔ [ true. ↦ Unit | false. ↦ Empty ]

def bridge_true_ne_false (p : Id Bool true. false.) : Empty ≔ transport Bool bridge_bool_code true. false. p star.

{` ex:S2-acts-on-C3. The blind swap(s) (enumeration of S sending false to s, evaluated at true) differs from s,
   hence is our two_set_swap s. `}
def bridge_s2_swap_ne (S : TwoElementSets) (s : two_set_carrier S)
  : Not (Id (two_set_carrier S) (blind_s2_swap S s) s)
  ≔ p ↦
    let A ≔ two_set_carrier S in
    let E ≔ two_pointed_enumeration A (blind_s2_two_element S) s in
    bridge_true_ne_false
      (equivalence_injective Bool A E true. false.
        (concat A (E .map true.) s (E .map false.) p
          (inverse A (E .map false.) s (two_pointed_enumeration_beta A (blind_s2_two_element S) s))))

def bridge_s2_swap (S : TwoElementSets) (s : two_set_carrier S)
  : Id (two_set_carrier S) (blind_s2_swap S s) (two_set_swap S s)
  ≔ two_set_other_is_swap S s (blind_s2_swap S s) (bridge_s2_swap_ne S s)

def bridge_s2c3_case (S : TwoElementSets) (s t : two_set_carrier S)
  (d d' : Decidable (Id (two_set_carrier S) t s))
  : Id (Sum (Fin (suc. zero.)) (two_set_carrier S)) (blind_s2c3_case S s t d) (s2c3_branch S s t d')
  ≔ match d, d' [
  | inl. _, inl. _ ↦ refl ((u ↦ inr. u) : two_set_carrier S → Sum (Fin (suc. zero.)) (two_set_carrier S)) (bridge_s2_swap S s)
  | inl. p, inr. n ↦ absurd (Id (Sum (Fin (suc. zero.)) (two_set_carrier S)) (inr. (blind_s2_swap S s)) (inl. (inr. star.))) (n p)
  | inr. n, inl. p ↦ absurd (Id (Sum (Fin (suc. zero.)) (two_set_carrier S)) (inl. (inr. star.)) (inr. (two_set_swap S s))) (n p)
  | inr. _, inr. _ ↦ refl (inl. (inr. star.) : Sum (Fin (suc. zero.)) (two_set_carrier S)) ]

def bridge_s2c3_fun_at (S : TwoElementSets) (s : two_set_carrier S) (x : Sum (Fin (suc. zero.)) (two_set_carrier S))
  : Id (Sum (Fin (suc. zero.)) (two_set_carrier S)) (blind_s2c3_fun S s x) (s2c3_move S s x)
  ≔ match x [
  | inl. _ ↦ refl (inr. s : Sum (Fin (suc. zero.)) (two_set_carrier S))
  | inr. t ↦ bridge_s2c3_case S s t (blind_s2_dec S t s) (two_set_decidable S t s) ]

{` The blind f equals our f, so the blind point of T_S is ours. `}
def bridge_def_s2c3_fun (S : TwoElementSets)
  : Id (two_set_carrier S → S2C3Plus S → S2C3Plus S) (blind_s2c3_fun S) (s2c3_move S)
  ≔ funext (two_set_carrier S) (_ ↦ S2C3Plus S → S2C3Plus S) (blind_s2c3_fun S) (s2c3_move S)
      (s ↦ funext (S2C3Plus S) (_ ↦ S2C3Plus S) (blind_s2c3_fun S s) (s2c3_move S s) (bridge_s2c3_fun_at S s))

def bridge_def_s2c3_point (S : TwoElementSets) : Id (S2C3Type S) (blind_s2c3_point S) (s2c3_point S)
  ≔ refl ((f ↦ (s2c3_one_plus S, f)) : (two_set_carrier S → S2C3Plus S → S2C3Plus S) → S2C3Type S) (bridge_def_s2c3_fun S)

def bridge_def_s2c3_type (S : TwoElementSets) : Id Type (BlindS2C3Type S) (S2C3Type S) ≔ refl (S2C3Type S)

{` The blind action G(S) is ours. `}
def bridge_def_s2_acts_on_c3 (S : TwoElementSets) : Id Group (blind_s2_acts_on_c3 S) (s2c3_group S)
  ≔ let T ≔ S2C3Type S in
    concat Group (automorphism_group T (blind_s2c3_type_groupoid S) (blind_s2c3_point S))
      (automorphism_group T (s2c3_type_groupoid S) (blind_s2c3_point S))
      (automorphism_group T (s2c3_type_groupoid S) (s2c3_point S))
      (refl ((h ↦ automorphism_group T h (blind_s2c3_point S)) : isGroupoid T → Group)
        (isgroupoid_isprop T (blind_s2c3_type_groupoid S) (s2c3_type_groupoid S)))
      (refl ((a ↦ automorphism_group T (s2c3_type_groupoid S) a) : T → Group) (bridge_def_s2c3_point S))

{` The shape bool of the blind statement is the standard shape Fin 2, along fin_two_equiv. `}
def bridge_bool_shape_path : Id TwoElementSets blind_bool_s2_shape s2c3_std
  ≔ component_path SetTypes (standard_set two) blind_bool_s2_shape s2c3_std
      (inverse SetTypes (standard_set two) (Bool, bool_set) (set_types_path (standard_set two) (Bool, bool_set) fin_two_equiv))

def bridge_s2_acts_on_c3_bool : blind_s2_acts_on_c3_bool
  ≔ concat Group (blind_s2_acts_on_c3 blind_bool_s2_shape) (s2c3_group blind_bool_s2_shape) (cyclic_group_fin two)
      (bridge_def_s2_acts_on_c3 blind_bool_s2_shape)
      (concat Group (s2c3_group blind_bool_s2_shape) (s2c3_group s2c3_std) (cyclic_group_fin two)
        (refl s2c3_group bridge_bool_shape_path) s2c3_group_c3_path)

{` xca:AutC3. For every pointing p, the blind classifying map agrees with ours on underlying maps (the second
   components are propositions), and ours is an equivalence. `}
def bridge_AutC3 : blind_AutC3
  ≔ p ↦ book_isequiv_homotopic TwoElementSets (NativeComponent Group (cyclic_group_fin two))
      s2_aut_c3_map (blind_autc3_classifying p .fst)
      (z ↦ component_path Group (cyclic_group_fin two) (s2_aut_c3_map z) (blind_autc3_classifying p .fst z)
             (inverse Group (blind_s2_acts_on_c3 z) (s2c3_group z) (bridge_def_s2_acts_on_c3 z)))
      s2_aut_c3_map_equiv

{` xca:not-normal. The blind figure-eight signature is our CircleWedgeSignature (same fields). `}
def bridge_def_wedge (W : FigureEightSignature) : CircleWedgeSignature
  ≔ (carrier ≔ W .carrier, base ≔ W .base, loop1 ≔ W .loop1, loop2 ≔ W .loop2, induction ≔ W .induction)

def bridge_cycle_at (x : Fin three) : Id (Fin three) (wedge_cycle_equiv .map x) (finite_fin_successor two .map x)
  ≔ match x [
  | inr. star. ↦ refl (inl. (inr. star.) : Fin three)
  | inl. (inr. star.) ↦ refl (inl. (inl. (inr. star.)) : Fin three)
  | inl. (inl. (inr. star.)) ↦ refl (inr. star. : Fin three)
  | inl. (inl. (inl. e)) ↦ match e [] ]

def bridge_cycle_equiv : Id (Equiv (Fin three) (Fin three)) wedge_cycle_equiv (finite_fin_successor two)
  ≔ equiv_path (Fin three) (Fin three) wedge_cycle_equiv (finite_fin_successor two)
      (funext (Fin three) (_ ↦ Fin three) (wedge_cycle_equiv .map) (finite_fin_successor two .map) bridge_cycle_at)

def BridgeWedgeData : Type ≔ Σ SetTypes (b ↦ Product (Id SetTypes b b) (Id SetTypes b b))

def bridge_wedge_data_of (e : Equiv (Fin three) (Fin three)) : BridgeWedgeData
  ≔ (standard_set three,
     (set_types_path (standard_set three) (standard_set three) e,
      set_types_path (standard_set three) (standard_set three) fin3_swap01_equiv))

{` The blind G-set of fig:not-normal is ours, transported along the identification of the recursion data. `}
def bridge_def_not_normal_gset (W : FigureEightSignature) (hW : isGroupoid (W .carrier))
  : Id (GSet (circle_wedge_group (bridge_def_wedge W) hW)) (wedge_gset (bridge_def_wedge W) hW) (blind_not_normal_gset W hW)
  ≔ refl ((d ↦ W .induction (_ ↦ SetTypes) d .fst) : BridgeWedgeData → W .carrier → SetTypes)
      (refl bridge_wedge_data_of bridge_cycle_equiv)

def bridge_not_normal_transitive : blind_not_normal_transitive
  ≔ W hW ↦
    let G ≔ circle_wedge_group (bridge_def_wedge W) hW in
    transport (GSet G) (X ↦ IsTransitive G X) (wedge_gset (bridge_def_wedge W) hW) (blind_not_normal_gset W hW)
      (bridge_def_not_normal_gset W hW) (wedge_gset_transitive (bridge_def_wedge W) hW)

def bridge_not_normal_aut_contractible : blind_not_normal_aut_contractible
  ≔ W hW ↦
    let G ≔ circle_wedge_group (bridge_def_wedge W) hW in
    transport (GSet G) (X ↦ BookIsContr (Id (GSet G) X X)) (wedge_gset (bridge_def_wedge W) hW) (blind_not_normal_gset W hW)
      (bridge_def_not_normal_gset W hW) (wedge_gset_symmetries_contractible (bridge_def_wedge W) hW)

def BridgeNotNormalEv (G : Group) (X : GSet G) : Type
  ≔ (x : X (shape G) .fst)
    → Product (IsEmbedding (Id (GSet G) X X) (X (shape G) .fst) (gset_path_eval G X X (shape G) x))
        (Not (Surjective (Id (GSet G) X X) (X (shape G) .fst) (gset_path_eval G X X (shape G) x)))

def bridge_not_normal_ev : blind_not_normal_ev
  ≔ W hW ↦
    let V ≔ bridge_def_wedge W in
    let G ≔ circle_wedge_group V hW in
    transport (GSet G) (BridgeNotNormalEv G) (wedge_gset V hW) (blind_not_normal_gset W hW)
      (bridge_def_not_normal_gset W hW)
      (x ↦ (wedge_eval_injective V hW x, h ↦ wedge_eval_not_surjective V hW x h))

{` xca:lagrange-if-subgr-not-normal. A choice map towards one point gives one towards any other point. `}
def BridgeChoice (G : Group) (X : GSet G) (p : gset_underlying G X) : Type
  ≔ (x : gset_underlying G X) → Σ (USym G) (g ↦ Id (gset_underlying G X) (gset_usym_act G X g x) p)

def bridge_choice_repoint (G : Group) (X : GSet G) (p q : gset_underlying G X) (c : BridgeChoice G X p)
  : BridgeChoice G X q
  ≔ x ↦
    let S ≔ gset_underlying G X in
    let k ≔ c q in
    let ki ≔ usym_inv G (k .fst) in
    (usym_mul G ki (c x .fst),
     concat S (gset_usym_act G X (usym_mul G ki (c x .fst)) x) (gset_usym_act G X ki (gset_usym_act G X (c x .fst) x)) q
       (gset_act_mul G X ki (c x .fst) x)
       (concat S (gset_usym_act G X ki (gset_usym_act G X (c x .fst) x)) (gset_usym_act G X ki (gset_usym_act G X (k .fst) q)) q
          (refl (gset_usym_act G X ki)
             (concat S (gset_usym_act G X (c x .fst) x) p (gset_usym_act G X (k .fst) q) (c x .snd)
                (inverse S (gset_usym_act G X (k .fst) q) p (k .snd))))
          (gset_act_inv_left G X (k .fst) q)))

def bridge_lagrange_if_subgr_not_normal : blind_lagrange_if_subgr_not_normal
  ≔ W hW ↦
    let V ≔ bridge_def_wedge W in
    let G ≔ circle_wedge_group V hW in
    let moved ≔ transport (GSet G) (X ↦ Σ (gset_underlying G X) (p ↦ BridgeChoice G X p)) (wedge_gset V hW)
        (blind_not_normal_gset W hW) (bridge_def_not_normal_gset W hW)
        (wedge_gset_point V fin3_zero, wedge_choice_map V hW) in
    bridge_choice_repoint G (blind_not_normal_gset W hW) (moved .fst) (blind_not_normal_zero W hW) (moved .snd)
