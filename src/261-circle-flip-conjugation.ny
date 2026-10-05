export "260-root-degree-comparison"

{` The inverse cycle (X, t⁻¹). `}
def cycle_inverse (c : Cycles) : Cycles
  ≔ (((c .fst .fst .fst, c .fst .fst .snd), canonical_inverse_equiv (c .fst .fst .fst) (c .fst .fst .fst) (c .fst .snd)),
      inverse_cyclic (c .fst .fst .fst) (c .fst .snd) (c .snd))

def int_succ_neg_succ (x : Int) : Id Int (int_succ (int_neg (int_succ x))) (int_neg x)
  ≔ match x [
  | pos. zero. ↦ refl (pos. zero. : Int)
  | pos. (suc. n) ↦ refl (neg. n : Int)
  | neg. zero. ↦ refl (pos. (suc. zero.) : Int)
  | neg. (suc. n) ↦ refl (pos. (suc. (suc. n)) : Int) ]

{` Negation identifies (Z, s) with (Z, s⁻¹), for any cycle structure on (Z, s). `}
def negation_iso (S : EndomorphismCycleStructure integer_endomorphism)
  : PermutationIsomorphisms (infinite_cycle .fst) (cycle_inverse (cycle_endomorphism_unpack (integer_endomorphism, S)) .fst)
  ≔ let E ≔ cycle_endomorphism_unpack (integer_endomorphism, S) .fst .snd in
    (int_neg_equiv, x ↦ inverse Int (equiv_inverse_map Int Int E (int_neg x)) (int_neg (int_succ x))
      (inverse_at_known_point Int Int E (int_neg (int_succ x)) (int_neg x) (int_succ_neg_succ x)))

def negation_cycle_path (S : EndomorphismCycleStructure integer_endomorphism)
  : Id Cycles infinite_cycle (cycle_inverse (cycle_endomorphism_unpack (integer_endomorphism, S)))
  ≔ equiv_inverse_map (Id Cycles infinite_cycle (cycle_inverse (cycle_endomorphism_unpack (integer_endomorphism, S))))
      (PermutationIsomorphisms (infinite_cycle .fst) (cycle_inverse (cycle_endomorphism_unpack (integer_endomorphism, S)) .fst))
      (cycle_paths_equiv infinite_cycle (cycle_inverse (cycle_endomorphism_unpack (integer_endomorphism, S))))
      (negation_iso S)

def negation_cycle_evaluation (S : EndomorphismCycleStructure integer_endomorphism) (x : Int)
  : Id Int (cycle_path_evaluate infinite_cycle (cycle_inverse (cycle_endomorphism_unpack (integer_endomorphism, S)))
      (negation_cycle_path S) x) (int_neg x)
  ≔ let d ≔ cycle_inverse (cycle_endomorphism_unpack (integer_endomorphism, S)) in
    inverse_evaluation_agreement (Id Cycles infinite_cycle d) (PermutationIsomorphisms (infinite_cycle .fst) (d .fst)) Int
      (cycle_paths_equiv infinite_cycle d) (p ↦ cycle_path_evaluate infinite_cycle d p x) (h ↦ h .fst .map x)
      (p ↦ refl (cycle_path_evaluate infinite_cycle d p x)) (negation_iso S)

def infinite_inverse_component (t : InfiniteCycles)
  : Mere (Id Endomorphisms integer_endomorphism (cycle_endomorphism (cycle_inverse (infinite_endomorphism_cycle t))))
  ≔ let target ≔ cycle_endomorphism (cycle_inverse (infinite_endomorphism_cycle t)) in
    let base ≔ cycle_endomorphism (cycle_inverse infinite_cycle) in
    trunc_map native_truncation (Id Cycles infinite_cycle (infinite_endomorphism_cycle t))
      (Id Endomorphisms integer_endomorphism target)
      (p ↦ concat Endomorphisms integer_endomorphism base target
        (refl cycle_endomorphism (negation_cycle_path (cycle_endomorphism_structure infinite_cycle)))
        (refl ((c ↦ cycle_endomorphism (cycle_inverse c)) : Cycles → Endomorphisms) p))
      (infinite_endomorphism_cycle_component t)

{` The operation (X, t) ↦ (X, t⁻¹) on infinite cycles in the endomorphism
   component; t is an equivalence there by the component structure. `}
def infinite_inverse (t : InfiniteCycles) : InfiniteCycles
  ≔ (cycle_endomorphism (cycle_inverse (infinite_endomorphism_cycle t)), infinite_inverse_component t)

def infinite_inverse_literal (t : InfiniteCycles)
  : Id Endomorphisms (infinite_inverse t .fst)
      (t .fst .fst, equiv_inverse_map (t .fst .fst) (t .fst .fst)
        (t .fst .snd, infinite_endomorphism_structure t .snd .fst))
  ≔ refl (infinite_inverse t .fst)

def infinite_negation_pointing : Id InfiniteCycles infinite_endomorphism_point (infinite_inverse infinite_endomorphism_point)
  ≔ subtype_equal Endomorphisms (u ↦ Mere (Id Endomorphisms integer_endomorphism u))
      (u ↦ mere_isprop (Id Endomorphisms integer_endomorphism u))
      infinite_endomorphism_point (infinite_inverse infinite_endomorphism_point)
      (refl cycle_endomorphism (negation_cycle_path (infinite_endomorphism_structure infinite_endomorphism_point)))

def negation_pointing_evaluate (y : Int)
  : Id Int (infinite_path_evaluate infinite_endomorphism_point (infinite_inverse infinite_endomorphism_point)
      infinite_negation_pointing y) (int_neg y)
  ≔ let pt ≔ infinite_endomorphism_point in let target ≔ infinite_inverse pt in
    let S ≔ infinite_endomorphism_structure pt in
    let P ≔ refl cycle_endomorphism (negation_cycle_path S) in
    concat Int (infinite_path_evaluate pt target infinite_negation_pointing y)
      (endomorphism_path_evaluate integer_endomorphism (target .fst) P y) (int_neg y)
      (refl ((Q ↦ endomorphism_path_evaluate integer_endomorphism (target .fst) Q y)
          : Id Endomorphisms integer_endomorphism (target .fst) → Int)
        (equiv_counit (Id InfiniteCycles pt target) (Id Endomorphisms integer_endomorphism (target .fst))
          (subtype_path_equiv Endomorphisms (u ↦ Mere (Id Endomorphisms integer_endomorphism u))
            (u ↦ mere_isprop (Id Endomorphisms integer_endomorphism u)) pt target) P))
      (negation_cycle_evaluation S y)

def negation_pointing_inverse (y : Int)
  : Id Int (infinite_path_evaluate (infinite_inverse infinite_endomorphism_point) infinite_endomorphism_point
      (inverse InfiniteCycles infinite_endomorphism_point (infinite_inverse infinite_endomorphism_point)
        infinite_negation_pointing) y) (int_neg y)
  ≔ let pt ≔ infinite_endomorphism_point in let target ≔ infinite_inverse pt in
    let back ≔ ((u ↦ infinite_path_evaluate target pt (inverse InfiniteCycles pt target infinite_negation_pointing) u)
      : Int → Int) in
    calc
      back y = back (infinite_path_evaluate pt target infinite_negation_pointing (int_neg y))
        by refl back (inverse Int (infinite_path_evaluate pt target infinite_negation_pointing (int_neg y)) y
          (concat Int (infinite_path_evaluate pt target infinite_negation_pointing (int_neg y)) (int_neg (int_neg y)) y
            (negation_pointing_evaluate (int_neg y)) (int_neg_neg y)))
      = int_neg y by infinite_inverse_roundtrip pt target infinite_negation_pointing (int_neg y) ∎

{` Inversion does not change carriers, so it acts trivially on evaluations. `}
def infinite_inverse_ap_evaluate (s t : InfiniteCycles) (q : Id InfiniteCycles s t) (x : s .fst .fst)
  : Id (t .fst .fst) (infinite_path_evaluate (infinite_inverse s) (infinite_inverse t) (refl infinite_inverse q) x)
      (infinite_path_evaluate s t q x)
  ≔ J InfiniteCycles s
      (t q ↦ Id (t .fst .fst) (infinite_path_evaluate (infinite_inverse s) (infinite_inverse t) (refl infinite_inverse q) x)
        (infinite_path_evaluate s t q x))
      (concat (s .fst .fst) (infinite_path_evaluate (infinite_inverse s) (infinite_inverse s) (refl (infinite_inverse s)) x)
        x (infinite_path_evaluate s s (refl s) x)
        (transport_refl Type (X ↦ X) (s .fst .fst) x)
        (inverse (s .fst .fst) (infinite_path_evaluate s s (refl s) x) x (transport_refl Type (X ↦ X) (s .fst .fst) x)))
      t q

def infinite_inverse_pointed : BookPointedMap infinite_pointed infinite_pointed
  ≔ (infinite_inverse, infinite_negation_pointing)

def circle_reflection_pointed_map (C : CircleSignature) : BookPointedMap (circle_pointed C) (circle_pointed C)
  ≔ pointed_circle_loop_rec C (C .carrier) (C .base) (inverse (C .carrier) (C .base) (C .base) (C .loop))

def inverse_after_circle (C : CircleSignature) : BookPointedMap (circle_pointed C) infinite_pointed
  ≔ book_pointed_compose (circle_pointed C) infinite_pointed infinite_pointed (circle_infinite_pointed_map C)
      infinite_inverse_pointed

def circle_after_reflection (C : CircleSignature) : BookPointedMap (circle_pointed C) infinite_pointed
  ≔ book_pointed_compose (circle_pointed C) (circle_pointed C) infinite_pointed (circle_reflection_pointed_map C)
      (circle_infinite_pointed_map C)

def inverse_after_circle_coordinate (C : CircleSignature)
  : Id Int (infinite_cycle_loop_coordinate (pointed_circle_loop_eval C InfiniteCycles infinite_endomorphism_point
      (inverse_after_circle C))) (pos. (suc. zero.))
  ≔ let pt ≔ infinite_endomorphism_point in let target ≔ infinite_inverse pt in
    let c ≔ circle_infinite_pointed_map C in
    let l ≔ pointed_circle_loop_eval C InfiniteCycles pt c in
    let back ≔ ((u ↦ infinite_path_evaluate target pt (inverse InfiniteCycles pt target infinite_negation_pointing) u)
      : Int → Int) in
    let mid ≔ ((u ↦ infinite_path_evaluate target target (refl infinite_inverse l) u) : Int → Int) in
    calc
      infinite_cycle_loop_coordinate (pointed_circle_loop_eval C InfiniteCycles pt (inverse_after_circle C))
      = infinite_cycle_loop_coordinate (pointed_loop_conjugate InfiniteCycles pt target infinite_negation_pointing
          (refl infinite_inverse l))
        by refl infinite_cycle_loop_coordinate
          (pointed_conjugate_compose InfiniteCycles InfiniteCycles pt pt infinite_inverse infinite_negation_pointing
            (c .fst (C .base)) (c .snd) (refl (c .fst) (C .loop)))
      = back (mid (infinite_path_evaluate pt target infinite_negation_pointing int_zero))
        by infinite_conjugate_evaluate pt target infinite_negation_pointing (refl infinite_inverse l) int_zero
      = back (mid int_zero) by refl ((u ↦ back (mid u)) : Int → Int) (negation_pointing_evaluate int_zero)
      = back (infinite_cycle_loop_coordinate l) by refl back (infinite_inverse_ap_evaluate pt pt l int_zero)
      = back (infinite_cycle_loop_coordinate infinite_predecessor_loop)
        by refl ((q ↦ back (infinite_cycle_loop_coordinate q)) : Id InfiniteCycles pt pt → Int)
          (pointed_circle_loop_rec_beta C InfiniteCycles pt infinite_predecessor_loop)
      = back (neg. zero.) by refl back infinite_predecessor_loop_coordinate
      = int_neg (neg. zero.) by negation_pointing_inverse (neg. zero.)
      = pos. (suc. zero.) by refl (pos. (suc. zero.) : Int) ∎

def circle_after_reflection_coordinate (C : CircleSignature)
  : Id Int (infinite_cycle_loop_coordinate (pointed_circle_loop_eval C InfiniteCycles infinite_endomorphism_point
      (circle_after_reflection C))) (pos. (suc. zero.))
  ≔ let pt ≔ infinite_endomorphism_point in
    let c ≔ circle_infinite_pointed_map C in
    let r ≔ circle_reflection_pointed_map C in
    let il ≔ inverse (C .carrier) (C .base) (C .base) (C .loop) in
    calc
      infinite_cycle_loop_coordinate (pointed_circle_loop_eval C InfiniteCycles pt (circle_after_reflection C))
      = infinite_cycle_loop_coordinate (pointed_loop_conjugate InfiniteCycles pt (c .fst (C .base)) (c .snd)
          (refl (c .fst) (pointed_circle_loop_eval C (C .carrier) (C .base) r)))
        by refl infinite_cycle_loop_coordinate
          (pointed_conjugate_compose InfiniteCycles (C .carrier) pt (C .base) (c .fst) (c .snd)
            (r .fst (C .base)) (r .snd) (refl (r .fst) (C .loop)))
      = infinite_cycle_loop_coordinate (pointed_loop_conjugate InfiniteCycles pt (c .fst (C .base)) (c .snd)
          (refl (c .fst) il))
        by refl ((l ↦ infinite_cycle_loop_coordinate (pointed_loop_conjugate InfiniteCycles pt (c .fst (C .base))
            (c .snd) (refl (c .fst) l))) : Id (C .carrier) (C .base) (C .base) → Int)
          (pointed_circle_loop_rec_beta C (C .carrier) (C .base) il)
      = infinite_cycle_loop_coordinate (circle_infinite_cycle_based_action C il)
        by refl infinite_cycle_loop_coordinate
          (conjugate_inverse_transport InfiniteCycles pt (c .fst (C .base))
            (circle_rec_beta C InfiniteCycles (pt, infinite_predecessor_loop) .fst) (refl (c .fst) il))
      = int_neg (circle_winding C il) by circle_infinite_cycle_action_coordinate C il
      = int_neg (neg. zero.) by refl int_neg (circle_winding_inverse_loop C)
      = pos. (suc. zero.) by refl (pos. (suc. zero.) : Int) ∎

{` Footnote of rem:flipthecircle, pointed form: inv ∘ c = c ∘ r as pointed
   maps S¹ →* InfCyc, where inv(X,t) = (X,t⁻¹) is pointed by negation. `}
def circle_flip_pointed (C : CircleSignature)
  : Id (BookPointedMap (circle_pointed C) infinite_pointed) (inverse_after_circle C) (circle_after_reflection C)
  ≔ let pt ≔ infinite_endomorphism_point in
    equivalence_injective (BookPointedMap (circle_pointed C) infinite_pointed) (Id InfiniteCycles pt pt)
      (pointed_circle_universal_property C InfiniteCycles pt) (inverse_after_circle C) (circle_after_reflection C)
      (equivalence_injective (Id InfiniteCycles pt pt) Int infinite_cycle_loop_coordinate_equiv
        (pointed_circle_loop_eval C InfiniteCycles pt (inverse_after_circle C))
        (pointed_circle_loop_eval C InfiniteCycles pt (circle_after_reflection C))
        (concat Int (infinite_cycle_loop_coordinate (pointed_circle_loop_eval C InfiniteCycles pt (inverse_after_circle C)))
          (pos. (suc. zero.))
          (infinite_cycle_loop_coordinate (pointed_circle_loop_eval C InfiniteCycles pt (circle_after_reflection C)))
          (inverse_after_circle_coordinate C)
          (inverse Int (infinite_cycle_loop_coordinate (pointed_circle_loop_eval C InfiniteCycles pt (circle_after_reflection C)))
            (pos. (suc. zero.)) (circle_after_reflection_coordinate C))))

def circle_flip_maps (C : CircleSignature)
  : Id (C .carrier → InfiniteCycles) (x ↦ infinite_inverse (circle_infinite_cycle_map C x))
      (x ↦ circle_infinite_cycle_map C (circle_reflection C x))
  ≔ refl ((u ↦ u .fst) : BookPointedMap (circle_pointed C) infinite_pointed → (C .carrier → InfiniteCycles))
      (circle_flip_pointed C)

{` The footnote itself: c r c⁻¹ : InfCyc → InfCyc maps (X,t) to (X,t⁻¹). `}
def circle_flip_conjugation (C : CircleSignature)
  : Id (InfiniteCycles → InfiniteCycles)
      (y ↦ circle_infinite_cycle_map C (circle_reflection C
        (equiv_inverse_map (C .carrier) InfiniteCycles
          (native_equivalence (C .carrier) InfiniteCycles (circle_infinite_cycles_equiv C)) y)))
      infinite_inverse
  ≔ let e ≔ native_equivalence (C .carrier) InfiniteCycles (circle_infinite_cycles_equiv C) in
    let g ≔ equiv_inverse_map (C .carrier) InfiniteCycles e in
    funext InfiniteCycles (_ ↦ InfiniteCycles)
      (y ↦ circle_infinite_cycle_map C (circle_reflection C (g y))) infinite_inverse
      (y ↦ calc
        circle_infinite_cycle_map C (circle_reflection C (g y))
        = infinite_inverse (circle_infinite_cycle_map C (g y))
          by inverse InfiniteCycles (infinite_inverse (circle_infinite_cycle_map C (g y)))
            (circle_infinite_cycle_map C (circle_reflection C (g y))) (circle_flip_maps C (refl (g y)))
        = infinite_inverse y by refl infinite_inverse (equiv_counit (C .carrier) InfiniteCycles e y) ∎)
