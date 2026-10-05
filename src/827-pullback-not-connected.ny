export "826-circle-pullback-components"
export "109-connected-map-sections"

{` Chapter 8 (congp.tex), litmus checks of ex:pullbackandgcd (line 355)
   and the remark at line 497: "the pullback is an example of when a
   construction of types not preserving connectivity can be used
   profitably also for groups". Two concrete instances of a pullback of
   connected types (circles and a point) that is not connected. `}

{` A type with at least two components is not connected. `}
def pbg_two_components_not_connected (X : Type) (n : Nat) (e : Equiv (SetTrunc X) (Fin (suc. (suc. n))))
  (h : Connected X) : Empty
  ≔ let F ≔ Fin (suc. (suc. n)) in
    let i0 : F ≔ inr. star. in
    let i1 : F ≔ inl. (inr. star.) in
    let g : X → F ≔ x ↦ e .map (set_trunc X x) in
    let wc ≔ connected_set_map_constant X F h (fin_set (suc. (suc. n))) g in
    let c0 ≔ equiv_inverse_map (SetTrunc X) F e i0 in
    let c1 ≔ equiv_inverse_map (SetTrunc X) F e i1 in
    mere_rec (BookFiber X (SetTrunc X) (set_trunc X) c0) Empty empty_prop
      (u ↦ mere_rec (BookFiber X (SetTrunc X) (set_trunc X) c1) Empty empty_prop
        (v ↦ inl_ne_inr (Fin (suc. n)) (inr. star.) (calc
          i0 = e .map c0 by inverse F (e .map c0) i0 (equiv_counit (SetTrunc X) F e i0)
          = g (u .fst) by refl (e .map) (u .snd)
          = g (v .fst) by wc (u .fst) (v .fst)
          = e .map c1 by refl (e .map) (inverse (SetTrunc X) c1 (set_trunc X (v .fst)) (v .snd))
          = i1 by equiv_counit (SetTrunc X) F e i1 ∎))
        (set_trunc_surjective X c1))
      (set_trunc_surjective X c0)

{` Litmus for ex:pullbackandgcd: a = 6, b = 9 (fig:circle-pullback) gives
   gcd = 3 components; a = b = 1 gives 1; a = b = 2 gives 2. The types
   are checked by computing nat_gcd. `}
def circle_power_pullback_six_nine (C : CircleSignature)
  : Equiv (SetTrunc (CirclePowerPullback C (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.)))))))))))
      (Fin (suc. (suc. (suc. zero.))))
  ≔ circle_power_pullback_components_fin C (suc. (suc. (suc. (suc. (suc. zero.))))) (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))

def circle_power_pullback_one_one (C : CircleSignature)
  : Equiv (SetTrunc (CirclePowerPullback C (suc. zero.) (suc. zero.))) (Fin (suc. zero.))
  ≔ circle_power_pullback_components_fin C zero. zero.

def circle_power_pullback_two_two (C : CircleSignature)
  : Equiv (SetTrunc (CirclePowerPullback C (suc. (suc. zero.)) (suc. (suc. zero.)))) (Fin (suc. (suc. zero.)))
  ≔ circle_power_pullback_components_fin C (suc. zero.) (suc. zero.)

{` Remark (line 497), first instance: the pullback of the squaring map
   S¹ → S¹ along itself is a pullback of connected types with two
   components, hence not connected. `}
def circle_power_pullback_not_connected (C : CircleSignature)
  (h : Connected (CirclePowerPullback C (suc. (suc. zero.)) (suc. (suc. zero.)))) : Empty
  ≔ pbg_two_components_not_connected (CirclePowerPullback C (suc. (suc. zero.)) (suc. (suc. zero.))) zero.
      (circle_power_pullback_two_two C) h

{` Second instance: the pullback of base : 1 → S¹ along itself is
   1 ×_{S¹} 1 = (base = base) ≃ ℤ; it is not connected (the windings of
   refl and loop differ). `}
def CirclePointPullback (C : CircleSignature) : Type
  ≔ TypePullback Unit Unit (C .carrier) (_ ↦ C .base) (_ ↦ C .base)

def circle_point_pullback_not_connected (C : CircleSignature) (h : Connected (CirclePointPullback C)) : Empty
  ≔ let w : CirclePointPullback C → Int ≔ t ↦ circle_winding C (t .snd) in
    let wc ≔ connected_set_map_constant (CirclePointPullback C) Int h int_set w in
    pbg_one_not_zero (calc
      (pos. (suc. zero.) : Int) = circle_winding C (loop_power (C .carrier) (C .base) (C .loop) (pos. (suc. zero.)))
        by inverse Int (circle_winding C (loop_power (C .carrier) (C .base) (C .loop) (pos. (suc. zero.)))) (pos. (suc. zero.))
          (circle_winding_power C (pos. (suc. zero.)))
      = w ((star., star.), C .loop) by refl (circle_winding C) (concat_1p (C .carrier) (C .base) (C .base) (C .loop))
      = w ((star., star.), refl (C .base)) by wc ((star., star.), C .loop) ((star., star.), refl (C .base))
      = pos. zero. by circle_winding_power C (pos. zero.) ∎)
