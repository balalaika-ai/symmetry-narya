export "1031-gset-automorphisms-conjugates"
export "912-weyl-fixed-points"

{` Chapter 10: chapter 10's Weyl group agrees with chapter 9's.

   subgroup_weyl_group G S (module 1031, used in the proof of thm:sylow1) is
   literally chapter 9's weyl_group G S (module 910, def:Weyl): both are
   Aut_{GSet G}(X) for S = (X, x). The two descriptions of its symmetries by
   fixed points also agree: chapter 10's equivalence
   USym W_G S ≃ {y : X(sh_G) | S fixes y} (subgroup_weyl_usym_equiv, for
   finite G and S) sends w to the point y = w(x), which is the value at the
   base point (sh_G, x) of BS of chapter 9's map
   e : USym W_G S → (G/H)^H (weyl_usym_fixed_map, module 912,
   lem:WGHisHfixofG/H corrected; an equivalence for finite G/H). `}

def subgroup_weyl_group_agrees (G : Group) (S : Subgroups G) : Id Group (subgroup_weyl_group G S) (weyl_group G S)
  ≔ refl (weyl_group G S)

{` The first component of a pair (y, (X, x) = (X, y)) is the evaluation at x
   of the corresponding automorphism. `}
def gset_aut_pointed_sum_eval (G : Group) (X : GSet G) (x : gset_underlying G X)
  (u : Σ (gset_underlying G X) (y ↦ Id (PointedGSet G) (X, x) (X, y)))
  : Id (gset_underlying G X) (u .fst) (gset_path_eval G X X (shape G) x (gset_aut_pointed_sum_equiv G X x .map u))
  ≔ let A ≔ Id (GSet G) X X in
    let Y ≔ gset_underlying G X in
    let ev ≔ gset_path_eval G X X (shape G) x in
    compose_equiv (Id (PointedGSet G) (X, x) (X, u .fst)) (Fiber A Y ev (u .fst)) (BookFiber A Y ev (u .fst))
      (pointed_gset_path_fiber_equiv G (X, x) (X, u .fst)) (fiber_conventions_equiv A Y ev (u .fst)) .map (u .snd) .snd

def gset_aut_pointed_sum_inverse_eval (G : Group) (X : GSet G) (x : gset_underlying G X) (f : Id (GSet G) X X)
  : Id (gset_underlying G X)
      (equiv_inverse_map (Σ (gset_underlying G X) (y ↦ Id (PointedGSet G) (X, x) (X, y))) (Id (GSet G) X X)
        (gset_aut_pointed_sum_equiv G X x) f .fst)
      (gset_path_eval G X X (shape G) x f)
  ≔ let U ≔ Σ (gset_underlying G X) (y ↦ Id (PointedGSet G) (X, x) (X, y)) in
    let e ≔ gset_aut_pointed_sum_equiv G X x in
    let ev ≔ gset_path_eval G X X (shape G) x in
    concat (gset_underlying G X) (equiv_inverse_map U (Id (GSet G) X X) e f .fst)
      (ev (e .map (equiv_inverse_map U (Id (GSet G) X X) e f))) (ev f)
      (gset_aut_pointed_sum_eval G X x (equiv_inverse_map U (Id (GSet G) X X) e f))
      (map_path (Id (GSet G) X X) (gset_underlying G X) ev (e .map (equiv_inverse_map U (Id (GSet G) X X) e f)) f
        (equiv_counit U (Id (GSet G) X X) e f))

{` Chapter 10's fixed point of w is chapter 9's e(w) at the base point. `}
def subgroup_weyl_fixed_points_agree (G : Group) (hG : IsFiniteGroup G) (S : Subgroups G)
  (hS : IsFiniteGroup (subgroup_group G S)) (w : USym (weyl_group G S))
  : Id (gset_underlying G (S .gset)) (subgroup_weyl_usym_equiv G hG S hS .map w .fst)
      (weyl_usym_fixed_map G S w (shape (subgroup_group G S)))
  ≔ gset_aut_pointed_sum_inverse_eval G (S .gset) (S .point) (w .fst)
