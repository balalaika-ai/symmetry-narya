export "1334-swap-pointed-domains"
export "1207-abelian-hom-group"

{` Chapter 13 (fields.tex 257-279, 782-850): the variant ptw_* of
   rem:loops-at-ptd-cst, the pointed map O' of def:O', and
   con:ptw-swap-ptd-doms. `}

{` rem:loops-at-ptd-cst: the variant ptw_* : Ω(X →* Y) ≃ (X →* ΩY) is
   constant_loops_pointed_equiv (module 1207): ptw_* of con:identity-ptd-maps
   followed by the equivalence replacing h(pt)·refl = refl (concatenation
   order: refl, then h(pt)) by refl = h(pt) (unit law and symmetry). Its
   underlying function sends r to x ↦ ptw(r₁)(x), judgmentally. `}
def loops_at_constant_ptw_function (X Y : Pointed)
  (r : Id (BookPointedMap X Y) (book_pointed_constant X Y) (book_pointed_constant X Y))
  : Id (X .carrier → Loop Y) (constant_loops_pointed_equiv X Y .map r .fst)
      (happly (X .carrier) (_ ↦ Y .carrier) (book_pointed_constant X Y .fst) (book_pointed_constant X Y .fst) (r .fst))
  ≔ refl (happly (X .carrier) (_ ↦ Y .carrier) (book_pointed_constant X Y .fst) (book_pointed_constant X Y .fst) (r .fst))

{` def:O'. As printed, O'_{A,B} ≔ (O_{A,B} ∘ swap⁻¹ ∘ -) does not
   typecheck against the printed type (A →* B) →* ((S¹ →* A) →* (S¹ →* B)):
   O_{A,B} already has domain A →* B. Formalized: the evident pointed map of
   the printed type, O_{A,B} pointed by O(cst) = cst (in fig:bjørn it is used
   at (A, B) = (X, O Y)). `}
def o_functor_pointed_point (C : CircleSignature) (A B : Pointed)
  : Id (BookPointedMap (circle_pointed_maps C A) (circle_pointed_maps C B))
      (book_pointed_constant (circle_pointed_maps C A) (circle_pointed_maps C B))
      (o_functor_map C A B (book_pointed_constant A B))
  ≔ let S ≔ circle_pointed C in let Y ≔ B .carrier in let b ≔ B .point in
    let OA ≔ circle_pointed_maps C A in let OB ≔ circle_pointed_maps C B in
    let M ≔ BookPointedMap S B in
    let cst ≔ book_pointed_constant S B in
    let rbb ≔ concat Y b b b (refl b) (refl b) in
    let F ≔ pointed_constant_at S B in
    let k0 ≔ (refl (constant (C .carrier) Y b), inverse (Id Y b b) rbb (refl b) (concat_p1 Y b b (refl b)))
      : Id M cst (F (b, rbb)) in
    let kpt : Id (Id M cst (F (b, rbb))) (concat M cst cst (F (b, rbb)) (refl cst) k0) (o_functor_map C A B (book_pointed_constant A B) .snd)
      ≔ concat (Id M cst (F (b, rbb))) (concat M cst cst (F (b, rbb)) (refl cst) k0) k0
          (o_functor_map C A B (book_pointed_constant A B) .snd)
          (concat_1p M cst (F (b, rbb)) k0)
          (refl ((s ↦ (refl (constant (C .carrier) Y b), s)) : Id (Id Y b b) (refl b) rbb → Id M cst (F (b, rbb)))
            (inverse (Id (Id Y b b) (refl b) rbb) (o_point_pathover Y b b (refl b))
              (inverse (Id Y b b) rbb (refl b) (concat_p1 Y b b (refl b))) (o_point_pathover_refl Y b))) in
    equiv_inverse_map
      (Id (BookPointedMap OA OB) (book_pointed_constant OA OB) (o_functor_map C A B (book_pointed_constant A B)))
      (PointedHomotopy OA OB (book_pointed_constant OA OB) (o_functor_map C A B (book_pointed_constant A B)))
      (pointed_map_path_equiv OA OB (book_pointed_constant OA OB) (o_functor_map C A B (book_pointed_constant A B)))
      ((_ ↦ k0), kpt)

def o_functor_pointed (C : CircleSignature) (A B : Pointed)
  : BookPointedMap (pointed_maps_pointed A B) (pointed_maps_pointed (circle_pointed_maps C A) (circle_pointed_maps C B))
  ≔ (o_functor_map C A B, o_functor_pointed_point C A B)

{` con:ptw-swap-ptd-doms: ev ∘ swap(f) = ptw_*(ev(f)) in X →* Ω Y for
   f : S¹ →* (X →* Y), where ev ∘ - is postcomposition with the pointed
   ev_Y, swap = swap_pointed_domains (con:swap-ptd-doms), and ptw_* is the
   variant of rem:loops-at-ptd-cst. As in the book, only the underlying
   functions are identified, by cor:Id-(B->*loopsA); pointwise this uses
   ptw(f_pt₁)(x) = ptw_*(f_pt)₁(x) and that ap and evaluation preserve path
   composition (the book's footnotes). `}
def ptw_swap_pointed_domains (C : CircleSignature) (X Y : Pointed)
  (f : BookPointedMap (circle_pointed C) (pointed_maps_pointed X Y))
  : Id (BookPointedMap X (Omega Y))
      (book_pointed_compose X (circle_pointed_maps C Y) (Omega Y)
        (swap_pointed_domains_map (circle_pointed C) X Y f) (pointed_circle_ev_pointed C Y))
      (constant_loops_pointed_equiv X Y .map (pointed_circle_ev C (pointed_maps_pointed X Y) f))
  ≔ let S ≔ circle_pointed C in let Yc ≔ Y .carrier in let y ≔ Y .point in
    let M ≔ BookPointedMap X Y in
    let cst ≔ book_pointed_constant X Y in
    let f0 ≔ f .fst in let fb ≔ f0 (C .base) in let fpt ≔ f .snd in
    let L ≔ refl f0 (C .loop) in
    let lhs ≔ book_pointed_compose X (circle_pointed_maps C Y) (Omega Y) (swap_pointed_domains_map S X Y f)
      (pointed_circle_ev_pointed C Y) in
    let rhs ≔ constant_loops_pointed_equiv X Y .map (pointed_circle_ev C (pointed_maps_pointed X Y) f) in
    loops_pointed_map_path_from_underlying Y X lhs rhs
      (funext (X .carrier) (_ ↦ Loop Y) (lhs .fst) (rhs .fst)
        (x ↦
          let F ≔ (m ↦ m .fst x) : M → Yc in
          let p ≔ refl F fpt in
          let l ≔ refl F L in
          let K ≔ pointed_map_path_equiv X Y cst fb .map fpt in
          calc
            lhs .fst x = pointed_loop_conjugate Yc y (fb .fst x) p l
              by refl ((q ↦ pointed_loop_conjugate Yc y (fb .fst x) q l) : Id Yc y (fb .fst x) → Loop Y)
                (refl ((K' ↦ K' .fst x) : PointedHomotopy X Y cst fb → Id Yc y (fb .fst x))
                  (pointed_map_path_equiv_ptw X Y cst fb fpt))
            = concat Yc y (fb .fst x) y p (concat Yc (fb .fst x) (fb .fst x) y l (refl F (inverse M cst fb fpt)))
              by refl ((q ↦ concat Yc y (fb .fst x) y p (concat Yc (fb .fst x) (fb .fst x) y l q)) : Id Yc (fb .fst x) y → Loop Y)
                (inverse (Id Yc (fb .fst x) y) (refl F (inverse M cst fb fpt)) (inverse Yc y (fb .fst x) p)
                  (map_path_inverse M Yc F cst fb fpt))
            = concat Yc y (fb .fst x) y p (refl F (concat M fb fb cst L (inverse M cst fb fpt)))
              by refl (concat Yc y (fb .fst x) y p)
                (inverse (Id Yc (fb .fst x) y) (refl F (concat M fb fb cst L (inverse M cst fb fpt)))
                  (concat Yc (fb .fst x) (fb .fst x) y l (refl F (inverse M cst fb fpt)))
                  (map_path_concat M Yc F fb fb cst L (inverse M cst fb fpt)))
            = rhs .fst x
              by inverse (Loop Y) (refl F (concat M cst fb cst fpt (concat M fb fb cst L (inverse M cst fb fpt))))
                (concat Yc y (fb .fst x) y p (refl F (concat M fb fb cst L (inverse M cst fb fpt))))
                (map_path_concat M Yc F cst fb cst fpt (concat M fb fb cst L (inverse M cst fb fpt))) ∎))
