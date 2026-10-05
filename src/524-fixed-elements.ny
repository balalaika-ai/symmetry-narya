export "522-orbit-fibers"

{` Chapter 5, sec:fixpts-orbits: fixed elements and invariant maps.
   lem:fixed-char (x fixed iff G · x contractible iff x = g · x for all g),
   with the identification of the fiber of Bi_x at sh_G with G · x (also
   the action type of G̃_x in con:orbit-stabilizer), the claim before
   lem:fixpts-are-fixed, lem:fixpts-are-fixed, xca:HomGsets-ev, and the
   footnote of def:actiontype on invariant maps (P_Z has none). `}

{` The fiber of Bi_x = fst : BG_x → BG at sh_G is G · x (proof of
   lem:fixed-char; it is also the action type of G̃_x, con:orbit-stabilizer):
   reassociate, contract away z with sh_G = z, and use
   ‖(sh_G, x) = (sh_G, y)‖ ≃ ([x] = [y]). `}
def StabilizerInclusionFiber (G : Group) (X : GSet G) (x : gset_underlying G X) : Type
  ≔ BookFiber (BG (stabilizer_group G X x) .carrier) (BG G .carrier)
      (hom_function (stabilizer_group G X x) G (stabilizer_inclusion G X x)) (shape G)

def stabilizer_fiber_regroup (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Equiv (StabilizerInclusionFiber G X x)
      (Σ (BG G .carrier) (z ↦ Product (Id (BG G .carrier) (shape G) z)
        (Σ (X z .fst) (y ↦ Mere (Id (ActionType G X) (shape G, x) (z, y))))))
  ≔ quasi_inverse_equiv (StabilizerInclusionFiber G X x)
      (Σ (BG G .carrier) (z ↦ Product (Id (BG G .carrier) (shape G) z)
        (Σ (X z .fst) (y ↦ Mere (Id (ActionType G X) (shape G, x) (z, y))))))
      (t ↦ (t .fst .fst .fst, (t .snd, (t .fst .fst .snd, t .fst .snd))))
      (s ↦ (((s .fst, s .snd .snd .fst), s .snd .snd .snd), s .snd .fst))
      (t ↦ refl t) (s ↦ refl s)

def stabilizer_inclusion_fiber_equiv (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Equiv (StabilizerInclusionFiber G X x) (OrbitUnderlying G X x)
  ≔ let B ≔ BG G .carrier in
    let P ≔ (z ↦ Σ (X z .fst) (y ↦ Mere (Id (ActionType G X) (shape G, x) (z, y)))) : B → Type in
    compose_equiv (StabilizerInclusionFiber G X x) (Σ B (z ↦ Product (Id B (shape G) z) (P z)))
      (OrbitUnderlying G X x)
      (stabilizer_fiber_regroup G X x)
      (compose_equiv (Σ B (z ↦ Product (Id B (shape G) z) (P z))) (P (shape G)) (OrbitUnderlying G X x)
        (contract_away_simple B (shape G) P)
        (orbit_gset_underlying_equiv G X x))

{` lem:fixed-char. x is fixed iff G · x is contractible: Bi_x is an
   equivalence iff all its fibers are contractible, iff (BG connected) its
   fiber at sh_G, which is G · x, is. `}
def fixed_element_orbit_contractible (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Equiv (IsFixedElement G X x) (BookIsContr (OrbitUnderlying G X x))
  ≔ let C ≔ BG (stabilizer_group G X x) .carrier in
    let B ≔ BG G .carrier in
    let f ≔ hom_function (stabilizer_group G X x) G (stabilizer_inclusion G X x) in
    let e ≔ book_contractibility_equiv (StabilizerInclusionFiber G X x) (OrbitUnderlying G X x)
      (stabilizer_inclusion_fiber_equiv G X x) in
    iff_equiv (IsFixedElement G X x) (BookIsContr (OrbitUnderlying G X x))
      (is_fixed_element_prop G X x) (book_iscontr_isprop (OrbitUnderlying G X x))
      (h ↦ e .map (h (shape G)))
      (c ↦ connected_based_elim native_truncation B (bg_connected G) (shape G)
        (z ↦ BookIsContr (BookFiber C B f z)) (z ↦ book_iscontr_isprop (BookFiber C B f z))
        (equiv_inverse_map (BookIsContr (StabilizerInclusionFiber G X x)) (BookIsContr (OrbitUnderlying G X x)) e c))

{` lem:fixed-char, "i.e. x = g · x for all g : USym G". `}
def orbit_contractible_fixed_by_all (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Equiv (BookIsContr (OrbitUnderlying G X x)) ((g : USym G) → Id (gset_underlying G X) x (gset_usym_act G X g x))
  ≔ let S ≔ gset_underlying G X in
    let Or ≔ Orbits G X in
    let Ox ≔ OrbitUnderlying G X x in
    let base : Ox ≔ (x, refl (orbit_of_point G X x)) in
    iff_equiv (BookIsContr Ox) ((g : USym G) → Id S x (gset_usym_act G X g x))
      (book_iscontr_isprop Ox)
      (pi_prop (USym G) (g ↦ Id S x (gset_usym_act G X g x)) (g ↦ gset_underlying_set G X x (gset_usym_act G X g x)))
      (h g ↦ map_path Ox S (w ↦ w .fst) base (orbit_action_map G X x g)
        (concat Ox base (h .center) (orbit_action_map G X x g)
          (inverse Ox (h .center) base (h .contract base)) (h .contract (orbit_action_map G X x g))))
      (k ↦ (base, w ↦
        mere_rec (Σ (USym G) (g ↦ Id S (gset_usym_act G X g x) (w .fst))) (Id Ox base w)
          (orbit_underlying_set G X x base w)
          (ge ↦ subtype_equal S (y ↦ Id Or (orbit_of_point G X x) (orbit_of_point G X y))
            (y ↦ orbits_set G X (orbit_of_point G X x) (orbit_of_point G X y)) base w
            (concat S x (gset_usym_act G X (ge .fst) x) (w .fst) (k (ge .fst)) (ge .snd)))
          (orbit_relation_from_path G X x (w .fst) (w .snd))))

def fixed_element_fixed_by_all (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Equiv (IsFixedElement G X x) ((g : USym G) → Id (gset_underlying G X) x (gset_usym_act G X g x))
  ≔ compose_equiv (IsFixedElement G X x) (BookIsContr (OrbitUnderlying G X x))
      ((g : USym G) → Id (gset_underlying G X) x (gset_usym_act G X g x))
      (fixed_element_orbit_contractible G X x) (orbit_contractible_fixed_by_all G X x)

{` def:actiontype (2), footnote: an invariant map f satisfies
   f(z) = g · f(z) for every z : BG and g : z = z (apd_f(g), with
   def:pathover-trp). `}
def invariant_map_fixed_by_loops (G : Group) (X : GSet G) (f : InvariantMaps G X) (z : BG G .carrier)
  (g : Id (BG G .carrier) z z) : Id (X z .fst) (f z) (gset_act G X z z g (f z))
  ≔ inverse (X z .fst) (gset_act G X z z g (f z)) (f z)
      (pathover_transport_equiv (BG G .carrier) (w ↦ X w .fst) z z g (f z) (f z) .map (refl f g))

{` The claim before lem:fixpts-are-fixed: evaluating an invariant map at
   sh_G lands in the fixed elements, x ≔ f(sh_G) satisfies g · x = x. `}
def invariant_map_value_fixed_by_all (G : Group) (X : GSet G) (f : InvariantMaps G X) (g : USym G)
  : Id (gset_underlying G X) (f (shape G)) (gset_usym_act G X g (f (shape G)))
  ≔ invariant_map_fixed_by_loops G X f (shape G) g

def invariant_map_value_fixed (G : Group) (X : GSet G) (f : InvariantMaps G X) : IsFixedElement G X (f (shape G))
  ≔ equiv_inverse_map (IsFixedElement G X (f (shape G)))
      ((g : USym G) → Id (gset_underlying G X) (f (shape G)) (gset_usym_act G X g (f (shape G))))
      (fixed_element_fixed_by_all G X (f (shape G))) (invariant_map_value_fixed_by_all G X f)

{` lem:fixpts-are-fixed. The evaluation map ev : X^hG → X(sh_G), f ↦ f(sh_G). `}
def invariant_map_eval (G : Group) (X : GSet G) (f : InvariantMaps G X) : gset_underlying G X ≔ f (shape G)

{` it:ev-is-inj. ev is injective (BG is connected, function extensionality). `}
def invariant_map_eval_reflects (G : Group) (X : GSet G)
  : PathReflecting (InvariantMaps G X) (gset_underlying G X) (invariant_map_eval G X)
  ≔ let B ≔ BG G .carrier in
    f f' e ↦ funext B (z ↦ X z .fst) f f'
      (connected_based_elim native_truncation B (bg_connected G) (shape G) (z ↦ Id (X z .fst) (f z) (f' z))
        (z ↦ X z .snd (f z) (f' z)) e)

def invariant_map_eval_injective (G : Group) (X : GSet G)
  : IsEmbedding (InvariantMaps G X) (gset_underlying G X) (invariant_map_eval G X)
  ≔ path_reflecting_set_embedding (InvariantMaps G X) (gset_underlying G X) (gset_underlying_set G X)
      (invariant_map_eval G X) (invariant_map_eval_reflects G X)

{` A fixed x determines an invariant map: since Bi_x = fst is an
   equivalence, each fiber at z is contractible; its center (c, q : z = c₁)
   gives f(z) ≔ q⁻¹ · c₂ : X(z). `}
def fixed_element_invariant_map (G : Group) (X : GSet G) (x : gset_underlying G X) (h : IsFixedElement G X x)
  : InvariantMaps G X
  ≔ let B ≔ BG G .carrier in
    z ↦ let c ≔ h z .center in
      gset_act G X (c .fst .fst .fst) z (inverse B z (c .fst .fst .fst) (c .snd)) (c .fst .fst .snd)

def fixed_element_invariant_map_eval (G : Group) (X : GSet G) (x : gset_underlying G X) (h : IsFixedElement G X x)
  : Id (gset_underlying G X) x (invariant_map_eval G X (fixed_element_invariant_map G X x h))
  ≔ let B ≔ BG G .carrier in
    let T ≔ ActionType G X in
    let S ≔ gset_underlying G X in
    let fixall ≔ fixed_element_fixed_by_all G X x .map h in
    let c ≔ h (shape G) .center in
    let z' ≔ c .fst .fst .fst in
    let y' ≔ c .fst .fst .snd in
    let qi ≔ inverse B (shape G) z' (c .snd) in
    let y ≔ gset_act G X z' (shape G) qi y' in
    let m2 : Mere (Id T (shape G, x) (shape G, y))
      ≔ trunc_map native_truncation (Id T (shape G, x) (z', y')) (Id T (shape G, x) (shape G, y))
          (r ↦ concat T (shape G, x) (z', y') (shape G, y) r (action_type_path G X z' (shape G) y' y qi (refl y)))
          (c .fst .snd) in
    mere_rec (Σ (USym G) (g ↦ Id S (gset_usym_act G X g x) y)) (Id S x y) (gset_underlying_set G X x y)
      (ge ↦ concat S x (gset_usym_act G X (ge .fst) x) y (fixall (ge .fst)) (ge .snd))
      (orbit_relation_from_path G X x y (orbit_map_path_from_mere G X (shape G, x) (shape G, y) m2))

{` it:ev-is-eq-on-inv. The fiber of ev at x is the proposition "x is
   fixed"; so the image of ev is {x : X(sh_G) | x is fixed}. `}
def invariant_map_eval_fiber_equiv (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Equiv (BookFiber (InvariantMaps G X) (gset_underlying G X) (invariant_map_eval G X) x) (IsFixedElement G X x)
  ≔ let S ≔ gset_underlying G X in
    iff_equiv (BookFiber (InvariantMaps G X) S (invariant_map_eval G X) x) (IsFixedElement G X x)
      (invariant_map_eval_injective G X x) (is_fixed_element_prop G X x)
      (t ↦ transport S (y ↦ IsFixedElement G X y) (t .fst (shape G)) x (inverse S x (t .fst (shape G)) (t .snd))
        (invariant_map_value_fixed G X (t .fst)))
      (h ↦ (fixed_element_invariant_map G X x h, fixed_element_invariant_map_eval G X x h))

def invariant_map_eval_image (G : Group) (X : GSet G) (x : gset_underlying G X)
  : Equiv (Mere (BookFiber (InvariantMaps G X) (gset_underlying G X) (invariant_map_eval G X) x))
      (IsFixedElement G X x)
  ≔ let F ≔ BookFiber (InvariantMaps G X) (gset_underlying G X) (invariant_map_eval G X) x in
    iff_equiv (Mere F) (IsFixedElement G X x) (mere_isprop F) (is_fixed_element_prop G X x)
      (m ↦ mere_rec F (IsFixedElement G X x) (is_fixed_element_prop G X x)
        (invariant_map_eval_fiber_equiv G X x .map) m)
      (h ↦ mere F (equiv_inverse_map F (IsFixedElement G X x) (invariant_map_eval_fiber_equiv G X x) h))

{` Together: X^hG ≃ {x : X(sh_G) | x is fixed}, f ↦ (f(sh_G), !). `}
def invariant_maps_fixed_elements_equiv (G : Group) (X : GSet G)
  : Equiv (InvariantMaps G X) (Σ (gset_underlying G X) (x ↦ IsFixedElement G X x))
  ≔ let S ≔ gset_underlying G X in
    let I ≔ InvariantMaps G X in
    compose_equiv I (Σ S (x ↦ BookFiber I S (invariant_map_eval G X) x)) (Σ S (x ↦ IsFixedElement G X x))
      (canonical_inverse_equiv (Σ S (x ↦ BookFiber I S (invariant_map_eval G X) x)) I
        (sum_of_fibers_equiv I S (invariant_map_eval G X)))
      (family_equiv S (x ↦ BookFiber I S (invariant_map_eval G X) x) (x ↦ IsFixedElement G X x)
        (invariant_map_eval_fiber_equiv G X))

{` xca:HomGsets-ev. The G-set z ↦ (X(z) → Y(z)); its invariant maps are
   by definition the maps of G-sets, and its action is conjugation
   p · φ = X(p) ∘ φ ∘ X(p)⁻¹ by definition (lem:trp-in-function-type, with
   the native backward transport .trl for X(p)⁻¹). `}
def gset_hom_gset (G : Group) (X Y : GSet G) : GSet G
  ≔ z ↦ (X z .fst → Y z .fst, pi_set (X z .fst) (_ ↦ Y z .fst) (_ ↦ Y z .snd))

def gset_hom_gset_invariant_maps (G : Group) (X Y : GSet G)
  : Id Type (InvariantMaps G (gset_hom_gset G X Y)) (GSetHom G X Y)
  ≔ refl (GSetHom G X Y)

def gset_hom_gset_act (G : Group) (X Y : GSet G) (z w : BG G .carrier) (p : Id (BG G .carrier) z w)
  (φ : X z .fst → Y z .fst) (a : X w .fst)
  : Id (Y w .fst) (gset_act G (gset_hom_gset G X Y) z w p φ a)
      (gset_act G Y z w p (φ (refl ((u ↦ X u .fst) : BG G .carrier → Type) p .trl a)))
  ≔ refl (gset_act G Y z w p (φ (refl ((u ↦ X u .fst) : BG G .carrier → Type) p .trl a)))

{` xca:HomGsets-ev. Evaluation at sh_G is an equivalence between
   Hom_G(X, Y) and the subset of X(sh_G) → Y(sh_G) of fixed elements of
   z ↦ (X(z) → Y(z)). `}
def gset_hom_fixed_maps_equiv (G : Group) (X Y : GSet G)
  : Equiv (GSetHom G X Y)
      (Σ (gset_underlying G X → gset_underlying G Y) (φ ↦ IsFixedElement G (gset_hom_gset G X Y) φ))
  ≔ invariant_maps_fixed_elements_equiv G (gset_hom_gset G X Y)

def gset_hom_fixed_maps_equiv_fst (G : Group) (X Y : GSet G) (f : GSetHom G X Y)
  : Id (gset_underlying G X → gset_underlying G Y) (gset_hom_fixed_maps_equiv G X Y .map f .fst) (f (shape G))
  ≔ refl (f (shape G))

{` Footnote of def:actiontype (2): the principal Z-set P_Z, Z = (S¹, base),
   has no invariant maps, Π_{z:S¹} (base = z) is empty: f(base) = f(base) ·
   loop would give loop = refl. Stated for every circle C. `}
def invariant_maps_int_one_code : Int → Type ≔ [
  | pos. zero. ↦ Empty
  | pos. (suc. _) ↦ Unit
  | neg. _ ↦ Empty ]

def invariant_maps_circle_loop_nontrivial (C : CircleSignature)
  (p : Id (Id (C .carrier) (C .base) (C .base)) (C .loop) (refl (C .base))) : Empty
  ≔ transport Int invariant_maps_int_one_code (pos. (suc. zero.)) int_zero
      (concat Int (pos. (suc. zero.)) (circle_winding C (C .loop)) int_zero
        (inverse Int (circle_winding C (C .loop)) (pos. (suc. zero.)) (circle_winding_loop C))
        (concat Int (circle_winding C (C .loop)) (circle_winding C (refl (C .base))) int_zero
          (refl (circle_winding C) p) (circle_winding_refl C)))
      star.

def principal_circle_no_invariant_maps (C : CircleSignature)
  (f : InvariantMaps (circle_group C) (principal_gset (circle_group C))) : Empty
  ≔ let A ≔ C .carrier in
    let b ≔ C .base in
    let l ≔ C .loop in
    let fb ≔ f b in
    let e : Id (Id A b b) fb (concat A b b b fb l)
      ≔ invariant_map_fixed_by_loops (circle_group C) (principal_gset (circle_group C)) f b l in
    invariant_maps_circle_loop_nontrivial C
      (inverse (Id A b b) (refl b) l
        (concat_cancel_left A b b b fb (refl b) l
          (concat (Id A b b) (concat A b b b fb (refl b)) fb (concat A b b b fb l) (concat_p1 A b b fb) e)))
