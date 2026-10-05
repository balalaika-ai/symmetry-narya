export "1333-pointed-circle-evaluation"
export "432-pointed-maps-truncation-level"

{` Chapter 13 (fields.tex 603-712): swapping pointed domains.
   X →* Y with the point cst is pointed_maps_pointed X Y. `}

def pointed_maps_pointed (X Y : Pointed) : Pointed ≔ (BookPointedMap X Y, book_pointed_constant X Y)

{` Running text before con:swap-ptd-doms: composition with O,
   (O ∘ -) : (S¹ →* (A →* B)) → (S¹ → ((S¹ →* A) →* (S¹ →* B))). `}
def o_functor_postcompose (C : CircleSignature) (A B : Pointed)
  (q : BookPointedMap (circle_pointed C) (pointed_maps_pointed A B))
  : C .carrier → BookPointedMap (circle_pointed_maps C A) (circle_pointed_maps C B)
  ≔ z ↦ o_functor_map C A B (q .fst z)

{` The symmetric description suggested in the book's implementation note:
   totally unpointed maps h : X → Y → Z with pointings a(x) : pt = h(x, pt_Y),
   b(y) : pt = h(pt_X, y) and the coherence a(pt_X) = b(pt_Y). `}
def BiPointedMap (X Y Z : Pointed) : Type
  ≔ Σ (X .carrier → Y .carrier → Z .carrier) (h ↦
      Σ ((x : X .carrier) → Id (Z .carrier) (Z .point) (h x (Y .point))) (a ↦
        Σ ((y : Y .carrier) → Id (Z .carrier) (Z .point) (h (X .point) y)) (b ↦
          Id (Id (Z .carrier) (Z .point) (h (X .point) (Y .point))) (a (X .point)) (b (Y .point)))))

def bi_concat_right_equiv (T : Type) (u v w : T) (e : Id T v w) : Equiv (Id T u v) (Id T u w)
  ≔ quasi_inverse_equiv (Id T u v) (Id T u w) (s ↦ concat T u v w s e) (t ↦ concat T u w v t (inverse T v w e))
      (s ↦ calc
        concat T u w v (concat T u v w s e) (inverse T v w e) = concat T u v v s (concat T v w v e (inverse T v w e))
          by concat_assoc T u v w v s e (inverse T v w e)
        = concat T u v v s (refl v) by refl (concat T u v v s) (concat_inverse_right T v w e)
        = s by concat_p1 T u v s ∎)
      (t ↦ calc
        concat T u v w (concat T u w v t (inverse T v w e)) e = concat T u w w t (concat T w v w (inverse T v w e) e)
          by concat_assoc T u w v w t (inverse T v w e) e
        = concat T u w w t (refl w) by refl (concat T u w w t) (concat_inverse_left T v w e)
        = t by concat_p1 T u w t ∎)

{` (refl·k(pt) = a) ≃ (a = k(pt)). `}
def bi_pointing_equiv (T : Type) (z t : T) (k a : Id T z t)
  : Equiv (Id (Id T z t) (concat T z z t (refl z) k) a) (Id (Id T z t) a k)
  ≔ compose_equiv (Id (Id T z t) (concat T z z t (refl z) k) a) (Id (Id T z t) a (concat T z z t (refl z) k))
      (Id (Id T z t) a k)
      (inverse_path_equiv (Id T z t) (concat T z z t (refl z) k) a)
      (bi_concat_right_equiv (Id T z t) a (concat T z z t (refl z) k) k (concat_1p T z t k))

{` X →* (Y →* Z) ≃ BiPointedMap X Y Z: the pointing f_pt : cst = f(pt_X) is
   replaced by ptw_*(f_pt) (con:identity-ptd-maps). The first component of
   the image of f is (x y ↦ f(x)(y)) judgmentally. `}
def bi_pointed_equiv (X Y Z : Pointed) : Equiv (BookPointedMap X (pointed_maps_pointed Y Z)) (BiPointedMap X Y Z)
  ≔ let A ≔ X .carrier in let B ≔ Y .carrier in let D ≔ Z .carrier in
    let x0 ≔ X .point in let y0 ≔ Y .point in let z ≔ Z .point in
    let YZ ≔ BookPointedMap Y Z in
    let cst ≔ book_pointed_constant Y Z in
    let Q ≔ (f0 ↦ Σ ((y : B) → Id D z (f0 x0 .fst y)) (k ↦ Id (Id D z (f0 x0 .fst y0)) (f0 x0 .snd) (k y0)))
      : (A → YZ) → Type in
    let S1 ≔ Σ (A → YZ) Q in
    compose_equiv (BookPointedMap X (pointed_maps_pointed Y Z)) S1 (BiPointedMap X Y Z)
      (family_equiv (A → YZ) (f0 ↦ Id YZ cst (f0 x0)) Q
        (f0 ↦ compose_equiv (Id YZ cst (f0 x0)) (PointedHomotopy Y Z cst (f0 x0)) (Q f0)
          (pointed_map_path_equiv Y Z cst (f0 x0))
          (family_equiv ((y : B) → Id D z (f0 x0 .fst y))
            (k ↦ Id (Id D z (f0 x0 .fst y0)) (concat D z z (f0 x0 .fst y0) (refl z) (k y0)) (f0 x0 .snd))
            (k ↦ Id (Id D z (f0 x0 .fst y0)) (f0 x0 .snd) (k y0))
            (k ↦ bi_pointing_equiv D z (f0 x0 .fst y0) (k y0) (f0 x0 .snd)))))
      (quasi_inverse_equiv S1 (BiPointedMap X Y Z)
        (u ↦ ((x y ↦ u .fst x .fst y), ((x ↦ u .fst x .snd), (u .snd .fst, u .snd .snd))))
        (v ↦ ((x ↦ (v .fst x, v .snd .fst x)), (v .snd .snd .fst, v .snd .snd .snd)))
        (u ↦ refl u) (v ↦ refl v))

{` Swapping the roles of X and Y in BiPointedMap. `}
def bi_pointed_swap (X Y Z : Pointed) (v : BiPointedMap X Y Z) : BiPointedMap Y X Z
  ≔ ((y x ↦ v .fst x y), (v .snd .snd .fst, (v .snd .fst,
      inverse (Id (Z .carrier) (Z .point) (v .fst (X .point) (Y .point))) (v .snd .fst (X .point)) (v .snd .snd .fst (Y .point))
        (v .snd .snd .snd))))

def bi_pointed_swap_equiv (X Y Z : Pointed) : Equiv (BiPointedMap X Y Z) (BiPointedMap Y X Z)
  ≔ let T ≔ (v ↦ Id (Z .carrier) (Z .point) (v .fst (X .point) (Y .point))) : BiPointedMap X Y Z → Type in
    quasi_inverse_equiv (BiPointedMap X Y Z) (BiPointedMap Y X Z) (bi_pointed_swap X Y Z) (bi_pointed_swap Y X Z)
      (v ↦ (refl (v .fst), (refl (v .snd .fst), (refl (v .snd .snd .fst),
        inverse_inverse (T v) (v .snd .fst (X .point)) (v .snd .snd .fst (Y .point)) (v .snd .snd .snd)))))
      (w ↦ (refl (w .fst), (refl (w .snd .fst), (refl (w .snd .snd .fst),
        inverse_inverse (Id (Z .carrier) (Z .point) (w .fst (Y .point) (X .point)))
          (w .snd .fst (Y .point)) (w .snd .snd .fst (X .point)) (w .snd .snd .snd)))))

{` The inverse of bi_pointed_equiv with an explicit underlying function:
   (h, a, b, c) ↦ (x ↦ (h x, a x)) pointed by ptw_*⁻¹(b, ·). `}
def bi_pointed_from (X Y Z : Pointed) (v : BiPointedMap X Y Z) : BookPointedMap X (pointed_maps_pointed Y Z)
  ≔ let D ≔ Z .carrier in let z ≔ Z .point in let y0 ≔ Y .point in
    let g ≔ (v .fst (X .point), v .snd .fst (X .point)) : BookPointedMap Y Z in
    let cst ≔ book_pointed_constant Y Z in
    ((x ↦ (v .fst x, v .snd .fst x)),
     equiv_inverse_map (Id (BookPointedMap Y Z) cst g) (PointedHomotopy Y Z cst g) (pointed_map_path_equiv Y Z cst g)
       (v .snd .snd .fst,
        equiv_inverse_map (Id (Id D z (g .fst y0)) (concat D z z (g .fst y0) (refl z) (v .snd .snd .fst y0)) (g .snd))
          (Id (Id D z (g .fst y0)) (g .snd) (v .snd .snd .fst y0))
          (bi_pointing_equiv D z (g .fst y0) (v .snd .snd .fst y0) (g .snd)) (v .snd .snd .snd)))

def bi_pointed_to_from (X Y Z : Pointed) (v : BiPointedMap X Y Z)
  : Id (BiPointedMap X Y Z) (bi_pointed_equiv X Y Z .map (bi_pointed_from X Y Z v)) v
  ≔ let D ≔ Z .carrier in let z ≔ Z .point in let y0 ≔ Y .point in
    let g ≔ (v .fst (X .point), v .snd .fst (X .point)) : BookPointedMap Y Z in
    let cst ≔ book_pointed_constant Y Z in
    let PH ≔ PointedHomotopy Y Z cst g in
    let E ≔ pointed_map_path_equiv Y Z cst g in
    let T ≔ Id D z (g .fst y0) in
    let V ≔ (k ↦ bi_pointing_equiv D z (g .fst y0) (k y0) (g .snd))
      : (k : (y : Y .carrier) → Id D z (g .fst y)) → Equiv (Id T (concat D z z (g .fst y0) (refl z) (k y0)) (g .snd)) (Id T (g .snd) (k y0)) in
    let fin ≔ (K ↦ (v .fst, (v .snd .fst, (K .fst, V (K .fst) .map (K .snd))))) : PH → BiPointedMap X Y Z in
    let K0 ≔ (v .snd .snd .fst,
        equiv_inverse_map (Id T (concat D z z (g .fst y0) (refl z) (v .snd .snd .fst y0)) (g .snd))
          (Id T (g .snd) (v .snd .snd .fst y0)) (V (v .snd .snd .fst)) (v .snd .snd .snd)) : PH in
    concat (BiPointedMap X Y Z) (fin (E .map (equiv_inverse_map (Id (BookPointedMap Y Z) cst g) PH E K0))) (fin K0) v
      (refl fin (equiv_counit (Id (BookPointedMap Y Z) cst g) PH E K0))
      (refl (v .fst), (refl (v .snd .fst), (refl (v .snd .snd .fst),
        equiv_counit (Id T (concat D z z (g .fst y0) (refl z) (v .snd .snd .fst y0)) (g .snd))
          (Id T (g .snd) (v .snd .snd .fst y0)) (V (v .snd .snd .fst)) (v .snd .snd .snd))))

def bi_pointed_from_inverse (X Y Z : Pointed) (v : BiPointedMap X Y Z)
  : Id (BookPointedMap X (pointed_maps_pointed Y Z))
      (equiv_inverse_map (BookPointedMap X (pointed_maps_pointed Y Z)) (BiPointedMap X Y Z) (bi_pointed_equiv X Y Z) v)
      (bi_pointed_from X Y Z v)
  ≔ let P ≔ BookPointedMap X (pointed_maps_pointed Y Z) in
    let Φ ≔ bi_pointed_equiv X Y Z in
    inverse P (bi_pointed_from X Y Z v) (equiv_inverse_map P (BiPointedMap X Y Z) Φ v)
      (concat P (bi_pointed_from X Y Z v) (equiv_inverse_map P (BiPointedMap X Y Z) Φ (Φ .map (bi_pointed_from X Y Z v)))
        (equiv_inverse_map P (BiPointedMap X Y Z) Φ v)
        (equiv_unit P (BiPointedMap X Y Z) Φ (bi_pointed_from X Y Z v))
        (refl (equiv_inverse_map P (BiPointedMap X Y Z) Φ) (bi_pointed_to_from X Y Z v)))

{` con:swap-ptd-doms: swap(f) ≔ bi_pointed_from (swap of bi_pointed_equiv f).
   Its underlying function is y ↦ (x ↦ f(x)(y)) judgmentally. `}
def swap_pointed_domains_map (X Y Z : Pointed) (f : BookPointedMap X (pointed_maps_pointed Y Z))
  : BookPointedMap Y (pointed_maps_pointed X Z)
  ≔ bi_pointed_from Y X Z (bi_pointed_swap X Y Z (bi_pointed_equiv X Y Z .map f))

def swap_pointed_domains_equiv (X Y Z : Pointed)
  : Equiv (BookPointedMap X (pointed_maps_pointed Y Z)) (BookPointedMap Y (pointed_maps_pointed X Z))
  ≔ equiv_change_map (BookPointedMap X (pointed_maps_pointed Y Z)) (BookPointedMap Y (pointed_maps_pointed X Z))
      (compose_equiv (BookPointedMap X (pointed_maps_pointed Y Z)) (BiPointedMap X Y Z) (BookPointedMap Y (pointed_maps_pointed X Z))
        (bi_pointed_equiv X Y Z)
        (compose_equiv (BiPointedMap X Y Z) (BiPointedMap Y X Z) (BookPointedMap Y (pointed_maps_pointed X Z))
          (bi_pointed_swap_equiv X Y Z)
          (canonical_inverse_equiv (BookPointedMap Y (pointed_maps_pointed X Z)) (BiPointedMap Y X Z) (bi_pointed_equiv Y X Z))))
      (swap_pointed_domains_map X Y Z)
      (f ↦ bi_pointed_from_inverse Y X Z (bi_pointed_swap X Y Z (bi_pointed_equiv X Y Z .map f)))

{` con:swap-ptd-doms: the totally unpointed map of swap is argument swapping:
   swap(f)(y)(x) = f(x)(y), judgmentally. `}
def swap_pointed_domains_underlying (X Y Z : Pointed) (f : BookPointedMap X (pointed_maps_pointed Y Z))
  : Id (Y .carrier → X .carrier → Z .carrier)
      (y x ↦ swap_pointed_domains_map X Y Z f .fst y .fst x) (y x ↦ f .fst x .fst y)
  ≔ refl ((y x ↦ f .fst x .fst y) : Y .carrier → X .carrier → Z .carrier)

{` The image of the constant map in BiPointedMap is the trivial datum. `}
def bi_pointed_trivial (X Y Z : Pointed) : BiPointedMap X Y Z
  ≔ ((_ _ ↦ Z .point), ((_ ↦ refl (Z .point)), ((_ ↦ refl (Z .point)), refl (refl (Z .point)))))

def bi_pointed_equiv_constant (X Y Z : Pointed)
  : Id (BiPointedMap X Y Z) (bi_pointed_equiv X Y Z .map (book_pointed_constant X (pointed_maps_pointed Y Z)))
      (bi_pointed_trivial X Y Z)
  ≔ let D ≔ Z .carrier in let z ≔ Z .point in let y0 ≔ Y .point in
    let cst ≔ book_pointed_constant Y Z in
    let L ≔ Id D z z in
    let cvt ≔ (K ↦ bi_pointing_equiv D z z (K .fst y0) (refl z) .map (K .snd))
      : (K : PointedHomotopy Y Z cst cst) → Id L (refl z) (K .fst y0) in
    let fin ≔ (K ↦ ((_ _ ↦ z), ((_ ↦ refl z), (K .fst, cvt K))))
      : PointedHomotopy Y Z cst cst → BiPointedMap X Y Z in
    concat (BiPointedMap X Y Z) (fin (pointed_map_path_equiv Y Z cst cst .map (refl cst)))
      (fin (pointed_homotopy_refl Y Z cst)) (bi_pointed_trivial X Y Z)
      (refl fin (ptw_refl_value Y Z cst))
      (refl ((_ _ ↦ z) : X .carrier → Y .carrier → D), (refl ((_ ↦ refl z) : X .carrier → L),
        (refl ((_ ↦ refl z) : Y .carrier → L),
         calc
           concat L (refl z) (concat D z z z (refl z) (refl z)) (refl z)
               (inverse L (concat D z z z (refl z) (refl z)) (refl z) (concat_p1 D z z (refl z))) (concat_1p D z z (refl z))
             = concat L (refl z) (concat D z z z (refl z) (refl z)) (refl z)
                 (inverse L (concat D z z z (refl z) (refl z)) (refl z) (concat_1p D z z (refl z))) (concat_1p D z z (refl z))
             by refl ((ρ ↦ concat L (refl z) (concat D z z z (refl z) (refl z)) (refl z)
                     (inverse L (concat D z z z (refl z) (refl z)) (refl z) ρ) (concat_1p D z z (refl z)))
                   : Id L (concat D z z z (refl z) (refl z)) (refl z) → Id L (refl z) (refl z))
                 (concat_p1_1p_refl D z)
           = refl (refl z) by concat_inverse_left L (concat D z z z (refl z) (refl z)) (refl z) (concat_1p D z z (refl z)) ∎)))

{` con:swap-ptd-doms: swap is pointed, swap(cst) = cst, hence a pointed
   equivalence (X →* (Y →* Z)) ≃* (Y →* (X →* Z)). `}
def swap_pointed_domains_point (X Y Z : Pointed)
  : Id (BookPointedMap Y (pointed_maps_pointed X Z)) (book_pointed_constant Y (pointed_maps_pointed X Z))
      (swap_pointed_domains_map X Y Z (book_pointed_constant X (pointed_maps_pointed Y Z)))
  ≔ let P ≔ BookPointedMap Y (pointed_maps_pointed X Z) in
    let Bp ≔ BiPointedMap Y X Z in
    let Φ ≔ bi_pointed_equiv Y X Z in
    let c ≔ book_pointed_constant Y (pointed_maps_pointed X Z) in
    let t ≔ bi_pointed_swap X Y Z (bi_pointed_equiv X Y Z .map (book_pointed_constant X (pointed_maps_pointed Y Z))) in
    let L ≔ Id (Z .carrier) (Z .point) (Z .point) in
    let e1 : Id Bp (Φ .map c) t
      ≔ calc
          Φ .map c = bi_pointed_trivial Y X Z by bi_pointed_equiv_constant Y X Z
          = bi_pointed_swap X Y Z (bi_pointed_trivial X Y Z)
            by (refl ((_ _ ↦ Z .point) : Y .carrier → X .carrier → Z .carrier),
                (refl ((_ ↦ refl (Z .point)) : Y .carrier → L), (refl ((_ ↦ refl (Z .point)) : X .carrier → L),
                 inverse (Id L (refl (Z .point)) (refl (Z .point)))
                   (inverse L (refl (Z .point)) (refl (Z .point)) (refl (refl (Z .point)))) (refl (refl (Z .point)))
                   (inverse_refl L (refl (Z .point))))))
          = t by refl (bi_pointed_swap X Y Z)
            (inverse (BiPointedMap X Y Z) (bi_pointed_equiv X Y Z .map (book_pointed_constant X (pointed_maps_pointed Y Z)))
              (bi_pointed_trivial X Y Z) (bi_pointed_equiv_constant X Y Z)) ∎ in
    concat P c (equiv_inverse_map P Bp Φ t) (bi_pointed_from Y X Z t)
      (concat P c (equiv_inverse_map P Bp Φ (Φ .map c)) (equiv_inverse_map P Bp Φ t)
        (equiv_unit P Bp Φ c) (refl (equiv_inverse_map P Bp Φ) e1))
      (bi_pointed_from_inverse Y X Z t)

def swap_pointed_domains (X Y Z : Pointed)
  : BookPointedEquiv (pointed_maps_pointed X (pointed_maps_pointed Y Z)) (pointed_maps_pointed Y (pointed_maps_pointed X Z))
  ≔ ((swap_pointed_domains_map X Y Z, swap_pointed_domains_point X Y Z),
     book_equivalence (BookPointedMap X (pointed_maps_pointed Y Z)) (BookPointedMap Y (pointed_maps_pointed X Z))
       (swap_pointed_domains_equiv X Y Z) .equiv)

{` xca:allptd-S1-contractible: for X, Y connected and Z a 1-type,
   X →* (Y →* Z) is contractible (Y →* Z is a set and X →* (a set) is a
   proposition by ft:ptd-decr-h-lev, module 432, inhabited by cst). `}
def pointed_pointed_maps_contractible (X Y Z : Pointed) (hX : Connected (X .carrier)) (hY : Connected (Y .carrier))
  (hZ : isGroupoid (Z .carrier))
  : BookIsContr (BookPointedMap X (pointed_maps_pointed Y Z))
  ≔ let one : Nat ≔ suc. zero. in
    let conn : (W : Type) → Connected W → NConnectedType one W
      ≔ W h ↦ equiv_inverse_map (NConnectedType one W) (Connected W) (zero_connected_connected W) h in
    let hYZ : HLevel (suc. (suc. zero.)) (BookPointedMap Y Z)
      ≔ pointed_maps_truncation_level one (suc. (suc. zero.)) Y Z (conn (Y .carrier) hY) (groupoid_to_hlevel (Z .carrier) hZ) in
    let hP : HLevel one (BookPointedMap X (pointed_maps_pointed Y Z))
      ≔ pointed_maps_truncation_level one one X (pointed_maps_pointed Y Z) (conn (X .carrier) hX) hYZ in
    let pr ≔ hlevel_one_to_prop (BookPointedMap X (pointed_maps_pointed Y Z)) hP in
    (book_pointed_constant X (pointed_maps_pointed Y Z), u ↦ pr (book_pointed_constant X (pointed_maps_pointed Y Z)) u)

{` con:swap-on-paths: for f : A → (B → C) and g(b)(a) ≔ f(a)(b), and
   q : b = b', the functions a ↦ ap_{f(a)}(q) and a ↦ ptw(ap_g(q))(a) are
   identified. By induction on q, as in the book. `}
def swap_on_paths (A B C : Type) (f : A → B → C) (b b' : B) (q : Id B b b')
  : Id ((a : A) → Id C (f a b) (f a b'))
      (a ↦ refl (f a) q)
      (happly A (_ ↦ C) ((a ↦ f a b) : A → C) ((a ↦ f a b') : A → C) (refl ((y a ↦ f a y) : B → A → C) q))
  ≔ J B b (b' q ↦ Id ((a : A) → Id C (f a b) (f a b'))
        (a ↦ refl (f a) q)
        (happly A (_ ↦ C) ((a ↦ f a b) : A → C) ((a ↦ f a b') : A → C) (refl ((y a ↦ f a y) : B → A → C) q)))
      (refl ((a ↦ refl (f a b)) : (a : A) → Id C (f a b) (f a b))) b' q
