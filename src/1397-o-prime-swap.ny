export "1335-swap-and-loops"

{` Chapter 13 (fields.tex:782), def:O' read through fig:bjørn. As printed, O'_{A,B} ≔ (O_{A,B} ∘ swap⁻¹ ∘ -)
   is ill-typed for general B. In fig:bjørn O' : (X →* O Y) → (O X →* O(O Y)) and the triangle
   (swap ∘ -) ∘ O' = O gives O'(φ) = swap⁻¹ ∘ O(φ), with swap = swap_{S¹,S¹,Y} the automorphism of
   O(O Y) = S¹ →* (S¹ →* Y) exchanging the two circle arguments (con:swap-ptd-doms). Here swap⁻¹ is the
   inverse pointed equivalence (pointed by swap(cst) = cst), O'(φ) ≔ swap⁻¹ ∘ O(φ) (pointed composition),
   and O' is a pointed map (A →* O Y) →* (O A →* O(O Y)), pointed through O(cst) = cst
   (o_functor_pointed_point) and swap⁻¹ ∘ cst = cst. o_functor_pointed (module 1335) is O_{A,B} pointed,
   without the swap; it is a different map, since swap is not the identity on S¹ →* (S¹ →* BB ℤ)
   (swap(m_k) = m_{−k}, example_swap_m_negative). `}

{` swap⁻¹ for X = Y = S¹, as a pointed map. `}
def swap_circle_inverse_map (C : CircleSignature) (Y : Pointed)
  : BookPointedMap (circle_pointed_maps C (circle_pointed_maps C Y)) (circle_pointed_maps C (circle_pointed_maps C Y))
  ≔ let S ≔ circle_pointed C in let M ≔ BookPointedMap S (pointed_maps_pointed S Y) in
    let e ≔ swap_pointed_domains_equiv S S Y in
    let g ≔ equiv_inverse_map M M e in
    let c ≔ book_pointed_constant S (pointed_maps_pointed S Y) in
    (g, concat M c (g (e .map c)) (g c)
          (inverse M (g (e .map c)) c (equiv_retraction M M e c))
          (refl g (inverse M c (e .map c) (swap_pointed_domains_point S S Y))))

def swap_circle_inverse (C : CircleSignature) (Y : Pointed)
  : BookPointedEquiv (circle_pointed_maps C (circle_pointed_maps C Y)) (circle_pointed_maps C (circle_pointed_maps C Y))
  ≔ let S ≔ circle_pointed C in let M ≔ BookPointedMap S (pointed_maps_pointed S Y) in
    (swap_circle_inverse_map C Y,
     book_equivalence M M (canonical_inverse_equiv M M (swap_pointed_domains_equiv S S Y)) .equiv)

{` swap⁻¹ also swaps the two arguments of the totally unpointed map. `}
def swap_circle_inverse_underlying (C : CircleSignature) (Y : Pointed)
  (F : BookPointedMap (circle_pointed C) (pointed_maps_pointed (circle_pointed C) Y))
  : Id (C .carrier → C .carrier → Y .carrier)
      (y x ↦ swap_circle_inverse_map C Y .fst F .fst y .fst x) (y x ↦ F .fst x .fst y)
  ≔ let S ≔ circle_pointed C in let M ≔ BookPointedMap S (pointed_maps_pointed S Y) in
    refl ((H ↦ (y x ↦ H .fst x .fst y)) : M → C .carrier → C .carrier → Y .carrier)
      (equiv_counit M M (swap_pointed_domains_equiv S S Y) F)

{` A pointed constant map followed by any pointed map is the pointed constant map. `}
def o_prime_constant_compose (V W W' : Pointed) (k : BookPointedMap W W')
  : Id (BookPointedMap V W') (book_pointed_constant V W') (book_pointed_compose V W W' (book_pointed_constant V W) k)
  ≔ book_pointed_constant_path V W' (k .fst (W .point))
      (concat (W' .carrier) (W' .point) (k .fst (W .point)) (k .fst (W .point)) (k .snd) (refl (k .fst (W .point))))

{` def:O' (fig:bjørn reading): O'(φ) ≔ swap⁻¹ ∘ O(φ). `}
def o_prime_map (C : CircleSignature) (A Y : Pointed) (φ : BookPointedMap A (circle_pointed_maps C Y))
  : BookPointedMap (circle_pointed_maps C A) (circle_pointed_maps C (circle_pointed_maps C Y))
  ≔ book_pointed_compose (circle_pointed_maps C A) (circle_pointed_maps C (circle_pointed_maps C Y))
      (circle_pointed_maps C (circle_pointed_maps C Y))
      (o_functor_map C A (circle_pointed_maps C Y) φ) (swap_circle_inverse_map C Y)

def o_prime_point (C : CircleSignature) (A Y : Pointed)
  : Id (BookPointedMap (circle_pointed_maps C A) (circle_pointed_maps C (circle_pointed_maps C Y)))
      (book_pointed_constant (circle_pointed_maps C A) (circle_pointed_maps C (circle_pointed_maps C Y)))
      (o_prime_map C A Y (book_pointed_constant A (circle_pointed_maps C Y)))
  ≔ let OA ≔ circle_pointed_maps C A in let W ≔ circle_pointed_maps C (circle_pointed_maps C Y) in
    let sw ≔ swap_circle_inverse_map C Y in
    concat (BookPointedMap OA W) (book_pointed_constant OA W) (book_pointed_compose OA W W (book_pointed_constant OA W) sw)
      (o_prime_map C A Y (book_pointed_constant A (circle_pointed_maps C Y)))
      (o_prime_constant_compose OA W W sw)
      (refl ((k ↦ book_pointed_compose OA W W k sw) : BookPointedMap OA W → BookPointedMap OA W)
        (o_functor_pointed_point C A (circle_pointed_maps C Y)))

def o_prime_pointed (C : CircleSignature) (A Y : Pointed)
  : BookPointedMap (pointed_maps_pointed A (circle_pointed_maps C Y))
      (pointed_maps_pointed (circle_pointed_maps C A) (circle_pointed_maps C (circle_pointed_maps C Y)))
  ≔ (o_prime_map C A Y, o_prime_point C A Y)
