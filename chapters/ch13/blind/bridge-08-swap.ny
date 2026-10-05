export "08-swap"
export "../../../src/1397-o-prime-swap"

{` Bridges for fields.tex, swapping pointed domains (blocks 612, 632, 693, 782).
   Our swap_pointed_domains is a BlindSwap (its totally unpointed map is the argument swap by refl).
   The specification BlindSwap fixes only the totally unpointed map; any two BlindSwaps agree there
   (bridge_swap_spec_unique), but the inner and outer pointing paths are left free.
   def:O' (782): the blind reading O'(φ) = sw ∘ O(φ), sw a BlindSwap S¹ S¹ Y standing for swap⁻¹, is the
   reading of fig:bjørn; our o_functor_pointed (module 1335) is O_{A,B} pointed without any swap, a
   different map. Ours is related to the blind reading only through sw: blind_O'(sw)(φ) = sw ∘ o_functor_map(φ)
   (bridge_def_O'_swap), and for every BlindSwap sw the totally unpointed part of blind_O'(sw)(φ)(g) is
   (y, x) ↦ O(φ)(g)(x)(y) (bridge_def_O'_unpointed). The fig:bjørn reading is now formalized in module 1397
   (o_prime_map, o_prime_pointed: O'(φ) = swap⁻¹ ∘ O(φ) with swap⁻¹ the inverse pointed equivalence of
   swap_{S¹,S¹,Y}); swap⁻¹ satisfies the blind specification and blind_O' at it is o_prime_map (bridge_def_O'). `}

{` con:swap-ptd-doms (fields.tex:612). `}
def bridge_def_swap (X Y Z : Pointed) : BlindSwap X Y Z
  ≔ (swap_pointed_domains X Y Z, F ↦ swap_pointed_domains_underlying X Y Z F)

def bridge_con_swap_ptd_doms : blind_con_swap_ptd_doms ≔ X Y Z ↦ bridge_def_swap X Y Z

def bridge_swap_spec_unique (X Y Z : Pointed) (sw sw' : BlindSwap X Y Z) (F : BookPointedMap X (blind_ptd_maps Y Z))
  : Id (Y .carrier → X .carrier → Z .carrier)
      (y x ↦ sw .fst .fst .fst F .fst y .fst x) (y x ↦ sw' .fst .fst .fst F .fst y .fst x)
  ≔ concat (Y .carrier → X .carrier → Z .carrier)
      (y x ↦ sw .fst .fst .fst F .fst y .fst x) (y x ↦ F .fst x .fst y) (y x ↦ sw' .fst .fst .fst F .fst y .fst x)
      (sw .snd F)
      (inverse (Y .carrier → X .carrier → Z .carrier) (y x ↦ sw' .fst .fst .fst F .fst y .fst x) (y x ↦ F .fst x .fst y)
        (sw' .snd F))

{` xca:allptd-S1-contractible (fields.tex:632). `}
def bridge_xca_allptd_S1_contractible : blind_xca_allptd_S1_contractible
  ≔ X Y Z hX hY hZ ↦ pointed_pointed_maps_contractible X Y Z hX hY hZ

{` con:swap-on-paths (fields.tex:693). `}
def bridge_con_swap_on_paths : blind_con_swap_on_paths ≔ A B C f b b' q ↦ swap_on_paths A B C f b b' q

{` def:O' (fields.tex:782). The O-map bridge of bridge-07, restated here (bridge files do not import each other). `}
def bridge_swap_O_map (C : CircleSignature) (A B : Pointed) (f : BookPointedMap A B)
  : Id (BookPointedMap (blind_O C A) (blind_O C B)) (blind_O_map C A B f) (o_functor_map C A B f)
  ≔ let fa ≔ f .fst (A .point) in
    (refl ((g ↦ book_pointed_compose (circle_pointed C) A B g f)
        : BookPointedMap (circle_pointed C) A → BookPointedMap (circle_pointed C) B),
     o_constant_paths_agree C B fa (concat (B .carrier) (B .point) fa fa (f .snd) (refl fa))
       (blind_O_sigma_path (B .carrier) (B .point) fa (f .snd)) (o_point_path (B .carrier) (B .point) fa (f .snd)))

def bridge_def_O'_swap (C : CircleSignature) (A Y : Pointed) (sw : BlindSwap (circle_pointed C) (circle_pointed C) Y)
  (φ : BookPointedMap A (blind_ptd_maps (circle_pointed C) Y))
  : Id (BookPointedMap (circle_pointed_maps C A) (circle_pointed_maps C (circle_pointed_maps C Y)))
      (blind_O' C A Y sw φ)
      (book_pointed_compose (circle_pointed_maps C A) (circle_pointed_maps C (circle_pointed_maps C Y))
        (circle_pointed_maps C (circle_pointed_maps C Y)) (o_functor_map C A (circle_pointed_maps C Y) φ) (sw .fst .fst))
  ≔ let OA ≔ circle_pointed_maps C A in let W ≔ circle_pointed_maps C (circle_pointed_maps C Y) in
    refl ((k ↦ book_pointed_compose OA W W k (sw .fst .fst)) : BookPointedMap OA W → BookPointedMap OA W)
      (bridge_swap_O_map C A (circle_pointed_maps C Y) φ)

def bridge_def_O'_unpointed (C : CircleSignature) (A Y : Pointed) (sw : BlindSwap (circle_pointed C) (circle_pointed C) Y)
  (φ : BookPointedMap A (blind_ptd_maps (circle_pointed C) Y)) (g : BookPointedMap (circle_pointed C) A)
  : Id (C .carrier → C .carrier → Y .carrier)
      (y x ↦ blind_O' C A Y sw φ .fst g .fst y .fst x)
      (y x ↦ o_functor_map C A (circle_pointed_maps C Y) φ .fst g .fst x .fst y)
  ≔ sw .snd (o_functor_map C A (circle_pointed_maps C Y) φ .fst g)

{` The inverse of our swap is a BlindSwap S¹ S¹ Y, and blind_O' at it is o_prime_map (module 1397). `}
def bridge_swap_inverse_as_blind (C : CircleSignature) (Y : Pointed) : BlindSwap (circle_pointed C) (circle_pointed C) Y
  ≔ (swap_circle_inverse C Y, F ↦ swap_circle_inverse_underlying C Y F)

def bridge_def_O' (C : CircleSignature) (A Y : Pointed) (φ : BookPointedMap A (blind_ptd_maps (circle_pointed C) Y))
  : Id (BookPointedMap (circle_pointed_maps C A) (circle_pointed_maps C (circle_pointed_maps C Y)))
      (blind_O' C A Y (bridge_swap_inverse_as_blind C Y) φ) (o_prime_map C A Y φ)
  ≔ bridge_def_O'_swap C A Y (bridge_swap_inverse_as_blind C Y) φ
