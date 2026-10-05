export "03-pullback"
export "../../../src/891-circle-pullback-explicit"

{` Bridges for ex:pullbackandgcd (congp.tex:355). BlindCirclePullback
   is our CirclePowerPullback. (1) is circle_power_pullback_components_fin;
   (2), the displayed square as an explicit equivalence with coordinates
   z^{b'}, z^{a'} on every copy, is the new explicit decomposition of module
   891 together with lcm(a,b)/a = b', lcm(a,b)/b = a' (cpx_quotient_*_eq),
   transported along d = gcd(a,b); (3) is circle_pullback_component_lcm_cover
   on the component of u (set-truncation component vs native component). `}

def bridge_ex_pullbackandgcd_components : blind_ex_pullbackandgcd_components
  ≔ C a b ↦ match a [
    | zero. ↦ ha _ ↦ absurd (BookEquiv (SetTrunc (BlindCirclePullback C zero. b)) (Fin (nat_gcd zero. b))) (ha (refl (zero. : Nat)))
    | suc. a1 ↦ match b [
      | zero. ↦ _ hb ↦ absurd (BookEquiv (SetTrunc (BlindCirclePullback C (suc. a1) zero.)) (Fin (nat_gcd (suc. a1) zero.)))
          (hb (refl (zero. : Nat)))
      | suc. b1 ↦ _ _ ↦ book_equivalence (SetTrunc (CirclePowerPullback C (suc. a1) (suc. b1))) (Fin (nat_gcd (suc. a1) (suc. b1)))
          (circle_power_pullback_components_fin C a1 b1) ] ]

def bp_square_type (C : CircleSignature) (a b d a' b' : Nat) : Type
  ≔ Σ (BookEquiv (Product (C .carrier) (Fin d)) (BlindCirclePullback C a b)) (e ↦
      (k : Fin d)
      → Product (Id (C .carrier → C .carrier) (z ↦ e .map (z, k) .fst .fst) (circle_degree_map C b'))
                (Id (C .carrier → C .carrier) (z ↦ e .map (z, k) .fst .snd) (circle_degree_map C a')))

def bp_square_at_gcd (C : CircleSignature) (a1 b1 a' b' : Nat)
  (ha : Id Nat (suc. a1) (mul (nat_gcd (suc. a1) (suc. b1)) a'))
  (hb : Id Nat (suc. b1) (mul (nat_gcd (suc. a1) (suc. b1)) b'))
  : bp_square_type C (suc. a1) (suc. b1) (nat_gcd (suc. a1) (suc. b1)) a' b'
  ≔ let S ≔ C .carrier in
    let E ≔ circle_pullback_explicit_decomposition C a1 b1 in
    (book_equivalence (Product S (Fin (nat_gcd (suc. a1) (suc. b1)))) (CirclePowerPullback C (suc. a1) (suc. b1)) (E .fst),
     k ↦ (concat (S → S) (z ↦ E .fst .map (z, k) .fst .fst) (circle_degree_map C (pbg_lcm_quotient_left a1 b1 .fst))
            (circle_degree_map C b')
            (circle_pullback_explicit_coordinates C a1 b1 k .fst)
            (refl (circle_degree_map C) (cpx_quotient_left_eq a1 b1 a' b' ha hb)),
          concat (S → S) (z ↦ E .fst .map (z, k) .fst .snd) (circle_degree_map C (pbg_lcm_quotient_right a1 b1 .fst))
            (circle_degree_map C a')
            (circle_pullback_explicit_coordinates C a1 b1 k .snd)
            (refl (circle_degree_map C) (cpx_quotient_right_eq a1 b1 a' b' ha hb))))

def bridge_ex_pullbackandgcd_square : blind_ex_pullbackandgcd_square
  ≔ C a b ↦ match a [
    | zero. ↦ d a' b' ha _ _ _ _ ↦ absurd (bp_square_type C zero. b d a' b') (ha (refl (zero. : Nat)))
    | suc. a1 ↦ match b [
      | zero. ↦ d a' b' _ hb _ _ _ ↦ absurd (bp_square_type C (suc. a1) zero. d a' b') (hb (refl (zero. : Nat)))
      | suc. b1 ↦ d a' b' _ _ hd ha' hb' ↦
          let G ≔ nat_gcd (suc. a1) (suc. b1) in
          transport Nat (x ↦ bp_square_type C (suc. a1) (suc. b1) x a' b') G d (inverse Nat d G hd)
            (bp_square_at_gcd C a1 b1 a' b'
              (concat Nat (suc. a1) (mul d a') (mul G a') ha' (refl ((x ↦ mul x a') : Nat → Nat) hd))
              (concat Nat (suc. b1) (mul d b') (mul G b') hb' (refl ((x ↦ mul x b') : Nat → Nat) hd))) ] ]

{` (3) Each component of P (the component of any u) is merely the lcm-fold covering. `}
def bp_lcm_type (C : CircleSignature) (a b : Nat) (u : BlindCirclePullback C a b) : Type
  ≔ Mere (Σ (BookEquiv (C .carrier) (NativeComponent (BlindCirclePullback C a b) u)) (e ↦
         Id (C .carrier → C .carrier) (z ↦ circle_degree_map C a (e .map z .fst .fst .fst))
           (circle_degree_map C (nat_lcm a b))))

def bp_lcm_at (C : CircleSignature) (a1 b1 : Nat) (u : CirclePowerPullback C (suc. a1) (suc. b1))
  : bp_lcm_type C (suc. a1) (suc. b1) u
  ≔ let S ≔ C .carrier in
    let P ≔ CirclePowerPullback C (suc. a1) (suc. b1) in
    let c ≔ set_trunc P u in
    let NC ≔ NativeComponent P u in
    let CC ≔ CplComponent C (suc. a1) (suc. b1) c in
    let F ≔ cpl_component_native_equiv P u c (refl c) in
    let T ≔ Σ (BookEquiv S NC) (e ↦ Id (S → S) (z ↦ circle_degree_map C (suc. a1) (e .map z .fst .fst .fst))
                (circle_degree_map C (nat_lcm (suc. a1) (suc. b1)))) in
    mere_rec (CplLcmCover C a1 b1 c) (Mere T) (mere_isprop T)
      (K ↦ let inv ≔ equiv_inverse_map NC CC F in
        mere T
          (book_equivalence S NC (compose_equiv S CC NC (native_equivalence S CC (K .fst)) (canonical_inverse_equiv NC CC F)),
           concat (S → S) (z ↦ circle_degree_map C (suc. a1) (inv (K .fst .map z) .fst .fst .fst))
             (z ↦ circle_degree_map C (suc. a1) (K .fst .map z .fst .fst .fst))
             (circle_degree_map C (nat_lcm (suc. a1) (suc. b1)))
             (funext S (_ ↦ S) (z ↦ circle_degree_map C (suc. a1) (inv (K .fst .map z) .fst .fst .fst))
               (z ↦ circle_degree_map C (suc. a1) (K .fst .map z .fst .fst .fst))
               (z ↦ refl ((v ↦ circle_degree_map C (suc. a1) (v .fst .fst)) : P → S)
                 (refl ((w ↦ w .fst) : CC → P) (equiv_counit NC CC F (K .fst .map z)))))
             (K .snd)))
      (circle_pullback_component_lcm_cover C a1 b1 c)

def bridge_ex_pullbackandgcd_lcm : blind_ex_pullbackandgcd_lcm
  ≔ C a b ↦ match a [
    | zero. ↦ ha _ u ↦ absurd (bp_lcm_type C zero. b u) (ha (refl (zero. : Nat)))
    | suc. a1 ↦ match b [
      | zero. ↦ _ hb u ↦ absurd (bp_lcm_type C (suc. a1) zero. u) (hb (refl (zero. : Nat)))
      | suc. b1 ↦ _ _ u ↦ bp_lcm_at C a1 b1 u ] ]
