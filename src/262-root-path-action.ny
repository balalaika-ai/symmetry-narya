export "261-circle-flip-conjugation"

{` The action of cdg_m on paths of cycles: the first projection of
   ap_{cdg_m}(e,!) is id × e. `}
def cycle_root_ap_evaluate (n : Nat) (c d : Cycles) (e : Id Cycles c d) (k : Fin (suc. n)) (x : c .fst .fst .fst)
  : Id (Product (Fin (suc. n)) (d .fst .fst .fst))
      (cycle_path_evaluate (cycle_root n c) (cycle_root n d) (refl (cycle_root n) e) (k, x))
      (k, cycle_path_evaluate c d e x)
  ≔ J Cycles c
      (d e ↦ Id (Product (Fin (suc. n)) (d .fst .fst .fst))
        (cycle_path_evaluate (cycle_root n c) (cycle_root n d) (refl (cycle_root n) e) (k, x))
        (k, cycle_path_evaluate c d e x))
      (concat (Product (Fin (suc. n)) (c .fst .fst .fst))
        (cycle_path_evaluate (cycle_root n c) (cycle_root n c) (refl (cycle_root n c)) (k, x))
        (k, x) (k, cycle_path_evaluate c c (refl c) x)
        (transport_refl Type (X ↦ X) (Product (Fin (suc. n)) (c .fst .fst .fst)) (k, x))
        (refl k, inverse (c .fst .fst .fst) (cycle_path_evaluate c c (refl c) x) x
          (transport_refl Type (X ↦ X) (c .fst .fst .fst) x)))
      d e

{` Paths of cycles are determined by their evaluation functions. `}
def cycle_paths_ext (c d : Cycles) (p q : Id Cycles c d)
  (h : (x : c .fst .fst .fst) → Id (d .fst .fst .fst) (cycle_path_evaluate c d p x) (cycle_path_evaluate c d q x))
  : Id (Id Cycles c d) p q
  ≔ let X ≔ c .fst .fst .fst in let Y ≔ d .fst .fst .fst in
    let I ≔ cycle_paths_equiv c d in
    equivalence_injective (Id Cycles c d) (PermutationIsomorphisms (c .fst) (d .fst)) I p q
      (subtype_equal (Equiv X Y) (e ↦ Commutes X Y (c .fst .snd) (d .fst .snd) (e .map))
        (e ↦ commutes_prop X Y (d .fst .fst .snd) (c .fst .snd) (d .fst .snd) (e .map))
        (I .map p) (I .map q)
        (equiv_path X Y (I .map p .fst) (I .map q .fst)
          (funext X (_ ↦ Y) (I .map p .fst .map) (I .map q .fst .map) h)))

{` The book's generating loop (t⁻¹, !) evaluates as t⁻¹. `}
def cycle_inverse_loop_evaluate (c : Cycles) (y : c .fst .fst .fst)
  : Id (c .fst .fst .fst)
      (cycle_path_evaluate c c (inverse Cycles c c (cycle_generating_loop c)) y)
      (equiv_inverse_map (c .fst .fst .fst) (c .fst .fst .fst) (c .fst .snd) y)
  ≔ let X ≔ c .fst .fst .fst in let e ≔ c .fst .snd in
    let g ≔ cycle_generating_loop c in
    let back ≔ ((u ↦ cycle_path_evaluate c c (inverse Cycles c c g) u) : X → X) in
    let y' ≔ equiv_inverse_map X X e y in
    calc
      back y = back (cycle_path_evaluate c c g y')
        by refl back (inverse X (cycle_path_evaluate c c g y') y
          (concat X (cycle_path_evaluate c c g y') (e .map y') y (cycle_generating_loop_action c y')
            (equiv_counit X X e y)))
      = y' by transport_inverse_roundtrip Cycles (d ↦ d .fst .fst .fst) c c g y' ∎

def cycle_loop_power_evaluate (c : Cycles) (l : Id Cycles c c) (m : Nat) (y : c .fst .fst .fst)
  : Id (c .fst .fst .fst) (cycle_path_evaluate c c (loop_power_nat Cycles c l m) y)
      (iterate (c .fst .fst .fst) (u ↦ cycle_path_evaluate c c l u) m y)
  ≔ match m [
  | zero. ↦ transport_refl Type (X ↦ X) (c .fst .fst .fst) y
  | suc. m ↦ concat (c .fst .fst .fst)
      (cycle_path_evaluate c c (concat Cycles c c c (loop_power_nat Cycles c l m) l) y)
      (cycle_path_evaluate c c l (cycle_path_evaluate c c (loop_power_nat Cycles c l m) y))
      (cycle_path_evaluate c c l (iterate (c .fst .fst .fst) (u ↦ cycle_path_evaluate c c l u) m y))
      (carrier_path_evaluate_concat Cycles (d ↦ d .fst .fst .fst) c c c (loop_power_nat Cycles c l m) l y)
      (refl (u ↦ cycle_path_evaluate c c l u) (cycle_loop_power_evaluate c l m y)) ]

{` The text after lem:deg-m-on-Cyc: ap_{cdg_m} of the generating loop
   (t⁻¹, !) of (X,t) is the m-th power of the generating loop ((ᵐ√t)⁻¹, !) of
   cdg_m(X,t), since (ᵐ√t)⁻ᵐ = id × t⁻¹; m = suc n. `}
def root_inverse_generator_power (n : Nat) (c : Cycles)
  : Id (Id Cycles (cycle_root n c) (cycle_root n c))
      (refl (cycle_root n) (inverse Cycles c c (cycle_generating_loop c)))
      (loop_power_nat Cycles (cycle_root n c) (inverse Cycles (cycle_root n c) (cycle_root n c)
        (cycle_generating_loop (cycle_root n c))) (suc. n))
  ≔ let X ≔ c .fst .fst .fst in let e ≔ c .fst .snd in
    let F ≔ Product (Fin (suc. n)) X in
    let r ≔ cycle_root n c in let R ≔ r .fst .snd in
    let G ≔ inverse Cycles r r (cycle_generating_loop r) in
    cycle_paths_ext r r (refl (cycle_root n) (inverse Cycles c c (cycle_generating_loop c))) (loop_power_nat Cycles r G (suc. n))
      (u ↦ calc
        cycle_path_evaluate r r (refl (cycle_root n) (inverse Cycles c c (cycle_generating_loop c))) u
        = (u .fst, cycle_path_evaluate c c (inverse Cycles c c (cycle_generating_loop c)) (u .snd))
          by cycle_root_ap_evaluate n c c (inverse Cycles c c (cycle_generating_loop c)) (u .fst) (u .snd)
        = (u .fst, equiv_inverse_map X X e (u .snd))
          by (refl (u .fst), cycle_inverse_loop_evaluate c (u .snd))
        = permutation_power F R (int_mul (pos. (suc. n)) (neg. zero.)) u
          by inverse F (permutation_power F R (int_mul (pos. (suc. n)) (neg. zero.)) u) (u .fst, equiv_inverse_map X X e (u .snd))
            (root_scaled_power n X e (neg. zero.) u)
        = iterate F (w ↦ cycle_path_evaluate r r G w) (suc. n) u
          by inverse F (iterate F (w ↦ cycle_path_evaluate r r G w) (suc. n) u)
            (iterate F (equiv_inverse_map F F R) (suc. n) u)
            (iterate_pointwise F (w ↦ cycle_path_evaluate r r G w) (equiv_inverse_map F F R)
              (cycle_inverse_loop_evaluate r) (suc. n) u)
        = cycle_path_evaluate r r (loop_power_nat Cycles r G (suc. n)) u
          by inverse F (cycle_path_evaluate r r (loop_power_nat Cycles r G (suc. n)) u)
            (iterate F (w ↦ cycle_path_evaluate r r G w) (suc. n) u)
            (cycle_loop_power_evaluate r G (suc. n) u) ∎)
