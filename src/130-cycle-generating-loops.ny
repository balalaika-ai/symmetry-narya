export "129-pointed-circle-universal-property"

def cycle_generating_loop (c : Cycles) : Id Cycles c c
  ≔ equiv_inverse_map (Id Cycles c c) (PermutationIsomorphisms (c .fst) (c .fst))
      (cycle_paths_equiv c c) (c .fst .snd, x ↦ refl (c .fst .snd .map (c .fst .snd .map x)))

def evaluation_of_inverse_beta (A B X : Type) (e : Equiv A B) (v : B → X) (b : B)
  : Id X (v (e .map (equiv_inverse_map A B e b))) (v b)
  ≔ refl v (equiv_counit A B e b)

def cycle_generating_loop_action (c : Cycles) (x : c .fst .fst .fst)
  : Id (c .fst .fst .fst) (cycle_path_evaluate c c (cycle_generating_loop c) x) (c .fst .snd .map x)
  ≔ evaluation_of_inverse_beta (Id Cycles c c) (PermutationIsomorphisms (c .fst) (c .fst))
      (c .fst .fst .fst) (cycle_paths_equiv c c)
      (h ↦ h .fst .map x) (c .fst .snd, y ↦ refl (c .fst .snd .map (c .fst .snd .map y)))

def cycle_path_evaluation_concat (c d e : Cycles) (p : Id Cycles c d) (q : Id Cycles d e)
  (x : c .fst .fst .fst)
  : Id (e .fst .fst .fst) (cycle_path_evaluate c e (concat Cycles c d e p q) x)
      (cycle_path_evaluate d e q (cycle_path_evaluate c d p x))
  ≔ carrier_path_evaluate_concat Cycles (c ↦ c .fst .fst .fst) c d e p q x

def cycle_evaluation_generator_right (c : Cycles) (x : c .fst .fst .fst) (p : Id Cycles c c)
  : Id (c .fst .fst .fst)
      (cycle_path_evaluate c c (concat Cycles c c c p (cycle_generating_loop c)) x)
      (c .fst .snd .map (cycle_path_evaluate c c p x))
  ≔ concat (c .fst .fst .fst)
      (cycle_path_evaluate c c (concat Cycles c c c p (cycle_generating_loop c)) x)
      (cycle_path_evaluate c c (cycle_generating_loop c) (cycle_path_evaluate c c p x))
      (c .fst .snd .map (cycle_path_evaluate c c p x))
      (cycle_path_evaluation_concat c c c p (cycle_generating_loop c) x)
      (cycle_generating_loop_action c (cycle_path_evaluate c c p x))

def cycle_evaluation_generator_left (c : Cycles) (x : c .fst .fst .fst) (p : Id Cycles c c)
  : Id (c .fst .fst .fst)
      (cycle_path_evaluate c c (concat Cycles c c c (cycle_generating_loop c) p) x)
      (c .fst .snd .map (cycle_path_evaluate c c p x))
  ≔ calc
      cycle_path_evaluate c c (concat Cycles c c c (cycle_generating_loop c) p) x
      = cycle_path_evaluate c c p (cycle_path_evaluate c c (cycle_generating_loop c) x)
        by cycle_path_evaluation_concat c c c (cycle_generating_loop c) p x
      = cycle_path_evaluate c c p (c .fst .snd .map x)
        by refl (cycle_path_evaluate c c p) (cycle_generating_loop_action c x)
      = c .fst .snd .map (cycle_path_evaluate c c p x)
        by cycle_paths_equiv c c .map p .snd x ∎

{` The finite standard cycle on the literal Fin(suc n), with zero in
   its right-hand unit summand, as in fin_book_below_equiv. `}
def finite_fin_successor (n : Nat) : Equiv (Fin (suc. n)) (Fin (suc. n))
  ≔ compose_equiv (Fin (suc. n)) (Remainder (suc. n)) (Fin (suc. n))
      (compose_equiv (Fin (suc. n)) (Remainder (suc. n)) (Remainder (suc. n))
        (fin_book_below_equiv (suc. n)) (modular_successor_equiv n))
      (canonical_inverse_equiv (Fin (suc. n)) (Remainder (suc. n)) (fin_book_below_equiv (suc. n)))

def finite_fin_successor_cyclic (n : Nat) : Cyclic (Fin (suc. n)) (finite_fin_successor n)
  ≔ let e ≔ fin_book_below_equiv (suc. n) in let g ≔ equiv_inverse_map (Fin (suc. n)) (Remainder (suc. n)) e in
    cyclic_transfer (Remainder (suc. n)) (Fin (suc. n)) (modular_successor_equiv n) (finite_fin_successor n)
      (canonical_inverse_equiv (Fin (suc. n)) (Remainder (suc. n)) e)
      (r ↦ inverse (Fin (suc. n)) (g (modular_successor n (e .map (g r)))) (g (modular_successor n r))
        (refl ((s ↦ g (modular_successor n s)) : Remainder (suc. n) → Fin (suc. n))
          (equiv_counit (Fin (suc. n)) (Remainder (suc. n)) e r))) (modular_successor_cyclic n)

def finite_fin_cycle (n : Nat) : Cycles
  ≔ (((Fin (suc. n), fin_set (suc. n)), finite_fin_successor n), finite_fin_successor_cyclic n)

{` cor:id-m-cycle. Evaluation is literal transport of zero, and both
   left and right composition with the successor loop are checked above. `}
def finite_cycle_loop_equiv (n : Nat) : BookEquiv (Id Cycles (finite_fin_cycle n) (finite_fin_cycle n)) (Fin (suc. n))
  ≔ cycle_automorphisms_evaluation (finite_fin_cycle n) (inr. star.)

def finite_cycle_loop_refl (n : Nat)
  : Id (Fin (suc. n)) (finite_cycle_loop_equiv n .map (refl (finite_fin_cycle n))) (inr. star.)
  ≔ cycle_automorphisms_identity_beta (finite_fin_cycle n) (inr. star.)

def finite_cycle_loop_successor_right (n : Nat) (p : Id Cycles (finite_fin_cycle n) (finite_fin_cycle n))
  : Id (Fin (suc. n)) (finite_cycle_loop_equiv n .map
      (concat Cycles (finite_fin_cycle n) (finite_fin_cycle n) (finite_fin_cycle n) p (cycle_generating_loop (finite_fin_cycle n))))
      (finite_fin_successor n .map (finite_cycle_loop_equiv n .map p))
  ≔ cycle_evaluation_generator_right (finite_fin_cycle n) (inr. star.) p

def finite_cycle_loop_successor_left (n : Nat) (p : Id Cycles (finite_fin_cycle n) (finite_fin_cycle n))
  : Id (Fin (suc. n)) (finite_cycle_loop_equiv n .map
      (concat Cycles (finite_fin_cycle n) (finite_fin_cycle n) (finite_fin_cycle n) (cycle_generating_loop (finite_fin_cycle n)) p))
      (finite_fin_successor n .map (finite_cycle_loop_equiv n .map p))
  ≔ cycle_evaluation_generator_left (finite_fin_cycle n) (inr. star.) p
