export "459-alternating-groups"

{` Chapter 4, sec:sign-homomorphism: the exercise at group.tex:1779 (there are
   n!/2 even permutations for n ≥ 2), the remark at group.tex:1741, the
   litmus that A_3 has 3 symmetries, and the counts of the introduction
   (8 directions of the complete graph on 3 elements, 2 classes). `}

def EvenPermutations (n : Nat) : Type
  ≔ Σ (Equiv (Fin n) (Fin n)) (s ↦ Id Sign (permutation_sign_at n (standard_shape n) s) plus.)

def OddPermutations (n : Nat) : Type
  ≔ Σ (Equiv (Fin n) (Fin n)) (s ↦ Id Sign (permutation_sign_at n (standard_shape n) s) minus.)

def sign_split (n : Nat) (s : Equiv (Fin n) (Fin n)) (t : Sign) (q : Id Sign (permutation_sign_at n (standard_shape n) s) t)
  : Sum (EvenPermutations n) (OddPermutations n)
  ≔ match t [ plus. ↦ inl. (s, q) | minus. ↦ inr. (s, q) ]

def even_odd_sum_fst (n : Nat) : Sum (EvenPermutations n) (OddPermutations n) → Equiv (Fin n) (Fin n)
  ≔ [ inl. u ↦ u .fst | inr. u ↦ u .fst ]

def sign_split_fst (n : Nat) (s : Equiv (Fin n) (Fin n)) (t : Sign) (q : Id Sign (permutation_sign_at n (standard_shape n) s) t)
  : Id (Equiv (Fin n) (Fin n)) (even_odd_sum_fst n (sign_split n s t q)) s
  ≔ match t [ plus. ↦ refl s | minus. ↦ refl s ]

def sign_split_even (n : Nat) (u : EvenPermutations n) (t : Sign) (q : Id Sign (permutation_sign_at n (standard_shape n) (u .fst)) t)
  : Id (Sum (EvenPermutations n) (OddPermutations n)) (sign_split n (u .fst) t q) (inl. u)
  ≔ match t [
  | plus. ↦ inl. (subtype_equal (Equiv (Fin n) (Fin n)) (s ↦ Id Sign (permutation_sign_at n (standard_shape n) s) plus.)
      (s ↦ sign_set (permutation_sign_at n (standard_shape n) s) plus.) (u .fst, q) u (refl (u .fst)))
  | minus. ↦ match plus_ne_minus (concat Sign plus. (permutation_sign_at n (standard_shape n) (u .fst)) minus.
      (inverse Sign (permutation_sign_at n (standard_shape n) (u .fst)) plus. (u .snd)) q) [] ]

def sign_split_odd (n : Nat) (u : OddPermutations n) (t : Sign) (q : Id Sign (permutation_sign_at n (standard_shape n) (u .fst)) t)
  : Id (Sum (EvenPermutations n) (OddPermutations n)) (sign_split n (u .fst) t q) (inr. u)
  ≔ match t [
  | minus. ↦ inr. (subtype_equal (Equiv (Fin n) (Fin n)) (s ↦ Id Sign (permutation_sign_at n (standard_shape n) s) minus.)
      (s ↦ sign_set (permutation_sign_at n (standard_shape n) s) minus.) (u .fst, q) u (refl (u .fst)))
  | plus. ↦ match plus_ne_minus (concat Sign plus. (permutation_sign_at n (standard_shape n) (u .fst)) minus.
      (inverse Sign (permutation_sign_at n (standard_shape n) (u .fst)) plus. q) (u .snd)) [] ]

def permutations_even_odd_equiv (n : Nat) : Equiv (Equiv (Fin n) (Fin n)) (Sum (EvenPermutations n) (OddPermutations n))
  ≔ quasi_inverse_equiv (Equiv (Fin n) (Fin n)) (Sum (EvenPermutations n) (OddPermutations n))
      (s ↦ sign_split n s (permutation_sign_at n (standard_shape n) s) (refl (permutation_sign_at n (standard_shape n) s)))
      (even_odd_sum_fst n)
      (s ↦ sign_split_fst n s (permutation_sign_at n (standard_shape n) s) (refl (permutation_sign_at n (standard_shape n) s)))
      [ inl. u ↦ sign_split_even n u (permutation_sign_at n (standard_shape n) (u .fst)) (refl (permutation_sign_at n (standard_shape n) (u .fst)))
      | inr. u ↦ sign_split_odd n u (permutation_sign_at n (standard_shape n) (u .fst)) (refl (permutation_sign_at n (standard_shape n) (u .fst))) ]

{` Composing with the transposition (0 1) exchanges even and odd permutations. `}
def fin_swap01_sign (m : Nat)
  : Id Sign (permutation_sign_at (suc. (suc. m)) (standard_shape (suc. (suc. m))) (fin_swap01_equiv m)) minus.
  ≔ concat Sign (permutation_sign_at (suc. (suc. m)) (standard_shape (suc. (suc. m))) (fin_swap01_equiv m))
      (sigma_two_sign (usgn (suc. (suc. m)) (permutation_symmetry (standard_set (suc. (suc. m))) (fin_swap01_equiv m)))) minus.
      (permutation_sign_standard m (fin_swap01_equiv m)) (usgn_swap01 m)

def swap01_times (m : Nat) (s : Equiv (Fin (suc. (suc. m))) (Fin (suc. (suc. m)))) : Equiv (Fin (suc. (suc. m))) (Fin (suc. (suc. m)))
  ≔ compose_equiv (Fin (suc. (suc. m))) (Fin (suc. (suc. m))) (Fin (suc. (suc. m))) (fin_swap01_equiv m) s

def swap01_times_sign (m : Nat) (s : Equiv (Fin (suc. (suc. m))) (Fin (suc. (suc. m)))) (t : Sign)
  (q : Id Sign (permutation_sign_at (suc. (suc. m)) (standard_shape (suc. (suc. m))) s) t)
  : Id Sign (permutation_sign_at (suc. (suc. m)) (standard_shape (suc. (suc. m))) (swap01_times m s)) (sign_mul t minus.)
  ≔ let n : Nat ≔ suc. (suc. m) in
    concat Sign (permutation_sign_at n (standard_shape n) (swap01_times m s))
      (sign_mul (permutation_sign_at n (standard_shape n) s) (permutation_sign_at n (standard_shape n) (fin_swap01_equiv m)))
      (sign_mul t minus.)
      (permutation_sign_at_compose n (standard_shape n) (fin_swap01_equiv m) s)
      (refl sign_mul q (fin_swap01_sign m))

def swap01_times_twice (m : Nat) (s : Equiv (Fin (suc. (suc. m))) (Fin (suc. (suc. m))))
  : Id (Equiv (Fin (suc. (suc. m))) (Fin (suc. (suc. m)))) (swap01_times m (swap01_times m s)) s
  ≔ equiv_homotopy (Fin (suc. (suc. m))) (Fin (suc. (suc. m))) (swap01_times m (swap01_times m s)) s
      (x ↦ refl (s .map) (fin_swap01_involutive m x))

def even_odd_equiv (m : Nat) : Equiv (EvenPermutations (suc. (suc. m))) (OddPermutations (suc. (suc. m)))
  ≔ let n : Nat ≔ suc. (suc. m) in
    let S : Sign → Type ≔ t ↦ Σ (Equiv (Fin n) (Fin n)) (s ↦ Id Sign (permutation_sign_at n (standard_shape n) s) t) in
    quasi_inverse_equiv (EvenPermutations n) (OddPermutations n)
      (u ↦ (swap01_times m (u .fst), swap01_times_sign m (u .fst) plus. (u .snd)))
      (v ↦ (swap01_times m (v .fst), swap01_times_sign m (v .fst) minus. (v .snd)))
      (u ↦ subtype_equal (Equiv (Fin n) (Fin n)) (s ↦ Id Sign (permutation_sign_at n (standard_shape n) s) plus.)
        (s ↦ sign_set (permutation_sign_at n (standard_shape n) s) plus.)
        (swap01_times m (swap01_times m (u .fst)), swap01_times_sign m (swap01_times m (u .fst)) minus. (swap01_times_sign m (u .fst) plus. (u .snd)))
        u (swap01_times_twice m (u .fst)))
      (v ↦ subtype_equal (Equiv (Fin n) (Fin n)) (s ↦ Id Sign (permutation_sign_at n (standard_shape n) s) minus.)
        (s ↦ sign_set (permutation_sign_at n (standard_shape n) s) minus.)
        (swap01_times m (swap01_times m (v .fst)), swap01_times_sign m (swap01_times m (v .fst)) plus. (swap01_times_sign m (v .fst) minus. (v .snd)))
        v (swap01_times_twice m (v .fst)))

def sign_decide (s t : Sign) : Decidable (Id Sign s t)
  ≔ match s, t [
  | plus., plus. ↦ inl. (refl (plus. : Sign))
  | minus., minus. ↦ inl. (refl (minus. : Sign))
  | plus., minus. ↦ inr. plus_ne_minus
  | minus., plus. ↦ inr. (p ↦ plus_ne_minus (inverse Sign minus. plus. p)) ]

def fin_permutations_finite (n : Nat) : IsFinite (Equiv (Fin n) (Fin n))
  ≔ finite_from_equiv (Equiv (Fin n) (Fin n)) (factorial n) (fin_automorphisms_equiv n)

def signed_permutations_finite (n : Nat) (t : Sign)
  : IsFinite (Σ (Equiv (Fin n) (Fin n)) (s ↦ Id Sign (permutation_sign_at n (standard_shape n) s) t))
  ≔ finite_decidable_subset (Equiv (Fin n) (Fin n)) (fin_permutations_finite n)
      (s ↦ Id Sign (permutation_sign_at n (standard_shape n) s) t)
      (s ↦ sign_set (permutation_sign_at n (standard_shape n) s) t)
      (s ↦ sign_decide (permutation_sign_at n (standard_shape n) s) t)

def even_permutations_count (n : Nat) : Nat ≔ cardinality (EvenPermutations n) (signed_permutations_finite n plus.)

{` Exercise (group.tex:1779): 2 · #even = n!, i.e. there are n!/2 even
   permutations of an n-element set, n ≥ 2. `}
def even_permutations_half (m : Nat)
  : Id Nat (add (even_permutations_count (suc. (suc. m))) (even_permutations_count (suc. (suc. m)))) (factorial (suc. (suc. m)))
  ≔ let n : Nat ≔ suc. (suc. m) in
    let hE ≔ signed_permutations_finite n plus. in let hO ≔ signed_permutations_finite n minus. in
    let hS ≔ finite_sum (EvenPermutations n) (OddPermutations n) hE hO in
    calc add (even_permutations_count n) (even_permutations_count n)
      = add (even_permutations_count n) (cardinality (OddPermutations n) hO)
        by refl (add (even_permutations_count n)) (cardinality_equiv (EvenPermutations n) (OddPermutations n) (even_odd_equiv m) hE hO)
      = cardinality (Sum (EvenPermutations n) (OddPermutations n)) hS
        by inverse Nat (cardinality (Sum (EvenPermutations n) (OddPermutations n)) hS)
          (add (even_permutations_count n) (cardinality (OddPermutations n) hO))
          (cardinality_sum (EvenPermutations n) (OddPermutations n) hE hO hS)
      = cardinality (Equiv (Fin n) (Fin n)) (fin_permutations_finite n)
        by cardinality_equiv (Sum (EvenPermutations n) (OddPermutations n)) (Equiv (Fin n) (Fin n))
          (canonical_inverse_equiv (Equiv (Fin n) (Fin n)) (Sum (EvenPermutations n) (OddPermutations n)) (permutations_even_odd_equiv n))
          hS (fin_permutations_finite n)
      = factorial n
        by cardinality_from_path (Equiv (Fin n) (Fin n)) (fin_permutations_finite n) (factorial n)
          (ua (Equiv (Fin n) (Fin n)) (Fin (factorial n)) (fin_automorphisms_equiv n)) ∎

{` Even permutations are the even symmetries of Σ_n, hence the symmetries of
   A_n; litmus: A_3 has exactly 3 symmetries. `}
def even_permutations_symmetries_equiv (m : Nat) : Equiv (EvenPermutations (suc. (suc. m))) (EvenSymmetries (suc. (suc. m)))
  ≔ let n : Nat ≔ suc. (suc. m) in
    let tq : (s : USym (symmetric_group n)) → Equiv (Fin n) (Fin n) ≔ s ↦ transport_equiv (Fin n) (Fin n) (s .fst .fst) in
    let back : (s : USym (symmetric_group n)) → Id (USym (symmetric_group n)) (permutation_symmetry (standard_set n) (tq s)) s
      ≔ s ↦ bsigma_path_ext n (standard_shape n) (standard_shape n) (permutation_symmetry (standard_set n) (tq s)) s (x ↦ refl (s .fst .fst .trr x)) in
    let f : EvenPermutations n → EvenSymmetries n
      ≔ u ↦ (permutation_symmetry (standard_set n) (u .fst),
        concat Sign (sigma_two_sign (usgn n (permutation_symmetry (standard_set n) (u .fst))))
          (permutation_sign_at n (standard_shape n) (u .fst)) plus.
          (inverse Sign (permutation_sign_at n (standard_shape n) (u .fst)) (sigma_two_sign (usgn n (permutation_symmetry (standard_set n) (u .fst))))
            (permutation_sign_standard m (u .fst))) (u .snd)) in
    let g : EvenSymmetries n → EvenPermutations n
      ≔ v ↦ (tq (v .fst),
        calc permutation_sign_at n (standard_shape n) (tq (v .fst))
          = sigma_two_sign (usgn n (permutation_symmetry (standard_set n) (tq (v .fst)))) by permutation_sign_standard m (tq (v .fst))
          = sigma_two_sign (usgn n (v .fst)) by refl ((s ↦ sigma_two_sign (usgn n s)) : USym (symmetric_group n) → Sign) (back (v .fst))
          = plus. by v .snd ∎) in
    quasi_inverse_equiv (EvenPermutations n) (EvenSymmetries n) f g
      (u ↦ subtype_equal (Equiv (Fin n) (Fin n)) (s ↦ Id Sign (permutation_sign_at n (standard_shape n) s) plus.)
        (s ↦ sign_set (permutation_sign_at n (standard_shape n) s) plus.) (g (f u)) u
        (equiv_homotopy (Fin n) (Fin n) (tq (permutation_symmetry (standard_set n) (u .fst))) (u .fst) (x ↦ refl (u .fst .map x))))
      (v ↦ subtype_equal (USym (symmetric_group n)) (s ↦ Id Sign (sigma_two_sign (usgn n s)) plus.)
        (s ↦ sign_set (sigma_two_sign (usgn n s)) plus.) (f (g v)) v (back (v .fst)))

def alternating_three_usym_even : Equiv (USym (alternating_group_printed (suc. zero.))) (EvenPermutations three)
  ≔ compose_equiv (USym (alternating_group_printed (suc. zero.))) (EvenSymmetries three) (EvenPermutations three)
      (alternating_usym_even (suc. zero.))
      (canonical_inverse_equiv (EvenPermutations three) (EvenSymmetries three) (even_permutations_symmetries_equiv (suc. zero.)))

def even_permutations_three : Id Nat (even_permutations_count three) three
  ≔ nat_double_injective (even_permutations_count three) three (even_permutations_half (suc. zero.))

def alternating_three_finite : IsFiniteGroup (alternating_group_printed (suc. zero.))
  ≔ finite_of_equiv (USym (alternating_group_printed (suc. zero.))) (EvenPermutations three) alternating_three_usym_even
      (signed_permutations_finite three plus.)

def alternating_three_card : Id Nat (group_card (alternating_group_printed (suc. zero.)) alternating_three_finite) three
  ≔ concat Nat (group_card (alternating_group_printed (suc. zero.)) alternating_three_finite) (even_permutations_count three) three
      (cardinality_equiv (USym (alternating_group_printed (suc. zero.))) (EvenPermutations three) alternating_three_usym_even
        alternating_three_finite (signed_permutations_finite three plus.))
      even_permutations_three

{` Remark (group.tex:1741). The number of inversions depends on the linear
   order, the sign does not: relabeling Fin 3 by ρ = (1 2) turns (0 2), with 3
   inversions, into (0 1), with 1 inversion; in general the sign of a
   relabeled permutation ρσρ⁻¹ equals that of σ. Composition ("pulling the
   strings taut") preserves the parity of the number of crossings. `}
def fin3_swap02 : Fin three → Fin three ≔ [
  | inr. u ↦ inl. (inl. (inr. u))
  | inl. (inr. u) ↦ inl. (inr. u)
  | inl. (inl. (inr. u)) ↦ inr. u
  | inl. (inl. (inl. e)) ↦ match e [] ]

def fin3_swap02_involutive (x : Fin three) : Id (Fin three) (fin3_swap02 (fin3_swap02 x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin three)
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin three)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin three)
  | inl. (inl. (inl. e)) ↦ match e [] ]

def fin3_swap02_equiv : Equiv (Fin three) (Fin three)
  ≔ quasi_inverse_equiv (Fin three) (Fin three) fin3_swap02 fin3_swap02 fin3_swap02_involutive fin3_swap02_involutive

def inversions_swap02 : Id Nat (inversion_number three fin3_swap02_equiv) three ≔ refl three

def inversions_swap01_relabeled : Id Nat (inversion_number three fin3_swap01_equiv) (suc. zero.) ≔ refl (suc. zero. : Nat)

{` (1 2)(0 2)(1 2) = (0 1), pointwise. `}
def relabel_swap02 (x : Fin three) : Id (Fin three) (fin3_swap12 (fin3_swap02 (fin3_swap12 x))) (fin3_swap01 x)
  ≔ match x [
  | inr. u ↦ refl (inl. (inr. u) : Fin three)
  | inl. (inr. u) ↦ refl (inr. u : Fin three)
  | inl. (inl. (inr. u)) ↦ refl (inl. (inl. (inr. u)) : Fin three)
  | inl. (inl. (inl. e)) ↦ match e [] ]

def sign_independent_of_ordering (n : Nat) (r s : Equiv (Fin n) (Fin n))
  : Id Sign (permutation_sign_at n (standard_shape n) s)
      (permutation_sign_at n (standard_shape n) (conjugate_permutation (Fin n) (Fin n)
        (bsigma_two_transport_n n (standard_shape n) (standard_shape n) (permutation_loop n (standard_shape n) r)) s))
  ≔ permutation_sign_at_transport n (standard_shape n) (standard_shape n) (permutation_loop n (standard_shape n) r) s

def inversion_parity_independent (n : Nat) (r s : Equiv (Fin n) (Fin n))
  : Id Bool (nat_odd (inversion_count n s))
      (nat_odd (inversion_count n (conjugate_permutation (Fin n) (Fin n)
        (bsigma_two_transport_n n (standard_shape n) (standard_shape n) (permutation_loop n (standard_shape n) r)) s)))
  ≔ let c ≔ conjugate_permutation (Fin n) (Fin n)
        (bsigma_two_transport_n n (standard_shape n) (standard_shape n) (permutation_loop n (standard_shape n) r)) s in
    bool_sign_injective (nat_odd (inversion_count n s)) (nat_odd (inversion_count n c))
      (calc bool_sign (nat_odd (inversion_count n s))
        = permutation_sign_at n (standard_shape n) s
          by inverse Sign (permutation_sign_at n (standard_shape n) s) (bool_sign (nat_odd (inversion_count n s)))
            (permutation_sign_at_inversions n s)
        = permutation_sign_at n (standard_shape n) c by sign_independent_of_ordering n r s
        = bool_sign (nat_odd (inversion_count n c)) by permutation_sign_at_inversions n c ∎)

def crossings_parity_compose (n : Nat) (s t : Equiv (Fin n) (Fin n))
  : Id Bool (nat_odd (inversion_count n (compose_equiv (Fin n) (Fin n) (Fin n) s t)))
      (bool_xor (nat_odd (inversion_count n t)) (nat_odd (inversion_count n s)))
  ≔ let st ≔ compose_equiv (Fin n) (Fin n) (Fin n) s t in
    bool_sign_injective (nat_odd (inversion_count n st)) (bool_xor (nat_odd (inversion_count n t)) (nat_odd (inversion_count n s)))
      (calc bool_sign (nat_odd (inversion_count n st))
        = permutation_sign_at n (standard_shape n) st
          by inverse Sign (permutation_sign_at n (standard_shape n) st) (bool_sign (nat_odd (inversion_count n st)))
            (permutation_sign_at_inversions n st)
        = sign_mul (permutation_sign_at n (standard_shape n) t) (permutation_sign_at n (standard_shape n) s)
          by permutation_sign_at_compose n (standard_shape n) s t
        = sign_mul (bool_sign (nat_odd (inversion_count n t))) (bool_sign (nat_odd (inversion_count n s)))
          by refl sign_mul (permutation_sign_at_inversions n t) (permutation_sign_at_inversions n s)
        = bool_sign (bool_xor (nat_odd (inversion_count n t)) (nat_odd (inversion_count n s)))
          by inverse Sign (bool_sign (bool_xor (nat_odd (inversion_count n t)) (nat_odd (inversion_count n s))))
            (sign_mul (bool_sign (nat_odd (inversion_count n t))) (bool_sign (nat_odd (inversion_count n s))))
            (bool_sign_xor (nat_odd (inversion_count n t)) (nat_odd (inversion_count n s))) ∎)

{` The figure: (1 2)(1 2) = id_2 with first two, then no crossings. `}
def fin_two_swap_twice_inversions
  : Id Nat (add (inversion_number two (fin_swap01_equiv zero.)) (inversion_number two (fin_swap01_equiv zero.))) two
  ≔ refl two

def fin_two_identity_inversions : Id Nat (inversion_number two (identity_equiv (Fin two))) zero. ≔ refl (zero. : Nat)

{` Introduction: the complete graph on a 3-element set has 8 directions
   (local orderings), falling into 2 classes (sign orderings). `}
def two_power (k : Nat) : Nat ≔ match k [ zero. ↦ suc. zero. | suc. j ↦ mul (two_power j) two ]

def fin_functions_cons (k : Nat) (B : Type) (gb : Product (Fin k → B) B) (x : Fin (suc. k)) : B
  ≔ match x [ inl. a ↦ gb .fst a | inr. _ ↦ gb .snd ]

def fin_functions_cons_eta (k : Nat) (B : Type) (f : Fin (suc. k) → B) (x : Fin (suc. k))
  : Id B (fin_functions_cons k B (a ↦ f (inl. a), f (inr. star.)) x) (f x)
  ≔ match x [
  | inl. a ↦ refl (f (inl. a))
  | inr. u ↦ refl f (inr. (unit_prop star. u) : Id (Fin (suc. k)) (inr. star.) (inr. u)) ]

def fin_functions_split (k : Nat) (B : Type) : Equiv (Fin (suc. k) → B) (Product (Fin k → B) B)
  ≔ quasi_inverse_equiv (Fin (suc. k) → B) (Product (Fin k → B) B)
      (f ↦ (a ↦ f (inl. a), f (inr. star.)))
      (gb ↦ x ↦ fin_functions_cons k B gb x)
      (f ↦ funext (Fin (suc. k)) (_ ↦ B) (x ↦ fin_functions_cons k B (a ↦ f (inl. a), f (inr. star.)) x) f
        (x ↦ fin_functions_cons_eta k B f x))
      (gb ↦ refl gb)

def product_equiv_left (A A' B : Type) (e : Equiv A A') : Equiv (Product A B) (Product A' B)
  ≔ quasi_inverse_equiv (Product A B) (Product A' B) (u ↦ (e .map (u .fst), u .snd))
      (v ↦ (equiv_inverse_map A A' e (v .fst), v .snd))
      (u ↦ (equiv_retraction A A' e (u .fst), refl (u .snd)))
      (v ↦ (equiv_counit A A' e (v .fst), refl (v .snd)))

def fin_functions_two_equiv (k : Nat) : Equiv (Fin k → Fin two) (Fin (two_power k))
  ≔ match k [
  | zero. ↦ quasi_inverse_equiv (Fin zero. → Fin two) (Fin (suc. zero.)) (_ ↦ inr. star.) (_ x ↦ absurd (Fin two) x)
      (f ↦ funext (Fin zero.) (_ ↦ Fin two) (x ↦ absurd (Fin two) x) f (x ↦ match x []))
      [ inl. e ↦ match e [] | inr. u ↦ inr. (unit_prop star. u) ]
  | suc. j ↦ compose_equiv (Fin (suc. j) → Fin two) (Product (Fin j → Fin two) (Fin two)) (Fin (two_power (suc. j)))
      (fin_functions_split j (Fin two))
      (compose_equiv (Product (Fin j → Fin two) (Fin two)) (Product (Fin (two_power j)) (Fin two)) (Fin (two_power (suc. j)))
        (product_equiv_left (Fin j → Fin two) (Fin (two_power j)) (Fin two) (fin_functions_two_equiv j))
        (fin_product_equiv (two_power j) two)) ]

def directions_count_eight : Nat ≔ two_power three

def local_orderings_fin_three_path : Mere (Id Type (LocalOrderings (Fin three) (fin_set three)) (Fin directions_count_eight))
  ≔ let E ≔ TwoSubsets (Fin three) in
    let C : E → Type ≔ e ↦ SubtypeCarrier (Fin three) (e .fst) in
    trunc_map native_truncation ((e : E) → Id Type (C e) (Fin two)) (Id Type (LocalOrderings (Fin three) (fin_set three)) (Fin directions_count_eight))
      (h ↦ calc LocalOrderings (Fin three) (fin_set three)
          = (E → Fin two) by refl ((F ↦ (e : E) → F e) : (E → Type) → Type) (funext E (_ ↦ Type) C (_ ↦ Fin two) h)
          = (Fin three → Fin two) by refl ((X ↦ X → Fin two) : Type → Type) (ua E (Fin three) (ksubsets_fin_equiv three two))
          = Fin directions_count_eight by ua (Fin three → Fin two) (Fin directions_count_eight) (fin_functions_two_equiv three) ∎)
      (finite_choice E (ksubsets_finite (Fin three) (fin_is_finite three) two) (e ↦ Id Type (C e) (Fin two)) (e ↦ e .snd))

def local_orderings_fin_three_finite : IsFinite (LocalOrderings (Fin three) (fin_set three))
  ≔ trunc_map native_truncation (Id Type (LocalOrderings (Fin three) (fin_set three)) (Fin directions_count_eight))
      (Σ Nat (k ↦ Id Type (LocalOrderings (Fin three) (fin_set three)) (Fin k))) (p ↦ (directions_count_eight, p)) local_orderings_fin_three_path

def local_orderings_fin_three_card : Id Nat (cardinality (LocalOrderings (Fin three) (fin_set three)) local_orderings_fin_three_finite) directions_count_eight
  ≔ mere_rec (Id Type (LocalOrderings (Fin three) (fin_set three)) (Fin directions_count_eight))
      (Id Nat (cardinality (LocalOrderings (Fin three) (fin_set three)) local_orderings_fin_three_finite) directions_count_eight)
      (nat_set (cardinality (LocalOrderings (Fin three) (fin_set three)) local_orderings_fin_three_finite) directions_count_eight)
      (p ↦ cardinality_from_path (LocalOrderings (Fin three) (fin_set three)) local_orderings_fin_three_finite directions_count_eight p)
      local_orderings_fin_three_path

def sign_orderings_fin_three_two_element
  : TwoElement (SignOrderings (Fin three) (fin_set three) (fin_is_finite three))
  ≔ parity_quotient_two_element (TwoSubsets (Fin three)) (ksubsets_finite (Fin three) (fin_is_finite three) two)
      (two_subset_bsigma (Fin three) (fin_set three)) (mere (TwoSubsets (Fin three)) fin_three_pair_zero_one)
