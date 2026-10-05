export "456-sign-inversions"

{` Chapter 4, sec:sign-homomorphism: def:sgn-permutation and the prose around
   it. The sign of a permutation σ of a finite set A: +1 if Card A ≤ 1, and
   otherwise ±1 according to whether Bsgn÷(σ) swaps the two elements of
   Bsgn÷(A). A is regarded as a point of BΣ_n, n = Card A, and σ as the loop
   ua(σ) at A. `}

def permutation_loop (n : Nat) (A : BookFiniteSetsAt n) (s : Equiv (A .fst .fst) (A .fst .fst)) : Id (BookFiniteSetsAt n) A A
  ≔ component_path SetTypes (Fin n, fin_set n) A A (set_types_path (A .fst) (A .fst) s)

def permutation_sign_at (n : Nat) : (A : BookFiniteSetsAt n) → Equiv (A .fst .fst) (A .fst .fst) → Sign
  ≔ match n [
  | zero. ↦ _ _ ↦ plus.
  | suc. zero. ↦ _ _ ↦ plus.
  | suc. (suc. m) ↦ A s ↦ two_loop_sign (bsgn (suc. (suc. m)) A) (refl (bsgn (suc. (suc. m))) (permutation_loop (suc. (suc. m)) A s)) ]

{` A finite set as a point of BΣ_{Card A}. `}
def finite_set_point (A : FiniteSets) : BookFiniteSetsAt (Card A)
  ≔ (A .fst, trunc_map native_truncation (Id Type (A .fst .fst) (Fin (Card A))) (Id SetTypes (Fin (Card A), fin_set (Card A)) (A .fst))
      (p ↦ subtype_equal Type isSet isset_isprop (Fin (Card A), fin_set (Card A)) (A .fst) (inverse Type (A .fst .fst) (Fin (Card A)) p))
      (cardinality_spec (A .fst .fst) (A .snd)))

{` def:sgn-permutation. `}
def permutation_sign (A : FiniteSets) (s : Equiv (A .fst .fst) (A .fst .fst)) : Sign
  ≔ permutation_sign_at (Card A) (finite_set_point A) s

def IsEvenPermutation (A : FiniteSets) (s : Equiv (A .fst .fst) (A .fst .fst)) : Type ≔ Id Sign (permutation_sign A s) plus.

{` The sign only depends on the underlying function. `}
def permutation_sign_at_homotopy (n : Nat) (A : BookFiniteSetsAt n) (s t : Equiv (A .fst .fst) (A .fst .fst))
  (h : (x : A .fst .fst) → Id (A .fst .fst) (s .map x) (t .map x))
  : Id Sign (permutation_sign_at n A s) (permutation_sign_at n A t)
  ≔ refl (permutation_sign_at n A) (equiv_homotopy (A .fst .fst) (A .fst .fst) s t h)

{` Loops of composites: the loop of t ∘ s is the loop of s followed by the loop of t. `}
def permutation_loop_compose (n : Nat) (A : BookFiniteSetsAt n) (s t : Equiv (A .fst .fst) (A .fst .fst))
  : Id (Id (BookFiniteSetsAt n) A A) (permutation_loop n A (compose_equiv (A .fst .fst) (A .fst .fst) (A .fst .fst) s t))
      (concat (BookFiniteSetsAt n) A A A (permutation_loop n A s) (permutation_loop n A t))
  ≔ bsigma_path_ext n A A (permutation_loop n A (compose_equiv (A .fst .fst) (A .fst .fst) (A .fst .fst) s t))
      (concat (BookFiniteSetsAt n) A A A (permutation_loop n A s) (permutation_loop n A t))
      (x ↦ inverse (A .fst .fst)
        (transport (BookFiniteSetsAt n) (B ↦ B .fst .fst) A A
          (concat (BookFiniteSetsAt n) A A A (permutation_loop n A s) (permutation_loop n A t)) x)
        (t .map (s .map x))
        (transport_concat (BookFiniteSetsAt n) (B ↦ B .fst .fst) A A A (permutation_loop n A s) (permutation_loop n A t) x))

{` "sgn defines an abstract homomorphism Aut(A) → Σ_2": multiplicativity. `}
def permutation_sign_at_compose (n : Nat) (A : BookFiniteSetsAt n) (s t : Equiv (A .fst .fst) (A .fst .fst))
  : Id Sign (permutation_sign_at n (A) (compose_equiv (A .fst .fst) (A .fst .fst) (A .fst .fst) s t))
      (sign_mul (permutation_sign_at n A t) (permutation_sign_at n A s))
  ≔ match n [
  | zero. ↦ refl (plus. : Sign)
  | suc. zero. ↦ refl (plus. : Sign)
  | suc. (suc. m) ↦
      let k : Nat ≔ suc. (suc. m) in
      let B2 ≔ BookFiniteSetsAt two in
      let ls ≔ permutation_loop k A s in let lt ≔ permutation_loop k A t in
      calc two_loop_sign (bsgn k A) (refl (bsgn k) (permutation_loop k A (compose_equiv (A .fst .fst) (A .fst .fst) (A .fst .fst) s t)))
        = two_loop_sign (bsgn k A) (refl (bsgn k) (concat (BookFiniteSetsAt k) A A A ls lt))
          by refl ((q ↦ two_loop_sign (bsgn k A) (refl (bsgn k) q)) : Id (BookFiniteSetsAt k) A A → Sign)
            (permutation_loop_compose k A s t)
        = two_loop_sign (bsgn k A) (concat B2 (bsgn k A) (bsgn k A) (bsgn k A) (refl (bsgn k) ls) (refl (bsgn k) lt))
          by refl (two_loop_sign (bsgn k A)) (map_path_concat (BookFiniteSetsAt k) B2 (bsgn k) A A A ls lt)
        = sign_mul (two_loop_sign (bsgn k A) (refl (bsgn k) ls)) (two_loop_sign (bsgn k A) (refl (bsgn k) lt))
          by two_loop_sign_concat (bsgn k A) (refl (bsgn k) ls) (refl (bsgn k) lt)
        = sign_mul (two_loop_sign (bsgn k A) (refl (bsgn k) lt)) (two_loop_sign (bsgn k A) (refl (bsgn k) ls))
          by sign_mul_comm (two_loop_sign (bsgn k A) (refl (bsgn k) ls)) (two_loop_sign (bsgn k A) (refl (bsgn k) lt)) ∎ ]

def permutation_sign_compose (A : FiniteSets) (s t : Equiv (A .fst .fst) (A .fst .fst))
  : Id Sign (permutation_sign A (compose_equiv (A .fst .fst) (A .fst .fst) (A .fst .fst) s t))
      (sign_mul (permutation_sign A t) (permutation_sign A s))
  ≔ permutation_sign_at_compose (Card A) (finite_set_point A) s t

def permutation_sign_at_identity (n : Nat) (A : BookFiniteSetsAt n)
  : Id Sign (permutation_sign_at n A (identity_equiv (A .fst .fst))) plus.
  ≔ let s ≔ permutation_sign_at n A (identity_equiv (A .fst .fst)) in
    concat Sign s (sign_mul s (sign_mul s s)) plus.
      (calc s = sign_mul s plus. by inverse Sign (sign_mul s plus.) s (sign_mul_plus_right s)
        = sign_mul s (sign_mul s s) by refl (sign_mul s) (inverse Sign (sign_mul s s) plus. (sign_mul_self s)) ∎)
      (calc sign_mul s (sign_mul s s)
        = sign_mul (sign_mul s s) s by sign_mul_assoc s s s
        = sign_mul plus. s by refl ((u ↦ sign_mul u s) : Sign → Sign) (sign_mul_self s)
        = s by refl s
        = permutation_sign_at n A (compose_equiv (A .fst .fst) (A .fst .fst) (A .fst .fst) (identity_equiv (A .fst .fst)) (identity_equiv (A .fst .fst)))
          by permutation_sign_at_homotopy n A (identity_equiv (A .fst .fst))
            (compose_equiv (A .fst .fst) (A .fst .fst) (A .fst .fst) (identity_equiv (A .fst .fst)) (identity_equiv (A .fst .fst)))
            (x ↦ refl x)
        = sign_mul s s by permutation_sign_at_compose n A (identity_equiv (A .fst .fst)) (identity_equiv (A .fst .fst))
        = plus. by sign_mul_self s ∎)

{` Transport invariance: the sign is invariant under identifications A = A'
   in BΣ_n (conjugation of the permutation). `}
def bsigma_two_transport_n (n : Nat) (A A' : BookFiniteSetsAt n) (c : Id (BookFiniteSetsAt n) A A')
  : Equiv (A .fst .fst) (A' .fst .fst)
  ≔ transport_equiv (A .fst .fst) (A' .fst .fst) (c .fst .fst)

def conjugate_permutation (X Y : Type) (c : Equiv X Y) (s : Equiv X X) : Equiv Y Y
  ≔ compose_equiv Y X Y (canonical_inverse_equiv X Y c) (compose_equiv X X Y s c)

def permutation_sign_at_transport (n : Nat) (A A' : BookFiniteSetsAt n) (c : Id (BookFiniteSetsAt n) A A')
  (s : Equiv (A .fst .fst) (A .fst .fst))
  : Id Sign (permutation_sign_at n A s)
      (permutation_sign_at n A' (conjugate_permutation (A .fst .fst) (A' .fst .fst) (bsigma_two_transport_n n A A' c) s))
  ≔ J (BookFiniteSetsAt n) A
      (A' c ↦ Id Sign (permutation_sign_at n A s)
        (permutation_sign_at n A' (conjugate_permutation (A .fst .fst) (A' .fst .fst) (bsigma_two_transport_n n A A' c) s)))
      (permutation_sign_at_homotopy n A s
        (conjugate_permutation (A .fst .fst) (A .fst .fst) (bsigma_two_transport_n n A A (refl A)) s)
        (x ↦ let tr ≔ bsigma_two_transport_n n A A (refl A) in
          let tri ≔ equiv_inverse_map (A .fst .fst) (A .fst .fst) tr in
          calc s .map x
            = s .map (tri x) by refl (s .map)
                (calc x = tr .map (tri x) by inverse (A .fst .fst) (tr .map (tri x)) x (equiv_counit (A .fst .fst) (A .fst .fst) tr x)
                  = tri x by transport_refl (BookFiniteSetsAt n) (B ↦ B .fst .fst) A (tri x) ∎)
            = tr .map (s .map (tri x)) by inverse (A .fst .fst) (tr .map (s .map (tri x))) (s .map (tri x))
                (transport_refl (BookFiniteSetsAt n) (B ↦ B .fst .fst) A (s .map (tri x))) ∎))
      A' c

{` For the standard n-element set, the sign of σ is the value Usgn(σ) (prose
   after def:sgn-permutation), for n ≥ 2. `}
def permutation_sign_standard (m : Nat) (s : Equiv (Fin (suc. (suc. m))) (Fin (suc. (suc. m))))
  : Id Sign (permutation_sign_at (suc. (suc. m)) (standard_shape (suc. (suc. m))) s)
      (sigma_two_sign (usgn (suc. (suc. m)) (permutation_symmetry (standard_set (suc. (suc. m))) s)))
  ≔ inverse Sign (sigma_two_sign (usgn (suc. (suc. m)) (permutation_symmetry (standard_set (suc. (suc. m))) s)))
      (permutation_sign_at (suc. (suc. m)) (standard_shape (suc. (suc. m))) s)
      (two_loop_sign_conjugate (shape sign_sigma_two) (bsgn (suc. (suc. m)) (standard_shape (suc. (suc. m))))
        (bsgn_point (suc. (suc. m))) (refl (bsgn (suc. (suc. m))) (permutation_symmetry (standard_set (suc. (suc. m))) s)))

{` xca:sign-by-crossings for the sign of permutations of Fin n, every n:
   sgn(σ) = (−1)^inv(σ). For n ≤ 1 there are no inversions. `}
def inversions_small_empty (n : Nat) (hn : Sum (Id Nat n zero.) (Id Nat n (suc. zero.))) (s : Equiv (Fin n) (Fin n))
  (v : Inversions n s) : Empty
  ≔ let isp : isProp (Fin n) ≔ fin_small_isprop n hn in
    fin_lt_ne n (v .fst .fst) (v .fst .snd) (v .snd .fst) (isp (v .fst .fst) (v .fst .snd))

def inversion_count_small (n : Nat) (hn : Sum (Id Nat n zero.) (Id Nat n (suc. zero.))) (s : Equiv (Fin n) (Fin n))
  : Id Nat (inversion_count n s) zero.
  ≔ cardinality_from_path (Inversions n s) (inversions_finite n s) zero.
      (ua (Inversions n s) Empty
        (quasi_inverse_equiv (Inversions n s) Empty (inversions_small_empty n hn s) (x ↦ match x [])
          (v ↦ match inversions_small_empty n hn s v []) (x ↦ match x [])))

def permutation_sign_at_inversions (n : Nat) (s : Equiv (Fin n) (Fin n))
  : Id Sign (permutation_sign_at n (standard_shape n) s) (bool_sign (nat_odd (inversion_count n s)))
  ≔ match n [
  | zero. ↦ inverse Sign (bool_sign (nat_odd (inversion_count zero. s))) plus.
      (refl ((k ↦ bool_sign (nat_odd k)) : Nat → Sign) (inversion_count_small zero. (inl. (refl (zero. : Nat))) s))
  | suc. zero. ↦ inverse Sign (bool_sign (nat_odd (inversion_count (suc. zero.) s))) plus.
      (refl ((k ↦ bool_sign (nat_odd k)) : Nat → Sign) (inversion_count_small (suc. zero.) (inr. (refl (suc. zero. : Nat))) s))
  | suc. (suc. m) ↦ concat Sign (permutation_sign_at (suc. (suc. m)) (standard_shape (suc. (suc. m))) s)
      (sigma_two_sign (usgn (suc. (suc. m)) (permutation_symmetry (standard_set (suc. (suc. m))) s)))
      (bool_sign (nat_odd (inversion_count (suc. (suc. m)) s)))
      (permutation_sign_standard m s) (usgn_inversions m s) ]

{` The standard n-element set: its sign is the sign at the designated shape. `}
def permutation_sign_standard_set (n : Nat) (s : Equiv (Fin n) (Fin n))
  : Id Sign (permutation_sign (standard_finite_set n) s) (permutation_sign_at n (standard_shape n) s)
  ≔ refl ((m ↦ permutation_sign_at n ((Fin n, fin_set n), m) s) : Mere (Id SetTypes (Fin n, fin_set n) (Fin n, fin_set n)) → Sign)
      (mere_isprop (Id SetTypes (Fin n, fin_set n) (Fin n, fin_set n)) (finite_set_point (standard_finite_set n) .snd) (standard_shape n .snd))

{` Footnote (group.tex:1641): Bsgn cannot be pointed uniformly in A. A family
   of identifications Bsgn(A) = sh_{Σ_2} amounts to an identification of
   Bsgn with the constant map, and for n ≥ 2 there is none (the loop of the
   transposition (0 1) is sent to the swap). `}
def bsgn_uniform_pointing_equiv (n : Nat)
  : Equiv ((A : BookFiniteSetsAt n) → Id (BookFiniteSetsAt two) (bsgn n A) (shape sign_sigma_two))
      (Id (BookFiniteSetsAt n → BookFiniteSetsAt two) (bsgn n) (_ ↦ shape sign_sigma_two))
  ≔ canonical_inverse_equiv (Id (BookFiniteSetsAt n → BookFiniteSetsAt two) (bsgn n) (_ ↦ shape sign_sigma_two))
      (Homotopy (BookFiniteSetsAt n) (_ ↦ BookFiniteSetsAt two) (bsgn n) (_ ↦ shape sign_sigma_two))
      (function_extensionality (BookFiniteSetsAt n) (_ ↦ BookFiniteSetsAt two) (bsgn n) (_ ↦ shape sign_sigma_two))

def bsgn_swap01_moves (m : Nat)
  : Id Bool (two_loop_moves (bsgn (suc. (suc. m)) (standard_shape (suc. (suc. m))))
      (refl (bsgn (suc. (suc. m))) (permutation_symmetry (standard_set (suc. (suc. m))) (fin_swap01_equiv m)))) true.
  ≔ let b ≔ two_loop_moves (bsgn (suc. (suc. m)) (standard_shape (suc. (suc. m))))
      (refl (bsgn (suc. (suc. m))) (permutation_symmetry (standard_set (suc. (suc. m))) (fin_swap01_equiv m))) in
    concat Bool b (sign_is_minus (bool_sign b)) true.
      (inverse Bool (sign_is_minus (bool_sign b)) b (sign_is_minus_bool_sign b))
      (refl sign_is_minus
        (concat Sign (permutation_sign_at (suc. (suc. m)) (standard_shape (suc. (suc. m))) (fin_swap01_equiv m))
          (sigma_two_sign (usgn (suc. (suc. m)) (permutation_symmetry (standard_set (suc. (suc. m))) (fin_swap01_equiv m))))
          minus.
          (permutation_sign_standard m (fin_swap01_equiv m)) (usgn_swap01 m)))

def ap_constant_refl (X Y : Type) (y : Y) (x : X) (p : Id X x x)
  : Id (Id Y y y) (refl y) (refl ((_ ↦ y) : X → Y) p)
  ≔ refl (refl y)

def bsgn_no_uniform_pointing (m : Nat)
  (p : (A : BookFiniteSetsAt (suc. (suc. m))) → Id (BookFiniteSetsAt two) (bsgn (suc. (suc. m)) A) (shape sign_sigma_two)) : Empty
  ≔ let n : Nat ≔ suc. (suc. m) in
    let tau ≔ permutation_symmetry (standard_set n) (fin_swap01_equiv m) in
    let c : BookFiniteSetsAt n → BookFiniteSetsAt two ≔ _ ↦ shape sign_sigma_two in
    bool_encode false. true.
      (calc (false. : Bool) = two_loop_moves (shape sign_sigma_two) (refl (shape sign_sigma_two))
          by inverse Bool (two_loop_moves (shape sign_sigma_two) (refl (shape sign_sigma_two))) false. (two_loop_moves_refl (shape sign_sigma_two))
        = two_loop_moves (c (standard_shape n)) (refl c tau) by refl (two_loop_moves (shape sign_sigma_two)) (ap_constant_refl (BookFiniteSetsAt n) (BookFiniteSetsAt two) (shape sign_sigma_two) (standard_shape n) tau)
        = two_loop_moves (bsgn n (standard_shape n)) (refl (bsgn n) tau)
          by two_loop_moves_homotopy (BookFiniteSetsAt n) (bsgn n) c p (standard_shape n) tau
        = true. by bsgn_swap01_moves m ∎)

{` The prose after def:sgn-permutation: for each finite set A the sign is a
   concrete homomorphism sgn^A : Hom(Aut(A), Σ_2) with
   Bsgn^A(B) ≔ (Bsgn(A) = Bsgn(B)), pointed by the identification of the loops
   of Bsgn(A) with {±1}. Stated for a point A0 of BΣ_n; Aut(A0) = Σ_{A0}. `}
def aut_to_bsigma (n : Nat) (A0 : BookFiniteSetsAt n) (B : NativeComponent SetTypes (A0 .fst)) : BookFiniteSetsAt n
  ≔ (B .fst, mere_rec (Id SetTypes (Fin n, fin_set n) (A0 .fst)) (Mere (Id SetTypes (Fin n, fin_set n) (B .fst)))
      (mere_isprop (Id SetTypes (Fin n, fin_set n) (B .fst)))
      (p ↦ trunc_map native_truncation (Id SetTypes (A0 .fst) (B .fst)) (Id SetTypes (Fin n, fin_set n) (B .fst))
        (q ↦ concat SetTypes (Fin n, fin_set n) (A0 .fst) (B .fst) p q) (B .snd))
      (A0 .snd))

def fin_two_sign : Fin two → Sign ≔ [ inr. _ ↦ plus. | inl. (inr. _) ↦ minus. | inl. (inl. e) ↦ match e [] ]

def fin_two_sign_equiv : Equiv (Fin two) Sign
  ≔ quasi_inverse_equiv (Fin two) Sign fin_two_sign [ plus. ↦ inr. star. | minus. ↦ inl. (inr. star.) ]
      [ inr. u ↦ inr. (unit_prop star. u)
      | inl. (inr. u) ↦ inl. (inr. (unit_prop star. u))
      | inl. (inl. e) ↦ match e [] ]
      [ plus. ↦ refl (plus. : Sign) | minus. ↦ refl (minus. : Sign) ]

def path_postcompose_equiv (X : Type) (x y z : X) (c : Id X y z) : Equiv (Id X x y) (Id X x z)
  ≔ quasi_inverse_equiv (Id X x y) (Id X x z) (q ↦ concat X x y z q c) (r ↦ concat X x z y r (inverse X y z c))
      (q ↦ calc concat X x z y (concat X x y z q c) (inverse X y z c)
          = concat X x y y q (concat X y z y c (inverse X y z c)) by concat_assoc X x y z y q c (inverse X y z c)
          = concat X x y y q (refl y) by refl (concat X x y y q) (concat_inverse_right X y z c)
          = q by concat_p1 X x y q ∎)
      (r ↦ calc concat X x y z (concat X x z y r (inverse X y z c)) c
          = concat X x z z r (concat X z y z (inverse X y z c) c) by concat_assoc X x z y z r (inverse X y z c) c
          = concat X x z z r (refl z) by refl (concat X x z z r) (concat_inverse_left X y z c)
          = r by concat_p1 X x z r ∎)

def sets_of_two_sets_paths (T U : BookFiniteSetsAt two) : isSet (Id (BookFiniteSetsAt two) T U)
  ≔ bg_groupoid sign_sigma_two T U

def two_set_paths_two_element (T U : BookFiniteSetsAt two) : TwoElement (Id (BookFiniteSetsAt two) T U)
  ≔ trunc_map native_truncation (Id (BookFiniteSetsAt two) T U) (Id Type (Fin two) (Id (BookFiniteSetsAt two) T U))
      (c ↦ ua (Fin two) (Id (BookFiniteSetsAt two) T U)
        (compose_equiv (Fin two) Sign (Id (BookFiniteSetsAt two) T U) fin_two_sign_equiv
          (compose_equiv Sign (Id (BookFiniteSetsAt two) T T) (Id (BookFiniteSetsAt two) T U)
            (canonical_inverse_equiv (Id (BookFiniteSetsAt two) T T) Sign (two_loops_sign_equiv T))
            (path_postcompose_equiv (BookFiniteSetsAt two) T T U c))))
      (bg_connected sign_sigma_two .snd T U)

def two_set_paths_point (T U : BookFiniteSetsAt two) : BookFiniteSetsAt two
  ≔ two_element_bsigma_two (Id (BookFiniteSetsAt two) T U, sets_of_two_sets_paths T U) (two_set_paths_two_element T U)

def bsgn_aut (n : Nat) (A0 : BookFiniteSetsAt n) (B : NativeComponent SetTypes (A0 .fst)) : BookFiniteSetsAt two
  ≔ two_set_paths_point (bsgn n (aut_to_bsigma n A0 (component_point SetTypes (A0 .fst)))) (bsgn n (aut_to_bsigma n A0 B))

def bsgn_aut_point_equiv (n : Nat) (A0 : BookFiniteSetsAt n)
  : Equiv (Fin two) (Id (BookFiniteSetsAt two) (bsgn n (aut_to_bsigma n A0 (component_point SetTypes (A0 .fst))))
      (bsgn n (aut_to_bsigma n A0 (component_point SetTypes (A0 .fst)))))
  ≔ let T ≔ bsgn n (aut_to_bsigma n A0 (component_point SetTypes (A0 .fst))) in
    compose_equiv (Fin two) Sign (Id (BookFiniteSetsAt two) T T) fin_two_sign_equiv
      (canonical_inverse_equiv (Id (BookFiniteSetsAt two) T T) Sign (two_loops_sign_equiv T))

def bsgn_aut_point (n : Nat) (A0 : BookFiniteSetsAt n)
  : Id (BookFiniteSetsAt two) (shape sign_sigma_two) (bsgn_aut n A0 (component_point SetTypes (A0 .fst)))
  ≔ let T ≔ bsgn n (aut_to_bsigma n A0 (component_point SetTypes (A0 .fst))) in
    component_path SetTypes (Fin two, fin_set two) (shape sign_sigma_two) (bsgn_aut n A0 (component_point SetTypes (A0 .fst)))
      (set_types_path (Fin two, fin_set two) (Id (BookFiniteSetsAt two) T T, sets_of_two_sets_paths T T)
        (bsgn_aut_point_equiv n A0))

def sign_aut_hom (n : Nat) (A0 : BookFiniteSetsAt n) : GroupHom (permutation_group (A0 .fst)) sign_sigma_two
  ≔ mkhom (permutation_group (A0 .fst)) sign_sigma_two (bsgn_aut n A0, bsgn_aut_point n A0)
