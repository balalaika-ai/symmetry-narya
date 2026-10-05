export "457-sign-permutations"

{` Chapter 4, sec:sign-homomorphism: lem:sign-properties and cor:sign-defined.
   Transpositions, cycles and words of transpositions are those of modules
   174 and 176 (transposition, cycle_notation, transposition_word_map); the
   product t_1 ⋯ t_k applies t_k first. `}

def sign_mul_minus_bool (b : Bool) : Id Sign (sign_mul minus. (bool_sign b)) (bool_sign (bool_not b))
  ≔ match b [ false. ↦ refl (minus. : Sign) | true. ↦ refl (plus. : Sign) ]

def sign_mul_bool_minus (b : Bool) : Id Sign (sign_mul (bool_sign b) minus.) (bool_sign (bool_not b))
  ≔ match b [ false. ↦ refl (minus. : Sign) | true. ↦ refl (plus. : Sign) ]

def bool_sign_injective (a b : Bool) (p : Id Sign (bool_sign a) (bool_sign b)) : Id Bool a b
  ≔ concat Bool a (sign_is_minus (bool_sign a)) b (inverse Bool (sign_is_minus (bool_sign a)) a (sign_is_minus_bool_sign a))
      (concat Bool (sign_is_minus (bool_sign a)) (sign_is_minus (bool_sign b)) b (refl sign_is_minus p) (sign_is_minus_bool_sign b))

{` Conjugating a transposition gives the transposition of the images. `}
def transposition_conjugate (X Y : Type) (dX : DecidableEquality X) (dY : DecidableEquality Y) (c : Equiv X Y) (a b : X) (y : Y)
  : Id Y (c .map (transposition X dX a b (equiv_inverse_map X Y c y))) (transposition Y dY (c .map a) (c .map b) y)
  ≔ let ci ≔ equiv_inverse_map X Y c in
    let ta ≔ transposition X dX a b in let tc ≔ transposition Y dY (c .map a) (c .map b) in
    match dY y (c .map a) [
    | inl. p ↦ calc c .map (ta (ci y))
        = c .map (ta a) by refl (x ↦ c .map (ta x))
            (calc ci y = ci (c .map a) by refl ci p
              = a by equiv_retraction X Y c a ∎)
        = c .map b by refl (c .map) (transposition_left X dX a b)
        = tc (c .map a) by inverse Y (tc (c .map a)) (c .map b) (transposition_left Y dY (c .map a) (c .map b))
        = tc y by refl tc (inverse Y y (c .map a) p) ∎
    | inr. na ↦ match dY y (c .map b) [
      | inl. q ↦ calc c .map (ta (ci y))
          = c .map (ta b) by refl (x ↦ c .map (ta x))
              (calc ci y = ci (c .map b) by refl ci q
                = b by equiv_retraction X Y c b ∎)
          = c .map a by refl (c .map) (transposition_right X dX a b)
          = tc (c .map b) by inverse Y (tc (c .map b)) (c .map a) (transposition_right Y dY (c .map a) (c .map b))
          = tc y by refl tc (inverse Y y (c .map b) q) ∎
      | inr. nb ↦ calc c .map (ta (ci y))
          = c .map (ci y) by refl (c .map) (transposition_fixed X dX a b (ci y)
              (r ↦ na (concat Y y (c .map (ci y)) (c .map a) (inverse Y (c .map (ci y)) y (equiv_counit X Y c y)) (refl (c .map) r)))
              (r ↦ nb (concat Y y (c .map (ci y)) (c .map b) (inverse Y (c .map (ci y)) y (equiv_counit X Y c y)) (refl (c .map) r))))
          = y by equiv_counit X Y c y
          = tc y by inverse Y (tc y) y (transposition_fixed Y dY (c .map a) (c .map b) y na nb) ∎ ] ]

{` The transposition (0 1) of Fin (m+2) is fin_swap01. `}
def transposition_swap01_std (m : Nat) (x : Fin (suc. (suc. m)))
  : Id (Fin (suc. (suc. m))) (transposition (Fin (suc. (suc. m))) (fin_decidable_equality (suc. (suc. m))) (inr. star.) (inl. (inr. star.)) x)
      (fin_swap01 m x)
  ≔ match x [
  | inr. u ↦ match u [ star. ↦ refl (inl. (inr. star.) : Fin (suc. (suc. m))) ]
  | inl. (inr. u) ↦ match u [ star. ↦ refl (inr. star. : Fin (suc. (suc. m))) ]
  | inl. (inl. y) ↦ refl (inl. (inl. y) : Fin (suc. (suc. m))) ]

def transposition_swap01 (m : Nat) (d : DecidableEquality (Fin (suc. (suc. m)))) (x : Fin (suc. (suc. m)))
  : Id (Fin (suc. (suc. m))) (transposition (Fin (suc. (suc. m))) d (inr. star.) (inl. (inr. star.)) x) (fin_swap01 m x)
  ≔ let k : Nat ≔ suc. (suc. m) in
    concat (Fin k) (transposition (Fin k) d (inr. star.) (inl. (inr. star.)) x)
      (transposition (Fin k) (fin_decidable_equality k) (inr. star.) (inl. (inr. star.)) x) (fin_swap01 m x)
      (refl ((e ↦ transposition (Fin k) e (inr. star.) (inl. (inr. star.)) x) : DecidableEquality (Fin k) → Fin k)
        (decidable_equality_prop (Fin k) (fin_set k) d (fin_decidable_equality k)))
      (transposition_swap01_std m x)

{` A permutation of Fin (m+2) sending i to 0 and j to 1 (i ≠ j). `}
def fin_to_front (m : Nat) (d : DecidableEquality (Fin (suc. (suc. m)))) (i j : Fin (suc. (suc. m))) : Equiv (Fin (suc. (suc. m))) (Fin (suc. (suc. m)))
  ≔ let k : Nat ≔ suc. (suc. m) in
    compose_equiv (Fin k) (Fin k) (Fin k) (transposition_equiv (Fin k) d (inr. star.) i)
      (transposition_equiv (Fin k) d (inl. (inr. star.)) (transposition (Fin k) d (inr. star.) i j))

def fin_to_front_i (m : Nat) (d : DecidableEquality (Fin (suc. (suc. m)))) (i j : Fin (suc. (suc. m))) (nij : Not (Id (Fin (suc. (suc. m))) i j))
  : Id (Fin (suc. (suc. m))) (fin_to_front m d i j .map i) (inr. star.)
  ≔ let k : Nat ≔ suc. (suc. m) in
    let t0 ≔ transposition (Fin k) d (inr. star.) i in
    let j' ≔ t0 j in
    calc transposition (Fin k) d (inl. (inr. star.)) j' (t0 i)
      = transposition (Fin k) d (inl. (inr. star.)) j' (inr. star.) by refl (transposition (Fin k) d (inl. (inr. star.)) j') (transposition_right (Fin k) d (inr. star.) i)
      = inr. star. by transposition_fixed (Fin k) d (inl. (inr. star.)) j' (inr. star.)
          (p ↦ sum_encode (Fin (suc. m)) Unit (inr. star.) (inl. (inr. star.)) p)
          (p ↦ nij (calc i = t0 (inr. star.) by inverse (Fin k) (t0 (inr. star.)) i (transposition_left (Fin k) d (inr. star.) i)
              = t0 j' by refl t0 p
              = j by transposition_involutive (Fin k) d (inr. star.) i j ∎)) ∎

def fin_to_front_j (m : Nat) (d : DecidableEquality (Fin (suc. (suc. m)))) (i j : Fin (suc. (suc. m)))
  : Id (Fin (suc. (suc. m))) (fin_to_front m d i j .map j) (inl. (inr. star.))
  ≔ transposition_right (Fin (suc. (suc. m))) d (inl. (inr. star.)) (transposition (Fin (suc. (suc. m))) d (inr. star.) i j)

def transposition_equiv_points (X : Type) (d : DecidableEquality X) (a a' b b' : X) (p : Id X a a') (q : Id X b b')
  : Id (Equiv X X) (transposition_equiv X d a b) (transposition_equiv X d a' b')
  ≔ refl ((u v ↦ transposition_equiv X d u v) : X → X → Equiv X X) p q

{` lem:sign-properties (1) on the standard set: every transposition of Fin n
   has sign −1. `}
def fin_transposition_sign (m : Nat) (d : DecidableEquality (Fin (suc. (suc. m)))) (i j : Fin (suc. (suc. m)))
  (nij : Not (Id (Fin (suc. (suc. m))) i j))
  : Id Sign (permutation_sign_at (suc. (suc. m)) (standard_shape (suc. (suc. m))) (transposition_equiv (Fin (suc. (suc. m))) d i j)) minus.
  ≔ let k : Nat ≔ suc. (suc. m) in let A0 ≔ standard_shape k in
    let r ≔ fin_to_front m d i j in
    let lr ≔ permutation_loop k A0 r in
    let c ≔ bsigma_two_transport_n k A0 A0 lr in
    calc permutation_sign_at k A0 (transposition_equiv (Fin k) d i j)
      = permutation_sign_at k A0 (conjugate_permutation (Fin k) (Fin k) c (transposition_equiv (Fin k) d i j))
        by permutation_sign_at_transport k A0 A0 lr (transposition_equiv (Fin k) d i j)
      = permutation_sign_at k A0 (transposition_equiv (Fin k) d (r .map i) (r .map j))
        by permutation_sign_at_homotopy k A0 (conjugate_permutation (Fin k) (Fin k) c (transposition_equiv (Fin k) d i j))
          (transposition_equiv (Fin k) d (r .map i) (r .map j))
          (transposition_conjugate (Fin k) (Fin k) d d c i j)
      = permutation_sign_at k A0 (transposition_equiv (Fin k) d (inr. star.) (inl. (inr. star.)))
        by refl (permutation_sign_at k A0) (transposition_equiv_points (Fin k) d (r .map i) (inr. star.) (r .map j) (inl. (inr. star.))
          (fin_to_front_i m d i j nij) (fin_to_front_j m d i j))
      = permutation_sign_at k A0 (fin_swap01_equiv m)
        by permutation_sign_at_homotopy k A0 (transposition_equiv (Fin k) d (inr. star.) (inl. (inr. star.))) (fin_swap01_equiv m)
          (transposition_swap01 m d)
      = sigma_two_sign (usgn k (permutation_symmetry (standard_set k) (fin_swap01_equiv m)))
        by permutation_sign_standard m (fin_swap01_equiv m)
      = minus. by usgn_swap01 m ∎

{` lem:sign-properties (1) for any point A of BΣ_n and any transposition (a b),
   a ≠ b; it forces n ≥ 2. `}
def bsigma_transposition_sign (n : Nat) (A : BookFiniteSetsAt n) (d : DecidableEquality (A .fst .fst)) (a b : A .fst .fst)
  (nab : Not (Id (A .fst .fst) a b))
  : Id Sign (permutation_sign_at n A (transposition_equiv (A .fst .fst) d a b)) minus.
  ≔ match n [
  | zero. ↦ match nab (bsigma_small_prop zero. (inl. (refl (zero. : Nat))) A a b) []
  | suc. zero. ↦ match nab (bsigma_small_prop (suc. zero.) (inr. (refl (suc. zero. : Nat))) A a b) []
  | suc. (suc. m) ↦
      let k : Nat ≔ suc. (suc. m) in let A0 ≔ standard_shape k in
      let t ≔ transposition_equiv (A .fst .fst) d a b in
      mere_rec (Id SetTypes (Fin k, fin_set k) (A .fst)) (Id Sign (permutation_sign_at k A t) minus.)
        (sign_set (permutation_sign_at k A t) minus.)
        (p ↦ let cpath : Id (BookFiniteSetsAt k) A A0
              ≔ inverse (BookFiniteSetsAt k) A0 A (component_path SetTypes (Fin k, fin_set k) A0 A p) in
          let c ≔ bsigma_two_transport_n k A A0 cpath in
          calc permutation_sign_at k A t
            = permutation_sign_at k A0 (conjugate_permutation (A .fst .fst) (Fin k) c t)
              by permutation_sign_at_transport k A A0 cpath t
            = permutation_sign_at k A0 (transposition_equiv (Fin k) (fin_decidable_equality k) (c .map a) (c .map b))
              by permutation_sign_at_homotopy k A0 (conjugate_permutation (A .fst .fst) (Fin k) c t)
                (transposition_equiv (Fin k) (fin_decidable_equality k) (c .map a) (c .map b))
                (transposition_conjugate (A .fst .fst) (Fin k) d (fin_decidable_equality k) c a b)
            = minus. by fin_transposition_sign m (fin_decidable_equality k) (c .map a) (c .map b)
                (q ↦ nab (equiv_injective_path (A .fst .fst) (Fin k) c a b q)) ∎)
        (A .snd) ]

{` lem:sign-properties (1): the sign of a transposition of a finite set is −1. `}
def transposition_sign (A : FiniteSets) (d : DecidableEquality (A .fst .fst)) (a b : A .fst .fst) (nab : Not (Id (A .fst .fst) a b))
  : Id Sign (permutation_sign A (transposition_equiv (A .fst .fst) d a b)) minus.
  ≔ bsigma_transposition_sign (Card A) (finite_set_point A) d a b nab

{` Products of transpositions: (a1 a_k) ⋯ (a1 a2) has sign (−1)^(k−1). `}
def transposition_chain_sign (n : Nat) (A : BookFiniteSetsAt n) (d : DecidableEquality (A .fst .fst)) (a1 : A .fst .fst)
  (l : List (A .fst .fst)) (h : NotInList (A .fst .fst) a1 l)
  : Id Sign (permutation_sign_at n A (transposition_chain_equiv (A .fst .fst) d a1 l)) (bool_sign (nat_odd (length (A .fst .fst) l)))
  ≔ match l [
  | nil. ↦ permutation_sign_at_identity n A
  | cons. b rest ↦
      let X ≔ A .fst .fst in
      calc permutation_sign_at n A (compose_equiv X X X (transposition_equiv X d a1 b) (transposition_chain_equiv X d a1 rest))
        = sign_mul (permutation_sign_at n A (transposition_chain_equiv X d a1 rest)) (permutation_sign_at n A (transposition_equiv X d a1 b))
          by permutation_sign_at_compose n A (transposition_equiv X d a1 b) (transposition_chain_equiv X d a1 rest)
        = sign_mul (bool_sign (nat_odd (length X rest))) minus.
          by refl sign_mul (transposition_chain_sign n A d a1 rest (h .snd)) (bsigma_transposition_sign n A d a1 b (h .fst))
        = bool_sign (bool_not (nat_odd (length X rest))) by sign_mul_bool_minus (nat_odd (length X rest)) ∎ ]

{` lem:sign-properties (2): the sign of a k-cycle (a1 a2 ... ak) with pairwise
   distinct entries is (−1)^(k−1) (via xca:perm-prod-transpositions). `}
def cycle_sign_at (n : Nat) (A : BookFiniteSetsAt n) (d : DecidableEquality (A .fst .fst)) (a1 : A .fst .fst)
  (rest : List (A .fst .fst)) (h : PairwiseDistinct (A .fst .fst) (cons. a1 rest))
  : Id Sign (permutation_sign_at n A (cycle_notation_equiv (A .fst .fst) d a1 rest h))
      (bool_sign (nat_odd (length (A .fst .fst) rest)))
  ≔ let X ≔ A .fst .fst in
    concat Sign (permutation_sign_at n A (cycle_notation_equiv X d a1 rest h))
      (permutation_sign_at n A (transposition_chain_equiv X d a1 rest))
      (bool_sign (nat_odd (length X rest)))
      (permutation_sign_at_homotopy n A (cycle_notation_equiv X d a1 rest h) (transposition_chain_equiv X d a1 rest)
        (x ↦ concat X (cycle_notation X d a1 rest x) (transposition_chain X d a1 rest x) (transposition_chain_equiv X d a1 rest .map x)
          (cycle_transposition_product_at X d a1 rest h x)
          (inverse X (transposition_chain_equiv X d a1 rest .map x) (transposition_chain X d a1 rest x)
            (transposition_chain_equiv_map X d a1 rest x))))
      (transposition_chain_sign n A d a1 rest (h .fst))

def cycle_sign (A : FiniteSets) (d : DecidableEquality (A .fst .fst)) (a1 : A .fst .fst)
  (rest : List (A .fst .fst)) (h : PairwiseDistinct (A .fst .fst) (cons. a1 rest))
  : Id Sign (permutation_sign A (cycle_notation_equiv (A .fst .fst) d a1 rest h))
      (bool_sign (nat_odd (length (A .fst .fst) rest)))
  ≔ cycle_sign_at (Card A) (finite_set_point A) d a1 rest h

{` Words of transpositions t_1 ⋯ t_k as equivalences, and their sign (−1)^k. `}
def transposition_word_equiv (X : Type) (d : DecidableEquality X) (w : List (Transpositions X)) : Equiv X X
  ≔ match w [
  | nil. ↦ identity_equiv X
  | cons. t rest ↦ compose_equiv X X X (transposition_word_equiv X d rest) (transposition_equiv X d (t .fst) (t .snd .fst)) ]

def transposition_word_equiv_map (X : Type) (d : DecidableEquality X) (w : List (Transpositions X)) (x : X)
  : Id X (transposition_word_equiv X d w .map x) (transposition_word_map X d w x)
  ≔ match w [
  | nil. ↦ refl x
  | cons. t rest ↦ refl (transposition X d (t .fst) (t .snd .fst)) (transposition_word_equiv_map X d rest x) ]

def transposition_word_sign (n : Nat) (A : BookFiniteSetsAt n) (d : DecidableEquality (A .fst .fst)) (w : List (Transpositions (A .fst .fst)))
  : Id Sign (permutation_sign_at n A (transposition_word_equiv (A .fst .fst) d w)) (bool_sign (nat_odd (length (Transpositions (A .fst .fst)) w)))
  ≔ match w [
  | nil. ↦ permutation_sign_at_identity n A
  | cons. t rest ↦
      let X ≔ A .fst .fst in
      calc permutation_sign_at n A (compose_equiv X X X (transposition_word_equiv X d rest) (transposition_equiv X d (t .fst) (t .snd .fst)))
        = sign_mul (permutation_sign_at n A (transposition_equiv X d (t .fst) (t .snd .fst))) (permutation_sign_at n A (transposition_word_equiv X d rest))
          by permutation_sign_at_compose n A (transposition_word_equiv X d rest) (transposition_equiv X d (t .fst) (t .snd .fst))
        = sign_mul minus. (bool_sign (nat_odd (length (Transpositions X) rest)))
          by refl sign_mul (bsigma_transposition_sign n A d (t .fst) (t .snd .fst) (t .snd .snd)) (transposition_word_sign n A d rest)
        = bool_sign (bool_not (nat_odd (length (Transpositions X) rest)))
          by sign_mul_minus_bool (nat_odd (length (Transpositions X) rest)) ∎ ]

{` The sign of a permutation written as a word of transpositions. `}
def permutation_sign_word (A : FiniteSets) (d : DecidableEquality (A .fst .fst)) (s : Equiv (A .fst .fst) (A .fst .fst))
  (w : List (Transpositions (A .fst .fst))) (h : (x : A .fst .fst) → Id (A .fst .fst) (s .map x) (transposition_word_map (A .fst .fst) d w x))
  : Id Sign (permutation_sign A s) (bool_sign (nat_odd (length (Transpositions (A .fst .fst)) w)))
  ≔ let X ≔ A .fst .fst in
    concat Sign (permutation_sign A s) (permutation_sign A (transposition_word_equiv X d w))
      (bool_sign (nat_odd (length (Transpositions X) w)))
      (permutation_sign_at_homotopy (Card A) (finite_set_point A) s (transposition_word_equiv X d w)
        (x ↦ concat X (s .map x) (transposition_word_map X d w x) (transposition_word_equiv X d w .map x)
          (h x) (inverse X (transposition_word_equiv X d w .map x) (transposition_word_map X d w x)
            (transposition_word_equiv_map X d w x))))
      (transposition_word_sign (Card A) (finite_set_point A) d w)

{` lem:sign-properties (3): the identity is only a product of an even number
   of transpositions. `}
def identity_word_even (A : FiniteSets) (d : DecidableEquality (A .fst .fst)) (w : List (Transpositions (A .fst .fst)))
  (h : (x : A .fst .fst) → Id (A .fst .fst) x (transposition_word_map (A .fst .fst) d w x))
  : IsEvenNat (length (Transpositions (A .fst .fst)) w)
  ≔ let X ≔ A .fst .fst in
    equiv_inverse_map (IsEvenNat (length (Transpositions X) w)) (Id Bool (nat_odd (length (Transpositions X) w)) false.)
      (is_even_nat_iff (length (Transpositions X) w))
      (inverse Bool false. (nat_odd (length (Transpositions X) w))
        (bool_sign_injective false. (nat_odd (length (Transpositions X) w))
          (calc (plus. : Sign) = permutation_sign A (identity_equiv X)
              by inverse Sign (permutation_sign A (identity_equiv X)) plus. (permutation_sign_at_identity (Card A) (finite_set_point A))
            = bool_sign (nat_odd (length (Transpositions X) w)) by permutation_sign_word A d (identity_equiv X) w h ∎)))

{` cor:sign-defined: two expressions of σ as products of transpositions have
   lengths of the same parity, and sgn(σ) = (−1)^m = (−1)^n. `}
def sign_defined_parity (A : FiniteSets) (d : DecidableEquality (A .fst .fst)) (s : Equiv (A .fst .fst) (A .fst .fst))
  (w1 w2 : List (Transpositions (A .fst .fst)))
  (h1 : (x : A .fst .fst) → Id (A .fst .fst) (s .map x) (transposition_word_map (A .fst .fst) d w1 x))
  (h2 : (x : A .fst .fst) → Id (A .fst .fst) (s .map x) (transposition_word_map (A .fst .fst) d w2 x))
  : Id Bool (nat_odd (length (Transpositions (A .fst .fst)) w1)) (nat_odd (length (Transpositions (A .fst .fst)) w2))
  ≔ let X ≔ A .fst .fst in
    bool_sign_injective (nat_odd (length (Transpositions X) w1)) (nat_odd (length (Transpositions X) w2))
      (concat Sign (bool_sign (nat_odd (length (Transpositions X) w1))) (permutation_sign A s) (bool_sign (nat_odd (length (Transpositions X) w2)))
        (inverse Sign (permutation_sign A s) (bool_sign (nat_odd (length (Transpositions X) w1))) (permutation_sign_word A d s w1 h1))
        (permutation_sign_word A d s w2 h2))
