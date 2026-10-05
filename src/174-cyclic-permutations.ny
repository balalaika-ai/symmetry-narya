export "173-permutation-support"

{` Case distinction on a decision, with its two computation laws. `}
def decide_branch (A P : Type) (d : Decidable P) (yes no : A) : A
  ≔ match d [ inl. _ ↦ yes | inr. _ ↦ no ]

def decide_branch_elim (A P : Type) (d : Decidable P) (yes no z : A)
  (hy : P → Id A yes z) (hn : Not P → Id A no z) : Id A (decide_branch A P d yes no) z
  ≔ match d [ inl. p ↦ hy p | inr. n ↦ hn n ]

def decide_branch_yes (A P : Type) (d : Decidable P) (yes no : A) (p : P)
  : Id A (decide_branch A P d yes no) yes
  ≔ decide_branch_elim A P d yes no yes (_ ↦ refl yes) (n ↦ absurd (Id A no yes) (n p))

def decide_branch_no (A P : Type) (d : Decidable P) (yes no : A) (n : Not P)
  : Id A (decide_branch A P d yes no) no
  ≔ decide_branch_elim A P d yes no no (p ↦ absurd (Id A yes no) (n p)) (_ ↦ refl no)

{` The transposition (a b) of a decidable set: a ↦ b, b ↦ a, all other
   points fixed.  The book requires a ≠ b; for a = b this is the identity. `}
def transposition (A : Type) (d : DecidableEquality A) (a b : A) (x : A) : A
  ≔ decide_branch A (Id A x a) (d x a) b (decide_branch A (Id A x b) (d x b) a x)

def transposition_left (A : Type) (d : DecidableEquality A) (a b : A)
  : Id A (transposition A d a b a) b
  ≔ decide_branch_yes A (Id A a a) (d a a) b (decide_branch A (Id A a b) (d a b) a a) (refl a)

def transposition_right (A : Type) (d : DecidableEquality A) (a b : A)
  : Id A (transposition A d a b b) a
  ≔ decide_branch_elim A (Id A b a) (d b a) b (decide_branch A (Id A b b) (d b b) a b) a
      (p ↦ p) (_ ↦ decide_branch_yes A (Id A b b) (d b b) a b (refl b))

def transposition_fixed (A : Type) (d : DecidableEquality A) (a b x : A)
  (na : Not (Id A x a)) (nb : Not (Id A x b)) : Id A (transposition A d a b x) x
  ≔ concat A (transposition A d a b x) (decide_branch A (Id A x b) (d x b) a x) x
      (decide_branch_no A (Id A x a) (d x a) b (decide_branch A (Id A x b) (d x b) a x) na)
      (decide_branch_no A (Id A x b) (d x b) a x nb)

def transposition_at_b (A : Type) (d : DecidableEquality A) (a b x : A)
  (na : Not (Id A x a)) (q : Id A x b) : Id A (transposition A d a b x) a
  ≔ concat A (transposition A d a b x) (decide_branch A (Id A x b) (d x b) a x) a
      (decide_branch_no A (Id A x a) (d x a) b (decide_branch A (Id A x b) (d x b) a x) na)
      (decide_branch_yes A (Id A x b) (d x b) a x q)

def transposition_involutive (A : Type) (d : DecidableEquality A) (a b x : A)
  : Id A (transposition A d a b (transposition A d a b x)) x
  ≔ let t ≔ transposition A d a b in
    match d x a [
    | inl. p ↦ calc
        t (t x) = t b by refl t (concat A (t x) (t a) b (refl t p) (transposition_left A d a b))
        = a by transposition_right A d a b
        = x by inverse A x a p ∎
    | inr. na ↦ match d x b [
      | inl. q ↦ calc
          t (t x) = t a by refl t (transposition_at_b A d a b x na q)
          = b by transposition_left A d a b
          = x by inverse A x b q ∎
      | inr. nb ↦ calc
          t (t x) = t x by refl t (transposition_fixed A d a b x na nb)
          = x by transposition_fixed A d a b x na nb ∎ ] ]

def transposition_equiv (A : Type) (d : DecidableEquality A) (a b : A) : Equiv A A
  ≔ quasi_inverse_equiv A A (transposition A d a b) (transposition A d a b)
      (transposition_involutive A d a b) (transposition_involutive A d a b)

def NotInList (A : Type) (x : A) (l : List A) : Type
  ≔ match l [ nil. ↦ Unit | cons. a rest ↦ Product (Not (Id A x a)) (NotInList A x rest) ]

def PairwiseDistinct (A : Type) (l : List A) : Type
  ≔ match l [ nil. ↦ Unit | cons. a rest ↦ Product (NotInList A a rest) (PairwiseDistinct A rest) ]

def cycle_next_head (A : Type) (first : A) (rest : List A) : A
  ≔ match rest [ nil. ↦ first | cons. b _ ↦ b ]

{` Look x up in a list: the first match is sent to the next entry, the
   last entry to first; points not in the list are fixed. `}
def cycle_lookup (A : Type) (d : DecidableEquality A) (first : A) (l : List A) (x : A) : A
  ≔ match l [
  | nil. ↦ x
  | cons. a rest ↦ decide_branch A (Id A x a) (d x a) (cycle_next_head A first rest)
      (cycle_lookup A d first rest x) ]

{` The cyclic permutation (a_1 a_2 ... a_k) of a decidable set, for the
   list a_1 :: rest with k = 1 + length rest. `}
def cycle_notation (A : Type) (d : DecidableEquality A) (a1 : A) (rest : List A) : A → A
  ≔ cycle_lookup A d a1 (cons. a1 rest)

def cycle_lookup_absent (A : Type) (d : DecidableEquality A) (first : A) (l : List A) (x : A)
  (h : NotInList A x l) : Id A (cycle_lookup A d first l x) x
  ≔ match l [
  | nil. ↦ refl x
  | cons. a rest ↦ concat A (cycle_lookup A d first (cons. a rest) x) (cycle_lookup A d first rest x) x
      (decide_branch_no A (Id A x a) (d x a) (cycle_next_head A first rest) (cycle_lookup A d first rest x) (h .fst))
      (cycle_lookup_absent A d first rest x (h .snd)) ]

def cycle_lookup_found (A : Type) (d : DecidableEquality A) (first : A) (pre : List A) (b : A) (post : List A)
  (h : NotInList A b pre)
  : Id A (cycle_lookup A d first (append A pre (cons. b post)) b) (cycle_next_head A first post)
  ≔ match pre [
  | nil. ↦ decide_branch_yes A (Id A b b) (d b b) (cycle_next_head A first post) (cycle_lookup A d first post b) (refl b)
  | cons. a pre ↦ concat A (cycle_lookup A d first (cons. a (append A pre (cons. b post))) b)
      (cycle_lookup A d first (append A pre (cons. b post)) b) (cycle_next_head A first post)
      (decide_branch_no A (Id A b a) (d b a) (cycle_next_head A first (append A pre (cons. b post)))
        (cycle_lookup A d first (append A pre (cons. b post)) b) (h .fst))
      (cycle_lookup_found A d first pre b post (h .snd)) ]

{` The defining behaviour: points outside the list are fixed, and an entry
   b is sent to the next entry, or to a_1 when b = a_k is last. `}
def cycle_notation_fixed (A : Type) (d : DecidableEquality A) (a1 : A) (rest : List A) (x : A)
  (h : NotInList A x (cons. a1 rest)) : Id A (cycle_notation A d a1 rest x) x
  ≔ cycle_lookup_absent A d a1 (cons. a1 rest) x h

def cycle_notation_successor (A : Type) (d : DecidableEquality A) (a1 : A) (pre : List A) (b : A)
  (post : List A) (h : NotInList A b (cons. a1 pre))
  : Id A (cycle_notation A d a1 (append A pre (cons. b post)) b) (cycle_next_head A a1 post)
  ≔ cycle_lookup_found A d a1 (cons. a1 pre) b post h

def cycle_notation_first (A : Type) (d : DecidableEquality A) (a1 : A) (rest : List A)
  : Id A (cycle_notation A d a1 rest a1) (cycle_next_head A a1 rest)
  ≔ cycle_lookup_found A d a1 nil. a1 rest star.

{` (a_1 ... a_k) = (a_1 ... a_{k-1}... without a_2) composed with (a_1 a_2). `}
def cycle_notation_step (A : Type) (d : DecidableEquality A) (a1 a2 : A) (rest : List A)
  (n12 : Not (Id A a1 a2)) (h2 : NotInList A a2 rest) (x : A)
  : Id A (cycle_notation A d a1 (cons. a2 rest) x) (cycle_notation A d a1 rest (transposition A d a1 a2 x))
  ≔ let c ≔ cycle_notation A d a1 rest in
    let t ≔ transposition A d a1 a2 in
    let n21 : Not (Id A a2 a1) ≔ p ↦ n12 (inverse A a2 a1 p) in
    match d x a1 [
    | inl. p ↦ calc
        cycle_notation A d a1 (cons. a2 rest) x = a2
          by decide_branch_yes A (Id A x a1) (d x a1) a2 (cycle_lookup A d a1 (cons. a2 rest) x) p
        = cycle_lookup A d a1 rest a2 by inverse A (cycle_lookup A d a1 rest a2) a2
          (cycle_lookup_absent A d a1 rest a2 h2)
        = c a2 by inverse A (c a2) (cycle_lookup A d a1 rest a2)
          (decide_branch_no A (Id A a2 a1) (d a2 a1) (cycle_next_head A a1 rest) (cycle_lookup A d a1 rest a2) n21)
        = c (t x) by inverse A (c (t x)) (c a2)
          (refl c (concat A (t x) (t a1) a2 (refl t p) (transposition_left A d a1 a2))) ∎
    | inr. na ↦ calc
        cycle_notation A d a1 (cons. a2 rest) x = cycle_lookup A d a1 (cons. a2 rest) x
          by decide_branch_no A (Id A x a1) (d x a1) a2 (cycle_lookup A d a1 (cons. a2 rest) x) na
        = c (t x) by match d x a2 [
          | inl. q ↦ calc
              cycle_lookup A d a1 (cons. a2 rest) x = cycle_next_head A a1 rest
                by decide_branch_yes A (Id A x a2) (d x a2) (cycle_next_head A a1 rest) (cycle_lookup A d a1 rest x) q
              = c a1 by inverse A (c a1) (cycle_next_head A a1 rest) (cycle_notation_first A d a1 rest)
              = c (t x) by inverse A (c (t x)) (c a1) (refl c (transposition_at_b A d a1 a2 x na q)) ∎
          | inr. nq ↦ calc
              cycle_lookup A d a1 (cons. a2 rest) x = cycle_lookup A d a1 rest x
                by decide_branch_no A (Id A x a2) (d x a2) (cycle_next_head A a1 rest) (cycle_lookup A d a1 rest x) nq
              = c x by inverse A (c x) (cycle_lookup A d a1 rest x)
                (decide_branch_no A (Id A x a1) (d x a1) (cycle_next_head A a1 rest) (cycle_lookup A d a1 rest x) na)
              = c (t x) by inverse A (c (t x)) (c x) (refl c (transposition_fixed A d a1 a2 x na nq)) ∎ ] ∎ ]

{` (a_1 a_k)(a_1 a_{k-1}) ... (a_1 a_2), rightmost factor applied first. `}
def transposition_chain (A : Type) (d : DecidableEquality A) (a1 : A) (l : List A) : A → A
  ≔ match l [
  | nil. ↦ identity A
  | cons. b rest ↦ compose A A A (transposition_chain A d a1 rest) (transposition A d a1 b) ]

def cycle_transposition_product_at (A : Type) (d : DecidableEquality A) (a1 : A) (rest : List A)
  (h : PairwiseDistinct A (cons. a1 rest)) (x : A)
  : Id A (cycle_notation A d a1 rest x) (transposition_chain A d a1 rest x)
  ≔ match rest [
  | nil. ↦ decide_branch_elim A (Id A x a1) (d x a1) a1 x x (p ↦ inverse A x a1 p) (_ ↦ refl x)
  | cons. a2 rest ↦ calc
      cycle_notation A d a1 (cons. a2 rest) x
      = cycle_notation A d a1 rest (transposition A d a1 a2 x)
        by cycle_notation_step A d a1 a2 rest (h .fst .fst) (h .snd .fst) x
      = transposition_chain A d a1 rest (transposition A d a1 a2 x)
        by cycle_transposition_product_at A d a1 rest (h .fst .snd, h .snd .snd) (transposition A d a1 a2 x) ∎ ]

{` xca:perm-prod-transpositions: for pairwise distinct a_1, ..., a_k,
   (a_1 a_2 ... a_k) = (a_1 a_k)(a_1 a_{k-1}) ... (a_1 a_2), with k-1 factors. `}
def cycle_transposition_product (A : Type) (d : DecidableEquality A) (a1 : A) (rest : List A)
  (h : PairwiseDistinct A (cons. a1 rest))
  : Id (A → A) (cycle_notation A d a1 rest) (transposition_chain A d a1 rest)
  ≔ funext A (_ ↦ A) (cycle_notation A d a1 rest) (transposition_chain A d a1 rest)
      (cycle_transposition_product_at A d a1 rest h)

def transposition_chain_equiv (A : Type) (d : DecidableEquality A) (a1 : A) (l : List A) : Equiv A A
  ≔ match l [
  | nil. ↦ identity_equiv A
  | cons. b rest ↦ compose_equiv A A A (transposition_equiv A d a1 b) (transposition_chain_equiv A d a1 rest) ]

def transposition_chain_equiv_map (A : Type) (d : DecidableEquality A) (a1 : A) (l : List A) (x : A)
  : Id A (transposition_chain_equiv A d a1 l .map x) (transposition_chain A d a1 l x)
  ≔ match l [
  | nil. ↦ refl x
  | cons. b rest ↦ transposition_chain_equiv_map A d a1 rest (transposition A d a1 b x) ]

{` Consequently every k-cycle of pairwise distinct entries is a permutation. `}
def cycle_notation_equiv (A : Type) (d : DecidableEquality A) (a1 : A) (rest : List A)
  (h : PairwiseDistinct A (cons. a1 rest)) : Equiv A A
  ≔ equiv_change_map A A (transposition_chain_equiv A d a1 rest) (cycle_notation A d a1 rest)
      (x ↦ concat A (transposition_chain_equiv A d a1 rest .map x) (transposition_chain A d a1 rest x)
        (cycle_notation A d a1 rest x) (transposition_chain_equiv_map A d a1 rest x)
        (inverse A (cycle_notation A d a1 rest x) (transposition_chain A d a1 rest x)
          (cycle_transposition_product_at A d a1 rest h x)))
