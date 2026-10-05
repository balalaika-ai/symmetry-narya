export "45-induced-quotients"

def add_swap_tail (a b c : Nat) : Id Nat (add (add a b) c) (add (add a c) b)
  ≔ calc
      add (add a b) c = add a (add b c) by add_assoc a b c
      = add a (add c b) by refl (add a) (add_comm b c)
      = add (add a c) b by add_assoc a c b ∎

def add_interchange (a b c d : Nat)
  : Id Nat (add (add a b) (add c d)) (add (add a c) (add b d))
  ≔ calc
      add (add a b) (add c d) = add (add (add a b) c) d by add_assoc (add a b) c d
      = add (add (add a c) b) d by refl ((x ↦ add x d) : Nat → Nat) (add_swap_tail a b c)
      = add (add a c) (add b d) by add_assoc (add a c) b d ∎

def mul_zero_left (n : Nat) : Id Nat (mul zero. n) zero.
  ≔ match n [ zero. ↦ refl zero. | suc. n ↦ mul_zero_left n ]

def mul_suc_left (m n : Nat) : Id Nat (mul (suc. m) n) (add (mul m n) n)
  ≔ match n [ zero. ↦ refl zero.
  | suc. n ↦ suc. (concat Nat (add (mul (suc. m) n) m) (add (add (mul m n) n) m)
      (add (add (mul m n) m) n)
      (refl ((x ↦ add x m) : Nat → Nat) (mul_suc_left m n)) (add_swap_tail (mul m n) n m)) ]

def mul_comm (m n : Nat) : Id Nat (mul m n) (mul n m)
  ≔ match n [
  | zero. ↦ inverse Nat (mul zero. m) zero. (mul_zero_left m)
  | suc. n ↦ concat Nat (add (mul m n) m) (add (mul n m) m) (mul (suc. n) m)
      (refl ((x ↦ add x m) : Nat → Nat) (mul_comm m n))
      (inverse Nat (mul (suc. n) m) (add (mul n m) m) (mul_suc_left n m)) ]

def mul_add_right (a b c : Nat) : Id Nat (mul (add a b) c) (add (mul a c) (mul b c))
  ≔ match c [ zero. ↦ refl zero.
  | suc. c ↦ concat Nat (add (mul (add a b) c) (add a b))
      (add (add (mul a c) (mul b c)) (add a b)) (add (add (mul a c) a) (add (mul b c) b))
      (refl ((x ↦ add x (add a b)) : Nat → Nat) (mul_add_right a b c))
      (add_interchange (mul a c) (mul b c) a b) ]

def mul_add_left (a b c : Nat) : Id Nat (mul a (add b c)) (add (mul a b) (mul a c))
  ≔ match c [ zero. ↦ refl (mul a b)
  | suc. c ↦ concat Nat (add (mul a (add b c)) a) (add (add (mul a b) (mul a c)) a)
      (add (mul a b) (add (mul a c) a))
      (refl ((x ↦ add x a) : Nat → Nat) (mul_add_left a b c)) (add_assoc (mul a b) (mul a c) a) ]

def mul_assoc (a b c : Nat) : Id Nat (mul (mul a b) c) (mul a (mul b c))
  ≔ match c [ zero. ↦ refl zero.
  | suc. c ↦ concat Nat (add (mul (mul a b) c) (mul a b))
      (add (mul a (mul b c)) (mul a b)) (mul a (add (mul b c) b))
      (refl ((x ↦ add x (mul a b)) : Nat → Nat) (mul_assoc a b c))
      (inverse Nat (mul a (add (mul b c) b)) (add (mul a (mul b c)) (mul a b)) (mul_add_left a (mul b c) b)) ]

def successor_paths_equiv (m n : Nat) : Equiv (Id Nat (suc. m) (suc. n)) (Id Nat m n)
  ≔ iff_equiv (Id Nat (suc. m) (suc. n)) (Id Nat m n) (nat_set (suc. m) (suc. n)) (nat_set m n)
      (p ↦ refl nat_pred p) (p ↦ suc. p)

def le_step (m n : Nat) (h : Le m n) : Le m (suc. n)
  ≔ match m, n [ zero., n ↦ star. | suc. m, zero. ↦ match h []
               | suc. m, suc. n ↦ le_step m n h ]

def lt_le (m n : Nat) (h : Lt m n) : Le m n
  ≔ le_trans m (suc. m) n (le_step m m (le_refl m)) h

def lt_trans (m n k : Nat) (p : Lt m n) (q : Lt n k) : Lt m k
  ≔ le_trans (suc. m) n k p (lt_le n k q)

def le_lt_trans (m n k : Nat) (p : Le m n) (q : Lt n k) : Lt m k
  ≔ le_trans (suc. m) (suc. n) k p q

def lt_le_trans (m n k : Nat) (p : Lt m n) (q : Le n k) : Lt m k
  ≔ le_trans (suc. m) n k p q

def lt_irrefl (n : Nat) : Lt n n → Empty
  ≔ match n [ zero. ↦ (h ↦ h) | suc. n ↦ lt_irrefl n ]

def lt_not_equal (m n : Nat) (h : Lt m n) (p : Id Nat m n) : Empty
  ≔ lt_irrefl m (transport Nat (Lt m) n m (inverse Nat m n p) h)

def lt_asym (m n : Nat) (p : Lt m n) (q : Lt n m) : Empty ≔ lt_irrefl m (lt_trans m n m p q)

def le_from_equal (m n : Nat) (p : Id Nat m n) : Le m n
  ≔ transport Nat (Le m) m n p (le_refl m)

def le_split (m n : Nat) (h : Le m n) : Sum (Lt m n) (Id Nat m n)
  ≔ match m, n [
  | zero., zero. ↦ inr. (refl zero.)
  | zero., suc. n ↦ inl. star.
  | suc. m, zero. ↦ match h []
  | suc. m, suc. n ↦ match le_split m n h [ inl. p ↦ inl. p | inr. p ↦ inr. (suc. p) ] ]

def disjoint_sum_prop (A B : Type) (ha : isProp A) (hb : isProp B) (h : A → B → Empty)
  : isProp (Sum A B)
  ≔ u v ↦ match u, v [
  | inl. a, inl. b ↦ inl. (ha a b)
  | inl. a, inr. b ↦ match h a b []
  | inr. b, inl. a ↦ match h a b []
  | inr. a, inr. b ↦ inr. (hb a b) ]

def le_split_equiv (m n : Nat) : Equiv (Le m n) (Sum (Lt m n) (Id Nat m n))
  ≔ iff_equiv (Le m n) (Sum (Lt m n) (Id Nat m n)) (le_prop m n)
      (disjoint_sum_prop (Lt m n) (Id Nat m n) (le_prop (suc. m) n) (nat_set m n) (lt_not_equal m n))
      (le_split m n) [ inl. p ↦ lt_le m n p | inr. p ↦ le_from_equal m n p ]

def le_antisym_equiv (m n : Nat) : Equiv (Product (Le m n) (Le n m)) (Id Nat m n)
  ≔ iff_equiv (Product (Le m n) (Le n m)) (Id Nat m n)
      (product_prop (Le m n) (Le n m) (le_prop m n) (le_prop n m)) (nat_set m n)
      (p ↦ le_antisym m n (p .fst) (p .snd))
      (p ↦ (le_from_equal m n p, le_from_equal n m (inverse Nat m n p)))

def le_add_right (m n k : Nat) (h : Le m n) : Le (add m k) (add n k)
  ≔ match k [ zero. ↦ h | suc. k ↦ le_add_right m n k h ]

def le_add_left (k m n : Nat) (h : Le m n) : Le (add k m) (add k n)
  ≔ refl Le (add_comm m k) (add_comm n k) .trr (le_add_right m n k h)

def lt_add_right (m n k : Nat) (h : Lt m n) : Lt (add m k) (add n k)
  ≔ transport Nat (x ↦ Le x (add n k)) (add (suc. m) k) (suc. (add m k))
      (add_suc_left m k) (le_add_right (suc. m) n k h)

def lt_add_left (k m n : Nat) (h : Lt m n) : Lt (add k m) (add k n)
  ≔ refl Lt (add_comm m k) (add_comm n k) .trr (lt_add_right m n k h)

def le_add_both (a b c d : Nat) (p : Le a b) (q : Le c d) : Le (add a c) (add b d)
  ≔ le_trans (add a c) (add b c) (add b d) (le_add_right a b c p) (le_add_left b c d q)

def le_mul_right (m n k : Nat) (h : Le m n) : Le (mul m k) (mul n k)
  ≔ match k [ zero. ↦ star. | suc. k ↦ le_add_both (mul m k) (mul n k) m n (le_mul_right m n k h) h ]

def le_mul_left (k m n : Nat) (h : Le m n) : Le (mul k m) (mul k n)
  ≔ refl Le (mul_comm m k) (mul_comm n k) .trr (le_mul_right m n k h)

{` xca:try-your-luck-N: the order statements with the exact book relations. `}
def book_le_split (m n : Nat) : Equiv (BookLe m n) (Sum (BookLt m n) (Id Nat m n))
  ≔ compose_equiv (BookLe m n) (Le m n) (Sum (BookLt m n) (Id Nat m n))
      (canonical_inverse_equiv (Le m n) (BookLe m n) (le_book_equiv m n))
      (compose_equiv (Le m n) (Sum (Lt m n) (Id Nat m n)) (Sum (BookLt m n) (Id Nat m n))
        (le_split_equiv m n) (sum_equiv (Lt m n) (Id Nat m n) (BookLt m n) (Id Nat m n)
          (lt_book_equiv m n) (identity_equiv (Id Nat m n))))

def book_le_trans (m n k : Nat) (p : BookLe m n) (q : BookLe n k) : BookLe m k
  ≔ le_to_book m k (le_trans m n k (le_from_book m n p) (le_from_book n k q))
def book_lt_trans (m n k : Nat) (p : BookLt m n) (q : BookLt n k) : BookLt m k
  ≔ lt_to_book m k (lt_trans m n k (lt_from_book m n p) (lt_from_book n k q))
def book_le_add_right (m n k : Nat) (h : BookLe m n) : BookLe (add m k) (add n k)
  ≔ le_to_book (add m k) (add n k) (le_add_right m n k (le_from_book m n h))
def book_lt_add_right (m n k : Nat) (h : BookLt m n) : BookLt (add m k) (add n k)
  ≔ lt_to_book (add m k) (add n k) (lt_add_right m n k (lt_from_book m n h))
def book_le_mul_right (m n k : Nat) (h : BookLe m n) : BookLe (mul m k) (mul n k)
  ≔ le_to_book (mul m k) (mul n k) (le_mul_right m n k (le_from_book m n h))
def book_le_add_left (k m n : Nat) (h : BookLe m n) : BookLe (add k m) (add k n)
  ≔ le_to_book (add k m) (add k n) (le_add_left k m n (le_from_book m n h))
def book_lt_add_left (k m n : Nat) (h : BookLt m n) : BookLt (add k m) (add k n)
  ≔ lt_to_book (add k m) (add k n) (lt_add_left k m n (lt_from_book m n h))
def book_le_mul_left (k m n : Nat) (h : BookLe m n) : BookLe (mul k m) (mul k n)
  ≔ le_to_book (mul k m) (mul k n) (le_mul_left k m n (le_from_book m n h))
def book_lt_asym (m n : Nat) (p : BookLt m n) (q : BookLt n m) : Empty
  ≔ lt_asym m n (lt_from_book m n p) (lt_from_book n m q)

def book_le_antisym_equiv (m n : Nat) : Equiv (Product (BookLe m n) (BookLe n m)) (Id Nat m n)
  ≔ compose_equiv (Product (BookLe m n) (BookLe n m)) (Product (Le m n) (Le n m)) (Id Nat m n)
      (product_equiv (BookLe m n) (BookLe n m) (Le m n) (Le n m)
        (canonical_inverse_equiv (Le m n) (BookLe m n) (le_book_equiv m n))
        (canonical_inverse_equiv (Le n m) (BookLe n m) (le_book_equiv n m))) (le_antisym_equiv m n)
