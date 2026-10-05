export "30-finite-types"
export "07-discrete"

def add_cancel_right (m x y : Nat) (p : Id Nat (add x m) (add y m)) : Id Nat x y
  ≔ match m [ zero. ↦ p | suc. m ↦ add_cancel_right m x y (refl nat_pred p) ]

{` def:orderonN: witness definitions, including uniqueness of the difference. `}
def BookLe (m n : Nat) : Type ≔ Σ Nat (k ↦ Id Nat (add k m) n)
def BookLt (m n : Nat) : Type ≔ Σ Nat (k ↦ Product (Id Nat k zero. → Empty) (Id Nat (add k m) n))
def Lt (m n : Nat) : Type ≔ Le (suc. m) n

def difference_unique (m n : Nat) (k l : Nat)
  (p : Id Nat (add k m) n) (q : Id Nat (add l m) n) : Id Nat k l
  ≔ add_cancel_right m k l
      (concat Nat (add k m) n (add l m) p (inverse Nat (add l m) n q))

def subtype_equal (A : Type) (B : A → Type) (h : (a : A) → isProp (B a))
  (u v : Σ A B) (p : Id A (u .fst) (v .fst)) : Id (Σ A B) u v
  ≔ equiv_inverse_map (Id (Σ A B) u v) (Id A (u .fst) (v .fst)) (subtype_path_equiv A B h u v) p

def book_le_prop (m n : Nat) : isProp (BookLe m n)
  ≔ u v ↦ subtype_equal Nat (k ↦ Id Nat (add k m) n) (k ↦ nat_set (add k m) n) u v
      (difference_unique m n (u .fst) (v .fst) (u .snd) (v .snd))

def book_lt_prop (m n : Nat) : isProp (BookLt m n)
  ≔ u v ↦ subtype_equal Nat (k ↦ Product (Id Nat k zero. → Empty) (Id Nat (add k m) n))
      (k ↦ product_prop (Id Nat k zero. → Empty) (Id Nat (add k m) n)
        (negation_prop (Id Nat k zero.)) (nat_set (add k m) n)) u v
      (difference_unique m n (u .fst) (v .fst) (u .snd .snd) (v .snd .snd))

def le_to_book (m n : Nat) (h : Le m n) : BookLe m n
  ≔ match m, n [
  | zero., n ↦ (n, refl n)
  | suc. m, zero. ↦ match h []
  | suc. m, suc. n ↦ let p ≔ le_to_book m n h in (p .fst, suc. (p .snd)) ]

def le_from_book_at (m n k : Nat) (p : Id Nat (add k m) n) : Le m n
  ≔ match m, n [
  | zero., n ↦ star.
  | suc. m, zero. ↦ match nat_encode (suc. (add k m)) zero. p []
  | suc. m, suc. n ↦ le_from_book_at m n k (refl nat_pred p) ]

def le_from_book (m n : Nat) (p : BookLe m n) : Le m n
  ≔ le_from_book_at m n (p .fst) (p .snd)

def le_book_equiv (m n : Nat) : Equiv (Le m n) (BookLe m n)
  ≔ iff_equiv (Le m n) (BookLe m n) (le_prop m n) (book_le_prop m n)
      (le_to_book m n) (le_from_book m n)

def lt_to_book (m n : Nat) (h : Lt m n) : BookLt m n
  ≔ let p ≔ le_to_book (suc. m) n h in
    (suc. (p .fst), ((q ↦ nat_encode (suc. (p .fst)) zero. q),
      concat Nat (add (suc. (p .fst)) m) (suc. (add (p .fst) m)) n (add_suc_left (p .fst) m) (p .snd)))

def lt_from_book_at (m n k : Nat) (h : Id Nat k zero. → Empty) (p : Id Nat (add k m) n) : Lt m n
  ≔ match k [
  | zero. ↦ match h (refl zero.) []
  | suc. k ↦ le_from_book_at (suc. m) n k
      (concat Nat (suc. (add k m)) (add (suc. k) m) n
        (inverse Nat (add (suc. k) m) (suc. (add k m)) (add_suc_left k m)) p) ]

def lt_from_book (m n : Nat) (p : BookLt m n) : Lt m n
  ≔ lt_from_book_at m n (p .fst) (p .snd .fst) (p .snd .snd)

def lt_book_equiv (m n : Nat) : Equiv (Lt m n) (BookLt m n)
  ≔ iff_equiv (Lt m n) (BookLt m n) (le_prop (suc. m) n) (book_lt_prop m n)
      (lt_to_book m n) (lt_from_book m n)

def lt_decidable (m n : Nat) : Decidable (Lt m n) ≔ le_decidable (suc. m) n

def book_le_decidable (m n : Nat) : Decidable (BookLe m n)
  ≔ match le_decidable m n [ inl. h ↦ inl. (le_to_book m n h) | inr. h ↦ inr. (p ↦ h (le_from_book m n p)) ]

def book_lt_decidable (m n : Nat) : Decidable (BookLt m n)
  ≔ match lt_decidable m n [ inl. h ↦ inl. (lt_to_book m n h) | inr. h ↦ inr. (p ↦ h (lt_from_book m n p)) ]
