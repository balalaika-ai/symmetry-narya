export "46-natural-arithmetic"

def le_not_lt_equal (m n : Nat) (h : Le m n) (no : Lt m n → Empty) : Id Nat m n
  ≔ match le_split m n h [ inl. p ↦ absurd (Id Nat m n) (no p) | inr. p ↦ p ]

def le_not_equal_lt (m n : Nat) (h : Le m n) (no : Id Nat m n → Empty) : Lt m n
  ≔ match le_split m n h [ inl. p ↦ p | inr. p ↦ absurd (Lt m n) (no p) ]

def SearchResult (P : Nat → Type) (n : Nat) : Type ≔ sig (
  value : Nat,
  bounded : Le value n,
  found : Lt value n → P value,
  minimal : (m : Nat) → P m → Le value m)

{` def:Nwellordered. The algorithm remembers its first hit; it inspects P(n)
   only if the previous search found no witness below n. Recursion decreases n. `}
def bounded_search_step (P : Nat → Type) (n : Nat) (s : SearchResult P n)
  (test : Decidable (Lt (s .value) n)) (dn : Decidable (P n)) : SearchResult P (suc. n)
  ≔ match test [
  | inl. hit ↦ (s .value, le_step (s .value) n (s .bounded), (_ ↦ s .found hit), s .minimal)
  | inr. nohit ↦ let eqn ≔ le_not_lt_equal (s .value) n (s .bounded) nohit in
      match dn [
      | inl. pn ↦ (n, le_step n n (le_refl n), (_ ↦ pn),
          (m pm ↦ transport Nat (k ↦ Le k m) (s .value) n eqn (s .minimal m pm)))
      | inr. no ↦ (suc. n, le_refl (suc. n), (p ↦ absurd (P (suc. n)) (lt_irrefl (suc. n) p)),
          (m pm ↦ le_not_equal_lt n m
            (transport Nat (k ↦ Le k m) (s .value) n eqn (s .minimal m pm))
            (p ↦ no (transport Nat P m n (inverse Nat n m p) pm)))) ] ]

def bounded_search (P : Nat → Type) (d : (n : Nat) → Decidable (P n)) (n : Nat) : SearchResult P n
  ≔ match n [
  | zero. ↦ (zero., star., (p ↦ absurd (P zero.) p), (m pm ↦ star.))
  | suc. n ↦ let s ≔ bounded_search P d n in
      bounded_search_step P n s (lt_decidable (s .value) n) (d n) ]

def bounded_min (P : Nat → Type) (d : (n : Nat) → Decidable (P n)) (n : Nat) : Nat
  ≔ bounded_search P d n .value

def bounded_value_step (P : Nat → Type) (n k : Nat) (test : Decidable (Lt k n)) (dn : Decidable (P n)) : Nat
  ≔ match test [ inl. hit ↦ k | inr. nohit ↦ match dn [ inl. pn ↦ n | inr. no ↦ suc. n ] ]

def bounded_min_step (P : Nat → Type) (d : (n : Nat) → Decidable (P n)) (n k : Nat) : Nat
  ≔ bounded_value_step P n k (lt_decidable k n) (d n)

def bounded_min_zero (P : Nat → Type) (d : (n : Nat) → Decidable (P n))
  : Id Nat (bounded_min P d zero.) zero. ≔ refl zero.

def bounded_search_step_value (P : Nat → Type) (n : Nat) (s : SearchResult P n)
  (test : Decidable (Lt (s .value) n)) (dn : Decidable (P n))
  : Id Nat (bounded_search_step P n s test dn .value) (bounded_value_step P n (s .value) test dn)
  ≔ match test [ inl. hit ↦ refl (s .value)
              | inr. nohit ↦ match dn [ inl. pn ↦ refl n | inr. no ↦ refl (suc. n) ] ]

def bounded_min_successor (P : Nat → Type) (d : (n : Nat) → Decidable (P n)) (n : Nat)
  : Id Nat (bounded_min P d (suc. n)) (bounded_min_step P d n (bounded_min P d n))
  ≔ bounded_search_step_value P n (bounded_search P d n) (lt_decidable (bounded_min P d n) n) (d n)

def bounded_min_bound (P : Nat → Type) (d : (n : Nat) → Decidable (P n)) (n : Nat)
  : BookLe (bounded_min P d n) n
  ≔ le_to_book (bounded_min P d n) n (bounded_search P d n .bounded)

def bounded_min_found (P : Nat → Type) (d : (n : Nat) → Decidable (P n)) (n : Nat)
  (h : BookLt (bounded_min P d n) n) : P (bounded_min P d n)
  ≔ bounded_search P d n .found (lt_from_book (bounded_min P d n) n h)

def bounded_min_minimal (P : Nat → Type) (d : (n : Nat) → Decidable (P n)) (n m : Nat) (pm : P m)
  : BookLe (bounded_min P d n) m
  ≔ le_to_book (bounded_min P d n) m (bounded_search P d n .minimal m pm)

def bounded_min_no_hit (P : Nat → Type) (d : (n : Nat) → Decidable (P n)) (n : Nat)
  (eqn : Id Nat (bounded_min P d n) n) (m : Nat) (h : BookLt m n) (pm : P m) : Empty
  ≔ lt_irrefl m (lt_le_trans m n m (lt_from_book m n h)
      (transport Nat (k ↦ Le k m) (bounded_min P d n) n eqn (bounded_search P d n .minimal m pm)))

def IsMinimum (P : Nat → Type) (n : Nat) : Type
  ≔ Product (P n) ((m : Nat) → P m → BookLe n m)

def isminimum_prop (P : Nat → Type) (hp : (n : Nat) → isProp (P n)) (n : Nat) : isProp (IsMinimum P n)
  ≔ product_prop (P n) ((m : Nat) → P m → BookLe n m) (hp n)
      (pi_prop Nat (m ↦ P m → BookLe n m) (m ↦ pi_prop (P m) (_ ↦ BookLe n m) (_ ↦ book_le_prop n m)))

def minimum_unique (P : Nat → Type) (u v : Σ Nat (IsMinimum P)) : Id Nat (u .fst) (v .fst)
  ≔ le_antisym (u .fst) (v .fst)
      (le_from_book (u .fst) (v .fst) (u .snd .snd (v .fst) (v .snd .fst)))
      (le_from_book (v .fst) (u .fst) (v .snd .snd (u .fst) (u .snd .fst)))

def minimum_prop (P : Nat → Type) (hp : (n : Nat) → isProp (P n)) : isProp (Σ Nat (IsMinimum P))
  ≔ u v ↦ subtype_equal Nat (IsMinimum P) (isminimum_prop P hp) u v (minimum_unique P u v)

def minimum_from_witness (P : Nat → Type) (d : (n : Nat) → Decidable (P n)) (n : Nat) (pn : P n)
  : Σ Nat (IsMinimum P)
  ≔ let s ≔ bounded_search P d (suc. n) in
    (s .value, (s .found (s .minimal n pn), (m pm ↦ le_to_book (s .value) m (s .minimal m pm))))

def least_number (P : Nat → Type) (hp : (n : Nat) → isProp (P n))
  (d : (n : Nat) → Decidable (P n)) (h : Mere (Σ Nat P)) : Σ Nat (IsMinimum P)
  ≔ mere_rec (Σ Nat P) (Σ Nat (IsMinimum P)) (minimum_prop P hp)
      (w ↦ minimum_from_witness P d (w .fst) (w .snd)) h
