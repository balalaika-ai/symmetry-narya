export "134-roots-preserve-cycles"

def root_finite_encode (n : Nat) (X : Type) (u : Product (Fin (suc. n)) X) : Product (Remainder (suc. n)) X
  ≔ (fin_book_below_equiv (suc. n) .map (u .fst), u .snd)
def root_finite_decode (n : Nat) (X : Type) (u : Product (Remainder (suc. n)) X) : Product (Fin (suc. n)) X
  ≔ (equiv_inverse_map (Fin (suc. n)) (Remainder (suc. n)) (fin_book_below_equiv (suc. n)) (u .fst), u .snd)

def root_finite_encode_decode (n : Nat) (X : Type) (u : Product (Remainder (suc. n)) X)
  : Id (Product (Remainder (suc. n)) X) (root_finite_encode n X (root_finite_decode n X u)) u
  ≔ (equiv_counit (Fin (suc. n)) (Remainder (suc. n)) (fin_book_below_equiv (suc. n)) (u .fst), refl (u .snd))
def root_finite_decode_encode (n : Nat) (X : Type) (u : Product (Fin (suc. n)) X)
  : Id (Product (Fin (suc. n)) X) (root_finite_decode n X (root_finite_encode n X u)) u
  ≔ (equiv_retraction (Fin (suc. n)) (Remainder (suc. n)) (fin_book_below_equiv (suc. n)) (u .fst), refl (u .snd))

def root_finite_coordinates (n : Nat) (X : Type)
  : Equiv (Product (Fin (suc. n)) X) (Product (Remainder (suc. n)) X)
  ≔ quasi_inverse_equiv (Product (Fin (suc. n)) X) (Product (Remainder (suc. n)) X)
      (root_finite_encode n X) (root_finite_decode n X) (root_finite_decode_encode n X) (root_finite_encode_decode n X)
def root_finite_coordinates_inverse (n : Nat) (X : Type)
  : Equiv (Product (Remainder (suc. n)) X) (Product (Fin (suc. n)) X)
  ≔ quasi_inverse_equiv (Product (Remainder (suc. n)) X) (Product (Fin (suc. n)) X)
      (root_finite_decode n X) (root_finite_encode n X) (root_finite_encode_decode n X) (root_finite_decode_encode n X)

{` con:root on the literal finite type, for m=suc n>0. `}
def root_finite (n : Nat) (X : Type) (t : X → X) (u : Product (Fin (suc. n)) X) : Product (Fin (suc. n)) X
  ≔ root_finite_decode n X (root_remainder n X t (root_finite_encode n X u))

def root_finite_decode_step (n : Nat) (X : Type) (t : X → X) (u : Product (Remainder (suc. n)) X)
  : Id (Product (Fin (suc. n)) X) (root_finite_decode n X (root_remainder n X t u))
      (root_finite n X t (root_finite_decode n X u))
  ≔ inverse (Product (Fin (suc. n)) X) (root_finite n X t (root_finite_decode n X u))
      (root_finite_decode n X (root_remainder n X t u))
      (refl ((v ↦ root_finite_decode n X (root_remainder n X t v)) : Product (Remainder (suc. n)) X → Product (Fin (suc. n)) X)
        (root_finite_encode_decode n X u))

def inverse_at_known_point (A B : Type) (e : Equiv A B) (a : A) (b : B) (p : Id B (e .map a) b)
  : Id A (equiv_inverse_map A B e b) a
  ≔ equivalence_injective A B e (equiv_inverse_map A B e b) a (calc
      e .map (equiv_inverse_map A B e b) = b by equiv_counit A B e b
      = e .map a by p ∎)

def finite_decode_zero (n : Nat)
  : Id (Fin (suc. n)) (equiv_inverse_map (Fin (suc. n)) (Remainder (suc. n))
      (fin_book_below_equiv (suc. n)) (remainder_at n zero. star.)) (inr. star.)
  ≔ inverse_at_known_point (Fin (suc. n)) (Remainder (suc. n)) (fin_book_below_equiv (suc. n))
      (inr. star.) (remainder_at n zero. star.)
      (remainder_equal (suc. n) (fin_book_below_equiv (suc. n) .map (inr. star.)) (remainder_at n zero. star.) (refl zero.))

def modular_successor_remainder_small (n : Nat) (r : Remainder (suc. n)) (small : Lt (r .fst) n)
  : Id (Remainder (suc. n)) (modular_successor n r) (remainder_at n (suc. (r .fst)) small)
  ≔ let h ≔ lt_from_book (r .fst) (suc. n) (r .snd) in
    calc
      modular_successor n r = modular_successor n (remainder_at n (r .fst) h)
        by refl (modular_successor n) (remainder_equal (suc. n) r (remainder_at n (r .fst) h) (refl (r .fst)))
      = remainder_at n (suc. (r .fst)) small by modular_successor_small n (r .fst) small h ∎

def root_finite_small (n : Nat) (X : Type) (t : X → X) (k : Fin (suc. n))
  (small : Lt (fin_book_below_equiv (suc. n) .map k .fst) n) (x : X)
  : Id (Product (Fin (suc. n)) X) (root_finite n X t (k, x)) (finite_fin_successor n .map k, x)
  ≔ let r ≔ fin_book_below_equiv (suc. n) .map k in
    let g ≔ equiv_inverse_map (Fin (suc. n)) (Remainder (suc. n)) (fin_book_below_equiv (suc. n)) in
    calc
      root_finite n X t (k, x) = root_finite_decode n X (remainder_at n (suc. (r .fst)) small, x)
        by refl (root_finite_decode n X) (root_remainder_small n X t r small x)
      = (finite_fin_successor n .map k, x)
        by (refl g (inverse (Remainder (suc. n)) (modular_successor n r) (remainder_at n (suc. (r .fst)) small)
          (modular_successor_remainder_small n r small)), refl x) ∎

def root_finite_last (n : Nat) (X : Type) (t : X → X) (k : Fin (suc. n))
  (last : Id Nat (fin_book_below_equiv (suc. n) .map k .fst) n) (x : X)
  : Id (Product (Fin (suc. n)) X) (root_finite n X t (k, x)) (inr. star., t x)
  ≔ calc
      root_finite n X t (k, x) = root_finite_decode n X (remainder_at n zero. star., t x)
        by refl (root_finite_decode n X) (root_remainder_last_at n X t (fin_book_below_equiv (suc. n) .map k) last x)
      = ((inr. star., t x) : Product (Fin (suc. n)) X) by (finite_decode_zero n, refl (t x)) ∎

def root_finite_full_turn (n : Nat) (X : Type) (t : X → X) (u : Product (Fin (suc. n)) X)
  : Id (Product (Fin (suc. n)) X) (iterate (Product (Fin (suc. n)) X) (root_finite n X t) (suc. n) u) (u .fst, t (u .snd))
  ≔ let F ≔ Product (Fin (suc. n)) X in let R ≔ Product (Remainder (suc. n)) X in
    calc
      iterate F (root_finite n X t) (suc. n) u = iterate F (root_finite n X t) (suc. n) (root_finite_decode n X (root_finite_encode n X u))
        by refl (iterate F (root_finite n X t) (suc. n)) (root_finite_decode_encode n X u)
      = root_finite_decode n X (iterate R (root_remainder n X t) (suc. n) (root_finite_encode n X u))
        by iterate_intertwine R F (root_remainder n X t) (root_finite n X t) (root_finite_decode n X)
          (root_finite_decode_step n X t) (suc. n) (root_finite_encode n X u)
      = root_finite_decode n X (root_finite_encode n X u .fst, t (u .snd))
        by refl (root_finite_decode n X) (root_remainder_full_turn n X t (root_finite_encode n X u))
      = (u .fst, t (u .snd)) by
        (equiv_retraction (Fin (suc. n)) (Remainder (suc. n)) (fin_book_below_equiv (suc. n)) (u .fst), refl (t (u .snd))) ∎

def root_finite_equiv (n : Nat) (X : Type) (e : Equiv X X)
  : Equiv (Product (Fin (suc. n)) X) (Product (Fin (suc. n)) X)
  ≔ compose_equiv (Product (Fin (suc. n)) X) (Product (Remainder (suc. n)) X) (Product (Fin (suc. n)) X)
      (compose_equiv (Product (Fin (suc. n)) X) (Product (Remainder (suc. n)) X) (Product (Remainder (suc. n)) X)
        (root_finite_coordinates n X) (root_remainder_equiv n X e)) (root_finite_coordinates_inverse n X)

def root_finite_cyclic (n : Nat) (X : Type) (e : Equiv X X) (c : Cyclic X e)
  : Cyclic (Product (Fin (suc. n)) X) (root_finite_equiv n X e)
  ≔ cyclic_transfer (Product (Remainder (suc. n)) X) (Product (Fin (suc. n)) X)
      (root_remainder_equiv n X e) (root_finite_equiv n X e) (root_finite_coordinates_inverse n X)
      (root_finite_decode_step n X (e .map)) (root_remainder_cyclic n X e c)

{` def:root, on the whole universe of endomorphisms, rather than only
   on sets, permutations, or cycles. `}
def formal_root (n : Nat) (u : Endomorphisms) : Endomorphisms
  ≔ (Product (Fin (suc. n)) (u .fst), root_finite n (u .fst) (u .snd))

def cycle_root (n : Nat) (c : Cycles) : Cycles
  ≔ (((Product (Fin (suc. n)) (c .fst .fst .fst),
        sigma_set (Fin (suc. n)) (_ ↦ c .fst .fst .fst) (fin_set (suc. n)) (_ ↦ c .fst .fst .snd)),
      root_finite_equiv n (c .fst .fst .fst) (c .fst .snd)),
      root_finite_cyclic n (c .fst .fst .fst) (c .fst .snd) (c .snd))

def cycle_root_endomorphism (n : Nat) (c : Cycles)
  : Id Endomorphisms (cycle_endomorphism (cycle_root n c)) (formal_root n (cycle_endomorphism c))
  ≔ refl (formal_root n (cycle_endomorphism c))
