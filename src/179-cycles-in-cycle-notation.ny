export "178-binomial-subsets"

{` The orbit list [x, f x, ..., f^{k-1} x]. `}
def iterate_list (A : Type) (f : A → A) (x : A) (k : Nat) : List A
  ≔ match k [ zero. ↦ nil. | suc. k ↦ cons. x (iterate_list A f (f x) k) ]

def iterate_list_length (A : Type) (f : A → A) (x : A) (k : Nat) : Id Nat (length A (iterate_list A f x k)) k
  ≔ match k [ zero. ↦ refl (zero. : Nat) | suc. k ↦ suc. (iterate_list_length A f (f x) k) ]

def iterate_shift (A : Type) (f : A → A) (i : Nat) (x : A)
  : Id A (iterate A f i (f x)) (iterate A f (suc. i) x)
  ≔ match i [ zero. ↦ refl (f x) | suc. i ↦ refl f (iterate_shift A f i x) ]

def InjectiveBelow (A : Type) (f : A → A) (x : A) (k : Nat) : Type
  ≔ (i j : Nat) → Lt i k → Lt j k → Id A (iterate A f i x) (iterate A f j x) → Id Nat i j

def injective_below_shift (A : Type) (f : A → A) (x : A) (k : Nat) (inj : InjectiveBelow A f x (suc. k))
  : InjectiveBelow A f (f x) k
  ≔ i j hi hj p ↦ nat_decode i j (nat_encode (suc. i) (suc. j)
      (inj (suc. i) (suc. j) hi hj
        (concat A (iterate A f (suc. i) x) (iterate A f i (f x)) (iterate A f (suc. j) x)
          (inverse A (iterate A f i (f x)) (iterate A f (suc. i) x) (iterate_shift A f i x))
          (concat A (iterate A f i (f x)) (iterate A f j (f x)) (iterate A f (suc. j) x) p (iterate_shift A f j x)))))

def injective_below_not_start (A : Type) (f : A → A) (x : A) (k j : Nat) (inj : InjectiveBelow A f x (suc. k))
  (hj : Lt (suc. j) (suc. k)) : Not (Id A (iterate A f (suc. j) x) x)
  ≔ p ↦ nat_encode (suc. j) zero. (inj (suc. j) zero. hj star. p)

{` In the orbit list with k+1 entries, entry i < k is sent to entry i+1. `}
def iterate_list_lookup_small (A : Type) (d : DecidableEquality A) (f : A → A) (first x : A) (k : Nat)
  (inj : InjectiveBelow A f x (suc. k)) (i : Nat) (hi : Lt i k)
  : Id A (cycle_lookup A d first (iterate_list A f x (suc. k)) (iterate A f i x)) (iterate A f (suc. i) x)
  ≔ match i [
  | zero. ↦ match k [
    | zero. ↦ match hi []
    | suc. k ↦ decide_branch_yes A (Id A x x) (d x x) (f x)
        (cycle_lookup A d first (iterate_list A f (f x) (suc. k)) x) (refl x) ]
  | suc. j ↦ match k [
    | zero. ↦ match hi []
    | suc. k ↦ calc
        cycle_lookup A d first (iterate_list A f x (suc. (suc. k))) (iterate A f (suc. j) x)
        = cycle_lookup A d first (iterate_list A f (f x) (suc. k)) (iterate A f (suc. j) x)
          by decide_branch_no A (Id A (iterate A f (suc. j) x) x) (d (iterate A f (suc. j) x) x) (f x)
            (cycle_lookup A d first (iterate_list A f (f x) (suc. k)) (iterate A f (suc. j) x))
            (injective_below_not_start A f x (suc. k) j inj (le_step (suc. j) k hi))
        = cycle_lookup A d first (iterate_list A f (f x) (suc. k)) (iterate A f j (f x))
          by refl (cycle_lookup A d first (iterate_list A f (f x) (suc. k)))
            (inverse A (iterate A f j (f x)) (iterate A f (suc. j) x) (iterate_shift A f j x))
        = iterate A f (suc. j) (f x)
          by iterate_list_lookup_small A d f first (f x) k (injective_below_shift A f x (suc. k) inj) j hi
        = iterate A f (suc. (suc. j)) x by iterate_shift A f (suc. j) x ∎ ] ]

{` The last entry is sent to the given first point. `}
def iterate_list_lookup_last (A : Type) (d : DecidableEquality A) (f : A → A) (first x : A) (k : Nat)
  (inj : InjectiveBelow A f x (suc. k))
  : Id A (cycle_lookup A d first (iterate_list A f x (suc. k)) (iterate A f k x)) first
  ≔ match k [
  | zero. ↦ decide_branch_yes A (Id A x x) (d x x) first (cycle_lookup A d first nil. x) (refl x)
  | suc. k ↦ calc
      cycle_lookup A d first (iterate_list A f x (suc. (suc. k))) (iterate A f (suc. k) x)
      = cycle_lookup A d first (iterate_list A f (f x) (suc. k)) (iterate A f (suc. k) x)
        by decide_branch_no A (Id A (iterate A f (suc. k) x) x) (d (iterate A f (suc. k) x) x) (f x)
          (cycle_lookup A d first (iterate_list A f (f x) (suc. k)) (iterate A f (suc. k) x))
          (injective_below_not_start A f x (suc. k) k inj (le_refl k))
      = cycle_lookup A d first (iterate_list A f (f x) (suc. k)) (iterate A f k (f x))
        by refl (cycle_lookup A d first (iterate_list A f (f x) (suc. k)))
          (inverse A (iterate A f k (f x)) (iterate A f (suc. k) x) (iterate_shift A f k x))
      = first by iterate_list_lookup_last A d f first (f x) k (injective_below_shift A f x (suc. k) inj) ∎ ]

def iterate_list_not_in (A : Type) (f : A → A) (x y : A) (len : Nat)
  (hy : (j : Nat) → Lt j len → Not (Id A (iterate A f j y) x)) : NotInList A x (iterate_list A f y len)
  ≔ match len [
  | zero. ↦ star.
  | suc. len ↦ (p ↦ hy zero. star. (inverse A x y p),
      iterate_list_not_in A f x (f y) len
        (j hj p ↦ hy (suc. j) hj (concat A (iterate A f (suc. j) y) (iterate A f j (f y)) x
          (inverse A (iterate A f j (f y)) (iterate A f (suc. j) y) (iterate_shift A f j y)) p))) ]

def iterate_list_distinct (A : Type) (f : A → A) (x : A) (k : Nat) (inj : InjectiveBelow A f x k)
  : PairwiseDistinct A (iterate_list A f x k)
  ≔ match k [
  | zero. ↦ star.
  | suc. k ↦ (iterate_list_not_in A f x (f x) k
        (j hj p ↦ injective_below_not_start A f x k j inj hj
          (concat A (iterate A f (suc. j) x) (iterate A f j (f x)) x
            (inverse A (iterate A f j (f x)) (iterate A f (suc. j) x) (iterate_shift A f j x)) p)),
      iterate_list_distinct A f (f x) k (injective_below_shift A f x k inj)) ]

{` The iterates of a point below the least period are distinct. `}
def cycle_iterates_injective (c : Cycles) (n : Nat) (minimal : IsMinimum (PositiveCyclePeriod c) n)
  (x : c .fst .fst .fst) : InjectiveBelow (c .fst .fst .fst) (c .fst .snd .map) x (suc. n)
  ≔ i j hi hj p ↦ cycle_remainder_injective c n minimal x (i, lt_to_book i (suc. n) hi) (j, lt_to_book j (suc. n) hj) p .fst

{` rem:cycle-vs-cycle: a cycle (X,t) whose least period is n+1, for instance
   a finite cycle with n+1 elements, is the cyclic permutation
   (x_0 t(x_0) ... t^n(x_0)) of pairwise distinct entries, for any x_0. `}
def cycle_orbit_notation_at (c : Cycles) (n : Nat) (minimal : IsMinimum (PositiveCyclePeriod c) n)
  (d : DecidableEquality (c .fst .fst .fst)) (x0 : c .fst .fst .fst) (y : c .fst .fst .fst)
  : Id (c .fst .fst .fst)
      (cycle_notation (c .fst .fst .fst) d x0 (iterate_list (c .fst .fst .fst) (c .fst .snd .map) (c .fst .snd .map x0) n) y)
      (c .fst .snd .map y)
  ≔ let X ≔ c .fst .fst .fst in
    let t ≔ c .fst .snd .map in
    let C ≔ cycle_notation X d x0 (iterate_list X t (t x0) n) in
    let inj ≔ cycle_iterates_injective c n minimal x0 in
    mere_rec (BookFiber (Remainder (suc. n)) X (cycle_remainder_map c (suc. n) x0) y) (Id X (C y) (t y))
      (c .fst .fst .snd (C y) (t y))
      (u ↦ transport X (z ↦ Id X (C z) (t z)) (iterate X t (u .fst .fst) x0) y
        (inverse X y (iterate X t (u .fst .fst) x0) (u .snd))
        (match le_split (u .fst .fst) n (lt_from_book (u .fst .fst) (suc. n) (u .fst .snd)) [
        | inl. small ↦ iterate_list_lookup_small X d t x0 x0 n inj (u .fst .fst) small
        | inr. last ↦ transport Nat (i ↦ Id X (C (iterate X t i x0)) (t (iterate X t i x0))) n (u .fst .fst)
            (inverse Nat (u .fst .fst) n last)
            (concat X (C (iterate X t n x0)) x0 (t (iterate X t n x0))
              (iterate_list_lookup_last X d t x0 x0 n inj)
              (inverse X (iterate X t (suc. n) x0) x0 (minimal .fst (refl x0)))) ]))
      (cycle_remainder_surjective c (suc. n) (lt_to_book zero. (suc. n) star.) (minimal .fst) x0 y)

def cycle_orbit_notation (c : Cycles) (n : Nat) (minimal : IsMinimum (PositiveCyclePeriod c) n)
  (d : DecidableEquality (c .fst .fst .fst)) (x0 : c .fst .fst .fst)
  : Id (c .fst .fst .fst → c .fst .fst .fst)
      (cycle_notation (c .fst .fst .fst) d x0 (iterate_list (c .fst .fst .fst) (c .fst .snd .map) (c .fst .snd .map x0) n))
      (c .fst .snd .map)
  ≔ funext (c .fst .fst .fst) (_ ↦ c .fst .fst .fst)
      (cycle_notation (c .fst .fst .fst) d x0 (iterate_list (c .fst .fst .fst) (c .fst .snd .map) (c .fst .snd .map x0) n))
      (c .fst .snd .map) (cycle_orbit_notation_at c n minimal d x0)

def cycle_orbit_distinct (c : Cycles) (n : Nat) (minimal : IsMinimum (PositiveCyclePeriod c) n)
  (x0 : c .fst .fst .fst)
  : PairwiseDistinct (c .fst .fst .fst) (iterate_list (c .fst .fst .fst) (c .fst .snd .map) x0 (suc. n))
  ≔ iterate_list_distinct (c .fst .fst .fst) (c .fst .snd .map) x0 (suc. n) (cycle_iterates_injective c n minimal x0)

{` For a finite cycle the list length is the cardinality of the carrier. `}
def finite_cycle_orbit_notation (c : Cycles) (finite : IsFinite (c .fst .fst .fst)) (x0 : c .fst .fst .fst)
  : Id (c .fst .fst .fst → c .fst .fst .fst)
      (cycle_notation (c .fst .fst .fst) (finite_decidable_equality (c .fst .fst .fst) finite) x0
        (iterate_list (c .fst .fst .fst) (c .fst .snd .map) (c .fst .snd .map x0) (finite_cycle_minimum c finite .fst)))
      (c .fst .snd .map)
  ≔ cycle_orbit_notation c (finite_cycle_minimum c finite .fst) (finite_cycle_minimum c finite .snd)
      (finite_decidable_equality (c .fst .fst .fst) finite) x0

def finite_cycle_orbit_length (c : Cycles) (finite : IsFinite (c .fst .fst .fst)) (x0 : c .fst .fst .fst)
  : Id Nat (length (c .fst .fst .fst)
      (iterate_list (c .fst .fst .fst) (c .fst .snd .map) x0 (suc. (finite_cycle_minimum c finite .fst))))
      (cardinality (c .fst .fst .fst) finite)
  ≔ concat Nat (length (c .fst .fst .fst)
      (iterate_list (c .fst .fst .fst) (c .fst .snd .map) x0 (suc. (finite_cycle_minimum c finite .fst))))
      (suc. (finite_cycle_minimum c finite .fst)) (cardinality (c .fst .fst .fst) finite)
      (iterate_list_length (c .fst .fst .fst) (c .fst .snd .map) x0 (suc. (finite_cycle_minimum c finite .fst)))
      (inverse Nat (cardinality (c .fst .fst .fst) finite) (suc. (finite_cycle_minimum c finite .fst))
        (finite_cycle_cardinality c finite))

{` A cyclic permutation moves only points of its list. `}
def cycle_notation_support (A : Type) (d : DecidableEquality A) (a1 : A) (rest : List A) (x : A)
  (moved : Not (Id A (cycle_notation A d a1 rest x) x)) : Not (NotInList A x (cons. a1 rest))
  ≔ h ↦ moved (cycle_notation_fixed A d a1 rest x h)

def int_list_bound (l : List Int) : Nat
  ≔ match l [ nil. ↦ zero. | cons. a rest ↦ add (int_list_bound rest) (int_magnitude a) ]

def int_list_avoid (l : List Int) (B : Nat) (hb : BookLe (int_list_bound l) B)
  : NotInList Int (pos. (suc. B)) l
  ≔ match l [
  | nil. ↦ star.
  | cons. a rest ↦
      (p ↦ lt_irrefl B (transport Nat (m ↦ Le m B) (int_magnitude a) (suc. B)
          (inverse Nat (suc. B) (int_magnitude a) (refl int_magnitude p))
          (le_from_book (int_magnitude a) B
            (book_le_trans (int_magnitude a) (int_list_bound (cons. a rest)) B
              (int_list_bound rest, refl (int_list_bound (cons. a rest))) hb))),
       int_list_avoid rest B
         (book_le_trans (int_list_bound rest) (int_list_bound (cons. a rest)) B
           (int_magnitude a, add_comm (int_magnitude a) (int_list_bound rest)) hb)) ]

{` The infinite cycle (Z, succ) is not a cyclic permutation (a_1 ... a_k). `}
def integer_successor_not_cycle_notation (d : DecidableEquality Int) (a1 : Int) (rest : List Int)
  (p : Id (Int → Int) (cycle_notation Int d a1 rest) int_succ) : Empty
  ≔ let B ≔ int_list_bound (cons. a1 rest) in
    let x : Int ≔ pos. (suc. B) in
    let q : Id Int x (int_succ x)
      ≔ concat Int x (cycle_notation Int d a1 rest x) (int_succ x)
          (inverse Int (cycle_notation Int d a1 rest x) x
            (cycle_notation_fixed Int d a1 rest x (int_list_avoid (cons. a1 rest) B (zero., add_zero_left B))))
          (p (refl x)) in
    lt_irrefl B (le_from_equal (suc. (suc. B)) (suc. B)
      (inverse Nat (suc. B) (suc. (suc. B)) (nat_decode (suc. B) (suc. (suc. B)) (int_encode x (int_succ x) q))))
