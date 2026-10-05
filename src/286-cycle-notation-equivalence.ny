export "244-k-cycle-count"
export "224-constructed-circle-checks"

{` The two representations of k-cycles agree (k = j+2 ≥ 2).  Module 174
   writes (a_1 a_2 ... a_k) for a list a_1 :: rest of pairwise distinct
   entries and defines the permutation by lookup (cycle_notation).  Module
   243 describes a k-cycle σ by an injective enumeration a : Z/k → A with
   σ(a i) = a(i+1) that fixes every other point (KCycleEnumeration).  Both
   encodings fix a base point, a_1 = a(0), so the comparison needs no
   identification up to rotation: the list of an enumeration is
   [a(0), a(1), ..., a(k-1)]. `}

{` Lists: images, tails, entries by index. `}
def cycle_list_map (X A : Type) (h : X → A) (l : List X) : List A
  ≔ match l [ nil. ↦ nil. | cons. x rest ↦ cons. (h x) (cycle_list_map X A h rest) ]

def cycle_list_map_length (X A : Type) (h : X → A) (l : List X)
  : Id Nat (length A (cycle_list_map X A h l)) (length X l)
  ≔ match l [ nil. ↦ refl (zero. : Nat) | cons. x rest ↦ suc. (cycle_list_map_length X A h rest) ]

def cycle_list_tail (A : Type) (l : List A) : List A
  ≔ match l [ nil. ↦ nil. | cons. _ rest ↦ rest ]

def cycle_list_entry (A : Type) (l : List A) (default : A) (i : Nat) : A
  ≔ match l [
  | nil. ↦ default
  | cons. x rest ↦ match i [ zero. ↦ x | suc. i ↦ cycle_list_entry A rest default i ] ]

def not_in_list_prop (A : Type) (x : A) (l : List A) : isProp (NotInList A x l)
  ≔ match l [
  | nil. ↦ unit_prop
  | cons. a rest ↦ product_prop (Not (Id A x a)) (NotInList A x rest) (negation_prop (Id A x a))
      (not_in_list_prop A x rest) ]

def pairwise_distinct_prop (A : Type) (l : List A) : isProp (PairwiseDistinct A l)
  ≔ match l [
  | nil. ↦ unit_prop
  | cons. a rest ↦ product_prop (NotInList A a rest) (PairwiseDistinct A rest) (not_in_list_prop A a rest)
      (pairwise_distinct_prop A rest) ]

def not_in_list_decide (A : Type) (d : DecidableEquality A) (x : A) (l : List A) : Decidable (NotInList A x l)
  ≔ match l [
  | nil. ↦ inl. star.
  | cons. a rest ↦ match d x a [
    | inl. p ↦ inr. (h ↦ h .fst p)
    | inr. n ↦ match not_in_list_decide A d x rest [
      | inl. h ↦ inl. (n, h)
      | inr. no ↦ inr. (h ↦ no (h .snd)) ] ] ]

def map_not_in_list (X A : Type) (h : X → A) (inj : PathReflecting X A h) (x : X) (l : List X)
  (hx : NotInList X x l) : NotInList A (h x) (cycle_list_map X A h l)
  ≔ match l [
  | nil. ↦ star.
  | cons. y rest ↦ ((p ↦ hx .fst (inj x y p)), map_not_in_list X A h inj x rest (hx .snd)) ]

def map_pairwise_distinct (X A : Type) (h : X → A) (inj : PathReflecting X A h) (l : List X)
  (hl : PairwiseDistinct X l) : PairwiseDistinct A (cycle_list_map X A h l)
  ≔ match l [
  | nil. ↦ star.
  | cons. y rest ↦ (map_not_in_list X A h inj y rest (hl .fst), map_pairwise_distinct X A h inj rest (hl .snd)) ]

def map_not_in_image (X A : Type) (h : X → A) (a : A) (no : (x : X) → Not (Id A a (h x))) (l : List X)
  : NotInList A a (cycle_list_map X A h l)
  ≔ match l [ nil. ↦ star. | cons. y rest ↦ (no y, map_not_in_image X A h a no rest) ]

def map_list_member (X A : Type) (d : DecidableEquality A) (h : X → A) (a : A) (l : List X)
  (m : Not (NotInList A a (cycle_list_map X A h l))) : Σ X (x ↦ Id A a (h x))
  ≔ match l [
  | nil. ↦ absurd (Σ X (x ↦ Id A a (h x))) (m star.)
  | cons. y rest ↦ match d a (h y) [
    | inl. p ↦ (y, p)
    | inr. n ↦ map_list_member X A d h a rest (hr ↦ m (n, hr)) ] ]

{` Cycle notation is natural along injections: the image of a list under
   an injective h denotes the conjugated lookup. `}
def cycle_next_head_map (X A : Type) (h : X → A) (first : X) (rest : List X)
  : Id A (cycle_next_head A (h first) (cycle_list_map X A h rest)) (h (cycle_next_head X first rest))
  ≔ match rest [ nil. ↦ refl (h first) | cons. b _ ↦ refl (h b) ]

def cycle_lookup_map (X A : Type) (dX : DecidableEquality X) (dA : DecidableEquality A) (h : X → A)
  (inj : PathReflecting X A h) (first : X) (l : List X) (x : X)
  : Id A (cycle_lookup A dA (h first) (cycle_list_map X A h l) (h x)) (h (cycle_lookup X dX first l x))
  ≔ match l [
  | nil. ↦ refl (h x)
  | cons. b rest ↦
      let nextA ≔ cycle_next_head A (h first) (cycle_list_map X A h rest) in
      let restA ≔ cycle_lookup A dA (h first) (cycle_list_map X A h rest) (h x) in
      let nextX ≔ cycle_next_head X first rest in
      let restX ≔ cycle_lookup X dX first rest x in
      match dX x b [
      | inl. p ↦ calc
          decide_branch A (Id A (h x) (h b)) (dA (h x) (h b)) nextA restA = nextA
            by decide_branch_yes A (Id A (h x) (h b)) (dA (h x) (h b)) nextA restA (refl h p)
          = h nextX by cycle_next_head_map X A h first rest
          = h (decide_branch X (Id X x b) (dX x b) nextX restX)
            by refl h (inverse X (decide_branch X (Id X x b) (dX x b) nextX restX) nextX
              (decide_branch_yes X (Id X x b) (dX x b) nextX restX p)) ∎
      | inr. n ↦ calc
          decide_branch A (Id A (h x) (h b)) (dA (h x) (h b)) nextA restA = restA
            by decide_branch_no A (Id A (h x) (h b)) (dA (h x) (h b)) nextA restA (q ↦ n (inj x b q))
          = h restX by cycle_lookup_map X A dX dA h inj first rest x
          = h (decide_branch X (Id X x b) (dX x b) nextX restX)
            by refl h (inverse X (decide_branch X (Id X x b) (dX x b) nextX restX) restX
              (decide_branch_no X (Id X x b) (dX x b) nextX restX n)) ∎ ] ]

{` Entries of images of orbit lists [x, f x, ..., f^{n-1} x]. `}
def iterate_list_map_entry (X A : Type) (f : X → X) (h : X → A) (default : A) (x : X) (n i : Nat)
  (hi : Lt i n)
  : Id A (cycle_list_entry A (cycle_list_map X A h (iterate_list X f x n)) default i) (h (iterate X f i x))
  ≔ match n [
  | zero. ↦ match hi []
  | suc. n ↦ match i [
    | zero. ↦ refl (h x)
    | suc. i ↦ concat A (cycle_list_entry A (cycle_list_map X A h (iterate_list X f (f x) n)) default i)
        (h (iterate X f i (f x))) (h (iterate X f (suc. i) x))
        (iterate_list_map_entry X A f h default (f x) n i hi)
        (refl h (iterate_shift X f i x)) ] ]

def iterate_list_map_by_entries (X A : Type) (f : X → X) (h : X → A) (default : A) (l : List A) (x : X)
  (n : Nat) (len : Id Nat (length A l) n)
  (hyp : (i : Nat) → Lt i n → Id A (h (iterate X f i x)) (cycle_list_entry A l default i))
  : Id (List A) (cycle_list_map X A h (iterate_list X f x n)) l
  ≔ match l, n [
  | nil., zero. ↦ refl (nil. : List A)
  | nil., suc. n ↦ absurd (Id (List A) (cons. (h x) (cycle_list_map X A h (iterate_list X f (f x) n))) nil.)
      (nat_encode zero. (suc. n) len)
  | cons. y rest, zero. ↦ absurd (Id (List A) nil. (cons. y rest)) (nat_encode (suc. (length A rest)) zero. len)
  | cons. y rest, suc. n ↦ cons. (hyp zero. star.)
      (iterate_list_map_by_entries X A f h default rest (f x) n (refl nat_pred len)
        (i hi ↦ concat A (h (iterate X f i (f x))) (h (iterate X f (suc. i) x)) (cycle_list_entry A rest default i)
          (refl h (iterate_shift X f i x)) (hyp (suc. i) hi))) ]

def not_in_map_iterate (X A : Type) (h : X → A) (f : X → X) (a : A) (x : X) (n : Nat)
  (hn : NotInList A a (cycle_list_map X A h (iterate_list X f x n))) (i : Nat) (hi : Lt i n)
  : Not (Id A a (h (iterate X f i x)))
  ≔ match n [
  | zero. ↦ match hi []
  | suc. n ↦ match i [
    | zero. ↦ hn .fst
    | suc. i ↦ p ↦ not_in_map_iterate X A h f a (f x) n (hn .snd) i hi
        (concat A a (h (iterate X f (suc. i) x)) (h (iterate X f i (f x))) p
          (refl h (inverse X (iterate X f i (f x)) (iterate X f (suc. i) x) (iterate_shift X f i x)))) ] ]

def cycle_list_entry_not_in (A : Type) (y : A) (l : List A) (default : A) (h : NotInList A y l) (i : Nat)
  (hi : Lt i (length A l)) : Not (Id A y (cycle_list_entry A l default i))
  ≔ match l [
  | nil. ↦ match hi []
  | cons. x rest ↦ match i [
    | zero. ↦ h .fst
    | suc. i ↦ cycle_list_entry_not_in A y rest default (h .snd) i hi ] ]

def cycle_list_entry_injective (A : Type) (l : List A) (default : A) (hl : PairwiseDistinct A l) (i i' : Nat)
  (hi : Lt i (length A l)) (hi' : Lt i' (length A l))
  (p : Id A (cycle_list_entry A l default i) (cycle_list_entry A l default i')) : Id Nat i i'
  ≔ match l [
  | nil. ↦ match hi []
  | cons. x rest ↦ match i, i' [
    | zero., zero. ↦ refl (zero. : Nat)
    | zero., suc. i' ↦ absurd (Id Nat zero. (suc. i'))
        (cycle_list_entry_not_in A x rest default (hl .fst) i' hi' p)
    | suc. i, zero. ↦ absurd (Id Nat (suc. i) zero.)
        (cycle_list_entry_not_in A x rest default (hl .fst) i hi (inverse A (cycle_list_entry A rest default i) x p))
    | suc. i, suc. i' ↦ suc. (cycle_list_entry_injective A rest default (hl .snd) i i' hi hi' p) ] ]

def cycle_injective_prop (X A : Type) (h : X → A) (hX : isSet X) : isProp (PathReflecting X A h)
  ≔ pi_prop X (x ↦ (y : X) → Id A (h x) (h y) → Id X x y)
      (x ↦ pi_prop X (y ↦ Id A (h x) (h y) → Id X x y)
        (y ↦ pi_prop (Id A (h x) (h y)) (_ ↦ Id X x y) (_ ↦ hX x y)))

{` In Z/(n+1), r = s^r(0). `}
def remainder_iterate_base (n : Nat) (r : Remainder (suc. n))
  : Id (Remainder (suc. n)) (iterate (Remainder (suc. n)) (modular_successor n) (r .fst) (remainder_at n zero. star.)) r
  ≔ let h ≔ lt_from_book (r .fst) (suc. n) (r .snd) in
    concat (Remainder (suc. n)) (iterate (Remainder (suc. n)) (modular_successor n) (r .fst) (remainder_at n zero. star.))
      (remainder_at n (r .fst) h) r
      (modular_successor_iterate n (r .fst) h)
      (remainder_equal (suc. n) (remainder_at n (r .fst) h) r (refl (r .fst)))

{` The two types of data.  PathReflecting enumerations a : Z/k → A, and lists
   a_1 :: rest of k pairwise distinct entries, k = j+2. `}
def InjectiveCycleEnumerations (A : Type) (j : Nat) : Type
  ≔ Σ (Remainder (suc. (suc. j)) → A) (PathReflecting (Remainder (suc. (suc. j))) A)

def CycleNotationLists (A : Type) (j : Nat) : Type
  ≔ Σ A (a1 ↦ Σ (List A) (rest ↦ Product (Id Nat (length A rest) (suc. j)) (PairwiseDistinct A (cons. a1 rest))))

{` The permutation (a_1 ... a_k) of module 174 denoted by such a list. `}
def cycle_notation_list_equiv (A : Type) (d : DecidableEquality A) (j : Nat) (l : CycleNotationLists A j) : Equiv A A
  ≔ cycle_notation_equiv A d (l .fst) (l .snd .fst) (l .snd .snd .snd)

{` [a(1), ..., a(k-1)]; the list of a is a(0) :: enumeration_rest. `}
def enumeration_rest (A : Type) (j : Nat) (a : Remainder (suc. (suc. j)) → A) : List A
  ≔ cycle_list_map (Remainder (suc. (suc. j))) A a
      (iterate_list (Remainder (suc. (suc. j))) (modular_successor (suc. j))
        (modular_successor (suc. j) (remainder_at (suc. j) zero. star.)) (suc. j))

def enumeration_to_list (A : Type) (j : Nat) (w : InjectiveCycleEnumerations A j) : CycleNotationLists A j
  ≔ let R ≔ Remainder (suc. (suc. j)) in
    let s ≔ modular_successor (suc. j) in
    let r0 ≔ remainder_at (suc. j) zero. star. in
    (w .fst r0, (enumeration_rest A j (w .fst),
      (concat Nat (length A (enumeration_rest A j (w .fst))) (length R (iterate_list R s (s r0) (suc. j))) (suc. j)
         (cycle_list_map_length R A (w .fst) (iterate_list R s (s r0) (suc. j)))
         (iterate_list_length R s (s r0) (suc. j)),
       map_pairwise_distinct R A (w .fst) (w .snd) (iterate_list R s r0 (suc. (suc. j)))
         (cycle_orbit_distinct (finite_standard_cycle (suc. j)) (suc. j) (finite_standard_minimum (suc. j)) r0))))

{` a(i) = a_{i+1}, the entry at position i of a_1 :: rest. `}
def list_to_enumeration (A : Type) (j : Nat) (l : CycleNotationLists A j) : InjectiveCycleEnumerations A j
  ≔ let R ≔ Remainder (suc. (suc. j)) in
    let full : List A ≔ cons. (l .fst) (l .snd .fst) in
    let bound ≔ ((r ↦ transport Nat (m ↦ Lt (r .fst) (suc. m)) (suc. j) (length A (l .snd .fst))
        (inverse Nat (length A (l .snd .fst)) (suc. j) (l .snd .snd .fst))
        (lt_from_book (r .fst) (suc. (suc. j)) (r .snd))) : (r : R) → Lt (r .fst) (length A full)) in
    ((r ↦ cycle_list_entry A full (l .fst) (r .fst)),
     (r r' p ↦ remainder_equal (suc. (suc. j)) r r'
        (cycle_list_entry_injective A full (l .fst) (l .snd .snd .snd) (r .fst) (r' .fst) (bound r) (bound r') p)))

def enumeration_list_roundtrip (A : Type) (j : Nat) (w : InjectiveCycleEnumerations A j)
  : Id (InjectiveCycleEnumerations A j) (list_to_enumeration A j (enumeration_to_list A j w)) w
  ≔ let R ≔ Remainder (suc. (suc. j)) in
    let s ≔ modular_successor (suc. j) in
    let r0 ≔ remainder_at (suc. j) zero. star. in
    subtype_equal (R → A) (PathReflecting R A) (a ↦ cycle_injective_prop R A a (remainder_set (suc. (suc. j))))
      (list_to_enumeration A j (enumeration_to_list A j w)) w
      (funext R (_ ↦ A) (list_to_enumeration A j (enumeration_to_list A j w) .fst) (w .fst)
        (r ↦ concat A
           (cycle_list_entry A (cycle_list_map R A (w .fst) (iterate_list R s r0 (suc. (suc. j)))) (w .fst r0) (r .fst))
           (w .fst (iterate R s (r .fst) r0)) (w .fst r)
           (iterate_list_map_entry R A s (w .fst) (w .fst r0) r0 (suc. (suc. j)) (r .fst)
             (lt_from_book (r .fst) (suc. (suc. j)) (r .snd)))
           (refl (w .fst) (remainder_iterate_base (suc. j) r))))

def list_enumeration_roundtrip (A : Type) (j : Nat) (l : CycleNotationLists A j)
  : Id (CycleNotationLists A j) (enumeration_to_list A j (list_to_enumeration A j l)) l
  ≔ let R ≔ Remainder (suc. (suc. j)) in
    let s ≔ modular_successor (suc. j) in
    let r0 ≔ remainder_at (suc. j) zero. star. in
    let a1 ≔ l .fst in
    let full : List A ≔ cons. a1 (l .snd .fst) in
    let a ≔ list_to_enumeration A j l .fst in
    let full_path : Id (List A) (cycle_list_map R A a (iterate_list R s r0 (suc. (suc. j)))) full
      ≔ iterate_list_map_by_entries R A s a a1 full r0 (suc. (suc. j)) (suc. (l .snd .snd .fst))
          (i hi ↦ refl ((m ↦ cycle_list_entry A full a1 m) : Nat → A)
            (modular_successor_iterate (suc. j) i hi .fst)) in
    let F ≔ ((rest ↦ Product (Id Nat (length A rest) (suc. j)) (PairwiseDistinct A (cons. a1 rest))) : List A → Type) in
    refl ((t ↦ (a1, t)) : Σ (List A) F → CycleNotationLists A j)
      (subtype_equal (List A) F
        (rest ↦ product_prop (Id Nat (length A rest) (suc. j)) (PairwiseDistinct A (cons. a1 rest))
          (nat_set (length A rest) (suc. j)) (pairwise_distinct_prop A (cons. a1 rest)))
        (enumeration_to_list A j (list_to_enumeration A j l) .snd) (l .snd)
        (refl (cycle_list_tail A) full_path))

{` PathReflecting enumerations Z/k → A and pairwise distinct lists of length k
   are equivalent, a ↦ [a(0), ..., a(k-1)], for any type A. `}
def enumeration_list_equiv (A : Type) (j : Nat) : Equiv (InjectiveCycleEnumerations A j) (CycleNotationLists A j)
  ≔ quasi_inverse_equiv (InjectiveCycleEnumerations A j) (CycleNotationLists A j)
      (enumeration_to_list A j) (list_to_enumeration A j)
      (enumeration_list_roundtrip A j) (list_enumeration_roundtrip A j)

{` The cycle notation of the list of an injective enumeration a sends
   a(i) to a(i+1) and fixes every point outside the image of a. `}
def enumeration_cycle_equiv (A : Type) (d : DecidableEquality A) (j : Nat) (w : InjectiveCycleEnumerations A j)
  : Equiv A A
  ≔ cycle_notation_list_equiv A d j (enumeration_to_list A j w)

def enumeration_cycle_step (A : Type) (d : DecidableEquality A) (j : Nat) (w : InjectiveCycleEnumerations A j)
  (r : Remainder (suc. (suc. j)))
  : Id A (enumeration_cycle_equiv A d j w .map (w .fst r)) (w .fst (modular_successor (suc. j) r))
  ≔ let R ≔ Remainder (suc. (suc. j)) in
    let s ≔ modular_successor (suc. j) in
    let r0 ≔ remainder_at (suc. j) zero. star. in
    let dR ≔ remainder_decidable_equality (suc. (suc. j)) in
    concat A (cycle_lookup A d (w .fst r0) (cycle_list_map R A (w .fst) (iterate_list R s r0 (suc. (suc. j)))) (w .fst r))
      (w .fst (cycle_lookup R dR r0 (iterate_list R s r0 (suc. (suc. j))) r)) (w .fst (s r))
      (cycle_lookup_map R A dR d (w .fst) (w .snd) r0 (iterate_list R s r0 (suc. (suc. j))) r)
      (refl (w .fst) (cycle_orbit_notation_at (finite_standard_cycle (suc. j)) (suc. j)
        (finite_standard_minimum (suc. j)) dR r0 r))

def enumeration_cycle_fixed (A : Type) (d : DecidableEquality A) (j : Nat) (w : InjectiveCycleEnumerations A j)
  (x : A) (no : (r : Remainder (suc. (suc. j))) → Not (Id A x (w .fst r)))
  : Id A (enumeration_cycle_equiv A d j w .map x) x
  ≔ cycle_notation_fixed A d (w .fst (remainder_at (suc. j) zero. star.)) (enumeration_rest A j (w .fst)) x
      (map_not_in_image (Remainder (suc. (suc. j))) A (w .fst) x no
        (iterate_list (Remainder (suc. (suc. j))) (modular_successor (suc. j)) (remainder_at (suc. j) zero. star.)
          (suc. (suc. j))))

def enumeration_kcycle (A : Type) (d : DecidableEquality A) (j : Nat) (w : InjectiveCycleEnumerations A j)
  : KCycleEnumeration A j (enumeration_cycle_equiv A d j w)
  ≔ (w .fst, (w .snd, (enumeration_cycle_step A d j w, enumeration_cycle_fixed A d j w)))

{` Conversely a permutation with a k-cycle enumeration a is the cycle
   notation of the list of a: it is determined by a. `}
def kcycle_enumeration_unique_at (A : Type) (d : DecidableEquality A) (j : Nat) (σ : Equiv A A)
  (E : KCycleEnumeration A j σ) (x : A)
  : Id A (σ .map x) (enumeration_cycle_equiv A d j (E .fst, E .snd .fst) .map x)
  ≔ let R ≔ Remainder (suc. (suc. j)) in
    let s ≔ modular_successor (suc. j) in
    let r0 ≔ remainder_at (suc. j) zero. star. in
    let w : InjectiveCycleEnumerations A j ≔ (E .fst, E .snd .fst) in
    let a ≔ E .fst in
    let c ≔ enumeration_cycle_equiv A d j w .map in
    let full ≔ iterate_list R s r0 (suc. (suc. j)) in
    match not_in_list_decide A d x (cycle_list_map R A a full) [
    | inl. h ↦ concat A (σ .map x) x (c x)
        (E .snd .snd .snd x (r p ↦ not_in_map_iterate R A a s x r0 (suc. (suc. j)) h (r .fst)
            (lt_from_book (r .fst) (suc. (suc. j)) (r .snd))
            (concat A x (a r) (a (iterate R s (r .fst) r0)) p
              (refl a (inverse R (iterate R s (r .fst) r0) r (remainder_iterate_base (suc. j) r))))))
        (inverse A (c x) x (cycle_notation_fixed A d (a r0) (enumeration_rest A j a) x h))
    | inr. m ↦ let u ≔ map_list_member R A d a x full m in
        calc σ .map x = σ .map (a (u .fst)) by refl (σ .map) (u .snd)
        = a (s (u .fst)) by E .snd .snd .fst (u .fst)
        = c (a (u .fst)) by inverse A (c (a (u .fst))) (a (s (u .fst))) (enumeration_cycle_step A d j w (u .fst))
        = c x by refl c (inverse A x (a (u .fst)) (u .snd)) ∎ ]

{` A permutation σ with a k-cycle enumeration a (module 243) is the cycle
   notation (a(0) a(1) ... a(k-1)) of module 174. `}
def kcycle_enumeration_cycle_notation (A : Type) (d : DecidableEquality A) (j : Nat) (σ : Equiv A A)
  (E : KCycleEnumeration A j σ)
  : Id (Equiv A A) σ (cycle_notation_list_equiv A d j (enumeration_to_list A j (E .fst, E .snd .fst)))
  ≔ equiv_path A A σ (enumeration_cycle_equiv A d j (E .fst, E .snd .fst))
      (funext A (_ ↦ A) (σ .map) (enumeration_cycle_equiv A d j (E .fst, E .snd .fst) .map)
        (kcycle_enumeration_unique_at A d j σ E))

def KCycleLaws (A : Type) (j : Nat) (a : Remainder (suc. (suc. j)) → A) (σ : Equiv A A) : Type
  ≔ Product ((i : Remainder (suc. (suc. j))) → Id A (σ .map (a i)) (a (modular_successor (suc. j) i)))
      ((x : A) → ((i : Remainder (suc. (suc. j))) → Not (Id A x (a i))) → Id A (σ .map x) x)

def kcycle_laws_prop (A : Type) (hA : isSet A) (j : Nat) (a : Remainder (suc. (suc. j)) → A) (σ : Equiv A A)
  : isProp (KCycleLaws A j a σ)
  ≔ let R ≔ Remainder (suc. (suc. j)) in
    product_prop ((i : R) → Id A (σ .map (a i)) (a (modular_successor (suc. j) i)))
      ((x : A) → ((i : R) → Not (Id A x (a i))) → Id A (σ .map x) x)
      (pi_prop R (i ↦ Id A (σ .map (a i)) (a (modular_successor (suc. j) i)))
        (i ↦ hA (σ .map (a i)) (a (modular_successor (suc. j) i))))
      (pi_prop A (x ↦ ((i : R) → Not (Id A x (a i))) → Id A (σ .map x) x)
        (x ↦ pi_prop ((i : R) → Not (Id A x (a i))) (_ ↦ Id A (σ .map x) x) (_ ↦ hA (σ .map x) x)))

{` Main comparison.  For a set A with decidable equality, pairs (σ, E) of
   a permutation with a k-cycle enumeration (module 243) are equivalent to
   injective enumerations, hence to pairwise distinct lists of length k,
   and the permutation is the cycle notation of the list (module 174). `}
def kcycle_enumerations_equiv (A : Type) (hA : isSet A) (d : DecidableEquality A) (j : Nat)
  : Equiv (Σ (Equiv A A) (KCycleEnumeration A j)) (InjectiveCycleEnumerations A j)
  ≔ let T ≔ Σ (Equiv A A) (KCycleEnumeration A j) in
    let W ≔ InjectiveCycleEnumerations A j in
    quasi_inverse_equiv T W
      (u ↦ (u .snd .fst, u .snd .snd .fst))
      (w ↦ (enumeration_cycle_equiv A d j w, enumeration_kcycle A d j w))
      (u ↦ let w : W ≔ (u .snd .fst, u .snd .snd .fst) in
        let L ≔ ((σ ↦ KCycleLaws A j (w .fst) σ) : Equiv A A → Type) in
        refl ((t ↦ (t .fst, (w .fst, (w .snd, t .snd)))) : Σ (Equiv A A) L → T)
          (subtype_equal (Equiv A A) L (σ ↦ kcycle_laws_prop A hA j (w .fst) σ)
            (enumeration_cycle_equiv A d j w, enumeration_kcycle A d j w .snd .snd)
            (u .fst, u .snd .snd .snd)
            (equiv_path A A (enumeration_cycle_equiv A d j w) (u .fst)
              (funext A (_ ↦ A) (enumeration_cycle_equiv A d j w .map) (u .fst .map)
                (x ↦ inverse A (u .fst .map x) (enumeration_cycle_equiv A d j w .map x)
                  (kcycle_enumeration_unique_at A d j (u .fst) (u .snd) x))))))
      (w ↦ refl w)

def kcycle_enumerations_lists_equiv (A : Type) (hA : isSet A) (d : DecidableEquality A) (j : Nat)
  : Equiv (Σ (Equiv A A) (KCycleEnumeration A j)) (CycleNotationLists A j)
  ≔ compose_equiv (Σ (Equiv A A) (KCycleEnumeration A j)) (InjectiveCycleEnumerations A j) (CycleNotationLists A j)
      (kcycle_enumerations_equiv A hA d j) (enumeration_list_equiv A j)

def kcycle_enumerations_lists_commute (A : Type) (hA : isSet A) (d : DecidableEquality A) (j : Nat)
  (u : Σ (Equiv A A) (KCycleEnumeration A j))
  : Id (Equiv A A) (u .fst) (cycle_notation_list_equiv A d j (kcycle_enumerations_lists_equiv A hA d j .map u))
  ≔ kcycle_enumeration_cycle_notation A d j (u .fst) (u .snd)

{` Conversely, for a list a_1 :: rest of k pairwise distinct entries, the
   permutation (a_1 ... a_k) of module 174 is a k-cycle in the sense of
   module 243, enumerated by a(i) = a_{i+1}: it sends a(i) to a(i+1) and
   fixes every other point. `}
def cycle_notation_list_laws (A : Type) (d : DecidableEquality A) (j : Nat) (l : CycleNotationLists A j)
  : KCycleLaws A j (list_to_enumeration A j l .fst) (cycle_notation_list_equiv A d j l)
  ≔ transport (CycleNotationLists A j)
      (m ↦ KCycleLaws A j (list_to_enumeration A j l .fst) (cycle_notation_list_equiv A d j m))
      (enumeration_to_list A j (list_to_enumeration A j l)) l (list_enumeration_roundtrip A j l)
      (enumeration_kcycle A d j (list_to_enumeration A j l) .snd .snd)

def cycle_notation_list_kcycle (A : Type) (d : DecidableEquality A) (j : Nat) (l : CycleNotationLists A j)
  : KCycleEnumeration A j (cycle_notation_list_equiv A d j l)
  ≔ (list_to_enumeration A j l .fst, (list_to_enumeration A j l .snd, cycle_notation_list_laws A d j l))

{` Hence σ is a k-cycle (module 243) iff merely σ = (a_1 ... a_k) for a
   list of k pairwise distinct entries (module 174). `}
def is_kcycle_cycle_notation_equiv (A : Type) (hA : isSet A) (d : DecidableEquality A) (j : Nat) (σ : Equiv A A)
  : Equiv (IsKCycle A j σ)
      (Mere (Σ (CycleNotationLists A j) (l ↦ Id (Equiv A A) (cycle_notation_list_equiv A d j l) σ)))
  ≔ let S ≔ Σ (CycleNotationLists A j) (l ↦ Id (Equiv A A) (cycle_notation_list_equiv A d j l) σ) in
    iff_equiv (IsKCycle A j σ) (Mere S) (mere_isprop (KCycleEnumeration A j σ)) (mere_isprop S)
      (trunc_map native_truncation (KCycleEnumeration A j σ) S
        (E ↦ (kcycle_enumerations_lists_equiv A hA d j .map (σ, E),
          inverse (Equiv A A) σ (cycle_notation_list_equiv A d j (kcycle_enumerations_lists_equiv A hA d j .map (σ, E)))
            (kcycle_enumerations_lists_commute A hA d j (σ, E)))))
      (trunc_map native_truncation S (KCycleEnumeration A j σ)
        (v ↦ transport (Equiv A A) (KCycleEnumeration A j) (cycle_notation_list_equiv A d j (v .fst)) σ (v .snd)
          (cycle_notation_list_kcycle A d j (v .fst))))

def kcycle_permutations_cycle_notation (A : Type) (hA : isSet A) (d : DecidableEquality A) (j : Nat)
  : Equiv (KCyclePermutations A j)
      (Σ (Equiv A A) (σ ↦ Mere (Σ (CycleNotationLists A j) (l ↦ Id (Equiv A A) (cycle_notation_list_equiv A d j l) σ))))
  ≔ family_equiv (Equiv A A) (IsKCycle A j)
      (σ ↦ Mere (Σ (CycleNotationLists A j) (l ↦ Id (Equiv A A) (cycle_notation_list_equiv A d j l) σ)))
      (is_kcycle_cycle_notation_equiv A hA d j)

{` The book's proof of the corollary after xca:perm-prod-transpositions:
   first write a permutation of a finite set as a composite of cyclic
   permutations (a_1 ... a_k), k ≥ 2, one for each orbit with at least two
   elements (by construction), then write each of them as k-1
   transpositions. `}

{` Least periods of points of a finite set, by pigeonhole. `}
def PointPeriod (A : Type) (f : A → A) (x : A) (n : Nat) : Type ≔ Id A (iterate A f (suc. n) x) x

def iterate_equiv_injective (A : Type) (σ : Equiv A A) (n : Nat) (y z : A)
  (p : Id A (iterate A (σ .map) n y) (iterate A (σ .map) n z)) : Id A y z
  ≔ match n [
  | zero. ↦ p
  | suc. n ↦ iterate_equiv_injective A σ n y z
      (equivalence_injective A A σ (iterate A (σ .map) n y) (iterate A (σ .map) n z) p) ]

def iterate_offset_period (A : Type) (σ : Equiv A A) (x : A) (l r k : Nat)
  (nz : Not (Id Nat k zero.)) (q : Id Nat (add k l) r)
  (p : Id A (iterate A (σ .map) l x) (iterate A (σ .map) r x))
  : Σ Nat (m ↦ Product (PointPeriod A (σ .map) x m) (Lt m r))
  ≔ let f ≔ σ .map in
    match k [
    | zero. ↦ absurd (Σ Nat (m ↦ Product (PointPeriod A f x m) (Lt m r))) (nz (refl (zero. : Nat)))
    | suc. k ↦ (k,
        (inverse A x (iterate A f (suc. k) x)
          (iterate_equiv_injective A σ l x (iterate A f (suc. k) x)
            (calc iterate A f l x = iterate A f r x by p
             = iterate A f (add (suc. k) l) x
               by refl ((n ↦ iterate A f n x) : Nat → A) (inverse Nat (add (suc. k) l) r q)
             = iterate A f l (iterate A f (suc. k) x) by iterate_add A f (suc. k) l x ∎)),
         le_from_book (suc. k) r (l, concat Nat (add l (suc. k)) (add (suc. k) l) r (add_comm l (suc. k)) q))) ]

def iterate_collision_ordered (A : Type) (σ : Equiv A A) (x : A) (l r : Nat) (lt : Lt l r)
  (p : Id A (iterate A (σ .map) l x) (iterate A (σ .map) r x))
  : Σ Nat (m ↦ Product (PointPeriod A (σ .map) x m) (Lt m r))
  ≔ let b ≔ lt_to_book l r lt in iterate_offset_period A σ x l r (b .fst) (b .snd .fst) (b .snd .snd) p

def nat_order_trichotomy (m n : Nat) : Sum (Lt m n) (Sum (Id Nat m n) (Lt n m))
  ≔ match le_total m n [
  | inl. h ↦ match le_split m n h [ inl. lt ↦ inl. lt | inr. e ↦ inr. (inl. e) ]
  | inr. h ↦ match le_split n m h [ inl. lt ↦ inr. (inr. lt) | inr. e ↦ inr. (inl. (inverse Nat n m e)) ] ]

def iterate_collision_period (A : Type) (σ : Equiv A A) (x : A) (l r : Nat) (ne : Not (Id Nat l r))
  (p : Id A (iterate A (σ .map) l x) (iterate A (σ .map) r x)) : Σ Nat (PointPeriod A (σ .map) x)
  ≔ match nat_order_trichotomy l r [
  | inl. lt ↦ let w ≔ iterate_collision_ordered A σ x l r lt p in (w .fst, w .snd .fst)
  | inr. c ↦ match c [
    | inl. e ↦ absurd (Σ Nat (PointPeriod A (σ .map) x)) (ne e)
    | inr. lt ↦ let w ≔ iterate_collision_ordered A σ x r l lt
          (inverse A (iterate A (σ .map) l x) (iterate A (σ .map) r x) p) in
        (w .fst, w .snd .fst) ] ]

def finite_point_period (A : Type) (ha : IsFinite A) (σ : Equiv A A) (x : A)
  : Mere (Σ Nat (PointPeriod A (σ .map) x))
  ≔ mere_rec (Σ Nat (N ↦ Id Type A (Fin N))) (Mere (Σ Nat (PointPeriod A (σ .map) x)))
      (mere_isprop (Σ Nat (PointPeriod A (σ .map) x)))
      (w ↦ let N ≔ w .fst in
        let e ≔ id_to_equiv A (Fin N) (w .snd) in
        let orbit ≔ ((i ↦ iterate A (σ .map) (fin_index (suc. N) i) x) : Fin (suc. N) → A) in
        let c ≔ fin_pigeonhole N (i ↦ e .map (orbit i)) in
        mere (Σ Nat (PointPeriod A (σ .map) x))
          (iterate_collision_period A σ x (fin_index (suc. N) (c .left)) (fin_index (suc. N) (c .right))
            (q ↦ c .distinct (fin_index_injective (suc. N) (c .left) (c .right) q))
            (equivalence_injective A (Fin N) e (orbit (c .left)) (orbit (c .right)) (c .same))))
      ha

def LeastPeriods (A : Type) (σ : Equiv A A) : Type ≔ (x : A) → Σ Nat (IsMinimum (PointPeriod A (σ .map) x))

def finite_least_period (A : Type) (ha : IsFinite A) (σ : Equiv A A) (x : A)
  : Σ Nat (IsMinimum (PointPeriod A (σ .map) x))
  ≔ least_number (PointPeriod A (σ .map) x)
      (n ↦ finite_sethood A ha (iterate A (σ .map) (suc. n) x) x)
      (n ↦ finite_decidable_equality A ha (iterate A (σ .map) (suc. n) x) x)
      (finite_point_period A ha σ x)

def finite_least_periods (A : Type) (ha : IsFinite A) (σ : Equiv A A) : LeastPeriods A σ
  ≔ x ↦ finite_least_period A ha σ x

def least_period_bound (A : Type) (σ : Equiv A A) (x : A) (n : Nat) (m : IsMinimum (PointPeriod A (σ .map) x) n)
  (k : Nat) (pk : PointPeriod A (σ .map) x k) (r : Nat) (hk : Lt k r) (hr : Lt r (suc. n)) : Empty
  ≔ lt_irrefl k (lt_le_trans k n k (lt_le_trans k r n hk hr) (le_from_book n k (m .snd k pk)))

{` Below its least period n+1 the iterates of x are distinct. `}
def least_period_injective (A : Type) (σ : Equiv A A) (x : A) (n : Nat) (m : IsMinimum (PointPeriod A (σ .map) x) n)
  : InjectiveBelow A (σ .map) x (suc. n)
  ≔ i i' hi hi' p ↦ match nat_order_trichotomy i i' [
    | inl. lt ↦ let w ≔ iterate_collision_ordered A σ x i i' lt p in
        absurd (Id Nat i i') (least_period_bound A σ x n m (w .fst) (w .snd .fst) i' (w .snd .snd) hi')
    | inr. c ↦ match c [
      | inl. e ↦ e
      | inr. lt ↦ let w ≔ iterate_collision_ordered A σ x i' i lt
            (inverse A (iterate A (σ .map) i x) (iterate A (σ .map) i' x) p) in
          absurd (Id Nat i i') (least_period_bound A σ x n m (w .fst) (w .snd .fst) i (w .snd .snd) hi) ] ]

{` The orbit of x, whose least period is n+1: y = σ^i(x) with i ≤ n. `}
def OrbitMember (A : Type) (σ : Equiv A A) (n : Nat) (x y : A) : Type
  ≔ Σ Nat (i ↦ Product (Lt i (suc. n)) (Id A y (iterate A (σ .map) i x)))

{` The cyclic permutation (x σx ... σ^n x) acts as σ on the orbit of x
   and as the identity elsewhere. `}
def orbit_member_cycle (A : Type) (d : DecidableEquality A) (σ : Equiv A A) (x : A) (n : Nat)
  (per : PointPeriod A (σ .map) x n) (inj : InjectiveBelow A (σ .map) x (suc. n)) (y : A)
  (i : Nat) (hi : Lt i (suc. n)) (q : Id A y (iterate A (σ .map) i x))
  : Id A (cycle_notation A d x (iterate_list A (σ .map) (σ .map x) n) y) (σ .map y)
  ≔ let f ≔ σ .map in
    let C ≔ cycle_notation A d x (iterate_list A f (f x) n) in
    transport A (z ↦ Id A (C z) (f z)) (iterate A f i x) y (inverse A y (iterate A f i x) q)
      (match le_split i n hi [
      | inl. small ↦ iterate_list_lookup_small A d f x x n inj i small
      | inr. last ↦ transport Nat (k ↦ Id A (C (iterate A f k x)) (f (iterate A f k x))) n i (inverse Nat i n last)
          (concat A (C (iterate A f n x)) x (f (iterate A f n x))
            (iterate_list_lookup_last A d f x x n inj)
            (inverse A (f (iterate A f n x)) x per)) ])

def orbit_nonmember_cycle (A : Type) (d : DecidableEquality A) (σ : Equiv A A) (x : A) (n : Nat) (y : A)
  (no : Not (OrbitMember A σ n x y))
  : Id A (cycle_notation A d x (iterate_list A (σ .map) (σ .map x) n) y) y
  ≔ cycle_notation_fixed A d x (iterate_list A (σ .map) (σ .map x) n) y
      (iterate_list_not_in A (σ .map) y x (suc. n) (i hi q ↦ no (i, (hi, inverse A (iterate A (σ .map) i x) y q))))

def orbit_nonmember_step_at (A : Type) (σ : Equiv A A) (x : A) (n : Nat) (per : PointPeriod A (σ .map) x n) (y : A)
  (no : Not (OrbitMember A σ n x y)) (i : Nat) (hi : Lt i (suc. n)) (q : Id A (σ .map y) (iterate A (σ .map) i x))
  : Empty
  ≔ match i [
  | zero. ↦ no (n, (le_refl n, equivalence_injective A A σ y (iterate A (σ .map) n x)
      (concat A (σ .map y) x (σ .map (iterate A (σ .map) n x)) q
        (inverse A (σ .map (iterate A (σ .map) n x)) x per))))
  | suc. i ↦ no (i, (lt_le i n hi, equivalence_injective A A σ y (iterate A (σ .map) i x) q)) ]

def orbit_nonmember_step (A : Type) (σ : Equiv A A) (x : A) (n : Nat) (per : PointPeriod A (σ .map) x n) (y : A)
  (no : Not (OrbitMember A σ n x y)) : Not (OrbitMember A σ n x (σ .map y))
  ≔ w ↦ orbit_nonmember_step_at A σ x n per y no (w .fst) (w .snd .fst) (w .snd .snd)

{` Orbits are closed under σ and σ⁻¹, so they contain all powers. `}
def orbit_member_next (A : Type) (σ : Equiv A A) (x : A) (n : Nat) (per : PointPeriod A (σ .map) x n) (y : A)
  (w : OrbitMember A σ n x y) : OrbitMember A σ n x (σ .map y)
  ≔ match le_split (w .fst) n (w .snd .fst) [
  | inl. small ↦ (suc. (w .fst), (small, refl (σ .map) (w .snd .snd)))
  | inr. last ↦ (zero., (star., concat A (σ .map y) (σ .map (iterate A (σ .map) (w .fst) x)) x
      (refl (σ .map) (w .snd .snd))
      (concat A (σ .map (iterate A (σ .map) (w .fst) x)) (σ .map (iterate A (σ .map) n x)) x
        (refl (σ .map) (refl ((k ↦ iterate A (σ .map) k x) : Nat → A) last)) per))) ]

def orbit_member_prev_at (A : Type) (σ : Equiv A A) (x : A) (n : Nat) (per : PointPeriod A (σ .map) x n) (y : A)
  (i : Nat) (hi : Lt i (suc. n)) (q : Id A y (iterate A (σ .map) i x))
  : OrbitMember A σ n x (equiv_inverse_map A A σ y)
  ≔ let f ≔ σ .map in
    let g ≔ equiv_inverse_map A A σ in
    match i [
    | zero. ↦ (n, (le_refl n, calc
        g y = g x by refl g q
        = g (f (iterate A f n x)) by refl g (inverse A (f (iterate A f n x)) x per)
        = iterate A f n x by inverse A (iterate A f n x) (g (f (iterate A f n x))) (equiv_unit A A σ (iterate A f n x)) ∎))
    | suc. i ↦ (i, (lt_le i n hi, calc
        g y = g (f (iterate A f i x)) by refl g q
        = iterate A f i x by inverse A (iterate A f i x) (g (f (iterate A f i x))) (equiv_unit A A σ (iterate A f i x)) ∎)) ]

def orbit_member_prev (A : Type) (σ : Equiv A A) (x : A) (n : Nat) (per : PointPeriod A (σ .map) x n) (y : A)
  (w : OrbitMember A σ n x y) : OrbitMember A σ n x (equiv_inverse_map A A σ y)
  ≔ orbit_member_prev_at A σ x n per y (w .fst) (w .snd .fst) (w .snd .snd)

def iterate_invariant (A : Type) (f : A → A) (P : A → Type) (step : (y : A) → P y → P (f y)) (k : Nat) (y : A)
  (py : P y) : P (iterate A f k y)
  ≔ match k [ zero. ↦ py | suc. k ↦ step (iterate A f k y) (iterate_invariant A f P step k y py) ]

def orbit_member_power (A : Type) (σ : Equiv A A) (x : A) (n : Nat) (per : PointPeriod A (σ .map) x n) (z : Int)
  : OrbitMember A σ n x (permutation_power A σ z x)
  ≔ let base : OrbitMember A σ n x x ≔ (zero., (star., refl x)) in
    match z [
    | pos. k ↦ iterate_invariant A (σ .map) (OrbitMember A σ n x) (orbit_member_next A σ x n per) k x base
    | neg. k ↦ iterate_invariant A (equiv_inverse_map A A σ) (OrbitMember A σ n x) (orbit_member_prev A σ x n per)
        (suc. k) x base ]

def bounded_index_decide (P : Nat → Type) (dP : (i : Nat) → Decidable (P i)) (k : Nat)
  : Sum (Σ Nat (i ↦ Product (Lt i k) (P i))) ((i : Nat) → Lt i k → Not (P i))
  ≔ match k [
  | zero. ↦ inr. (i hi _ ↦ match hi [])
  | suc. k ↦ match bounded_index_decide P dP k [
    | inl. w ↦ inl. (w .fst, (le_step (suc. (w .fst)) k (w .snd .fst), w .snd .snd))
    | inr. no ↦ match dP k [
      | inl. pk ↦ inl. (k, (le_refl k, pk))
      | inr. npk ↦ inr. (i hi pi ↦ match le_split i k hi [
        | inl. lt ↦ no i lt pi
        | inr. e ↦ npk (transport Nat P i k e pi) ]) ] ] ]

def orbit_member_decide (A : Type) (d : DecidableEquality A) (σ : Equiv A A) (n : Nat) (x y : A)
  : Decidable (OrbitMember A σ n x y)
  ≔ match bounded_index_decide (i ↦ Id A y (iterate A (σ .map) i x)) (i ↦ d y (iterate A (σ .map) i x)) (suc. n) [
  | inl. w ↦ inl. w
  | inr. no ↦ inr. (w ↦ no (w .fst) (w .snd .fst) (w .snd .snd)) ]

{` These orbits are the orbits of module 58 (SameOrbit), used in 240. `}
def orbit_member_same_orbit (A : Type) (σ : Equiv A A) (n : Nat) (x y : A) (w : OrbitMember A σ n x y)
  : SameOrbit A σ x y
  ≔ mere (OrbitWitness A σ x y) (pos. (w .fst), w .snd .snd)

def same_orbit_member (A : Type) (d : DecidableEquality A) (σ : Equiv A A) (x : A) (n : Nat)
  (per : PointPeriod A (σ .map) x n) (y : A) (s : SameOrbit A σ x y) : OrbitMember A σ n x y
  ≔ match orbit_member_decide A d σ n x y [
  | inl. w ↦ w
  | inr. no ↦ absurd (OrbitMember A σ n x y)
      (mere_rec (OrbitWitness A σ x y) Empty empty_prop
        (v ↦ no (transport A (OrbitMember A σ n x) (permutation_power A σ (v .fst) x) y
          (inverse A y (permutation_power A σ (v .fst) x) (v .snd))
          (orbit_member_power A σ x n per (v .fst)))) s) ]

def OrbitOf (A : Type) (σ : Equiv A A) (lp : LeastPeriods A σ) (x y : A) : Type ≔ OrbitMember A σ (lp x .fst) x y

def orbit_of_symmetric (A : Type) (d : DecidableEquality A) (σ : Equiv A A) (lp : LeastPeriods A σ) (x y : A)
  (w : OrbitOf A σ lp x y) : OrbitOf A σ lp y x
  ≔ same_orbit_member A d σ y (lp y .fst) (lp y .snd .fst) x
      (same_orbit_sym A σ x y (orbit_member_same_orbit A σ (lp x .fst) x y w))

def orbit_of_transitive (A : Type) (d : DecidableEquality A) (σ : Equiv A A) (lp : LeastPeriods A σ) (x y z : A)
  (w : OrbitOf A σ lp x y) (v : OrbitOf A σ lp y z) : OrbitOf A σ lp x z
  ≔ same_orbit_member A d σ x (lp x .fst) (lp x .snd .fst) z
      (same_orbit_trans A σ x y z (orbit_member_same_orbit A σ (lp x .fst) x y w)
        (orbit_member_same_orbit A σ (lp y .fst) y z v))

{` y lies in the orbit of some point of the list l. `}
def OrbitCovered (A : Type) (σ : Equiv A A) (lp : LeastPeriods A σ) (l : List A) (y : A) : Type
  ≔ match l [ nil. ↦ Empty | cons. r rest ↦ Sum (OrbitOf A σ lp r y) (OrbitCovered A σ lp rest y) ]

def orbit_covered_decide (A : Type) (d : DecidableEquality A) (σ : Equiv A A) (lp : LeastPeriods A σ) (l : List A)
  (y : A) : Decidable (OrbitCovered A σ lp l y)
  ≔ match l [
  | nil. ↦ inr. (e ↦ e)
  | cons. r rest ↦ match orbit_member_decide A d σ (lp r .fst) r y [
    | inl. w ↦ inl. (inl. w)
    | inr. no ↦ match orbit_covered_decide A d σ lp rest y [
      | inl. c ↦ inl. (inr. c)
      | inr. nc ↦ inr. (c ↦ match c [ inl. w ↦ no w | inr. c ↦ nc c ]) ] ] ]

def orbit_covered_transfer (A : Type) (d : DecidableEquality A) (σ : Equiv A A) (lp : LeastPeriods A σ) (l : List A)
  (y z : A) (w : OrbitOf A σ lp y z) (c : OrbitCovered A σ lp l y) : OrbitCovered A σ lp l z
  ≔ match l [
  | nil. ↦ match c []
  | cons. r rest ↦ match c [
    | inl. v ↦ inl. (orbit_of_transitive A d σ lp r y z v w)
    | inr. c ↦ inr. (orbit_covered_transfer A d σ lp rest y z w c) ] ]

def orbit_covered_of_occurs (A : Type) (d : DecidableEquality A) (σ : Equiv A A) (lp : LeastPeriods A σ) (l : List A)
  (y : A) (m : Not (NotInList A y l)) : OrbitCovered A σ lp l y
  ≔ match l [
  | nil. ↦ m star.
  | cons. a rest ↦ match d y a [
    | inl. p ↦ inl. (zero., (star., p))
    | inr. n ↦ inr. (orbit_covered_of_occurs A d σ lp rest y (h ↦ m (n, h))) ] ]

{` Lists of cyclic permutations (a_1 ... a_k), k = j+2 ≥ 2, and their
   composite, the head of the list applied last. `}
def CycleFactors (A : Type) : Type ≔ List (Σ Nat (CycleNotationLists A))

def cycle_factors_product (A : Type) (d : DecidableEquality A) (cs : CycleFactors A) : A → A
  ≔ match cs [
  | nil. ↦ identity A
  | cons. c rest ↦ compose A A A (cycle_notation A d (c .snd .fst) (c .snd .snd .fst)) (cycle_factors_product A d rest) ]

def cycle_notation_singleton (A : Type) (d : DecidableEquality A) (x : A) (rest : List A)
  (len : Id Nat (length A rest) zero.) (z : A) : Id A (cycle_notation A d x rest z) z
  ≔ match rest [
  | nil. ↦ decide_branch_elim A (Id A z x) (d z x) x z z (p ↦ inverse A z x p) (_ ↦ refl z)
  | cons. b rest ↦ absurd (Id A (cycle_notation A d x (cons. b rest) z) z) (nat_encode (suc. (length A rest)) zero. len) ]

{` Add the orbit cycle (x σx ... σ^n x) in front, unless n = 0. `}
def orbit_factor_cons (A : Type) (x : A) (n : Nat) (rest : List A) (len : Id Nat (length A rest) n)
  (dist : PairwiseDistinct A (cons. x rest)) (tail : CycleFactors A) : CycleFactors A
  ≔ match n [ zero. ↦ tail | suc. j ↦ cons. (j, (x, (rest, (len, dist)))) tail ]

def orbit_factor_cons_product (A : Type) (d : DecidableEquality A) (x : A) (n : Nat) (rest : List A)
  (len : Id Nat (length A rest) n) (dist : PairwiseDistinct A (cons. x rest)) (tail : CycleFactors A) (y : A)
  : Id A (cycle_factors_product A d (orbit_factor_cons A x n rest len dist tail) y)
      (cycle_notation A d x rest (cycle_factors_product A d tail y))
  ≔ match n [
  | zero. ↦ inverse A (cycle_notation A d x rest (cycle_factors_product A d tail y)) (cycle_factors_product A d tail y)
      (cycle_notation_singleton A d x rest len (cycle_factors_product A d tail y))
  | suc. j ↦ refl (cycle_notation A d x rest (cycle_factors_product A d tail y)) ]

{` One factor per orbit meeting the list l: a point e of l contributes its
   orbit cycle unless its orbit meets the rest of the list. `}
def orbit_factors_step (A : Type) (σ : Equiv A A) (lp : LeastPeriods A σ) (e : A) (rest : List A)
  (dec : Decidable (OrbitCovered A σ lp rest e)) (tail : CycleFactors A) : CycleFactors A
  ≔ match dec [
  | inl. _ ↦ tail
  | inr. _ ↦ orbit_factor_cons A e (lp e .fst) (iterate_list A (σ .map) (σ .map e) (lp e .fst))
      (iterate_list_length A (σ .map) (σ .map e) (lp e .fst))
      (iterate_list_distinct A (σ .map) e (suc. (lp e .fst)) (least_period_injective A σ e (lp e .fst) (lp e .snd)))
      tail ]

def orbit_factors (A : Type) (d : DecidableEquality A) (σ : Equiv A A) (lp : LeastPeriods A σ) (l : List A)
  : CycleFactors A
  ≔ match l [
  | nil. ↦ nil.
  | cons. e rest ↦ orbit_factors_step A σ lp e rest (orbit_covered_decide A d σ lp rest e) (orbit_factors A d σ lp rest) ]

def OrbitFactorsInvariant (A : Type) (σ : Equiv A A) (lp : LeastPeriods A σ) (l : List A) (P : A → A) : Type
  ≔ (y : A) → Product (OrbitCovered A σ lp l y → Id A (P y) (σ .map y)) (Not (OrbitCovered A σ lp l y) → Id A (P y) y)

def orbit_factors_step_invariant (A : Type) (d : DecidableEquality A) (σ : Equiv A A) (lp : LeastPeriods A σ)
  (e : A) (rest : List A) (dec : Decidable (OrbitCovered A σ lp rest e)) (tail : CycleFactors A)
  (ih : OrbitFactorsInvariant A σ lp rest (cycle_factors_product A d tail))
  : OrbitFactorsInvariant A σ lp (cons. e rest) (cycle_factors_product A d (orbit_factors_step A σ lp e rest dec tail))
  ≔ match dec [
  | inl. c ↦ y ↦
      ((cov ↦ match cov [
        | inl. m ↦ ih y .fst (orbit_covered_transfer A d σ lp rest e y m c)
        | inr. cr ↦ ih y .fst cr ]),
       (ncov ↦ ih y .snd (cr ↦ ncov (inr. cr))))
  | inr. nc ↦ y ↦
      let n ≔ lp e .fst in
      let f ≔ σ .map in
      let L ≔ iterate_list A f (f e) n in
      let per ≔ lp e .snd .fst in
      let inj ≔ least_period_injective A σ e n (lp e .snd) in
      let C ≔ cycle_notation A d e L in
      let T ≔ cycle_factors_product A d tail in
      let P ≔ cycle_factors_product A d (orbit_factors_step A σ lp e rest (inr. nc) tail) in
      let factor_split : Id A (P y) (C (T y))
        ≔ orbit_factor_cons_product A d e n L (iterate_list_length A f (f e) n)
            (iterate_list_distinct A f e (suc. n) inj) tail y in
      let member_case ≔ ((m ↦ concat A (P y) (C (T y)) (f y) factor_split
          (concat A (C (T y)) (C y) (f y)
            (refl C (ih y .snd (cr ↦ nc (orbit_covered_transfer A d σ lp rest y e (orbit_of_symmetric A d σ lp e y m) cr))))
            (orbit_member_cycle A d σ e n per inj y (m .fst) (m .snd .fst) (m .snd .snd))))
        : OrbitOf A σ lp e y → Id A (P y) (f y)) in
      ((cov ↦ match cov [
        | inl. m ↦ member_case m
        | inr. cr ↦ match orbit_member_decide A d σ n e y [
          | inl. m ↦ member_case m
          | inr. nm ↦ concat A (P y) (C (T y)) (f y) factor_split
              (concat A (C (T y)) (C (f y)) (f y) (refl C (ih y .fst cr))
                (orbit_nonmember_cycle A d σ e n (f y) (orbit_nonmember_step A σ e n per y nm))) ] ]),
       (ncov ↦ concat A (P y) (C (T y)) y factor_split
          (concat A (C (T y)) (C y) y (refl C (ih y .snd (cr ↦ ncov (inr. cr))))
            (orbit_nonmember_cycle A d σ e n y (m ↦ ncov (inl. m)))))) ]

def orbit_factors_invariant (A : Type) (d : DecidableEquality A) (σ : Equiv A A) (lp : LeastPeriods A σ) (l : List A)
  : OrbitFactorsInvariant A σ lp l (cycle_factors_product A d (orbit_factors A d σ lp l))
  ≔ match l [
  | nil. ↦ y ↦ ((c ↦ match c []), (_ ↦ refl y))
  | cons. e rest ↦ orbit_factors_step_invariant A d σ lp e rest (orbit_covered_decide A d σ lp rest e)
      (orbit_factors A d σ lp rest) (orbit_factors_invariant A d σ lp rest) ]

{` Cycle decomposition: if every point occurs in l, then σ is the
   composite of the orbit cycles (x σx ... σ^n x) with n ≥ 1 of the
   representatives x chosen from l (by construction one point of each orbit;
   orbits with one element contribute no factor). `}
def cycle_decomposition_of_list (A : Type) (d : DecidableEquality A) (σ : Equiv A A) (lp : LeastPeriods A σ)
  (l : List A) (all : (y : A) → Not (NotInList A y l))
  : Id (A → A) (σ .map) (cycle_factors_product A d (orbit_factors A d σ lp l))
  ≔ funext A (_ ↦ A) (σ .map) (cycle_factors_product A d (orbit_factors A d σ lp l))
      (y ↦ inverse A (cycle_factors_product A d (orbit_factors A d σ lp l) y) (σ .map y)
        (orbit_factors_invariant A d σ lp l y .fst (orbit_covered_of_occurs A d σ lp l y (all y))))

def fin_all_elements (n : Nat) : List (Fin n)
  ≔ match n [
  | zero. ↦ nil.
  | suc. n ↦ cons. (inr. star.) (cycle_list_map (Fin n) (Fin (suc. n)) (i ↦ inl. i) (fin_all_elements n)) ]

def map_not_in_list_reflect (X A : Type) (h : X → A) (x : X) (l : List X)
  (hx : NotInList A (h x) (cycle_list_map X A h l)) : NotInList X x l
  ≔ match l [
  | nil. ↦ star.
  | cons. y rest ↦ ((p ↦ hx .fst (refl h p)), map_not_in_list_reflect X A h x rest (hx .snd)) ]

def fin_all_elements_occurs (n : Nat) (i : Fin n) : Not (NotInList (Fin n) i (fin_all_elements n))
  ≔ match n [
  | zero. ↦ match i []
  | suc. n ↦ match i [
    | inr. u ↦ h ↦ h .fst (refl ((v ↦ (inr. v : Fin (suc. n))) : Unit → Fin (suc. n)) (unit_prop u star.))
    | inl. i ↦ h ↦ fin_all_elements_occurs n i
        (map_not_in_list_reflect (Fin n) (Fin (suc. n)) (k ↦ inl. k) i (fin_all_elements n) (h .snd)) ] ]

def equiv_all_elements_occurs (A : Type) (N : Nat) (e : Equiv A (Fin N)) (y : A)
  : Not (NotInList A y (cycle_list_map (Fin N) A (equiv_inverse_map A (Fin N) e) (fin_all_elements N)))
  ≔ let g ≔ equiv_inverse_map A (Fin N) e in
    h ↦ fin_all_elements_occurs N (e .map y)
      (map_not_in_list_reflect (Fin N) A g (e .map y) (fin_all_elements N)
        (transport A (z ↦ NotInList A z (cycle_list_map (Fin N) A g (fin_all_elements N))) y (g (e .map y))
          (equiv_unit A (Fin N) e y) h))

{` Every permutation of Fin n is an explicit composite of cyclic
   permutations, and every permutation of a finite set merely is. `}
def fin_cycle_decomposition (n : Nat) (σ : Equiv (Fin n) (Fin n))
  : Σ (CycleFactors (Fin n)) (cs ↦ Id (Fin n → Fin n) (σ .map) (cycle_factors_product (Fin n) (fin_decidable_equality n) cs))
  ≔ let lp ≔ finite_least_periods (Fin n) (fin_is_finite n) σ in
    (orbit_factors (Fin n) (fin_decidable_equality n) σ lp (fin_all_elements n),
     cycle_decomposition_of_list (Fin n) (fin_decidable_equality n) σ lp (fin_all_elements n)
       (fin_all_elements_occurs n))

def finite_cycle_decomposition (A : Type) (ha : IsFinite A) (σ : Equiv A A)
  : Mere (Σ (CycleFactors A) (cs ↦ Id (A → A) (σ .map) (cycle_factors_product A (finite_decidable_equality A ha) cs)))
  ≔ let d ≔ finite_decidable_equality A ha in
    let lp ≔ finite_least_periods A ha σ in
    let S ≔ Σ (CycleFactors A) (cs ↦ Id (A → A) (σ .map) (cycle_factors_product A d cs)) in
    mere_rec (Σ Nat (N ↦ Id Type A (Fin N))) (Mere S) (mere_isprop S)
      (w ↦ let e ≔ id_to_equiv A (Fin (w .fst)) (w .snd) in
        let L ≔ cycle_list_map (Fin (w .fst)) A (equiv_inverse_map A (Fin (w .fst)) e) (fin_all_elements (w .fst)) in
        mere S (orbit_factors A d σ lp L,
          cycle_decomposition_of_list A d σ lp L (equiv_all_elements_occurs A (w .fst) e)))
      ha

{` Each factor is a k-cycle in the sense of module 243. `}
def kcycle_factors_product (A : Type) (ks : List (Σ Nat (KCyclePermutations A))) : A → A
  ≔ match ks [
  | nil. ↦ identity A
  | cons. k rest ↦ compose A A A (k .snd .fst .map) (kcycle_factors_product A rest) ]

def kcycle_factors_of_cycle_factors (A : Type) (d : DecidableEquality A) (cs : CycleFactors A)
  : List (Σ Nat (KCyclePermutations A))
  ≔ cycle_list_map (Σ Nat (CycleNotationLists A)) (Σ Nat (KCyclePermutations A))
      (c ↦ (c .fst, (cycle_notation_list_equiv A d (c .fst) (c .snd),
        mere (KCycleEnumeration A (c .fst) (cycle_notation_list_equiv A d (c .fst) (c .snd)))
          (cycle_notation_list_kcycle A d (c .fst) (c .snd))))) cs

def kcycle_factors_product_agree (A : Type) (d : DecidableEquality A) (cs : CycleFactors A) (y : A)
  : Id A (kcycle_factors_product A (kcycle_factors_of_cycle_factors A d cs) y) (cycle_factors_product A d cs y)
  ≔ match cs [
  | nil. ↦ refl y
  | cons. c rest ↦ refl (cycle_notation A d (c .snd .fst) (c .snd .snd .fst)) (kcycle_factors_product_agree A d rest y) ]

def finite_kcycle_decomposition (A : Type) (ha : IsFinite A) (σ : Equiv A A)
  : Mere (Σ (List (Σ Nat (KCyclePermutations A))) (ks ↦ Id (A → A) (σ .map) (kcycle_factors_product A ks)))
  ≔ let d ≔ finite_decidable_equality A ha in
    let S ≔ Σ (List (Σ Nat (KCyclePermutations A))) (ks ↦ Id (A → A) (σ .map) (kcycle_factors_product A ks)) in
    trunc_map native_truncation (Σ (CycleFactors A) (cs ↦ Id (A → A) (σ .map) (cycle_factors_product A d cs))) S
      (v ↦ (kcycle_factors_of_cycle_factors A d (v .fst),
        concat (A → A) (σ .map) (cycle_factors_product A d (v .fst))
          (kcycle_factors_product A (kcycle_factors_of_cycle_factors A d (v .fst))) (v .snd)
          (funext A (_ ↦ A) (cycle_factors_product A d (v .fst))
            (kcycle_factors_product A (kcycle_factors_of_cycle_factors A d (v .fst)))
            (y ↦ inverse A (kcycle_factors_product A (kcycle_factors_of_cycle_factors A d (v .fst)) y)
              (cycle_factors_product A d (v .fst) y) (kcycle_factors_product_agree A d (v .fst) y)))))
      (finite_cycle_decomposition A ha σ)

{` Then apply xca:perm-prod-transpositions to each factor:
   (a_1 ... a_k) = (a_1 a_k) ... (a_1 a_2) as a word of transpositions. `}
def cycle_transposition_word (A : Type) (a1 : A) (rest : List A) (h : NotInList A a1 rest) : List (Transpositions A)
  ≔ match rest [
  | nil. ↦ nil.
  | cons. b rest ↦ append (Transpositions A) (cycle_transposition_word A a1 rest (h .snd)) (cons. (a1, (b, h .fst)) nil.) ]

def transposition_word_append (A : Type) (d : DecidableEquality A) (w1 w2 : List (Transpositions A)) (x : A)
  : Id A (transposition_word_map A d (append (Transpositions A) w1 w2) x)
      (transposition_word_map A d w1 (transposition_word_map A d w2 x))
  ≔ match w1 [
  | nil. ↦ refl (transposition_word_map A d w2 x)
  | cons. t rest ↦ refl (transposition A d (t .fst) (t .snd .fst)) (transposition_word_append A d rest w2 x) ]

def cycle_transposition_word_map (A : Type) (d : DecidableEquality A) (a1 : A) (rest : List A) (h : NotInList A a1 rest)
  (x : A) : Id A (transposition_word_map A d (cycle_transposition_word A a1 rest h) x) (transposition_chain A d a1 rest x)
  ≔ match rest [
  | nil. ↦ refl x
  | cons. b rest ↦ concat A
      (transposition_word_map A d (cycle_transposition_word A a1 (cons. b rest) h) x)
      (transposition_word_map A d (cycle_transposition_word A a1 rest (h .snd)) (transposition A d a1 b x))
      (transposition_chain A d a1 rest (transposition A d a1 b x))
      (transposition_word_append A d (cycle_transposition_word A a1 rest (h .snd)) (cons. (a1, (b, h .fst)) nil.) x)
      (cycle_transposition_word_map A d a1 rest (h .snd) (transposition A d a1 b x)) ]

def cycle_factors_word (A : Type) (cs : CycleFactors A) : List (Transpositions A)
  ≔ match cs [
  | nil. ↦ nil.
  | cons. c rest ↦ append (Transpositions A)
      (cycle_transposition_word A (c .snd .fst) (c .snd .snd .fst) (c .snd .snd .snd .snd .fst))
      (cycle_factors_word A rest) ]

def cycle_factors_word_map (A : Type) (d : DecidableEquality A) (cs : CycleFactors A) (x : A)
  : Id A (transposition_word_map A d (cycle_factors_word A cs) x) (cycle_factors_product A d cs x)
  ≔ match cs [
  | nil. ↦ refl x
  | cons. c rest ↦
      let a1 ≔ c .snd .fst in
      let r ≔ c .snd .snd .fst in
      let W ≔ cycle_transposition_word A a1 r (c .snd .snd .snd .snd .fst) in
      let y ≔ cycle_factors_product A d rest x in
      calc transposition_word_map A d (append (Transpositions A) W (cycle_factors_word A rest)) x
        = transposition_word_map A d W (transposition_word_map A d (cycle_factors_word A rest) x)
          by transposition_word_append A d W (cycle_factors_word A rest) x
        = transposition_word_map A d W y by refl (transposition_word_map A d W) (cycle_factors_word_map A d rest x)
        = transposition_chain A d a1 r y by cycle_transposition_word_map A d a1 r (c .snd .snd .snd .snd .fst) y
        = cycle_notation A d a1 r y
          by inverse A (cycle_notation A d a1 r y) (transposition_chain A d a1 r y)
            (cycle_transposition_product_at A d a1 r (c .snd .snd .snd .snd) y) ∎ ]

{` The corollary after xca:perm-prod-transpositions by the book's route:
   explicitly for Fin n, merely for every finite set. `}
def fin_transposition_word_via_cycles (n : Nat) (σ : Equiv (Fin n) (Fin n))
  : TranspositionWord (Fin n) (fin_decidable_equality n) σ
  ≔ let d ≔ fin_decidable_equality n in
    let D ≔ fin_cycle_decomposition n σ in
    (cycle_factors_word (Fin n) (D .fst),
     x ↦ concat (Fin n) (σ .map x) (cycle_factors_product (Fin n) d (D .fst) x)
       (transposition_word_map (Fin n) d (cycle_factors_word (Fin n) (D .fst)) x)
       (D .snd (refl x))
       (inverse (Fin n) (transposition_word_map (Fin n) d (cycle_factors_word (Fin n) (D .fst)) x)
         (cycle_factors_product (Fin n) d (D .fst) x) (cycle_factors_word_map (Fin n) d (D .fst) x)))

def finite_transposition_generated_via_cycles (A : Type) (ha : IsFinite A) (σ : Equiv A A)
  : TranspositionGenerated A (finite_decidable_equality A ha) σ
  ≔ let d ≔ finite_decidable_equality A ha in
    let W ≔ Σ (List (Transpositions A)) (w ↦ Id (A → A) (σ .map) (transposition_word_map A d w)) in
    trunc_map native_truncation (Σ (CycleFactors A) (cs ↦ Id (A → A) (σ .map) (cycle_factors_product A d cs))) W
      (v ↦ (cycle_factors_word A (v .fst),
        concat (A → A) (σ .map) (cycle_factors_product A d (v .fst)) (transposition_word_map A d (cycle_factors_word A (v .fst)))
          (v .snd)
          (funext A (_ ↦ A) (cycle_factors_product A d (v .fst)) (transposition_word_map A d (cycle_factors_word A (v .fst)))
            (x ↦ inverse A (transposition_word_map A d (cycle_factors_word A (v .fst)) x)
              (cycle_factors_product A d (v .fst) x) (cycle_factors_word_map A d (v .fst) x)))))
      (finite_cycle_decomposition A ha σ)

{` rem:cycle-vs-cycle by the printed route, for any circle signature C
   (the circle is constructed in module 223).  A permutation corresponds to
   a covering of the circle (thm:coveringsofS1perms); its total space is the
   sum of its connected components; each component is a connected covering,
   hence a cycle (thm:cycset-connS1cover); and the permutation is the sum of
   these cycles over the set of components. `}
def fiberwise_transport_natural (B : Type) (P Q : B → Type) (φ : (b : B) → P b → Q b) (b0 b1 : B)
  (l : Id B b0 b1) (u : P b0)
  : Id (Q b1) (φ b1 (transport B P b0 b1 l u)) (transport B Q b0 b1 l (φ b0 u))
  ≔ J B b0 (b1 l ↦ Id (Q b1) (φ b1 (transport B P b0 b1 l u)) (transport B Q b0 b1 l (φ b0 u)))
      (concat (Q b0) (φ b0 (transport B P b0 b0 (refl b0) u)) (φ b0 u) (transport B Q b0 b0 (refl b0) (φ b0 u))
        (refl (φ b0) (transport_refl B P b0 u))
        (inverse (Q b0) (transport B Q b0 b0 (refl b0) (φ b0 u)) (φ b0 u) (transport_refl B Q b0 (φ b0 u))))
      b1 l

def component_member_path (A : Type) (z : SetTrunc A) (a : A) (m : z .fst a .fst) : Id (SetTrunc A) z (set_trunc A a)
  ≔ equiv_inverse_map (Id (SetTrunc A) z (set_trunc A a)) (z .fst a .fst)
      (quotient_class_property A (mere_path_relation A) z a) m

{` Each point lies in exactly one component. `}
def component_membership_prop (A : Type) (a : A) : isProp (Σ (SetTrunc A) (z ↦ z .fst a .fst))
  ≔ u v ↦ subtype_equal (SetTrunc A) (z ↦ z .fst a .fst) (z ↦ z .fst a .snd) u v
      (concat (SetTrunc A) (u .fst) (set_trunc A a) (v .fst) (component_member_path A (u .fst) a (u .snd))
        (inverse (SetTrunc A) (v .fst) (set_trunc A a) (component_member_path A (v .fst) a (v .snd))))

def truncated_component_connected (A : Type) (z : SetTrunc A) : Connected (TruncatedComponent A z)
  ≔ let T ≔ TruncatedComponent A z in
    (trunc_map native_truncation (BookFiber A (SetTrunc A) (set_trunc A) z) T
       (w ↦ (w .fst, quotient_class_property A (mere_path_relation A) z (w .fst) .map (w .snd)))
       (set_trunc_surjective A z),
     u v ↦ trunc_map native_truncation (Id A (u .fst) (v .fst)) (Id T u v)
       (p ↦ subtype_equal A (a ↦ z .fst a .fst) (a ↦ z .fst a .snd) u v p)
       (set_trunc_paths A (u .fst) (v .fst) .map
         (concat (SetTrunc A) (set_trunc A (u .fst)) z (set_trunc A (v .fst))
           (inverse (SetTrunc A) z (set_trunc A (u .fst)) (component_member_path A z (u .fst) (u .snd)))
           (component_member_path A z (v .fst) (v .snd)))))

def component_fiber_reassoc (B : Type) (c : Coverings B) (z : SetTrunc (c .fst)) (b : B)
  : Equiv (Σ (BookFiber (c .fst) B (c .snd .fst) b) (w ↦ z .fst (w .fst) .fst))
      (BookFiber (TruncatedComponent (c .fst) z) B (u ↦ c .snd .fst (u .fst)) b)
  ≔ quasi_inverse_equiv (Σ (BookFiber (c .fst) B (c .snd .fst) b) (w ↦ z .fst (w .fst) .fst))
      (BookFiber (TruncatedComponent (c .fst) z) B (u ↦ c .snd .fst (u .fst)) b)
      (v ↦ ((v .fst .fst, v .snd), v .fst .snd)) (u ↦ ((u .fst .fst, u .snd), u .fst .snd))
      (v ↦ refl v) (u ↦ refl u)

def component_covering_property (B : Type) (c : Coverings B) (z : SetTrunc (c .fst))
  : IsCovering (TruncatedComponent (c .fst) z) B (u ↦ c .snd .fst (u .fst))
  ≔ b ↦ transport Type isSet (Σ (BookFiber (c .fst) B (c .snd .fst) b) (w ↦ z .fst (w .fst) .fst))
      (BookFiber (TruncatedComponent (c .fst) z) B (u ↦ c .snd .fst (u .fst)) b)
      (ua (Σ (BookFiber (c .fst) B (c .snd .fst) b) (w ↦ z .fst (w .fst) .fst))
        (BookFiber (TruncatedComponent (c .fst) z) B (u ↦ c .snd .fst (u .fst)) b)
        (component_fiber_reassoc B c z b))
      (sigma_set (BookFiber (c .fst) B (c .snd .fst) b) (w ↦ z .fst (w .fst) .fst) (c .snd .snd b)
        (w ↦ prop_is_set (z .fst (w .fst) .fst) (z .fst (w .fst) .snd)))

{` The component z of a covering, as a connected covering. `}
def component_covering (B : Type) (c : Coverings B) (z : SetTrunc (c .fst)) : Coverings B
  ≔ (TruncatedComponent (c .fst) z, ((u ↦ c .snd .fst (u .fst)), component_covering_property B c z))

def component_connected_covering (B : Type) (c : Coverings B) (z : SetTrunc (c .fst)) : ConnectedCoverings B
  ≔ (component_covering B c z, truncated_component_connected (c .fst) z)

def circle_component_cycle (C : CircleSignature) (c : Coverings (C .carrier)) (z : SetTrunc (c .fst)) : Cycles
  ≔ circle_connected_coverings_cycles C .map (component_connected_covering (C .carrier) c z)

{` The fiber of a covering is the sum over the components of their fibers. `}
def components_base_fiber_equiv (B : Type) (c : Coverings B) (b : B)
  : Equiv (Σ (SetTrunc (c .fst)) (z ↦ BookFiber (TruncatedComponent (c .fst) z) B (u ↦ c .snd .fst (u .fst)) b))
      (BookFiber (c .fst) B (c .snd .fst) b)
  ≔ let E ≔ c .fst in let π ≔ c .snd .fst in
    let M ≔ ((a ↦ Σ (SetTrunc E) (z ↦ z .fst a .fst)) : E → Type) in
    let X ≔ Σ (SetTrunc E) (z ↦ BookFiber (TruncatedComponent E z) B (u ↦ π (u .fst)) b) in
    let Y ≔ Σ E (a ↦ Product (M a) (Id B b (π a))) in
    let F ≔ BookFiber E B π b in
    compose_equiv X Y F
      (quasi_inverse_equiv X Y
        (x ↦ (x .snd .fst .fst, ((x .fst, x .snd .fst .snd), x .snd .snd)))
        (y ↦ (y .snd .fst .fst, ((y .fst, y .snd .fst .snd), y .snd .snd)))
        (x ↦ refl x) (y ↦ refl y))
      (quasi_inverse_equiv Y F
        (y ↦ (y .fst, y .snd .snd))
        (f ↦ (f .fst, ((set_trunc E (f .fst), mere (Id E (f .fst) (f .fst)) (refl (f .fst))), f .snd)))
        (y ↦ refl ((w ↦ (y .fst, (w, y .snd .snd))) : M (y .fst) → Y)
          (component_membership_prop E (y .fst)
            (set_trunc E (y .fst), mere (Id E (y .fst) (y .fst)) (refl (y .fst))) (y .snd .fst)))
        (f ↦ refl f))

{` The permutation of a covering is isomorphic to the sum, over its set of
   components, of the cycles of the components. `}
def circle_components_permutation_iso (C : CircleSignature) (c : Coverings (C .carrier))
  : PermutationIsomorphisms
      (permutation_sum (SetTrunc (c .fst), set_trunc_set (c .fst)) (z ↦ circle_component_cycle C c z .fst))
      (circle_coverings_permutations C .map c)
  ≔ let S ≔ C .carrier in let E ≔ c .fst in let π ≔ c .snd .fst in
    let P ≔ ((z ↦ (b ↦ BookFiber (TruncatedComponent E z) S (u ↦ π (u .fst)) b)) : SetTrunc E → S → Type) in
    let Q ≔ ((b ↦ BookFiber E S π b) : S → Type) in
    (components_base_fiber_equiv S c (C .base),
     x ↦ fiberwise_transport_natural S (P (x .fst)) Q (b v ↦ (v .fst .fst, v .snd)) (C .base) (C .base) (C .loop)
       (x .snd))

def circle_permutation_covering (C : CircleSignature) (p : Permutations) : Coverings (C .carrier)
  ≔ equiv_inverse_map (Coverings (C .carrier)) Permutations (circle_coverings_permutations C) p

def circle_permutation_cycles_sum (C : CircleSignature) (p : Permutations) : Permutations
  ≔ permutation_sum (SetTrunc (circle_permutation_covering C p .fst), set_trunc_set (circle_permutation_covering C p .fst))
      (z ↦ circle_component_cycle C (circle_permutation_covering C p) z .fst)

{` rem:cycle-vs-cycle: every permutation of a set is the sum of the cycles
   given by the connected components of its covering of the circle. `}
def circle_permutation_cycle_decomposition (C : CircleSignature) (p : Permutations)
  : PermutationIsomorphisms (circle_permutation_cycles_sum C p) p
  ≔ transport Permutations (q ↦ PermutationIsomorphisms (circle_permutation_cycles_sum C p) q)
      (circle_coverings_permutations C .map (circle_permutation_covering C p)) p
      (equiv_counit (Coverings (C .carrier)) Permutations (circle_coverings_permutations C) p)
      (circle_components_permutation_iso C (circle_permutation_covering C p))

def circle_permutation_cycle_decomposition_path (C : CircleSignature) (p : Permutations)
  : Id Permutations (circle_permutation_cycles_sum C p) p
  ≔ equiv_inverse_map (Id Permutations (circle_permutation_cycles_sum C p) p)
      (PermutationIsomorphisms (circle_permutation_cycles_sum C p) p)
      (permutation_paths_equiv (circle_permutation_cycles_sum C p) p)
      (circle_permutation_cycle_decomposition C p)

{` Instantiated at the circle constructed in modules 220–223. `}
def S1_circle_permutation_cycle_decomposition (p : Permutations)
  : PermutationIsomorphisms (circle_permutation_cycles_sum constructed_circle p) p
  ≔ circle_permutation_cycle_decomposition constructed_circle p

def S1_circle_permutation_cycle_decomposition_path (p : Permutations)
  : Id Permutations (circle_permutation_cycles_sum constructed_circle p) p
  ≔ circle_permutation_cycle_decomposition_path constructed_circle p
