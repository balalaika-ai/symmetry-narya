export "407-group-family-products"

{` Chapter 4, sec:sign-homomorphism, preliminaries. Parity of natural numbers
   (false = even, true = odd), Boolean exclusive or, the number of points of a
   finite set where a Boolean function is true, and a toolkit for two-element
   types: decidable equality, the other point, the Boolean "differ" indicator and
   whether an automorphism moves the points. `}

def nat_odd (n : Nat) : Bool ≔ match n [ zero. ↦ false. | suc. k ↦ bool_not (nat_odd k) ]

def bool_xor (a b : Bool) : Bool ≔ match a [ false. ↦ b | true. ↦ bool_not b ]

def bool_xor_false_right (a : Bool) : Id Bool (bool_xor a false.) a
  ≔ match a [ false. ↦ refl (false. : Bool) | true. ↦ refl (true. : Bool) ]

def bool_xor_self (a : Bool) : Id Bool (bool_xor a a) false.
  ≔ match a [ false. ↦ refl (false. : Bool) | true. ↦ refl (false. : Bool) ]

def bool_xor_comm (a b : Bool) : Id Bool (bool_xor a b) (bool_xor b a)
  ≔ match a, b [
  | false., false. ↦ refl (false. : Bool)
  | false., true. ↦ refl (true. : Bool)
  | true., false. ↦ refl (true. : Bool)
  | true., true. ↦ refl (false. : Bool) ]

def bool_xor_not_right (a b : Bool) : Id Bool (bool_xor a (bool_not b)) (bool_not (bool_xor a b))
  ≔ match a, b [
  | false., false. ↦ refl (true. : Bool)
  | false., true. ↦ refl (false. : Bool)
  | true., false. ↦ refl (false. : Bool)
  | true., true. ↦ refl (true. : Bool) ]

def bool_xor_assoc (a b c : Bool) : Id Bool (bool_xor (bool_xor a b) c) (bool_xor a (bool_xor b c))
  ≔ match a, b, c [
  | false., false., false. ↦ refl (false. : Bool)
  | false., false., true. ↦ refl (true. : Bool)
  | false., true., false. ↦ refl (true. : Bool)
  | false., true., true. ↦ refl (false. : Bool)
  | true., false., false. ↦ refl (true. : Bool)
  | true., false., true. ↦ refl (false. : Bool)
  | true., true., false. ↦ refl (false. : Bool)
  | true., true., true. ↦ refl (true. : Bool) ]

def bool_xor_interchange (a b c d : Bool)
  : Id Bool (bool_xor (bool_xor a b) (bool_xor c d)) (bool_xor (bool_xor a c) (bool_xor b d))
  ≔ match a, b, c, d [
  | false., false., false., false. ↦ refl (false. : Bool)
  | false., false., false., true. ↦ refl (true. : Bool)
  | false., false., true., false. ↦ refl (true. : Bool)
  | false., false., true., true. ↦ refl (false. : Bool)
  | false., true., false., false. ↦ refl (true. : Bool)
  | false., true., false., true. ↦ refl (false. : Bool)
  | false., true., true., false. ↦ refl (false. : Bool)
  | false., true., true., true. ↦ refl (true. : Bool)
  | true., false., false., false. ↦ refl (true. : Bool)
  | true., false., false., true. ↦ refl (false. : Bool)
  | true., false., true., false. ↦ refl (false. : Bool)
  | true., false., true., true. ↦ refl (true. : Bool)
  | true., true., false., false. ↦ refl (false. : Bool)
  | true., true., false., true. ↦ refl (true. : Bool)
  | true., true., true., false. ↦ refl (true. : Bool)
  | true., true., true., true. ↦ refl (false. : Bool) ]

def bool_xor_path (a a' b b' : Bool) (p : Id Bool a a') (q : Id Bool b b')
  : Id Bool (bool_xor a b) (bool_xor a' b')
  ≔ refl bool_xor p q

def bool_not_false_true (b : Bool) (p : Id Bool (bool_not b) false.) : Id Bool b true.
  ≔ match b [ false. ↦ absurd (Id Bool false. true.) (bool_encode true. false. p) | true. ↦ refl (true. : Bool) ]

def bool_not_true_false (b : Bool) (p : Id Bool (bool_not b) true.) : Id Bool b false.
  ≔ match b [ false. ↦ refl (false. : Bool) | true. ↦ absurd (Id Bool true. false.) (bool_encode false. true. p) ]

def bool_false_not_true (b : Bool) (p : Id Bool b false.) (q : Id Bool b true.) : Empty
  ≔ bool_encode false. true. (concat Bool false. b true. (inverse Bool b false. p) q)

{` Parity is additive: (m + n) is odd iff exactly one of m, n is odd. `}
def nat_odd_add (m n : Nat) : Id Bool (nat_odd (add m n)) (bool_xor (nat_odd m) (nat_odd n))
  ≔ match n [
  | zero. ↦ inverse Bool (bool_xor (nat_odd m) false.) (nat_odd m) (bool_xor_false_right (nat_odd m))
  | suc. k ↦ concat Bool (bool_not (nat_odd (add m k))) (bool_not (bool_xor (nat_odd m) (nat_odd k)))
      (bool_xor (nat_odd m) (bool_not (nat_odd k)))
      (refl bool_not (nat_odd_add m k))
      (inverse Bool (bool_xor (nat_odd m) (bool_not (nat_odd k))) (bool_not (bool_xor (nat_odd m) (nat_odd k)))
        (bool_xor_not_right (nat_odd m) (nat_odd k))) ]

def nat_odd_bool_to_nat (b : Bool) : Id Bool (nat_odd (bool_to_nat b)) b
  ≔ match b [ false. ↦ refl (false. : Bool) | true. ↦ refl (true. : Bool) ]

{` "Even" in the book's sense: n = k + k for some k. It is a proposition and
   is equivalent to nat_odd n = false. `}
def IsEvenNat (n : Nat) : Type ≔ Σ Nat (k ↦ Id Nat n (add k k))

def nat_double_injective (k l : Nat) (p : Id Nat (add k k) (add l l)) : Id Nat k l
  ≔ match k, l [
  | zero., zero. ↦ refl (zero. : Nat)
  | zero., suc. l ↦ absurd (Id Nat zero. (suc. l))
      (nat_encode zero. (suc. (add (suc. l) l)) p)
  | suc. k, zero. ↦ absurd (Id Nat (suc. k) zero.)
      (nat_encode (suc. (add (suc. k) k)) zero. p)
  | suc. k, suc. l ↦ refl ((x ↦ suc. x) : Nat → Nat)
      (nat_double_injective k l
        (refl nat_pred
          (calc (suc. (add k k) : Nat) = add (suc. k) k by inverse Nat (add (suc. k) k) (suc. (add k k)) (add_suc_left k k)
            = add (suc. l) l by refl nat_pred p
            = suc. (add l l) by add_suc_left l l ∎))) ]

def is_even_nat_prop (n : Nat) : isProp (IsEvenNat n)
  ≔ u v ↦ subtype_equal Nat (k ↦ Id Nat n (add k k)) (k ↦ nat_set n (add k k)) u v
      (nat_double_injective (u .fst) (v .fst)
        (concat Nat (add (u .fst) (u .fst)) n (add (v .fst) (v .fst))
          (inverse Nat n (add (u .fst) (u .fst)) (u .snd)) (v .snd)))

def nat_odd_double (k : Nat) : Id Bool (nat_odd (add k k)) false.
  ≔ concat Bool (nat_odd (add k k)) (bool_xor (nat_odd k) (nat_odd k)) false.
      (nat_odd_add k k) (bool_xor_self (nat_odd k))

def nat_parity_witness (n : Nat)
  : Product (Id Bool (nat_odd n) false. → IsEvenNat n)
      (Id Bool (nat_odd n) true. → Σ Nat (k ↦ Id Nat n (suc. (add k k))))
  ≔ match n [
  | zero. ↦ (_ ↦ (zero., refl (zero. : Nat)),
             q ↦ absurd (Σ Nat (k ↦ Id Nat zero. (suc. (add k k)))) (bool_encode false. true. q))
  | suc. m ↦
      (q ↦ let w ≔ nat_parity_witness m .snd (bool_not_false_true (nat_odd m) q) in
        (suc. (w .fst),
          calc (suc. m : Nat) = suc. (suc. (add (w .fst) (w .fst))) by refl ((x ↦ suc. x) : Nat → Nat) (w .snd)
            = suc. (add (suc. (w .fst)) (w .fst))
              by refl ((x ↦ suc. x) : Nat → Nat)
                (inverse Nat (add (suc. (w .fst)) (w .fst)) (suc. (add (w .fst) (w .fst))) (add_suc_left (w .fst) (w .fst)))
            = add (suc. (w .fst)) (suc. (w .fst)) by refl (add (suc. (w .fst)) (suc. (w .fst))) ∎),
       q ↦ let w ≔ nat_parity_witness m .fst (bool_not_true_false (nat_odd m) q) in
        (w .fst, refl ((x ↦ suc. x) : Nat → Nat) (w .snd))) ]

def is_even_nat_iff (n : Nat) : Equiv (IsEvenNat n) (Id Bool (nat_odd n) false.)
  ≔ iff_equiv (IsEvenNat n) (Id Bool (nat_odd n) false.) (is_even_nat_prop n) (bool_set (nat_odd n) false.)
      (w ↦ concat Bool (nat_odd n) (nat_odd (add (w .fst) (w .fst))) false.
        (refl nat_odd (w .snd)) (nat_odd_double (w .fst)))
      (nat_parity_witness n .fst)

{` The number of points of a finite set where a Boolean function is true:
   the cardinality of the decidable subset { e | b(e) = true }. `}
def bool_decide_true (b : Bool) : Decidable (Id Bool b true.)
  ≔ match b [ false. ↦ inr. (q ↦ bool_encode false. true. q) | true. ↦ inl. (refl (true. : Bool)) ]

def finite_true_subset (E : Type) (hE : IsFinite E) (b : E → Bool) : IsFinite (Σ E (e ↦ Id Bool (b e) true.))
  ≔ finite_decidable_subset E hE (e ↦ Id Bool (b e) true.) (e ↦ bool_set (b e) true.) (e ↦ bool_decide_true (b e))

def finite_true_count (E : Type) (hE : IsFinite E) (b : E → Bool) : Nat
  ≔ cardinality (Σ E (e ↦ Id Bool (b e) true.)) (finite_true_subset E hE b)

{` On the standard finite sets it is the recursive count true_count of module 178. `}
def finite_true_count_fin (n : Nat) (hE : IsFinite (Fin n)) (b : Fin n → Bool)
  : Id Nat (finite_true_count (Fin n) hE b) (true_count n b)
  ≔ cardinality_from_path (BoolCarrier n b) (finite_true_subset (Fin n) hE b) (true_count n b)
      (ua (BoolCarrier n b) (Fin (true_count n b)) (bool_carrier_fin n b))

def nat_odd_true_count_step (m : Nat) (f : Fin (suc. m) → Bool)
  : Id Bool (nat_odd (true_count (suc. m) f)) (bool_xor (nat_odd (true_count m (a ↦ f (inl. a)))) (f (inr. star.)))
  ≔ concat Bool (nat_odd (true_count (suc. m) f))
      (bool_xor (nat_odd (true_count m (a ↦ f (inl. a)))) (nat_odd (bool_to_nat (f (inr. star.)))))
      (bool_xor (nat_odd (true_count m (a ↦ f (inl. a)))) (f (inr. star.)))
      (nat_odd_add (true_count m (a ↦ f (inl. a))) (bool_to_nat (f (inr. star.))))
      (refl (bool_xor (nat_odd (true_count m (a ↦ f (inl. a))))) (nat_odd_bool_to_nat (f (inr. star.))))

def true_count_odd_xor (n : Nat) (b c : Fin n → Bool)
  : Id Bool (nat_odd (true_count n (e ↦ bool_xor (b e) (c e))))
      (bool_xor (nat_odd (true_count n b)) (nat_odd (true_count n c)))
  ≔ match n [
  | zero. ↦ refl (false. : Bool)
  | suc. m ↦
      let tb ≔ nat_odd (true_count m (a ↦ b (inl. a))) in
      let tc ≔ nat_odd (true_count m (a ↦ c (inl. a))) in
      calc nat_odd (true_count (suc. m) (e ↦ bool_xor (b e) (c e)))
        = bool_xor (nat_odd (true_count m (a ↦ bool_xor (b (inl. a)) (c (inl. a)))))
            (bool_xor (b (inr. star.)) (c (inr. star.)))
          by nat_odd_true_count_step m (e ↦ bool_xor (b e) (c e))
        = bool_xor (bool_xor tb tc) (bool_xor (b (inr. star.)) (c (inr. star.)))
          by refl ((x ↦ bool_xor x (bool_xor (b (inr. star.)) (c (inr. star.)))) : Bool → Bool)
            (true_count_odd_xor m (a ↦ b (inl. a)) (a ↦ c (inl. a)))
        = bool_xor (bool_xor tb (b (inr. star.))) (bool_xor tc (c (inr. star.)))
          by bool_xor_interchange tb tc (b (inr. star.)) (c (inr. star.))
        = bool_xor (nat_odd (true_count (suc. m) b)) (nat_odd (true_count (suc. m) c))
          by bool_xor_path (bool_xor tb (b (inr. star.))) (nat_odd (true_count (suc. m) b))
            (bool_xor tc (c (inr. star.))) (nat_odd (true_count (suc. m) c))
            (inverse Bool (nat_odd (true_count (suc. m) b)) (bool_xor tb (b (inr. star.))) (nat_odd_true_count_step m b))
            (inverse Bool (nat_odd (true_count (suc. m) c)) (bool_xor tc (c (inr. star.))) (nat_odd_true_count_step m c)) ∎ ]

def FiniteTrueCountXor (A : Type) : Type
  ≔ (hA : IsFinite A) (b c : A → Bool) →
      Id Bool (nat_odd (finite_true_count A hA (e ↦ bool_xor (b e) (c e))))
        (bool_xor (nat_odd (finite_true_count A hA b)) (nat_odd (finite_true_count A hA c)))

def finite_true_count_xor_prop (A : Type) : isProp (FiniteTrueCountXor A)
  ≔ pi_prop (IsFinite A) (hA ↦ (b c : A → Bool) →
      Id Bool (nat_odd (finite_true_count A hA (e ↦ bool_xor (b e) (c e))))
        (bool_xor (nat_odd (finite_true_count A hA b)) (nat_odd (finite_true_count A hA c))))
      (hA ↦ pi_prop (A → Bool) (b ↦ (c : A → Bool) →
        Id Bool (nat_odd (finite_true_count A hA (e ↦ bool_xor (b e) (c e))))
          (bool_xor (nat_odd (finite_true_count A hA b)) (nat_odd (finite_true_count A hA c))))
        (b ↦ pi_prop (A → Bool) (c ↦
          Id Bool (nat_odd (finite_true_count A hA (e ↦ bool_xor (b e) (c e))))
            (bool_xor (nat_odd (finite_true_count A hA b)) (nat_odd (finite_true_count A hA c))))
          (c ↦ bool_set (nat_odd (finite_true_count A hA (e ↦ bool_xor (b e) (c e))))
            (bool_xor (nat_odd (finite_true_count A hA b)) (nat_odd (finite_true_count A hA c))))))

def fin_true_count_xor (n : Nat) : FiniteTrueCountXor (Fin n)
  ≔ hA b c ↦ calc
      nat_odd (finite_true_count (Fin n) hA (e ↦ bool_xor (b e) (c e)))
      = nat_odd (true_count n (e ↦ bool_xor (b e) (c e)))
        by refl nat_odd (finite_true_count_fin n hA (e ↦ bool_xor (b e) (c e)))
      = bool_xor (nat_odd (true_count n b)) (nat_odd (true_count n c)) by true_count_odd_xor n b c
      = bool_xor (nat_odd (finite_true_count (Fin n) hA b)) (nat_odd (finite_true_count (Fin n) hA c))
        by bool_xor_path (nat_odd (true_count n b)) (nat_odd (finite_true_count (Fin n) hA b))
          (nat_odd (true_count n c)) (nat_odd (finite_true_count (Fin n) hA c))
          (refl nat_odd (inverse Nat (finite_true_count (Fin n) hA b) (true_count n b) (finite_true_count_fin n hA b)))
          (refl nat_odd (inverse Nat (finite_true_count (Fin n) hA c) (true_count n c) (finite_true_count_fin n hA c))) ∎

{` The parity of the number of points where b xor c is true is the xor of the
   parities: the key additivity behind transitivity of the parity relation. `}
def finite_true_count_xor (E : Type) (hE : IsFinite E) : FiniteTrueCountXor E
  ≔ finite_ind_prop FiniteTrueCountXor finite_true_count_xor_prop fin_true_count_xor E hE

{` Counts only depend on the function (pointwise), and counts of an all-false function are 0. `}
def finite_true_count_homotopy (E : Type) (hE : IsFinite E) (b c : E → Bool) (h : (e : E) → Id Bool (b e) (c e))
  : Id Nat (finite_true_count E hE b) (finite_true_count E hE c)
  ≔ refl ((f ↦ finite_true_count E hE f) : (E → Bool) → Nat) (funext E (_ ↦ Bool) b c h)

def finite_true_count_false (E : Type) (hE : IsFinite E) (b : E → Bool) (h : (e : E) → Id Bool (b e) false.)
  : Id Nat (finite_true_count E hE b) zero.
  ≔ cardinality_from_path (Σ E (e ↦ Id Bool (b e) true.)) (finite_true_subset E hE b) zero.
      (ua (Σ E (e ↦ Id Bool (b e) true.)) Empty
        (quasi_inverse_equiv (Σ E (e ↦ Id Bool (b e) true.)) Empty
          (u ↦ bool_false_not_true (b (u .fst)) (h (u .fst)) (u .snd)) (x ↦ match x [])
          (u ↦ match bool_false_not_true (b (u .fst)) (h (u .fst)) (u .snd) []) (x ↦ match x [])))

{` A Boolean function true at exactly one point has count 1. `}
def finite_true_count_single (E : Type) (hE : IsFinite E) (b : E → Bool) (e0 : E)
  (h : (e : E) → Equiv (Id Bool (b e) true.) (Id E e e0))
  : Id Nat (finite_true_count E hE b) (suc. zero.)
  ≔ let S ≔ Σ E (e ↦ Id Bool (b e) true.) in
    let c : S ≔ (e0, equiv_inverse_map (Id Bool (b e0) true.) (Id E e0 e0) (h e0) (refl e0)) in
    let hs : isProp S ≔ u v ↦ subtype_equal E (e ↦ Id Bool (b e) true.) (e ↦ bool_set (b e) true.) u v
      (concat E (u .fst) e0 (v .fst) (h (u .fst) .map (u .snd)) (inverse E (v .fst) e0 (h (v .fst) .map (v .snd)))) in
    inhabited_prop_cardinality S hs (finite_true_subset E hE b) c

{` Decisions turned into Booleans: false when the proposition holds. `}
def decision_differ (P : Type) (d : Decidable P) : Bool ≔ match d [ inl. _ ↦ false. | inr. _ ↦ true. ]

def decision_differ_yes (P : Type) (d : Decidable P) (p : P) : Id Bool (decision_differ P d) false.
  ≔ match d [ inl. _ ↦ refl (false. : Bool) | inr. n ↦ absurd (Id Bool true. false.) (n p) ]

def decision_differ_no (P : Type) (d : Decidable P) (n : Not P) : Id Bool (decision_differ P d) true.
  ≔ match d [ inl. p ↦ absurd (Id Bool false. true.) (n p) | inr. _ ↦ refl (true. : Bool) ]

def decision_differ_false (P : Type) (d : Decidable P) (q : Id Bool (decision_differ P d) false.) : P
  ≔ match d [ inl. p ↦ p | inr. _ ↦ absurd P (bool_encode true. false. q) ]

def decision_differ_true (P : Type) (d : Decidable P) (q : Id Bool (decision_differ P d) true.) : Not P
  ≔ match d [ inl. _ ↦ absurd (Not P) (bool_encode false. true. q) | inr. n ↦ n ]

def decision_differ_iff (P Q : Type) (d : Decidable P) (d' : Decidable Q) (f : P → Q) (g : Q → P)
  : Id Bool (decision_differ P d) (decision_differ Q d')
  ≔ match d [
  | inl. p ↦ inverse Bool (decision_differ Q d') false. (decision_differ_yes Q d' (f p))
  | inr. n ↦ inverse Bool (decision_differ Q d') true. (decision_differ_no Q d' (q ↦ n (g q))) ]

{` Two-element types: elimination into propositions from the Booleans. `}
def two_element_prop_elim (P : Type → Type) (A : Type) (h : TwoElement A) (hp : isProp (P A)) (base : P Bool) : P A
  ≔ mere_rec (Id Type Bool A) (P A) hp (p ↦ transport Type P Bool A p base) (two_as_bool A h)

def bool_ne_ne (x y z : Bool) (nxy : Not (Id Bool x y)) (nzy : Not (Id Bool z y)) : Id Bool x z
  ≔ match x, y, z [
  | false., false., _ ↦ absurd (Id Bool false. z) (nxy (refl (false. : Bool)))
  | true., true., _ ↦ absurd (Id Bool true. z) (nxy (refl (true. : Bool)))
  | false., true., false. ↦ refl (false. : Bool)
  | false., true., true. ↦ absurd (Id Bool false. true.) (nzy (refl (true. : Bool)))
  | true., false., true. ↦ refl (true. : Bool)
  | true., false., false. ↦ absurd (Id Bool true. false.) (nzy (refl (false. : Bool))) ]

{` In a two-element type, two points different from a third one are equal. `}
def two_element_ne_ne (A : Type) (h : TwoElement A) (x y z : A)
  (nxy : Not (Id A x y)) (nzy : Not (Id A z y)) : Id A x z
  ≔ two_element_prop_elim (X ↦ (x y z : X) → Not (Id X x y) → Not (Id X z y) → Id X x z) A h
      (pi_prop A (x ↦ (y z : A) → Not (Id A x y) → Not (Id A z y) → Id A x z)
        (x ↦ pi_prop A (y ↦ (z : A) → Not (Id A x y) → Not (Id A z y) → Id A x z)
          (y ↦ pi_prop A (z ↦ Not (Id A x y) → Not (Id A z y) → Id A x z)
            (z ↦ pi_prop (Not (Id A x y)) (_ ↦ Not (Id A z y) → Id A x z)
              (_ ↦ pi_prop (Not (Id A z y)) (_ ↦ Id A x z)
                (_ ↦ two_element_set A h x z))))))
      bool_ne_ne x y z nxy nzy

def two_element_has_other (A : Type) (h : TwoElement A) (x : A) : Mere (Σ A (y ↦ Not (Id A y x)))
  ≔ two_element_prop_elim (X ↦ (x : X) → Mere (Σ X (y ↦ Not (Id X y x)))) A h
      (pi_prop A (x ↦ Mere (Σ A (y ↦ Not (Id A y x)))) (x ↦ mere_isprop (Σ A (y ↦ Not (Id A y x)))))
      (b ↦ mere (Σ Bool (y ↦ Not (Id Bool y b))) (bool_not b, bool_not_no_fixed_point b)) x

def two_element_mere_point (A : Type) (h : TwoElement A) : Mere A
  ≔ mere_rec (Id Type (Fin two) A) (Mere A) (mere_isprop A)
      (p ↦ mere A (transport Type (X ↦ X) (Fin two) A p (inr. star.))) h

def two_element_decidable_equality (A : Type) (h : TwoElement A) : DecidableEquality A
  ≔ finite_decidable_equality A (two_element_finite A h)

def two_element_other_prop (A : Type) (h : TwoElement A) (x : A) : isProp (Σ A (y ↦ Not (Id A y x)))
  ≔ u v ↦ subtype_equal A (y ↦ Not (Id A y x)) (y ↦ negation_prop (Id A y x)) u v
      (two_element_ne_ne A h (u .fst) x (v .fst) (u .snd) (v .snd))

def two_element_other_point (A : Type) (h : TwoElement A) (x : A) : Σ A (y ↦ Not (Id A y x))
  ≔ mere_rec (Σ A (y ↦ Not (Id A y x))) (Σ A (y ↦ Not (Id A y x))) (two_element_other_prop A h x)
      (u ↦ u) (two_element_has_other A h x)

{` The other point of a two-element type. `}
def two_element_other (A : Type) (h : TwoElement A) (x : A) : A ≔ two_element_other_point A h x .fst

def two_element_other_ne (A : Type) (h : TwoElement A) (x : A) : Not (Id A (two_element_other A h x) x)
  ≔ two_element_other_point A h x .snd

def two_element_other_unique (A : Type) (h : TwoElement A) (x y : A) (n : Not (Id A y x))
  : Id A y (two_element_other A h x)
  ≔ two_element_ne_ne A h y x (two_element_other A h x) n (two_element_other_ne A h x)

{` differ(x, y) is false if x = y and true otherwise. `}
def two_differ (A : Type) (h : TwoElement A) (x y : A) : Bool
  ≔ decision_differ (Id A x y) (two_element_decidable_equality A h x y)

def two_differ_eq (A : Type) (h : TwoElement A) (x y : A) (p : Id A x y) : Id Bool (two_differ A h x y) false.
  ≔ decision_differ_yes (Id A x y) (two_element_decidable_equality A h x y) p

def two_differ_ne (A : Type) (h : TwoElement A) (x y : A) (n : Not (Id A x y)) : Id Bool (two_differ A h x y) true.
  ≔ decision_differ_no (Id A x y) (two_element_decidable_equality A h x y) n

def two_differ_false (A : Type) (h : TwoElement A) (x y : A) (q : Id Bool (two_differ A h x y) false.) : Id A x y
  ≔ decision_differ_false (Id A x y) (two_element_decidable_equality A h x y) q

def two_differ_true (A : Type) (h : TwoElement A) (x y : A) (q : Id Bool (two_differ A h x y) true.) : Not (Id A x y)
  ≔ decision_differ_true (Id A x y) (two_element_decidable_equality A h x y) q

def two_differ_refl (A : Type) (h : TwoElement A) (x : A) : Id Bool (two_differ A h x x) false.
  ≔ two_differ_eq A h x x (refl x)

def two_differ_symm (A : Type) (h : TwoElement A) (x y : A) : Id Bool (two_differ A h x y) (two_differ A h y x)
  ≔ decision_differ_iff (Id A x y) (Id A y x) (two_element_decidable_equality A h x y)
      (two_element_decidable_equality A h y x) (inverse A x y) (inverse A y x)

{` The cocycle law differ(x, z) = differ(x, y) xor differ(y, z). `}
def two_differ_cocycle (A : Type) (h : TwoElement A) (x y z : A)
  : Id Bool (two_differ A h x z) (bool_xor (two_differ A h x y) (two_differ A h y z))
  ≔ let d ≔ two_differ A h in
    match two_element_decidable_equality A h x y [
    | inl. p ↦ calc d x z = d y z by refl ((w ↦ d w z) : A → Bool) p
        = bool_xor false. (d y z) by refl (d y z)
        = bool_xor (d x y) (d y z) by bool_xor_path false. (d x y) (d y z) (d y z)
            (inverse Bool (d x y) false. (two_differ_eq A h x y p)) (refl (d y z)) ∎
    | inr. nxy ↦ match two_element_decidable_equality A h y z [
      | inl. q ↦ calc d x z = true. by two_differ_ne A h x z
            (r ↦ nxy (concat A x z y r (inverse A y z q)))
          = bool_xor true. false. by refl (true. : Bool)
          = bool_xor (d x y) (d y z) by bool_xor_path true. (d x y) false. (d y z)
              (inverse Bool (d x y) true. (two_differ_ne A h x y nxy))
              (inverse Bool (d y z) false. (two_differ_eq A h y z q)) ∎
      | inr. nyz ↦ calc d x z = false. by two_differ_eq A h x z
            (two_element_ne_ne A h x y z nxy (r ↦ nyz (inverse A z y r)))
          = bool_xor true. true. by refl (false. : Bool)
          = bool_xor (d x y) (d y z) by bool_xor_path true. (d x y) true. (d y z)
              (inverse Bool (d x y) true. (two_differ_ne A h x y nxy))
              (inverse Bool (d y z) true. (two_differ_ne A h y z nyz)) ∎ ] ]

{` differ is invariant under equivalences of two-element types. `}
def two_differ_equiv (A B : Type) (hA : TwoElement A) (hB : TwoElement B) (e : Equiv A B) (x y : A)
  : Id Bool (two_differ B hB (e .map x) (e .map y)) (two_differ A hA x y)
  ≔ decision_differ_iff (Id B (e .map x) (e .map y)) (Id A x y)
      (two_element_decidable_equality B hB (e .map x) (e .map y)) (two_element_decidable_equality A hA x y)
      (q ↦ calc x = equiv_inverse_map A B e (e .map x) by equiv_unit A B e x
        = equiv_inverse_map A B e (e .map y) by refl (equiv_inverse_map A B e) q
        = y by equiv_retraction A B e y ∎)
      (q ↦ refl (e .map) q)

{` Whether an automorphism of a two-element type moves the points. It is
   computed at any point; this does not depend on the point. `}
def two_moves_at (A : Type) (h : TwoElement A) (a : A → A) (x : A) : Bool ≔ two_differ A h x (a x)

def equiv_injective_path (A B : Type) (e : Equiv A B) (x y : A) (q : Id B (e .map x) (e .map y)) : Id A x y
  ≔ calc x = equiv_inverse_map A B e (e .map x) by equiv_unit A B e x
      = equiv_inverse_map A B e (e .map y) by refl (equiv_inverse_map A B e) q
      = y by equiv_retraction A B e y ∎

def two_moves_constant (A : Type) (h : TwoElement A) (a : Equiv A A) (x y : A)
  : Id Bool (two_moves_at A h (a .map) x) (two_moves_at A h (a .map) y)
  ≔ let d ≔ two_differ A h in
    match two_element_decidable_equality A h x y [
    | inl. p ↦ refl ((w ↦ d w (a .map w)) : A → Bool) p
    | inr. nxy ↦ match two_element_decidable_equality A h (a .map x) x [
      | inl. fx ↦ calc d x (a .map x) = false. by two_differ_eq A h x (a .map x) (inverse A (a .map x) x fx)
          = d y (a .map y) by inverse Bool (d y (a .map y)) false. (two_differ_eq A h y (a .map y)
              (inverse A (a .map y) y (two_element_ne_ne A h (a .map y) x y
                (r ↦ nxy (equiv_injective_path A A a x y (concat A (a .map x) x (a .map y) fx (inverse A (a .map y) x r))))
                (r ↦ nxy (inverse A y x r))))) ∎
      | inr. nfx ↦ calc d x (a .map x) = true. by two_differ_ne A h x (a .map x) (r ↦ nfx (inverse A x (a .map x) r))
          = d y (a .map y) by inverse Bool (d y (a .map y)) true. (two_differ_ne A h y (a .map y)
              (r ↦ nxy (equiv_injective_path A A a x y
                (calc a .map x = y by two_element_ne_ne A h (a .map x) x y nfx (s ↦ nxy (inverse A y x s))
                  = a .map y by r ∎)))) ∎ ] ]

def two_moves (A : Type) (h : TwoElement A) (a : Equiv A A) : Bool
  ≔ weakly_constant_rec A Bool (two_moves_at A h (a .map)) bool_set (two_moves_constant A h a)
      (two_element_mere_point A h)

def two_moves_value (A : Type) (h : TwoElement A) (a : Equiv A A) (x : A)
  : Id Bool (two_moves A h a) (two_differ A h x (a .map x))
  ≔ weakly_constant_rec_value A Bool (two_moves_at A h (a .map)) bool_set (two_moves_constant A h a)
      (two_element_mere_point A h) x

{` Elimination of a mere point of a two-element type into propositions. `}
def two_element_point_elim (A : Type) (h : TwoElement A) (P : Type) (hp : isProp P) (f : A → P) : P
  ≔ mere_rec A P hp f (two_element_mere_point A h)

def two_moves_homotopy (A : Type) (h : TwoElement A) (a b : Equiv A A) (hab : (x : A) → Id A (a .map x) (b .map x))
  : Id Bool (two_moves A h a) (two_moves A h b)
  ≔ two_element_point_elim A h (Id Bool (two_moves A h a) (two_moves A h b)) (bool_set (two_moves A h a) (two_moves A h b))
      (x ↦ calc two_moves A h a = two_differ A h x (a .map x) by two_moves_value A h a x
        = two_differ A h x (b .map x) by refl (two_differ A h x) (hab x)
        = two_moves A h b by inverse Bool (two_moves A h b) (two_differ A h x (b .map x)) (two_moves_value A h b x) ∎)

{` Composition: moves(b ∘ a) = moves(a) xor moves(b). `}
def two_moves_compose (A : Type) (h : TwoElement A) (a b : Equiv A A)
  : Id Bool (two_moves A h (compose_equiv A A A a b)) (bool_xor (two_moves A h a) (two_moves A h b))
  ≔ let P ≔ Id Bool (two_moves A h (compose_equiv A A A a b)) (bool_xor (two_moves A h a) (two_moves A h b)) in
    two_element_point_elim A h P (bool_set (two_moves A h (compose_equiv A A A a b)) (bool_xor (two_moves A h a) (two_moves A h b)))
      (x ↦ calc two_moves A h (compose_equiv A A A a b) = two_differ A h x (b .map (a .map x))
          by two_moves_value A h (compose_equiv A A A a b) x
        = bool_xor (two_differ A h x (a .map x)) (two_differ A h (a .map x) (b .map (a .map x)))
          by two_differ_cocycle A h x (a .map x) (b .map (a .map x))
        = bool_xor (two_moves A h a) (two_moves A h b)
          by bool_xor_path (two_differ A h x (a .map x)) (two_moves A h a)
            (two_differ A h (a .map x) (b .map (a .map x))) (two_moves A h b)
            (inverse Bool (two_moves A h a) (two_differ A h x (a .map x)) (two_moves_value A h a x))
            (inverse Bool (two_moves A h b) (two_differ A h (a .map x) (b .map (a .map x))) (two_moves_value A h b (a .map x))) ∎)

def two_moves_identity (A : Type) (h : TwoElement A) : Id Bool (two_moves A h (identity_equiv A)) false.
  ≔ two_element_point_elim A h (Id Bool (two_moves A h (identity_equiv A)) false.) (bool_set (two_moves A h (identity_equiv A)) false.)
      (x ↦ concat Bool (two_moves A h (identity_equiv A)) (two_differ A h x x) false.
        (two_moves_value A h (identity_equiv A) x) (two_differ_refl A h x))

{` Conjugation invariance, phrased with a commuting square e ∘ a = b ∘ e. `}
def two_moves_conjugate (A B : Type) (hA : TwoElement A) (hB : TwoElement B) (e : Equiv A B)
  (a : Equiv A A) (b : Equiv B B) (comm : (x : A) → Id B (b .map (e .map x)) (e .map (a .map x)))
  : Id Bool (two_moves B hB b) (two_moves A hA a)
  ≔ two_element_point_elim A hA (Id Bool (two_moves B hB b) (two_moves A hA a)) (bool_set (two_moves B hB b) (two_moves A hA a))
      (x ↦ calc two_moves B hB b = two_differ B hB (e .map x) (b .map (e .map x)) by two_moves_value B hB b (e .map x)
        = two_differ B hB (e .map x) (e .map (a .map x)) by refl (two_differ B hB (e .map x)) (comm x)
        = two_differ A hA x (a .map x) by two_differ_equiv A B hA hB e x (a .map x)
        = two_moves A hA a by inverse Bool (two_moves A hA a) (two_differ A hA x (a .map x)) (two_moves_value A hA a x) ∎)

{` An automorphism that moves nothing is the identity, one that moves is the swap to the other point. `}
def two_moves_false_fixed (A : Type) (h : TwoElement A) (a : Equiv A A) (q : Id Bool (two_moves A h a) false.) (x : A)
  : Id A (a .map x) x
  ≔ inverse A x (a .map x) (two_differ_false A h x (a .map x)
      (concat Bool (two_differ A h x (a .map x)) (two_moves A h a) false.
        (inverse Bool (two_moves A h a) (two_differ A h x (a .map x)) (two_moves_value A h a x)) q))

def two_moves_true_moved (A : Type) (h : TwoElement A) (a : Equiv A A) (q : Id Bool (two_moves A h a) true.) (x : A)
  : Not (Id A x (a .map x))
  ≔ two_differ_true A h x (a .map x)
      (concat Bool (two_differ A h x (a .map x)) (two_moves A h a) true.
        (inverse Bool (two_moves A h a) (two_differ A h x (a .map x)) (two_moves_value A h a x)) q)
