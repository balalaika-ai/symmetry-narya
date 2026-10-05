export "177-circle-flip"

def bool_to_nat (b : Bool) : Nat ≔ match b [ false. ↦ zero. | true. ↦ suc. zero. ]

def true_count (n : Nat) (f : Fin n → Bool) : Nat
  ≔ match n [
  | zero. ↦ zero.
  | suc. k ↦ add (true_count k (a ↦ f (inl. a))) (bool_to_nat (f (inr. star.))) ]

{` Binomial coefficients by Pascal's rule. `}
def binomial (n k : Nat) : Nat ≔ match n, k [
  | zero., zero. ↦ suc. zero.
  | zero., suc. k ↦ zero.
  | suc. n, zero. ↦ suc. zero.
  | suc. n, suc. k ↦ add (binomial n (suc. k)) (binomial n k) ]

def binomial_zero (n : Nat) : Id Nat (binomial n zero.) (suc. zero.)
  ≔ match n [ zero. ↦ refl (suc. zero. : Nat) | suc. n ↦ refl (suc. zero. : Nat) ]

def BoolSubsets (n k : Nat) : Type ≔ Σ (Fin n → Bool) (f ↦ Id Nat (true_count n f) k)

def BoolSubsetsSplit (n k : Nat) : Type
  ≔ Sum (BoolSubsets n k) (Σ (Fin n → Bool) (g ↦ Id Nat (suc. (true_count n g)) k))

def fin_extend (n : Nat) (g : Fin n → Bool) (b : Bool) : Fin (suc. n) → Bool
  ≔ [ inl. a ↦ g a | inr. _ ↦ b ]

def bool_subsets_split_at (n k : Nat) (g : Fin n → Bool) (b : Bool)
  (c : Id Nat (add (true_count n g) (bool_to_nat b)) k) : BoolSubsetsSplit n k
  ≔ match b [ false. ↦ inl. (g, c) | true. ↦ inr. (g, c) ]

def bool_subsets_split_to (n k : Nat) (s : BoolSubsets (suc. n) k) : BoolSubsetsSplit n k
  ≔ bool_subsets_split_at n k (a ↦ s .fst (inl. a)) (s .fst (inr. star.)) (s .snd)

def bool_subsets_split_from (n k : Nat) : BoolSubsetsSplit n k → BoolSubsets (suc. n) k
  ≔ [ inl. u ↦ (fin_extend n (u .fst) false., u .snd) | inr. u ↦ (fin_extend n (u .fst) true., u .snd) ]

def bool_subsets_split_at_fst (n k : Nat) (g : Fin n → Bool) (b : Bool)
  (c : Id Nat (add (true_count n g) (bool_to_nat b)) k)
  : Id (Fin (suc. n) → Bool) (bool_subsets_split_from n k (bool_subsets_split_at n k g b c) .fst) (fin_extend n g b)
  ≔ match b [ false. ↦ refl (fin_extend n g false.) | true. ↦ refl (fin_extend n g true.) ]

def fin_extend_eta (n : Nat) (f : Fin (suc. n) → Bool)
  : Id (Fin (suc. n) → Bool) (fin_extend n (a ↦ f (inl. a)) (f (inr. star.))) f
  ≔ funext (Fin (suc. n)) (_ ↦ Bool) (fin_extend n (a ↦ f (inl. a)) (f (inr. star.))) f
      [ inl. a ↦ refl (f (inl. a)) | inr. u ↦ match u [ star. ↦ refl (f (inr. star.)) ] ]

def bool_subsets_split_equiv (n k : Nat) : Equiv (BoolSubsets (suc. n) k) (BoolSubsetsSplit n k)
  ≔ quasi_inverse_equiv (BoolSubsets (suc. n) k) (BoolSubsetsSplit n k)
      (bool_subsets_split_to n k) (bool_subsets_split_from n k)
      (s ↦ subtype_equal (Fin (suc. n) → Bool) (f ↦ Id Nat (true_count (suc. n) f) k)
        (f ↦ nat_set (true_count (suc. n) f) k)
        (bool_subsets_split_from n k (bool_subsets_split_to n k s)) s
        (concat (Fin (suc. n) → Bool) (bool_subsets_split_from n k (bool_subsets_split_to n k s) .fst)
          (fin_extend n (a ↦ s .fst (inl. a)) (s .fst (inr. star.))) (s .fst)
          (bool_subsets_split_at_fst n k (a ↦ s .fst (inl. a)) (s .fst (inr. star.)) (s .snd))
          (fin_extend_eta n (s .fst))))
      [ inl. u ↦ refl (inl. u : BoolSubsetsSplit n k) | inr. u ↦ refl (inr. u : BoolSubsetsSplit n k) ]

def succ_count_equiv (n j : Nat)
  : Equiv (Σ (Fin n → Bool) (g ↦ Id Nat (suc. (true_count n g)) (suc. j))) (BoolSubsets n j)
  ≔ family_equiv (Fin n → Bool) (g ↦ Id Nat (suc. (true_count n g)) (suc. j))
      (g ↦ Id Nat (true_count n g) j) (g ↦ successor_paths_equiv (true_count n g) j)

def succ_count_zero_empty (n : Nat) (u : Σ (Fin n → Bool) (g ↦ Id Nat (suc. (true_count n g)) zero.)) : Empty
  ≔ nat_encode (suc. (true_count n (u .fst))) zero. (u .snd)

def empty_bool_function : Fin zero. → Bool ≔ x ↦ match x []

def bool_subsets_fin (n k : Nat) : Equiv (BoolSubsets n k) (Fin (binomial n k))
  ≔ match n, k [
  | zero., zero. ↦ quasi_inverse_equiv (BoolSubsets zero. zero.) (Fin (suc. zero.))
      (_ ↦ inr. star.) (_ ↦ (empty_bool_function, refl (zero. : Nat)))
      (s ↦ subtype_equal (Fin zero. → Bool) (f ↦ Id Nat (true_count zero. f) zero.)
        (f ↦ nat_set (true_count zero. f) zero.) (empty_bool_function, refl (zero. : Nat)) s
        (funext (Fin zero.) (_ ↦ Bool) empty_bool_function (s .fst) (x ↦ match x [])))
      [ inl. x ↦ match x [] | inr. u ↦ inr. (unit_prop star. u) ]
  | zero., suc. j ↦ quasi_inverse_equiv (BoolSubsets zero. (suc. j)) Empty
      (s ↦ nat_encode zero. (suc. j) (s .snd)) (x ↦ match x [])
      (s ↦ match nat_encode zero. (suc. j) (s .snd) []) (x ↦ match x [])
  | suc. m, zero. ↦ compose_equiv (BoolSubsets (suc. m) zero.) (BoolSubsetsSplit m zero.) (Fin (suc. zero.))
      (bool_subsets_split_equiv m zero.)
      (compose_equiv (BoolSubsetsSplit m zero.) (BoolSubsets m zero.) (Fin (suc. zero.))
        (quasi_inverse_equiv (BoolSubsetsSplit m zero.) (BoolSubsets m zero.)
          [ inl. u ↦ u | inr. u ↦ absurd (BoolSubsets m zero.) (succ_count_zero_empty m u) ]
          (u ↦ inl. u)
          [ inl. u ↦ refl (inl. u : BoolSubsetsSplit m zero.) | inr. u ↦ match succ_count_zero_empty m u [] ]
          (u ↦ refl u))
        (compose_equiv (BoolSubsets m zero.) (Fin (binomial m zero.)) (Fin (suc. zero.))
          (bool_subsets_fin m zero.)
          (id_to_equiv (Fin (binomial m zero.)) (Fin (suc. zero.)) (refl Fin (binomial_zero m)))))
  | suc. m, suc. j ↦ compose_equiv (BoolSubsets (suc. m) (suc. j)) (BoolSubsetsSplit m (suc. j))
      (Fin (binomial (suc. m) (suc. j)))
      (bool_subsets_split_equiv m (suc. j))
      (compose_equiv (BoolSubsetsSplit m (suc. j)) (Sum (Fin (binomial m (suc. j))) (Fin (binomial m j)))
        (Fin (binomial (suc. m) (suc. j)))
        (sum_equiv (BoolSubsets m (suc. j)) (Σ (Fin m → Bool) (g ↦ Id Nat (suc. (true_count m g)) (suc. j)))
          (Fin (binomial m (suc. j))) (Fin (binomial m j))
          (bool_subsets_fin m (suc. j))
          (compose_equiv (Σ (Fin m → Bool) (g ↦ Id Nat (suc. (true_count m g)) (suc. j))) (BoolSubsets m j)
            (Fin (binomial m j)) (succ_count_equiv m j) (bool_subsets_fin m j)))
        (fin_sum_equiv (binomial m (suc. j)) (binomial m j))) ]

{` k-element subsets: predicates whose carrier merely is Fin k. `}
def KSubsets (A : Type) (k : Nat) : Type
  ≔ Σ (Subtypes A) (P ↦ Mere (Id Type (SubtypeCarrier A P) (Fin k)))

def decidable_iff (X Y : Type) (d : Decidable X) (f : X → Y) (g : Y → X) : Decidable Y
  ≔ match d [ inl. x ↦ inl. (f x) | inr. n ↦ inr. (y ↦ n (g y)) ]

def decision_bool (X : Type) (d : Decidable X) : Bool ≔ match d [ inl. _ ↦ true. | inr. _ ↦ false. ]

def decision_bool_true (X : Type) (d : Decidable X) (x : X) : Id Bool (decision_bool X d) true.
  ≔ match d [ inl. _ ↦ refl (true. : Bool) | inr. n ↦ absurd (Id Bool false. true.) (n x) ]

def decision_bool_reflect (X : Type) (d : Decidable X) (e : Id Bool (decision_bool X d) true.) : X
  ≔ match d [ inl. x ↦ x | inr. _ ↦ absurd X (bool_encode false. true. e) ]

def decision_bool_value (b : Bool) (d : Decidable (Id Bool b true.))
  : Id Bool (decision_bool (Id Bool b true.) d) b
  ≔ match b [
  | true. ↦ decision_bool_true (Id Bool true. true.) d (refl (true. : Bool))
  | false. ↦ match d [
    | inl. e ↦ absurd (Id Bool true. false.) (bool_encode false. true. e)
    | inr. _ ↦ refl (false. : Bool) ] ]

{` Membership in a subset with a finite carrier of a set with decidable
   equality is decidable. `}
def subset_member_decidable (A : Type) (hA : isSet A) (dA : DecidableEquality A) (P : Subtypes A) (k : Nat)
  (h : Mere (Id Type (SubtypeCarrier A P) (Fin k))) (x : A) : Decidable (P x .fst)
  ≔ let S ≔ SubtypeCarrier A P in
    let hs : IsFinite S ≔ trunc_map native_truncation (Id Type S (Fin k)) (Σ Nat (n ↦ Id Type S (Fin n)))
      (q ↦ (k, q)) h in
    decidable_iff (Mere (Σ S (s ↦ Id A (s .fst) x))) (P x .fst)
      (finite_quantifiers S hs (s ↦ Id A (s .fst) x) (s ↦ hA (s .fst) x) (s ↦ dA (s .fst) x) .snd)
      (mere_rec (Σ S (s ↦ Id A (s .fst) x)) (P x .fst) (P x .snd)
        (u ↦ transport A (y ↦ P y .fst) (u .fst .fst) x (u .snd) (u .fst .snd)))
      (p ↦ mere (Σ S (s ↦ Id A (s .fst) x)) ((x, p), refl x))

def subset_characteristic (n k : Nat) (P : Subtypes (Fin n))
  (h : Mere (Id Type (SubtypeCarrier (Fin n) P) (Fin k))) : Fin n → Bool
  ≔ x ↦ decision_bool (P x .fst) (subset_member_decidable (Fin n) (fin_set n) (fin_decidable_equality n) P k h x)

def BoolCarrier (n : Nat) (f : Fin n → Bool) : Type ≔ Σ (Fin n) (x ↦ Id Bool (f x) true.)

def bool_true_fin (b : Bool) : Equiv (Id Bool b true.) (Fin (bool_to_nat b))
  ≔ match b [
  | false. ↦ quasi_inverse_equiv (Id Bool false. true.) Empty (e ↦ bool_encode false. true. e) (x ↦ match x [])
      (e ↦ match bool_encode false. true. e []) (x ↦ match x [])
  | true. ↦ quasi_inverse_equiv (Id Bool true. true.) (Fin (suc. zero.)) (_ ↦ inr. star.) (_ ↦ refl (true. : Bool))
      (e ↦ bool_set true. true. (refl (true. : Bool)) e)
      [ inl. x ↦ match x [] | inr. u ↦ inr. (unit_prop star. u) ] ]

def bool_carrier_fin (n : Nat) (f : Fin n → Bool) : Equiv (BoolCarrier n f) (Fin (true_count n f))
  ≔ match n [
  | zero. ↦ quasi_inverse_equiv (BoolCarrier zero. f) Empty (u ↦ match u .fst []) (x ↦ match x [])
      (u ↦ match u .fst []) (x ↦ match x [])
  | suc. m ↦ compose_equiv (BoolCarrier (suc. m) f)
      (Sum (BoolCarrier m (a ↦ f (inl. a))) (Id Bool (f (inr. star.)) true.))
      (Fin (true_count (suc. m) f))
      (sigma_fin_succ_equiv m (x ↦ Id Bool (f x) true.))
      (compose_equiv (Sum (BoolCarrier m (a ↦ f (inl. a))) (Id Bool (f (inr. star.)) true.))
        (Sum (Fin (true_count m (a ↦ f (inl. a)))) (Fin (bool_to_nat (f (inr. star.)))))
        (Fin (true_count (suc. m) f))
        (sum_equiv (BoolCarrier m (a ↦ f (inl. a))) (Id Bool (f (inr. star.)) true.)
          (Fin (true_count m (a ↦ f (inl. a)))) (Fin (bool_to_nat (f (inr. star.))))
          (bool_carrier_fin m (a ↦ f (inl. a))) (bool_true_fin (f (inr. star.))))
        (fin_sum_equiv (true_count m (a ↦ f (inl. a))) (bool_to_nat (f (inr. star.))))) ]

def subset_characteristic_carrier (n k : Nat) (P : Subtypes (Fin n))
  (h : Mere (Id Type (SubtypeCarrier (Fin n) P) (Fin k)))
  : Equiv (SubtypeCarrier (Fin n) P) (BoolCarrier n (subset_characteristic n k P h))
  ≔ family_equiv (Fin n) (x ↦ P x .fst) (x ↦ Id Bool (subset_characteristic n k P h x) true.)
      (x ↦ let d ≔ subset_member_decidable (Fin n) (fin_set n) (fin_decidable_equality n) P k h x in
        iff_equiv (P x .fst) (Id Bool (decision_bool (P x .fst) d) true.) (P x .snd)
          (bool_set (decision_bool (P x .fst) d) true.)
          (decision_bool_true (P x .fst) d) (decision_bool_reflect (P x .fst) d))

def subsets_to_bool (n k : Nat) (u : KSubsets (Fin n) k) : BoolSubsets n k
  ≔ let f ≔ subset_characteristic n k (u .fst) (u .snd) in
    (f, mere_rec (Id Type (SubtypeCarrier (Fin n) (u .fst)) (Fin k)) (Id Nat (true_count n f) k)
      (nat_set (true_count n f) k)
      (q ↦ fin_equiv_cardinality (true_count n f) k
        (compose_equiv (Fin (true_count n f)) (SubtypeCarrier (Fin n) (u .fst)) (Fin k)
          (compose_equiv (Fin (true_count n f)) (BoolCarrier n f) (SubtypeCarrier (Fin n) (u .fst))
            (canonical_inverse_equiv (BoolCarrier n f) (Fin (true_count n f)) (bool_carrier_fin n f))
            (canonical_inverse_equiv (SubtypeCarrier (Fin n) (u .fst)) (BoolCarrier n f)
              (subset_characteristic_carrier n k (u .fst) (u .snd))))
          (id_to_equiv (SubtypeCarrier (Fin n) (u .fst)) (Fin k) q)))
      (u .snd))

def bool_predicate (n : Nat) (f : Fin n → Bool) : Subtypes (Fin n)
  ≔ x ↦ (Id Bool (f x) true., bool_set (f x) true.)

def bool_to_subsets (n k : Nat) (s : BoolSubsets n k) : KSubsets (Fin n) k
  ≔ (bool_predicate n (s .fst),
      mere (Id Type (BoolCarrier n (s .fst)) (Fin k))
        (ua (BoolCarrier n (s .fst)) (Fin k)
          (compose_equiv (BoolCarrier n (s .fst)) (Fin (true_count n (s .fst))) (Fin k)
            (bool_carrier_fin n (s .fst))
            (id_to_equiv (Fin (true_count n (s .fst))) (Fin k) (refl Fin (s .snd))))))

def ksubsets_bool_equiv (n k : Nat) : Equiv (KSubsets (Fin n) k) (BoolSubsets n k)
  ≔ quasi_inverse_equiv (KSubsets (Fin n) k) (BoolSubsets n k) (subsets_to_bool n k) (bool_to_subsets n k)
      (u ↦ subtype_equal (Subtypes (Fin n)) (P ↦ Mere (Id Type (SubtypeCarrier (Fin n) P) (Fin k)))
        (P ↦ mere_isprop (Id Type (SubtypeCarrier (Fin n) P) (Fin k)))
        (bool_to_subsets n k (subsets_to_bool n k u)) u
        (funext (Fin n) (_ ↦ PropTypes) (bool_predicate n (subset_characteristic n k (u .fst) (u .snd))) (u .fst)
          (x ↦ let d ≔ subset_member_decidable (Fin n) (fin_set n) (fin_decidable_equality n) (u .fst) k (u .snd) x in
            proposition_extensionality (bool_predicate n (subset_characteristic n k (u .fst) (u .snd)) x) (u .fst x)
              (decision_bool_reflect (u .fst x .fst) d) (decision_bool_true (u .fst x .fst) d))))
      (s ↦ subtype_equal (Fin n → Bool) (f ↦ Id Nat (true_count n f) k) (f ↦ nat_set (true_count n f) k)
        (subsets_to_bool n k (bool_to_subsets n k s)) s
        (funext (Fin n) (_ ↦ Bool) (subsets_to_bool n k (bool_to_subsets n k s) .fst) (s .fst)
          (x ↦ decision_bool_value (s .fst x)
            (subset_member_decidable (Fin n) (fin_set n) (fin_decidable_equality n)
              (bool_predicate n (s .fst)) k (bool_to_subsets n k s .snd) x))))

def ksubsets_fin_equiv (n k : Nat) : Equiv (KSubsets (Fin n) k) (Fin (binomial n k))
  ≔ compose_equiv (KSubsets (Fin n) k) (BoolSubsets n k) (Fin (binomial n k))
      (ksubsets_bool_equiv n k) (bool_subsets_fin n k)

def ksubsets_finite (A : Type) (ha : IsFinite A) (k : Nat) : IsFinite (KSubsets A k)
  ≔ mere_rec (Σ Nat (n ↦ Id Type A (Fin n))) (IsFinite (KSubsets A k)) (isfinite_prop (KSubsets A k))
      (p ↦ mere (Σ Nat (m ↦ Id Type (KSubsets A k) (Fin m))) (binomial (p .fst) k,
        concat Type (KSubsets A k) (KSubsets (Fin (p .fst)) k) (Fin (binomial (p .fst) k))
          (refl ((X ↦ KSubsets X k) : Type → Type) (p .snd))
          (ua (KSubsets (Fin (p .fst)) k) (Fin (binomial (p .fst) k)) (ksubsets_fin_equiv (p .fst) k))))
      ha

{` First part of the unlabeled exercise after xca:factorial: a finite set of
   cardinality n has binomial(n,k) subsets with k elements. `}
def ksubsets_cardinality (A : Type) (ha : IsFinite A) (k : Nat) (h : IsFinite (KSubsets A k))
  : Id Nat (cardinality (KSubsets A k) h) (binomial (cardinality A ha) k)
  ≔ let n ≔ cardinality A ha in
    mere_rec (Id Type A (Fin n)) (Id Nat (cardinality (KSubsets A k) h) (binomial n k))
      (nat_set (cardinality (KSubsets A k) h) (binomial n k))
      (p ↦ cardinality_from_path (KSubsets A k) h (binomial n k)
        (concat Type (KSubsets A k) (KSubsets (Fin n) k) (Fin (binomial n k))
          (refl ((X ↦ KSubsets X k) : Type → Type) p)
          (ua (KSubsets (Fin n) k) (Fin (binomial n k)) (ksubsets_fin_equiv n k))))
      (cardinality_spec A ha)

{` The coefficient is the book's n!/(k!(n-k)!): binomial(n,k) k! (n-k)! = n!. `}
def mul_one_left (x : Nat) : Id Nat (mul (suc. zero.) x) x
  ≔ concat Nat (mul (suc. zero.) x) (add (mul zero. x) x) x (mul_suc_left zero. x)
      (concat Nat (add (mul zero. x) x) (add zero. x) x
        (refl ((y ↦ add y x) : Nat → Nat) (mul_zero_left x)) (add_zero_left x))

def mul_one_right (x : Nat) : Id Nat (mul x (suc. zero.)) x ≔ add_zero_left x

def binomial_vanish (n k : Nat) (h : Lt n k) : Id Nat (binomial n k) zero.
  ≔ match n, k [
  | zero., zero. ↦ match h []
  | zero., suc. k ↦ refl (zero. : Nat)
  | suc. n, zero. ↦ match h []
  | suc. n, suc. k ↦ calc
      add (binomial n (suc. k)) (binomial n k) = add zero. (binomial n k)
        by refl ((y ↦ add y (binomial n k)) : Nat → Nat) (binomial_vanish n (suc. k) (lt_le n k h))
      = add zero. zero. by refl (add zero.) (binomial_vanish n k h)
      = (zero. : Nat) by refl (zero. : Nat) ∎ ]

def binomial_self (n : Nat) : Id Nat (binomial n n) (suc. zero.)
  ≔ match n [
  | zero. ↦ refl (suc. zero. : Nat)
  | suc. m ↦ calc
      add (binomial m (suc. m)) (binomial m m) = add zero. (binomial m m)
        by refl ((y ↦ add y (binomial m m)) : Nat → Nat) (binomial_vanish m (suc. m) (le_refl m))
      = add zero. (suc. zero.) by refl (add zero.) (binomial_self m)
      = (suc. zero. : Nat) by refl (suc. zero. : Nat) ∎ ]

def binomial_factorial_zero (n j : Nat) (h : Id Nat j n)
  : Id Nat (mul (binomial n zero.) (mul (factorial zero.) (factorial j))) (factorial n)
  ≔ calc
      mul (binomial n zero.) (mul (factorial zero.) (factorial j))
      = mul (suc. zero.) (mul (suc. zero.) (factorial j))
        by refl ((y ↦ mul y (mul (suc. zero.) (factorial j))) : Nat → Nat) (binomial_zero n)
      = mul (suc. zero.) (factorial j) by mul_one_left (mul (suc. zero.) (factorial j))
      = factorial j by mul_one_left (factorial j)
      = factorial n by refl factorial h ∎

def binomial_factorial_diagonal (k : Nat)
  : Id Nat (mul (binomial (suc. k) (suc. k)) (mul (factorial (suc. k)) (factorial zero.))) (factorial (suc. k))
  ≔ calc
      mul (binomial (suc. k) (suc. k)) (mul (factorial (suc. k)) (factorial zero.))
      = mul (suc. zero.) (mul (factorial (suc. k)) (suc. zero.))
        by refl ((y ↦ mul y (mul (factorial (suc. k)) (suc. zero.))) : Nat → Nat) (binomial_self (suc. k))
      = mul (factorial (suc. k)) (suc. zero.) by mul_one_left (mul (factorial (suc. k)) (suc. zero.))
      = factorial (suc. k) by mul_one_right (factorial (suc. k)) ∎

def mul_regroup_right (B a K b J : Nat)
  : Id Nat (mul B (mul (mul a K) (mul b J))) (mul (mul B (mul (mul a K) J)) b)
  ≔ calc
      mul B (mul (mul a K) (mul b J)) = mul B (mul (mul a K) (mul J b))
        by refl ((y ↦ mul B (mul (mul a K) y)) : Nat → Nat) (mul_comm b J)
      = mul B (mul (mul (mul a K) J) b)
        by refl (mul B) (inverse Nat (mul (mul (mul a K) J) b) (mul (mul a K) (mul J b)) (mul_assoc (mul a K) J b))
      = mul (mul B (mul (mul a K) J)) b
        by inverse Nat (mul (mul B (mul (mul a K) J)) b) (mul B (mul (mul (mul a K) J) b)) (mul_assoc B (mul (mul a K) J) b) ∎

def mul_regroup_left (B a K Z : Nat)
  : Id Nat (mul B (mul (mul a K) Z)) (mul (mul B (mul K Z)) a)
  ≔ calc
      mul B (mul (mul a K) Z) = mul B (mul a (mul K Z)) by refl (mul B) (mul_assoc a K Z)
      = mul B (mul (mul K Z) a) by refl (mul B) (mul_comm a (mul K Z))
      = mul (mul B (mul K Z)) a
        by inverse Nat (mul (mul B (mul K Z)) a) (mul B (mul (mul K Z) a)) (mul_assoc B (mul K Z) a) ∎

{` Recursion is structural in n. `}
def binomial_factorial (n k j : Nat) (h : Id Nat (add j k) n)
  : Id Nat (mul (binomial n k) (mul (factorial k) (factorial j))) (factorial n)
  ≔ match k [
  | zero. ↦ binomial_factorial_zero n j h
  | suc. k ↦ match n [
    | zero. ↦ absurd (Id Nat (mul (binomial zero. (suc. k)) (mul (factorial (suc. k)) (factorial j))) (factorial zero.))
        (nat_encode (suc. (add j k)) zero. h)
    | suc. m ↦ match j [
      | zero. ↦ transport Nat
          (x ↦ Id Nat (mul (binomial x (suc. k)) (mul (factorial (suc. k)) (factorial zero.))) (factorial x))
          (suc. k) (suc. m)
          (concat Nat (suc. k) (suc. (add zero. k)) (suc. m)
            (inverse Nat (suc. (add zero. k)) (suc. k) (suc. (add_zero_left k))) h)
          (binomial_factorial_diagonal k)
      | suc. j ↦
          let hm : Id Nat (add (suc. j) k) m ≔ nat_decode (add (suc. j) k) m (nat_encode (suc. (add (suc. j) k)) (suc. m) h) in
          let h1 : Id Nat (add j (suc. k)) m
            ≔ concat Nat (suc. (add j k)) (add (suc. j) k) m (inverse Nat (add (suc. j) k) (suc. (add j k)) (add_suc_left j k)) hm in
          let B1 ≔ binomial m (suc. k) in
          let B2 ≔ binomial m k in
          let K ≔ factorial k in
          let J ≔ factorial j in
          let X ≔ mul (mul (suc. k) K) (mul (suc. j) J) in
          calc
            mul (add B1 B2) X = add (mul B1 X) (mul B2 X) by mul_add_right B1 B2 X
            = add (mul (mul B1 (mul (mul (suc. k) K) J)) (suc. j)) (mul B2 X)
              by refl ((y ↦ add y (mul B2 X)) : Nat → Nat) (mul_regroup_right B1 (suc. k) K (suc. j) J)
            = add (mul (factorial m) (suc. j)) (mul B2 X)
              by refl ((y ↦ add (mul y (suc. j)) (mul B2 X)) : Nat → Nat) (binomial_factorial m (suc. k) j h1)
            = add (mul (factorial m) (suc. j)) (mul (mul B2 (mul K (mul (suc. j) J))) (suc. k))
              by refl (add (mul (factorial m) (suc. j))) (mul_regroup_left B2 (suc. k) K (mul (suc. j) J))
            = add (mul (factorial m) (suc. j)) (mul (factorial m) (suc. k))
              by refl ((y ↦ add (mul (factorial m) (suc. j)) (mul y (suc. k))) : Nat → Nat)
                (binomial_factorial m k (suc. j) hm)
            = mul (factorial m) (add (suc. j) (suc. k))
              by inverse Nat (mul (factorial m) (add (suc. j) (suc. k)))
                (add (mul (factorial m) (suc. j)) (mul (factorial m) (suc. k))) (mul_add_left (factorial m) (suc. j) (suc. k))
            = mul (factorial m) (suc. m) by refl (mul (factorial m)) h
            = mul (suc. m) (factorial m) by mul_comm (factorial m) (suc. m) ∎ ] ] ]

def binomial_factorial_formula (n k : Nat) (le : BookLe k n)
  : Id Nat (mul (binomial n k) (mul (factorial k) (factorial (le .fst)))) (factorial n)
  ≔ binomial_factorial n k (le .fst) (le .snd)
