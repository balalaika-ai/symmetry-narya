export "175-permutation-factorial"
export "178-binomial-subsets"
export "412-symmetric-group-two"
export "1010-usym-powers"

{` Chapter 10: counting the permutations of Fin n with a
   decidable property by enumeration.

   PermCode n = Fin n × Fin (n-1) × … × Fin 1 codes the permutations of
   Fin n: iterating eq:type-factorial (permutation_option_equiv, module 175),
   perm_code_equiv : PermCode n ≃ Aut(Fin n). For a Bool-valued property β of
   functions Fin n → Fin n, the symmetries g of Σ_n with β(g) = true form a
   type equivalent to Fin (perm_code_count n β) (sym_bool_count_equiv), and
   perm_code_count is a closed structural recursion over the codes, so for
   concrete n and β it computes to a numeral (n! evaluations of β).

   Application: the symmetries g of Σ_n with g³ = e
   (sym_order_three_equiv), numbered 1, 1, 1, 3, 9, 21, 81 for n = 0, …, 6
   (the counts are checked by refl at the end). `}

{` Codes of permutations. `}
def PermCode (n : Nat) : Type
  ≔ match n [ zero. ↦ Fin (suc. zero.) | suc. k ↦ Product (Fin (suc. k)) (PermCode k) ]

def perm_code_decode (n : Nat) (c : PermCode n) : Equiv (Fin n) (Fin n)
  ≔ match n [
  | zero. ↦ identity_equiv (Fin zero.)
  | suc. k ↦ permutation_option_from (Fin k) (fin_decidable_equality k) (c .fst, perm_code_decode k (c .snd)) ]

def perm_code_encode (n : Nat) (e : Equiv (Fin n) (Fin n)) : PermCode n
  ≔ match n [
  | zero. ↦ inr. star.
  | suc. k ↦ let u ≔ permutation_option_to (Fin k) (fin_decidable_equality k) e in
      (u .fst, perm_code_encode k (u .snd)) ]

def perm_code_decode_encode (n : Nat) (e : Equiv (Fin n) (Fin n))
  : Id (Equiv (Fin n) (Fin n)) (perm_code_decode n (perm_code_encode n e)) e
  ≔ match n [
  | zero. ↦ equiv_homotopy (Fin zero.) (Fin zero.) (identity_equiv (Fin zero.)) e (x ↦ match x [])
  | suc. k ↦
      let d ≔ fin_decidable_equality k in
      let u ≔ permutation_option_to (Fin k) d e in
      let F : Equiv (Fin k) (Fin k) → Equiv (Fin (suc. k)) (Fin (suc. k))
        ≔ r ↦ permutation_option_from (Fin k) d (u .fst, r) in
      concat (Equiv (Fin (suc. k)) (Fin (suc. k)))
        (F (perm_code_decode k (perm_code_encode k (u .snd)))) (F (u .snd)) e
        (refl F (perm_code_decode_encode k (u .snd)))
        (permutation_option_eta (Fin k) d e) ]

def perm_code_encode_decode (n : Nat) (c : PermCode n)
  : Id (PermCode n) (perm_code_encode n (perm_code_decode n c)) c
  ≔ match n [
  | zero. ↦ match c [
    | inl. x ↦ match x []
    | inr. u ↦ inr. (unit_prop star. u) ]
  | suc. k ↦
      let d ≔ fin_decidable_equality k in
      let D ≔ perm_code_decode k (c .snd) in
      let g : Product (Fin (suc. k)) (Equiv (Fin k) (Fin k)) → PermCode (suc. k)
        ≔ u ↦ (u .fst, perm_code_encode k (u .snd)) in
      concat (PermCode (suc. k))
        (g (permutation_option_to (Fin k) d (permutation_option_from (Fin k) d (c .fst, D))))
        (g (c .fst, D)) c
        (refl g (permutation_option_epsilon (Fin k) d (c .fst, D)))
        (refl (c .fst), perm_code_encode_decode k (c .snd)) ]

def perm_code_equiv (n : Nat) : Equiv (PermCode n) (Equiv (Fin n) (Fin n))
  ≔ quasi_inverse_equiv (PermCode n) (Equiv (Fin n) (Fin n)) (perm_code_decode n) (perm_code_encode n)
      (perm_code_encode_decode n) (perm_code_decode_encode n)

{` Counting codes with a Bool-valued property. `}
def pcode_sum (n : Nat) (f : Fin n → Nat) : Nat
  ≔ match n [ zero. ↦ zero. | suc. k ↦ add (pcode_sum k (i ↦ f (inl. i))) (f (inr. star.)) ]

def perm_code_count (n : Nat) (b : PermCode n → Bool) : Nat
  ≔ match n [
  | zero. ↦ pcode_sum (suc. zero.) (i ↦ bool_to_nat (b i))
  | suc. k ↦ pcode_sum (suc. k) (i ↦ perm_code_count k (c ↦ b (i, c))) ]

def pcode_sigma_fin (n : Nat) (f : Fin n → Nat) : Equiv (Σ (Fin n) (i ↦ Fin (f i))) (Fin (pcode_sum n f))
  ≔ match n [
  | zero. ↦ quasi_inverse_equiv (Σ (Fin zero.) (i ↦ Fin (f i))) Empty (u ↦ match u .fst []) (x ↦ match x [])
      (u ↦ match u .fst []) (x ↦ match x [])
  | suc. k ↦
      let A ≔ Σ (Fin k) (j ↦ Fin (f (inl. j))) in
      let B ≔ Fin (f (inr. star.)) in
      compose_equiv (Σ (Fin (suc. k)) (i ↦ Fin (f i))) (Sum A B) (Fin (pcode_sum (suc. k) f))
        (sigma_fin_succ_equiv k (i ↦ Fin (f i)))
        (compose_equiv (Sum A B) (Sum (Fin (pcode_sum k (j ↦ f (inl. j)))) B) (Fin (pcode_sum (suc. k) f))
          (sum_equiv A B (Fin (pcode_sum k (j ↦ f (inl. j)))) B (pcode_sigma_fin k (j ↦ f (inl. j))) (identity_equiv B))
          (fin_sum_equiv (pcode_sum k (j ↦ f (inl. j))) (f (inr. star.)))) ]

def PermCodeCarrier (n : Nat) (b : PermCode n → Bool) : Type ≔ Σ (PermCode n) (c ↦ Id Bool (b c) true.)

def perm_code_carrier_fin (n : Nat) (b : PermCode n → Bool) : Equiv (PermCodeCarrier n b) (Fin (perm_code_count n b))
  ≔ match n [
  | zero. ↦ compose_equiv (PermCodeCarrier zero. b) (Σ (Fin (suc. zero.)) (i ↦ Fin (bool_to_nat (b i))))
      (Fin (perm_code_count zero. b))
      (family_equiv (Fin (suc. zero.)) (c ↦ Id Bool (b c) true.) (i ↦ Fin (bool_to_nat (b i))) (i ↦ bool_true_fin (b i)))
      (pcode_sigma_fin (suc. zero.) (i ↦ bool_to_nat (b i)))
  | suc. k ↦
      let P : Fin (suc. k) → Type ≔ i ↦ PermCodeCarrier k (c ↦ b (i, c)) in
      let N : Fin (suc. k) → Nat ≔ i ↦ perm_code_count k (c ↦ b (i, c)) in
      compose_equiv (PermCodeCarrier (suc. k) b) (Σ (Fin (suc. k)) P) (Fin (perm_code_count (suc. k) b))
        (sigma_assoc (Fin (suc. k)) (_ ↦ PermCode k) (i c ↦ Id Bool (b (i, c)) true.))
        (compose_equiv (Σ (Fin (suc. k)) P) (Σ (Fin (suc. k)) (i ↦ Fin (N i))) (Fin (perm_code_count (suc. k) b))
          (family_equiv (Fin (suc. k)) P (i ↦ Fin (N i)) (i ↦ perm_code_carrier_fin k (c ↦ b (i, c))))
          (pcode_sigma_fin (suc. k) N)) ]

{` The symmetries of Σ_n whose action satisfies β, counted by codes. `}
def SymBoolCarrier (n : Nat) (β : (Fin n → Fin n) → Bool) : Type
  ≔ Σ (USym (symmetric_group n)) (g ↦ Id Bool (β (permutation_action (standard_set n) g)) true.)

def sym_bool_code_predicate (n : Nat) (β : (Fin n → Fin n) → Bool) : PermCode n → Bool
  ≔ c ↦ β (perm_code_decode n c .map)

def sym_bool_count_equiv (n : Nat) (β : (Fin n → Fin n) → Bool)
  : Equiv (SymBoolCarrier n β) (Fin (perm_code_count n (sym_bool_code_predicate n β)))
  ≔ let E ≔ Equiv (Fin n) (Fin n) in
    let C : E → Type ≔ e ↦ Id Bool (β (e .map)) true. in
    let b ≔ sym_bool_code_predicate n β in
    compose_equiv (SymBoolCarrier n β) (Σ E C) (Fin (perm_code_count n b))
      (sigma_reindex_equiv (USym (symmetric_group n)) E (permutation_action_equiv (standard_set n)) C)
      (compose_equiv (Σ E C) (PermCodeCarrier n b) (Fin (perm_code_count n b))
        (canonical_inverse_equiv (PermCodeCarrier n b) (Σ E C) (sigma_reindex_equiv (PermCode n) E (perm_code_equiv n) C))
        (perm_code_carrier_fin n b))

{` The same with a known count k. Downstream modules should use this form:
   types mentioning Fin (perm_code_count n …) for concrete n are evaluated,
   i.e. the enumeration is rerun, at every use. `}
def sym_bool_count_fin (n : Nat) (β : (Fin n → Fin n) → Bool) (k : Nat)
  (c : Id Nat (perm_code_count n (sym_bool_code_predicate n β)) k)
  : Equiv (SymBoolCarrier n β) (Fin k)
  ≔ compose_equiv (SymBoolCarrier n β) (Fin (perm_code_count n (sym_bool_code_predicate n β))) (Fin k)
      (sym_bool_count_equiv n β)
      (id_to_equiv (Fin (perm_code_count n (sym_bool_code_predicate n β))) (Fin k) (refl Fin c))

{` Bool tests on Fin n. `}
def pcode_and (a b : Bool) : Bool ≔ match a [ false. ↦ false. | true. ↦ b ]

def pcode_and_true_to (a b : Bool) (q : Id Bool (pcode_and a b) true.) : Product (Id Bool a true.) (Id Bool b true.)
  ≔ match a [
  | false. ↦ match bool_encode false. true. q []
  | true. ↦ (refl (true. : Bool), q) ]

def pcode_and_true_from (a b : Bool) (pq : Product (Id Bool a true.) (Id Bool b true.)) : Id Bool (pcode_and a b) true.
  ≔ match a [ false. ↦ pq .fst | true. ↦ pq .snd ]

def pcode_fin_all (n : Nat) (p : Fin n → Bool) : Bool
  ≔ match n [ zero. ↦ true. | suc. k ↦ pcode_and (pcode_fin_all k (i ↦ p (inl. i))) (p (inr. star.)) ]

def pcode_fin_all_elim (n : Nat) (p : Fin n → Bool) (h : Id Bool (pcode_fin_all n p) true.) (x : Fin n)
  : Id Bool (p x) true.
  ≔ match n [
  | zero. ↦ match x []
  | suc. k ↦ match x [
    | inl. i ↦ pcode_fin_all_elim k (j ↦ p (inl. j))
        (pcode_and_true_to (pcode_fin_all k (j ↦ p (inl. j))) (p (inr. star.)) h .fst) i
    | inr. u ↦ match u [
      | star. ↦ pcode_and_true_to (pcode_fin_all k (j ↦ p (inl. j))) (p (inr. star.)) h .snd ] ] ]

def pcode_fin_all_intro (n : Nat) (p : Fin n → Bool) (h : (x : Fin n) → Id Bool (p x) true.)
  : Id Bool (pcode_fin_all n p) true.
  ≔ match n [
  | zero. ↦ refl (true. : Bool)
  | suc. k ↦ pcode_and_true_from (pcode_fin_all k (i ↦ p (inl. i))) (p (inr. star.))
      (pcode_fin_all_intro k (i ↦ p (inl. i)) (i ↦ h (inl. i)), h (inr. star.)) ]

def pcode_eqb (n : Nat) (x y : Fin n) : Bool ≔ decision_bool (Id (Fin n) x y) (fin_decidable_equality n x y)

{` "f and g agree everywhere" as a Bool. `}
def pcode_agree (n : Nat) (f g : Fin n → Fin n) : Bool ≔ pcode_fin_all n (x ↦ pcode_eqb n (f x) (g x))

def pcode_agree_elim (n : Nat) (f g : Fin n → Fin n) (h : Id Bool (pcode_agree n f g) true.) (x : Fin n)
  : Id (Fin n) (f x) (g x)
  ≔ decision_bool_reflect (Id (Fin n) (f x) (g x)) (fin_decidable_equality n (f x) (g x))
      (pcode_fin_all_elim n (y ↦ pcode_eqb n (f y) (g y)) h x)

def pcode_agree_intro (n : Nat) (f g : Fin n → Fin n) (h : (x : Fin n) → Id (Fin n) (f x) (g x))
  : Id Bool (pcode_agree n f g) true.
  ≔ pcode_fin_all_intro n (y ↦ pcode_eqb n (f y) (g y))
      (x ↦ decision_bool_true (Id (Fin n) (f x) (g x)) (fin_decidable_equality n (f x) (g x)) (h x))

{` The action of a power of a symmetry is the iterated action. `}
def perm_power_action (S : SetTypes) (g : USym (permutation_group S)) (k : Nat) (x : S .fst)
  : Id (S .fst) (permutation_action S (usym_power (permutation_group S) g k) x) (iterate (S .fst) (permutation_action S g) k x)
  ≔ let P ≔ permutation_group S in
    match k [
    | zero. ↦ permutation_action_unit S x
    | suc. k ↦ concat (S .fst) (permutation_action S (usym_mul P g (usym_power P g k)) x)
        (permutation_action S g (permutation_action S (usym_power P g k) x))
        (iterate (S .fst) (permutation_action S g) (suc. k) x)
        (permutation_action_mul S g (usym_power P g k) x)
        (refl (permutation_action S g) (perm_power_action S g k x)) ]

{` g^k = e in Σ_n iff the k-th iterate of the action of g is the identity. `}
def pcode_power_unit_test (n k : Nat) : (Fin n → Fin n) → Bool ≔ f ↦ pcode_agree n (iterate (Fin n) f k) (x ↦ x)

def sym_power_unit_iff (n k : Nat) (g : USym (symmetric_group n))
  : Equiv (Id (USym (symmetric_group n)) (usym_power (symmetric_group n) g k) (usym_unit (symmetric_group n)))
          (Id Bool (pcode_power_unit_test n k (permutation_action (standard_set n) g)) true.)
  ≔ let S ≔ standard_set n in let G ≔ symmetric_group n in
    let a ≔ permutation_action S g in
    iff_equiv (Id (USym G) (usym_power G g k) (usym_unit G)) (Id Bool (pcode_power_unit_test n k a) true.)
      (usym_set G (usym_power G g k) (usym_unit G)) (bool_set (pcode_power_unit_test n k a) true.)
      (q ↦ pcode_agree_intro n (iterate (Fin n) a k) (x ↦ x)
        (x ↦ concat (Fin n) (iterate (Fin n) a k x) (permutation_action S (usym_power G g k) x) x
          (inverse (Fin n) (permutation_action S (usym_power G g k) x) (iterate (Fin n) a k x) (perm_power_action S g k x))
          (concat (Fin n) (permutation_action S (usym_power G g k) x) (permutation_action S (usym_unit G) x) x
            (refl ((h ↦ permutation_action S h x) : USym G → Fin n) q)
            (permutation_action_unit S x))))
      (h ↦ permutation_symmetries_ext S (usym_power G g k) (usym_unit G)
        (x ↦ concat (Fin n) (permutation_action S (usym_power G g k) x) x (permutation_action S (usym_unit G) x)
          (concat (Fin n) (permutation_action S (usym_power G g k) x) (iterate (Fin n) a k x) x
            (perm_power_action S g k x) (pcode_agree_elim n (iterate (Fin n) a k) (x ↦ x) h x))
          (inverse (Fin n) (permutation_action S (usym_unit G) x) x (permutation_action_unit S x))))

{` The symmetries g of Σ_n with g^k = e, counted by codes. `}
def sym_power_unit_count_equiv (n k : Nat)
  : Equiv (Σ (USym (symmetric_group n)) (g ↦ Id (USym (symmetric_group n)) (usym_power (symmetric_group n) g k)
                                                (usym_unit (symmetric_group n))))
          (Fin (perm_code_count n (sym_bool_code_predicate n (pcode_power_unit_test n k))))
  ≔ compose_equiv
      (Σ (USym (symmetric_group n)) (g ↦ Id (USym (symmetric_group n)) (usym_power (symmetric_group n) g k)
                                            (usym_unit (symmetric_group n))))
      (SymBoolCarrier n (pcode_power_unit_test n k))
      (Fin (perm_code_count n (sym_bool_code_predicate n (pcode_power_unit_test n k))))
      (family_equiv (USym (symmetric_group n))
        (g ↦ Id (USym (symmetric_group n)) (usym_power (symmetric_group n) g k) (usym_unit (symmetric_group n)))
        (g ↦ Id Bool (pcode_power_unit_test n k (permutation_action (standard_set n) g)) true.)
        (sym_power_unit_iff n k))
      (sym_bool_count_equiv n (pcode_power_unit_test n k))

{` Litmus: Σ_3 has 6 symmetries, 3 of them with g³ = e; Σ_4 has 9 such. `}
def perm_code_count_all_three : Id Nat (perm_code_count 3 (_ ↦ true.)) 6 ≔ refl (6 : Nat)

def sym_order_three_count_three : Id Nat (perm_code_count 3 (sym_bool_code_predicate 3 (pcode_power_unit_test 3 3))) 3
  ≔ refl (3 : Nat)

def sym_order_three_count_four : Id Nat (perm_code_count 4 (sym_bool_code_predicate 4 (pcode_power_unit_test 4 3))) 9
  ≔ refl (9 : Nat)

{` Σ_5 has 21 and Σ_6 has 81 symmetries g with g³ = e (by cycle type:
   1 + 20 three-cycles, and 1 + 40 three-cycles + 40 products of two
   disjoint three-cycles). `}
def sym_order_three_count_five : Id Nat (perm_code_count 5 (sym_bool_code_predicate 5 (pcode_power_unit_test 5 3))) 21
  ≔ refl (21 : Nat)

def sym_order_three_count_six : Id Nat (perm_code_count 6 (sym_bool_code_predicate 6 (pcode_power_unit_test 6 3))) 81
  ≔ refl (81 : Nat)
