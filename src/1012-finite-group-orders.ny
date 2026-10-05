export "412-symmetric-group-two"
export "407-group-family-products"
export "180-cyc-n-loops"
export "1000-prime-numbers"

{` Chapter 10 (fingp.tex), orders of the first finite groups:
   - the example at fingp.tex:59: the trivial group has order 1, the cyclic
     group C_n has order n, the permutation group Σ_n has order n!
     (symmetric_group_card, module 412); C_0 ≃ Z is not finite;
   - the corollary at fingp.tex:102: |G × G'| = |G|·|G'|;
   - the remark at fingp.tex:105: the n-fold product C_2^n (rem:noofsubgps)
     has order 2^n. We use power_group (Fin n) (module 407, the book's
     Π_{s:S} G of ex:bigproductofgroups for the constant family), since its
     symmetries are literally functions Fin n → USym C_2; the binary iterate
     is covered by product_group_card (litmus |C_2 × C_2| = 4).
   Cardinality statements take an arbitrary finiteness proof h (IsFiniteGroup
   is a proposition). Helper: |Fin n → A| = |A|^n (fin_functions_split is a
   local copy of module 460's lemma, to avoid importing chapter-4 sign theory). `}

{` Contractible types are finite of cardinality 1. `}
def fingp_contractible_fin_one_equiv (A : Type) (h : BookIsContr A) : Equiv A (Fin (suc. zero.))
  ≔ compose_equiv A Unit (Fin (suc. zero.)) (contractible_unit_equiv A (native_contraction A h))
      (canonical_inverse_equiv (Fin (suc. zero.)) Unit fin_one_equiv)

def unit_group_finite : IsFiniteGroup unit_group
  ≔ finite_from_equiv (USym unit_group) (suc. zero.)
      (fingp_contractible_fin_one_equiv (USym unit_group) unit_group_usym_contractible)

def unit_group_card (h : IsFiniteGroup unit_group) : Id Nat (group_card unit_group h) (suc. zero.)
  ≔ cardinality_from_path (USym unit_group) h (suc. zero.)
      (ua (USym unit_group) (Fin (suc. zero.))
        (fingp_contractible_fin_one_equiv (USym unit_group) unit_group_usym_contractible))

def trivial_group_finite : IsFiniteGroup trivial_group
  ≔ finite_from_equiv (USym trivial_group) (suc. zero.)
      (fingp_contractible_fin_one_equiv (USym trivial_group) trivial_group_usym_contractible)

{` fingp.tex:59, first clause: the trivial group has order 1. `}
def trivial_group_card (h : IsFiniteGroup trivial_group) : Id Nat (group_card trivial_group h) (suc. zero.)
  ≔ cardinality_from_path (USym trivial_group) h (suc. zero.)
      (ua (USym trivial_group) (Fin (suc. zero.))
        (fingp_contractible_fin_one_equiv (USym trivial_group) trivial_group_usym_contractible))

{` C_{b+1}: evaluation at 0 (cyc_loop_equiv, module 180) followed by
   Z/(b+1) ≃ Fin (b+1). `}
def cyclic_group_usym_fin_equiv (b : Nat) : Equiv (USym (cyclic_group (suc. b))) (Fin (suc. b))
  ≔ compose_equiv (USym (cyclic_group (suc. b))) (Remainder (suc. b)) (Fin (suc. b)) (cyc_loop_equiv b)
      (canonical_inverse_equiv (Fin (suc. b)) (Remainder (suc. b)) (fin_book_below_equiv (suc. b)))

def cyclic_group_finite (b : Nat) : IsFiniteGroup (cyclic_group (suc. b))
  ≔ finite_from_equiv (USym (cyclic_group (suc. b))) (suc. b) (cyclic_group_usym_fin_equiv b)

{` fingp.tex:59, second clause: C_n has order n (n = b+1 ≥ 1). `}
def cyclic_group_card (b : Nat) (h : IsFiniteGroup (cyclic_group (suc. b)))
  : Id Nat (group_card (cyclic_group (suc. b)) h) (suc. b)
  ≔ cardinality_from_path (USym (cyclic_group (suc. b))) h (suc. b)
      (ua (USym (cyclic_group (suc. b))) (Fin (suc. b)) (cyclic_group_usym_fin_equiv b))

{` C_0 = Aut_Cyc(Z, succ) ≃ Z is not finite: Z is not finite, since
   i ↦ pos i would inject Fin (n+1) into Fin n (pigeonhole, module 49). `}
def fingp_int_fin_map (n : Nat) (e : Equiv Int (Fin n)) (i : Fin (suc. n)) : Fin n
  ≔ e .map (pos. (fin_index (suc. n) i))

def fingp_int_pos_injective (a b : Nat) (p : Id Int (pos. a) (pos. b)) : Id Nat a b
  ≔ nat_decode a b (int_encode (pos. a) (pos. b) p)

{` (The steps below are separate definitions: inlined into one term they
   trigger the Narya anomaly "Meta.Map.find_opt".) `}
def fingp_int_collision_same (n : Nat) (e : Equiv Int (Fin n)) (c : Collision (Fin (suc. n)) (Fin n) (fingp_int_fin_map n e))
  : Id Int (pos. (fin_index (suc. n) (c .left))) (pos. (fin_index (suc. n) (c .right)))
  ≔ equivalence_injective Int (Fin n) e (pos. (fin_index (suc. n) (c .left))) (pos. (fin_index (suc. n) (c .right))) (c .same)

def fingp_int_collision_distinct (n : Nat) (e : Equiv Int (Fin n)) (c : Collision (Fin (suc. n)) (Fin n) (fingp_int_fin_map n e))
  (q : Id Nat (fin_index (suc. n) (c .left)) (fin_index (suc. n) (c .right))) : Empty
  ≔ c .distinct (fin_index_injective (suc. n) (c .left) (c .right) q)

def fingp_int_collision_absurd (n : Nat) (e : Equiv Int (Fin n)) (c : Collision (Fin (suc. n)) (Fin n) (fingp_int_fin_map n e))
  : Empty
  ≔ fingp_int_collision_distinct n e c
      (fingp_int_pos_injective (fin_index (suc. n) (c .left)) (fin_index (suc. n) (c .right)) (fingp_int_collision_same n e c))

def fingp_int_not_fin (n : Nat) (p : Id Type Int (Fin n)) : Empty
  ≔ fingp_int_collision_absurd n (id_to_equiv Int (Fin n) p)
      (fin_pigeonhole n (fingp_int_fin_map n (id_to_equiv Int (Fin n) p)))

def int_not_finite (h : IsFinite Int) : Empty
  ≔ mere_rec (Σ Nat (n ↦ Id Type Int (Fin n))) Empty empty_prop (w ↦ fingp_int_not_fin (w .fst) (w .snd)) h

def cyclic_group_zero_usym_int_equiv : Equiv (USym (cyclic_group zero.)) Int
  ≔ compose_equiv (USym (cyclic_group zero.)) (Id Cycles infinite_cycle infinite_cycle) Int
      (automorphism_group_usym_equiv Cycles cycles_groupoid (principal_cycle zero.))
      (native_equivalence (Id Cycles infinite_cycle infinite_cycle) Int
        (cycle_automorphisms_evaluation infinite_cycle int_zero))

def cyclic_group_zero_not_finite (h : IsFiniteGroup (cyclic_group zero.)) : Empty
  ≔ int_not_finite (finite_of_equiv Int (USym (cyclic_group zero.))
      (canonical_inverse_equiv (USym (cyclic_group zero.)) Int cyclic_group_zero_usym_int_equiv) h)

{` The example at fingp.tex:59 in one statement: |TG| = 1, |C_{n+1}| = n+1
   and |Σ_n| = n! (with the finiteness proofs supplied here). `}
def fingp_example_group_orders
  : Product (Id Nat (group_card trivial_group trivial_group_finite) (suc. zero.))
      (Product ((n : Nat) → Id Nat (group_card (cyclic_group (suc. n)) (cyclic_group_finite n)) (suc. n))
        ((n : Nat) → Id Nat (group_card (symmetric_group n) (symmetric_group_finite n)) (factorial n)))
  ≔ (trivial_group_card trivial_group_finite, (n ↦ cyclic_group_card n (cyclic_group_finite n), symmetric_group_card))

{` The corollary at fingp.tex:102: |G × G'| = |G|·|G'|. `}
def product_group_finite (G H : Group) (hG : IsFiniteGroup G) (hH : IsFiniteGroup H) : IsFiniteGroup (product_group G H)
  ≔ finite_of_equiv (USym (product_group G H)) (Product (USym G) (USym H)) (product_group_usym_equiv G H)
      (finite_product (USym G) (USym H) hG hH)

def product_group_card (G H : Group) (hG : IsFiniteGroup G) (hH : IsFiniteGroup H) (h : IsFiniteGroup (product_group G H))
  : Id Nat (group_card (product_group G H) h) (mul (group_card G hG) (group_card H hH))
  ≔ let P ≔ Product (USym G) (USym H) in
    let hP ≔ finite_product (USym G) (USym H) hG hH in
    concat Nat (group_card (product_group G H) h) (cardinality P hP) (mul (group_card G hG) (group_card H hH))
      (cardinality_equiv (USym (product_group G H)) P (product_group_usym_equiv G H) h hP)
      (cardinality_product (USym G) (USym H) hG hH hP)

{` |Fin n → A| = |A|^n. `}
def fingp_fin_functions_join (k : Nat) (B : Type) (gb : Product (Fin k → B) B) : Fin (suc. k) → B
  ≔ [ inl. a ↦ gb .fst a | inr. u ↦ gb .snd ]

def fingp_fin_functions_join_eta (k : Nat) (B : Type) (f : Fin (suc. k) → B) (x : Fin (suc. k))
  : Id B (fingp_fin_functions_join k B (a ↦ f (inl. a), f (inr. star.)) x) (f x)
  ≔ match x [
  | inl. a ↦ refl (f (inl. a))
  | inr. u ↦ refl f (inr. (unit_prop star. u) : Id (Fin (suc. k)) (inr. star.) (inr. u)) ]

def fingp_fin_functions_split (k : Nat) (B : Type) : Equiv (Fin (suc. k) → B) (Product (Fin k → B) B)
  ≔ quasi_inverse_equiv (Fin (suc. k) → B) (Product (Fin k → B) B)
      (f ↦ (a ↦ f (inl. a), f (inr. star.)))
      (fingp_fin_functions_join k B)
      (f ↦ funext (Fin (suc. k)) (_ ↦ B) (fingp_fin_functions_join k B (a ↦ f (inl. a), f (inr. star.))) f
        (fingp_fin_functions_join_eta k B f))
      (gb ↦ refl gb)

def fingp_fin_zero_function (B : Type) (x : Fin zero.) : B ≔ match x []

def fingp_fin_zero_functions_equiv (B : Type) : Equiv (Fin zero. → B) (Fin (suc. zero.))
  ≔ quasi_inverse_equiv (Fin zero. → B) (Fin (suc. zero.)) (_ ↦ inr. star.) (_ ↦ fingp_fin_zero_function B)
      (f ↦ funext (Fin zero.) (_ ↦ B) (fingp_fin_zero_function B) f (x ↦ match x []))
      [ inl. e ↦ match e [] | inr. u ↦ inr. (unit_prop star. u) ]

def fin_functions_finite (n : Nat) (A : Type) (hA : IsFinite A) : IsFinite (Fin n → A)
  ≔ match n [
  | zero. ↦ finite_from_equiv (Fin zero. → A) (suc. zero.) (fingp_fin_zero_functions_equiv A)
  | suc. k ↦ finite_of_equiv (Fin (suc. k) → A) (Product (Fin k → A) A) (fingp_fin_functions_split k A)
      (finite_product (Fin k → A) A (fin_functions_finite k A hA) hA) ]

def fin_functions_card (n : Nat) (A : Type) (hA : IsFinite A) (h : IsFinite (Fin n → A))
  : Id Nat (cardinality (Fin n → A) h) (nat_power (cardinality A hA) n)
  ≔ match n [
  | zero. ↦ cardinality_from_path (Fin zero. → A) h (suc. zero.)
      (ua (Fin zero. → A) (Fin (suc. zero.)) (fingp_fin_zero_functions_equiv A))
  | suc. k ↦
    let P ≔ Product (Fin k → A) A in
    let hk ≔ fin_functions_finite k A hA in
    let hP ≔ finite_product (Fin k → A) A hk hA in
    calc
      cardinality (Fin (suc. k) → A) h = cardinality P hP
        by cardinality_equiv (Fin (suc. k) → A) P (fingp_fin_functions_split k A) h hP
      = mul (cardinality (Fin k → A) hk) (cardinality A hA) by cardinality_product (Fin k → A) A hk hA hP
      = mul (nat_power (cardinality A hA) k) (cardinality A hA)
        by refl ((x ↦ mul x (cardinality A hA)) : Nat → Nat) (fin_functions_card k A hA hk) ∎ ]

{` G^n ≔ power_group (Fin n) G has order |G|^n. `}
def fin_power_group_finite (n : Nat) (G : Group) (hG : IsFiniteGroup G)
  : IsFiniteGroup (power_group (Fin n) (fin_is_finite n) G)
  ≔ finite_of_equiv (USym (power_group (Fin n) (fin_is_finite n) G)) (Fin n → USym G)
      (power_group_usym_equiv (Fin n) (fin_is_finite n) G) (fin_functions_finite n (USym G) hG)

def fin_power_group_card (n : Nat) (G : Group) (hG : IsFiniteGroup G) (h : IsFiniteGroup (power_group (Fin n) (fin_is_finite n) G))
  : Id Nat (group_card (power_group (Fin n) (fin_is_finite n) G) h) (nat_power (group_card G hG) n)
  ≔ let F ≔ Fin n → USym G in
    let hF ≔ fin_functions_finite n (USym G) hG in
    concat Nat (group_card (power_group (Fin n) (fin_is_finite n) G) h) (cardinality F hF) (nat_power (group_card G hG) n)
      (cardinality_equiv (USym (power_group (Fin n) (fin_is_finite n) G)) F
        (power_group_usym_equiv (Fin n) (fin_is_finite n) G) h hF)
      (fin_functions_card n (USym G) hG hF)

{` The remark at fingp.tex:105: C_2^n has order 2^n. `}
def cyclic_two_power_finite (n : Nat) : IsFiniteGroup (power_group (Fin n) (fin_is_finite n) (cyclic_group two))
  ≔ fin_power_group_finite n (cyclic_group two) (cyclic_group_finite (suc. zero.))

def cyclic_two_power_card (n : Nat) (h : IsFiniteGroup (power_group (Fin n) (fin_is_finite n) (cyclic_group two)))
  : Id Nat (group_card (power_group (Fin n) (fin_is_finite n) (cyclic_group two)) h) (nat_power two n)
  ≔ concat Nat (group_card (power_group (Fin n) (fin_is_finite n) (cyclic_group two)) h)
      (nat_power (group_card (cyclic_group two) (cyclic_group_finite (suc. zero.))) n) (nat_power two n)
      (fin_power_group_card n (cyclic_group two) (cyclic_group_finite (suc. zero.)) h)
      (refl ((x ↦ nat_power x n) : Nat → Nat) (cyclic_group_card (suc. zero.) (cyclic_group_finite (suc. zero.))))

{` Litmus: |C_2 × C_2| = 4 and |C_2^3| = 8 (the right-hand sides are
   numerals, so these also check that mul and nat_power compute). `}
def cyclic_two_square_card
  : Id Nat (group_card (product_group (cyclic_group two) (cyclic_group two))
      (product_group_finite (cyclic_group two) (cyclic_group two) (cyclic_group_finite (suc. zero.)) (cyclic_group_finite (suc. zero.))))
      (suc. (suc. (suc. (suc. zero.))))
  ≔ concat Nat (group_card (product_group (cyclic_group two) (cyclic_group two))
      (product_group_finite (cyclic_group two) (cyclic_group two) (cyclic_group_finite (suc. zero.)) (cyclic_group_finite (suc. zero.))))
      (mul (group_card (cyclic_group two) (cyclic_group_finite (suc. zero.))) (group_card (cyclic_group two) (cyclic_group_finite (suc. zero.))))
      (suc. (suc. (suc. (suc. zero.))))
      (product_group_card (cyclic_group two) (cyclic_group two) (cyclic_group_finite (suc. zero.)) (cyclic_group_finite (suc. zero.))
        (product_group_finite (cyclic_group two) (cyclic_group two) (cyclic_group_finite (suc. zero.)) (cyclic_group_finite (suc. zero.))))
      (refl ((x ↦ mul x x) : Nat → Nat) (cyclic_group_card (suc. zero.) (cyclic_group_finite (suc. zero.))))

def cyclic_two_cube_card
  : Id Nat (group_card (power_group (Fin (suc. (suc. (suc. zero.)))) (fin_is_finite (suc. (suc. (suc. zero.)))) (cyclic_group two))
      (cyclic_two_power_finite (suc. (suc. (suc. zero.)))))
      (suc. (suc. (suc. (suc. (suc. (suc. (suc. (suc. zero.))))))))
  ≔ cyclic_two_power_card (suc. (suc. (suc. zero.))) (cyclic_two_power_finite (suc. (suc. (suc. zero.))))
