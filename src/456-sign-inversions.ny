export "455-sign-homomorphism"

{` Chapter 4, sec:sign-homomorphism: xca:sign-by-crossings. For a permutation
   σ of Fin n, an inversion is an ordered pair (i, j) with i < j and
   σ(i) > σ(j); sgn(σ) = (−1)^inv(σ). Here for n ≥ 2 and USym sgn; the
   version for the sign of permutations (all n) is in module 458. `}

def bool_and (a b : Bool) : Bool ≔ match a [ false. ↦ false. | true. ↦ b ]

{` The ordered pairs i < j of Fin n, and the inversions of σ. `}
def FinOrderedPairs (n : Nat) : Type
  ≔ Σ (Product (Fin n) (Fin n)) (p ↦ Id Bool (fin_lt n (p .fst) (p .snd)) true.)

def Inversions (n : Nat) (s : Equiv (Fin n) (Fin n)) : Type
  ≔ Σ (Product (Fin n) (Fin n)) (p ↦ Product (Id Bool (fin_lt n (p .fst) (p .snd)) true.)
      (Id Bool (fin_lt n (s .map (p .snd)) (s .map (p .fst))) true.))

def bool_and_true_to (a b : Bool) (q : Id Bool (bool_and a b) true.) : Product (Id Bool a true.) (Id Bool b true.)
  ≔ match a [
  | false. ↦ match bool_encode false. true. q []
  | true. ↦ (refl (true. : Bool), q) ]

def bool_and_true_from (a b : Bool) (pq : Product (Id Bool a true.) (Id Bool b true.)) : Id Bool (bool_and a b) true.
  ≔ match a [
  | false. ↦ pq .fst
  | true. ↦ pq .snd ]

def bool_and_true (a b : Bool) : Equiv (Id Bool (bool_and a b) true.) (Product (Id Bool a true.) (Id Bool b true.))
  ≔ iff_equiv (Id Bool (bool_and a b) true.) (Product (Id Bool a true.) (Id Bool b true.))
      (bool_set (bool_and a b) true.) (product_prop (Id Bool a true.) (Id Bool b true.) (bool_set a true.) (bool_set b true.))
      (bool_and_true_to a b) (bool_and_true_from a b)

def inversion_test (n : Nat) (s : Equiv (Fin n) (Fin n)) (i j : Fin n) : Bool
  ≔ bool_and (fin_lt n i j) (fin_lt n (s .map j) (s .map i))

def inversions_finite (n : Nat) (s : Equiv (Fin n) (Fin n)) : IsFinite (Inversions n s)
  ≔ finite_of_equiv (Inversions n s) (Σ (Product (Fin n) (Fin n)) (p ↦ Id Bool (inversion_test n s (p .fst) (p .snd)) true.))
      (family_equiv (Product (Fin n) (Fin n))
        (p ↦ Product (Id Bool (fin_lt n (p .fst) (p .snd)) true.) (Id Bool (fin_lt n (s .map (p .snd)) (s .map (p .fst))) true.))
        (p ↦ Id Bool (inversion_test n s (p .fst) (p .snd)) true.)
        (p ↦ canonical_inverse_equiv (Id Bool (inversion_test n s (p .fst) (p .snd)) true.)
          (Product (Id Bool (fin_lt n (p .fst) (p .snd)) true.) (Id Bool (fin_lt n (s .map (p .snd)) (s .map (p .fst))) true.))
          (bool_and_true (fin_lt n (p .fst) (p .snd)) (fin_lt n (s .map (p .snd)) (s .map (p .fst))))))
      (finite_true_subset (Product (Fin n) (Fin n)) (finite_product (Fin n) (Fin n) (fin_is_finite n) (fin_is_finite n))
        (p ↦ inversion_test n s (p .fst) (p .snd)))

{` inv(σ), the number of inversions. `}
def inversion_count (n : Nat) (s : Equiv (Fin n) (Fin n)) : Nat ≔ cardinality (Inversions n s) (inversions_finite n s)

{` A computable count: Σ_i #{ j | (i, j) is an inversion }. `}
def fin_nat_sum (n : Nat) (c : Fin n → Nat) : Nat
  ≔ match n [ zero. ↦ zero. | suc. k ↦ add (fin_nat_sum k (i ↦ c (inl. i))) (c (inr. star.)) ]

def inversion_number_fun (n : Nat) (f : Fin n → Fin n) : Nat
  ≔ fin_nat_sum n (i ↦ true_count n (j ↦ bool_and (fin_lt n i j) (fin_lt n (f j) (f i))))

def inversion_number (n : Nat) (s : Equiv (Fin n) (Fin n)) : Nat ≔ inversion_number_fun n (s .map)

def arithmetic_sum_fin (n : Nat) (c : Fin n → Nat) : Id Nat (arithmetic_sum (Fin n) (fin_is_finite n) c) (fin_nat_sum n c)
  ≔ match n [
  | zero. ↦ arithmetic_sum_empty c
  | suc. k ↦ concat Nat (arithmetic_sum (Fin (suc. k)) (fin_is_finite (suc. k)) c)
      (add (arithmetic_sum (Fin k) (fin_is_finite k) (i ↦ c (inl. i))) (c (inr. star.)))
      (fin_nat_sum (suc. k) c)
      (arithmetic_sum_step k c)
      (refl ((x ↦ add x (c (inr. star.))) : Nat → Nat) (arithmetic_sum_fin k (i ↦ c (inl. i)))) ]

def pairs_sigma_equiv (n : Nat) (b : Fin n → Fin n → Bool)
  : Equiv (Σ (Product (Fin n) (Fin n)) (p ↦ Id Bool (b (p .fst) (p .snd)) true.)) (Σ (Fin n) (i ↦ Fin (true_count n (b i))))
  ≔ compose_equiv (Σ (Product (Fin n) (Fin n)) (p ↦ Id Bool (b (p .fst) (p .snd)) true.)) (Σ (Fin n) (i ↦ BoolCarrier n (b i)))
      (Σ (Fin n) (i ↦ Fin (true_count n (b i))))
      (quasi_inverse_equiv (Σ (Product (Fin n) (Fin n)) (p ↦ Id Bool (b (p .fst) (p .snd)) true.)) (Σ (Fin n) (i ↦ BoolCarrier n (b i)))
        (u ↦ (u .fst .fst, (u .fst .snd, u .snd))) (v ↦ ((v .fst, v .snd .fst), v .snd .snd)) (u ↦ refl u) (v ↦ refl v))
      (family_equiv (Fin n) (i ↦ BoolCarrier n (b i)) (i ↦ Fin (true_count n (b i))) (i ↦ bool_carrier_fin n (b i)))

def inversion_count_number (n : Nat) (s : Equiv (Fin n) (Fin n)) : Id Nat (inversion_count n s) (inversion_number n s)
  ≔ let b ≔ inversion_test n s in
    let S ≔ Σ (Product (Fin n) (Fin n)) (p ↦ Id Bool (b (p .fst) (p .snd)) true.) in
    let T ≔ Σ (Fin n) (i ↦ Fin (true_count n (b i))) in
    let hT ≔ finite_sigma (Fin n) (fin_is_finite n) (i ↦ Fin (true_count n (b i))) (i ↦ fin_is_finite (true_count n (b i))) in
    calc inversion_count n s
      = cardinality T hT
        by cardinality_equiv (Inversions n s) T
          (compose_equiv (Inversions n s) S T
            (family_equiv (Product (Fin n) (Fin n))
              (p ↦ Product (Id Bool (fin_lt n (p .fst) (p .snd)) true.) (Id Bool (fin_lt n (s .map (p .snd)) (s .map (p .fst))) true.))
              (p ↦ Id Bool (b (p .fst) (p .snd)) true.)
              (p ↦ canonical_inverse_equiv (Id Bool (b (p .fst) (p .snd)) true.)
                (Product (Id Bool (fin_lt n (p .fst) (p .snd)) true.) (Id Bool (fin_lt n (s .map (p .snd)) (s .map (p .fst))) true.))
                (bool_and_true (fin_lt n (p .fst) (p .snd)) (fin_lt n (s .map (p .snd)) (s .map (p .fst))))))
            (pairs_sigma_equiv n b))
          (inversions_finite n s) hT
      = fin_nat_sum n (i ↦ true_count n (b i)) by arithmetic_sum_fin n (i ↦ true_count n (b i)) ∎

{` E(Fin n) ≃ ordered pairs, d ↦ (min d, max d). `}
def two_subsets_path (X : Type) (e e' : TwoSubsets X) (p : Id (Subtypes X) (e .fst) (e' .fst)) : Id (TwoSubsets X) e e'
  ≔ subtype_equal (Subtypes X) (P ↦ Mere (Id Type (SubtypeCarrier X P) (Fin two))) (P ↦ mere_isprop (Id Type (SubtypeCarrier X P) (Fin two))) e e' p

def subset_to_pair (n : Nat) (d : TwoSubsets (Fin n)) : FinOrderedPairs n
  ≔ ((two_subset_min n d .fst, two_subset_max n d .fst), two_subset_min_lt_max n d)

def pair_to_subset (n : Nat) (u : FinOrderedPairs n) : TwoSubsets (Fin n)
  ≔ pair_subset (Fin n) (fin_set n) (u .fst .fst) (u .fst .snd) (fin_lt_ne n (u .fst .fst) (u .fst .snd) (u .snd))

def two_subset_member_min_or_max (n : Nat) (d : TwoSubsets (Fin n)) (c : two_subset_carrier n d)
  (dc : Decidable (Id (two_subset_carrier n d) c (two_subset_min n d)))
  : Sum (Id (Fin n) (c .fst) (two_subset_min n d .fst)) (Id (Fin n) (c .fst) (two_subset_max n d .fst))
  ≔ match dc [
  | inl. p ↦ inl. (refl ((u ↦ u .fst) : two_subset_carrier n d → Fin n) p)
  | inr. q ↦ inr. (refl ((u ↦ u .fst) : two_subset_carrier n d → Fin n)
      (two_element_other_unique (two_subset_carrier n d) (two_subset_two_element (Fin n) d) (two_subset_min n d) c q)) ]

def pair_subset_roundtrip (n : Nat) (d : TwoSubsets (Fin n)) : Id (TwoSubsets (Fin n)) (pair_to_subset n (subset_to_pair n d)) d
  ≔ let C ≔ two_subset_carrier n d in
    let mn ≔ two_subset_min n d in let mx ≔ two_subset_max n d in
    two_subsets_path (Fin n) (pair_to_subset n (subset_to_pair n d)) d
      (funext (Fin n) (_ ↦ PropTypes) (pair_to_subset n (subset_to_pair n d) .fst) (d .fst)
        (x ↦ proposition_extensionality (pair_to_subset n (subset_to_pair n d) .fst x) (d .fst x)
          [ inl. p ↦ transport (Fin n) (y ↦ d .fst y .fst) (mn .fst) x (inverse (Fin n) x (mn .fst) p) (mn .snd)
          | inr. q ↦ transport (Fin n) (y ↦ d .fst y .fst) (mx .fst) x (inverse (Fin n) x (mx .fst) q) (mx .snd) ]
          (h ↦ two_subset_member_min_or_max n d (x, h)
            (two_element_decidable_equality C (two_subset_two_element (Fin n) d) (x, h) mn))))

def pair_min_point (n : Nat) (u : FinOrderedPairs n) : two_subset_carrier n (pair_to_subset n u)
  ≔ (u .fst .fst, inl. (refl (u .fst .fst)))

def pair_max_point (n : Nat) (u : FinOrderedPairs n) : two_subset_carrier n (pair_to_subset n u)
  ≔ (u .fst .snd, inr. (refl (u .fst .snd)))

def pair_other_min (n : Nat) (u : FinOrderedPairs n)
  : Id (two_subset_carrier n (pair_to_subset n u)) (pair_max_point n u) (two_subset_other n (pair_to_subset n u) (pair_min_point n u))
  ≔ two_element_other_unique (two_subset_carrier n (pair_to_subset n u)) (two_subset_two_element (Fin n) (pair_to_subset n u))
      (pair_min_point n u) (pair_max_point n u)
      (p ↦ fin_lt_ne n (u .fst .fst) (u .fst .snd) (u .snd)
        (inverse (Fin n) (u .fst .snd) (u .fst .fst) (refl ((c ↦ c .fst) : two_subset_carrier n (pair_to_subset n u) → Fin n) p)))

def pair_min_is_min (n : Nat) (u : FinOrderedPairs n)
  : Id (two_subset_carrier n (pair_to_subset n u)) (pair_min_point n u) (two_subset_min n (pair_to_subset n u))
  ≔ two_subset_min_unique n (pair_to_subset n u) (pair_min_point n u)
      (concat Bool (fin_lt n (u .fst .fst) (two_subset_other n (pair_to_subset n u) (pair_min_point n u) .fst))
        (fin_lt n (u .fst .fst) (u .fst .snd)) true.
        (refl ((c ↦ fin_lt n (u .fst .fst) (c .fst)) : two_subset_carrier n (pair_to_subset n u) → Bool)
          (inverse (two_subset_carrier n (pair_to_subset n u)) (pair_max_point n u)
            (two_subset_other n (pair_to_subset n u) (pair_min_point n u)) (pair_other_min n u)))
        (u .snd))

def subset_pair_roundtrip (n : Nat) (u : FinOrderedPairs n) : Id (FinOrderedPairs n) (subset_to_pair n (pair_to_subset n u)) u
  ≔ let e ≔ pair_to_subset n u in let C ≔ two_subset_carrier n e in
    let pmin : Id C (two_subset_min n e) (pair_min_point n u) ≔ inverse C (pair_min_point n u) (two_subset_min n e) (pair_min_is_min n u) in
    let pmax : Id C (two_subset_max n e) (pair_max_point n u)
      ≔ concat C (two_subset_max n e) (two_subset_other n e (pair_min_point n u)) (pair_max_point n u)
          (refl (two_subset_other n e) pmin) (inverse C (pair_max_point n u) (two_subset_other n e (pair_min_point n u)) (pair_other_min n u)) in
    subtype_equal (Product (Fin n) (Fin n)) (p ↦ Id Bool (fin_lt n (p .fst) (p .snd)) true.)
      (p ↦ bool_set (fin_lt n (p .fst) (p .snd)) true.) (subset_to_pair n e) u
      (refl ((c ↦ c .fst) : C → Fin n) pmin, refl ((c ↦ c .fst) : C → Fin n) pmax)

def two_subsets_pairs_equiv (n : Nat) : Equiv (TwoSubsets (Fin n)) (FinOrderedPairs n)
  ≔ quasi_inverse_equiv (TwoSubsets (Fin n)) (FinOrderedPairs n) (subset_to_pair n) (pair_to_subset n)
      (pair_subset_roundtrip n) (subset_pair_roundtrip n)

{` The preimage of two-element subsets along a permutation is a bijection of E. `}
def subset_preimage_equiv (n : Nat) (t : Equiv (Fin n) (Fin n)) : Equiv (TwoSubsets (Fin n)) (TwoSubsets (Fin n))
  ≔ let ti ≔ canonical_inverse_equiv (Fin n) (Fin n) t in
    quasi_inverse_equiv (TwoSubsets (Fin n)) (TwoSubsets (Fin n)) (subset_preimage (Fin n) (Fin n) t)
      (subset_preimage (Fin n) (Fin n) ti)
      (e ↦ two_subsets_path (Fin n) (subset_preimage (Fin n) (Fin n) ti (subset_preimage (Fin n) (Fin n) t e)) e
        (funext (Fin n) (_ ↦ PropTypes) (x ↦ e .fst (t .map (ti .map x))) (e .fst) (x ↦ refl (e .fst) (equiv_counit (Fin n) (Fin n) t x))))
      (e ↦ two_subsets_path (Fin n) (subset_preimage (Fin n) (Fin n) t (subset_preimage (Fin n) (Fin n) ti e)) e
        (funext (Fin n) (_ ↦ PropTypes) (x ↦ e .fst (ti .map (t .map x))) (e .fst) (x ↦ refl (e .fst) (equiv_retraction (Fin n) (Fin n) t x))))

{` Counting is invariant under reindexing by a bijection. `}
def finite_true_count_reindex (E : Type) (hE : IsFinite E) (f : Equiv E E) (b : E → Bool)
  : Id Nat (finite_true_count E hE (e ↦ b (f .map e))) (finite_true_count E hE b)
  ≔ cardinality_equiv (Σ E (e ↦ Id Bool (b (f .map e)) true.)) (Σ E (e ↦ Id Bool (b e) true.))
      (subtype_reindex_equiv E E f (e ↦ Id Bool (b e) true.) (e ↦ bool_set (b e) true.))
      (finite_true_subset E hE (e ↦ b (f .map e))) (finite_true_subset E hE b)

def finite_true_count_transfer (E F : Type) (hE : IsFinite E) (hF : IsFinite F) (f : Equiv E F) (b : F → Bool)
  : Id Nat (finite_true_count E hE (e ↦ b (f .map e))) (finite_true_count F hF b)
  ≔ cardinality_equiv (Σ E (e ↦ Id Bool (b (f .map e)) true.)) (Σ F (y ↦ Id Bool (b y) true.))
      (subtype_reindex_equiv E F f (y ↦ Id Bool (b y) true.) (y ↦ bool_set (b y) true.))
      (finite_true_subset E hE (e ↦ b (f .map e))) (finite_true_subset F hF b)

{` The key local computation: t·ω0 and ω0 differ at e exactly when
   d = t⁻¹(e) is an inversion: t(max d) < t(min d). `}
def action_image_min (n : Nat) (t : Equiv (Fin n) (Fin n)) (e : TwoSubsets (Fin n)) : two_subset_carrier n e
  ≔ (t .map (two_subset_min n (subset_preimage (Fin n) (Fin n) t e) .fst), two_subset_min n (subset_preimage (Fin n) (Fin n) t e) .snd)

def action_image_max (n : Nat) (t : Equiv (Fin n) (Fin n)) (e : TwoSubsets (Fin n)) : two_subset_carrier n e
  ≔ (t .map (two_subset_max n (subset_preimage (Fin n) (Fin n) t e) .fst), two_subset_max n (subset_preimage (Fin n) (Fin n) t e) .snd)

def action_differ_case (n : Nat) (t : Equiv (Fin n) (Fin n)) (e : TwoSubsets (Fin n)) (b : Bool)
  (q : Id Bool (fin_lt n (t .map (two_subset_min n (subset_preimage (Fin n) (Fin n) t e) .fst))
      (t .map (two_subset_max n (subset_preimage (Fin n) (Fin n) t e) .fst))) b)
  : Id Bool (two_differ (two_subset_carrier n e) (two_set_two_element (two_subset_bsigma (Fin n) (fin_set n) e))
        (local_ordering_action (Fin n) (Fin n) t (standard_local_ordering n) e) (two_subset_min n e))
      (fin_lt n (t .map (two_subset_max n (subset_preimage (Fin n) (Fin n) t e) .fst))
        (t .map (two_subset_min n (subset_preimage (Fin n) (Fin n) t e) .fst)))
  ≔ let d ≔ subset_preimage (Fin n) (Fin n) t e in
    let C ≔ two_subset_carrier n e in let h ≔ two_subset_two_element (Fin n) e in
    let h2 ≔ two_set_two_element (two_subset_bsigma (Fin n) (fin_set n) e) in
    let mn ≔ two_subset_min n d in let mx ≔ two_subset_max n d in
    let a : C ≔ action_image_min n t e in
    let c : C ≔ action_image_max n t e in
    let nmm : Not (Id (Fin n) (mn .fst) (mx .fst)) ≔ fin_lt_ne n (mn .fst) (mx .fst) (two_subset_min_lt_max n d) in
    let nac : Not (Id C a c) ≔ p ↦ nmm (equiv_injective_path (Fin n) (Fin n) t (mn .fst) (mx .fst)
      (refl ((u ↦ u .fst) : C → Fin n) p)) in
    let oa : Id C c (two_subset_other n e a) ≔ two_element_other_unique C h a c (p ↦ nac (inverse C c a p)) in
    let oc : Id C a (two_subset_other n e c) ≔ two_element_other_unique C h c a nac in
    match b [
    | true. ↦ calc two_differ C h2 a (two_subset_min n e)
        = false. by two_differ_eq C h2 a (two_subset_min n e)
            (two_subset_min_unique n e a
              (concat Bool (fin_lt n (a .fst) (two_subset_other n e a .fst)) (fin_lt n (a .fst) (c .fst)) true.
                (refl ((u ↦ fin_lt n (a .fst) (u .fst)) : C → Bool) (inverse C c (two_subset_other n e a) oa)) q))
        = fin_lt n (c .fst) (a .fst)
          by inverse Bool (fin_lt n (c .fst) (a .fst)) false. (fin_lt_asym n (a .fst) (c .fst) q) ∎
    | false. ↦
        let cl : Id Bool (fin_lt n (c .fst) (a .fst)) true.
          ≔ calc fin_lt n (c .fst) (a .fst) = bool_not (fin_lt n (a .fst) (c .fst))
                by fin_lt_flip n (a .fst) (c .fst) (p ↦ nac (subtype_equal (Fin n) (x ↦ e .fst x .fst) (x ↦ e .fst x .snd) a c p))
              = true. by refl bool_not q ∎ in
        calc two_differ C h2 a (two_subset_min n e)
          = true. by two_differ_ne C h2 a (two_subset_min n e)
              (p ↦ nac (inverse C c a (concat C c (two_subset_min n e) a
                (two_subset_min_unique n e c
                  (concat Bool (fin_lt n (c .fst) (two_subset_other n e c .fst)) (fin_lt n (c .fst) (a .fst)) true.
                    (refl ((u ↦ fin_lt n (c .fst) (u .fst)) : C → Bool) (inverse C a (two_subset_other n e c) oc)) cl))
                (inverse C a (two_subset_min n e) p))))
          = fin_lt n (c .fst) (a .fst) by inverse Bool (fin_lt n (c .fst) (a .fst)) true. cl ∎ ]

def action_differ (n : Nat) (t : Equiv (Fin n) (Fin n)) (e : TwoSubsets (Fin n))
  : Id Bool (two_differ (two_subset_carrier n e) (two_set_two_element (two_subset_bsigma (Fin n) (fin_set n) e))
        (local_ordering_action (Fin n) (Fin n) t (standard_local_ordering n) e) (two_subset_min n e))
      (fin_lt n (t .map (two_subset_max n (subset_preimage (Fin n) (Fin n) t e) .fst))
        (t .map (two_subset_min n (subset_preimage (Fin n) (Fin n) t e) .fst)))
  ≔ action_differ_case n t e
      (fin_lt n (t .map (two_subset_min n (subset_preimage (Fin n) (Fin n) t e) .fst))
        (t .map (two_subset_max n (subset_preimage (Fin n) (Fin n) t e) .fst)))
      (refl (fin_lt n (t .map (two_subset_min n (subset_preimage (Fin n) (Fin n) t e) .fst))
        (t .map (two_subset_max n (subset_preimage (Fin n) (Fin n) t e) .fst))))

{` The parity of the disagreement between t·ω0 and ω0 is the parity of inv(t). `}
def action_parity_inversions (n : Nat) (hE : IsFinite (TwoSubsets (Fin n))) (t : Equiv (Fin n) (Fin n))
  : Id Bool (parity_odd (TwoSubsets (Fin n)) hE (two_subset_bsigma (Fin n) (fin_set n))
        (local_ordering_action (Fin n) (Fin n) t (standard_local_ordering n)) (standard_local_ordering n))
      (nat_odd (inversion_count n t))
  ≔ let E ≔ TwoSubsets (Fin n) in
    let P ≔ two_subset_bsigma (Fin n) (fin_set n) in
    let w0 ≔ standard_local_ordering n in
    let w1 ≔ local_ordering_action (Fin n) (Fin n) t w0 in
    let g : E → Bool ≔ d ↦ fin_lt n (t .map (two_subset_max n d .fst)) (t .map (two_subset_min n d .fst)) in
    let hP ≔ finite_true_subset (Product (Fin n) (Fin n)) (finite_product (Fin n) (Fin n) (fin_is_finite n) (fin_is_finite n))
      (p ↦ inversion_test n t (p .fst) (p .snd)) in
    let hO : IsFinite (FinOrderedPairs n) ≔ finite_of_equiv (FinOrderedPairs n) E
      (canonical_inverse_equiv E (FinOrderedPairs n) (two_subsets_pairs_equiv n)) hE in
    let g' : FinOrderedPairs n → Bool ≔ u ↦ fin_lt n (t .map (u .fst .snd)) (t .map (u .fst .fst)) in
    calc parity_odd E hE P w1 w0
      = nat_odd (finite_true_count E hE (parity_differ E P w1 w0)) by parity_odd_count E hE P w1 w0
      = nat_odd (finite_true_count E hE (e ↦ g (subset_preimage (Fin n) (Fin n) t e)))
        by refl nat_odd (finite_true_count_homotopy E hE (parity_differ E P w1 w0) (e ↦ g (subset_preimage (Fin n) (Fin n) t e))
          (action_differ n t))
      = nat_odd (finite_true_count E hE g) by refl nat_odd (finite_true_count_reindex E hE (subset_preimage_equiv n t) g)
      = nat_odd (finite_true_count (FinOrderedPairs n) hO g')
        by refl nat_odd (finite_true_count_transfer E (FinOrderedPairs n) hE hO (two_subsets_pairs_equiv n) g')
      = nat_odd (inversion_count n t)
        by refl nat_odd (cardinality_equiv (Σ (FinOrderedPairs n) (u ↦ Id Bool (g' u) true.)) (Inversions n t)
          (quasi_inverse_equiv (Σ (FinOrderedPairs n) (u ↦ Id Bool (g' u) true.)) (Inversions n t)
            (v ↦ (v .fst .fst, (v .fst .snd, v .snd))) (w ↦ ((w .fst, w .snd .fst), w .snd .snd)) (v ↦ refl v) (w ↦ refl w))
          (finite_true_subset (FinOrderedPairs n) hO g') (inversions_finite n t)) ∎

{` xca:sign-by-crossings for USym sgn (n ≥ 2): sgn(σ) = (−1)^inv(σ). `}
def usgn_inversions (m : Nat) (t : Equiv (Fin (suc. (suc. m))) (Fin (suc. (suc. m))))
  : Id Sign (sigma_two_sign (usgn (suc. (suc. m)) (permutation_symmetry (standard_set (suc. (suc. m))) t)))
      (bool_sign (nat_odd (inversion_count (suc. (suc. m)) t)))
  ≔ concat Sign (sigma_two_sign (usgn (suc. (suc. m)) (permutation_symmetry (standard_set (suc. (suc. m))) t)))
      (bool_sign (parity_odd (TwoSubsets (Fin (suc. (suc. m)))) (sign_subsets_finite (suc. (suc. m)) (standard_shape (suc. (suc. m))))
        (two_subset_bsigma (Fin (suc. (suc. m))) (fin_set (suc. (suc. m))))
        (local_ordering_action (Fin (suc. (suc. m))) (Fin (suc. (suc. m))) t (standard_local_ordering (suc. (suc. m))))
        (standard_local_ordering (suc. (suc. m)))))
      (bool_sign (nat_odd (inversion_count (suc. (suc. m)) t)))
      (usgn_permutation_parity m t)
      (refl bool_sign (action_parity_inversions (suc. (suc. m)) (sign_subsets_finite (suc. (suc. m)) (standard_shape (suc. (suc. m)))) t))

def usgn_inversion_number (m : Nat) (t : Equiv (Fin (suc. (suc. m))) (Fin (suc. (suc. m))))
  : Id Sign (sigma_two_sign (usgn (suc. (suc. m)) (permutation_symmetry (standard_set (suc. (suc. m))) t)))
      (bool_sign (nat_odd (inversion_number (suc. (suc. m)) t)))
  ≔ concat Sign (sigma_two_sign (usgn (suc. (suc. m)) (permutation_symmetry (standard_set (suc. (suc. m))) t)))
      (bool_sign (nat_odd (inversion_count (suc. (suc. m)) t)))
      (bool_sign (nat_odd (inversion_number (suc. (suc. m)) t)))
      (usgn_inversions m t)
      (refl ((k ↦ bool_sign (nat_odd k)) : Nat → Sign) (inversion_count_number (suc. (suc. m)) t))

{` The transposition (0 1) of Fin (m+2) has exactly one inversion, hence sign −1. `}
def fin_swap01 (m : Nat) : Fin (suc. (suc. m)) → Fin (suc. (suc. m))
  ≔ [ inr. u ↦ inl. (inr. u) | inl. (inr. u) ↦ inr. u | inl. (inl. x) ↦ inl. (inl. x) ]

def fin_swap01_involutive (m : Nat) (x : Fin (suc. (suc. m))) : Id (Fin (suc. (suc. m))) (fin_swap01 m (fin_swap01 m x)) x
  ≔ match x [
  | inr. u ↦ refl (inr. u : Fin (suc. (suc. m)))
  | inl. (inr. u) ↦ refl (inl. (inr. u) : Fin (suc. (suc. m)))
  | inl. (inl. y) ↦ refl (inl. (inl. y) : Fin (suc. (suc. m))) ]

def fin_swap01_equiv (m : Nat) : Equiv (Fin (suc. (suc. m))) (Fin (suc. (suc. m)))
  ≔ quasi_inverse_equiv (Fin (suc. (suc. m))) (Fin (suc. (suc. m))) (fin_swap01 m) (fin_swap01 m)
      (fin_swap01_involutive m) (fin_swap01_involutive m)

def true_count_all_false (n : Nat) (f : Fin n → Bool) (h : (x : Fin n) → Id Bool (f x) false.) : Id Nat (true_count n f) zero.
  ≔ match n [
  | zero. ↦ refl (zero. : Nat)
  | suc. k ↦ calc true_count (suc. k) f
      = add (true_count k (a ↦ f (inl. a))) (bool_to_nat (f (inr. star.))) by refl (true_count (suc. k) f)
      = add zero. zero. by refl add (true_count_all_false k (a ↦ f (inl. a)) (a ↦ h (inl. a))) (refl bool_to_nat (h (inr. star.)))
      = zero. by refl (zero. : Nat) ∎ ]

def fin_nat_sum_zero (n : Nat) (c : Fin n → Nat) (h : (x : Fin n) → Id Nat (c x) zero.) : Id Nat (fin_nat_sum n c) zero.
  ≔ match n [
  | zero. ↦ refl (zero. : Nat)
  | suc. k ↦ calc fin_nat_sum (suc. k) c
      = add (fin_nat_sum k (a ↦ c (inl. a))) (c (inr. star.)) by refl (fin_nat_sum (suc. k) c)
      = add zero. zero. by refl add (fin_nat_sum_zero k (a ↦ c (inl. a)) (a ↦ h (inl. a))) (h (inr. star.))
      = zero. by refl (zero. : Nat) ∎ ]

def bool_cases (b : Bool) : Sum (Id Bool b true.) (Id Bool b false.)
  ≔ match b [ true. ↦ inl. (refl (true. : Bool)) | false. ↦ inr. (refl (false. : Bool)) ]

def bool_and_asym (m : Nat) (x y : Fin m) : Id Bool (bool_and (fin_lt m x y) (fin_lt m y x)) false.
  ≔ match bool_cases (fin_lt m x y) [
  | inl. q ↦ concat Bool (bool_and (fin_lt m x y) (fin_lt m y x)) (bool_and true. false.) false.
      (refl bool_and q (fin_lt_asym m x y q)) (refl (false. : Bool))
  | inr. q ↦ refl ((b ↦ bool_and b (fin_lt m y x)) : Bool → Bool) q ]

def swap01_inversion_number (m : Nat) : Id Nat (inversion_number (suc. (suc. m)) (fin_swap01_equiv m)) (suc. zero.)
  ≔ let n : Nat ≔ suc. (suc. m) in
    let t ≔ fin_swap01_equiv m in
    let row : Fin n → Nat ≔ i ↦ true_count n (j ↦ inversion_test n t i j) in
    calc inversion_number n t
      = add (add (fin_nat_sum m (x ↦ row (inl. (inl. x)))) (row (inl. (inr. star.)))) (row (inr. star.))
        by refl (inversion_number n t)
      = add (add zero. zero.) (suc. zero.)
        by refl add
          (refl add
            (fin_nat_sum_zero m (x ↦ row (inl. (inl. x)))
              (x ↦ true_count_all_false m (y ↦ inversion_test n t (inl. (inl. x)) (inl. (inl. y)))
                (y ↦ bool_and_asym m x y)))
            (true_count_all_false m (y ↦ inversion_test n t (inl. (inr. star.)) (inl. (inl. y))) (y ↦ refl (false. : Bool))))
          (refl ((k ↦ suc. k) : Nat → Nat)
            (true_count_all_false m (y ↦ inversion_test n t (inr. star.) (inl. (inl. y))) (y ↦ refl (false. : Bool))))
      = suc. zero. by refl (suc. zero. : Nat) ∎

{` Litmus (lem:sign-properties (1) for the standard transposition): the
   transposition (0 1) of Fin (m+2) has sign −1, for every m. `}
def usgn_swap01 (m : Nat)
  : Id Sign (sigma_two_sign (usgn (suc. (suc. m)) (permutation_symmetry (standard_set (suc. (suc. m))) (fin_swap01_equiv m)))) minus.
  ≔ concat Sign (sigma_two_sign (usgn (suc. (suc. m)) (permutation_symmetry (standard_set (suc. (suc. m))) (fin_swap01_equiv m))))
      (bool_sign (nat_odd (inversion_number (suc. (suc. m)) (fin_swap01_equiv m)))) minus.
      (usgn_inversion_number m (fin_swap01_equiv m))
      (refl ((k ↦ bool_sign (nat_odd k)) : Nat → Sign) (swap01_inversion_number m))

{` Litmus: in Σ_3 the transposition (0 1) = τ of module 406 has one
   inversion (computed by refl) and sign −1. `}
def sigma3_tau_inversions : Id Nat (inversion_number three fin3_swap01_equiv) (suc. zero.) ≔ refl (suc. zero. : Nat)

def sigma3_tau_sign : Id Sign (sigma_two_sign (usgn three sigma3_tau)) minus.
  ≔ concat Sign (sigma_two_sign (usgn three sigma3_tau)) (bool_sign (nat_odd (inversion_number three fin3_swap01_equiv))) minus.
      (usgn_inversion_number (suc. zero.) fin3_swap01_equiv)
      (refl (minus. : Sign))

{` Counting over two-element subsets of Fin n by their ordered pairs (min, max). `}
def ordered_pairs_true_count (n : Nat) (b : Fin n → Fin n → Bool) (hO : IsFinite (FinOrderedPairs n))
  : Id Nat (finite_true_count (FinOrderedPairs n) hO (u ↦ b (u .fst .fst) (u .fst .snd)))
      (fin_nat_sum n (i ↦ true_count n (j ↦ bool_and (fin_lt n i j) (b i j))))
  ≔ let c : Fin n → Fin n → Bool ≔ i j ↦ bool_and (fin_lt n i j) (b i j) in
    let S1 ≔ Σ (FinOrderedPairs n) (u ↦ Id Bool (b (u .fst .fst) (u .fst .snd)) true.) in
    let S1' ≔ Σ (Product (Fin n) (Fin n)) (p ↦ Product (Id Bool (fin_lt n (p .fst) (p .snd)) true.) (Id Bool (b (p .fst) (p .snd)) true.)) in
    let S2 ≔ Σ (Product (Fin n) (Fin n)) (p ↦ Id Bool (c (p .fst) (p .snd)) true.) in
    let T ≔ Σ (Fin n) (i ↦ Fin (true_count n (c i))) in
    let hT ≔ finite_sigma (Fin n) (fin_is_finite n) (i ↦ Fin (true_count n (c i))) (i ↦ fin_is_finite (true_count n (c i))) in
    calc finite_true_count (FinOrderedPairs n) hO (u ↦ b (u .fst .fst) (u .fst .snd))
      = cardinality T hT
        by cardinality_equiv S1 T
          (compose_equiv S1 S1' T
            (quasi_inverse_equiv S1 S1' (v ↦ (v .fst .fst, (v .fst .snd, v .snd))) (w ↦ ((w .fst, w .snd .fst), w .snd .snd))
              (v ↦ refl v) (w ↦ refl w))
            (compose_equiv S1' S2 T
              (family_equiv (Product (Fin n) (Fin n))
                (p ↦ Product (Id Bool (fin_lt n (p .fst) (p .snd)) true.) (Id Bool (b (p .fst) (p .snd)) true.))
                (p ↦ Id Bool (c (p .fst) (p .snd)) true.)
                (p ↦ canonical_inverse_equiv (Id Bool (c (p .fst) (p .snd)) true.)
                  (Product (Id Bool (fin_lt n (p .fst) (p .snd)) true.) (Id Bool (b (p .fst) (p .snd)) true.))
                  (bool_and_true (fin_lt n (p .fst) (p .snd)) (b (p .fst) (p .snd)))))
              (pairs_sigma_equiv n c)))
          (finite_true_subset (FinOrderedPairs n) hO (u ↦ b (u .fst .fst) (u .fst .snd))) hT
      = fin_nat_sum n (i ↦ true_count n (c i)) by arithmetic_sum_fin n (i ↦ true_count n (c i)) ∎

def two_subsets_pair_count (n : Nat) (hE : IsFinite (TwoSubsets (Fin n))) (b : Fin n → Fin n → Bool)
  : Id Nat (finite_true_count (TwoSubsets (Fin n)) hE (d ↦ b (two_subset_min n d .fst) (two_subset_max n d .fst)))
      (fin_nat_sum n (i ↦ true_count n (j ↦ bool_and (fin_lt n i j) (b i j))))
  ≔ let hO : IsFinite (FinOrderedPairs n) ≔ finite_of_equiv (FinOrderedPairs n) (TwoSubsets (Fin n))
      (canonical_inverse_equiv (TwoSubsets (Fin n)) (FinOrderedPairs n) (two_subsets_pairs_equiv n)) hE in
    concat Nat (finite_true_count (TwoSubsets (Fin n)) hE (d ↦ b (two_subset_min n d .fst) (two_subset_max n d .fst)))
      (finite_true_count (FinOrderedPairs n) hO (u ↦ b (u .fst .fst) (u .fst .snd)))
      (fin_nat_sum n (i ↦ true_count n (j ↦ bool_and (fin_lt n i j) (b i j))))
      (finite_true_count_transfer (TwoSubsets (Fin n)) (FinOrderedPairs n) hE hO (two_subsets_pairs_equiv n)
        (u ↦ b (u .fst .fst) (u .fst .snd)))
      (ordered_pairs_true_count n b hO)
