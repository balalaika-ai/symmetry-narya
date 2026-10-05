export "453-sign-mu"
export "406-symmetric-group-three"

{` Chapter 4, sec:sign-homomorphism: two-element subsets E(A), local and sign
   orderings (def:sign-ordering), the standard order of Fin n and the order
   identification of each two-element subset of Fin n with Fin 2. `}

{` E(A): the two-element subsets of A (KSubsets of module 178). `}
def TwoSubsets (A : Type) : Type ≔ KSubsets A two

def two_subset_carrier_set (A : Type) (hA : isSet A) (e : TwoSubsets A) : isSet (SubtypeCarrier A (e .fst))
  ≔ sigma_set A (t ↦ e .fst t .fst) hA (t ↦ prop_is_set (e .fst t .fst) (e .fst t .snd))

def two_subset_two_element (A : Type) (e : TwoSubsets A) : TwoElement (SubtypeCarrier A (e .fst))
  ≔ trunc_map native_truncation (Id Type (SubtypeCarrier A (e .fst)) (Fin two)) (Id Type (Fin two) (SubtypeCarrier A (e .fst)))
      (inverse Type (SubtypeCarrier A (e .fst)) (Fin two)) (e .snd)

{` P : E(A) → BΣ_2, a two-element subset as a two-element set. `}
def two_subset_bsigma (A : Type) (hA : isSet A) (e : TwoSubsets A) : BookFiniteSetsAt two
  ≔ two_element_bsigma_two (SubtypeCarrier A (e .fst), two_subset_carrier_set A hA e) (two_subset_two_element A e)

{` def:sign-ordering. A local ordering of A is an element of Π_{e:E(A)} P(e);
   a sign ordering is an element of the quotient by the parity relation. `}
def LocalOrderings (A : Type) (hA : isSet A) : Type ≔ LocalSections (TwoSubsets A) (two_subset_bsigma A hA)

def SignOrderings (A : Type) (hA : isSet A) (fA : IsFinite A) : Type
  ≔ ParityQuotient (TwoSubsets A) (ksubsets_finite A fA two) (two_subset_bsigma A hA)

def local_ordering_unfold (A : Type) (hA : isSet A)
  : Id Type (LocalOrderings A hA) ((e : TwoSubsets A) → SubtypeCarrier A (e .fst))
  ≔ refl (LocalOrderings A hA)

{` The pair subset {i, j} of a set with i ≠ j. `}
def pair_predicate (A : Type) (hA : isSet A) (i j : A) (nij : Not (Id A i j)) : Subtypes A
  ≔ x ↦ (Sum (Id A x i) (Id A x j),
      disjoint_sum_prop (Id A x i) (Id A x j) (hA x i) (hA x j)
        (p q ↦ nij (concat A i x j (inverse A x i p) q)))

def pair_carrier_to (A : Type) (hA : isSet A) (i j : A) (nij : Not (Id A i j))
  (u : SubtypeCarrier A (pair_predicate A hA i j nij)) : Fin two
  ≔ match u .snd [ inl. _ ↦ inr. star. | inr. _ ↦ inl. (inr. star.) ]

def pair_carrier_from (A : Type) (hA : isSet A) (i j : A) (nij : Not (Id A i j))
  : Fin two → SubtypeCarrier A (pair_predicate A hA i j nij)
  ≔ [ inr. _ ↦ (i, inl. (refl i)) | inl. (inr. _) ↦ (j, inr. (refl j)) | inl. (inl. e) ↦ match e [] ]

def pair_carrier_path (A : Type) (hA : isSet A) (i j : A) (nij : Not (Id A i j))
  (u v : SubtypeCarrier A (pair_predicate A hA i j nij)) (p : Id A (u .fst) (v .fst))
  : Id (SubtypeCarrier A (pair_predicate A hA i j nij)) u v
  ≔ subtype_equal A (x ↦ pair_predicate A hA i j nij x .fst) (x ↦ pair_predicate A hA i j nij x .snd) u v p

def pair_carrier_roundtrip (A : Type) (hA : isSet A) (i j : A) (nij : Not (Id A i j))
  (x : A) (m : Sum (Id A x i) (Id A x j))
  : Id (SubtypeCarrier A (pair_predicate A hA i j nij))
      (pair_carrier_from A hA i j nij (pair_carrier_to A hA i j nij (x, m))) (x, m)
  ≔ match m [
  | inl. p ↦ pair_carrier_path A hA i j nij (i, inl. (refl i)) (x, inl. p) (inverse A x i p)
  | inr. q ↦ pair_carrier_path A hA i j nij (j, inr. (refl j)) (x, inr. q) (inverse A x j q) ]

def pair_carrier_equiv (A : Type) (hA : isSet A) (i j : A) (nij : Not (Id A i j))
  : Equiv (SubtypeCarrier A (pair_predicate A hA i j nij)) (Fin two)
  ≔ quasi_inverse_equiv (SubtypeCarrier A (pair_predicate A hA i j nij)) (Fin two)
      (pair_carrier_to A hA i j nij) (pair_carrier_from A hA i j nij)
      (u ↦ pair_carrier_roundtrip A hA i j nij (u .fst) (u .snd))
      [ inr. u ↦ inr. (unit_prop star. u)
      | inl. (inr. u) ↦ inl. (inr. (unit_prop star. u))
      | inl. (inl. e) ↦ match e [] ]

def pair_subset (A : Type) (hA : isSet A) (i j : A) (nij : Not (Id A i j)) : TwoSubsets A
  ≔ (pair_predicate A hA i j nij,
      mere (Id Type (SubtypeCarrier A (pair_predicate A hA i j nij)) (Fin two))
        (ua (SubtypeCarrier A (pair_predicate A hA i j nij)) (Fin two) (pair_carrier_equiv A hA i j nij)))

{` A set with two distinct points and decidable equality has a two-element
   subset; so E(A) is inhabited when A has at least two elements. `}
def two_subsets_fin_inhabited (m : Nat) : TwoSubsets (Fin (suc. (suc. m)))
  ≔ pair_subset (Fin (suc. (suc. m))) (fin_set (suc. (suc. m))) (inr. star.) (inl. (inr. star.))
      (p ↦ sum_encode (Fin (suc. m)) Unit (inr. star.) (inl. (inr. star.)) p)

{` The standard total order 0 < 1 < ... < n−1 on Fin n, as a Boolean test;
   0 = inr star and k+1 = inl k as in def:finiteset. `}
def fin_lt (n : Nat) : Fin n → Fin n → Bool
  ≔ match n [
  | zero. ↦ x _ ↦ match x []
  | suc. m ↦ x y ↦ match x, y [
    | inr. _, inr. _ ↦ false.
    | inr. _, inl. _ ↦ true.
    | inl. _, inr. _ ↦ false.
    | inl. a, inl. b ↦ fin_lt m a b ] ]

def fin_lt_irrefl (n : Nat) (i : Fin n) : Id Bool (fin_lt n i i) false.
  ≔ match n [
  | zero. ↦ match i []
  | suc. m ↦ match i [ inr. _ ↦ refl (false. : Bool) | inl. a ↦ fin_lt_irrefl m a ] ]

def fin_lt_flip (n : Nat) (i j : Fin n) (nij : Not (Id (Fin n) i j))
  : Id Bool (fin_lt n j i) (bool_not (fin_lt n i j))
  ≔ match n [
  | zero. ↦ match i []
  | suc. m ↦ match i, j [
    | inr. u, inr. v ↦ match nij (inr. (unit_prop u v)) []
    | inr. _, inl. _ ↦ refl (false. : Bool)
    | inl. _, inr. _ ↦ refl (true. : Bool)
    | inl. a, inl. b ↦ fin_lt_flip m a b (p ↦ nij (inl. p)) ] ]

def fin_lt_asym (n : Nat) (i j : Fin n) (h : Id Bool (fin_lt n i j) true.) : Id Bool (fin_lt n j i) false.
  ≔ match n [
  | zero. ↦ match i []
  | suc. m ↦ match i, j [
    | inr. _, inr. _ ↦ match bool_encode false. true. h []
    | inr. _, inl. _ ↦ refl (false. : Bool)
    | inl. _, inr. _ ↦ match bool_encode false. true. h []
    | inl. a, inl. b ↦ fin_lt_asym m a b h ] ]

def fin_lt_ne (n : Nat) (i j : Fin n) (h : Id Bool (fin_lt n i j) true.) : Not (Id (Fin n) i j)
  ≔ p ↦ bool_encode false. true.
      (calc (false. : Bool) = fin_lt n j j by inverse Bool (fin_lt n j j) false. (fin_lt_irrefl n j)
        = fin_lt n i j by refl ((x ↦ fin_lt n x j) : Fin n → Bool) (inverse (Fin n) i j p)
        = true. by h ∎)

def fin_lt_trans (n : Nat) (i j k : Fin n) (h1 : Id Bool (fin_lt n i j) true.) (h2 : Id Bool (fin_lt n j k) true.)
  : Id Bool (fin_lt n i k) true.
  ≔ match n [
  | zero. ↦ match i []
  | suc. m ↦ match i, j, k [
    | inr. _, inr. _, _ ↦ match bool_encode false. true. h1 []
    | inr. _, inl. _, inr. _ ↦ match bool_encode false. true. h2 []
    | inr. _, inl. _, inl. _ ↦ refl (true. : Bool)
    | inl. _, inr. _, _ ↦ match bool_encode false. true. h1 []
    | inl. _, inl. _, inr. _ ↦ match bool_encode false. true. h2 []
    | inl. a, inl. b, inl. c ↦ fin_lt_trans m a b c h1 h2 ] ]

{` The least element of a two-element subset of Fin n: the point c whose
   other point lies above it. Uniquely determined, hence obtained from the
   mere identification with Fin 2. `}
def two_subset_carrier (n : Nat) (e : TwoSubsets (Fin n)) : Type ≔ SubtypeCarrier (Fin n) (e .fst)

def two_subset_other (n : Nat) (e : TwoSubsets (Fin n)) (c : two_subset_carrier n e) : two_subset_carrier n e
  ≔ two_element_other (two_subset_carrier n e) (two_subset_two_element (Fin n) e) c

def IsLeastOfPair (n : Nat) (e : TwoSubsets (Fin n)) (c : two_subset_carrier n e) : Type
  ≔ Id Bool (fin_lt n (c .fst) (two_subset_other n e c .fst)) true.

def carrier_fst_ne (n : Nat) (e : TwoSubsets (Fin n)) (c d : two_subset_carrier n e)
  (n0 : Not (Id (two_subset_carrier n e) c d)) : Not (Id (Fin n) (c .fst) (d .fst))
  ≔ p ↦ n0 (subtype_equal (Fin n) (x ↦ e .fst x .fst) (x ↦ e .fst x .snd) c d p)

def two_subset_least_contra (n : Nat) (e : TwoSubsets (Fin n)) (u v : Σ (two_subset_carrier n e) (IsLeastOfPair n e))
  (nuv : Not (Id (two_subset_carrier n e) (u .fst) (v .fst))) : Empty
  ≔ let C ≔ two_subset_carrier n e in let h ≔ two_subset_two_element (Fin n) e in
    let ov : Id C (u .fst) (two_subset_other n e (v .fst))
      ≔ two_element_other_unique C h (v .fst) (u .fst) nuv in
    let ou : Id C (v .fst) (two_subset_other n e (u .fst))
      ≔ two_element_other_unique C h (u .fst) (v .fst) (r ↦ nuv (inverse C (v .fst) (u .fst) r)) in
    let uv : Id Bool (fin_lt n (u .fst .fst) (v .fst .fst)) true.
      ≔ concat Bool (fin_lt n (u .fst .fst) (v .fst .fst)) (fin_lt n (u .fst .fst) (two_subset_other n e (u .fst) .fst)) true.
          (refl ((c ↦ fin_lt n (u .fst .fst) (c .fst)) : C → Bool) ou) (u .snd) in
    let vu : Id Bool (fin_lt n (v .fst .fst) (u .fst .fst)) true.
      ≔ concat Bool (fin_lt n (v .fst .fst) (u .fst .fst)) (fin_lt n (v .fst .fst) (two_subset_other n e (v .fst) .fst)) true.
          (refl ((c ↦ fin_lt n (v .fst .fst) (c .fst)) : C → Bool) ov) (v .snd) in
    bool_false_not_true (fin_lt n (v .fst .fst) (u .fst .fst)) (fin_lt_asym n (u .fst .fst) (v .fst .fst) uv) vu

def two_subset_least_fst (n : Nat) (e : TwoSubsets (Fin n)) (u v : Σ (two_subset_carrier n e) (IsLeastOfPair n e))
  (d : Decidable (Id (two_subset_carrier n e) (u .fst) (v .fst))) : Id (two_subset_carrier n e) (u .fst) (v .fst)
  ≔ match d [ inl. p ↦ p | inr. nuv ↦ match two_subset_least_contra n e u v nuv [] ]

def two_subset_least_prop (n : Nat) (e : TwoSubsets (Fin n)) : isProp (Σ (two_subset_carrier n e) (IsLeastOfPair n e))
  ≔ u v ↦ subtype_equal (two_subset_carrier n e) (IsLeastOfPair n e)
      (c ↦ bool_set (fin_lt n (c .fst) (two_subset_other n e c .fst)) true.) u v
      (two_subset_least_fst n e u v
        (two_element_decidable_equality (two_subset_carrier n e) (two_subset_two_element (Fin n) e) (u .fst) (v .fst)))

def two_subset_least_step (n : Nat) (e : TwoSubsets (Fin n)) (c : two_subset_carrier n e) (b : Bool)
  (q : Id Bool (fin_lt n (c .fst) (two_subset_other n e c .fst)) b)
  : Σ (two_subset_carrier n e) (IsLeastOfPair n e)
  ≔ let C ≔ two_subset_carrier n e in let h ≔ two_subset_two_element (Fin n) e in
    let oc ≔ two_subset_other n e c in
    match b [
    | true. ↦ (c, q)
    | false. ↦ (oc,
        calc fin_lt n (oc .fst) (two_subset_other n e oc .fst)
          = fin_lt n (oc .fst) (c .fst) by refl ((d ↦ fin_lt n (oc .fst) (d .fst)) : C → Bool) (two_element_other_other C h c)
          = bool_not (fin_lt n (c .fst) (oc .fst))
            by fin_lt_flip n (c .fst) (oc .fst)
              (carrier_fst_ne n e c oc (p ↦ two_element_other_ne C h c (inverse C c oc p)))
          = true. by refl bool_not q ∎) ]

def two_subset_least (n : Nat) (e : TwoSubsets (Fin n)) : Σ (two_subset_carrier n e) (IsLeastOfPair n e)
  ≔ two_element_point_elim (two_subset_carrier n e) (two_subset_two_element (Fin n) e)
      (Σ (two_subset_carrier n e) (IsLeastOfPair n e)) (two_subset_least_prop n e)
      (c ↦ two_subset_least_step n e c (fin_lt n (c .fst) (two_subset_other n e c .fst))
        (refl (fin_lt n (c .fst) (two_subset_other n e c .fst))))

def two_subset_min (n : Nat) (e : TwoSubsets (Fin n)) : two_subset_carrier n e ≔ two_subset_least n e .fst

def two_subset_max (n : Nat) (e : TwoSubsets (Fin n)) : two_subset_carrier n e ≔ two_subset_other n e (two_subset_min n e)

def two_subset_min_lt_max (n : Nat) (e : TwoSubsets (Fin n))
  : Id Bool (fin_lt n (two_subset_min n e .fst) (two_subset_max n e .fst)) true.
  ≔ two_subset_least n e .snd

{` Any point of the carrier lying below the other point is the minimum. `}
def two_subset_min_unique (n : Nat) (e : TwoSubsets (Fin n)) (c : two_subset_carrier n e) (q : IsLeastOfPair n e c)
  : Id (two_subset_carrier n e) c (two_subset_min n e)
  ≔ refl ((u ↦ u .fst) : Σ (two_subset_carrier n e) (IsLeastOfPair n e) → two_subset_carrier n e)
      (two_subset_least_prop n e (c, q) (two_subset_least n e))

{` The enumeration Fin 2 ≃ T of a two-element type sending 0 to a chosen
   point c and 1 to the other point. `}
def two_pointed_enum (A : Type) (h : TwoElement A) (c : A) : Fin two → A
  ≔ [ inr. _ ↦ c | inl. (inr. _) ↦ two_element_other A h c | inl. (inl. e) ↦ match e [] ]

def two_pointed_index (A : Type) (c x : A) (d : Decidable (Id A x c)) : Fin two
  ≔ match d [ inl. _ ↦ inr. star. | inr. _ ↦ inl. (inr. star.) ]

def two_pointed_index_enum (A : Type) (h : TwoElement A) (c x : A) (d : Decidable (Id A x c))
  : Id A (two_pointed_enum A h c (two_pointed_index A c x d)) x
  ≔ match d [
  | inl. p ↦ inverse A x c p
  | inr. n ↦ inverse A x (two_element_other A h c) (two_element_other_unique A h c x n) ]

def two_pointed_enum_index (A : Type) (h : TwoElement A) (c : A) (k : Fin two)
  (d : Decidable (Id A (two_pointed_enum A h c k) c))
  : Id (Fin two) (two_pointed_index A c (two_pointed_enum A h c k) d) k
  ≔ match k [
  | inr. u ↦ match d [
    | inl. _ ↦ inr. (unit_prop star. u)
    | inr. n ↦ match n (refl c) [] ]
  | inl. (inr. u) ↦ match d [
    | inl. p ↦ match two_element_other_ne A h c p []
    | inr. _ ↦ inl. (inr. (unit_prop star. u)) ]
  | inl. (inl. e) ↦ match e [] ]

def two_pointed_equiv (A : Type) (h : TwoElement A) (c : A) : Equiv (Fin two) A
  ≔ let d ≔ two_element_decidable_equality A h in
    quasi_inverse_equiv (Fin two) A (two_pointed_enum A h c) (x ↦ two_pointed_index A c x (d x c))
      (k ↦ two_pointed_enum_index A h c k (d (two_pointed_enum A h c k) c))
      (x ↦ two_pointed_index_enum A h c x (d x c))

def fin_two_one_ne_zero (u : Unit) (p : Id (Fin two) (inl. (inr. u)) (inr. star.)) : Empty
  ≔ sum_encode (Fin (suc. zero.)) Unit (inl. (inr. u)) (inr. star.) p

def two_choice_ordering_one (A : Type) (h : TwoElement A) (o : Equiv (Fin two) A) (u : Unit)
  : Id A (two_element_other A h (o .map (inr. star.))) (o .map (inl. (inr. u)))
  ≔ inverse A (o .map (inl. (inr. u))) (two_element_other A h (o .map (inr. star.)))
      (two_element_other_unique A h (o .map (inr. star.)) (o .map (inl. (inr. u)))
        (p ↦ fin_two_one_ne_zero u (equiv_injective_path (Fin two) A o (inl. (inr. u)) (inr. star.) p)))

{` Intro paragraph: choosing an element of a two-element set is equivalent to
   ordering it (an enumeration Fin 2 ≃ T, the chosen element first). `}
def two_choice_ordering_equiv (A : Type) (h : TwoElement A) : Equiv A (Equiv (Fin two) A)
  ≔ quasi_inverse_equiv A (Equiv (Fin two) A) (two_pointed_equiv A h) (o ↦ o .map (inr. star.))
      (c ↦ refl c)
      (o ↦ equiv_homotopy (Fin two) A (two_pointed_equiv A h (o .map (inr. star.))) o
        [ inr. u ↦ refl (o .map) (inr. (unit_prop star. u) : Id (Fin two) (inr. star.) (inr. u))
        | inl. (inr. u) ↦ two_choice_ordering_one A h o u
        | inl. (inl. e) ↦ match e [] ])

{` The standard local ordering of Fin n: each two-element subset is ordered
   by the total order (smaller element first), and the identification of
   each two-element subset with the standard two-element set. `}
def standard_local_ordering (n : Nat) : LocalOrderings (Fin n) (fin_set n) ≔ e ↦ two_subset_min n e

def standard_order_equiv (n : Nat) (e : TwoSubsets (Fin n)) : Equiv (Fin two) (two_subset_carrier n e)
  ≔ two_pointed_equiv (two_subset_carrier n e) (two_subset_two_element (Fin n) e) (two_subset_min n e)

def standard_order_path (n : Nat) (e : TwoSubsets (Fin n))
  : Id (BookFiniteSetsAt two) (shape sign_sigma_two) (two_subset_bsigma (Fin n) (fin_set n) e)
  ≔ component_path SetTypes (Fin two, fin_set two) (shape sign_sigma_two) (two_subset_bsigma (Fin n) (fin_set n) e)
      (set_types_path (Fin two, fin_set two) (two_subset_carrier n e, two_subset_carrier_set (Fin n) (fin_set n) e)
        (standard_order_equiv n e))

def standard_order_family_path (n : Nat)
  : Id (TwoSubsets (Fin n) → BookFiniteSetsAt two) (_ ↦ shape sign_sigma_two) (two_subset_bsigma (Fin n) (fin_set n))
  ≔ funext (TwoSubsets (Fin n)) (_ ↦ BookFiniteSetsAt two) (_ ↦ shape sign_sigma_two) (two_subset_bsigma (Fin n) (fin_set n))
      (standard_order_path n)

{` Litmus: in the two-element subset {0, 1} of Fin 3 the minimum is 0. `}
def fin_three_pair_zero_one : TwoSubsets (Fin three) ≔ two_subsets_fin_inhabited (suc. zero.)

def fin_three_zero_ne_one (p : Id (Fin three) (inr. star.) (inl. (inr. star.))) : Empty
  ≔ sum_encode (Fin two) Unit (inr. star.) (inl. (inr. star.)) p

def fin3_pair01_zero : two_subset_carrier three fin_three_pair_zero_one
  ≔ (inr. star., inl. (refl (inr. star. : Fin three)))

def fin3_pair01_one : two_subset_carrier three fin_three_pair_zero_one
  ≔ (inl. (inr. star.), inr. (refl (inl. (inr. star.) : Fin three)))

def fin3_pair01_distinct (p : Id (two_subset_carrier three fin_three_pair_zero_one) fin3_pair01_one fin3_pair01_zero) : Empty
  ≔ fin_three_zero_ne_one (inverse (Fin three) (inl. (inr. star.)) (inr. star.)
      (refl ((u ↦ u .fst) : two_subset_carrier three fin_three_pair_zero_one → Fin three) p))

def fin3_pair01_other : Id (two_subset_carrier three fin_three_pair_zero_one) fin3_pair01_one
    (two_subset_other three fin_three_pair_zero_one fin3_pair01_zero)
  ≔ two_element_other_unique (two_subset_carrier three fin_three_pair_zero_one) (two_subset_two_element (Fin three) fin_three_pair_zero_one)
      fin3_pair01_zero fin3_pair01_one fin3_pair01_distinct

def fin_three_pair_min_zero : Id (Fin three) (two_subset_min three fin_three_pair_zero_one .fst) (inr. star.)
  ≔ refl ((u ↦ u .fst) : two_subset_carrier three fin_three_pair_zero_one → Fin three)
      (inverse (two_subset_carrier three fin_three_pair_zero_one) fin3_pair01_zero (two_subset_min three fin_three_pair_zero_one)
        (two_subset_min_unique three fin_three_pair_zero_one fin3_pair01_zero
          (refl ((u ↦ fin_lt three (inr. star.) (u .fst)) : two_subset_carrier three fin_three_pair_zero_one → Bool)
            (inverse (two_subset_carrier three fin_three_pair_zero_one) fin3_pair01_one
              (two_subset_other three fin_three_pair_zero_one fin3_pair01_zero) fin3_pair01_other))))
