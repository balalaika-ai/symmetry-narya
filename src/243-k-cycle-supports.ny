export "242-cycle-structures-count"

def remainder_is_finite (m : Nat) : IsFinite (Remainder m)
  ≔ finite_from_equiv (Remainder m) m (canonical_inverse_equiv (Fin m) (Remainder m) (fin_book_below_equiv m))

def remainder_fin_path (m : Nat) : Id Type (Remainder m) (Fin m)
  ≔ ua (Remainder m) (Fin m) (canonical_inverse_equiv (Fin m) (Remainder m) (fin_book_below_equiv m))

def one_not_multiple (j : Nat) (w : Multiples (suc. (suc. j)) (pos. (suc. zero.)) .fst) : Empty
  ≔ nat_encode (suc. j) zero. (refl nat_pred (nat_divides_one (suc. (suc. j))
      (mere_rec (MultipleWitness (suc. (suc. j)) (pos. (suc. zero.))) (NatDivides (suc. (suc. j)) (suc. zero.))
        (nat_divides_prop (suc. (suc. j)) (suc. zero.)) (multiple_nat_divides (suc. (suc. j)) (suc. zero.)) w)))

{` A cycle with k ≥ 2 elements has no fixed points. `}
def finite_cycle_moves (c : Cycles) (j : Nat) (h : Mere (Id Type (c .fst .fst .fst) (Fin (suc. (suc. j)))))
  (x : c .fst .fst .fst) : Not (Id (c .fst .fst .fst) (c .fst .snd .map x) x)
  ≔ p ↦ one_not_multiple j
      (transport (Subtypes Int) (H ↦ H (pos. (suc. zero.)) .fst) (CyclePeriods c) (Multiples (suc. (suc. j)))
        (finite_cycle_periods_multiples c (suc. j) h)
        (cycle_period_from_point (c .fst .fst .fst) (c .fst .fst .snd) (c .fst .snd) (c .snd) x (pos. (suc. zero.)) p))

def modular_successor_moves (j : Nat) (i : Remainder (suc. (suc. j)))
  : Not (Id (Remainder (suc. (suc. j))) (modular_successor (suc. j) i) i)
  ≔ finite_cycle_moves (finite_standard_cycle (suc. j)) j
      (mere (Id Type (Remainder (suc. (suc. j))) (Fin (suc. (suc. j)))) (remainder_fin_path (suc. (suc. j)))) i

{` The book's k-cycle (a_1 ... a_k), k = j+2: pairwise distinct entries,
   given as an injective a : Z/k → A with a_1 = a(0); a_i ↦ a_{i+1},
   a_k ↦ a_1, and every other element is left untouched. `}
def KCycleEnumeration (A : Type) (j : Nat) (σ : Equiv A A) : Type
  ≔ Σ (Remainder (suc. (suc. j)) → A) (a ↦ Product (PathReflecting (Remainder (suc. (suc. j))) A a)
      (Product ((i : Remainder (suc. (suc. j))) → Id A (σ .map (a i)) (a (modular_successor (suc. j) i)))
        ((x : A) → ((i : Remainder (suc. (suc. j))) → Not (Id A x (a i))) → Id A (σ .map x) x)))

def IsKCycle (A : Type) (j : Nat) (σ : Equiv A A) : Type ≔ Mere (KCycleEnumeration A j σ)
def KCyclePermutations (A : Type) (j : Nat) : Type ≔ Σ (Equiv A A) (IsKCycle A j)

def MovedIff (A : Type) (σ : Equiv A A) (Q : Subtypes A) : Type
  ≔ Product ((x : A) → Q x .fst → MovedPoint A σ x) ((x : A) → MovedPoint A σ x → Q x .fst)

def moved_iff_of_path (A : Type) (σ : Equiv A A) (Q : Subtypes A) (p : Id (Subtypes A) Q (permutation_support A σ))
  : MovedIff A σ Q
  ≔ (x q ↦ transport (Subtypes A) (H ↦ H x .fst) Q (permutation_support A σ) p q,
     x m ↦ transport (Subtypes A) (H ↦ H x .fst) (permutation_support A σ) Q
       (inverse (Subtypes A) Q (permutation_support A σ) p) m)

def moved_preimage_moved (A : Type) (σ : Equiv A A) (x : A) (m : MovedPoint A σ x)
  : MovedPoint A σ (equiv_inverse_map A A σ x)
  ≔ p ↦ let y ≔ equiv_inverse_map A A σ x in
    m (concat A (σ .map x) (σ .map y) x
      (refl (σ .map) (concat A x (σ .map y) y (inverse A (σ .map y) x (equiv_counit A A σ x)) p))
      (equiv_counit A A σ x))

def subtype_carrier_set (A : Type) (hA : isSet A) (Q : Subtypes A) : isSet (SubtypeCarrier A Q)
  ≔ sigma_set A (x ↦ Q x .fst) hA (x ↦ prop_is_set (Q x .fst) (Q x .snd))

def moved_restriction (A : Type) (σ : Equiv A A) (Q : Subtypes A) (iff : MovedIff A σ Q)
  : Equiv (SubtypeCarrier A Q) (SubtypeCarrier A Q)
  ≔ subtype_induced_equiv A A σ (x ↦ Q x .fst) (x ↦ Q x .fst) (x ↦ Q x .snd) (x ↦ Q x .snd)
      (x q ↦ iff .snd (σ .map x) (moved_image_moved A σ x (iff .fst x q)))
      (x q ↦ iff .snd (equiv_inverse_map A A σ x) (moved_preimage_moved A σ x (iff .fst x q)))

{` The entries of a k-cycle are exactly its moved points. `}
def enumeration_moved (A : Type) (j : Nat) (σ : Equiv A A) (E : KCycleEnumeration A j σ) (i : Remainder (suc. (suc. j)))
  : MovedPoint A σ (E .fst i)
  ≔ p ↦ modular_successor_moves j i
      (E .snd .fst (modular_successor (suc. j) i) i
        (concat A (E .fst (modular_successor (suc. j) i)) (σ .map (E .fst i)) (E .fst i)
          (inverse A (σ .map (E .fst i)) (E .fst (modular_successor (suc. j) i)) (E .snd .snd .fst i)) p))

def enumeration_to_moved (A : Type) (hA : isSet A) (d : DecidableEquality A) (j : Nat) (σ : Equiv A A)
  (E : KCycleEnumeration A j σ) (Q : Subtypes A) (iff : MovedIff A σ Q)
  : Equiv (Remainder (suc. (suc. j))) (SubtypeCarrier A Q)
  ≔ let R ≔ Remainder (suc. (suc. j)) in let C ≔ SubtypeCarrier A Q in
    let f ≔ ((i ↦ (E .fst i, iff .snd (E .fst i) (enumeration_moved A j σ E i))) : R → C) in
    set_bijection_equiv R C (subtype_carrier_set A hA Q) f
      (i i' p ↦ E .snd .fst i i' (refl ((c ↦ c .fst) : C → A) p))
      (c ↦ let P ≔ ((i ↦ Id A (c .fst) (E .fst i)) : R → Type) in
        match finite_quantifiers R (remainder_is_finite (suc. (suc. j))) P (i ↦ hA (c .fst) (E .fst i))
          (i ↦ d (c .fst) (E .fst i)) .snd [
        | inl. m ↦ mere_rec (Σ R P) (Mere (BookFiber R C f c)) (mere_isprop (BookFiber R C f c))
            (w ↦ mere (BookFiber R C f c) (w .fst,
              subtype_equal A (x ↦ Q x .fst) (x ↦ Q x .snd) c (f (w .fst)) (w .snd))) m
        | inr. no ↦ absurd (Mere (BookFiber R C f c))
            (iff .fst (c .fst) (c .snd)
              (E .snd .snd .snd (c .fst) (i p ↦ no (mere (Σ R P) (i, p))))) ])

def enumeration_restriction_commutes (A : Type) (hA : isSet A) (d : DecidableEquality A) (j : Nat) (σ : Equiv A A)
  (E : KCycleEnumeration A j σ) (Q : Subtypes A) (iff : MovedIff A σ Q)
  : Commutes (Remainder (suc. (suc. j))) (SubtypeCarrier A Q) (modular_successor_equiv (suc. j))
      (moved_restriction A σ Q iff) (enumeration_to_moved A hA d j σ E Q iff .map)
  ≔ i ↦ subtype_equal A (x ↦ Q x .fst) (x ↦ Q x .snd)
      (enumeration_to_moved A hA d j σ E Q iff .map (modular_successor (suc. j) i))
      (moved_restriction A σ Q iff .map (enumeration_to_moved A hA d j σ E Q iff .map i))
      (inverse A (σ .map (E .fst i)) (E .fst (modular_successor (suc. j) i)) (E .snd .snd .fst i))

def moved_restriction_cyclic (A : Type) (hA : isSet A) (d : DecidableEquality A) (j : Nat) (σ : Equiv A A)
  (isk : IsKCycle A j σ) (Q : Subtypes A) (iff : MovedIff A σ Q)
  : Cyclic (SubtypeCarrier A Q) (moved_restriction A σ Q iff)
  ≔ mere_rec (KCycleEnumeration A j σ) (Cyclic (SubtypeCarrier A Q) (moved_restriction A σ Q iff))
      (cyclic_prop (SubtypeCarrier A Q) (moved_restriction A σ Q iff))
      (E ↦ cyclic_transfer (Remainder (suc. (suc. j))) (SubtypeCarrier A Q) (modular_successor_equiv (suc. j))
        (moved_restriction A σ Q iff) (enumeration_to_moved A hA d j σ E Q iff)
        (enumeration_restriction_commutes A hA d j σ E Q iff) (modular_successor_cyclic (suc. j)))
      isk

def moved_size (A : Type) (hA : isSet A) (d : DecidableEquality A) (j : Nat) (σ : Equiv A A)
  (isk : IsKCycle A j σ) (Q : Subtypes A) (iff : MovedIff A σ Q)
  : Mere (Id Type (SubtypeCarrier A Q) (Fin (suc. (suc. j))))
  ≔ trunc_map native_truncation (KCycleEnumeration A j σ) (Id Type (SubtypeCarrier A Q) (Fin (suc. (suc. j))))
      (E ↦ concat Type (SubtypeCarrier A Q) (Remainder (suc. (suc. j))) (Fin (suc. (suc. j)))
        (inverse Type (Remainder (suc. (suc. j))) (SubtypeCarrier A Q)
          (ua (Remainder (suc. (suc. j))) (SubtypeCarrier A Q) (enumeration_to_moved A hA d j σ E Q iff)))
        (remainder_fin_path (suc. (suc. j)))) isk

{` Extension of a permutation of a decidable subset by the identity. `}
def dep_branch (A P : Type) (d : Decidable P) (yes : P → A) (no : A) : A
  ≔ match d [ inl. p ↦ yes p | inr. _ ↦ no ]

def dep_branch_elim (A P : Type) (d : Decidable P) (yes : P → A) (no z : A)
  (hy : (p : P) → Id A (yes p) z) (hn : Not P → Id A no z) : Id A (dep_branch A P d yes no) z
  ≔ match d [ inl. p ↦ hy p | inr. n ↦ hn n ]

def subset_extension_map (A : Type) (P : Subtypes A) (dP : (x : A) → Decidable (P x .fst))
  (f : SubtypeCarrier A P → SubtypeCarrier A P) (x : A) : A
  ≔ dep_branch A (P x .fst) (dP x) (p ↦ f (x, p) .fst) x

def subset_extension_in (A : Type) (P : Subtypes A) (dP : (x : A) → Decidable (P x .fst))
  (f : SubtypeCarrier A P → SubtypeCarrier A P) (x : A) (p : P x .fst)
  : Id A (subset_extension_map A P dP f x) (f (x, p) .fst)
  ≔ dep_branch_elim A (P x .fst) (dP x) (q ↦ f (x, q) .fst) x (f (x, p) .fst)
      (q ↦ refl ((r ↦ f (x, r) .fst) : P x .fst → A) (P x .snd q p))
      (n ↦ absurd (Id A x (f (x, p) .fst)) (n p))

def subset_extension_out (A : Type) (P : Subtypes A) (dP : (x : A) → Decidable (P x .fst))
  (f : SubtypeCarrier A P → SubtypeCarrier A P) (x : A) (n : Not (P x .fst))
  : Id A (subset_extension_map A P dP f x) x
  ≔ dep_branch_elim A (P x .fst) (dP x) (q ↦ f (x, q) .fst) x x
      (q ↦ absurd (Id A (f (x, q) .fst) x) (n q)) (_ ↦ refl x)

def subset_extension_retraction (A : Type) (P : Subtypes A) (dP : (x : A) → Decidable (P x .fst))
  (f g : SubtypeCarrier A P → SubtypeCarrier A P) (h : (c : SubtypeCarrier A P) → Id (SubtypeCarrier A P) (g (f c)) c) (x : A)
  : Id A (subset_extension_map A P dP g (subset_extension_map A P dP f x)) x
  ≔ let ext ≔ subset_extension_map A P dP in
    match dP x [
    | inl. p ↦ calc
        ext g (ext f x) = ext g (f (x, p) .fst) by refl (ext g) (subset_extension_in A P dP f x p)
        = g (f (x, p)) .fst by subset_extension_in A P dP g (f (x, p) .fst) (f (x, p) .snd)
        = x by refl ((c ↦ c .fst) : SubtypeCarrier A P → A) (h (x, p)) ∎
    | inr. n ↦ calc
        ext g (ext f x) = ext g x by refl (ext g) (subset_extension_out A P dP f x n)
        = x by subset_extension_out A P dP g x n ∎ ]

def subset_extension (A : Type) (P : Subtypes A) (dP : (x : A) → Decidable (P x .fst))
  (t : Equiv (SubtypeCarrier A P) (SubtypeCarrier A P)) : Equiv A A
  ≔ let C ≔ SubtypeCarrier A P in
    quasi_inverse_equiv A A (subset_extension_map A P dP (t .map))
      (subset_extension_map A P dP (equiv_inverse_map C C t))
      (subset_extension_retraction A P dP (t .map) (equiv_inverse_map C C t) (equiv_retraction C C t))
      (subset_extension_retraction A P dP (equiv_inverse_map C C t) (t .map) (equiv_counit C C t))
