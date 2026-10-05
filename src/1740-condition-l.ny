export "1753-rewriting-closures"
export "287-chapter-two-text-claims"
export "1110-finite-index"
export "565-standard-symmetric-gsets"
export "412-symmetric-group-two"

{` Definition "The condition L(Z,n)" (choicefin.tex:241), on the book's
   concrete subgroups. A subgroup of Σ_n = symmetric_group n is an element
   of Subgroups (symmetric_group n) (def:set-of-subgroups, module 502) with
   underlying group subgroup_group; "finite" is IsFiniteGroup (module 400),
   "proper" is IsProperSubgroup (def:triv-proper-Mono), the index |G : K| = m
   is SubgroupHasIndex G K m (def:finite-index, module 1110: the coset G-set
   of K has m-element fibres). G acts on n through the standard Σ_n-set
   restricted along the inclusion; "without fixed points" means
   GSetFixedPoints (module 563) of that action is empty. The printed sum of
   indices uses H_i for the subgroups called K_i; the K_i are meant. `}

def SymmetricSubgroupAction (n : Nat) (S : Subgroups (symmetric_group n))
  : GSet (subgroup_group (symmetric_group n) S)
  ≔ gset_restrict (subgroup_group (symmetric_group n) S) (symmetric_group n)
      (subgroup_inclusion (symmetric_group n) S) (standard_symmetric_gset n)

def ActsWithoutFixedPoints (n : Nat) (S : Subgroups (symmetric_group n)) : Type
  ≔ Not (GSetFixedPoints (subgroup_group (symmetric_group n) S) (SymmetricSubgroupAction n S))

{` One summand: a proper finite subgroup K of G together with its index. `}
def IndexedProperSubgroup (G : Group) : Type
  ≔ Σ (Subgroups G) (K ↦ Product (IsProperSubgroup G K)
      (Product (IsFiniteGroup (subgroup_group G K)) (Σ Nat (m ↦ SubgroupHasIndex G K m))))

def index_of (G : Group) (K : IndexedProperSubgroup G) : Nat ≔ K .snd .snd .snd .fst

def fin_family_sum (r : Nat) (f : Fin r → Nat) : Nat
  ≔ match r [ zero. ↦ zero. | suc. r ↦ add (fin_family_sum r (j ↦ f (inl. j))) (f (inr. star.)) ]

def ConditionLWitness (Z : Subtypes Nat) (G : Group) : Type
  ≔ Σ Nat (r ↦ Σ (Fin r → IndexedProperSubgroup G) (K ↦ Z (fin_family_sum r (j ↦ index_of G (K j))) .fst))

{` L(Z,n): for every finite subgroup G of Σ_n acting without fixed points
   there are finitely many proper finite subgroups K_1, …, K_r of G with
   |G : K_1| + ⋯ + |G : K_r| ∈ Z. Z is any subset of ℕ (the book takes a
   finite one; finiteness plays no role in the definition). `}
def ConditionL (Z : Subtypes Nat) (n : Nat) : Type
  ≔ (S : Subgroups (symmetric_group n)) → IsFiniteGroup (subgroup_group (symmetric_group n) S)
    → ActsWithoutFixedPoints n S → Mere (ConditionLWitness Z (subgroup_group (symmetric_group n) S))

def condition_l_prop (Z : Subtypes Nat) (n : Nat) : isProp (ConditionL Z n)
  ≔ let G ≔ symmetric_group n in
    pi_prop (Subgroups G)
      (S ↦ IsFiniteGroup (subgroup_group G S) → ActsWithoutFixedPoints n S → Mere (ConditionLWitness Z (subgroup_group G S)))
      (S ↦ pi_prop (IsFiniteGroup (subgroup_group G S))
        (_ ↦ ActsWithoutFixedPoints n S → Mere (ConditionLWitness Z (subgroup_group G S)))
        (_ ↦ pi_prop (ActsWithoutFixedPoints n S) (_ ↦ Mere (ConditionLWitness Z (subgroup_group G S)))
          (_ ↦ mere_isprop (ConditionLWitness Z (subgroup_group G S)))))

{` Litmus checks. `}
def EmptySubsetOfNat : Subtypes Nat ≔ _ ↦ (Empty, empty_prop)

{` L(∅, 1): every symmetry of a one-element set fixes its point, so no
   subgroup of Σ_1 acts without fixed points (fin_one_prop, module 287). `}
def condition_l_one : ConditionL EmptySubsetOfNat (suc. zero.)
  ≔ S _ fpf ↦ absurd (Mere (ConditionLWitness EmptySubsetOfNat (subgroup_group (symmetric_group (suc. zero.)) S)))
      (fpf (inr. star., g ↦ fin_one_prop
        (gset_usym_act (subgroup_group (symmetric_group (suc. zero.)) S) (SymmetricSubgroupAction (suc. zero.) S) g (inr. star.))
        (inr. star.)))

{` The unit type as a set, and the trivial G-set has index 1 (as in module 1113, which this module
   does not import). `}
def condition_l_unit_set_type : SetTypes ≔ (Unit, unit_set)

def condition_l_trivial_gset_index_one (G : Group) : GSetHasIndex G (gset_trivial G condition_l_unit_set_type) (suc. zero.)
  ≔ _ ↦ mere (Id Type Unit (Fin (suc. zero.)))
      (ua Unit (Fin (suc. zero.)) (quasi_inverse_equiv Unit (Fin (suc. zero.)) (_ ↦ inr. star.) (_ ↦ star.)
        (u ↦ match u [ star. ↦ refl (star. : Unit) ])
        (i ↦ match i [ inl. z ↦ match z [] | inr. u ↦ match u [ star. ↦ refl (inr. star. : Fin (suc. zero.)) ] ])))

{` The full subgroup of G as the one-point G-set (its G-set has contractible
   underlying set, so by subgroup_full_of_contractible, module 1021, it is
   group_full_subgroup G). `}
def unit_gset_subgroup (G : Group) : Subgroups G
  ≔ (gset_trivial G condition_l_unit_set_type, star.,
     mere (Σ Unit (x ↦ (y : Unit) → Mere (Σ (USym G) (g ↦ Id Unit x (gset_usym_act G (gset_trivial G condition_l_unit_set_type) g y)))))
       (star., y ↦ mere (Σ (USym G) (g ↦ Id Unit star. (gset_usym_act G (gset_trivial G condition_l_unit_set_type) g y)))
         (usym_unit G, unit_prop star. (gset_usym_act G (gset_trivial G condition_l_unit_set_type) (usym_unit G) y))))

def unit_gset_subgroup_usym_equiv (G : Group)
  : Equiv (USym (subgroup_group G (unit_gset_subgroup G))) (USym G)
  ≔ let A ≔ ActionType G (gset_trivial G condition_l_unit_set_type) in
    equivalence_on_paths A (BG G .carrier)
      (quasi_inverse_equiv A (BG G .carrier) (u ↦ u .fst) (z ↦ (z, star.))
        (u ↦ (refl (u .fst), unit_prop star. (u .snd))) (z ↦ refl z))
      (shape G, star.) (shape G, star.)

def unit_gset_subgroup_finite (n : Nat) : IsFiniteGroup (subgroup_group (symmetric_group n) (unit_gset_subgroup (symmetric_group n)))
  ≔ finite_of_equiv (USym (subgroup_group (symmetric_group n) (unit_gset_subgroup (symmetric_group n))))
      (USym (symmetric_group n)) (unit_gset_subgroup_usym_equiv (symmetric_group n)) (symmetric_group_finite n)

{` Σ_2 acts on 2 without fixed points: the swap moves both points. `}
def whole_two_without_fixed_points : ActsWithoutFixedPoints two (unit_gset_subgroup (symmetric_group two))
  ≔ u ↦ gset_fin2_transposition_no_fixed (u .fst) (u .snd (sigma_two_swap, refl (star. : Unit)))

{` Not L(∅, 2): no sum of indices lies in the empty set. `}
def not_condition_l_two (h : ConditionL EmptySubsetOfNat two) : Empty
  ≔ let G ≔ subgroup_group (symmetric_group two) (unit_gset_subgroup (symmetric_group two)) in
    mere_rec (ConditionLWitness EmptySubsetOfNat G) Empty empty_prop (w ↦ w .snd .snd)
      (h (unit_gset_subgroup (symmetric_group two)) (unit_gset_subgroup_finite two) whole_two_without_fixed_points)

{` Index checks: |Σ_n : Σ_n| = 1, and the trivial subgroup (P_G, refl) of
   Σ_2 has index 2. `}
def condition_l_whole_index_one (n : Nat)
  : SubgroupHasIndex (symmetric_group n) (unit_gset_subgroup (symmetric_group n)) (suc. zero.)
  ≔ condition_l_trivial_gset_index_one (symmetric_group n)

def condition_l_trivial_index_two
  : SubgroupHasIndex (symmetric_group two)
      (principal_gset (symmetric_group two), refl (shape (symmetric_group two)),
        principal_gset_transitive (symmetric_group two)) two
  ≔ gset_index_iff_shape (symmetric_group two) (principal_gset (symmetric_group two)) two .snd
      (mere (Id Type (USym (symmetric_group two)) (Fin two))
        (ua (USym (symmetric_group two)) (Fin two) sigma2_usym_equiv))
