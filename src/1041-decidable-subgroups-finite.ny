export "1040-decidable-subgroups-closed-subsets"
export "1012-finite-group-orders"

{` Chapter 10, rem:noofsubgps (fingp.tex 35-40), continued.

   decidable_subgroups_closed_subsets_equiv: for every group G, the decidable
   subgroups Σ (S : Sub(G)) isDecidable(S) are equivalent to the Bool-valued
   abstract subgroups of abstr(G) (no hypothesis on G). The two composites
   are the identity: the stabilizer of [refl] in the coset G-set of A is A
   (closed_subset_coset_fixes_iff), and a decidable subgroup is determined
   by its stabilizer (subgroup_le_antisym, module 1030).

   decidable_subgroups_finite: for a finite group G the decidable subgroups
   form a finite set (a decidable subset of the finite set USym G → Bool),
   so "the number of (decidable) subgroups" of a finite group is
   cardinality (DecidableSubgroups G) (decidable_subgroups_finite G hG). `}

def decidable_subgroups_to_from (G : Group) (P : ClosedBoolSubsets (abstr G))
  : Id (ClosedBoolSubsets (abstr G))
      (decidable_subgroup_closed_subset G (closed_subset_decidable_subgroup G P)) P
  ≔ let S ≔ closed_subset_subgroup G P in
    let dS ≔ closed_subset_subgroup_decidable G P in
    closed_bool_subsets_path (abstr G) (decidable_subgroup_closed_subset G (closed_subset_decidable_subgroup G P)) P
      (g ↦ decsub_bool_unique (SubgroupPointFixed G S g) (dS (gset_usym_act G (S .gset) g (S .point)) (S .point))
        (P .fst g) (closed_subset_coset_fixes_member G P g) (closed_subset_coset_member_fixes G P g))

def decidable_subgroups_from_to (G : Group) (u : DecidableSubgroups G)
  : Id (DecidableSubgroups G) (closed_subset_decidable_subgroup G (decidable_subgroup_closed_subset G u)) u
  ≔ let A ≔ decidable_subgroup_closed_subset G u in
    let SA ≔ closed_subset_subgroup G A in
    subtype_equal (Subgroups G) (IsDecidableSubgroup G) (is_decidable_subgroup_prop G)
      (closed_subset_decidable_subgroup G A) u
      (subgroup_le_antisym G SA (u .fst)
        (g r ↦ subgroup_fix_indicator_reflect G (u .fst) (u .snd) g (closed_subset_coset_fixes_member G A g r))
        (g r ↦ closed_subset_coset_member_fixes G A g (subgroup_fix_indicator_true G (u .fst) (u .snd) g r)))

{` Decidable subgroups ≃ Bool-valued abstract subgroups. `}
def decidable_subgroups_closed_subsets_equiv (G : Group)
  : Equiv (Σ (Subgroups G) (IsDecidableSubgroup G)) (ClosedBoolSubsets (abstr G))
  ≔ quasi_inverse_equiv (DecidableSubgroups G) (ClosedBoolSubsets (abstr G))
      (decidable_subgroup_closed_subset G) (closed_subset_decidable_subgroup G)
      (decidable_subgroups_from_to G) (decidable_subgroups_to_from G)

{` Finiteness. Bool-valued functions on a finite type form a finite type. `}
def decsub_bool_finite : IsFinite Bool
  ≔ finite_of_equiv Bool (Fin two) (canonical_inverse_equiv (Fin two) Bool fin_two_equiv) (fin_is_finite two)

def finite_bool_functions (A : Type) (hA : IsFinite A) : IsFinite (A → Bool)
  ≔ mere_rec (Σ Nat (n ↦ Id Type A (Fin n))) (IsFinite (A → Bool)) (isfinite_prop (A → Bool))
      (w ↦ transport Type (T ↦ IsFinite (T → Bool)) (Fin (w .fst)) A (inverse Type A (Fin (w .fst)) (w .snd))
        (fin_functions_finite (w .fst) Bool decsub_bool_finite))
      hA

def decsub_decidable_implication (X Y : Type) (dX : Decidable X) (dY : Decidable Y) : Decidable (X → Y)
  ≔ match dY [
    | inl. y ↦ inl. (_ ↦ y)
    | inr. ny ↦ match dX [
      | inl. x ↦ inr. (f ↦ ny (f x))
      | inr. nx ↦ inl. (x ↦ absurd Y (nx x)) ] ]

def decsub_decidable_product (X Y : Type) (dX : Decidable X) (dY : Decidable Y) : Decidable (Product X Y)
  ≔ match dX [
    | inl. x ↦ match dY [ inl. y ↦ inl. (x, y) | inr. ny ↦ inr. (w ↦ ny (w .snd)) ]
    | inr. nx ↦ inr. (w ↦ nx (w .fst)) ]

{` For a finite group, being a Bool-valued abstract subgroup is decidable. `}
def closed_bool_subsets_decidable (G : Group) (hG : IsFiniteGroup G) (A : USym G → Bool)
  : Decidable (IsAbstractSubgroup (abstr G) (BoolSubgroupFamily (abstr G) A))
  ≔ let U ≔ USym G in
    let T : U → Type ≔ g ↦ Id Bool (A g) true. in
    let hT : (g : U) → isProp (T g) ≔ g ↦ bool_set (A g) true. in
    let dT : (g : U) → Decidable (T g) ≔ g ↦ bool_true_decidable (A g) in
    let MulAt : U → U → Type ≔ x y ↦ T x → T y → T (usym_mul G x y) in
    let mul_prop : (x y : U) → isProp (MulAt x y)
      ≔ x y ↦ pi_prop (T x) (_ ↦ T y → T (usym_mul G x y))
          (_ ↦ pi_prop (T y) (_ ↦ T (usym_mul G x y)) (_ ↦ hT (usym_mul G x y))) in
    let mul_dec : (x y : U) → Decidable (MulAt x y)
      ≔ x y ↦ decsub_decidable_implication (T x) (T y → T (usym_mul G x y)) (dT x)
          (decsub_decidable_implication (T y) (T (usym_mul G x y)) (dT y) (dT (usym_mul G x y))) in
    let MulAll : U → Type ≔ x ↦ (y : U) → MulAt x y in
    let mul_all_dec : (x : U) → Decidable (MulAll x)
      ≔ x ↦ finite_quantifiers U hG (MulAt x) (mul_prop x) (mul_dec x) .fst in
    let mul_all_prop : (x : U) → isProp (MulAll x) ≔ x ↦ pi_prop U (MulAt x) (mul_prop x) in
    let InvAt : U → Type ≔ x ↦ T x → T (usym_inv G x) in
    let inv_dec : Decidable ((x : U) → InvAt x)
      ≔ finite_quantifiers U hG InvAt (x ↦ pi_prop (T x) (_ ↦ T (usym_inv G x)) (_ ↦ hT (usym_inv G x)))
          (x ↦ decsub_decidable_implication (T x) (T (usym_inv G x)) (dT x) (dT (usym_inv G x))) .fst in
    decsub_decidable_product ((x : U) → isProp (T x))
      (Product (T (usym_unit G)) (Product ((x : U) → MulAll x) ((x : U) → InvAt x)))
      (inl. hT)
      (decsub_decidable_product (T (usym_unit G)) (Product ((x : U) → MulAll x) ((x : U) → InvAt x))
        (dT (usym_unit G))
        (decsub_decidable_product ((x : U) → MulAll x) ((x : U) → InvAt x)
          (finite_quantifiers U hG MulAll mul_all_prop mul_all_dec .fst) inv_dec))

def closed_bool_subsets_finite (G : Group) (hG : IsFiniteGroup G) : IsFinite (ClosedBoolSubsets (abstr G))
  ≔ finite_decidable_subset (USym G → Bool) (finite_bool_functions (USym G) hG)
      (A ↦ IsAbstractSubgroup (abstr G) (BoolSubgroupFamily (abstr G) A))
      (closed_bool_subsets_prop (abstr G)) (closed_bool_subsets_decidable G hG)

{` The decidable subgroups of a finite group form a finite set. `}
def decidable_subgroups_finite (G : Group) (hG : IsFiniteGroup G) : IsFinite (Σ (Subgroups G) (IsDecidableSubgroup G))
  ≔ finite_of_equiv (DecidableSubgroups G) (ClosedBoolSubsets (abstr G)) (decidable_subgroups_closed_subsets_equiv G)
      (closed_bool_subsets_finite G hG)

{` The number of decidable subgroups is the number of Bool-valued abstract
   subgroups (for any finiteness proofs). `}
def decidable_subgroups_card (G : Group) (hG : IsFiniteGroup G) (h : IsFinite (Σ (Subgroups G) (IsDecidableSubgroup G)))
  : Id Nat (cardinality (Σ (Subgroups G) (IsDecidableSubgroup G)) h)
      (cardinality (ClosedBoolSubsets (abstr G)) (closed_bool_subsets_finite G hG))
  ≔ cardinality_equiv (DecidableSubgroups G) (ClosedBoolSubsets (abstr G)) (decidable_subgroups_closed_subsets_equiv G)
      h (closed_bool_subsets_finite G hG)
