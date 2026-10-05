export "700-monoids-and-group-laws"

{` Chapter 7 (absgroup.tex), xca:typemonoidisgroupoid, the monoid half
   (the abstract-group half is abstract_group_groupoid, module 702).

   Monoid ≃ Σ (X : Set) (Σ e Σ μ UnitLaws × AssocLaw); the base is the
   groupoid of sets (sets_groupoid, lem:Set-is-groupoid) and the fibres
   are sets (X is a set, so are X → X → X, and the laws are propositions),
   so the Σ-type has h-level 3 (hlevel_sigma) and so has Monoid.

   Litmus: Monoid is not a set. The three-element monoid {1, a, b}
   (carrier Sum Unit Bool, unit inl star, x · y = x for x ≠ 1) has the
   automorphism swapping a and b; the identification it induces by
   univalence is not refl. `}

def MonoidStructureOnSet (X : SetTypes) : Type
  ≔ Σ (X .fst) (e ↦ Σ (X .fst → X .fst → X .fst) (mul ↦
      Product (UnitLaws (X .fst) e mul) (AssocLaw (X .fst) mul)))

def MonoidOverSets : Type ≔ Σ SetTypes MonoidStructureOnSet

def monoid_to_over_sets (M : Monoid) : MonoidOverSets
  ≔ ((M .carrier, M .laws .fst), (M .unit, (M .mul, M .laws .snd)))

def monoid_from_over_sets (t : MonoidOverSets) : Monoid
  ≔ (t .fst .fst, t .snd .fst, t .snd .snd .fst, (t .fst .snd, t .snd .snd .snd))

def monoid_over_sets_equiv : Equiv Monoid MonoidOverSets
  ≔ quasi_inverse_equiv Monoid MonoidOverSets monoid_to_over_sets monoid_from_over_sets (M ↦ refl M) (t ↦ refl t)

def monoid_structure_laws_prop (S : Type) (hS : isSet S) (e : S) (mul : S → S → S)
  : isProp (Product (UnitLaws S e mul) (AssocLaw S mul))
  ≔ u v ↦ refl ((w ↦ w .snd) : MonoidLaws S e mul → Product (UnitLaws S e mul) (AssocLaw S mul))
      (monoid_laws_prop S e mul (hS, u) (hS, v))

def monoid_structure_set (X : SetTypes) : isSet (MonoidStructureOnSet X)
  ≔ let S ≔ X .fst in
    sigma_set S (e ↦ Σ (S → S → S) (mul ↦ Product (UnitLaws S e mul) (AssocLaw S mul))) (X .snd)
      (e ↦ sigma_set (S → S → S) (mul ↦ Product (UnitLaws S e mul) (AssocLaw S mul))
        (pi_set S (_ ↦ S → S) (_ ↦ pi_set S (_ ↦ S) (_ ↦ X .snd)))
        (mul ↦ prop_is_set (Product (UnitLaws S e mul) (AssocLaw S mul))
          (monoid_structure_laws_prop S (X .snd) e mul)))

def monoid_over_sets_hlevel : HLevel (suc. (suc. (suc. zero.))) MonoidOverSets
  ≔ hlevel_sigma (suc. (suc. (suc. zero.))) SetTypes MonoidStructureOnSet
      (groupoid_to_hlevel SetTypes sets_groupoid)
      (X ↦ hlevel_raise (suc. (suc. zero.)) (MonoidStructureOnSet X)
        (set_to_hlevel_two (MonoidStructureOnSet X) (monoid_structure_set X)))

{` xca:typemonoidisgroupoid: the type of monoids is a groupoid. `}
def monoid_groupoid : isGroupoid Monoid
  ≔ hlevel_to_groupoid Monoid
      (hlevel_equiv (suc. (suc. (suc. zero.))) MonoidOverSets Monoid
        (canonical_inverse_equiv Monoid MonoidOverSets monoid_over_sets_equiv) monoid_over_sets_hlevel)

{` Litmus: the monoid {1, a, b} with x · y = x for x ≠ 1. `}
def left_zero_monoid_mul (x y : Sum Unit Bool) : Sum Unit Bool ≔ match x [ inl. _ ↦ y | inr. b ↦ inr. b ]

def left_zero_monoid_laws : MonoidLaws (Sum Unit Bool) (inl. star.) left_zero_monoid_mul
  ≔ (sum_set Unit Bool unit_set bool_set,
     (g ↦ match g [
       | inl. s ↦ (match s [ star. ↦ refl (inl. star. : Sum Unit Bool) ], refl (inl. s : Sum Unit Bool))
       | inr. b ↦ (refl (inr. b : Sum Unit Bool), refl (inr. b : Sum Unit Bool)) ],
      g1 g2 g3 ↦ match g1 [
       | inl. _ ↦ refl (left_zero_monoid_mul g2 g3)
       | inr. b ↦ refl (inr. b : Sum Unit Bool) ]))

def left_zero_monoid : Monoid ≔ (Sum Unit Bool, inl. star., left_zero_monoid_mul, left_zero_monoid_laws)

def left_zero_swap (x : Sum Unit Bool) : Sum Unit Bool ≔ match x [ inl. s ↦ inl. s | inr. b ↦ inr. (bool_not b) ]

def left_zero_swap_involutive (x : Sum Unit Bool) : Id (Sum Unit Bool) (left_zero_swap (left_zero_swap x)) x
  ≔ match x [ inl. s ↦ refl (inl. s : Sum Unit Bool) | inr. b ↦ inr. (bool_not_involutive b) ]

def left_zero_swap_equiv : Equiv (Sum Unit Bool) (Sum Unit Bool)
  ≔ quasi_inverse_equiv (Sum Unit Bool) (Sum Unit Bool) left_zero_swap left_zero_swap
      left_zero_swap_involutive left_zero_swap_involutive

def left_zero_swap_mul (x y : Sum Unit Bool)
  : Id (Sum Unit Bool) (left_zero_swap (left_zero_monoid_mul x y)) (left_zero_monoid_mul (left_zero_swap x) (left_zero_swap y))
  ≔ match x [ inl. _ ↦ refl (left_zero_swap y) | inr. b ↦ refl (inr. (bool_not b) : Sum Unit Bool) ]

{` Identifications of monoids from identifications of the data. `}
def MonoidData : Type ≔ Σ Type (S ↦ Σ S (e ↦ S → S → S))

def monoid_data (M : Monoid) : MonoidData ≔ (M .carrier, (M .unit, M .mul))

def MonoidLawsAt (d : MonoidData) : Type ≔ MonoidLaws (d .fst) (d .snd .fst) (d .snd .snd)

def monoid_laws_pathover (d d' : MonoidData) (q : Id MonoidData d d') (l : MonoidLawsAt d) (l' : MonoidLawsAt d')
  : Id MonoidLawsAt q l l'
  ≔ pathover_hlevel zero. MonoidData MonoidLawsAt
      (d ↦ prop_to_hlevel_one (MonoidLawsAt d) (monoid_laws_prop (d .fst) (d .snd .fst) (d .snd .snd)))
      d d' q l l' .center

def monoid_path_of_data (M N : Monoid) (q : Id MonoidData (monoid_data M) (monoid_data N)) : Id Monoid M N
  ≔ (q .fst, q .snd .fst, q .snd .snd, monoid_laws_pathover (monoid_data M) (monoid_data N) q (M .laws) (N .laws))

def left_zero_swap_path : Id Monoid left_zero_monoid left_zero_monoid
  ≔ let S ≔ Sum Unit Bool in let f ≔ left_zero_swap_equiv in
    monoid_path_of_data left_zero_monoid left_zero_monoid
      (ua S S f,
       ((unglue ≔ refl (inl. star. : Sum Unit Bool)),
        x y ⤇ (unglue ≔ concat S (left_zero_swap (left_zero_monoid_mul x.0 y.0))
                 (left_zero_monoid_mul (left_zero_swap x.0) (left_zero_swap y.0)) (left_zero_monoid_mul x.1 y.1)
                 (left_zero_swap_mul x.0 y.0) (refl left_zero_monoid_mul (x.2 .unglue) (y.2 .unglue)))))

def left_zero_swap_path_nontrivial (r : Id (Id Monoid left_zero_monoid left_zero_monoid) left_zero_swap_path (refl left_zero_monoid))
  : Empty
  ≔ let S ≔ Sum Unit Bool in
    let ev : Id Monoid left_zero_monoid left_zero_monoid → S ≔ q ↦ q .carrier .trr (inr. false.) in
    bool_encode true. false.
      (sum_encode Unit Bool (inr. true.) (inr. false.)
        (concat S (inr. true.) (ev (refl left_zero_monoid)) (inr. false.)
          (refl ev r)
          (inverse S (inr. false.) (ev (refl left_zero_monoid)) (refl S .liftr (inr. false.)))))

def monoid_not_set (h : isSet Monoid) : Empty
  ≔ left_zero_swap_path_nontrivial (h left_zero_monoid left_zero_monoid left_zero_swap_path (refl left_zero_monoid))
