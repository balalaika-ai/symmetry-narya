export "412-symmetric-group-two"

{` Chapter 4, ex:groups and xca:group-example-details (group.tex 419-520). `}

{` A group whose symmetries form a contractible type is identified with the
   trivial group TG = Aut_Prop(true). `}
def usym_contractible_trivial (G : Group) (h : BookIsContr (USym G)) : Id Group G trivial_group
  ≔ usym_contractible_groups_path G trivial_group h trivial_group_usym_contractible

def automorphism_group_usym_contractible (A : Type) (hA : isGroupoid A) (a : A) (h : BookIsContr (Id A a a))
  : BookIsContr (USym (automorphism_group A hA a))
  ≔ book_contractibility_equiv (Id A a a) (USym (automorphism_group A hA a))
      (canonical_inverse_equiv (USym (automorphism_group A hA a)) (Id A a a)
        (automorphism_group_usym_equiv A hA a)) .map h

{` ex:groups (1). true and true = true are contractible. `}
def true_proposition_loops_contractible : BookIsContr (Id PropTypes true_proposition true_proposition)
  ≔ set_loops_contractible PropTypes propositions_set true_proposition

{` xca:group-example-details: Aut_Prop(P) is trivial for every proposition P. `}
def prop_automorphism_group_trivial (P : PropTypes)
  : Id Group (automorphism_group PropTypes props_groupoid P) trivial_group
  ≔ usym_contractible_trivial (automorphism_group PropTypes props_groupoid P)
      (automorphism_group_usym_contractible PropTypes props_groupoid P
        (set_loops_contractible PropTypes propositions_set P))

{` ex:groups (1): TG = mkgroup(true, triv) (the unit group), and
   TG = mkgroup(C, c) for every contractible C and c : C. `}
def unit_group_trivial : Id Group unit_group trivial_group
  ≔ usym_contractible_trivial unit_group unit_group_usym_contractible

def contractible_group_trivial (C : Type) (c : C) (h : BookIsContr C)
  : Id Group (contractible_group C c h) trivial_group
  ≔ concat Group (contractible_group C c h) unit_group trivial_group
      (contractible_classifying_groups_path (contractible_group C c h) unit_group h unit_contraction)
      unit_group_trivial

{` ex:groups (1): TG = Aut_S(x) for every set S and x : S. `}
def set_automorphism_group_trivial (S : Type) (hS : isSet S) (x : S)
  : Id Group (automorphism_group S (set_is_groupoid S hS) x) trivial_group
  ≔ usym_contractible_trivial (automorphism_group S (set_is_groupoid S hS) x)
      (automorphism_group_usym_contractible S (set_is_groupoid S hS) x (set_loops_contractible S hS x))

{` xca:group-example-details: Σ_S is trivial whenever the set S is a
   proposition, since then S ≃ S is contractible. In particular Σ_0, Σ_1 and
   Σ_false (with false = ∅; note Σ_0 = Σ_{Fin 0} = Σ_∅ by definition) are trivial. `}
def prop_automorphisms_contractible (S : Type) (hS : isProp S) : BookIsContr (Equiv S S)
  ≔ (identity_equiv S, e ↦ equiv_homotopy S S (identity_equiv S) e (x ↦ hS x (e .map x)))

def prop_permutation_group_trivial (S : SetTypes) (hS : isProp (S .fst))
  : Id Group (permutation_group S) trivial_group
  ≔ usym_contractible_trivial (permutation_group S)
      (book_contractibility_equiv (Equiv (S .fst) (S .fst)) (USym (permutation_group S))
        (canonical_inverse_equiv (USym (permutation_group S)) (Equiv (S .fst) (S .fst))
          (permutation_group_usym_equiv S)) .map (prop_automorphisms_contractible (S .fst) hS))

def empty_permutation_group : Group ≔ permutation_group (Empty, empty_set)

def empty_permutation_group_trivial : Id Group empty_permutation_group trivial_group
  ≔ prop_permutation_group_trivial (Empty, empty_set) empty_prop

def symmetric_group_zero_trivial : Id Group (symmetric_group zero.) trivial_group
  ≔ prop_permutation_group_trivial (standard_set zero.) empty_prop

def symmetric_group_zero_is_empty : Id Group (symmetric_group zero.) empty_permutation_group
  ≔ refl empty_permutation_group

def fin_one_type_prop : isProp (Fin (suc. zero.))
  ≔ x y ↦ match x, y [
  | inl. e, _ ↦ match e []
  | inr. _, inl. e ↦ match e []
  | inr. u, inr. v ↦ refl ((w ↦ inr. w) : Unit → Fin (suc. zero.)) (unit_prop u v) ]

def symmetric_group_one_trivial : Id Group (symmetric_group (suc. zero.)) trivial_group
  ≔ prop_permutation_group_trivial (standard_set (suc. zero.)) fin_one_type_prop

{` ex:genpermgroup: the groupoid Set is not connected (∅ and 1 are not
   merely equal), which is why Σ_S uses the component Set_(S). `}
def set_types_not_connected (h : Connected SetTypes) : Empty
  ≔ mere_rec (Id SetTypes (Empty, empty_set) (Unit, unit_set)) Empty empty_prop
      (p ↦ transport Type (X ↦ X) Unit Empty (inverse Type Empty Unit (p .fst)) star.)
      (h .snd (Empty, empty_set) (Unit, unit_set))

def permutation_group_classifying (S : SetTypes)
  : Id Pointed (BG (permutation_group S)) (NativeComponent SetTypes S, component_point SetTypes S)
  ≔ refl (BG (permutation_group S))

{` xca:group-example-details: Aut_FinSet(n) = Σ_n (FinSet = Σ(S : Set) isfinite(S)
   is a subtype of Set). `}
def finite_set_automorphism_group (n : Nat) : Group
  ≔ automorphism_group FiniteSets finite_sets_groupoid (standard_finite_set n)

def finite_set_automorphism_symmetric (n : Nat)
  : Id Group (finite_set_automorphism_group n) (symmetric_group n)
  ≔ automorphism_group_subtype_path SetTypes (S ↦ IsFinite (S .fst)) (S ↦ isfinite_prop (S .fst))
      finite_sets_groupoid sets_groupoid (standard_finite_set n)

{` ex:groups (2): Σ_n = Aut_{FinSet_n}(n) (rem:symmetriesofnonconnectedgroupoids,
   FinSet_n being connected). `}
def symmetric_group_finset_n_automorphism (n : Nat)
  : Id Group (symmetric_group n)
      (automorphism_group (BookFiniteSetsAt n) (bg_groupoid (symmetric_group n)) (shape (symmetric_group n)))
  ≔ group_shape_automorphism_path (symmetric_group n)

{` ex:groups (2): Σ_S = Aut_U(S) for every set S, where Aut_U(S) ≔ mkgroup(U_(S), S)
   is a group because U_(S) is a groupoid (universe_set_automorphism_group of
   module 485; "stretching the definition of Aut", rem:autinfgp). The
   identification is induced by component_subtype_equiv for Set ⊆ U. `}
def permutation_group_universe_path (S : SetTypes)
  : Id Group (permutation_group S) (universe_set_automorphism_group (S .fst) (S .snd))
  ≔ group_path_from_pointed_equiv (permutation_group S) (universe_set_automorphism_group (S .fst) (S .snd))
      ((component_subtype_equiv Type isSet isset_isprop S .map,
        component_path Type (S .fst) (component_point Type (S .fst))
          (component_subtype_equiv Type isSet isset_isprop S .map (component_point SetTypes S)) (refl (S .fst))),
       book_equivalence (NativeComponent SetTypes S) (NativeComponent Type (S .fst))
         (component_subtype_equiv Type isSet isset_isprop S) .equiv)

def symmetric_group_universe_path (n : Nat)
  : Id Group (symmetric_group n) (universe_set_automorphism_group (Fin n) (fin_set n))
  ≔ permutation_group_universe_path (standard_set n)

{` Equivalent sets have identified permutation groups. `}
def permutation_group_equiv_path (S T : SetTypes) (e : Equiv (S .fst) (T .fst))
  : Id Group (permutation_group S) (permutation_group T)
  ≔ refl permutation_group (set_types_path S T e)
