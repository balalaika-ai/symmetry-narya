export "211-exponential-fibers"
export "220-free-integer-actions"

{` Chapter 2 completions: small side claims and companion statements
   that were stated only informally or only for the universe Type. `}

{` (a) lem:Prop-in-Set, for every model universe U (def:Prop-Set):
   the type Prop_U of U-small propositions is a set. `}
def prop_u_set (U : Universe) : isSet (PropU U)
  ≔ P Q ↦
    retract_prop (Id Type (P .fst .fst) (Q .fst .fst)) (Id (PropU U) P Q)
      (proposition_type_paths_prop (P .fst .fst) (Q .fst .fst) (Q .snd))
      (equiv_inverse_map (Id (PropU U) P Q) (Id Type (P .fst .fst) (Q .fst .fst)) (prop_u_path_equiv U P Q))
      (prop_u_path_equiv U P Q .map)
      (equiv_retraction (Id (PropU U) P Q) (Id Type (P .fst .fst) (Q .fst .fst)) (prop_u_path_equiv U P Q))

{` (a) Identifications in Set_U are identifications of the underlying types. `}
def set_u_path_equiv (U : Universe) (A B : SetU U)
  : Equiv (Id (SetU U) A B) (Id Type (A .fst .fst) (B .fst .fst))
  ≔ compose_equiv (Id (SetU U) A B) (Id (UniverseType U) (A .fst) (B .fst)) (Id Type (A .fst .fst) (B .fst .fst))
      (subtype_path_equiv (UniverseType U) (X ↦ isSet (X .fst)) (X ↦ isset_isprop (X .fst)) A B)
      (subtype_path_equiv Type (U .small) (U .small_prop) (A .fst) (B .fst))

{` (a) lem:Set-is-groupoid, for every model universe U: Set_U is a groupoid. `}
def set_u_groupoid (U : Universe) : isGroupoid (SetU U)
  ≔ A B ↦ hlevel_two_to_set (Id (SetU U) A B)
      (hlevel_equiv (suc. (suc. zero.)) (Id Type (A .fst .fst) (B .fst .fst)) (Id (SetU U) A B)
        (canonical_inverse_equiv (Id (SetU U) A B) (Id Type (A .fst .fst) (B .fst .fst)) (set_u_path_equiv U A B))
        (set_to_hlevel_two (Id Type (A .fst .fst) (B .fst .fst))
          (set_type_paths_set (A .fst .fst) (B .fst .fst) (B .snd))))

{` (b) xca:try-your-luck-N, the parentheticals for the book relations
   (def:orderonN): < is irreflexive, as the case m = n of ¬((m<n)×(n<m)),
   and ≤ is reflexive, with difference witness 0. `}
def book_lt_irrefl (n : Nat) (h : BookLt n n) : Empty ≔ book_lt_asym n n h h

def book_le_refl (n : Nat) : BookLe n n ≔ (zero., add_zero_left n)

{` (c) rem:subset-of-fin-set, the headline "a subset of a finite set is not
   necessarily finite": that every subset (def:subtype, a Prop-valued
   predicate) of every finite set is finite is equivalent to the law of
   excluded middle. Given the former, a proposition p is a subset of the
   finite set 1, so it is finite and hence decidable; conversely, under
   excluded middle every predicate is decidable, and decidable subsets of
   finite sets are finite. `}
def FiniteSubsetsFinite : Type
  ≔ (A : Type) → IsFinite A → (P : Subtypes A) → IsFinite (SubtypeCarrier A P)

def finite_subsets_finite_prop : isProp FiniteSubsetsFinite
  ≔ pi_prop Type (A ↦ IsFinite A → (P : Subtypes A) → IsFinite (SubtypeCarrier A P))
      (A ↦ pi_prop (IsFinite A) (_ ↦ (P : Subtypes A) → IsFinite (SubtypeCarrier A P))
        (_ ↦ pi_prop (Subtypes A) (P ↦ IsFinite (SubtypeCarrier A P)) (P ↦ isfinite_prop (SubtypeCarrier A P))))

def subsets_finite_excluded_middle (all : FiniteSubsetsFinite) : ExcludedMiddle
  ≔ P hp ↦
    let S : Subtypes Unit ≔ _ ↦ (P, hp) in
    finite_prop_decidable P hp
      (finite_of_equiv P (SubtypeCarrier Unit S)
        (quasi_inverse_equiv P (SubtypeCarrier Unit S) (p ↦ (star., p)) (t ↦ t .snd)
          (p ↦ refl p) (t ↦ (unit_prop star. (t .fst), refl (t .snd))))
        (all Unit finite_unit S))

def excluded_middle_subsets_finite (lem : ExcludedMiddle) : FiniteSubsetsFinite
  ≔ A ha P ↦ finite_decidable_subset A ha (t ↦ P t .fst) (t ↦ P t .snd) (t ↦ lem (P t .fst) (P t .snd))

def subsets_finite_excluded_middle_equiv : Equiv FiniteSubsetsFinite ExcludedMiddle
  ≔ iff_equiv FiniteSubsetsFinite ExcludedMiddle finite_subsets_finite_prop excluded_middle_prop
      subsets_finite_excluded_middle excluded_middle_subsets_finite

{` (d) lem:typefamiliesandfibrations in its same-universe form, for every
   model universe U and A : U: preim : Σ_{B:U}(B → A) → (A → U), with
   preim(B,f)(a) = f⁻¹(a) (a U-small type by closure of U under Σ and
   identity types), is an equivalence with inverse C ↦ (Σ_{a:A} C(a), fst). `}
def universe_fibers_of_map (U : Universe) (A : UniverseType U)
  (t : Σ (UniverseType U) (B ↦ B .fst → A .fst)) : A .fst → UniverseType U
  ≔ a ↦ (BookFiber (t .fst .fst) (A .fst) (t .snd) a,
      U .sigma_small (t .fst .fst) (b ↦ Id (A .fst) a (t .snd b)) (t .fst .snd)
        (b ↦ U .id_small (A .fst) (A .snd) a (t .snd b)))

def universe_map_of_family (U : Universe) (A : UniverseType U) (C : A .fst → UniverseType U)
  : Σ (UniverseType U) (B ↦ B .fst → A .fst)
  ≔ ((Σ (A .fst) (a ↦ C a .fst), U .sigma_small (A .fst) (a ↦ C a .fst) (A .snd) (a ↦ C a .snd)),
      u ↦ u .fst)

def universe_maps_families_eta (U : Universe) (A : UniverseType U)
  (t : Σ (UniverseType U) (B ↦ B .fst → A .fst))
  : Id (Σ (UniverseType U) (B ↦ B .fst → A .fst)) (universe_map_of_family U A (universe_fibers_of_map U A t)) t
  ≔ let A0 ≔ A .fst in
    let M ≔ Σ (MapsInto A0) (s ↦ U .small (s .fst)) in
    let back ≔ ((w ↦ ((w .fst .fst, w .snd), w .fst .snd)) : M → Σ (UniverseType U) (B ↦ B .fst → A0)) in
    let t0 : MapsInto A0 ≔ (t .fst .fst, t .snd) in
    let s0 ≔ universe_map_of_family U A (universe_fibers_of_map U A t) .fst .snd in
    let r ≔ maps_families_eta A0 t0 in
    let p : Id M (map_of_family A0 (fibers_of_map A0 t0), s0) (t0, t .fst .snd)
      ≔ (r, prop_family_pathover (MapsInto A0) (s ↦ U .small (s .fst)) (s ↦ U .small_prop (s .fst))
          (map_of_family A0 (fibers_of_map A0 t0)) t0 r s0 (t .fst .snd)) in
    refl back p

def universe_maps_families_beta (U : Universe) (A : UniverseType U) (C : A .fst → UniverseType U)
  : Id (A .fst → UniverseType U) (universe_fibers_of_map U A (universe_map_of_family U A C)) C
  ≔ funext (A .fst) (_ ↦ UniverseType U) (universe_fibers_of_map U A (universe_map_of_family U A C)) C
      (a ↦
        let F ≔ BookFiber (Σ (A .fst) (x ↦ C x .fst)) (A .fst) (u ↦ u .fst) a in
        let p ≔ ua F (C a .fst) (projection_book_fiber_equiv (A .fst) (x ↦ C x .fst) a) in
        (p, prop_family_pathover Type (U .small) (U .small_prop) F (C a .fst) p
          (universe_fibers_of_map U A (universe_map_of_family U A C) a .snd) (C a .snd)))

def universe_maps_families_equiv (U : Universe) (A : UniverseType U)
  : BookEquiv (Σ (UniverseType U) (B ↦ B .fst → A .fst)) (A .fst → UniverseType U)
  ≔ book_quasi_inverse_equiv (Σ (UniverseType U) (B ↦ B .fst → A .fst)) (A .fst → UniverseType U)
      (universe_fibers_of_map U A) (universe_map_of_family U A)
      (universe_maps_families_eta U A) (universe_maps_families_beta U A)

{` (d) The map of the equivalence is preim, by definition. `}
def universe_maps_families_map (U : Universe) (A : UniverseType U)
  (t : Σ (UniverseType U) (B ↦ B .fst → A .fst)) (a : A .fst)
  : Id Type (universe_maps_families_equiv U A .map t a .fst) (BookFiber (t .fst .fst) (A .fst) (t .snd) a)
  ≔ refl (BookFiber (t .fst .fst) (A .fst) (t .snd) a)

{` (e) xca:stuff-struct-prop, maps between groupoids. In the terminology
   before exa:stuff-struct-prop, f forgets at most properties, structure or
   1-structure (stuff) when its fibers are propositions, sets or groupoids,
   i.e. TruncatedMap at h-level 1, 2 or 3; it forgets nothing when they are
   contractible. Between groupoids every map forgets at most stuff. `}
def groupoid_map_one_truncated (A B : Type) (hA : isGroupoid A) (hB : isGroupoid B) (f : A → B)
  : TruncatedMap (suc. (suc. (suc. zero.))) A B f
  ≔ b ↦ hlevel_sigma (suc. (suc. (suc. zero.))) A (a ↦ Id B b (f a)) (groupoid_to_hlevel A hA)
      (a ↦ hlevel_raise (suc. (suc. zero.)) (Id B b (f a)) (set_to_hlevel_two (Id B b (f a)) (hB b (f a))))

def set_types_not_set (h : isSet SetTypes) : Empty
  ≔ bool_swap_nontrivial
      (refl ((l ↦ l .fst) : Id SetTypes boolean_set boolean_set → Id Type Bool Bool)
        (h boolean_set boolean_set boolean_set_swap_pair (refl boolean_set)))

{` (e) Forgetting that a set is non-empty (def:non-empty) forgets at most
   properties, and it does forget something: the fiber over the empty set
   is empty. Both types are groupoids. `}
def NonemptySets : Type ≔ Σ SetTypes (S ↦ Mere (S .fst))

def nonempty_sets_groupoid : isGroupoid NonemptySets
  ≔ hlevel_to_groupoid NonemptySets
      (subtype_hlevel (suc. (suc. zero.)) SetTypes (S ↦ Mere (S .fst))
        (groupoid_to_hlevel SetTypes sets_groupoid) (S ↦ mere_isprop (S .fst)))

def nonempty_sets_forget_properties : TruncatedMap (suc. zero.) NonemptySets SetTypes (S ↦ S .fst)
  ≔ projection_truncated (suc. zero.) SetTypes (S ↦ Mere (S .fst))
      (S ↦ prop_to_hlevel_one (Mere (S .fst)) (mere_isprop (S .fst)))

def nonempty_sets_forget_something (h : TruncatedMap zero. NonemptySets SetTypes (S ↦ S .fst)) : Empty
  ≔ let E : SetTypes ≔ (Empty, empty_set) in
    mere_rec Empty Empty empty_prop (x ↦ x)
      (projection_fiber_level_reflect zero. SetTypes (S ↦ Mere (S .fst)) E (h E) .center)

{` (e) Forgetting the point of a pointed set forgets at most structure,
   and not only properties: the fiber over a set X is X itself, and the
   fiber over Bool is not a proposition. Both types are groupoids. `}
def PointedSets : Type ≔ Σ SetTypes (S ↦ S .fst)

def pointed_sets_groupoid : isGroupoid PointedSets
  ≔ hlevel_to_groupoid PointedSets
      (hlevel_sigma (suc. (suc. (suc. zero.))) SetTypes (S ↦ S .fst) (groupoid_to_hlevel SetTypes sets_groupoid)
        (S ↦ hlevel_raise (suc. (suc. zero.)) (S .fst) (set_to_hlevel_two (S .fst) (S .snd))))

def pointed_sets_forget_structure : TruncatedMap (suc. (suc. zero.)) PointedSets SetTypes (X ↦ X .fst)
  ≔ projection_truncated (suc. (suc. zero.)) SetTypes (S ↦ S .fst) (S ↦ set_to_hlevel_two (S .fst) (S .snd))

def pointed_sets_forget_not_properties (h : TruncatedMap (suc. zero.) PointedSets SetTypes (X ↦ X .fst)) : Empty
  ≔ bool_encode false. true.
      (hlevel_one_to_prop Bool
        (projection_fiber_level_reflect (suc. zero.) SetTypes (S ↦ S .fst) boolean_set (h boolean_set))
        false. true.)

{` (e) Forgetting a set altogether, the map Set → 1 between groupoids,
   forgets stuff (1-structure) and not merely structure: its fiber is the
   groupoid Set, which is not a set. `}
def unit_groupoid : isGroupoid Unit ≔ x y ↦ prop_is_set (Id Unit x y) (unit_set x y)

def sets_to_unit : SetTypes → Unit ≔ _ ↦ star.

def sets_to_unit_one_truncated : TruncatedMap (suc. (suc. (suc. zero.))) SetTypes Unit sets_to_unit
  ≔ groupoid_map_one_truncated SetTypes Unit sets_groupoid unit_groupoid sets_to_unit

def sets_to_unit_not_zero_truncated (h : TruncatedMap (suc. (suc. zero.)) SetTypes Unit sets_to_unit) : Empty
  ≔ set_types_not_set (hlevel_two_to_set SetTypes
      (hlevel_equiv (suc. (suc. zero.)) (BookFiber SetTypes Unit sets_to_unit star.) SetTypes
        (contractible_fiber_projection SetTypes (_ ↦ Id Unit star. star.)
          (_ ↦ prop_paths_contractible Unit unit_prop star. star.))
        (h star.)))

{` (e) Forgetting the point of a pointed groupoid forgets stuff and not
   merely structure. This map is between 2-types (the type of groupoids is
   not a groupoid), so it lies outside the exercise's groupoids; it is the
   correct form of the remark that forgetting the point of a pointed type
   forgets stuff: for pointed types in general the fiber over X is X, which
   need not be a groupoid. `}
def GroupoidTypes : Type ≔ Σ Type isGroupoid

def PointedGroupoids : Type ≔ Σ GroupoidTypes (X ↦ X .fst)

def pointed_groupoids_forget_stuff
  : TruncatedMap (suc. (suc. (suc. zero.))) PointedGroupoids GroupoidTypes (X ↦ X .fst)
  ≔ projection_truncated (suc. (suc. (suc. zero.))) GroupoidTypes (X ↦ X .fst)
      (X ↦ groupoid_to_hlevel (X .fst) (X .snd))

def pointed_groupoids_forget_not_structure
  (h : TruncatedMap (suc. (suc. zero.)) PointedGroupoids GroupoidTypes (X ↦ X .fst)) : Empty
  ≔ set_types_not_set (hlevel_two_fiber_set GroupoidTypes (X ↦ X .fst) h (SetTypes, sets_groupoid))

{` (f) lem:trp-in-function-type, native companion. Stated with the native
   backward transport .trl along e in place of transport along e⁻¹, it
   holds by definition: HOTT computes transport in a function-type family
   in exactly this way. `}
def transport_function_family_trl (X : Type) (Y Z : X → Type) (x x' : X) (e : Id X x x')
  (f : Y x → Z x) (y' : Y x')
  : Id (Z x') (transport X (FunctionFamily X Y Z) x x' e f y')
      (transport X Z x x' e (f (refl Y e .trl y')))
  ≔ refl (transport X Z x x' e (f (refl Y e .trl y')))

{` (f) The backward transport along ua(g) is the inverse map of g, by
   definition (the forward direction is ua_transport). `}
def ua_trl (A B : Type) (g : Equiv A B) (y : B)
  : Id A (ua A B g .trl y) (equiv_inverse_map A B g y)
  ≔ refl (equiv_inverse_map A B g y)

{` (f) The special case after lem:trp-in-function-type, transport of an
   endomorphism along ua(g) is g ∘ f ∘ g⁻¹, also holds by definition
   (compare transport_endomorphism_ua). `}
def transport_endomorphism_ua_trl (A B : Type) (g : Equiv A B) (f : A → A)
  : Id (B → B) (transport Type (T ↦ T → T) A B (ua A B g) f) (y ↦ g .map (f (equiv_inverse_map A B g y)))
  ≔ refl ((y ↦ g .map (f (equiv_inverse_map A B g y))) : B → B)

{` (g) ℤ is the free type with an automorphism, with the book's map: for
   every type Y and automorphism F, evaluation at 0, f ↦ f(0), on maps
   (ℤ, succ) → (Y, F) of types with automorphism is an equivalence. The map
   of int_maps_equiv is not evaluation at 0 by definition, because it
   reindexes sums with sigma_base_change (defined by equivalence induction).
   Here the same chain of equivalences is rebuilt with a reindexing whose
   maps are explicit, (a, c) ↦ (e a, c) and (b, c) ↦ (e⁻¹ b, c transported
   back along the counit), so that the composite is evaluation at 0 by
   definition (int_maps_evaluation_map). `}
def sigma_base_change_map (A B : Type) (e : Equiv A B) (C : B → Type) (u : Σ A (a ↦ C (e .map a)))
  : Id (Σ B C) (sigma_base_change A B e C .map u) (e .map (u .fst), u .snd)
  ≔ equivalence_induction A
      (B e ↦ Σ ((C : B → Type) → Equiv (Σ A (a ↦ C (e .map a))) (Σ B C))
        (s ↦ (C : B → Type) (u : Σ A (a ↦ C (e .map a))) → Id (Σ B C) (s C .map u) (e .map (u .fst), u .snd)))
      ((C ↦ identity_equiv (Σ A C)), (C u ↦ refl u))
      B e .snd C u

def sigma_reindex_map (A B : Type) (e : Equiv A B) (C : B → Type) (u : Σ A (a ↦ C (e .map a))) : Σ B C
  ≔ (e .map (u .fst), u .snd)

def sigma_reindex_inverse (A B : Type) (e : Equiv A B) (C : B → Type) (w : Σ B C) : Σ A (a ↦ C (e .map a))
  ≔ (equiv_inverse_map A B e (w .fst), refl C (equiv_counit A B e (w .fst)) .trl (w .snd))

def sigma_reindex_counit (A B : Type) (e : Equiv A B) (C : B → Type) (w : Σ B C)
  : Id (Σ B C) (sigma_reindex_map A B e C (sigma_reindex_inverse A B e C w)) w
  ≔ (equiv_counit A B e (w .fst), refl C (equiv_counit A B e (w .fst)) .liftl (w .snd))

def sigma_reindex_unit (A B : Type) (e : Equiv A B) (C : B → Type) (u : Σ A (a ↦ C (e .map a)))
  : Id (Σ A (a ↦ C (e .map a))) (sigma_reindex_inverse A B e C (sigma_reindex_map A B e C u)) u
  ≔ let D ≔ Σ A (a ↦ C (e .map a)) in
    let f ≔ sigma_reindex_map A B e C in
    let g ≔ sigma_reindex_inverse A B e C in
    let E ≔ equiv_change_map D (Σ B C) (sigma_base_change A B e C) f (sigma_base_change_map A B e C) in
    let h ≔ equiv_inverse_map D (Σ B C) E in
    concat D (g (f u)) (h (f (g (f u)))) u
      (equiv_unit D (Σ B C) E (g (f u)))
      (concat D (h (f (g (f u)))) (h (f u)) u
        (refl h (sigma_reindex_counit A B e C (f u)))
        (equiv_retraction D (Σ B C) E u))

def sigma_reindex_equiv (A B : Type) (e : Equiv A B) (C : B → Type)
  : Equiv (Σ A (a ↦ C (e .map a))) (Σ B C)
  ≔ quasi_inverse_equiv (Σ A (a ↦ C (e .map a))) (Σ B C)
      (sigma_reindex_map A B e C) (sigma_reindex_inverse A B e C)
      (sigma_reindex_unit A B e C) (sigma_reindex_counit A B e C)

def int_maps_split_reindex_equiv (Y : Type) (F : Equiv Y Y) : Equiv (IntSplit Y F) (IntMaps Y F)
  ≔ compose_equiv (IntSplit Y F)
      (Σ (Product (Nat → Y) (Nat → Y)) (pq ↦ Commutes Int Y int_succ_equiv F (int_cons Y (pq .fst) (pq .snd))))
      (IntMaps Y F)
      (family_equiv (Product (Nat → Y) (Nat → Y)) (pq ↦ IntSplitSteps Y F (pq .fst) (pq .snd))
        (pq ↦ Commutes Int Y int_succ_equiv F (int_cons Y (pq .fst) (pq .snd)))
        (pq ↦ commutes_split_equiv Y F (pq .fst) (pq .snd)))
      (sigma_reindex_equiv (Product (Nat → Y) (Nat → Y)) (Int → Y) (int_fun_split Y) (Commutes Int Y int_succ_equiv F))

def int_maps_evaluation (Y : Type) (F : Equiv Y Y) (f : IntMaps Y F) : Y ≔ f .fst int_zero

{` The same chain as int_maps_equiv, with sigma_reindex_equiv. `}
def int_maps_evaluation_equiv (Y : Type) (F : Equiv Y Y) : Equiv (IntMaps Y F) Y
  ≔ let A0 ≔ IntMaps Y F in let A1 ≔ IntSplit Y F in let A2 ≔ IntSplitCurried Y F in
    let A3 ≔ IntSplitHead Y F in let A4 ≔ IntSplitSeparated Y F in let A5 ≔ IntSplitFibers Y F in
    let e01 ≔ canonical_inverse_equiv A1 A0 (int_maps_split_reindex_equiv Y F) in
    let e12 ≔ int_split_curry_equiv Y F in
    let e23 ≔ canonical_inverse_equiv A3 A2
      (sigma_reindex_equiv (Product Y (Nat → Y)) (Nat → Y) (nat_fun_split Y) (p ↦ Σ (Nat → Y) (q ↦ IntSplitSteps Y F p q))) in
    let e34 ≔ canonical_inverse_equiv A4 A3 (int_split_separate_equiv Y F) in
    let e45 ≔ int_split_fibers_equiv Y F in
    compose_equiv A0 A5 Y
      (compose_equiv A0 A4 A5 (compose_equiv A0 A3 A4 (compose_equiv A0 A2 A3 (compose_equiv A0 A1 A2 e01 e12) e23) e34) e45)
      (int_split_fibers_contract Y F)

{` (g) The map of this equivalence is evaluation at 0, by definition. `}
def int_maps_evaluation_map (Y : Type) (F : Equiv Y Y)
  : Id (IntMaps Y F → Y) (int_maps_evaluation_equiv Y F .map) (int_maps_evaluation Y F)
  ≔ refl (int_maps_evaluation Y F)

{` (h) rem:expforreal at the base point, about the preimage: for every
   circle C, the fiber of exp = fst : Tot(R) → S¹ over base is equivalent
   to ℤ (lem:fst-fiber(a)=B(a) composed with R(base) ≃ ℤ). `}
def exponential_base_preimage (C : CircleSignature)
  : Equiv (BookFiber (Σ (C .carrier) (circle_integer_family C)) (C .carrier) (t ↦ t .fst) (C .base)) Int
  ≔ compose_equiv (BookFiber (Σ (C .carrier) (circle_integer_family C)) (C .carrier) (t ↦ t .fst) (C .base))
      (circle_integer_family C (C .base)) Int
      (projection_book_fiber_equiv (C .carrier) (circle_integer_family C) (C .base))
      (exponential_base_fiber C)
