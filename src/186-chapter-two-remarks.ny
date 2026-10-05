export "185-native-truncation-logic"

{` rem:iterated-sums: the triple (x,y,z) is (x,(y,z)); for a family over the
   pairs, ((x,y),z) is identified with it by reassociation. `}
def triple (X : Type) (Y : X → Type) (Z : (x : X) → Y x → Type) (x : X) (y : Y x) (z : Z x y)
  : Σ X (x ↦ Σ (Y x) (Z x))
  ≔ (x, (y, z))

def triple_reassociation (X : Type) (Y : X → Type) (Z : (x : X) → Y x → Type) (x : X) (y : Y x) (z : Z x y)
  : Id (Σ X (x ↦ Σ (Y x) (Z x))) (sigma_assoc X Y Z .map ((x, y), z)) (triple X Y Z x y z)
  ≔ refl (triple X Y Z x y z)

{` def:groupoidFin, footnote: with identifications taken in Set, FinSet_n is
   by definition the component Set_(Fin n). `}
def BookFiniteSetsAt (n : Nat) : Type ≔ Σ SetTypes (S ↦ Mere (Id SetTypes (Fin n, fin_set n) S))

def book_finite_sets_at_component (n : Nat)
  : Id Type (BookFiniteSetsAt n) (NativeComponent SetTypes (Fin n, fin_set n))
  ≔ refl (BookFiniteSetsAt n)

def book_finite_sets_at_equiv (n : Nat) : Equiv (BookFiniteSetsAt n) (FiniteSetsAt n)
  ≔ canonical_inverse_equiv (FiniteSetsAt n) (BookFiniteSetsAt n) (finite_sets_at_set_component n)

def book_finite_sets_at_finite_path (n : Nat)
  : Id Type (BookFiniteSetsAt n) (NativeComponent FiniteSets (standard_finite_set n))
  ≔ ua (BookFiniteSetsAt n) (NativeComponent FiniteSets (standard_finite_set n))
      (compose_equiv (BookFiniteSetsAt n) (FiniteSetsAt n) (NativeComponent FiniteSets (standard_finite_set n))
        (book_finite_sets_at_equiv n) (finite_sets_at_finite_component n))

def book_finite_sets_at_universe_path (n : Nat)
  : Id Type (BookFiniteSetsAt n) (NativeComponent Type (Fin n))
  ≔ ua (BookFiniteSetsAt n) (NativeComponent Type (Fin n))
      (compose_equiv (BookFiniteSetsAt n) (FiniteSetsAt n) (NativeComponent Type (Fin n))
        (book_finite_sets_at_equiv n) (finite_sets_at_universe_component n))

{` xca:stuff-struct-prop, further examples. `}
def hlevel_one_fiber_prop (A : Type) (B : A → Type) (h : TruncatedMap (suc. zero.) (Σ A B) A (u ↦ u .fst)) (a : A)
  : isProp (B a)
  ≔ hlevel_one_to_prop (B a)
      (hlevel_equiv (suc. zero.) (BookFiber (Σ A B) A (u ↦ u .fst) a) (B a) (projection_book_fiber_equiv A B a) (h a))

def hlevel_two_fiber_set (A : Type) (B : A → Type) (h : TruncatedMap (suc. (suc. zero.)) (Σ A B) A (u ↦ u .fst)) (a : A)
  : isSet (B a)
  ≔ hlevel_two_to_set (B a)
      (hlevel_equiv (suc. (suc. zero.)) (BookFiber (Σ A B) A (u ↦ u .fst) a) (B a) (projection_book_fiber_equiv A B a) (h a))

{` Forgetting that a permutation is cyclic forgets at most properties. `}
def cycles_forget_properties : TruncatedMap (suc. zero.) Cycles Permutations (c ↦ c .fst)
  ≔ projection_truncated (suc. zero.) Permutations (p ↦ Cyclic (p .fst .fst) (p .snd))
      (p ↦ prop_to_hlevel_one (Cyclic (p .fst .fst) (p .snd)) (cyclic_prop (p .fst .fst) (p .snd)))

{` Forgetting sethood forgets at most properties. `}
def sets_forget_properties : TruncatedMap (suc. zero.) SetTypes Type (S ↦ S .fst)
  ≔ projection_truncated (suc. zero.) Type isSet (A ↦ prop_to_hlevel_one (isSet A) (isset_isprop A))

{` Forgetting the permutation of a set forgets at most structure, and not only properties. `}
def permutations_forget_structure : TruncatedMap (suc. (suc. zero.)) Permutations SetTypes (p ↦ p .fst)
  ≔ projection_truncated (suc. (suc. zero.)) SetTypes (S ↦ Equiv (S .fst) (S .fst))
      (S ↦ set_to_hlevel_two (Equiv (S .fst) (S .fst)) (equivalences_set (S .fst) (S .fst) (S .snd)))

{` Proved by evaluating two points of the fibre through .trl rather than via
   ua of projection_book_fiber_equiv, which raises bug[E0500] in Narya efafad2
   (see docs/narya-notes.md). `}
def permutations_forget_not_properties
  (h : TruncatedMap (suc. zero.) Permutations SetTypes (p ↦ p .fst)) : Empty
  ≔ let S ≔ ((X ↦ Equiv (X .fst) (X .fst)) : SetTypes → Type) in
    let F ≔ BookFiber Permutations SetTypes (p ↦ p .fst) boolean_set in
    let at_true : F → Bool ≔ t ↦ refl S (t .snd) .trl (t .fst .snd) .map true. in
    let t0 ≔ refl Bool .trr true. in
    let back ≔ inverse Bool true. t0 (refl Bool .liftr true.) in
    bool_encode true. false.
      (calc
        (true. : Bool)
        = refl Bool .trl t0
          by concat Bool (refl Bool .trl t0) t0 true. (refl Bool .liftl t0) back
        = refl Bool .trl (bool_not t0)
          by refl at_true
               (hlevel_one_to_prop F (h boolean_set)
                  ((boolean_set, identity_equiv Bool), refl boolean_set)
                  ((boolean_set, bool_not_equiv), refl boolean_set))
        = false.
          by concat Bool (refl Bool .trl (bool_not t0)) (bool_not t0) false.
               (refl Bool .liftl (bool_not t0)) (refl bool_not back) ∎)

{` Forgetting the point of a pointed type does not forget at most structure:
   its fibers are the types themselves, and the fiber over Set is not a set.
   (It does not forget at most stuff either in general, since Type is not a
   groupoid; the groupoid examples of xca:stuff-struct-prop are in module 284.) `}
def pointed_types_forget_not_structure
  (h : TruncatedMap (suc. (suc. zero.)) PointedTypes Type (X ↦ X .fst)) : Empty
  ≔ let hs ≔ hlevel_two_fiber_set Type (A ↦ A) h SetTypes in
    bool_swap_nontrivial
      (refl ((l ↦ l .fst) : Id SetTypes boolean_set boolean_set → Id Type Bool Bool)
        (hs boolean_set boolean_set boolean_set_swap_pair (refl boolean_set)))
