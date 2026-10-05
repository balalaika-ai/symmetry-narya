export "163-quotient-signatures"

{` The terminology before exa:stuff-struct-prop: f forgets at most
   n-structure when its book fibers are n-truncated, i.e. TruncatedMap
   at h-level n+2; properties are level 1 and nothing is level 0. `}
def projection_book_fiber_equiv (A : Type) (B : A → Type) (a : A)
  : Equiv (BookFiber (Σ A B) A (u ↦ u .fst) a) (B a)
  ≔ native_equivalence (BookFiber (Σ A B) A (u ↦ u .fst) a) (B a) (book_projection_fiber_equiv A B a)

def projection_truncated (level : Nat) (A : Type) (B : A → Type) (h : (a : A) → HLevel level (B a))
  : TruncatedMap level (Σ A B) A (u ↦ u .fst)
  ≔ a ↦ hlevel_equiv level (B a) (BookFiber (Σ A B) A (u ↦ u .fst) a)
      (canonical_inverse_equiv (BookFiber (Σ A B) A (u ↦ u .fst) a) (B a) (projection_book_fiber_equiv A B a))
      (h a)

def projection_fiber_level_reflect (level : Nat) (A : Type) (B : A → Type) (a : A)
  (h : HLevel level (BookFiber (Σ A B) A (u ↦ u .fst) a)) : HLevel level (B a)
  ≔ hlevel_equiv level (BookFiber (Σ A B) A (u ↦ u .fst) a) (B a) (projection_book_fiber_equiv A B a) h

def boolean_finite_set : FiniteSets ≔ (boolean_set, two_element_finite Bool bool_two_element)

def boolean_finite_swap : Id FiniteSets boolean_finite_set boolean_finite_set
  ≔ (boolean_set_swap_pair, prop_family_pathover SetTypes (S ↦ IsFinite (S .fst))
      (S ↦ mere_isprop (Σ Nat (n ↦ Id Type (S .fst) (Fin n))))
      boolean_set boolean_set boolean_set_swap_pair
      (two_element_finite Bool bool_two_element) (two_element_finite Bool bool_two_element))

def finite_sets_not_set (h : isSet FiniteSets) : Empty
  ≔ bool_swap_nontrivial
      (refl ((l ↦ l .fst .fst) : Id FiniteSets boolean_finite_set boolean_finite_set → Id Type Bool Bool)
        (h boolean_finite_set boolean_finite_set boolean_finite_swap (refl boolean_finite_set)))

{` exa:stuff-struct-prop, first item: the first projection of pairs of
   finite sets forgets 1-structure, and not merely structure. `}
def finite_pair_projection : Product FiniteSets FiniteSets → FiniteSets ≔ u ↦ u .fst

def finite_pair_projection_one_truncated
  : TruncatedMap (suc. (suc. (suc. zero.)))
      (Product FiniteSets FiniteSets) FiniteSets finite_pair_projection
  ≔ projection_truncated (suc. (suc. (suc. zero.))) FiniteSets (_ ↦ FiniteSets)
      (_ ↦ groupoid_to_hlevel FiniteSets finite_sets_groupoid)

def finite_pair_projection_not_zero_truncated
  (h : TruncatedMap (suc. (suc. zero.)) (Product FiniteSets FiniteSets) FiniteSets finite_pair_projection)
  : Empty
  ≔ finite_sets_not_set (hlevel_two_to_set FiniteSets
      (projection_fiber_level_reflect (suc. (suc. zero.)) FiniteSets (_ ↦ FiniteSets)
        boolean_finite_set (h boolean_finite_set)))

{` Second item: forgetting the point of a pointed finite set forgets
   structure, and not merely a property. `}
def PointedFiniteSets : Type ≔ Σ FiniteSets (A ↦ A .fst .fst)

def pointed_finite_projection : PointedFiniteSets → FiniteSets ≔ u ↦ u .fst

def pointed_finite_projection_zero_truncated
  : TruncatedMap (suc. (suc. zero.)) PointedFiniteSets FiniteSets pointed_finite_projection
  ≔ projection_truncated (suc. (suc. zero.)) FiniteSets (A ↦ A .fst .fst)
      (A ↦ set_to_hlevel_two (A .fst .fst) (A .fst .snd))

def pointed_finite_projection_not_injective
  (h : TruncatedMap (suc. zero.) PointedFiniteSets FiniteSets pointed_finite_projection) : Empty
  ≔ let hb : isProp Bool ≔ hlevel_one_to_prop Bool
      (projection_fiber_level_reflect (suc. zero.) FiniteSets (A ↦ A .fst .fst)
        boolean_finite_set (h boolean_finite_set)) in
    bool_encode false. true. (hb false. true.)

{` Third item: the inclusion of FinSet_n into FinSet forgets a property,
   and does forget something. `}
def finite_sets_at_witness (n : Nat) (S : SetTypes) (w : Mere (Id Type (Fin n) (S .fst)))
  : IsFinite (S .fst)
  ≔ trunc_map native_truncation (Id Type (Fin n) (S .fst)) (Σ Nat (m ↦ Id Type (S .fst) (Fin m)))
      (p ↦ (n, inverse Type (Fin n) (S .fst) p)) w

def finite_sets_at_inclusion (n : Nat) : FiniteSetsAt n → FiniteSets
  ≔ totalize SetTypes (S ↦ Mere (Id Type (Fin n) (S .fst))) (S ↦ IsFinite (S .fst))
      (finite_sets_at_witness n)

def finite_sets_at_inclusion_injective (n : Nat)
  : TruncatedMap (suc. zero.) (FiniteSetsAt n) FiniteSets (finite_sets_at_inclusion n)
  ≔ a ↦
    let B : SetTypes → Type ≔ S ↦ Mere (Id Type (Fin n) (S .fst)) in
    let C : SetTypes → Type ≔ S ↦ IsFinite (S .fst) in
    let F ≔ BookFiber (B (a .fst)) (C (a .fst)) (finite_sets_at_witness n (a .fst)) (a .snd) in
    hlevel_equiv (suc. zero.) F (BookFiber (FiniteSetsAt n) FiniteSets (finite_sets_at_inclusion n) a)
      (canonical_inverse_equiv (BookFiber (FiniteSetsAt n) FiniteSets (finite_sets_at_inclusion n) a) F
        (total_fiber_equiv SetTypes B C (finite_sets_at_witness n) (a .fst) (a .snd)))
      (prop_to_hlevel_one F
        (sigma_prop (B (a .fst)) (w ↦ Id (C (a .fst)) (a .snd) (finite_sets_at_witness n (a .fst) w))
          (mere_isprop (Id Type (Fin n) (a .fst .fst)))
          (w ↦ prop_is_set (C (a .fst)) (mere_isprop (Σ Nat (m ↦ Id Type (a .fst .fst) (Fin m))))
            (a .snd) (finite_sets_at_witness n (a .fst) w))))

def finite_sets_at_inclusion_not_equivalence (n : Nat)
  (h : TruncatedMap zero. (FiniteSetsAt n) FiniteSets (finite_sets_at_inclusion n)) : Empty
  ≔ let c ≔ h (standard_finite_set (suc. n)) .center in
    let q : Id Type (Fin (suc. n)) (c .fst .fst .fst) ≔ c .snd .fst .fst in
    mere_rec (Id Type (Fin n) (c .fst .fst .fst)) Empty empty_prop
      (p ↦ lt_not_equal n (suc. n) (le_refl (suc. n))
        (fin_path_cardinality n (suc. n)
          (concat Type (Fin n) (c .fst .fst .fst) (Fin (suc. n)) p
            (inverse Type (Fin (suc. n)) (c .fst .fst .fst) q))))
      (c .fst .snd)

{` xca:stuff-struct-prop, further examples: the diagonal of a groupoid
   forgets at most structure (an identification), and for FinSet it
   forgets actual structure. `}
def pair_diagonal (A : Type) (a : A) : Product A A ≔ (a, a)

def pair_diagonal_fiber_equiv (A : Type) (a b : A)
  : Equiv (BookFiber A (Product A A) (pair_diagonal A) (a, b)) (Id A a b)
  ≔ compose_equiv (BookFiber A (Product A A) (pair_diagonal A) (a, b))
      (Σ A (x ↦ Product (Id A a x) (Id A b x))) (Id A a b)
      (family_equiv A (x ↦ Id (Product A A) (a, b) (x, x)) (x ↦ Product (Id A a x) (Id A b x))
        (x ↦ canonical_inverse_equiv (SigmaPath A (_ ↦ A) (a, b) (x, x)) (Id (Product A A) (a, b) (x, x))
          (sigma_path_equiv A (_ ↦ A) (a, b) (x, x))))
      (compose_equiv (Σ A (x ↦ Product (Id A a x) (Id A b x))) (Id A b a) (Id A a b)
        (contract_away_simple A a (x ↦ Id A b x)) (inverse_path_equiv A b a))

def pair_diagonal_groupoid_structure (A : Type) (hA : isGroupoid A)
  : TruncatedMap (suc. (suc. zero.)) A (Product A A) (pair_diagonal A)
  ≔ u ↦ hlevel_equiv (suc. (suc. zero.)) (Id A (u .fst) (u .snd))
      (BookFiber A (Product A A) (pair_diagonal A) u)
      (canonical_inverse_equiv (BookFiber A (Product A A) (pair_diagonal A) u) (Id A (u .fst) (u .snd))
        (pair_diagonal_fiber_equiv A (u .fst) (u .snd)))
      (set_to_hlevel_two (Id A (u .fst) (u .snd)) (hA (u .fst) (u .snd)))

def finite_diagonal_not_injective
  (h : TruncatedMap (suc. zero.) FiniteSets (Product FiniteSets FiniteSets) (pair_diagonal FiniteSets))
  : Empty
  ≔ let b ≔ boolean_finite_set in
    let loops : isProp (Id FiniteSets b b)
      ≔ hlevel_one_to_prop (Id FiniteSets b b)
          (hlevel_equiv (suc. zero.) (BookFiber FiniteSets (Product FiniteSets FiniteSets) (pair_diagonal FiniteSets) (b, b))
            (Id FiniteSets b b) (pair_diagonal_fiber_equiv FiniteSets b b) (h (b, b))) in
    bool_swap_nontrivial
      (refl ((l ↦ l .fst .fst) : Id FiniteSets b b → Id Type Bool Bool)
        (loops boolean_finite_swap (refl b)))

{` xca:0Im-to-Im. The map ‖_‖' from the set truncation of a fiber to its
   propositional truncation, and the second map of the refined image
   factorization. Its fiber at (a,p) is the set truncation of the fiber. `}
def set_to_prop_trunc (A : Type) : SetTrunc A → Mere A
  ≔ set_trunc_rec A (Mere A) (prop_is_set (Mere A) (mere_isprop A)) (mere A)

def zero_image_to_image (A B : Type) (f : A → B) : ZeroImage A B f → Image A B f
  ≔ totalize B (b ↦ SetTrunc (BookFiber A B f b)) (b ↦ Mere (BookFiber A B f b))
      (b ↦ set_to_prop_trunc (BookFiber A B f b))

def zero_image_to_image_fiber_equiv (A B : Type) (f : A → B) (b : B) (p : Mere (BookFiber A B f b))
  : Equiv (BookFiber (ZeroImage A B f) (Image A B f) (zero_image_to_image A B f) (b, p))
      (SetTrunc (BookFiber A B f b))
  ≔ let F ≔ BookFiber A B f b in
    compose_equiv (BookFiber (ZeroImage A B f) (Image A B f) (zero_image_to_image A B f) (b, p))
      (BookFiber (SetTrunc F) (Mere F) (set_to_prop_trunc F) p) (SetTrunc F)
      (total_fiber_equiv B (b ↦ SetTrunc (BookFiber A B f b)) (b ↦ Mere (BookFiber A B f b))
        (b ↦ set_to_prop_trunc (BookFiber A B f b)) b p)
      (contractible_fiber_projection (SetTrunc F) (x ↦ Id (Mere F) p (set_to_prop_trunc F x))
        (x ↦ prop_paths_contractible (Mere F) (mere_isprop F) p (set_to_prop_trunc F x)))

{` What is forgotten: at most structure, since the fibers are sets; and
   it is pure structure, since every fiber is non-empty. `}
def zero_image_to_image_zero_truncated (A B : Type) (f : A → B)
  : TruncatedMap (suc. (suc. zero.)) (ZeroImage A B f) (Image A B f) (zero_image_to_image A B f)
  ≔ u ↦ hlevel_equiv (suc. (suc. zero.)) (SetTrunc (BookFiber A B f (u .fst)))
      (BookFiber (ZeroImage A B f) (Image A B f) (zero_image_to_image A B f) u)
      (canonical_inverse_equiv (BookFiber (ZeroImage A B f) (Image A B f) (zero_image_to_image A B f) u)
        (SetTrunc (BookFiber A B f (u .fst))) (zero_image_to_image_fiber_equiv A B f (u .fst) (u .snd)))
      (set_to_hlevel_two (SetTrunc (BookFiber A B f (u .fst))) (set_trunc_set (BookFiber A B f (u .fst))))

def zero_image_to_image_surjective (A B : Type) (f : A → B)
  : Surjective (ZeroImage A B f) (Image A B f) (zero_image_to_image A B f)
  ≔ u ↦
    let F ≔ BookFiber A B f (u .fst) in
    let G ≔ BookFiber (ZeroImage A B f) (Image A B f) (zero_image_to_image A B f) u in
    trunc_map native_truncation F G
      (x ↦ equiv_inverse_map G (SetTrunc F) (zero_image_to_image_fiber_equiv A B f (u .fst) (u .snd))
        (set_trunc F x)) (u .snd)
