export "192-propositional-resizing"

{` pri:replacement, as a type used as a hypothesis. `}
def Replacement (U : Universe) : Type
  ≔ (A B : Type) (f : A → B) → EssentiallySmall U A → LocallySmall U B → EssentiallySmall U (Image A B f)

def replacement_prop (U : Universe) : isProp (Replacement U)
  ≔ pi_prop Type (A ↦ (B : Type) (f : A → B) → EssentiallySmall U A → LocallySmall U B → EssentiallySmall U (Image A B f))
      (A ↦ pi_prop Type (B ↦ (f : A → B) → EssentiallySmall U A → LocallySmall U B → EssentiallySmall U (Image A B f))
        (B ↦ pi_prop (A → B) (f ↦ EssentiallySmall U A → LocallySmall U B → EssentiallySmall U (Image A B f))
          (f ↦ pi_prop (EssentiallySmall U A) (_ ↦ LocallySmall U B → EssentiallySmall U (Image A B f))
            (_ ↦ pi_prop (LocallySmall U B) (_ ↦ EssentiallySmall U (Image A B f))
              (_ ↦ essentially_small_prop U (Image A B f))))))

{` In the universe of all types the principle holds trivially. `}
def total_replacement : Replacement total_universe
  ≔ A B f _ _ ↦ small_essentially_small total_universe (Image A B f) star.

{` xca:comp-loc-small-ess-small. `}
def component_image_equiv (A : Type) (a : A) : Equiv (Image Unit A (_ ↦ a)) (NativeComponent A a)
  ≔ family_equiv A (x ↦ Mere (BookFiber Unit A (_ ↦ a) x)) (x ↦ Mere (Id A a x))
      (x ↦ iff_equiv (Mere (BookFiber Unit A (_ ↦ a) x)) (Mere (Id A a x))
        (mere_isprop (BookFiber Unit A (_ ↦ a) x)) (mere_isprop (Id A a x))
        (trunc_map native_truncation (BookFiber Unit A (_ ↦ a) x) (Id A a x) (w ↦ inverse A x a (w .snd)))
        (trunc_map native_truncation (Id A a x) (BookFiber Unit A (_ ↦ a) x) (p ↦ (star., inverse A a x p))))

def component_essentially_small (U : Universe) (rep : Replacement U) (A : Type) (hA : LocallySmall U A) (a : A)
  : EssentiallySmall U (NativeComponent A a)
  ≔ essentially_small_equiv U (Image Unit A (_ ↦ a)) (NativeComponent A a) (component_image_equiv A a)
      (rep Unit A (_ ↦ a) (small_essentially_small U Unit (U .unit_small)) hA)

{` The type of finite sets is the image of Fin : N → U, hence essentially small. `}
def fin_small (U : Universe) (n : Nat) : U .small (Fin n)
  ≔ match n [ zero. ↦ U .empty_small | suc. n ↦ U .sum_small (Fin n) Unit (fin_small U n) (U .unit_small) ]

def fin_code (U : Universe) (n : Nat) : UniverseType U ≔ (Fin n, fin_small U n)

def finite_small (U : Universe) (A : Type) (h : IsFinite A) : U .small A
  ≔ mere_rec (Σ Nat (n ↦ Id Type A (Fin n))) (U .small A) (U .small_prop A)
      (w ↦ transport Type (U .small) (Fin (w .fst)) A (inverse Type A (Fin (w .fst)) (w .snd)) (fin_small U (w .fst))) h

def fin_image_finite_sets (U : Universe) : Equiv (Image Nat (UniverseType U) (fin_code U)) FiniteSets
  ≔ let I ≔ Image Nat (UniverseType U) (fin_code U) in
    let F ≔ ((X ↦ BookFiber Nat (UniverseType U) (fin_code U) X) : UniverseType U → Type) in
    let to ≔ ((v ↦ ((v .fst .fst,
        mere_rec (F (v .fst)) (isSet (v .fst .fst)) (isset_isprop (v .fst .fst))
          (w ↦ transport Type isSet (Fin (w .fst)) (v .fst .fst) (inverse Type (v .fst .fst) (Fin (w .fst)) (w .snd .fst))
            (fin_set (w .fst))) (v .snd)),
        trunc_map native_truncation (F (v .fst)) (Σ Nat (n ↦ Id Type (v .fst .fst) (Fin n))) (w ↦ (w .fst, w .snd .fst)) (v .snd)))
      : I → FiniteSets) in
    let from ≔ ((S ↦ let X : UniverseType U ≔ (S .fst .fst, finite_small U (S .fst .fst) (S .snd)) in
        (X, trunc_map native_truncation (Σ Nat (n ↦ Id Type (S .fst .fst) (Fin n))) (F X)
          (w ↦ (w .fst, subtype_equal Type (U .small) (U .small_prop) X (fin_code U (w .fst)) (w .snd))) (S .snd)))
      : FiniteSets → I) in
    quasi_inverse_equiv I FiniteSets to from
      (v ↦ subtype_equal (UniverseType U) (X ↦ Mere (F X)) (X ↦ mere_isprop (F X)) (from (to v)) v
        (subtype_equal Type (U .small) (U .small_prop) (from (to v) .fst) (v .fst) (refl (v .fst .fst))))
      (S ↦ subtype_equal SetTypes (T ↦ IsFinite (T .fst)) (T ↦ mere_isprop (Σ Nat (n ↦ Id Type (T .fst) (Fin n))))
        (to (from S)) S (subtype_equal Type isSet isset_isprop (to (from S) .fst) (S .fst) (refl (S .fst .fst))))

def finite_sets_essentially_small (U : Universe) (rep : Replacement U) : EssentiallySmall U FiniteSets
  ≔ essentially_small_equiv U (Image Nat (UniverseType U) (fin_code U)) FiniteSets (fin_image_finite_sets U)
      (rep Nat (UniverseType U) (fin_code U) (small_essentially_small U Nat (U .nat_small)) (universe_locally_small U))

{` The exercise at the end of the section on types and maps. `}
def EssentiallySmallTypes (N : NestedUniverses) : Type
  ≔ Σ (UniverseType (N .upper)) (A ↦ EssentiallySmall (N .lower) (A .fst))

def upper_equiv_singleton (N : NestedUniverses) (X : UniverseType (N .lower))
  : isContr (Σ (UniverseType (N .upper)) (A ↦ Equiv (A .fst) (X .fst)))
  ≔ let T0 ≔ Σ Type (A ↦ Equiv A (X .fst)) in
    let h0 : isContr T0 ≔ hlevel_equiv zero. (Σ Type (A ↦ Id Type A (X .fst))) T0
      (family_equiv Type (A ↦ Id Type A (X .fst)) (A ↦ Equiv A (X .fst)) (A ↦ univalence_equiv A (X .fst)))
      (path_to_contractible Type (X .fst)) in
    let small_at ≔ ((p ↦ small_equiv (N .upper) (X .fst) (p .fst) (canonical_inverse_equiv (p .fst) (X .fst) (p .snd))
        (N .cumulative (X .fst) (X .snd))) : (p : T0) → N .upper .small (p .fst)) in
    hlevel_equiv zero. (Σ T0 (p ↦ N .upper .small (p .fst))) (Σ (UniverseType (N .upper)) (A ↦ Equiv (A .fst) (X .fst)))
      (quasi_inverse_equiv (Σ T0 (p ↦ N .upper .small (p .fst))) (Σ (UniverseType (N .upper)) (A ↦ Equiv (A .fst) (X .fst)))
        (t ↦ ((t .fst .fst, t .snd), t .fst .snd)) (t ↦ ((t .fst .fst, t .snd), t .fst .snd)) (t ↦ refl t) (t ↦ refl t))
      (sigma_contractible T0 (p ↦ N .upper .small (p .fst)) h0
        (p ↦ (small_at p, s ↦ N .upper .small_prop (p .fst) s (small_at p))))

{` Projection to the U-type is an equivalence (Σ_{A:U'} S(A)) ≃ U. `}
def essentially_small_types_equiv (N : NestedUniverses) : Equiv (EssentiallySmallTypes N) (UniverseType (N .lower))
  ≔ quasi_inverse_equiv (EssentiallySmallTypes N) (UniverseType (N .lower))
      (v ↦ v .snd .fst)
      (X ↦ ((X .fst, N .cumulative (X .fst) (X .snd)), (X, identity_equiv (X .fst))))
      (v ↦ let X ≔ v .snd .fst in
        let E ≔ Σ (UniverseType (N .upper)) (A ↦ Equiv (A .fst) (X .fst)) in
        refl ((p ↦ (p .fst, (X, p .snd))) : E → EssentiallySmallTypes N)
          (contractible_prop E (upper_equiv_singleton N X)
            ((X .fst, N .cumulative (X .fst) (X .snd)), identity_equiv (X .fst)) (v .fst, v .snd .snd)))
      (X ↦ refl X)

def upper_small_of_small_fibers (N : NestedUniverses) (A : UniverseType (N .upper)) (B : Type) (f : B → A .fst)
  (s : (a : A .fst) → N .lower .small (BookFiber B (A .fst) f a)) : N .upper .small B
  ≔ small_equiv (N .upper) (Σ (A .fst) (a ↦ BookFiber B (A .fst) f a)) B (sum_of_fibers_equiv B (A .fst) f)
      (N .upper .sigma_small (A .fst) (a ↦ BookFiber B (A .fst) f a) (A .snd)
        (a ↦ N .cumulative (BookFiber B (A .fst) f a) (s a)))

def maps_small_fibers_equiv (N : NestedUniverses) (A : UniverseType (N .upper))
  : Equiv (Σ Type (B ↦ Σ (B → A .fst) (f ↦ (a : A .fst) → N .lower .small (BookFiber B (A .fst) f a))))
      (Σ (UniverseType (N .upper)) (B ↦ Σ (B .fst → A .fst) (f ↦ (a : A .fst) → EssentiallySmall (N .lower) (BookFiber (B .fst) (A .fst) f a))))
  ≔ let L ≔ N .lower in let V ≔ N .upper in
    let S1 ≔ Σ Type (B ↦ Σ (B → A .fst) (f ↦ (a : A .fst) → L .small (BookFiber B (A .fst) f a))) in
    let S2 ≔ Σ (UniverseType V) (B ↦ Σ (B .fst → A .fst) (f ↦ (a : A .fst) → EssentiallySmall L (BookFiber (B .fst) (A .fst) f a))) in
    let to ≔ ((t ↦ ((t .fst, upper_small_of_small_fibers N A (t .fst) (t .snd .fst) (t .snd .snd)),
        (t .snd .fst, a ↦ small_essentially_small L (BookFiber (t .fst) (A .fst) (t .snd .fst) a) (t .snd .snd a)))) : S1 → S2) in
    let from ≔ ((u ↦ (u .fst .fst, (u .snd .fst,
        a ↦ essentially_small_is_small L (BookFiber (u .fst .fst) (A .fst) (u .snd .fst) a) (u .snd .snd a)))) : S2 → S1) in
    quasi_inverse_equiv S1 S2 to from
      (t ↦ (refl (t .fst), (refl (t .snd .fst),
        pi_prop (A .fst) (a ↦ L .small (BookFiber (t .fst) (A .fst) (t .snd .fst) a))
          (a ↦ L .small_prop (BookFiber (t .fst) (A .fst) (t .snd .fst) a)) (from (to t) .snd .snd) (t .snd .snd))))
      (u ↦ ((refl (u .fst .fst), V .small_prop (u .fst .fst) (to (from u) .fst .snd) (u .fst .snd)),
        (refl (u .snd .fst),
          pi_prop (A .fst) (a ↦ EssentiallySmall L (BookFiber (u .fst .fst) (A .fst) (u .snd .fst) a))
            (a ↦ essentially_small_prop L (BookFiber (u .fst .fst) (A .fst) (u .snd .fst) a))
            (to (from u) .snd .snd) (u .snd .snd))))

{` Families of U-small types over A : U' correspond to maps into A in U'
   with essentially U-small fibers. `}
def small_families_maps_equiv (N : NestedUniverses) (A : UniverseType (N .upper))
  : Equiv (A .fst → UniverseType (N .lower))
      (Σ (UniverseType (N .upper)) (B ↦ Σ (B .fst → A .fst)
        (f ↦ (a : A .fst) → EssentiallySmall (N .lower) (BookFiber (B .fst) (A .fst) f a))))
  ≔ compose_equiv (A .fst → UniverseType (N .lower))
      (Σ Type (B ↦ Σ (B → A .fst) (f ↦ (a : A .fst) → N .lower .small (BookFiber B (A .fst) f a))))
      (Σ (UniverseType (N .upper)) (B ↦ Σ (B .fst → A .fst)
        (f ↦ (a : A .fst) → EssentiallySmall (N .lower) (BookFiber (B .fst) (A .fst) f a))))
      (structured_families_equiv (A .fst) (N .lower .small)) (maps_small_fibers_equiv N A)

{` Footnote to def:quotient-set: A/R is essentially U-small by replacement,
   for A : U and R with values in Prop_U. `}
def relation_small_props (U : Universe) (A : Type) (R : EquivalenceRelation A)
  (hR : (x y : A) → U .small (R .predicate x y .fst)) (x y : A) : PropU U
  ≔ ((R .predicate x y .fst, hR x y), R .predicate x y .snd)

def forget_small_props (U : Universe) (A : Type) (Q : A → PropU U) : A → PropTypes
  ≔ x ↦ (Q x .fst .fst, Q x .snd)

def quotient_small_image_equiv (U : Universe) (A : Type) (R : EquivalenceRelation A)
  (hR : (x y : A) → U .small (R .predicate x y .fst))
  : Equiv (Image A (A → PropU U) (relation_small_props U A R hR)) (Quotient A R)
  ≔ let RU ≔ relation_small_props U A R hR in
    let I ≔ Image A (A → PropU U) RU in
    let FU ≔ ((Q ↦ BookFiber A (A → PropU U) RU Q) : (A → PropU U) → Type) in
    let FP ≔ ((P ↦ BookFiber A (A → PropTypes) (R .predicate) P) : (A → PropTypes) → Type) in
    let forget ≔ forget_small_props U A in
    let small_of ≔ ((u x ↦ mere_rec (FP (u .fst)) (U .small (u .fst x .fst)) (U .small_prop (u .fst x .fst))
        (w ↦ transport Type (U .small) (R .predicate (w .fst) x .fst) (u .fst x .fst)
          (inverse Type (u .fst x .fst) (R .predicate (w .fst) x .fst)
            (refl ((P ↦ P x .fst) : (A → PropTypes) → Type) (w .snd))) (hR (w .fst) x)) (u .snd))
      : (u : Quotient A R) (x : A) → U .small (u .fst x .fst)) in
    let lift ≔ ((u ↦ ((x ↦ ((u .fst x .fst, small_of u x), u .fst x .snd)) : A → PropU U))
      : Quotient A R → A → PropU U) in
    let to ≔ ((v ↦ (forget (v .fst), trunc_map native_truncation (FU (v .fst)) (FP (forget (v .fst)))
        (w ↦ (w .fst, refl forget (w .snd))) (v .snd))) : I → Quotient A R) in
    let from ≔ ((u ↦ (lift u, trunc_map native_truncation (FP (u .fst)) (FU (lift u))
        (w ↦ (w .fst, funext A (_ ↦ PropU U) (lift u) (RU (w .fst))
          (x ↦ subtype_equal (UniverseType U) (X ↦ isProp (X .fst)) (X ↦ isprop_isprop (X .fst)) (lift u x) (RU (w .fst) x)
            (subtype_equal Type (U .small) (U .small_prop) (lift u x .fst) (RU (w .fst) x .fst)
              (refl ((P ↦ P x .fst) : (A → PropTypes) → Type) (w .snd)))))) (u .snd))) : Quotient A R → I) in
    quasi_inverse_equiv I (Quotient A R) to from
      (v ↦ subtype_equal (A → PropU U) (Q ↦ Mere (FU Q)) (Q ↦ mere_isprop (FU Q)) (from (to v)) v
        (funext A (_ ↦ PropU U) (from (to v) .fst) (v .fst)
          (x ↦ subtype_equal (UniverseType U) (X ↦ isProp (X .fst)) (X ↦ isprop_isprop (X .fst)) (from (to v) .fst x) (v .fst x)
            (subtype_equal Type (U .small) (U .small_prop) (from (to v) .fst x .fst) (v .fst x .fst) (refl (v .fst x .fst .fst))))))
      (u ↦ subtype_equal (A → PropTypes) (P ↦ Mere (FP P)) (P ↦ mere_isprop (FP P)) (to (from u)) u (refl (u .fst)))

def quotient_essentially_small (U : Universe) (rep : Replacement U) (A : Type) (sA : U .small A)
  (R : EquivalenceRelation A) (hR : (x y : A) → U .small (R .predicate x y .fst))
  : EssentiallySmall U (Quotient A R)
  ≔ essentially_small_equiv U (Image A (A → PropU U) (relation_small_props U A R hR)) (Quotient A R)
      (quotient_small_image_equiv U A R hR)
      (rep A (A → PropU U) (relation_small_props U A R hR) (small_essentially_small U A sA)
        (pi_locally_small U A sA (_ ↦ PropU U) (_ ↦ prop_u_locally_small U)))

{` The alternative in the same footnote: resizing pushes the values of R down. `}
def resized_relation (N : NestedUniverses) (r : PropositionalResizing N) (A : Type) (R : A → A → PropU (N .upper))
  (x y : A) : PropU (N .lower)
  ≔ equiv_inverse_map (PropU (N .lower)) (PropU (N .upper))
      (native_equivalence (PropU (N .lower)) (PropU (N .upper)) (prop_inclusion N, r)) (R x y)

def resized_relation_beta (N : NestedUniverses) (r : PropositionalResizing N) (A : Type) (R : A → A → PropU (N .upper))
  (x y : A) : Id (PropU (N .upper)) (prop_inclusion N (resized_relation N r A R x y)) (R x y)
  ≔ equiv_counit (PropU (N .lower)) (PropU (N .upper))
      (native_equivalence (PropU (N .lower)) (PropU (N .upper)) (prop_inclusion N, r)) (R x y)

{` Footnote to rem:set-trunc-as-quotient: the 0-truncation of A : U is the
   U-small image of the (-1)-truncated identity relation. `}
def set_trunc_essentially_small (U : Universe) (rep : Replacement U) (A : Type) (sA : U .small A)
  : EssentiallySmall U (SetTrunc A)
  ≔ quotient_essentially_small U rep A sA (mere_path_relation A)
      (x y ↦ U .trunc_small (Id A x y) (U .id_small A sA x y))
