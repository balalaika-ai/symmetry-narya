export "42-quotient-induction"

def mere_path_relation (A : Type) : EquivalenceRelation A
  ≔ ((x y ↦ (Mere (Id A x y), mere_isprop (Id A x y))),
      (x ↦ mere (Id A x x) (refl x)),
      (x y ↦ trunc_map native_truncation (Id A x y) (Id A y x) (inverse A x y)),
      (x y z p q ↦ mere_rec (Id A x y) (Mere (Id A x z)) (mere_isprop (Id A x z))
        (r ↦ trunc_map native_truncation (Id A y z) (Id A x z) (concat A x y z r) q) p))

{` rem:set-trunc-as-quotient, in the native single universe. `}
def SetTrunc (A : Type) : Type ≔ Quotient A (mere_path_relation A)
def set_trunc (A : Type) : A → SetTrunc A ≔ quotient_class A (mere_path_relation A)
def set_trunc_set (A : Type) : isSet (SetTrunc A) ≔ quotient_set A (mere_path_relation A)
def set_trunc_surjective (A : Type) : Surjective A (SetTrunc A) (set_trunc A)
  ≔ quotient_surjective A (mere_path_relation A)

def set_trunc_paths (A : Type) (x y : A)
  : Equiv (Id (SetTrunc A) (set_trunc A x) (set_trunc A y)) (Mere (Id A x y))
  ≔ quotient_effective A (mere_path_relation A) x y

def set_trunc_respects (A B : Type) (hb : isSet B) (f : A → B)
  : Respects A B (mere_path_relation A) f
  ≔ x y ↦ mere_rec (Id A x y) (Id B (f x) (f y)) (hb (f x) (f y)) (map_path A B f x y)

def set_trunc_rec (A B : Type) (hb : isSet B) (f : A → B) : SetTrunc A → B
  ≔ quotient_rec A B (mere_path_relation A) hb f (set_trunc_respects A B hb f)

def set_trunc_rec_beta (A B : Type) (hb : isSet B) (f : A → B) (a : A)
  : Id B (set_trunc_rec A B hb f (set_trunc A a)) (f a) ≔ refl (f a)

def set_trunc_rec_eta (A B : Type) (hb : isSet B) (g : SetTrunc A → B)
  : Id (SetTrunc A → B) (set_trunc_rec A B hb (a ↦ g (set_trunc A a))) g
  ≔ quotient_lifts_prop A B (mere_path_relation A) hb (a ↦ g (set_trunc A a))
      (set_trunc_rec A B hb (a ↦ g (set_trunc A a)), refl (a ↦ g (set_trunc A a)))
      (g, refl (a ↦ g (set_trunc A a))) .fst

def set_trunc_universal_property (A B : Type) (hb : isSet B)
  : BookEquiv (SetTrunc A → B) (A → B)
  ≔ book_quasi_inverse_equiv (SetTrunc A → B) (A → B)
      (g a ↦ g (set_trunc A a)) (set_trunc_rec A B hb) (set_trunc_rec_eta A B hb) (f ↦ refl f)

def set_trunc_boundary (A : Type) (S : SetTrunc A → Type) (hs : (z : SetTrunc A) → isSet (S z))
  (b : (a : A) → S (set_trunc A a)) : QuotientBoundary A (mere_path_relation A) S b
  ≔ x y r ↦
    let q ≔ quotient_encode A (mere_path_relation A) x y r in
    mere_rec (Id A x y) (Id S q (b x) (b y))
      (hlevel_one_to_prop (Id S q (b x) (b y))
        (pathover_hlevel (suc. zero.) (SetTrunc A) S (z ↦ set_to_hlevel_two (S z) (hs z))
          (set_trunc A x) (set_trunc A y) q (b x) (b y)))
      (p ↦ transport (Id (SetTrunc A) (set_trunc A x) (set_trunc A y))
        (v ↦ Id S v (b x) (b y)) (map_path A (SetTrunc A) (set_trunc A) x y p) q
        (set_trunc_set A (set_trunc A x) (set_trunc A y) (map_path A (SetTrunc A) (set_trunc A) x y p) q)
        (refl b p)) r

def set_trunc_induction (A : Type) (S : SetTrunc A → Type) (hs : (z : SetTrunc A) → isSet (S z))
  (b : (a : A) → S (set_trunc A a)) : (z : SetTrunc A) → S z
  ≔ quotient_induction A (mere_path_relation A) S hs b (set_trunc_boundary A S hs b)

def set_trunc_induction_beta (A : Type) (S : SetTrunc A → Type) (hs : (z : SetTrunc A) → isSet (S z))
  (b : (a : A) → S (set_trunc A a)) (a : A)
  : Id (S (set_trunc A a)) (set_trunc_induction A S hs b (set_trunc A a)) (b a)
  ≔ quotient_induction_beta A (mere_path_relation A) S hs b (set_trunc_boundary A S hs b) a

{` xca:sum-of-conn-components. At set_trunc a this is definitionally NativeComponent A a. `}
def TruncatedComponent (A : Type) (z : SetTrunc A) : Type ≔ Σ A (a ↦ z .fst a .fst)

def truncated_component_at_point (A : Type) (a : A)
  : Id Type (TruncatedComponent A (set_trunc A a)) (NativeComponent A a) ≔ refl (NativeComponent A a)

def truncated_component_fiber_equiv (A : Type) (z : SetTrunc A)
  : Equiv (TruncatedComponent A z) (BookFiber A (SetTrunc A) (set_trunc A) z)
  ≔ family_equiv A (a ↦ z .fst a .fst) (a ↦ Id (SetTrunc A) z (set_trunc A a))
      (a ↦ canonical_inverse_equiv (Id (SetTrunc A) z (set_trunc A a)) (z .fst a .fst)
        (quotient_class_property A (mere_path_relation A) z a))

def components_total_equiv (A : Type) : Equiv (Σ (SetTrunc A) (TruncatedComponent A)) A
  ≔ compose_equiv (Σ (SetTrunc A) (TruncatedComponent A))
      (Σ (SetTrunc A) (BookFiber A (SetTrunc A) (set_trunc A))) A
      (family_equiv (SetTrunc A) (TruncatedComponent A) (BookFiber A (SetTrunc A) (set_trunc A))
        (truncated_component_fiber_equiv A))
      (sum_of_fibers_equiv A (SetTrunc A) (set_trunc A))

def components_decomposition (A : Type) : Equiv A (Σ (SetTrunc A) (TruncatedComponent A))
  ≔ let into ≔ (a ↦ (set_trunc A a, (a, mere (Id A a a) (refl a)))) : A → Σ (SetTrunc A) (TruncatedComponent A) in
    quasi_inverse_equiv A (Σ (SetTrunc A) (TruncatedComponent A)) into (t ↦ t .snd .fst)
      (a ↦ refl a)
      (t ↦ equivalence_injective (Σ (SetTrunc A) (TruncatedComponent A)) A (components_total_equiv A)
        (into (t .snd .fst)) t (refl (t .snd .fst)))

def connected_isprop (A : Type) : isProp (Connected A)
  ≔ product_prop (Mere A) ((x y : A) → Mere (Id A x y)) (mere_isprop A)
      (pi_prop A (x ↦ (y : A) → Mere (Id A x y))
        (x ↦ pi_prop A (y ↦ Mere (Id A x y)) (y ↦ mere_isprop (Id A x y))))

def connected_set_trunc_contractible (A : Type) (h : Connected A) : BookIsContr (SetTrunc A)
  ≔ connected_set_contractible native_truncation (SetTrunc A)
      (surjection_preserves_connected native_truncation A (SetTrunc A) (set_trunc A) h (set_trunc_surjective A))
      (set_trunc_set A)

def contractible_set_trunc_connected (A : Type) (h : BookIsContr (SetTrunc A)) : Connected A
  ≔ (trunc_map native_truncation (BookFiber A (SetTrunc A) (set_trunc A) (h .center)) A
        (w ↦ w .fst) (set_trunc_surjective A (h .center)),
      x y ↦ set_trunc_paths A x y .map
        (concat (SetTrunc A) (set_trunc A x) (h .center) (set_trunc A y)
          (inverse (SetTrunc A) (h .center) (set_trunc A x) (h .contract (set_trunc A x)))
          (h .contract (set_trunc A y))))

def connected_set_trunc_equiv (A : Type) : Equiv (Connected A) (BookIsContr (SetTrunc A))
  ≔ iff_equiv (Connected A) (BookIsContr (SetTrunc A)) (connected_isprop A) (book_iscontr_isprop (SetTrunc A))
      (connected_set_trunc_contractible A) (contractible_set_trunc_connected A)
