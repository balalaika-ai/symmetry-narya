export "44-finite-quotients"

def surjections_compose (A B C : Type) (f : A → B) (g : B → C)
  (hf : Surjective A B f) (hg : Surjective B C g) : Surjective A C (compose A B C g f)
  ≔ c ↦ mere_rec (BookFiber B C g c) (Mere (BookFiber A C (compose A B C g f) c))
      (mere_isprop (BookFiber A C (compose A B C g f) c))
      (u ↦ mere_rec (BookFiber A B f (u .fst)) (Mere (BookFiber A C (compose A B C g f) c))
        (mere_isprop (BookFiber A C (compose A B C g f) c))
        (v ↦ mere (BookFiber A C (compose A B C g f) c)
          (v .fst, concat C c (g (u .fst)) (g (f (v .fst))) (u .snd)
            (map_path B C g (u .fst) (f (v .fst)) (v .snd)))) (hf (u .fst))) (hg c)

def surjection_function_ext (A B Y : Type) (p : A → B) (hp : Surjective A B p) (hy : isSet Y)
  (f g : B → Y) (h : Id (A → Y) (precompose A B Y p f) (precompose A B Y p g)) : Id (B → Y) f g
  ≔ equiv_inverse_map (Id (B → Y) f g) (Id (A → Y) (precompose A B Y p f) (precompose A B Y p g))
      (cancel_surjection_into_set A B Y p hp hy f g) h

def pullback_relation (A B : Type) (f : A → B) (R : EquivalenceRelation B) : EquivalenceRelation A
  ≔ ((x y ↦ R .predicate (f x) (f y)), (x ↦ R .reflexive (f x)),
      (x y ↦ R .symmetric (f x) (f y)), (x y z ↦ R .transitive (f x) (f y) (f z)))

def induced_relation (A B : Type) (f : A → B) : EquivalenceRelation A
  ≔ pullback_relation A B f (mere_path_relation B)

def InducedQuotient (A B : Type) (f : A → B) : Type ≔ Quotient A (induced_relation A B f)
def TruncatedImage (A B : Type) (f : A → B) : Type ≔ SetTrunc (Image A B f)

def truncated_image_map (A B : Type) (f : A → B) : A → TruncatedImage A B f
  ≔ compose A (Image A B f) (TruncatedImage A B f) (set_trunc (Image A B f)) (image_factor A B f)

def truncated_image_respects (A B : Type) (f : A → B)
  : Respects A (TruncatedImage A B f) (induced_relation A B f) (truncated_image_map A B f)
  ≔ x y r ↦ quotient_encode (Image A B f) (mere_path_relation (Image A B f))
      (image_factor A B f x) (image_factor A B f y)
      (trunc_map native_truncation (Id B (f x) (f y))
        (Id (Image A B f) (image_factor A B f x) (image_factor A B f y))
        (subtype_equal B (b ↦ Mere (BookFiber A B f b)) (b ↦ mere_isprop (BookFiber A B f b))
          (image_factor A B f x) (image_factor A B f y)) r)

def induced_quotient_to_image (A B : Type) (f : A → B) : InducedQuotient A B f → TruncatedImage A B f
  ≔ quotient_rec A (TruncatedImage A B f) (induced_relation A B f) (set_trunc_set (Image A B f))
      (truncated_image_map A B f) (truncated_image_respects A B f)

def image_to_induced_quotient (A B : Type) (f : A → B) (z : Image A B f) : InducedQuotient A B f
  ≔ weakly_constant_rec (BookFiber A B f (z .fst)) (InducedQuotient A B f)
      (w ↦ quotient_class A (induced_relation A B f) (w .fst)) (quotient_set A (induced_relation A B f))
      (u v ↦ quotient_encode A (induced_relation A B f) (u .fst) (v .fst)
        (mere (Id B (f (u .fst)) (f (v .fst)))
          (concat B (f (u .fst)) (z .fst) (f (v .fst))
            (inverse B (z .fst) (f (u .fst)) (u .snd)) (v .snd)))) (z .snd)

def truncated_image_to_quotient (A B : Type) (f : A → B) : TruncatedImage A B f → InducedQuotient A B f
  ≔ set_trunc_rec (Image A B f) (InducedQuotient A B f) (quotient_set A (induced_relation A B f))
      (image_to_induced_quotient A B f)

def induced_quotient_roundtrip (A B : Type) (f : A → B)
  : Id (InducedQuotient A B f → InducedQuotient A B f)
      (compose (InducedQuotient A B f) (TruncatedImage A B f) (InducedQuotient A B f)
        (truncated_image_to_quotient A B f) (induced_quotient_to_image A B f)) (identity (InducedQuotient A B f))
  ≔ surjection_function_ext A (InducedQuotient A B f) (InducedQuotient A B f)
      (quotient_class A (induced_relation A B f)) (quotient_surjective A (induced_relation A B f))
      (quotient_set A (induced_relation A B f))
      (compose (InducedQuotient A B f) (TruncatedImage A B f) (InducedQuotient A B f)
        (truncated_image_to_quotient A B f) (induced_quotient_to_image A B f)) (identity (InducedQuotient A B f))
      (refl (quotient_class A (induced_relation A B f)))

def truncated_image_roundtrip (A B : Type) (f : A → B)
  : Id (TruncatedImage A B f → TruncatedImage A B f)
      (compose (TruncatedImage A B f) (InducedQuotient A B f) (TruncatedImage A B f)
        (induced_quotient_to_image A B f) (truncated_image_to_quotient A B f)) (identity (TruncatedImage A B f))
  ≔ surjection_function_ext A (TruncatedImage A B f) (TruncatedImage A B f)
      (truncated_image_map A B f)
      (surjections_compose A (Image A B f) (TruncatedImage A B f) (image_factor A B f) (set_trunc (Image A B f))
        (image_factor_surjective A B f) (set_trunc_surjective (Image A B f)))
      (set_trunc_set (Image A B f))
      (compose (TruncatedImage A B f) (InducedQuotient A B f) (TruncatedImage A B f)
        (induced_quotient_to_image A B f) (truncated_image_to_quotient A B f)) (identity (TruncatedImage A B f))
      (refl (truncated_image_map A B f))

def induced_quotient_equiv (A B : Type) (f : A → B)
  : BookEquiv (InducedQuotient A B f) (TruncatedImage A B f)
  ≔ book_quasi_inverse_equiv (InducedQuotient A B f) (TruncatedImage A B f)
      (induced_quotient_to_image A B f) (truncated_image_to_quotient A B f)
      (z ↦ induced_quotient_roundtrip A B f (refl z)) (z ↦ truncated_image_roundtrip A B f (refl z))

def QuotientEquivalenceLifts (A B : Type) (R : EquivalenceRelation A) (f : A → B) : Type
  ≔ Σ (BookEquiv (Quotient A R) B) (e ↦ Id (A → B) f (compose A (Quotient A R) B (e .map) (quotient_class A R)))

def quotient_equivalence_lifts_prop (A B : Type) (R : EquivalenceRelation A) (hb : isSet B) (f : A → B)
  : isProp (QuotientEquivalenceLifts A B R f)
  ≔ u v ↦ subtype_equal (BookEquiv (Quotient A R) B)
      (e ↦ Id (A → B) f (compose A (Quotient A R) B (e .map) (quotient_class A R)))
      (e ↦ pi_set A (_ ↦ B) (_ ↦ hb) f (compose A (Quotient A R) B (e .map) (quotient_class A R))) u v
      (book_equiv_path (Quotient A R) B (u .fst) (v .fst)
        (quotient_lifts_prop A B R hb f (u .fst .map, u .snd) (v .fst .map, v .snd) .fst))

{` xca:map-induces-quotient: equivalence, commuting triangle, and uniqueness together. `}
def induced_quotient_unique (A B : Type) (f : A → B)
  : BookIsContr (QuotientEquivalenceLifts A (TruncatedImage A B f) (induced_relation A B f) (truncated_image_map A B f))
  ≔ let c : QuotientEquivalenceLifts A (TruncatedImage A B f) (induced_relation A B f) (truncated_image_map A B f)
      ≔ (induced_quotient_equiv A B f, refl (truncated_image_map A B f)) in
    (c, quotient_equivalence_lifts_prop A (TruncatedImage A B f) (induced_relation A B f)
      (set_trunc_set (Image A B f)) (truncated_image_map A B f) c)
