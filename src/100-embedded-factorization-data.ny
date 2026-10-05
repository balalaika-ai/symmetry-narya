export "99-universal-cover-presentations"

def surjective_property_prop (A B : Type) (f : A → B) : isProp (Surjective A B f)
  ≔ pi_prop B (b ↦ Mere (BookFiber A B f b)) (b ↦ mere_isprop (BookFiber A B f b))

def postcomposition_embedding (A C B : Type) (h : C → B) (embedding : IsEmbedding C B h)
  : IsEmbedding (A → C) (A → B) (compose A C B h)
  ≔ path_equivalences_embedding (A → C) (A → B) (compose A C B h)
      (g k ↦ book_equivalence (Id (A → C) g k)
        (Id (A → B) (compose A C B h g) (compose A C B h k))
        (cancel_injection C B A h embedding g k) .equiv)

def injection_to_bundle (B : Type) (i : InjectionsInto B) : BundledInjection B
  ≔ ((i .fst, i .snd .fst), i .snd .snd)
def bundled_to_injection (B : Type) (i : BundledInjection B) : InjectionsInto B
  ≔ (i .fst .fst, (i .fst .snd, i .snd))

def injection_fiber_predicate (B : Type) (i : InjectionsInto B) : Subtypes B
  ≔ b ↦ (BookFiber (i .fst) B (i .snd .fst) b, i .snd .snd b)

{` The forward map is the actual proposition-valued family of fibers. `}
def injection_fiber_predicate_equiv (B : Type) : Equiv (InjectionsInto B) (Subtypes B)
  ≔ quasi_inverse_equiv (InjectionsInto B) (Subtypes B) (injection_fiber_predicate B)
      (P ↦ bundled_to_injection B (subtype_to_bundled_injection B P))
      (i ↦ refl (bundled_to_injection B) (subtypes_injections_beta B (injection_to_bundle B i)))
      (subtypes_injections_eta B)

def EmbeddingFactorData (A B : Type) (f : A → B) (i : InjectionsInto B) : Type
  ≔ Σ (A → i .fst) (g ↦ Product (Id (A → B) f (compose A (i .fst) B (i .snd .fst) g))
      (Surjective A (i .fst) g))

def EmbeddedFunctionLifts (A B : Type) (f : A → B) (i : InjectionsInto B) : Type
  ≔ BookFiber (A → i .fst) (A → B) (compose A (i .fst) B (i .snd .fst)) f

{` Once the embedding is fixed, the map and its specified commuting
   triangle form a proposition.  Surjectivity is another proposition. `}
def embedding_factor_data_prop (A B : Type) (f : A → B) (i : InjectionsInto B)
  : isProp (EmbeddingFactorData A B f i)
  ≔ retract_prop
      (Σ (EmbeddedFunctionLifts A B f i) (u ↦ Surjective A (i .fst) (u .fst)))
      (EmbeddingFactorData A B f i)
      (sigma_prop (EmbeddedFunctionLifts A B f i) (u ↦ Surjective A (i .fst) (u .fst))
        (postcomposition_embedding A (i .fst) B (i .snd .fst) (i .snd .snd) f)
        (u ↦ surjective_property_prop A (i .fst) (u .fst)))
      (u ↦ (u .fst .fst, (u .fst .snd, u .snd)))
      (u ↦ ((u .fst, u .snd .fst), u .snd .snd)) (u ↦ refl u)

def EmbeddedImageFactorizations (A B : Type) (f : A → B) : Type
  ≔ Σ (InjectionsInto B) (EmbeddingFactorData A B f)

def image_factorizations_regroup (A B : Type) (f : A → B)
  : Equiv (ImageFactorizations A B f) (EmbeddedImageFactorizations A B f)
  ≔ quasi_inverse_equiv (ImageFactorizations A B f) (EmbeddedImageFactorizations A B f)
      (t ↦ ((t .fst, (t .snd .snd .fst, t .snd .snd .snd .snd .snd)),
        (t .snd .fst, (t .snd .snd .snd .fst, t .snd .snd .snd .snd .fst))))
      (t ↦ (t .fst .fst, (t .snd .fst, (t .fst .snd .fst,
        (t .snd .snd .fst, (t .snd .snd .snd, t .fst .snd .snd))))))
      (t ↦ refl t) (t ↦ refl t)
