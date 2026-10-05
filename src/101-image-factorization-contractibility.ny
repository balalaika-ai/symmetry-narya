export "100-embedded-factorization-data"

def image_fiber_predicate (A B : Type) (f : A → B) : Subtypes B
  ≔ b ↦ (Mere (BookFiber A B f b), mere_isprop (BookFiber A B f b))

def embedded_fiber_to_image (A B : Type) (f : A → B) (i : InjectionsInto B)
  (factor : EmbeddingFactorData A B f i) (b : B) (u : BookFiber (i .fst) B (i .snd .fst) b)
  : Mere (BookFiber A B f b)
  ≔ mere_rec (BookFiber A (i .fst) (factor .fst) (u .fst))
      (Mere (BookFiber A B f b)) (mere_isprop (BookFiber A B f b))
      (w ↦ mere (BookFiber A B f b) (w .fst, calc
        b = i .snd .fst (u .fst) by u .snd
        = i .snd .fst (factor .fst (w .fst)) by refl (i .snd .fst) (w .snd)
        = f (w .fst) by factor .snd .fst (refl (w .fst)) ∎)) (factor .snd .snd (u .fst))

def image_to_embedded_fiber (A B : Type) (f : A → B) (i : InjectionsInto B)
  (factor : EmbeddingFactorData A B f i) (b : B) : Mere (BookFiber A B f b) → BookFiber (i .fst) B (i .snd .fst) b
  ≔ mere_rec (BookFiber A B f b) (BookFiber (i .fst) B (i .snd .fst) b) (i .snd .snd b)
      (w ↦ (factor .fst (w .fst), concat B b (f (w .fst)) (i .snd .fst (factor .fst (w .fst)))
        (w .snd) (factor .snd .fst (refl (w .fst)))))

def embedded_factor_image_predicate (A B : Type) (f : A → B) (i : InjectionsInto B)
  (factor : EmbeddingFactorData A B f i)
  : Id (Subtypes B) (injection_fiber_predicate B i) (image_fiber_predicate A B f)
  ≔ funext B (_ ↦ PropTypes) (injection_fiber_predicate B i) (image_fiber_predicate A B f)
      (b ↦ proposition_extensionality (injection_fiber_predicate B i b) (image_fiber_predicate A B f b)
        (embedded_fiber_to_image A B f i factor b) (image_to_embedded_fiber A B f i factor b))

def embedded_factor_bases_equal (A B : Type) (f : A → B) (i j : InjectionsInto B)
  (di : EmbeddingFactorData A B f i) (dj : EmbeddingFactorData A B f j) : Id (InjectionsInto B) i j
  ≔ equivalence_injective (InjectionsInto B) (Subtypes B) (injection_fiber_predicate_equiv B) i j
      (concat (Subtypes B) (injection_fiber_predicate B i) (image_fiber_predicate A B f)
        (injection_fiber_predicate B j) (embedded_factor_image_predicate A B f i di)
        (inverse (Subtypes B) (injection_fiber_predicate B j) (image_fiber_predicate A B f)
          (embedded_factor_image_predicate A B f j dj)))

def embedded_image_factorizations_prop (A B : Type) (f : A → B)
  : isProp (EmbeddedImageFactorizations A B f)
  ≔ u v ↦ subtype_equal (InjectionsInto B) (EmbeddingFactorData A B f) (embedding_factor_data_prop A B f) u v
      (embedded_factor_bases_equal A B f (u .fst) (v .fst) (u .snd) (v .snd))

def image_factorizations_prop (A B : Type) (f : A → B) : isProp (ImageFactorizations A B f)
  ≔ retract_prop (EmbeddedImageFactorizations A B f) (ImageFactorizations A B f)
      (embedded_image_factorizations_prop A B f)
      (equiv_inverse_map (ImageFactorizations A B f) (EmbeddedImageFactorizations A B f) (image_factorizations_regroup A B f))
      (image_factorizations_regroup A B f .map)
      (equiv_retraction (ImageFactorizations A B f) (EmbeddedImageFactorizations A B f) (image_factorizations_regroup A B f))

{` xca:unique-fact-image, the full six-component type as printed.  The
   canonical image factorization is the center.  A and B are arbitrary. `}
def image_factorizations_contractible (A B : Type) (f : A → B) : BookIsContr (ImageFactorizations A B f)
  ≔ (image_factorization A B f, image_factorizations_prop A B f (image_factorization A B f))

def image_factorization_paths_contractible (A B : Type) (f : A → B) (t u : ImageFactorizations A B f)
  : BookIsContr (Id (ImageFactorizations A B f) t u)
  ≔ book_contraction (Id (ImageFactorizations A B f) t u)
      (prop_paths_contractible (ImageFactorizations A B f) (image_factorizations_prop A B f) t u)

def image_factorization_carrier_equiv (A B : Type) (f : A → B) (t : ImageFactorizations A B f)
  : Equiv (Image A B f) (t .fst)
  ≔ transport_equiv (Image A B f) (t .fst) (image_factorizations_contractible A B f .contract t .fst)

def ImageFactorizationTriangles (A B : Type) (f : A → B) : Type
  ≔ Σ Type (C ↦ Σ (A → C) (g ↦ Σ (C → B) (h ↦ Id (A → B) f (compose A C B h g))))

def image_factorization_forget_properties (A B : Type) (f : A → B) (t : ImageFactorizations A B f)
  : ImageFactorizationTriangles A B f
  ≔ (t .fst, (t .snd .fst, (t .snd .snd .fst, t .snd .snd .snd .fst)))

{` Coherence is retained as a path of full triangular data, including
   the originally specified equality f = h o g. `}
def image_factorization_triangle_comparison (A B : Type) (f : A → B) (t u : ImageFactorizations A B f)
  : Id (ImageFactorizationTriangles A B f) (image_factorization_forget_properties A B f t)
      (image_factorization_forget_properties A B f u)
  ≔ refl (image_factorization_forget_properties A B f) (image_factorizations_prop A B f t u)
