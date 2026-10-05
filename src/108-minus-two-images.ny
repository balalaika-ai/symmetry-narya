export "107-truncated-dependent-sums"

{` The (-2)-truncation is Unit. Connectivity of a map at this level
   records a contraction of Unit for each fiber, so every map qualifies. `}
def MinusTwoConnectedMap (A B : Type) (f : A → B) : Type ≔ (b : B) → BookIsContr Unit
def minus_two_connected_map (A B : Type) (f : A → B) : MinusTwoConnectedMap A B f
  ≔ b ↦ book_contraction Unit unit_contractible
def minus_two_connected_map_prop (A B : Type) (f : A → B) : isProp (MinusTwoConnectedMap A B f)
  ≔ pi_prop B (_ ↦ BookIsContr Unit) (_ ↦ book_iscontr_isprop Unit)

def MinusTwoImage (A B : Type) (f : A → B) : Type ≔ Σ B (_ ↦ Unit)
def minus_two_image_factor (A B : Type) (f : A → B) : A → MinusTwoImage A B f ≔ a ↦ (f a, star.)
def minus_two_image_include (A B : Type) (f : A → B) : MinusTwoImage A B f → B ≔ z ↦ z .fst

def EquivalencesInto (B : Type) : Type ≔ Σ Type (C ↦ Equiv C B)
def equivalences_into_contractible (B : Type) : isContr (EquivalencesInto B)
  ≔ hlevel_equiv zero. (Σ Type (C ↦ Id Type C B)) (EquivalencesInto B)
      (family_equiv Type (C ↦ Id Type C B) (C ↦ Equiv C B) (C ↦ univalence_equiv C B))
      (path_to_contractible Type B)

def EquivalenceFactorData (A B : Type) (f : A → B) (e : EquivalencesInto B) : Type
  ≔ BookFiber (A → e .fst) (A → B) (compose A (e .fst) B (e .snd .map)) f

def equivalence_factor_data_contractible (A B : Type) (f : A → B) (e : EquivalencesInto B)
  : isContr (EquivalenceFactorData A B f e)
  ≔ native_contraction (EquivalenceFactorData A B f e)
      (book_equivalence (A → e .fst) (A → B)
        (pi_equiv A (_ ↦ e .fst) (_ ↦ B) (_ ↦ e .snd)) .equiv f)

def EquivalenceFactorizations (A B : Type) (f : A → B) : Type
  ≔ Σ (EquivalencesInto B) (EquivalenceFactorData A B f)
def equivalence_factorizations_contractible (A B : Type) (f : A → B)
  : isContr (EquivalenceFactorizations A B f)
  ≔ sigma_contractible (EquivalencesInto B) (EquivalenceFactorData A B f)
      (equivalences_into_contractible B) (equivalence_factor_data_contractible A B f)

def MinusTwoImageFactorizations (A B : Type) (f : A → B) : Type
  ≔ Σ Type (C ↦ Σ (A → C) (g ↦ Σ (C → B) (h ↦ Product (Id (A → B) f (compose A C B h g))
      (Product (MinusTwoConnectedMap A C g) (BookIsEquiv C B h)))))

def minus_two_factorization_to_equivalence (A B : Type) (f : A → B) (v : MinusTwoImageFactorizations A B f)
  : EquivalenceFactorizations A B f
  ≔ ((v .fst, native_equivalence (v .fst) B (v .snd .snd .fst, v .snd .snd .snd .snd .snd)),
      (v .snd .fst, v .snd .snd .snd .fst))

def equivalence_to_minus_two_factorization (A B : Type) (f : A → B) (v : EquivalenceFactorizations A B f)
  : MinusTwoImageFactorizations A B f
  ≔ (v .fst .fst, (v .snd .fst, (v .fst .snd .map, (v .snd .snd,
      (minus_two_connected_map A (v .fst .fst) (v .snd .fst),
        book_equivalence (v .fst .fst) B (v .fst .snd) .equiv)))))

def minus_two_factorization_retraction (A B : Type) (f : A → B) (v : MinusTwoImageFactorizations A B f)
  : Id (MinusTwoImageFactorizations A B f)
      (equivalence_to_minus_two_factorization A B f (minus_two_factorization_to_equivalence A B f v)) v
  ≔ (refl (v .fst), (refl (v .snd .fst), (refl (v .snd .snd .fst), (refl (v .snd .snd .snd .fst),
      (minus_two_connected_map_prop A (v .fst) (v .snd .fst)
        (minus_two_connected_map A (v .fst) (v .snd .fst)) (v .snd .snd .snd .snd .fst),
      book_isequiv_isprop (v .fst) B (v .snd .snd .fst)
        (book_equivalence (v .fst) B
          (native_equivalence (v .fst) B (v .snd .snd .fst, v .snd .snd .snd .snd .snd)) .equiv)
        (v .snd .snd .snd .snd .snd))))))

def minus_two_image_factorizations_prop (A B : Type) (f : A → B)
  : isProp (MinusTwoImageFactorizations A B f)
  ≔ retract_prop (EquivalenceFactorizations A B f) (MinusTwoImageFactorizations A B f)
      (contractible_prop (EquivalenceFactorizations A B f) (equivalence_factorizations_contractible A B f))
      (equivalence_to_minus_two_factorization A B f) (minus_two_factorization_to_equivalence A B f)
      (minus_two_factorization_retraction A B f)

def minus_two_image_factorization (A B : Type) (f : A → B) : MinusTwoImageFactorizations A B f
  ≔ (MinusTwoImage A B f, (minus_two_image_factor A B f, (minus_two_image_include A B f,
      (refl f, (minus_two_connected_map A (MinusTwoImage A B f) (minus_two_image_factor A B f),
        book_equivalence (MinusTwoImage A B f) B (unit_projection_equiv B) .equiv)))))

{` thm:n-im-univ-prop, n=-2: the full six-component type is contractible,
   including the specified triangular equality and both property proofs. `}
def minus_two_image_universal_property (A B : Type) (f : A → B)
  : BookIsContr (MinusTwoImageFactorizations A B f)
  ≔ (minus_two_image_factorization A B f,
    minus_two_image_factorizations_prop A B f (minus_two_image_factorization A B f))
