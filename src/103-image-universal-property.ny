export "102-surjection-embedding-diagonals"

{` Evaluate a path of functions whose domain varies, at forward transport
   of an argument. The reflexive case uses typal transport beta. `}
def domain_pathover_evaluate (X Y B : Type) (q : Id Type X Y) (f : X → B) (g : Y → B)
  (h : Id (T ↦ T → B) q f g) (x : X) : Id B (f x) (g (q .trr x))
  ≔ J Type X
      (Y q ↦ (g : Y → B) → Id (T ↦ T → B) q f g → (x : X) → Id B (f x) (g (q .trr x)))
      (g h x ↦ concat B (f x) (g x) (g (transport Type (T ↦ T) X X (refl X) x))
        (h (refl x))
        (inverse B (g (transport Type (T ↦ T) X X (refl X) x)) (g x)
          (refl g (transport_refl Type (T ↦ T) X x)))) Y q g h x

def image_factorization_right_triangle (A B : Type) (f : A → B) (factor : ImageFactorizations A B f)
  : Id (Image A B f → B) (image_include A B f)
      (compose (Image A B f) (factor .fst) B (factor .snd .snd .fst)
        (image_factorization_carrier_equiv A B f factor .map))
  ≔ let P ≔ image_factorizations_contractible A B f .contract factor in
    funext (Image A B f) (_ ↦ B) (image_include A B f)
      (compose (Image A B f) (factor .fst) B (factor .snd .snd .fst)
        (image_factorization_carrier_equiv A B f factor .map))
      (domain_pathover_evaluate (Image A B f) (factor .fst) B (P .fst)
        (image_include A B f) (factor .snd .snd .fst) (P .snd .snd .fst))

{` Comparison with any known equivalent diagonal proves that every right
   diagonal is an equivalence; the right triangle is compared as well. `}
def right_diagonal_equiv (X C B : Type) (i : C → B) (hi : IsEmbedding C B i) (t : X → B)
  (e : Equiv X C) (beta : Id (X → B) t (compose X C B i (e .map)))
  (r : RightDiagonals X C B i t) : Equiv X C
  ≔ equiv_change_map X C e (r .fst)
      (happly X (_ ↦ C) (e .map) (r .fst)
        (right_diagonals_prop X C B i hi t (e .map, beta) r .fst))

def image_factorization_square (A B : Type) (f : A → B) (factor : ImageFactorizations A B f)
  : Id (A → B) (compose A (factor .fst) B (factor .snd .snd .fst) (factor .snd .fst))
      (precompose A (Image A B f) B (image_factor A B f) (image_include A B f))
  ≔ concat (A → B) (compose A (factor .fst) B (factor .snd .snd .fst) (factor .snd .fst)) f
      (precompose A (Image A B f) B (image_factor A B f) (image_include A B f))
      (inverse (A → B) f (compose A (factor .fst) B (factor .snd .snd .fst) (factor .snd .fst))
        (factor .snd .snd .snd .fst)) (image_triangle A B f)

def CoherentImageDiagonals (A B : Type) (f : A → B) (factor : ImageFactorizations A B f) : Type
  ≔ CoherentDiagonals A (Image A B f) (factor .fst) B (image_factor A B f)
      (factor .snd .snd .fst) (factor .snd .fst) (image_include A B f)
      (image_factorization_square A B f factor)

def coherent_image_diagonals_contractible (A B : Type) (f : A → B) (factor : ImageFactorizations A B f)
  : BookIsContr (CoherentImageDiagonals A B f factor)
  ≔ coherent_diagonals_contractible A (Image A B f) (factor .fst) B
      (image_factor A B f) (image_factor_surjective A B f)
      (factor .snd .snd .fst) (factor .snd .snd .snd .snd .snd) (factor .snd .fst) (image_include A B f)
      (image_factorization_square A B f factor)

def image_diagonal_equiv (A B : Type) (f : A → B) (factor : ImageFactorizations A B f)
  (d : CoherentImageDiagonals A B f factor) : Equiv (Image A B f) (factor .fst)
  ≔ right_diagonal_equiv (Image A B f) (factor .fst) B (factor .snd .snd .fst)
      (factor .snd .snd .snd .snd .snd) (image_include A B f)
      (image_factorization_carrier_equiv A B f factor) (image_factorization_right_triangle A B f factor) (d .fst)

def CoherentImageEquivalences (A B : Type) (f : A → B) (factor : ImageFactorizations A B f) : Type
  ≔ Σ (CoherentImageDiagonals A B f factor) (d ↦ BookIsEquiv (Image A B f) (factor .fst) (d .fst .fst))

{` eqn:image-univ-prop: unique equivalence, both triangular paths and their
   compatibility with the original square. Equivalence proofs are retained.
   Independent unrelated triangle paths are not asserted to be unique. `}
def image_universal_property (A B : Type) (f : A → B) (factor : ImageFactorizations A B f)
  : BookIsContr (CoherentImageEquivalences A B f factor)
  ≔ book_contraction (CoherentImageEquivalences A B f factor)
      (sigma_contractible (CoherentImageDiagonals A B f factor)
        (d ↦ BookIsEquiv (Image A B f) (factor .fst) (d .fst .fst))
        (native_contraction (CoherentImageDiagonals A B f factor) (coherent_image_diagonals_contractible A B f factor))
        (d ↦ native_contraction (BookIsEquiv (Image A B f) (factor .fst) (d .fst .fst))
          (let e ≔ book_equivalence (Image A B f) (factor .fst) (image_diagonal_equiv A B f factor d) in
            (e .equiv, book_isequiv_isprop (Image A B f) (factor .fst) (d .fst .fst) (e .equiv)))))
