export "116-images-preserve-connectedness"

def postequivalence_truncated_map (level : Nat) (A X Y : Type) (e : Equiv X Y) (f : A → X)
  (hf : TruncatedMap level A X f) : TruncatedMap level A Y (compose A X Y (e .map) f)
  ≔ equivalence_induction X (Y e ↦ TruncatedMap level A Y (compose A X Y (e .map) f)) hf Y e

def preequivalence_truncated_map (level : Nat) (A X B : Type) (e : Equiv A X) (f : X → B)
  (hf : TruncatedMap level X B f) : TruncatedMap level A B (compose A X B f (e .map))
  ≔ equivalence_induction A
      (X e ↦ (f : X → B) → TruncatedMap level X B f → TruncatedMap level A B (compose A X B f (e .map)))
      (f hf ↦ hf) X e f hf

def cancel_postequivalence_truncated_map (level : Nat) (A X Y : Type) (e : Equiv X Y) (f : A → X)
  (hf : TruncatedMap level A Y (compose A X Y (e .map) f)) : TruncatedMap level A X f
  ≔ equivalence_induction X
      (Y e ↦ TruncatedMap level A Y (compose A X Y (e .map) f) → TruncatedMap level A X f)
      (hf ↦ hf) Y e hf

def cancel_preequivalence_truncated_map (level : Nat) (A X B : Type) (e : Equiv A X) (f : X → B)
  (hf : TruncatedMap level A B (compose A X B f (e .map))) : TruncatedMap level X B f
  ≔ equivalence_induction A
      (X e ↦ (f : X → B) → TruncatedMap level A B (compose A X B f (e .map)) → TruncatedMap level X B f)
      (f hf ↦ hf) X e f hf

def total_truncated_fiberwise (level : Nat) (B : Type) (P Q : B → Type) (f : (b : B) → P b → Q b)
  (hf : TruncatedMap level (Σ B P) (Σ B Q) (totalize B P Q f))
  : (b : B) → TruncatedMap level (P b) (Q b) (f b)
  ≔ b q ↦ hlevel_equiv level
      (BookFiber (Σ B P) (Σ B Q) (totalize B P Q f) (b, q)) (BookFiber (P b) (Q b) (f b) q)
      (total_fiber_equiv B P Q f b q) (hf (b, q))

def fiberwise_truncated_total (level : Nat) (B : Type) (P Q : B → Type) (f : (b : B) → P b → Q b)
  (hf : (b : B) → TruncatedMap level (P b) (Q b) (f b))
  : TruncatedMap level (Σ B P) (Σ B Q) (totalize B P Q f)
  ≔ z ↦ hlevel_equiv level (BookFiber (P (z .fst)) (Q (z .fst)) (f (z .fst)) (z .snd))
      (BookFiber (Σ B P) (Σ B Q) (totalize B P Q f) z)
      (canonical_inverse_equiv (BookFiber (Σ B P) (Σ B Q) (totalize B P Q f) z)
        (BookFiber (P (z .fst)) (Q (z .fst)) (f (z .fst)) (z .snd))
        (total_fiber_equiv B P Q f (z .fst) (z .snd))) (hf (z .fst) (z .snd))

def composite_fiber_map_truncated (level : Nat) (A X B : Type) (g : A → X)
  (hg : TruncatedMap level A X g) (h : X → B)
  : (b : B) → TruncatedMap level (BookFiber A B (compose A X B h g) b) (BookFiber X B h b)
      (composite_fiber_map A X B g h b)
  ≔ total_truncated_fiberwise level B (BookFiber A B (compose A X B h g)) (BookFiber X B h)
      (composite_fiber_map A X B g h)
      (cancel_preequivalence_truncated_map level A (Σ B (BookFiber A B (compose A X B h g)))
        (Σ B (BookFiber X B h)) (fiber_decomposition_equiv A B (compose A X B h g))
        (totalize B (BookFiber A B (compose A X B h g)) (BookFiber X B h) (composite_fiber_map A X B g h))
        (postequivalence_truncated_map level A X (Σ B (BookFiber X B h)) (fiber_decomposition_equiv X B h) g hg))

def truncated_map_domain_hlevel (level : Nat) (A B : Type) (f : A → B)
  (hf : TruncatedMap level A B f) (hb : HLevel level B) : HLevel level A
  ≔ hlevel_equiv level (Σ B (BookFiber A B f)) A (sum_of_fibers_equiv A B f)
      (hlevel_sigma level B (BookFiber A B f) hb hf)

def truncated_maps_compose (level : Nat) (A B C : Type) (f : A → B) (g : B → C)
  (hf : TruncatedMap level A B f) (hg : TruncatedMap level B C g)
  : TruncatedMap level A C (compose A B C g f)
  ≔ c ↦ truncated_map_domain_hlevel level (BookFiber A C (compose A B C g f) c) (BookFiber B C g c)
      (composite_fiber_map A B C f g c) (composite_fiber_map_truncated level A B C f hf g c) (hg c)

def maps_between_hlevels_truncated (level : Nat) (A B : Type)
  (ha : HLevel (suc. level) A) (hb : HLevel (suc. level) B) (f : A → B)
  : TruncatedMap (suc. level) A B f
  ≔ b ↦ hlevel_sigma (suc. level) A (a ↦ Id B b (f a)) ha
      (a ↦ hlevel_raise level (Id B b (f a)) (hb b (f a)))

def truncated_maps_left_cancel (level : Nat) (A B C : Type) (f : A → B) (g : B → C)
  (hg : TruncatedMap (suc. level) B C g) (hgf : TruncatedMap (suc. level) A C (compose A B C g f))
  : TruncatedMap (suc. level) A B f
  ≔ let P ≔ BookFiber A C (compose A B C g f) in
    let Q ≔ BookFiber B C g in
    let F ≔ totalize C P Q (composite_fiber_map A B C f g) in
    cancel_postequivalence_truncated_map (suc. level) A B (Σ C Q) (fiber_decomposition_equiv B C g) f
      (preequivalence_truncated_map (suc. level) A (Σ C P) (Σ C Q)
        (fiber_decomposition_equiv A C (compose A B C g f)) F
        (fiberwise_truncated_total (suc. level) C P Q (composite_fiber_map A B C f g)
          (c ↦ maps_between_hlevels_truncated level (P c) (Q c) (hgf c) (hg c) (composite_fiber_map A B C f g c))))
