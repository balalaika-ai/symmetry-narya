export "101-image-factorization-contractibility"

{` The diagonal filler for a square with a surjective left map and an
   embedding on the right. No set assumption is imposed on any vertex. `}
def RightDiagonals (X C B : Type) (i : C → B) (t : X → B) : Type
  ≔ BookFiber (X → C) (X → B) (compose X C B i) t

def right_diagonals_prop (X C B : Type) (i : C → B) (hi : IsEmbedding C B i) (t : X → B)
  : isProp (RightDiagonals X C B i t)
  ≔ postcomposition_embedding X C B i hi t

def square_pointwise_lift (A X C B : Type) (p : A → X) (hp : Surjective A X p)
  (i : C → B) (hi : IsEmbedding C B i) (s : A → C) (t : X → B)
  (alpha : Id (A → B) (compose A C B i s) (precompose A X B p t))
  (x : X) : BookFiber C B i (t x)
  ≔ mere_rec (BookFiber A X p x) (BookFiber C B i (t x)) (hi (t x))
      (w ↦ (s (w .fst), concat B (t x) (t (p (w .fst))) (i (s (w .fst)))
        (refl t (w .snd))
        (inverse B (i (s (w .fst))) (t (p (w .fst))) (alpha (refl (w .fst)))))) (hp x)

def square_right_diagonal (A X C B : Type) (p : A → X) (hp : Surjective A X p)
  (i : C → B) (hi : IsEmbedding C B i) (s : A → C) (t : X → B)
  (alpha : Id (A → B) (compose A C B i s) (precompose A X B p t))
  : RightDiagonals X C B i t
  ≔ let lift ≔ square_pointwise_lift A X C B p hp i hi s t alpha in
    let d ≔ ((x ↦ lift x .fst) : X → C) in
    (d, funext X (_ ↦ B) t (compose X C B i d) (x ↦ lift x .snd))

def square_right_diagonals_contractible (A X C B : Type) (p : A → X) (hp : Surjective A X p)
  (i : C → B) (hi : IsEmbedding C B i) (s : A → C) (t : X → B)
  (alpha : Id (A → B) (compose A C B i s) (precompose A X B p t))
  : BookIsContr (RightDiagonals X C B i t)
  ≔ (square_right_diagonal A X C B p hp i hi s t alpha,
    right_diagonals_prop X C B i hi t (square_right_diagonal A X C B p hp i hi s t alpha))

{` alpha followed by beta restricted along p is the prescribed image of
   the left triangle under postcomposition by i. Its fiber retains the
   two-dimensional compatibility, rather than forgetting it. `}
def diagonal_triangle_target (A X C B : Type) (p : A → X) (i : C → B) (s : A → C) (t : X → B)
  (alpha : Id (A → B) (compose A C B i s) (precompose A X B p t))
  (r : RightDiagonals X C B i t)
  : Id (A → B) (compose A C B i s) (compose A C B i (precompose A X C p (r .fst)))
  ≔ concat (A → B) (compose A C B i s) (precompose A X B p t)
      (compose A C B i (precompose A X C p (r .fst))) alpha (refl (precompose A X B p) (r .snd))

def LeftCoherentDiagonals (A X C B : Type) (p : A → X) (i : C → B) (s : A → C) (t : X → B)
  (alpha : Id (A → B) (compose A C B i s) (precompose A X B p t))
  (r : RightDiagonals X C B i t) : Type
  ≔ BookFiber (Id (A → C) s (precompose A X C p (r .fst)))
      (Id (A → B) (compose A C B i s) (compose A C B i (precompose A X C p (r .fst))))
      (map_path (A → C) (A → B) (compose A C B i) s (precompose A X C p (r .fst)))
      (diagonal_triangle_target A X C B p i s t alpha r)

def left_coherent_diagonals_contractible (A X C B : Type) (p : A → X)
  (i : C → B) (hi : IsEmbedding C B i) (s : A → C) (t : X → B)
  (alpha : Id (A → B) (compose A C B i s) (precompose A X B p t))
  (r : RightDiagonals X C B i t) : BookIsContr (LeftCoherentDiagonals A X C B p i s t alpha r)
  ≔ book_equivalence (Id (A → C) s (precompose A X C p (r .fst)))
      (Id (A → B) (compose A C B i s) (compose A C B i (precompose A X C p (r .fst))))
      (cancel_injection C B A i hi s (precompose A X C p (r .fst))) .equiv
      (diagonal_triangle_target A X C B p i s t alpha r)

def CoherentDiagonals (A X C B : Type) (p : A → X) (i : C → B) (s : A → C) (t : X → B)
  (alpha : Id (A → B) (compose A C B i s) (precompose A X B p t)) : Type
  ≔ Σ (RightDiagonals X C B i t) (LeftCoherentDiagonals A X C B p i s t alpha)

def coherent_diagonals_contractible (A X C B : Type) (p : A → X) (hp : Surjective A X p)
  (i : C → B) (hi : IsEmbedding C B i) (s : A → C) (t : X → B)
  (alpha : Id (A → B) (compose A C B i s) (precompose A X B p t))
  : BookIsContr (CoherentDiagonals A X C B p i s t alpha)
  ≔ book_contraction (CoherentDiagonals A X C B p i s t alpha)
      (sigma_contractible (RightDiagonals X C B i t) (LeftCoherentDiagonals A X C B p i s t alpha)
        (native_contraction (RightDiagonals X C B i t)
          (square_right_diagonals_contractible A X C B p hp i hi s t alpha))
        (r ↦ native_contraction (LeftCoherentDiagonals A X C B p i s t alpha r)
          (left_coherent_diagonals_contractible A X C B p i hi s t alpha r)))
