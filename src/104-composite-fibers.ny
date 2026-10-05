export "103-image-universal-property"

def pathover_domain_contractible (B : Type) (P : B → Type) (b c : B) (q : Id B b c) (v : P c)
  : isContr (Σ (P b) (u ↦ Id P q u v))
  ≔ J B b (c q ↦ (v : P c) → isContr (Σ (P b) (u ↦ Id P q u v)))
      (v ↦ path_to_contractible (P b) v) c q v

def projection_composite_fiber_split (A B : Type) (P : B → Type) (f : A → Σ B P) (b : B)
  : Equiv (Σ (P b) (u ↦ BookFiber A (Σ B P) f (b, u)))
      (Σ (BookFiber A B (a ↦ f a .fst) b) (w ↦ Σ (P b) (u ↦ Id P (w .snd) u (f (w .fst) .snd))))
  ≔ quasi_inverse_equiv
      (Σ (P b) (u ↦ BookFiber A (Σ B P) f (b, u)))
      (Σ (BookFiber A B (a ↦ f a .fst) b) (w ↦ Σ (P b) (u ↦ Id P (w .snd) u (f (w .fst) .snd))))
      (z ↦ ((z .snd .fst, z .snd .snd .fst), (z .fst, z .snd .snd .snd)))
      (z ↦ (z .snd .fst, (z .fst .fst, (z .fst .snd, z .snd .snd))))
      (z ↦ refl z) (z ↦ refl z)

{` Fibers of a composite with a projection split as a sum of fibers.
   The proof contracts the pathover's varying source, including its path. `}
def projection_composite_fiber_equiv (A B : Type) (P : B → Type) (f : A → Σ B P) (b : B)
  : Equiv (Σ (P b) (u ↦ BookFiber A (Σ B P) f (b, u))) (BookFiber A B (a ↦ f a .fst) b)
  ≔ compose_equiv
      (Σ (P b) (u ↦ BookFiber A (Σ B P) f (b, u)))
      (Σ (BookFiber A B (a ↦ f a .fst) b) (w ↦ Σ (P b) (u ↦ Id P (w .snd) u (f (w .fst) .snd))))
      (BookFiber A B (a ↦ f a .fst) b)
      (projection_composite_fiber_split A B P f b)
      (contractible_fiber_projection (BookFiber A B (a ↦ f a .fst) b)
        (w ↦ Σ (P b) (u ↦ Id P (w .snd) u (f (w .fst) .snd)))
        (w ↦ pathover_domain_contractible B P b (f (w .fst) .fst) (w .snd) (f (w .fst) .snd)))

def fiber_decomposition (A B : Type) (f : A → B) : A → Σ B (BookFiber A B f)
  ≔ a ↦ (f a, (a, refl (f a)))

def fiber_decomposition_equiv (A B : Type) (f : A → B) : Equiv A (Σ B (BookFiber A B f))
  ≔ let e ≔ sum_of_fibers_equiv A B f in
    equiv_change_map A (Σ B (BookFiber A B f))
      (canonical_inverse_equiv (Σ B (BookFiber A B f)) A e) (fiber_decomposition A B f)
      (a ↦ equivalence_injective (Σ B (BookFiber A B f)) A e
        (equiv_inverse_map (Σ B (BookFiber A B f)) A e a) (fiber_decomposition A B f a)
        (equiv_counit (Σ B (BookFiber A B f)) A e a))

def composite_fiber_decomposition (A X B : Type) (g : A → X) (h : X → B)
  : A → Σ B (BookFiber X B h)
  ≔ compose A X (Σ B (BookFiber X B h)) (fiber_decomposition X B h) g

{` con:fibcomp=fibfib and xca:fibcomp=fibfib: the requested double-fiber
   equivalence for arbitrary types, using the allowed contract-away proof. `}
def composite_double_fiber_equiv (A X B : Type) (g : A → X) (h : X → B) (b : B)
  : Equiv (BookFiber A B (compose A X B h g) b)
      (Σ (BookFiber X B h b) (u ↦ BookFiber A (Σ B (BookFiber X B h))
        (composite_fiber_decomposition A X B g h) (b, u)))
  ≔ canonical_inverse_equiv
      (Σ (BookFiber X B h b) (u ↦ BookFiber A (Σ B (BookFiber X B h))
        (composite_fiber_decomposition A X B g h) (b, u)))
      (BookFiber A B (compose A X B h g) b)
      (projection_composite_fiber_equiv A B (BookFiber X B h)
        (composite_fiber_decomposition A X B g h) b)

def preequivalence_fiber_equiv (A X B : Type) (e : Equiv A X) (f : X → B) (b : B)
  : Equiv (BookFiber A B (compose A X B f (e .map)) b) (BookFiber X B f b)
  ≔ sigma_pullback_equiv A X e (x ↦ Id B b (f x))
