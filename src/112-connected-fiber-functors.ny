export "111-connected-set-reflections"

def postequivalence_connected_fibers (A X Y : Type) (e : Equiv X Y) (f : A → X) (hf : ConnectedFibers A X f)
  : ConnectedFibers A Y (compose A X Y (e .map) f)
  ≔ equivalence_induction X
      (Y e ↦ ConnectedFibers A Y (compose A X Y (e .map) f)) hf Y e

def cancel_preequivalence_connected_fibers (A X B : Type) (e : Equiv A X) (f : X → B)
  (hf : ConnectedFibers A B (compose A X B f (e .map))) : ConnectedFibers X B f
  ≔ equivalence_induction A
      (X e ↦ (f : X → B) → ConnectedFibers A B (compose A X B f (e .map)) → ConnectedFibers X B f)
      (f hf ↦ hf) X e f hf

def total_connected_fiberwise (B : Type) (P Q : B → Type) (f : (b : B) → P b → Q b)
  (hf : ConnectedFibers (Σ B P) (Σ B Q) (totalize B P Q f))
  : (b : B) → ConnectedFibers (P b) (Q b) (f b)
  ≔ b q ↦ connected_equiv
      (BookFiber (Σ B P) (Σ B Q) (totalize B P Q f) (b, q)) (BookFiber (P b) (Q b) (f b) q)
      (total_fiber_equiv B P Q f b q) .map (hf (b, q))

def composite_fiber_map (A X B : Type) (g : A → X) (h : X → B) (b : B)
  : BookFiber A B (compose A X B h g) b → BookFiber X B h b
  ≔ w ↦ (g (w .fst), w .snd)

{` Passing a 0-connected map to fibers over a further map preserves
   0-connectivity. Totalization is compared with the literal decomposition
   into fibers; all maps in the commuting square agree judgmentally. `}
def composite_fiber_map_connected (A X B : Type) (g : A → X) (hg : ConnectedFibers A X g) (h : X → B)
  : (b : B) → ConnectedFibers (BookFiber A B (compose A X B h g) b) (BookFiber X B h b)
      (composite_fiber_map A X B g h b)
  ≔ total_connected_fiberwise B (BookFiber A B (compose A X B h g)) (BookFiber X B h)
      (composite_fiber_map A X B g h)
      (cancel_preequivalence_connected_fibers A (Σ B (BookFiber A B (compose A X B h g)))
        (Σ B (BookFiber X B h)) (fiber_decomposition_equiv A B (compose A X B h g))
        (totalize B (BookFiber A B (compose A X B h g)) (BookFiber X B h) (composite_fiber_map A X B g h))
        (postequivalence_connected_fibers A X (Σ B (BookFiber X B h)) (fiber_decomposition_equiv X B h) g hg))

def composite_truncated_fiber_equiv (A X B : Type) (g : A → X) (hg : ConnectedFibers A X g)
  (h : X → B) (hh : IsCovering X B h) (b : B)
  : Equiv (SetTrunc (BookFiber A B (compose A X B h g) b)) (BookFiber X B h b)
  ≔ connected_set_reflection_equiv (BookFiber A B (compose A X B h g) b) (BookFiber X B h b) (hh b)
      (composite_fiber_map A X B g h b) (composite_fiber_map_connected A X B g hg h b)
