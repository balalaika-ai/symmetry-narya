export "104-composite-fibers"

{` Book n=0: the set-truncation of every fiber is contractible. `}
def ZeroConnectedMap (A B : Type) (f : A → B) : Type
  ≔ (b : B) → BookIsContr (SetTrunc (BookFiber A B f b))

def ConnectedFibers (A B : Type) (f : A → B) : Type
  ≔ (b : B) → Connected (BookFiber A B f b)

def zero_connected_map_prop (A B : Type) (f : A → B) : isProp (ZeroConnectedMap A B f)
  ≔ pi_prop B (b ↦ BookIsContr (SetTrunc (BookFiber A B f b)))
      (b ↦ book_iscontr_isprop (SetTrunc (BookFiber A B f b)))

def zero_connected_map_fibers (A B : Type) (f : A → B) (h : ZeroConnectedMap A B f)
  : ConnectedFibers A B f
  ≔ b ↦ contractible_set_trunc_connected (BookFiber A B f b) (h b)

def connected_fibers_zero_map (A B : Type) (f : A → B) (h : ConnectedFibers A B f)
  : ZeroConnectedMap A B f
  ≔ b ↦ connected_set_trunc_contractible (BookFiber A B f b) (h b)

def zero_connected_map_surjective (A B : Type) (f : A → B) (h : ZeroConnectedMap A B f)
  : Surjective A B f ≔ b ↦ zero_connected_map_fibers A B f h b .fst

def set_trunc_fiber_connected_at_point (A : Type) (a : A)
  : Connected (BookFiber A (SetTrunc A) (set_trunc A) (set_trunc A a))
  ≔ connected_equiv (NativeComponent A a)
      (BookFiber A (SetTrunc A) (set_trunc A) (set_trunc A a))
      (truncated_component_fiber_equiv A (set_trunc A a)) .map (native_component_connected A a)

def set_trunc_fibers_connected (A : Type) : ConnectedFibers A (SetTrunc A) (set_trunc A)
  ≔ z ↦ mere_rec (BookFiber A (SetTrunc A) (set_trunc A) z)
      (Connected (BookFiber A (SetTrunc A) (set_trunc A) z))
      (connected_isprop (BookFiber A (SetTrunc A) (set_trunc A) z))
      (w ↦ transport (SetTrunc A) (v ↦ Connected (BookFiber A (SetTrunc A) (set_trunc A) v))
        (set_trunc A (w .fst)) z (inverse (SetTrunc A) z (set_trunc A (w .fst)) (w .snd))
        (set_trunc_fiber_connected_at_point A (w .fst))) (set_trunc_surjective A z)

{` lem:trunc-n-connected, constructed for n=0, without a truncation axiom. `}
def set_trunc_constructor_zero_connected (A : Type) : ZeroConnectedMap A (SetTrunc A) (set_trunc A)
  ≔ connected_fibers_zero_map A (SetTrunc A) (set_trunc A) (set_trunc_fibers_connected A)
