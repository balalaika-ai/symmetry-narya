export "110-truncated-map-levels"

def connected_map_truncated_inverse (A S : Type) (g : A → S) (hg : ConnectedFibers A S g)
  : S → SetTrunc A
  ≔ s ↦ connected_set_map_value (BookFiber A S g s) (SetTrunc A) (hg s) (set_trunc_set A)
      (w ↦ set_trunc A (w .fst))

def connected_map_truncated_inverse_beta (A S : Type) (g : A → S) (hg : ConnectedFibers A S g) (a : A)
  : Id (SetTrunc A) (connected_map_truncated_inverse A S g hg (g a)) (set_trunc A a)
  ≔ connected_set_map_value_beta (BookFiber A S g (g a)) (SetTrunc A) (hg (g a)) (set_trunc_set A)
      (w ↦ set_trunc A (w .fst)) (a, refl (g a))

def connected_set_reflection_retraction (A S : Type) (hs : isSet S) (g : A → S) (hg : ConnectedFibers A S g)
  : Id (SetTrunc A → SetTrunc A)
      (compose (SetTrunc A) S (SetTrunc A) (connected_map_truncated_inverse A S g hg) (set_trunc_rec A S hs g))
      (identity (SetTrunc A))
  ≔ surjection_function_ext A (SetTrunc A) (SetTrunc A) (set_trunc A) (set_trunc_surjective A) (set_trunc_set A)
      (compose (SetTrunc A) S (SetTrunc A) (connected_map_truncated_inverse A S g hg) (set_trunc_rec A S hs g))
      (identity (SetTrunc A))
      (funext A (_ ↦ SetTrunc A) (compose A S (SetTrunc A) (connected_map_truncated_inverse A S g hg) g)
        (set_trunc A) (connected_map_truncated_inverse_beta A S g hg))

def connected_set_reflection_section (A S : Type) (hs : isSet S) (g : A → S) (hg : ConnectedFibers A S g) (s : S)
  : Id S (set_trunc_rec A S hs g (connected_map_truncated_inverse A S g hg s)) s
  ≔ mere_rec (BookFiber A S g s)
      (Id S (set_trunc_rec A S hs g (connected_map_truncated_inverse A S g hg s)) s)
      (hs (set_trunc_rec A S hs g (connected_map_truncated_inverse A S g hg s)) s)
      (w ↦ calc
        set_trunc_rec A S hs g (connected_map_truncated_inverse A S g hg s)
        = set_trunc_rec A S hs g (set_trunc A (w .fst))
          by refl (set_trunc_rec A S hs g)
            (connected_set_map_value_beta (BookFiber A S g s) (SetTrunc A) (hg s) (set_trunc_set A)
              (v ↦ set_trunc A (v .fst)) w)
        = g (w .fst) by set_trunc_rec_beta A S hs g (w .fst)
        = s by w .snd ∎) (hg s .fst)

{` A 0-connected map into a set presents that set as the actual
   set-truncation of its domain. The map is exactly the recursor of g. `}
def connected_set_reflection_equiv (A S : Type) (hs : isSet S) (g : A → S) (hg : ConnectedFibers A S g)
  : Equiv (SetTrunc A) S
  ≔ quasi_inverse_equiv (SetTrunc A) S (set_trunc_rec A S hs g) (connected_map_truncated_inverse A S g hg)
      (z ↦ connected_set_reflection_retraction A S hs g hg (refl z)) (connected_set_reflection_section A S hs g hg)

def zero_connected_set_reflection (A S : Type) (hs : isSet S) (g : A → S) (hg : ZeroConnectedMap A S g)
  : BookEquiv (SetTrunc A) S
  ≔ book_equivalence (SetTrunc A) S (connected_set_reflection_equiv A S hs g (zero_connected_map_fibers A S g hg))
