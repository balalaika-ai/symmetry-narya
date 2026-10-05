export "128-dependent-circle-universal-property"

{` Written with concatenation order: p, then l, then inverse p.
   This is p^{-1} l p in the book's composition notation. `}
def pointed_loop_conjugate (A : Type) (a x : A) (p : Id A a x) (l : Id A x x) : Id A a a
  ≔ concat A a x a p (concat A x x a l (inverse A a x p))

def pointed_loop_boundary (A : Type) (a x : A) (p : Id A a x) (l : Id A x x)
  : Id (FreeLoop A) (a, pointed_loop_conjugate A a x p l) (x, l)
  ≔ J A a
      (x p ↦ (l : Id A x x) → Id (FreeLoop A) (a, pointed_loop_conjugate A a x p l) (x, l))
      (l ↦ (refl a, calc
        pointed_loop_conjugate A a a (refl a) l
        = concat A a a a l (inverse A a a (refl a))
          by concat_1p A a a (concat A a a a l (inverse A a a (refl a)))
        = concat A a a a l (refl a) by refl (concat A a a a l) (inverse_refl A a)
        = l by concat_p1 A a a l ∎)) x p l

def pointed_circle_loop_eval (C : CircleSignature) (A : Type) (a : A)
  (u : BookPointedMap (circle_pointed C) (A, a)) : Id A a a
  ≔ pointed_loop_conjugate A a (u .fst (C .base)) (u .snd) (refl (u .fst) (C .loop))

def pointed_circle_total_equiv (C : CircleSignature) (A : Type)
  : Equiv (Σ A (a ↦ BookPointedMap (circle_pointed C) (A, a))) (FreeLoop A)
  ≔ let T ≔ Σ A (a ↦ BookPointedMap (circle_pointed C) (A, a)) in
    equiv_change_map T (FreeLoop A)
      (compose_equiv T (C .carrier → A) (FreeLoop A)
        (pointed_map_chosen_target_equiv (circle_pointed C) A) (circle_universal_property C A))
      (totalize A (a ↦ BookPointedMap (circle_pointed C) (A, a)) (a ↦ Id A a a) (pointed_circle_loop_eval C A))
      (u ↦ inverse (FreeLoop A) (u .fst, pointed_circle_loop_eval C A (u .fst) (u .snd))
        (circle_eval C A (u .snd .fst))
        (pointed_loop_boundary A (u .fst) (u .snd .fst (C .base)) (u .snd .snd)
          (refl (u .snd .fst) (C .loop))))

{` cor:circle-loopspace, for every target type, with the literal displayed
   conjugation map and the book orientation of the pointed path. `}
def pointed_circle_universal_property (C : CircleSignature) (A : Type) (a : A)
  : Equiv (BookPointedMap (circle_pointed C) (A, a)) (Id A a a)
  ≔ (pointed_circle_loop_eval C A a,
      fiberwise_from_total A (a ↦ BookPointedMap (circle_pointed C) (A, a)) (a ↦ Id A a a)
        (pointed_circle_loop_eval C A) (pointed_circle_total_equiv C A .equiv) a)

{` The inverse proposed in the footnote. The inverse of the coherent base
   beta replaces the footnote's judgmental reflexivity at the chosen point. `}
def pointed_circle_loop_rec (C : CircleSignature) (A : Type) (a : A) (l : Id A a a)
  : BookPointedMap (circle_pointed C) (A, a)
  ≔ (circle_rec C A (a, l), inverse A (circle_rec C A (a, l) (C .base)) a
      (circle_rec_beta C A (a, l) .fst))

def pointed_circle_loop_rec_beta (C : CircleSignature) (A : Type) (a : A) (l : Id A a a)
  : Id (Id A a a) (pointed_circle_loop_eval C A a (pointed_circle_loop_rec C A a l)) l
  ≔ let f ≔ circle_rec C A (a, l) in let q ≔ circle_rec_beta C A (a, l) in
    calc
      pointed_circle_loop_eval C A a (pointed_circle_loop_rec C A a l)
      = loop_conjugate A (f (C .base)) a (q .fst) (refl f (C .loop))
        by refl (concat A a (f (C .base)) a (inverse A (f (C .base)) a (q .fst)))
          (refl (concat A (f (C .base)) (f (C .base)) a (refl f (C .loop)))
            (inverse_inverse A (f (C .base)) a (q .fst)))
      = transport A (x ↦ Id A x x) (f (C .base)) a (q .fst) (refl f (C .loop))
        by loop_transport_conjugate A (f (C .base)) a (q .fst) (refl f (C .loop))
      = l by pathover_transport_equiv A (x ↦ Id A x x) (f (C .base)) a (q .fst)
        (refl f (C .loop)) l .map (q .snd) ∎

def pointed_circle_loop_rec_eta (C : CircleSignature) (A : Type) (a : A)
  (u : BookPointedMap (circle_pointed C) (A, a))
  : Id (BookPointedMap (circle_pointed C) (A, a))
      (pointed_circle_loop_rec C A a (pointed_circle_loop_eval C A a u)) u
  ≔ equivalence_injective (BookPointedMap (circle_pointed C) (A, a)) (Id A a a)
      (pointed_circle_universal_property C A a)
      (pointed_circle_loop_rec C A a (pointed_circle_loop_eval C A a u)) u
      (pointed_circle_loop_rec_beta C A a (pointed_circle_loop_eval C A a u))

def pointed_circle_loop_type_path (C : CircleSignature) (A : Type) (a : A)
  : Id Type (BookPointedMap (circle_pointed C) (A, a)) (Id A a a)
  ≔ ua (BookPointedMap (circle_pointed C) (A, a)) (Id A a a) (pointed_circle_universal_property C A a)
