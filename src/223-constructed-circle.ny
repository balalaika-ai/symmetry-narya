export "222-circle-recursion"

{` Generic: a type C with base and loop whose free-loop evaluation is an
   equivalence for every target type satisfies circle induction, with the
   coherent boundary computation required by CircleSignature. `}
def free_loop_evaluation (C : Type) (b0 : C) (l0 : Id C b0 b0) (A : Type) (f : C → A) : FreeLoop A
  ≔ (f b0, refl f l0)

def NondependentCircleProperty (C : Type) (b0 : C) (l0 : Id C b0 b0) : Type
  ≔ (A : Type) → isEquiv (C → A) (FreeLoop A) (free_loop_evaluation C b0 l0 A)

def free_loop_fst (C : Type) (P : C → Type) (W : FreeLoop (Σ C P)) : FreeLoop C ≔ (W .fst .fst, W .snd .fst)

def BoundaryFamily (C : Type) (P : C → Type) (u : FreeLoop C) : Type ≔ Σ (P (u .fst)) (p ↦ Id P (u .snd) p p)

def boundary_transport (C : Type) (P : C → Type) (W : FreeLoop (Σ C P)) (u : FreeLoop C)
  (q : Id (FreeLoop C) (free_loop_fst C P W) u) : BoundaryFamily C P u
  ≔ transport (FreeLoop C) (BoundaryFamily C P) (free_loop_fst C P W) u q (W .fst .snd, W .snd .snd)

def boundary_transport_ap (C : Type) (P : C → Type) (W W' : FreeLoop (Σ C P)) (w : Id (FreeLoop (Σ C P)) W W')
  : Id (BoundaryFamily C P (free_loop_fst C P W'))
      (boundary_transport C P W (free_loop_fst C P W') (refl (free_loop_fst C P) w)) (W' .fst .snd, W' .snd .snd)
  ≔ J (FreeLoop (Σ C P)) W
      (W' w ↦ Id (BoundaryFamily C P (free_loop_fst C P W'))
        (boundary_transport C P W (free_loop_fst C P W') (refl (free_loop_fst C P) w)) (W' .fst .snd, W' .snd .snd))
      (transport_refl (FreeLoop C) (BoundaryFamily C P) (free_loop_fst C P W) (W .fst .snd, W .snd .snd))
      W' w

def section_transport (C : Type) (P : C → Type) (r r' : C → C) (H : Id (C → C) r r') (t : (x : C) → P (r x))
  (x : C) : P (r' x)
  ≔ transport C P (r x) (r' x) (happly C (_ ↦ C) r r' H x) (t x)

def section_boundary_lemma (C : Type) (b0 : C) (l0 : Id C b0 b0) (P : C → Type)
  (r : C → C) (t : (x : C) → P (r x)) (r' : C → C) (H : Id (C → C) r r')
  : Id (BoundaryFamily C P (free_loop_evaluation C b0 l0 C r'))
      (section_transport C P r r' H t b0, refl (section_transport C P r r' H t) l0)
      (boundary_transport C P (free_loop_evaluation C b0 l0 (Σ C P) (x ↦ (r x, t x)))
        (free_loop_evaluation C b0 l0 C r') (refl (free_loop_evaluation C b0 l0 C) H))
  ≔ J (C → C) r
      (r' H ↦ Id (BoundaryFamily C P (free_loop_evaluation C b0 l0 C r'))
        (section_transport C P r r' H t b0, refl (section_transport C P r r' H t) l0)
        (boundary_transport C P (free_loop_evaluation C b0 l0 (Σ C P) (x ↦ (r x, t x)))
          (free_loop_evaluation C b0 l0 C r') (refl (free_loop_evaluation C b0 l0 C) H)))
      (concat (BoundaryFamily C P (free_loop_evaluation C b0 l0 C r))
        (section_transport C P r r (refl r) t b0, refl (section_transport C P r r (refl r) t) l0)
        (t b0, refl t l0)
        (boundary_transport C P (free_loop_evaluation C b0 l0 (Σ C P) (x ↦ (r x, t x)))
          (free_loop_evaluation C b0 l0 C r) (refl (free_loop_evaluation C b0 l0 C r)))
        (refl ((g ↦ (g b0, refl g l0)) : ((x : C) → P (r x)) → BoundaryFamily C P (free_loop_evaluation C b0 l0 C r))
          (funext C (x ↦ P (r x)) (section_transport C P r r (refl r) t) t
            (x ↦ transport_refl C P (r x) (t x))))
        (inverse (BoundaryFamily C P (free_loop_evaluation C b0 l0 C r))
          (boundary_transport C P (free_loop_evaluation C b0 l0 (Σ C P) (x ↦ (r x, t x)))
            (free_loop_evaluation C b0 l0 C r) (refl (free_loop_evaluation C b0 l0 C r)))
          (t b0, refl t l0)
          (transport_refl (FreeLoop C) (BoundaryFamily C P) (free_loop_evaluation C b0 l0 C r) (t b0, refl t l0))))
      r' H

def circle_total_loop (C : Type) (b0 : C) (l0 : Id C b0 b0) (P : C → Type) (d : CircleBoundary C b0 l0 P)
  : FreeLoop (Σ C P)
  ≔ ((b0, d .fst), (l0, d .snd))

def circle_induction_from_recursion (C : Type) (b0 : C) (l0 : Id C b0 b0) (up : NondependentCircleProperty C b0 l0)
  (P : C → Type) (d : CircleBoundary C b0 l0 P)
  : Σ ((x : C) → P x) (f ↦ Id (CircleBoundary C b0 l0 P) (circle_evaluate C b0 l0 P f) d)
  ≔ let T ≔ Σ C P in
    let evT : Equiv (C → T) (FreeLoop T) ≔ (free_loop_evaluation C b0 l0 T, up T) in
    let evC : Equiv (C → C) (FreeLoop C) ≔ (free_loop_evaluation C b0 l0 C, up C) in
    let W0 ≔ circle_total_loop C b0 l0 P d in
    let s ≔ equiv_inverse_map (C → T) (FreeLoop T) evT W0 in
    let w ≔ equiv_counit (C → T) (FreeLoop T) evT W0 in
    let r ≔ ((x ↦ s x .fst) : C → C) in
    let t ≔ ((x ↦ s x .snd) : (x : C) → P (r x)) in
    let q ≔ refl (free_loop_fst C P) w in
    let paths ≔ equivalence_on_paths (C → C) (FreeLoop C) evC r (identity C) in
    let H ≔ equiv_inverse_map (Id (C → C) r (identity C))
      (Id (FreeLoop C) (evC .map r) (evC .map (identity C))) paths q in
    let Hq ≔ equiv_counit (Id (C → C) r (identity C))
      (Id (FreeLoop C) (evC .map r) (evC .map (identity C))) paths q in
    let f ≔ section_transport C P r (identity C) H t in
    (f, calc
      circle_evaluate C b0 l0 P f
      = boundary_transport C P (free_loop_evaluation C b0 l0 T s) (b0, l0) (refl (free_loop_evaluation C b0 l0 C) H)
        by section_boundary_lemma C b0 l0 P r t (identity C) H
      = boundary_transport C P (free_loop_evaluation C b0 l0 T s) (b0, l0) q
        by refl (boundary_transport C P (free_loop_evaluation C b0 l0 T s) (b0, l0)) Hq
      = d by boundary_transport_ap C P (free_loop_evaluation C b0 l0 T s) W0 w ∎)

def circle_nondependent_property
  : NondependentCircleProperty (CycleComponent zero.) (principal_component_point zero.) circle_loop
  ≔ A ↦ native_equivalence (CycleComponent zero. → A) (FreeLoop A) (circle_universal_equiv A) .equiv

{` The circle, constructed without postulates: the component of the
   standard infinite cycle, based there, with the successor symmetry as loop. `}
def constructed_circle : CircleSignature
  ≔ (CycleComponent zero., principal_component_point zero., circle_loop,
     P d ↦ circle_induction_from_recursion (CycleComponent zero.) (principal_component_point zero.) circle_loop
       circle_nondependent_property P d)
