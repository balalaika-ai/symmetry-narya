export "877-constructed-free-groups"

{` Nondependent universal property ⇒ wedge induction (as module 223 for the
   circle and module 872 for bouquets).  If X has maps i1 : A1 → X,
   i2 : A2 → X and g : i1 a1 = i2 a2 such that, for EVERY type T, the
   cocone evaluation (X → T) → WedgeCocone A1 A2 T, h ↦ (h i1, h i2, ap_h g)
   is an equivalence, then (X, i1, i2, g) is a WedgeSignature (def:wedge,
   module 841), with the coherent boundary identification. `}

def fsc_wedge_cocone_eval (A1 A2 : Pointed) (X : Type) (i1 : A1 .carrier → X) (i2 : A2 .carrier → X)
  (g : Id X (i1 (A1 .point)) (i2 (A2 .point))) (T : Type) (h : X → T) : WedgeCocone A1 A2 T
  ≔ (a ↦ h (i1 a), (a ↦ h (i2 a), refl h g))

def NondependentWedgeProperty (A1 A2 : Pointed) (X : Type) (i1 : A1 .carrier → X) (i2 : A2 .carrier → X)
  (g : Id X (i1 (A1 .point)) (i2 (A2 .point))) : Type
  ≔ (T : Type) → isEquiv (X → T) (WedgeCocone A1 A2 T) (fsc_wedge_cocone_eval A1 A2 X i1 i2 g T)

def wedge_cocone_first (A1 A2 : Pointed) (X : Type) (P : X → Type) (W : WedgeCocone A1 A2 (Σ X P))
  : WedgeCocone A1 A2 X
  ≔ (a ↦ W .fst a .fst, (a ↦ W .snd .fst a .fst, W .snd .snd .fst))

def WedgeBoundaryFamily (A1 A2 : Pointed) (X : Type) (P : X → Type) (u : WedgeCocone A1 A2 X) : Type
  ≔ Σ ((a : A1 .carrier) → P (u .fst a)) (s1 ↦ Σ ((a : A2 .carrier) → P (u .snd .fst a)) (s2 ↦
      Id P (u .snd .snd) (s1 (A1 .point)) (s2 (A2 .point))))

def wedge_cocone_second (A1 A2 : Pointed) (X : Type) (P : X → Type) (W : WedgeCocone A1 A2 (Σ X P))
  : WedgeBoundaryFamily A1 A2 X P (wedge_cocone_first A1 A2 X P W)
  ≔ (a ↦ W .fst a .snd, (a ↦ W .snd .fst a .snd, W .snd .snd .snd))

def wedge_boundary_transport (A1 A2 : Pointed) (X : Type) (P : X → Type) (W : WedgeCocone A1 A2 (Σ X P))
  (u : WedgeCocone A1 A2 X) (q : Id (WedgeCocone A1 A2 X) (wedge_cocone_first A1 A2 X P W) u)
  : WedgeBoundaryFamily A1 A2 X P u
  ≔ transport (WedgeCocone A1 A2 X) (WedgeBoundaryFamily A1 A2 X P) (wedge_cocone_first A1 A2 X P W) u q
      (wedge_cocone_second A1 A2 X P W)

def wedge_boundary_transport_ap (A1 A2 : Pointed) (X : Type) (P : X → Type) (W W' : WedgeCocone A1 A2 (Σ X P))
  (w : Id (WedgeCocone A1 A2 (Σ X P)) W W')
  : Id (WedgeBoundaryFamily A1 A2 X P (wedge_cocone_first A1 A2 X P W'))
      (wedge_boundary_transport A1 A2 X P W (wedge_cocone_first A1 A2 X P W') (refl (wedge_cocone_first A1 A2 X P) w))
      (wedge_cocone_second A1 A2 X P W')
  ≔ J (WedgeCocone A1 A2 (Σ X P)) W
      (W' w ↦ Id (WedgeBoundaryFamily A1 A2 X P (wedge_cocone_first A1 A2 X P W'))
        (wedge_boundary_transport A1 A2 X P W (wedge_cocone_first A1 A2 X P W') (refl (wedge_cocone_first A1 A2 X P) w))
        (wedge_cocone_second A1 A2 X P W'))
      (transport_refl (WedgeCocone A1 A2 X) (WedgeBoundaryFamily A1 A2 X P) (wedge_cocone_first A1 A2 X P W)
        (wedge_cocone_second A1 A2 X P W))
      W' w

def wedge_section_boundary (A1 A2 : Pointed) (X : Type) (i1 : A1 .carrier → X) (i2 : A2 .carrier → X)
  (g : Id X (i1 (A1 .point)) (i2 (A2 .point))) (P : X → Type) (r : X → X) (s : (x : X) → P (r x))
  : WedgeBoundaryFamily A1 A2 X P (fsc_wedge_cocone_eval A1 A2 X i1 i2 g X r)
  ≔ (a ↦ s (i1 a), (a ↦ s (i2 a), refl s g))

def wedge_section_boundary_lemma (A1 A2 : Pointed) (X : Type) (i1 : A1 .carrier → X) (i2 : A2 .carrier → X)
  (g : Id X (i1 (A1 .point)) (i2 (A2 .point))) (P : X → Type)
  (r : X → X) (t : (x : X) → P (r x)) (r' : X → X) (H : Id (X → X) r r')
  : Id (WedgeBoundaryFamily A1 A2 X P (fsc_wedge_cocone_eval A1 A2 X i1 i2 g X r'))
      (wedge_section_boundary A1 A2 X i1 i2 g P r' (section_transport X P r r' H t))
      (wedge_boundary_transport A1 A2 X P (fsc_wedge_cocone_eval A1 A2 X i1 i2 g (Σ X P) (x ↦ (r x, t x)))
        (fsc_wedge_cocone_eval A1 A2 X i1 i2 g X r') (refl (fsc_wedge_cocone_eval A1 A2 X i1 i2 g X) H))
  ≔ J (X → X) r
      (r' H ↦ Id (WedgeBoundaryFamily A1 A2 X P (fsc_wedge_cocone_eval A1 A2 X i1 i2 g X r'))
        (wedge_section_boundary A1 A2 X i1 i2 g P r' (section_transport X P r r' H t))
        (wedge_boundary_transport A1 A2 X P (fsc_wedge_cocone_eval A1 A2 X i1 i2 g (Σ X P) (x ↦ (r x, t x)))
          (fsc_wedge_cocone_eval A1 A2 X i1 i2 g X r') (refl (fsc_wedge_cocone_eval A1 A2 X i1 i2 g X) H)))
      (concat (WedgeBoundaryFamily A1 A2 X P (fsc_wedge_cocone_eval A1 A2 X i1 i2 g X r))
        (wedge_section_boundary A1 A2 X i1 i2 g P r (section_transport X P r r (refl r) t))
        (wedge_section_boundary A1 A2 X i1 i2 g P r t)
        (wedge_boundary_transport A1 A2 X P (fsc_wedge_cocone_eval A1 A2 X i1 i2 g (Σ X P) (x ↦ (r x, t x)))
          (fsc_wedge_cocone_eval A1 A2 X i1 i2 g X r) (refl (fsc_wedge_cocone_eval A1 A2 X i1 i2 g X r)))
        (refl (wedge_section_boundary A1 A2 X i1 i2 g P r)
          (funext X (x ↦ P (r x)) (section_transport X P r r (refl r) t) t
            (x ↦ transport_refl X P (r x) (t x))))
        (inverse (WedgeBoundaryFamily A1 A2 X P (fsc_wedge_cocone_eval A1 A2 X i1 i2 g X r))
          (wedge_boundary_transport A1 A2 X P (fsc_wedge_cocone_eval A1 A2 X i1 i2 g (Σ X P) (x ↦ (r x, t x)))
            (fsc_wedge_cocone_eval A1 A2 X i1 i2 g X r) (refl (fsc_wedge_cocone_eval A1 A2 X i1 i2 g X r)))
          (wedge_section_boundary A1 A2 X i1 i2 g P r t)
          (transport_refl (WedgeCocone A1 A2 X) (WedgeBoundaryFamily A1 A2 X P) (fsc_wedge_cocone_eval A1 A2 X i1 i2 g X r)
            (wedge_section_boundary A1 A2 X i1 i2 g P r t))))
      r' H

def wedge_total_cocone (A1 A2 : Pointed) (X : Type) (i1 : A1 .carrier → X) (i2 : A2 .carrier → X)
  (g : Id X (i1 (A1 .point)) (i2 (A2 .point))) (P : X → Type) (d : WedgeBoundary A1 A2 X i1 i2 g P)
  : WedgeCocone A1 A2 (Σ X P)
  ≔ (a ↦ (i1 a, d .fst a), (a ↦ (i2 a, d .snd .fst a), (g, d .snd .snd)))

def wedge_induction_from_recursion (A1 A2 : Pointed) (X : Type) (i1 : A1 .carrier → X) (i2 : A2 .carrier → X)
  (g : Id X (i1 (A1 .point)) (i2 (A2 .point))) (up : NondependentWedgeProperty A1 A2 X i1 i2 g)
  (P : X → Type) (d : WedgeBoundary A1 A2 X i1 i2 g P)
  : Σ ((x : X) → P x) (f ↦ Id (WedgeBoundary A1 A2 X i1 i2 g P) (wedge_evaluate A1 A2 X i1 i2 g P f) d)
  ≔ let T ≔ Σ X P in
    let evT : Equiv (X → T) (WedgeCocone A1 A2 T) ≔ (fsc_wedge_cocone_eval A1 A2 X i1 i2 g T, up T) in
    let evX : Equiv (X → X) (WedgeCocone A1 A2 X) ≔ (fsc_wedge_cocone_eval A1 A2 X i1 i2 g X, up X) in
    let W0 ≔ wedge_total_cocone A1 A2 X i1 i2 g P d in
    let s ≔ equiv_inverse_map (X → T) (WedgeCocone A1 A2 T) evT W0 in
    let w ≔ equiv_counit (X → T) (WedgeCocone A1 A2 T) evT W0 in
    let r ≔ ((x ↦ s x .fst) : X → X) in
    let t ≔ ((x ↦ s x .snd) : (x : X) → P (r x)) in
    let q ≔ refl (wedge_cocone_first A1 A2 X P) w in
    let paths ≔ equivalence_on_paths (X → X) (WedgeCocone A1 A2 X) evX r (identity X) in
    let H ≔ equiv_inverse_map (Id (X → X) r (identity X))
      (Id (WedgeCocone A1 A2 X) (evX .map r) (evX .map (identity X))) paths q in
    let Hq ≔ equiv_counit (Id (X → X) r (identity X))
      (Id (WedgeCocone A1 A2 X) (evX .map r) (evX .map (identity X))) paths q in
    let f ≔ section_transport X P r (identity X) H t in
    (f, calc
      wedge_evaluate A1 A2 X i1 i2 g P f
      = wedge_boundary_transport A1 A2 X P (fsc_wedge_cocone_eval A1 A2 X i1 i2 g T s) (a ↦ i1 a, (a ↦ i2 a, g))
          (refl (fsc_wedge_cocone_eval A1 A2 X i1 i2 g X) H)
        by wedge_section_boundary_lemma A1 A2 X i1 i2 g P r t (identity X) H
      = wedge_boundary_transport A1 A2 X P (fsc_wedge_cocone_eval A1 A2 X i1 i2 g T s) (a ↦ i1 a, (a ↦ i2 a, g)) q
        by refl (wedge_boundary_transport A1 A2 X P (fsc_wedge_cocone_eval A1 A2 X i1 i2 g T s) (a ↦ i1 a, (a ↦ i2 a, g))) Hq
      = d by wedge_boundary_transport_ap A1 A2 X P (fsc_wedge_cocone_eval A1 A2 X i1 i2 g T s) W0 w ∎)

def wedge_signature_from_recursion (A1 A2 : Pointed) (X : Type) (i1 : A1 .carrier → X) (i2 : A2 .carrier → X)
  (g : Id X (i1 (A1 .point)) (i2 (A2 .point))) (up : NondependentWedgeProperty A1 A2 X i1 i2 g)
  : WedgeSignature A1 A2
  ≔ (X, i1, i2, g, P d ↦ wedge_induction_from_recursion A1 A2 X i1 i2 g up P d)
