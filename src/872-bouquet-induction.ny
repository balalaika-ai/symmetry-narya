export "871-bouquet-lift-data"
export "223-constructed-circle"

{` Nondependent universal property ⇒ induction with the coherent boundary
   identification required by FreeGroupSignature (generalizing
   circle_induction_from_recursion of module 223 from FreeLoop to
   BouquetData S).  For a type C with b0 : C and l0 : S → b0 = b0 such that
   evaluation (C → A) → BouquetData S A is an equivalence for EVERY type A,
   sections of every family P are obtained from a section of the total
   space Σ C P (recursion into Σ C P) corrected along the uniqueness of
   maps C → C. `}

def NondependentBouquetProperty (S C : Type) (b0 : C) (l0 : S → Id C b0 b0) : Type
  ≔ (A : Type) → isEquiv (C → A) (BouquetData S A) (fsc_bouquet_eval S C b0 l0 A)

def bouquet_first (S C : Type) (P : C → Type) (W : BouquetData S (Σ C P)) : BouquetData S C
  ≔ (W .fst .fst, a ↦ W .snd a .fst)

def BouquetBoundaryFamily (S C : Type) (P : C → Type) (u : BouquetData S C) : Type
  ≔ Σ (P (u .fst)) (p ↦ (a : S) → Id P (u .snd a) p p)

def bouquet_boundary_transport (S C : Type) (P : C → Type) (W : BouquetData S (Σ C P)) (u : BouquetData S C)
  (q : Id (BouquetData S C) (bouquet_first S C P W) u) : BouquetBoundaryFamily S C P u
  ≔ transport (BouquetData S C) (BouquetBoundaryFamily S C P) (bouquet_first S C P W) u q
      (W .fst .snd, a ↦ W .snd a .snd)

def bouquet_boundary_transport_ap (S C : Type) (P : C → Type) (W W' : BouquetData S (Σ C P))
  (w : Id (BouquetData S (Σ C P)) W W')
  : Id (BouquetBoundaryFamily S C P (bouquet_first S C P W'))
      (bouquet_boundary_transport S C P W (bouquet_first S C P W') (refl (bouquet_first S C P) w))
      (W' .fst .snd, a ↦ W' .snd a .snd)
  ≔ J (BouquetData S (Σ C P)) W
      (W' w ↦ Id (BouquetBoundaryFamily S C P (bouquet_first S C P W'))
        (bouquet_boundary_transport S C P W (bouquet_first S C P W') (refl (bouquet_first S C P) w))
        (W' .fst .snd, a ↦ W' .snd a .snd))
      (transport_refl (BouquetData S C) (BouquetBoundaryFamily S C P) (bouquet_first S C P W)
        (W .fst .snd, a ↦ W .snd a .snd))
      W' w

def bouquet_section_boundary_lemma (S C : Type) (b0 : C) (l0 : S → Id C b0 b0) (P : C → Type)
  (r : C → C) (t : (x : C) → P (r x)) (r' : C → C) (H : Id (C → C) r r')
  : Id (BouquetBoundaryFamily S C P (fsc_bouquet_eval S C b0 l0 C r'))
      (section_transport C P r r' H t b0, a ↦ refl (section_transport C P r r' H t) (l0 a))
      (bouquet_boundary_transport S C P (fsc_bouquet_eval S C b0 l0 (Σ C P) (x ↦ (r x, t x)))
        (fsc_bouquet_eval S C b0 l0 C r') (refl (fsc_bouquet_eval S C b0 l0 C) H))
  ≔ J (C → C) r
      (r' H ↦ Id (BouquetBoundaryFamily S C P (fsc_bouquet_eval S C b0 l0 C r'))
        (section_transport C P r r' H t b0, a ↦ refl (section_transport C P r r' H t) (l0 a))
        (bouquet_boundary_transport S C P (fsc_bouquet_eval S C b0 l0 (Σ C P) (x ↦ (r x, t x)))
          (fsc_bouquet_eval S C b0 l0 C r') (refl (fsc_bouquet_eval S C b0 l0 C) H)))
      (concat (BouquetBoundaryFamily S C P (fsc_bouquet_eval S C b0 l0 C r))
        (section_transport C P r r (refl r) t b0, a ↦ refl (section_transport C P r r (refl r) t) (l0 a))
        (t b0, a ↦ refl t (l0 a))
        (bouquet_boundary_transport S C P (fsc_bouquet_eval S C b0 l0 (Σ C P) (x ↦ (r x, t x)))
          (fsc_bouquet_eval S C b0 l0 C r) (refl (fsc_bouquet_eval S C b0 l0 C r)))
        (refl ((g ↦ (g b0, a ↦ refl g (l0 a)))
            : ((x : C) → P (r x)) → BouquetBoundaryFamily S C P (fsc_bouquet_eval S C b0 l0 C r))
          (funext C (x ↦ P (r x)) (section_transport C P r r (refl r) t) t
            (x ↦ transport_refl C P (r x) (t x))))
        (inverse (BouquetBoundaryFamily S C P (fsc_bouquet_eval S C b0 l0 C r))
          (bouquet_boundary_transport S C P (fsc_bouquet_eval S C b0 l0 (Σ C P) (x ↦ (r x, t x)))
            (fsc_bouquet_eval S C b0 l0 C r) (refl (fsc_bouquet_eval S C b0 l0 C r)))
          (t b0, a ↦ refl t (l0 a))
          (transport_refl (BouquetData S C) (BouquetBoundaryFamily S C P) (fsc_bouquet_eval S C b0 l0 C r)
            (t b0, a ↦ refl t (l0 a)))))
      r' H

def bouquet_total_data (S C : Type) (b0 : C) (l0 : S → Id C b0 b0) (P : C → Type)
  (d : FreeGroupBoundary S C b0 l0 P) : BouquetData S (Σ C P)
  ≔ ((b0, d .fst), a ↦ (l0 a, d .snd a))

def bouquet_induction_from_recursion (S C : Type) (b0 : C) (l0 : S → Id C b0 b0)
  (up : NondependentBouquetProperty S C b0 l0) (P : C → Type) (d : FreeGroupBoundary S C b0 l0 P)
  : Σ ((x : C) → P x) (f ↦ Id (FreeGroupBoundary S C b0 l0 P) (free_group_evaluate S C b0 l0 P f) d)
  ≔ let T ≔ Σ C P in
    let evT : Equiv (C → T) (BouquetData S T) ≔ (fsc_bouquet_eval S C b0 l0 T, up T) in
    let evC : Equiv (C → C) (BouquetData S C) ≔ (fsc_bouquet_eval S C b0 l0 C, up C) in
    let W0 ≔ bouquet_total_data S C b0 l0 P d in
    let s ≔ equiv_inverse_map (C → T) (BouquetData S T) evT W0 in
    let w ≔ equiv_counit (C → T) (BouquetData S T) evT W0 in
    let r ≔ ((x ↦ s x .fst) : C → C) in
    let t ≔ ((x ↦ s x .snd) : (x : C) → P (r x)) in
    let q ≔ refl (bouquet_first S C P) w in
    let paths ≔ equivalence_on_paths (C → C) (BouquetData S C) evC r (identity C) in
    let H ≔ equiv_inverse_map (Id (C → C) r (identity C))
      (Id (BouquetData S C) (evC .map r) (evC .map (identity C))) paths q in
    let Hq ≔ equiv_counit (Id (C → C) r (identity C))
      (Id (BouquetData S C) (evC .map r) (evC .map (identity C))) paths q in
    let f ≔ section_transport C P r (identity C) H t in
    (f, calc
      free_group_evaluate S C b0 l0 P f
      = bouquet_boundary_transport S C P (fsc_bouquet_eval S C b0 l0 T s) (b0, l0)
          (refl (fsc_bouquet_eval S C b0 l0 C) H)
        by bouquet_section_boundary_lemma S C b0 l0 P r t (identity C) H
      = bouquet_boundary_transport S C P (fsc_bouquet_eval S C b0 l0 T s) (b0, l0) q
        by refl (bouquet_boundary_transport S C P (fsc_bouquet_eval S C b0 l0 T s) (b0, l0)) Hq
      = d by bouquet_boundary_transport_ap S C P (fsc_bouquet_eval S C b0 l0 T s) W0 w ∎)

{` Any type with a point and S-indexed loops satisfying the nondependent
   universal property for every target type is a FreeGroupSignature S. `}
def free_group_signature_from_recursion (S C : Type) (b0 : C) (l0 : S → Id C b0 b0)
  (up : NondependentBouquetProperty S C b0 l0) : FreeGroupSignature S
  ≔ (C, b0, l0, P d ↦ bouquet_induction_from_recursion S C b0 l0 up P d)

def free_loops_bouquet_recursion (S : Type) (Q : FreeLoopsBouquet S)
  : NondependentBouquetProperty S (Q .carrier) (Q .base) (Q .loop)
  ≔ A ↦ bouquet_universal_equiv S Q A .equiv

{` A pointed type, merely connected to its base, whose loop space with left
   composition by the given loops is a weakly free S-set, is a free group
   signature on S. `}
def free_group_signature_from_free_loops (S : Type) (Q : FreeLoopsBouquet S) : FreeGroupSignature S
  ≔ free_group_signature_from_recursion S (Q .carrier) (Q .base) (Q .loop) (free_loops_bouquet_recursion S Q)
