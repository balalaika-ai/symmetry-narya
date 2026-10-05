export "1203-universal-cover"

{` Chapter 12, lemma:universal-cover-is-universal (abelian.tex 331-343): the
   projection fst : Ũ_a A →* (A, a) is universal in the sense of
   def:univ-cover (IsUniversalPointedCover, module 98), for an arbitrary
   pointed type (A, a).

   Proof, following the book: for a pointed set bundle g : (C, c0) →* (A, a)
   with fibers F(x) ≔ g⁻¹(x), lifts h with fst = g ∘ h correspond to pointed
   sections s : Π(u : Ũ_a A) F(fst u) with s(a, |refl|) = (c0, g0); such a
   section is determined on |p|₀ by path induction on p (s(x, |p|₀) is the
   transport of (c0, g0) along p), so the type of pointed sections is
   contractible, and the lifts form a retract of it. `}

{` The pointing coherence of a lift, as a path over q in the fiber family. `}
def covering_pointing_equiv (A C : Type) (g : C → A) (a : A) (c0 : C) (g0 : Id A a (g c0)) (c : C)
  (q : Id C c0 c) (e2 : Id A a (g c))
  : Equiv (Id (Id A a (g c)) (concat A a a (g c) (refl a) e2) (concat A a (g c0) (g c) g0 (refl g q)))
      (Id ((z ↦ Id A a (g z)) : C → Type) q g0 e2)
  ≔ J C c0
      (c q ↦ (e2 : Id A a (g c)) → Equiv (Id (Id A a (g c)) (concat A a a (g c) (refl a) e2) (concat A a (g c0) (g c) g0 (refl g q)))
        (Id ((z ↦ Id A a (g z)) : C → Type) q g0 e2))
      (e2 ↦ compose_equiv
        (Id (Id A a (g c0)) (concat A a a (g c0) (refl a) e2) (concat A a (g c0) (g c0) g0 (refl (g c0))))
        (Id (Id A a (g c0)) e2 g0) (Id (Id A a (g c0)) g0 e2)
        (path_endpoints_equiv (Id A a (g c0)) (concat A a a (g c0) (refl a) e2) e2
          (concat A a (g c0) (g c0) g0 (refl (g c0))) g0
          (inverse (Id A a (g c0)) (concat A a a (g c0) (refl a) e2) e2 (concat_1p A a (g c0) e2))
          (concat_p1 A a (g c0) g0))
        (inverse_path_equiv (Id A a (g c0)) e2 g0))
      c q e2

{` Pointed sections over Ũ_a A of the fibers of g. `}
def CoverSections (A : Type) (a : A) (C : Pointed) (g : BookPointedMap C (A, a)) : Type
  ≔ Σ ((u : UnivCover A a) → BookFiber (C .carrier) A (g .fst) (u .fst))
      (s ↦ Id (BookFiber (C .carrier) A (g .fst) a) (C .point, g .snd) (s (univ_cover_point A a)))

def cover_sections_center (A : Type) (a : A) (C : Pointed) (g : BookPointedMap C (A, a))
  (cov : IsCovering (C .carrier) A (g .fst)) : CoverSections A a C g
  ≔ let F ≔ (x ↦ BookFiber (C .carrier) A (g .fst) x) : A → Type in
    ((u ↦ set_trunc_rec (Id A a (u .fst)) (F (u .fst)) (cov (u .fst))
        (p ↦ transport A F a (u .fst) p (C .point, g .snd)) (u .snd)),
     inverse (F a) (transport A F a a (refl a) (C .point, g .snd)) (C .point, g .snd)
       (transport_refl A F a (C .point, g .snd)))

def cover_sections_contractible (A : Type) (a : A) (C : Pointed) (g : BookPointedMap C (A, a))
  (cov : IsCovering (C .carrier) A (g .fst)) : BookIsContr (CoverSections A a C g)
  ≔ let F ≔ (x ↦ BookFiber (C .carrier) A (g .fst) x) : A → Type in
    let c0 ≔ cover_sections_center A a C g cov in
    let S ≔ (u : UnivCover A a) → F (u .fst) in
    let P ≔ (s ↦ Id (F a) (C .point, g .snd) (s (univ_cover_point A a))) : S → Type in
    (c0, t ↦ subtype_equal S P (s ↦ cov a (C .point, g .snd) (s (univ_cover_point A a))) c0 t
      (funext (UnivCover A a) (u ↦ F (u .fst)) (c0 .fst) (t .fst)
        (u ↦ set_trunc_induction (Id A a (u .fst))
          (α ↦ Id (F (u .fst)) (c0 .fst (u .fst, α)) (t .fst (u .fst, α)))
          (α ↦ prop_is_set (Id (F (u .fst)) (c0 .fst (u .fst, α)) (t .fst (u .fst, α)))
            (cov (u .fst) (c0 .fst (u .fst, α)) (t .fst (u .fst, α))))
          (p ↦ J A a (x p ↦ Id (F x) (transport A F a x p (C .point, g .snd)) (t .fst (x, set_trunc (Id A a x) p)))
            (concat (F a) (transport A F a a (refl a) (C .point, g .snd)) (C .point, g .snd)
              (t .fst (univ_cover_point A a)) (transport_refl A F a (C .point, g .snd)) (t .snd))
            (u .fst) p)
          (u .snd))))

{` Lifts and pointed sections: PointedCoverLifts ≃ CoverSections, as a
   composite of equivalences (pointed homotopies, regrouping, paths in the
   fiber over a). `}
def cover_lift_homotopy_equiv (A : Type) (a : A) (C : Pointed) (g : BookPointedMap C (A, a))
  : Equiv (PointedCoverLifts (univ_cover_pointed A a) (A, a) C (univ_cover_projection A a) g)
      (Σ (BookPointedMap (univ_cover_pointed A a) C)
        (h ↦ PointedHomotopy (univ_cover_pointed A a) (A, a) (univ_cover_projection A a)
          (book_pointed_compose (univ_cover_pointed A a) C (A, a) h g)))
  ≔ let U ≔ univ_cover_pointed A a in
    family_equiv (BookPointedMap U C)
      (h ↦ Id (BookPointedMap U (A, a)) (univ_cover_projection A a) (book_pointed_compose U C (A, a) h g))
      (h ↦ PointedHomotopy U (A, a) (univ_cover_projection A a) (book_pointed_compose U C (A, a) h g))
      (h ↦ pointed_map_path_equiv U (A, a) (univ_cover_projection A a) (book_pointed_compose U C (A, a) h g))

def CoverPointing (A : Type) (a : A) (C : Pointed) (g : BookPointedMap C (A, a))
  (s : (u : UnivCover A a) → BookFiber (C .carrier) A (g .fst) (u .fst)) : Type
  ≔ Σ (Id (C .carrier) (C .point) (s (univ_cover_point A a) .fst))
      (q ↦ Id (Id A a (g .fst (s (univ_cover_point A a) .fst)))
        (concat A a a (g .fst (s (univ_cover_point A a) .fst)) (refl a) (s (univ_cover_point A a) .snd))
        (concat A a (g .fst (C .point)) (g .fst (s (univ_cover_point A a) .fst)) (g .snd) (refl (g .fst) q)))

def cover_lift_regroup_equiv (A : Type) (a : A) (C : Pointed) (g : BookPointedMap C (A, a))
  : Equiv (Σ (BookPointedMap (univ_cover_pointed A a) C)
        (h ↦ PointedHomotopy (univ_cover_pointed A a) (A, a) (univ_cover_projection A a)
          (book_pointed_compose (univ_cover_pointed A a) C (A, a) h g)))
      (Σ ((u : UnivCover A a) → BookFiber (C .carrier) A (g .fst) (u .fst)) (CoverPointing A a C g))
  ≔ let U ≔ univ_cover_pointed A a in
    let S ≔ Σ (BookPointedMap U C)
        (h ↦ PointedHomotopy U (A, a) (univ_cover_projection A a) (book_pointed_compose U C (A, a) h g)) in
    let T ≔ Σ ((u : UnivCover A a) → BookFiber (C .carrier) A (g .fst) (u .fst)) (CoverPointing A a C g) in
    quasi_inverse_equiv S T
      (w ↦ ((u ↦ (w .fst .fst u, w .snd .fst u)), (w .fst .snd, w .snd .snd)))
      (t ↦ (((u ↦ t .fst u .fst), t .snd .fst), ((u ↦ t .fst u .snd), t .snd .snd)))
      (w ↦ refl w) (t ↦ refl t)

def cover_pointing_equiv (A : Type) (a : A) (C : Pointed) (g : BookPointedMap C (A, a))
  (s : (u : UnivCover A a) → BookFiber (C .carrier) A (g .fst) (u .fst))
  : Equiv (CoverPointing A a C g s)
      (Id (BookFiber (C .carrier) A (g .fst) a) (C .point, g .snd) (s (univ_cover_point A a)))
  ≔ let c ≔ s (univ_cover_point A a) .fst in let e2 ≔ s (univ_cover_point A a) .snd in
    let F ≔ (z ↦ Id A a (g .fst z)) : C .carrier → Type in
    compose_equiv (CoverPointing A a C g s) (SigmaPath (C .carrier) F (C .point, g .snd) (c, e2))
      (Id (BookFiber (C .carrier) A (g .fst) a) (C .point, g .snd) (c, e2))
      (family_equiv (Id (C .carrier) (C .point) c)
        (q ↦ Id (Id A a (g .fst c)) (concat A a a (g .fst c) (refl a) e2)
          (concat A a (g .fst (C .point)) (g .fst c) (g .snd) (refl (g .fst) q)))
        (q ↦ Id F q (g .snd) e2)
        (q ↦ covering_pointing_equiv A (C .carrier) (g .fst) a (C .point) (g .snd) c q e2))
      (sigma_path_equiv (C .carrier) F (C .point, g .snd) (c, e2))

def cover_lift_sections_equiv (A : Type) (a : A) (C : Pointed) (g : BookPointedMap C (A, a))
  : Equiv (PointedCoverLifts (univ_cover_pointed A a) (A, a) C (univ_cover_projection A a) g) (CoverSections A a C g)
  ≔ let U ≔ univ_cover_pointed A a in
    let S ≔ (u : UnivCover A a) → BookFiber (C .carrier) A (g .fst) (u .fst) in
    compose_equiv (PointedCoverLifts U (A, a) C (univ_cover_projection A a) g)
      (Σ (BookPointedMap U C) (h ↦ PointedHomotopy U (A, a) (univ_cover_projection A a) (book_pointed_compose U C (A, a) h g)))
      (CoverSections A a C g)
      (cover_lift_homotopy_equiv A a C g)
      (compose_equiv
        (Σ (BookPointedMap U C) (h ↦ PointedHomotopy U (A, a) (univ_cover_projection A a) (book_pointed_compose U C (A, a) h g)))
        (Σ S (CoverPointing A a C g)) (CoverSections A a C g)
        (cover_lift_regroup_equiv A a C g)
        (family_equiv S (CoverPointing A a C g)
          (s ↦ Id (BookFiber (C .carrier) A (g .fst) a) (C .point, g .snd) (s (univ_cover_point A a)))
          (cover_pointing_equiv A a C g)))

{` lemma:universal-cover-is-universal. `}
def univ_cover_universal (A : Type) (a : A)
  : IsUniversalPointedCover (univ_cover_pointed A a) (A, a) (univ_cover_projection A a)
  ≔ C g cov ↦ book_contractibility_equiv (CoverSections A a C g)
      (PointedCoverLifts (univ_cover_pointed A a) (A, a) C (univ_cover_projection A a) g)
      (canonical_inverse_equiv (PointedCoverLifts (univ_cover_pointed A a) (A, a) C (univ_cover_projection A a) g)
        (CoverSections A a C g) (cover_lift_sections_equiv A a C g))
      .map (cover_sections_contractible A a C g cov)

{` Together with univ_cover_projection_covering, fst is a universal pointed
   set bundle (an element of BookPointedCoverings with universality). `}
def univ_cover_pointed_covering (A : Type) (a : A) : BookPointedCoverings (A, a)
  ≔ (univ_cover_pointed A a, (univ_cover_projection A a, univ_cover_projection_covering A a))
