export "651-precomposition-extensions"
export "621-functor-categories"

{` Chapter 6, lem:precomp-equiv-cat, part 3 (HoTT book Theorem 9.9.4):
   the extension G of F : C → E along a weak equivalence H : C → D (E a
   category), G(d) the object of the contractible type ExtObj at d, and
   G(g) the unique m with k_{c',h'} ∘ F(f) = m ∘ k_{c,h} whenever
   h' ∘ H(f) = g ∘ h; then GH ≅ F, so - ∘ H is split essentially
   surjective, and with module 650 it is an equivalence. `}

{` The extension data are taken from an abstract proof ec that each
   ExtObj is contractible (instantiated with ext_obj_contractible only at
   the very end): this keeps the centers neutral, so that the type checker
   never normalizes the contraction proofs. `}
def ext_functor_obj (C D : WildPrecat) (E : Category) (H : WildFunctor C D) (F : WildFunctor C (E .wild))
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b)) (eso : IsEso C D H)
  (ec : (d : D .ob) → isContr (ExtObj C D (E .wild) H F d))
  (d : D .ob) : E .wild .ob
  ≔ ec d .center .fst .fst

def ext_functor_iso (C D : WildPrecat) (E : Category) (H : WildFunctor C D) (F : WildFunctor C (E .wild))
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b)) (eso : IsEso C D H)
  (ec : (d : D .ob) → isContr (ExtObj C D (E .wild) H F d))
  (d : D .ob) (c : C .ob) (h : CatIso D (H .obj c) d) : CatIso (E .wild) (F .obj c) (ext_functor_obj C D E H F hH eso ec d)
  ≔ ec d .center .fst .snd c h

def ext_functor_compatible (C D : WildPrecat) (E : Category) (H : WildFunctor C D) (F : WildFunctor C (E .wild))
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b)) (eso : IsEso C D H)
  (ec : (d : D .ob) → isContr (ExtObj C D (E .wild) H F d))
  (d : D .ob) : ExtCompatible C D (E .wild) H F d (ec d .center .fst)
  ≔ ec d .center .snd

{` The condition determining G(g). `}
def ExtMorCond (C D : WildPrecat) (E : Category) (H : WildFunctor C D) (F : WildFunctor C (E .wild))
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b)) (eso : IsEso C D H)
  (ec : (d : D .ob) → isContr (ExtObj C D (E .wild) H F d))
  (d d' : D .ob) (g : D .hom d d')
  (m : E .wild .hom (ext_functor_obj C D E H F hH eso ec d) (ext_functor_obj C D E H F hH eso ec d')) : Type
  ≔ let Gd ≔ ext_functor_obj C D E H F hH eso ec d in
    let Gd' ≔ ext_functor_obj C D E H F hH eso ec d' in
    (c c' : C .ob) (h : CatIso D (H .obj c) d) (h' : CatIso D (H .obj c') d') (f : C .hom c c')
    → Id (D .hom (H .obj c) d') (D .comp (H .obj c) (H .obj c') d' (h' .fst) (H .mor c c' f))
        (D .comp (H .obj c) d d' g (h .fst))
    → Id (E .wild .hom (F .obj c) Gd')
        (E .wild .comp (F .obj c) (F .obj c') Gd' (ext_functor_iso C D E H F hH eso ec d' c' h' .fst) (F .mor c c' f))
        (E .wild .comp (F .obj c) Gd Gd' m (ext_functor_iso C D E H F hH eso ec d c h .fst))

def ExtMor (C D : WildPrecat) (E : Category) (H : WildFunctor C D) (F : WildFunctor C (E .wild))
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b)) (eso : IsEso C D H)
  (ec : (d : D .ob) → isContr (ExtObj C D (E .wild) H F d))
  (d d' : D .ob) (g : D .hom d d') : Type
  ≔ Σ (E .wild .hom (ext_functor_obj C D E H F hH eso ec d) (ext_functor_obj C D E H F hH eso ec d'))
      (ExtMorCond C D E H F hH eso ec d d' g)

def ext_mor_cond_prop (C D : WildPrecat) (E : Category) (H : WildFunctor C D) (F : WildFunctor C (E .wild))
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b)) (eso : IsEso C D H)
  (ec : (d : D .ob) → isContr (ExtObj C D (E .wild) H F d))
  (d d' : D .ob) (g : D .hom d d')
  (m : E .wild .hom (ext_functor_obj C D E H F hH eso ec d) (ext_functor_obj C D E H F hH eso ec d'))
  : isProp (ExtMorCond C D E H F hH eso ec d d' g m)
  ≔ let Ew ≔ E .wild in
    let Gd ≔ ext_functor_obj C D E H F hH eso ec d in
    let Gd' ≔ ext_functor_obj C D E H F hH eso ec d' in
    let k ≔ ext_functor_iso C D E H F hH eso ec d in
    let k' ≔ ext_functor_iso C D E H F hH eso ec d' in
    ch6c_pi_prop5 (C .ob) (_ ↦ C .ob) (c _ ↦ CatIso D (H .obj c) d) (_ c' _ ↦ CatIso D (H .obj c') d')
      (c c' _ _ ↦ C .hom c c')
      (c c' h h' f ↦ Id (D .hom (H .obj c) d') (D .comp (H .obj c) (H .obj c') d' (h' .fst) (H .mor c c' f))
          (D .comp (H .obj c) d d' g (h .fst))
        → Id (Ew .hom (F .obj c) Gd') (Ew .comp (F .obj c) (F .obj c') Gd' (k' c' h' .fst) (F .mor c c' f))
            (Ew .comp (F .obj c) Gd Gd' m (k c h .fst)))
      (c c' h h' f ↦ pi_prop (Id (D .hom (H .obj c) d') (D .comp (H .obj c) (H .obj c') d' (h' .fst) (H .mor c c' f))
          (D .comp (H .obj c) d d' g (h .fst)))
        (_ ↦ Id (Ew .hom (F .obj c) Gd') (Ew .comp (F .obj c) (F .obj c') Gd' (k' c' h' .fst) (F .mor c c' f))
            (Ew .comp (F .obj c) Gd Gd' m (k c h .fst)))
        (_ ↦ E .homset (F .obj c) Gd' (Ew .comp (F .obj c) (F .obj c') Gd' (k' c' h' .fst) (F .mor c c' f))
            (Ew .comp (F .obj c) Gd Gd' m (k c h .fst))))

def ext_mor_unique_at (C D : WildPrecat) (E : Category) (H : WildFunctor C D) (F : WildFunctor C (E .wild))
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b)) (eso : IsEso C D H)
  (ec : (d : D .ob) → isContr (ExtObj C D (E .wild) H F d))
  (d d' : D .ob) (g : D .hom d d') (u v : ExtMor C D E H F hH eso ec d d' g)
  (c : C .ob) (h : CatIso D (H .obj c) d) (c' : C .ob) (h' : CatIso D (H .obj c') d')
  : Id (E .wild .hom (ext_functor_obj C D E H F hH eso ec d) (ext_functor_obj C D E H F hH eso ec d')) (u .fst) (v .fst)
  ≔ let Ew ≔ E .wild in
    let Gd ≔ ext_functor_obj C D E H F hH eso ec d in
    let Gd' ≔ ext_functor_obj C D E H F hH eso ec d' in
    let k ≔ ext_functor_iso C D E H F hH eso ec d c h in
    let l ≔ ff_lift_through_iso C D H hH c c' d' h' (D .comp (H .obj c) d d' g (h .fst)) in
    equivalence_injective (Ew .hom Gd Gd') (Ew .hom (F .obj c) Gd')
      (cat_precompose_equiv Ew (F .obj c) Gd (k .fst) (k .snd) Gd') (u .fst) (v .fst)
      (concat (Ew .hom (F .obj c) Gd') (Ew .comp (F .obj c) Gd Gd' (u .fst) (k .fst))
        (Ew .comp (F .obj c) (F .obj c') Gd' (ext_functor_iso C D E H F hH eso ec d' c' h' .fst) (F .mor c c' (l .fst)))
        (Ew .comp (F .obj c) Gd Gd' (v .fst) (k .fst))
        (inverse (Ew .hom (F .obj c) Gd')
          (Ew .comp (F .obj c) (F .obj c') Gd' (ext_functor_iso C D E H F hH eso ec d' c' h' .fst) (F .mor c c' (l .fst)))
          (Ew .comp (F .obj c) Gd Gd' (u .fst) (k .fst)) (u .snd c c' h h' (l .fst) (l .snd)))
        (v .snd c c' h h' (l .fst) (l .snd)))

def ext_mor_prop (C D : WildPrecat) (E : Category) (H : WildFunctor C D) (F : WildFunctor C (E .wild))
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b)) (eso : IsEso C D H)
  (ec : (d : D .ob) → isContr (ExtObj C D (E .wild) H F d))
  (d d' : D .ob) (g : D .hom d d') : isProp (ExtMor C D E H F hH eso ec d d' g)
  ≔ u v ↦
      let Gd ≔ ext_functor_obj C D E H F hH eso ec d in
      let Gd' ≔ ext_functor_obj C D E H F hH eso ec d' in
      let T ≔ Id (E .wild .hom Gd Gd') (u .fst) (v .fst) in
      let p : T
        ≔ mere_rec (Σ (C .ob) (c ↦ CatIso D (H .obj c) d)) T (E .homset Gd Gd' (u .fst) (v .fst))
            (t ↦ mere_rec (Σ (C .ob) (c ↦ CatIso D (H .obj c) d')) T (E .homset Gd Gd' (u .fst) (v .fst))
              (t' ↦ ext_mor_unique_at C D E H F hH eso ec d d' g u v (t .fst) (t .snd) (t' .fst) (t' .snd)) (eso d'))
            (eso d) in
      (p, pathover_of_eq (E .wild .hom Gd Gd') (ExtMorCond C D E H F hH eso ec d d' g) (u .fst) (v .fst) p (u .snd) (v .snd)
         (ext_mor_cond_prop C D E H F hH eso ec d d' g (v .fst)
           (transport (E .wild .hom Gd Gd') (ExtMorCond C D E H F hH eso ec d d' g) (u .fst) (v .fst) p (u .snd)) (v .snd)))

{` Existence of G(g) from h : H(c) ≅ d and h' : H(c') ≅ d':
   m = (k_{c',h'} ∘ F(f)) ∘ k_{c,h}⁻¹ with h' ∘ H(f) = g ∘ h. `}
def ext_mor_from_isos (C D : WildPrecat) (E : Category) (H : WildFunctor C D) (F : WildFunctor C (E .wild))
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b)) (eso : IsEso C D H)
  (ec : (d : D .ob) → isContr (ExtObj C D (E .wild) H F d))
  (d d' : D .ob) (g : D .hom d d') (c : C .ob) (h : CatIso D (H .obj c) d) (c' : C .ob) (h' : CatIso D (H .obj c') d')
  : ExtMor C D E H F hH eso ec d d' g
  ≔ let Ew ≔ E .wild in
    let Gd ≔ ext_functor_obj C D E H F hH eso ec d in
    let Gd' ≔ ext_functor_obj C D E H F hH eso ec d' in
    let kd ≔ ext_functor_iso C D E H F hH eso ec d in
    let kd' ≔ ext_functor_iso C D E H F hH eso ec d' in
    let Fc ≔ F .obj c in
    let Fc' ≔ F .obj c' in
    let Hc ≔ H .obj c in
    let Hc' ≔ H .obj c' in
    let l ≔ ff_lift_through_iso C D H hH c c' d' h' (D .comp Hc d d' g (h .fst)) in
    let f ≔ l .fst in
    let X ≔ Ew .comp Fc Fc' Gd' (kd' c' h' .fst) (F .mor c c' f) in
    let m ≔ Ew .comp Gd Fc Gd' X (cat_iso_inverse Ew Fc Gd (kd c h) .fst) in
    let mk : Id (Ew .hom Fc Gd') (Ew .comp Fc Gd Gd' m (kd c h .fst)) X
      ≔ cat_iso_inverse_cancel_right Ew Fc Gd Gd' (kd c h) X in
    (m, c1 c1' h1 h1' f1 q1 ↦
      let Hc1 ≔ H .obj c1 in
      let Hc1' ≔ H .obj c1' in
      let Fc1 ≔ F .obj c1 in
      let Fc1' ≔ F .obj c1' in
      let l2 ≔ ff_lift_through_iso C D H hH c1 c d h (h1 .fst) in
      let f2 ≔ l2 .fst in
      let l3 ≔ ff_lift_through_iso C D H hH c1' c' d' h' (h1' .fst) in
      let f3 ≔ l3 .fst in
      let K2 ≔ ext_functor_compatible C D E H F hH eso ec d c1 c h1 h f2 (l2 .snd) in
      let K3 ≔ ext_functor_compatible C D E H F hH eso ec d' c1' c' h1' h' f3 (l3 .snd) in
      let f31 ≔ C .comp c1 c1' c' f3 f1 in
      let f02 ≔ C .comp c1 c c' f f2 in
      let eqC : Id (C .hom c1 c') f31 f02
        ≔ ff_iso_cancel C D H hH c1 c' d' h' f31 f02
            (calc
              D .comp Hc1 Hc' d' (h' .fst) (H .mor c1 c' f31)
              = D .comp Hc1 Hc' d' (h' .fst) (D .comp Hc1 Hc1' Hc' (H .mor c1' c' f3) (H .mor c1 c1' f1))
                by cat_whisker_left D Hc1 Hc' d' (h' .fst) (H .mor c1 c' f31)
                     (D .comp Hc1 Hc1' Hc' (H .mor c1' c' f3) (H .mor c1 c1' f1)) (H .map_comp c1 c1' c' f1 f3)
              = D .comp Hc1 Hc1' d' (D .comp Hc1' Hc' d' (h' .fst) (H .mor c1' c' f3)) (H .mor c1 c1' f1)
                by D .assoc Hc1 Hc1' Hc' d' (H .mor c1 c1' f1) (H .mor c1' c' f3) (h' .fst)
              = D .comp Hc1 Hc1' d' (h1' .fst) (H .mor c1 c1' f1)
                by cat_whisker_right D Hc1 Hc1' d' (D .comp Hc1' Hc' d' (h' .fst) (H .mor c1' c' f3)) (h1' .fst)
                     (H .mor c1 c1' f1) (l3 .snd)
              = D .comp Hc1 d d' g (h1 .fst) by q1
              = D .comp Hc1 d d' g (D .comp Hc1 Hc d (h .fst) (H .mor c1 c f2))
                by cat_whisker_left D Hc1 d d' g (h1 .fst) (D .comp Hc1 Hc d (h .fst) (H .mor c1 c f2))
                     (inverse (D .hom Hc1 d) (D .comp Hc1 Hc d (h .fst) (H .mor c1 c f2)) (h1 .fst) (l2 .snd))
              = D .comp Hc1 Hc d' (D .comp Hc d d' g (h .fst)) (H .mor c1 c f2)
                by D .assoc Hc1 Hc d d' (H .mor c1 c f2) (h .fst) g
              = D .comp Hc1 Hc d' (D .comp Hc Hc' d' (h' .fst) (H .mor c c' f)) (H .mor c1 c f2)
                by cat_whisker_right D Hc1 Hc d' (D .comp Hc d d' g (h .fst)) (D .comp Hc Hc' d' (h' .fst) (H .mor c c' f))
                     (H .mor c1 c f2)
                     (inverse (D .hom Hc d') (D .comp Hc Hc' d' (h' .fst) (H .mor c c' f)) (D .comp Hc d d' g (h .fst)) (l .snd))
              = D .comp Hc1 Hc' d' (h' .fst) (D .comp Hc1 Hc Hc' (H .mor c c' f) (H .mor c1 c f2))
                by inverse (D .hom Hc1 d') (D .comp Hc1 Hc' d' (h' .fst) (D .comp Hc1 Hc Hc' (H .mor c c' f) (H .mor c1 c f2)))
                     (D .comp Hc1 Hc d' (D .comp Hc Hc' d' (h' .fst) (H .mor c c' f)) (H .mor c1 c f2))
                     (D .assoc Hc1 Hc Hc' d' (H .mor c1 c f2) (H .mor c c' f) (h' .fst))
              = D .comp Hc1 Hc' d' (h' .fst) (H .mor c1 c' f02)
                by cat_whisker_left D Hc1 Hc' d' (h' .fst) (D .comp Hc1 Hc Hc' (H .mor c c' f) (H .mor c1 c f2))
                     (H .mor c1 c' f02)
                     (inverse (D .hom Hc1 Hc') (H .mor c1 c' f02) (D .comp Hc1 Hc Hc' (H .mor c c' f) (H .mor c1 c f2))
                       (H .map_comp c1 c c' f2 f)) ∎) in
      let kc' ≔ kd' c' h' .fst in
      calc
        Ew .comp Fc1 Fc1' Gd' (kd' c1' h1' .fst) (F .mor c1 c1' f1)
        = Ew .comp Fc1 Fc1' Gd' (Ew .comp Fc1' Fc' Gd' kc' (F .mor c1' c' f3)) (F .mor c1 c1' f1)
          by cat_whisker_right Ew Fc1 Fc1' Gd' (kd' c1' h1' .fst) (Ew .comp Fc1' Fc' Gd' kc' (F .mor c1' c' f3))
               (F .mor c1 c1' f1)
               (inverse (Ew .hom Fc1' Gd') (Ew .comp Fc1' Fc' Gd' kc' (F .mor c1' c' f3)) (kd' c1' h1' .fst) K3)
        = Ew .comp Fc1 Fc' Gd' kc' (Ew .comp Fc1 Fc1' Fc' (F .mor c1' c' f3) (F .mor c1 c1' f1))
          by inverse (Ew .hom Fc1 Gd') (Ew .comp Fc1 Fc' Gd' kc' (Ew .comp Fc1 Fc1' Fc' (F .mor c1' c' f3) (F .mor c1 c1' f1)))
               (Ew .comp Fc1 Fc1' Gd' (Ew .comp Fc1' Fc' Gd' kc' (F .mor c1' c' f3)) (F .mor c1 c1' f1))
               (Ew .assoc Fc1 Fc1' Fc' Gd' (F .mor c1 c1' f1) (F .mor c1' c' f3) kc')
        = Ew .comp Fc1 Fc' Gd' kc' (F .mor c1 c' f31)
          by cat_whisker_left Ew Fc1 Fc' Gd' kc' (Ew .comp Fc1 Fc1' Fc' (F .mor c1' c' f3) (F .mor c1 c1' f1))
               (F .mor c1 c' f31)
               (inverse (Ew .hom Fc1 Fc') (F .mor c1 c' f31) (Ew .comp Fc1 Fc1' Fc' (F .mor c1' c' f3) (F .mor c1 c1' f1))
                 (F .map_comp c1 c1' c' f1 f3))
        = Ew .comp Fc1 Fc' Gd' kc' (F .mor c1 c' f02)
          by cat_whisker_left Ew Fc1 Fc' Gd' kc' (F .mor c1 c' f31) (F .mor c1 c' f02) (refl (F .mor c1 c') eqC)
        = Ew .comp Fc1 Fc' Gd' kc' (Ew .comp Fc1 Fc Fc' (F .mor c c' f) (F .mor c1 c f2))
          by cat_whisker_left Ew Fc1 Fc' Gd' kc' (F .mor c1 c' f02) (Ew .comp Fc1 Fc Fc' (F .mor c c' f) (F .mor c1 c f2))
               (F .map_comp c1 c c' f2 f)
        = Ew .comp Fc1 Fc Gd' X (F .mor c1 c f2)
          by Ew .assoc Fc1 Fc Fc' Gd' (F .mor c1 c f2) (F .mor c c' f) kc'
        = Ew .comp Fc1 Fc Gd' (Ew .comp Fc Gd Gd' m (kd c h .fst)) (F .mor c1 c f2)
          by cat_whisker_right Ew Fc1 Fc Gd' X (Ew .comp Fc Gd Gd' m (kd c h .fst)) (F .mor c1 c f2)
               (inverse (Ew .hom Fc Gd') (Ew .comp Fc Gd Gd' m (kd c h .fst)) X mk)
        = Ew .comp Fc1 Gd Gd' m (Ew .comp Fc1 Fc Gd (kd c h .fst) (F .mor c1 c f2))
          by inverse (Ew .hom Fc1 Gd') (Ew .comp Fc1 Gd Gd' m (Ew .comp Fc1 Fc Gd (kd c h .fst) (F .mor c1 c f2)))
               (Ew .comp Fc1 Fc Gd' (Ew .comp Fc Gd Gd' m (kd c h .fst)) (F .mor c1 c f2))
               (Ew .assoc Fc1 Fc Gd Gd' (F .mor c1 c f2) (kd c h .fst) m)
        = Ew .comp Fc1 Gd Gd' m (kd c1 h1 .fst)
          by cat_whisker_left Ew Fc1 Gd Gd' m (Ew .comp Fc1 Fc Gd (kd c h .fst) (F .mor c1 c f2)) (kd c1 h1 .fst) K2 ∎)

def ext_mor_contractible (C D : WildPrecat) (E : Category) (H : WildFunctor C D) (F : WildFunctor C (E .wild))
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b)) (eso : IsEso C D H)
  (ec : (d : D .ob) → isContr (ExtObj C D (E .wild) H F d))
  (d d' : D .ob) (g : D .hom d d') : isContr (ExtMor C D E H F hH eso ec d d' g)
  ≔ let T ≔ ExtMor C D E H F hH eso ec d d' g in
    let pT ≔ ext_mor_prop C D E H F hH eso ec d d' g in
    let c : T
      ≔ mere_rec (Σ (C .ob) (c ↦ CatIso D (H .obj c) d)) T pT
          (t ↦ mere_rec (Σ (C .ob) (c ↦ CatIso D (H .obj c) d')) T pT
            (t' ↦ ext_mor_from_isos C D E H F hH eso ec d d' g (t .fst) (t .snd) (t' .fst) (t' .snd)) (eso d'))
          (eso d) in
    (c, x ↦ pT x c)

def ext_functor_mor (C D : WildPrecat) (E : Category) (H : WildFunctor C D) (F : WildFunctor C (E .wild))
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b)) (eso : IsEso C D H)
  (ec : (d : D .ob) → isContr (ExtObj C D (E .wild) H F d))
  (d d' : D .ob) (g : D .hom d d')
  : E .wild .hom (ext_functor_obj C D E H F hH eso ec d) (ext_functor_obj C D E H F hH eso ec d')
  ≔ ext_mor_contractible C D E H F hH eso ec d d' g .center .fst

def ext_functor_map_id (C D : WildPrecat) (E : Category) (H : WildFunctor C D) (F : WildFunctor C (E .wild))
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b)) (eso : IsEso C D H)
  (ec : (d : D .ob) → isContr (ExtObj C D (E .wild) H F d))
  (d : D .ob)
  : Id (E .wild .hom (ext_functor_obj C D E H F hH eso ec d) (ext_functor_obj C D E H F hH eso ec d))
      (ext_functor_mor C D E H F hH eso ec d d (D .idn d)) (E .wild .idn (ext_functor_obj C D E H F hH eso ec d))
  ≔ let Ew ≔ E .wild in
    let Gd ≔ ext_functor_obj C D E H F hH eso ec d in
    let k ≔ ext_functor_iso C D E H F hH eso ec d in
    ext_mor_prop C D E H F hH eso ec d d (D .idn d)
      (ext_mor_contractible C D E H F hH eso ec d d (D .idn d) .center)
      (Ew .idn Gd, c c' h h' f q ↦
        concat (Ew .hom (F .obj c) Gd) (Ew .comp (F .obj c) (F .obj c') Gd (k c' h' .fst) (F .mor c c' f)) (k c h .fst)
          (Ew .comp (F .obj c) Gd Gd (Ew .idn Gd) (k c h .fst))
          (ext_functor_compatible C D E H F hH eso ec d c c' h h' f
            (concat (D .hom (H .obj c) d) (D .comp (H .obj c) (H .obj c') d (h' .fst) (H .mor c c' f))
              (D .comp (H .obj c) d d (D .idn d) (h .fst)) (h .fst) q (D .lu (H .obj c) d (h .fst))))
          (inverse (Ew .hom (F .obj c) Gd) (Ew .comp (F .obj c) Gd Gd (Ew .idn Gd) (k c h .fst)) (k c h .fst)
            (Ew .lu (F .obj c) Gd (k c h .fst)))) .fst

def ext_functor_map_comp (C D : WildPrecat) (E : Category) (H : WildFunctor C D) (F : WildFunctor C (E .wild))
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b)) (eso : IsEso C D H)
  (ec : (d : D .ob) → isContr (ExtObj C D (E .wild) H F d))
  (x y z : D .ob) (f : D .hom x y) (g : D .hom y z)
  : Id (E .wild .hom (ext_functor_obj C D E H F hH eso ec x) (ext_functor_obj C D E H F hH eso ec z))
      (ext_functor_mor C D E H F hH eso ec x z (D .comp x y z g f))
      (E .wild .comp (ext_functor_obj C D E H F hH eso ec x) (ext_functor_obj C D E H F hH eso ec y)
        (ext_functor_obj C D E H F hH eso ec z)
        (ext_functor_mor C D E H F hH eso ec y z g) (ext_functor_mor C D E H F hH eso ec x y f))
  ≔ let Ew ≔ E .wild in
    let Gx ≔ ext_functor_obj C D E H F hH eso ec x in
    let Gy ≔ ext_functor_obj C D E H F hH eso ec y in
    let Gz ≔ ext_functor_obj C D E H F hH eso ec z in
    let kx ≔ ext_functor_iso C D E H F hH eso ec x in
    let ky ≔ ext_functor_iso C D E H F hH eso ec y in
    let kz ≔ ext_functor_iso C D E H F hH eso ec z in
    let Gf ≔ ext_functor_mor C D E H F hH eso ec x y f in
    let Gg ≔ ext_functor_mor C D E H F hH eso ec y z g in
    let Pf ≔ ext_mor_contractible C D E H F hH eso ec x y f .center .snd in
    let Pg ≔ ext_mor_contractible C D E H F hH eso ec y z g .center .snd in
    let GgGf ≔ Ew .comp Gx Gy Gz Gg Gf in
    ext_mor_prop C D E H F hH eso ec x z (D .comp x y z g f)
      (ext_mor_contractible C D E H F hH eso ec x z (D .comp x y z g f) .center)
      (GgGf, c c'' h h'' f0 q ↦
        let Hc ≔ H .obj c in
        let Hc'' ≔ H .obj c'' in
        let Fc ≔ F .obj c in
        let Fc'' ≔ F .obj c'' in
        let T ≔ Id (Ew .hom Fc Gz) (Ew .comp Fc Fc'' Gz (kz c'' h'' .fst) (F .mor c c'' f0))
          (Ew .comp Fc Gx Gz GgGf (kx c h .fst)) in
        mere_rec (Σ (C .ob) (c' ↦ CatIso D (H .obj c') y)) T
          (E .homset Fc Gz (Ew .comp Fc Fc'' Gz (kz c'' h'' .fst) (F .mor c c'' f0)) (Ew .comp Fc Gx Gz GgGf (kx c h .fst)))
          (t ↦
            let c' ≔ t .fst in
            let h' ≔ t .snd in
            let Hc' ≔ H .obj c' in
            let Fc' ≔ F .obj c' in
            let l1 ≔ ff_lift_through_iso C D H hH c c' y h' (D .comp Hc x y f (h .fst)) in
            let f1 ≔ l1 .fst in
            let l2 ≔ ff_lift_through_iso C D H hH c' c'' z h'' (D .comp Hc' y z g (h' .fst)) in
            let f2 ≔ l2 .fst in
            let f21 ≔ C .comp c c' c'' f2 f1 in
            let eqC : Id (C .hom c c'') f21 f0
              ≔ ff_iso_cancel C D H hH c c'' z h'' f21 f0
                  (calc
                    D .comp Hc Hc'' z (h'' .fst) (H .mor c c'' f21)
                    = D .comp Hc Hc'' z (h'' .fst) (D .comp Hc Hc' Hc'' (H .mor c' c'' f2) (H .mor c c' f1))
                      by cat_whisker_left D Hc Hc'' z (h'' .fst) (H .mor c c'' f21)
                           (D .comp Hc Hc' Hc'' (H .mor c' c'' f2) (H .mor c c' f1)) (H .map_comp c c' c'' f1 f2)
                    = D .comp Hc Hc' z (D .comp Hc' Hc'' z (h'' .fst) (H .mor c' c'' f2)) (H .mor c c' f1)
                      by D .assoc Hc Hc' Hc'' z (H .mor c c' f1) (H .mor c' c'' f2) (h'' .fst)
                    = D .comp Hc Hc' z (D .comp Hc' y z g (h' .fst)) (H .mor c c' f1)
                      by cat_whisker_right D Hc Hc' z (D .comp Hc' Hc'' z (h'' .fst) (H .mor c' c'' f2))
                           (D .comp Hc' y z g (h' .fst)) (H .mor c c' f1) (l2 .snd)
                    = D .comp Hc y z g (D .comp Hc Hc' y (h' .fst) (H .mor c c' f1))
                      by inverse (D .hom Hc z) (D .comp Hc y z g (D .comp Hc Hc' y (h' .fst) (H .mor c c' f1)))
                           (D .comp Hc Hc' z (D .comp Hc' y z g (h' .fst)) (H .mor c c' f1))
                           (D .assoc Hc Hc' y z (H .mor c c' f1) (h' .fst) g)
                    = D .comp Hc y z g (D .comp Hc x y f (h .fst))
                      by cat_whisker_left D Hc y z g (D .comp Hc Hc' y (h' .fst) (H .mor c c' f1)) (D .comp Hc x y f (h .fst))
                           (l1 .snd)
                    = D .comp Hc x z (D .comp x y z g f) (h .fst)
                      by D .assoc Hc x y z (h .fst) f g
                    = D .comp Hc Hc'' z (h'' .fst) (H .mor c c'' f0)
                      by inverse (D .hom Hc z) (D .comp Hc Hc'' z (h'' .fst) (H .mor c c'' f0))
                           (D .comp Hc x z (D .comp x y z g f) (h .fst)) q ∎) in
            calc
              Ew .comp Fc Fc'' Gz (kz c'' h'' .fst) (F .mor c c'' f0)
              = Ew .comp Fc Fc'' Gz (kz c'' h'' .fst) (F .mor c c'' f21)
                by cat_whisker_left Ew Fc Fc'' Gz (kz c'' h'' .fst) (F .mor c c'' f0) (F .mor c c'' f21)
                     (refl (F .mor c c'') (inverse (C .hom c c'') f21 f0 eqC))
              = Ew .comp Fc Fc'' Gz (kz c'' h'' .fst) (Ew .comp Fc Fc' Fc'' (F .mor c' c'' f2) (F .mor c c' f1))
                by cat_whisker_left Ew Fc Fc'' Gz (kz c'' h'' .fst) (F .mor c c'' f21)
                     (Ew .comp Fc Fc' Fc'' (F .mor c' c'' f2) (F .mor c c' f1)) (F .map_comp c c' c'' f1 f2)
              = Ew .comp Fc Fc' Gz (Ew .comp Fc' Fc'' Gz (kz c'' h'' .fst) (F .mor c' c'' f2)) (F .mor c c' f1)
                by Ew .assoc Fc Fc' Fc'' Gz (F .mor c c' f1) (F .mor c' c'' f2) (kz c'' h'' .fst)
              = Ew .comp Fc Fc' Gz (Ew .comp Fc' Gy Gz Gg (ky c' h' .fst)) (F .mor c c' f1)
                by cat_whisker_right Ew Fc Fc' Gz (Ew .comp Fc' Fc'' Gz (kz c'' h'' .fst) (F .mor c' c'' f2))
                     (Ew .comp Fc' Gy Gz Gg (ky c' h' .fst)) (F .mor c c' f1) (Pg c' c'' h' h'' f2 (l2 .snd))
              = Ew .comp Fc Gy Gz Gg (Ew .comp Fc Fc' Gy (ky c' h' .fst) (F .mor c c' f1))
                by inverse (Ew .hom Fc Gz) (Ew .comp Fc Gy Gz Gg (Ew .comp Fc Fc' Gy (ky c' h' .fst) (F .mor c c' f1)))
                     (Ew .comp Fc Fc' Gz (Ew .comp Fc' Gy Gz Gg (ky c' h' .fst)) (F .mor c c' f1))
                     (Ew .assoc Fc Fc' Gy Gz (F .mor c c' f1) (ky c' h' .fst) Gg)
              = Ew .comp Fc Gy Gz Gg (Ew .comp Fc Gx Gy Gf (kx c h .fst))
                by cat_whisker_left Ew Fc Gy Gz Gg (Ew .comp Fc Fc' Gy (ky c' h' .fst) (F .mor c c' f1))
                     (Ew .comp Fc Gx Gy Gf (kx c h .fst)) (Pf c c' h h' f1 (l1 .snd))
              = Ew .comp Fc Gx Gz GgGf (kx c h .fst)
                by Ew .assoc Fc Gx Gy Gz (kx c h .fst) Gf Gg ∎)
          (eso y)) .fst

{` The extension G : D → E. `}
def ext_functor (C D : WildPrecat) (E : Category) (H : WildFunctor C D) (F : WildFunctor C (E .wild))
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b)) (eso : IsEso C D H)
  (ec : (d : D .ob) → isContr (ExtObj C D (E .wild) H F d))
  : WildFunctor D (E .wild)
  ≔ (obj ≔ ext_functor_obj C D E H F hH eso ec,
     mor ≔ ext_functor_mor C D E H F hH eso ec,
     map_id ≔ ext_functor_map_id C D E H F hH eso ec,
     map_comp ≔ ext_functor_map_comp C D E H F hH eso ec)

{` The natural isomorphism F ≅ GH, with components k_{c, id}. `}
def ext_functor_nat_iso (C D : WildPrecat) (E : Category) (H : WildFunctor C D) (F : WildFunctor C (E .wild))
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b)) (eso : IsEso C D H)
  (ec : (d : D .ob) → isContr (ExtObj C D (E .wild) H F d))
  : NatIso C (E .wild) F (functor_compose C D (E .wild) (ext_functor C D E H F hH eso ec) H)
  ≔ let Ew ≔ E .wild in
    let G ≔ ext_functor C D E H F hH eso ec in
    let th : (c : C .ob) → CatIso Ew (F .obj c) (G .obj (H .obj c))
      ≔ c ↦ ext_functor_iso C D E H F hH eso ec (H .obj c) c (cat_identity_iso D (H .obj c)) in
    ((component ≔ c ↦ th c .fst,
      natural ≔ a b f ↦
        let Ha ≔ H .obj a in
        let Hb ≔ H .obj b in
        let Hf ≔ H .mor a b f in
        inverse (Ew .hom (F .obj a) (G .obj Hb))
          (Ew .comp (F .obj a) (F .obj b) (G .obj Hb) (th b .fst) (F .mor a b f))
          (Ew .comp (F .obj a) (G .obj Ha) (G .obj Hb) (G .mor Ha Hb Hf) (th a .fst))
          (ext_mor_contractible C D E H F hH eso ec Ha Hb Hf .center .snd a b
            (cat_identity_iso D Ha) (cat_identity_iso D Hb) f
            (concat (D .hom Ha Hb) (D .comp Ha Hb Hb (D .idn Hb) Hf) Hf (D .comp Ha Ha Hb Hf (D .idn Ha))
              (D .lu Ha Hb Hf) (inverse (D .hom Ha Hb) (D .comp Ha Ha Hb Hf (D .idn Ha)) Hf (D .ru Ha Hb Hf))))),
     c ↦ th c .snd)

{` The extension with its isomorphism GH ≅ F, for an abstract ec. `}
def ext_split_eso_at (C D : WildPrecat) (E : Category) (H : WildFunctor C D) (F : WildFunctor C (E .wild))
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b)) (eso : IsEso C D H)
  (ec : (d : D .ob) → isContr (ExtObj C D (E .wild) H F d))
  : Σ (WildFunctor D (E .wild)) (G ↦ CatIso (FunctorWild C (category_precat E)) (functor_compose C D (E .wild) G H) F)
  ≔ let G ≔ ext_functor C D E H F hH eso ec in
    let GH ≔ functor_compose C D (E .wild) G H in
    (G, cat_iso_inverse (FunctorWild C (category_precat E)) F GH
      (equiv_inverse_map (CatIso (FunctorWild C (category_precat E)) F GH) (NatIso C (E .wild) F GH)
        (functor_cat_iso_equiv C (category_precat E) F GH) (ext_functor_nat_iso C D E H F hH eso ec)))

{` - ∘ H is split essentially surjective. `}
def precomposition_split_eso (C D : WildPrecat) (E : Category) (H : WildFunctor C D) (w : IsWeakEquivalence C D H)
  : IsSplitEso (FunctorWild D (category_precat E)) (FunctorWild C (category_precat E))
      (precomposition_functor C D (category_precat E) H)
  ≔ F ↦ ext_split_eso_at C D E H F (ff_mor_is_equiv C D H (w .fst)) (w .snd)
      (ext_obj_contractible C D E H F (ff_mor_is_equiv C D H (w .fst)) (w .snd))

{` lem:precomp-equiv-cat. If H : C → D is a weak equivalence of
   precategories and E is a category, then - ∘ H : E^D → E^C is an
   equivalence of categories (E^D and E^C are the functor categories of
   xca:functor-cat-univalent, module 621). `}
def precomposition_cat_equivalence (C D : Precat) (E : Category) (H : WildFunctor (C .wild) (D .wild))
  (w : IsWeakEquivalence (C .wild) (D .wild) H)
  : IsCatEquivalence (FunctorCategory (D .wild) E .wild) (FunctorCategory (C .wild) E .wild)
      (precomposition_functor (C .wild) (D .wild) (category_precat E) H)
  ≔ ff_split_eso_is_cat_equivalence (FunctorWild (D .wild) (category_precat E)) (FunctorWild (C .wild) (category_precat E))
      (precomposition_functor (C .wild) (D .wild) (category_precat E) H)
      (precomposition_fully_faithful (C .wild) (D .wild) (category_precat E) H w)
      (precomposition_split_eso (C .wild) (D .wild) E H w)

{` Litmus: precomposition with the identity functor acts on objects as the
   identity on actions on objects, and the identity functor is a weak
   equivalence, so the lemma applies to it. `}
def precomposition_identity_obj (C : WildPrecat) (E : Precat) (K : WildFunctor C (E .wild)) (c : C .ob)
  : Id (E .wild .ob) (precomposition_functor C C E (functor_identity C) .obj K .obj c) (K .obj c)
  ≔ refl (K .obj c)

def precomposition_identity_cat_equivalence (C : Precat) (E : Category)
  : IsCatEquivalence (FunctorCategory (C .wild) E .wild) (FunctorCategory (C .wild) E .wild)
      (precomposition_functor (C .wild) (C .wild) (category_precat E) (functor_identity (C .wild)))
  ≔ precomposition_cat_equivalence C C E (functor_identity (C .wild)) (identity_weak_equivalence (C .wild))
