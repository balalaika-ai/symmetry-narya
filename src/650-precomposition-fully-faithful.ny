export "643-ff-eso-equivalences"
export "620-natural-isomorphisms"

{` Chapter 6, lem:precomp-equiv-cat, part 1 (HoTT book Lemmas 9.9.1 and
   9.9.2): for a weak equivalence H : C → D and a precategory E, the
   precomposition functor - ∘ H : E^D → E^C is fully faithful. Given
   γ : KH → K'H, its unique extension α : K → K' has α_d determined by
   α_d ∘ K(h) = K'(h) ∘ γ_c for every isomorphism h : H(c) ≅ d; the type
   of such α_d is contractible since H is essentially surjective and fully
   faithful. Only E needs hom-sets here. `}

{` Whiskering a natural transformation with H, and the precomposition
   functor. `}
def nat_trans_whisker_right (C D E : WildPrecat) (H : WildFunctor C D) (K K' : WildFunctor D E)
  (a : WildNatTrans D E K K') : WildNatTrans C E (functor_compose C D E K H) (functor_compose C D E K' H)
  ≔ (component ≔ c ↦ a .component (H .obj c),
     natural ≔ x y f ↦ a .natural (H .obj x) (H .obj y) (H .mor x y f))

def precomposition_functor (C D : WildPrecat) (E : Precat) (H : WildFunctor C D)
  : WildFunctor (FunctorWild D E) (FunctorWild C E)
  ≔ (obj ≔ K ↦ functor_compose C D (E .wild) K H,
     mor ≔ K K' a ↦ nat_trans_whisker_right C D (E .wild) H K K' a,
     map_id ≔ K ↦ nat_trans_path_pointwise C (E .wild) (E .homset)
       (functor_compose C D (E .wild) K H) (functor_compose C D (E .wild) K H)
       (nat_trans_whisker_right C D (E .wild) H K K (nat_trans_identity D (E .wild) K))
       (nat_trans_identity C (E .wild) (functor_compose C D (E .wild) K H))
       (c ↦ refl (E .wild .idn (K .obj (H .obj c)))),
     map_comp ≔ K K' K'' a b ↦ nat_trans_path_pointwise C (E .wild) (E .homset)
       (functor_compose C D (E .wild) K H) (functor_compose C D (E .wild) K'' H)
       (nat_trans_whisker_right C D (E .wild) H K K'' (nat_trans_compose D (E .wild) K K' K'' b a))
       (nat_trans_compose C (E .wild) (functor_compose C D (E .wild) K H) (functor_compose C D (E .wild) K' H)
         (functor_compose C D (E .wild) K'' H)
         (nat_trans_whisker_right C D (E .wild) H K' K'' b) (nat_trans_whisker_right C D (E .wild) H K K' a))
       (c ↦ refl (E .wild .comp (K .obj (H .obj c)) (K' .obj (H .obj c)) (K'' .obj (H .obj c))
         (b .component (H .obj c)) (a .component (H .obj c)))))

{` The extension condition for γ : KH → K'H at d: g ∘ K(h) = K'(h) ∘ γ_c
   for all h : H(c) ≅ d (in the orientation of naturality squares). `}
def WhiskerExtCond (C D : WildPrecat) (E : Precat) (H : WildFunctor C D) (K K' : WildFunctor D (E .wild))
  (g0 : WildNatTrans C (E .wild) (functor_compose C D (E .wild) K H) (functor_compose C D (E .wild) K' H))
  (d : D .ob) (g : E .wild .hom (K .obj d) (K' .obj d)) : Type
  ≔ (c : C .ob) (h : CatIso D (H .obj c) d)
    → Id (E .wild .hom (K .obj (H .obj c)) (K' .obj d))
        (E .wild .comp (K .obj (H .obj c)) (K' .obj (H .obj c)) (K' .obj d) (K' .mor (H .obj c) d (h .fst)) (g0 .component c))
        (E .wild .comp (K .obj (H .obj c)) (K .obj d) (K' .obj d) g (K .mor (H .obj c) d (h .fst)))

def WhiskerExt (C D : WildPrecat) (E : Precat) (H : WildFunctor C D) (K K' : WildFunctor D (E .wild))
  (g0 : WildNatTrans C (E .wild) (functor_compose C D (E .wild) K H) (functor_compose C D (E .wild) K' H))
  (d : D .ob) : Type
  ≔ Σ (E .wild .hom (K .obj d) (K' .obj d)) (WhiskerExtCond C D E H K K' g0 d)

def whisker_ext_cond_prop (C D : WildPrecat) (E : Precat) (H : WildFunctor C D) (K K' : WildFunctor D (E .wild))
  (g0 : WildNatTrans C (E .wild) (functor_compose C D (E .wild) K H) (functor_compose C D (E .wild) K' H))
  (d : D .ob) (g : E .wild .hom (K .obj d) (K' .obj d)) : isProp (WhiskerExtCond C D E H K K' g0 d g)
  ≔ let Ew ≔ E .wild in
    ch6c_pi_prop2 (C .ob) (c ↦ CatIso D (H .obj c) d)
      (c h ↦ Id (Ew .hom (K .obj (H .obj c)) (K' .obj d))
        (Ew .comp (K .obj (H .obj c)) (K' .obj (H .obj c)) (K' .obj d) (K' .mor (H .obj c) d (h .fst)) (g0 .component c))
        (Ew .comp (K .obj (H .obj c)) (K .obj d) (K' .obj d) g (K .mor (H .obj c) d (h .fst))))
      (c h ↦ E .homset (K .obj (H .obj c)) (K' .obj d)
        (Ew .comp (K .obj (H .obj c)) (K' .obj (H .obj c)) (K' .obj d) (K' .mor (H .obj c) d (h .fst)) (g0 .component c))
        (Ew .comp (K .obj (H .obj c)) (K .obj d) (K' .obj d) g (K .mor (H .obj c) d (h .fst))))

{` Two arrows satisfying the extension condition at one isomorphism
   h : H(c) ≅ d agree (K(h) is an isomorphism). `}
def whisker_ext_unique_at (C D : WildPrecat) (E : Precat) (H : WildFunctor C D) (K K' : WildFunctor D (E .wild))
  (g0 : WildNatTrans C (E .wild) (functor_compose C D (E .wild) K H) (functor_compose C D (E .wild) K' H))
  (d : D .ob) (u v : WhiskerExt C D E H K K' g0 d) (c : C .ob) (h : CatIso D (H .obj c) d)
  : Id (E .wild .hom (K .obj d) (K' .obj d)) (u .fst) (v .fst)
  ≔ let Ew ≔ E .wild in
    let KHc ≔ K .obj (H .obj c) in
    let Kh ≔ K .mor (H .obj c) d (h .fst) in
    equivalence_injective (Ew .hom (K .obj d) (K' .obj d)) (Ew .hom KHc (K' .obj d))
      (cat_precompose_equiv Ew KHc (K .obj d) Kh (functor_preserves_iso D Ew K (H .obj c) d (h .fst) (h .snd)) (K' .obj d))
      (u .fst) (v .fst)
      (concat (Ew .hom KHc (K' .obj d)) (Ew .comp KHc (K .obj d) (K' .obj d) (u .fst) Kh)
        (Ew .comp KHc (K' .obj (H .obj c)) (K' .obj d) (K' .mor (H .obj c) d (h .fst)) (g0 .component c))
        (Ew .comp KHc (K .obj d) (K' .obj d) (v .fst) Kh)
        (inverse (Ew .hom KHc (K' .obj d))
          (Ew .comp KHc (K' .obj (H .obj c)) (K' .obj d) (K' .mor (H .obj c) d (h .fst)) (g0 .component c))
          (Ew .comp KHc (K .obj d) (K' .obj d) (u .fst) Kh) (u .snd c h))
        (v .snd c h))

def whisker_ext_prop (C D : WildPrecat) (E : Precat) (H : WildFunctor C D) (eso : IsEso C D H)
  (K K' : WildFunctor D (E .wild))
  (g0 : WildNatTrans C (E .wild) (functor_compose C D (E .wild) K H) (functor_compose C D (E .wild) K' H))
  (d : D .ob) : isProp (WhiskerExt C D E H K K' g0 d)
  ≔ u v ↦
      let p ≔ mere_rec (Σ (C .ob) (c ↦ CatIso D (H .obj c) d)) (Id (E .wild .hom (K .obj d) (K' .obj d)) (u .fst) (v .fst))
        (E .homset (K .obj d) (K' .obj d) (u .fst) (v .fst))
        (t ↦ whisker_ext_unique_at C D E H K K' g0 d u v (t .fst) (t .snd)) (eso d) in
      (p, pathover_of_eq (E .wild .hom (K .obj d) (K' .obj d)) (WhiskerExtCond C D E H K K' g0 d) (u .fst) (v .fst) p
         (u .snd) (v .snd)
         (whisker_ext_cond_prop C D E H K K' g0 d (v .fst)
           (transport (E .wild .hom (K .obj d) (K' .obj d)) (WhiskerExtCond C D E H K K' g0 d) (u .fst) (v .fst) p (u .snd))
           (v .snd)))

{` Existence of the extension from one isomorphism h0 : H(c0) ≅ d:
   g = (K'(h0) ∘ γ_{c0}) ∘ K(h0⁻¹). `}
def whisker_ext_from_iso (C D : WildPrecat) (E : Precat) (H : WildFunctor C D)
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b))
  (K K' : WildFunctor D (E .wild))
  (g0 : WildNatTrans C (E .wild) (functor_compose C D (E .wild) K H) (functor_compose C D (E .wild) K' H))
  (d : D .ob) (c0 : C .ob) (h0 : CatIso D (H .obj c0) d) : WhiskerExt C D E H K K' g0 d
  ≔ let Ew ≔ E .wild in
    let Hc0 ≔ H .obj c0 in
    let Kd ≔ K .obj d in
    let K'd ≔ K' .obj d in
    let KHc0 ≔ K .obj Hc0 in
    let K'Hc0 ≔ K' .obj Hc0 in
    let i0 ≔ cat_iso_inverse D Hc0 d h0 .fst in
    let K'h0 ≔ K' .mor Hc0 d (h0 .fst) in
    let gam0 ≔ g0 .component c0 in
    let A ≔ Ew .comp KHc0 K'Hc0 K'd K'h0 gam0 in
    let g ≔ Ew .comp Kd KHc0 K'd A (K .mor d Hc0 i0) in
    (g, c h ↦
      let Hc ≔ H .obj c in
      let KHc ≔ K .obj Hc in
      let K'Hc ≔ K' .obj Hc in
      let m ≔ D .comp Hc d Hc0 i0 (h .fst) in
      let phi ≔ ff_mor_inverse C D H hH c c0 m in
      let Hphi ≔ H .mor c c0 phi in
      let Hphi_m ≔ ff_mor_inverse_counit C D H hH c c0 m in
      let P : Id (D .hom Hc d) (D .comp Hc Hc0 d (h0 .fst) Hphi) (h .fst)
        ≔ calc
            D .comp Hc Hc0 d (h0 .fst) Hphi
            = D .comp Hc Hc0 d (h0 .fst) m by cat_whisker_left D Hc Hc0 d (h0 .fst) Hphi m Hphi_m
            = D .comp Hc d d (D .comp d Hc0 d (h0 .fst) i0) (h .fst) by D .assoc Hc d Hc0 d (h .fst) i0 (h0 .fst)
            = D .comp Hc d d (D .idn d) (h .fst)
              by cat_whisker_right D Hc d d (D .comp d Hc0 d (h0 .fst) i0) (D .idn d) (h .fst) (h0 .snd .fst .snd)
            = h .fst by D .lu Hc d (h .fst) ∎ in
      inverse (Ew .hom KHc K'd) (Ew .comp KHc Kd K'd g (K .mor Hc d (h .fst)))
        (Ew .comp KHc K'Hc K'd (K' .mor Hc d (h .fst)) (g0 .component c))
        (calc
          Ew .comp KHc Kd K'd g (K .mor Hc d (h .fst))
          = Ew .comp KHc KHc0 K'd A (Ew .comp KHc Kd KHc0 (K .mor d Hc0 i0) (K .mor Hc d (h .fst)))
            by inverse (Ew .hom KHc K'd) (Ew .comp KHc KHc0 K'd A (Ew .comp KHc Kd KHc0 (K .mor d Hc0 i0) (K .mor Hc d (h .fst))))
                 (Ew .comp KHc Kd K'd g (K .mor Hc d (h .fst))) (Ew .assoc KHc Kd KHc0 K'd (K .mor Hc d (h .fst)) (K .mor d Hc0 i0) A)
          = Ew .comp KHc KHc0 K'd A (K .mor Hc Hc0 m)
            by cat_whisker_left Ew KHc KHc0 K'd A (Ew .comp KHc Kd KHc0 (K .mor d Hc0 i0) (K .mor Hc d (h .fst))) (K .mor Hc Hc0 m)
                 (inverse (Ew .hom KHc KHc0) (K .mor Hc Hc0 m) (Ew .comp KHc Kd KHc0 (K .mor d Hc0 i0) (K .mor Hc d (h .fst)))
                   (K .map_comp Hc d Hc0 (h .fst) i0))
          = Ew .comp KHc KHc0 K'd A (K .mor Hc Hc0 Hphi)
            by cat_whisker_left Ew KHc KHc0 K'd A (K .mor Hc Hc0 m) (K .mor Hc Hc0 Hphi)
                 (refl (K .mor Hc Hc0) (inverse (D .hom Hc Hc0) Hphi m Hphi_m))
          = Ew .comp KHc K'Hc0 K'd K'h0 (Ew .comp KHc KHc0 K'Hc0 gam0 (K .mor Hc Hc0 Hphi))
            by inverse (Ew .hom KHc K'd) (Ew .comp KHc K'Hc0 K'd K'h0 (Ew .comp KHc KHc0 K'Hc0 gam0 (K .mor Hc Hc0 Hphi)))
                 (Ew .comp KHc KHc0 K'd A (K .mor Hc Hc0 Hphi)) (Ew .assoc KHc KHc0 K'Hc0 K'd (K .mor Hc Hc0 Hphi) gam0 K'h0)
          = Ew .comp KHc K'Hc0 K'd K'h0 (Ew .comp KHc K'Hc K'Hc0 (K' .mor Hc Hc0 Hphi) (g0 .component c))
            by cat_whisker_left Ew KHc K'Hc0 K'd K'h0 (Ew .comp KHc KHc0 K'Hc0 gam0 (K .mor Hc Hc0 Hphi))
                 (Ew .comp KHc K'Hc K'Hc0 (K' .mor Hc Hc0 Hphi) (g0 .component c))
                 (inverse (Ew .hom KHc K'Hc0) (Ew .comp KHc K'Hc K'Hc0 (K' .mor Hc Hc0 Hphi) (g0 .component c))
                   (Ew .comp KHc KHc0 K'Hc0 gam0 (K .mor Hc Hc0 Hphi)) (g0 .natural c c0 phi))
          = Ew .comp KHc K'Hc K'd (Ew .comp K'Hc K'Hc0 K'd K'h0 (K' .mor Hc Hc0 Hphi)) (g0 .component c)
            by Ew .assoc KHc K'Hc K'Hc0 K'd (g0 .component c) (K' .mor Hc Hc0 Hphi) K'h0
          = Ew .comp KHc K'Hc K'd (K' .mor Hc d (D .comp Hc Hc0 d (h0 .fst) Hphi)) (g0 .component c)
            by cat_whisker_right Ew KHc K'Hc K'd (Ew .comp K'Hc K'Hc0 K'd K'h0 (K' .mor Hc Hc0 Hphi))
                 (K' .mor Hc d (D .comp Hc Hc0 d (h0 .fst) Hphi)) (g0 .component c)
                 (inverse (Ew .hom K'Hc K'd) (K' .mor Hc d (D .comp Hc Hc0 d (h0 .fst) Hphi))
                   (Ew .comp K'Hc K'Hc0 K'd K'h0 (K' .mor Hc Hc0 Hphi)) (K' .map_comp Hc Hc0 d Hphi (h0 .fst)))
          = Ew .comp KHc K'Hc K'd (K' .mor Hc d (h .fst)) (g0 .component c)
            by cat_whisker_right Ew KHc K'Hc K'd (K' .mor Hc d (D .comp Hc Hc0 d (h0 .fst) Hphi))
                 (K' .mor Hc d (h .fst)) (g0 .component c) (refl (K' .mor Hc d) P) ∎))

def whisker_ext_contractible (C D : WildPrecat) (E : Precat) (H : WildFunctor C D)
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b)) (eso : IsEso C D H)
  (K K' : WildFunctor D (E .wild))
  (g0 : WildNatTrans C (E .wild) (functor_compose C D (E .wild) K H) (functor_compose C D (E .wild) K' H))
  (d : D .ob) : isContr (WhiskerExt C D E H K K' g0 d)
  ≔ let c ≔ mere_rec (Σ (C .ob) (c ↦ CatIso D (H .obj c) d)) (WhiskerExt C D E H K K' g0 d)
        (whisker_ext_prop C D E H eso K K' g0 d)
        (t ↦ whisker_ext_from_iso C D E H hH K K' g0 d (t .fst) (t .snd)) (eso d) in
    (c, x ↦ whisker_ext_prop C D E H eso K K' g0 d x c)

{` The extension α of γ, with its naturality. `}
def whisker_ext_component (C D : WildPrecat) (E : Precat) (H : WildFunctor C D)
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b)) (eso : IsEso C D H)
  (K K' : WildFunctor D (E .wild))
  (g0 : WildNatTrans C (E .wild) (functor_compose C D (E .wild) K H) (functor_compose C D (E .wild) K' H))
  (d : D .ob) : E .wild .hom (K .obj d) (K' .obj d)
  ≔ whisker_ext_contractible C D E H hH eso K K' g0 d .center .fst

def whisker_ext_natural_at (C D : WildPrecat) (E : Precat) (H : WildFunctor C D)
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b)) (eso : IsEso C D H)
  (K K' : WildFunctor D (E .wild))
  (g0 : WildNatTrans C (E .wild) (functor_compose C D (E .wild) K H) (functor_compose C D (E .wild) K' H))
  (d d' : D .ob) (u : D .hom d d') (c : C .ob) (h : CatIso D (H .obj c) d) (c' : C .ob) (h' : CatIso D (H .obj c') d')
  : Id (E .wild .hom (K .obj d) (K' .obj d'))
      (E .wild .comp (K .obj d) (K' .obj d) (K' .obj d') (K' .mor d d' u) (whisker_ext_component C D E H hH eso K K' g0 d))
      (E .wild .comp (K .obj d) (K .obj d') (K' .obj d') (whisker_ext_component C D E H hH eso K K' g0 d') (K .mor d d' u))
  ≔ let Ew ≔ E .wild in
    let Hc ≔ H .obj c in
    let Hc' ≔ H .obj c' in
    let Kd ≔ K .obj d in let Kd' ≔ K .obj d' in
    let K'd ≔ K' .obj d in let K'd' ≔ K' .obj d' in
    let KHc ≔ K .obj Hc in let KHc' ≔ K .obj Hc' in
    let K'Hc ≔ K' .obj Hc in let K'Hc' ≔ K' .obj Hc' in
    let ad ≔ whisker_ext_component C D E H hH eso K K' g0 d in
    let ad' ≔ whisker_ext_component C D E H hH eso K K' g0 d' in
    let Pd ≔ whisker_ext_contractible C D E H hH eso K K' g0 d .center .snd in
    let Pd' ≔ whisker_ext_contractible C D E H hH eso K K' g0 d' .center .snd in
    let i' ≔ cat_iso_inverse D Hc' d' h' .fst in
    let uh ≔ D .comp Hc d d' u (h .fst) in
    let m ≔ D .comp Hc d' Hc' i' uh in
    let f ≔ ff_mor_inverse C D H hH c c' m in
    let Hf ≔ H .mor c c' f in
    let P : Id (D .hom Hc d') (D .comp Hc Hc' d' (h' .fst) Hf) uh
      ≔ calc
          D .comp Hc Hc' d' (h' .fst) Hf
          = D .comp Hc Hc' d' (h' .fst) m by cat_whisker_left D Hc Hc' d' (h' .fst) Hf m (ff_mor_inverse_counit C D H hH c c' m)
          = D .comp Hc d' d' (D .comp d' Hc' d' (h' .fst) i') uh by D .assoc Hc d' Hc' d' uh i' (h' .fst)
          = D .comp Hc d' d' (D .idn d') uh
            by cat_whisker_right D Hc d' d' (D .comp d' Hc' d' (h' .fst) i') (D .idn d') uh (h' .snd .fst .snd)
          = uh by D .lu Hc d' uh ∎ in
    let Kh ≔ K .mor Hc d (h .fst) in
    equivalence_injective (Ew .hom Kd K'd') (Ew .hom KHc K'd')
      (cat_precompose_equiv Ew KHc Kd Kh (functor_preserves_iso D Ew K Hc d (h .fst) (h .snd)) K'd')
      (Ew .comp Kd K'd K'd' (K' .mor d d' u) ad) (Ew .comp Kd Kd' K'd' ad' (K .mor d d' u))
      (calc
        Ew .comp KHc Kd K'd' (Ew .comp Kd K'd K'd' (K' .mor d d' u) ad) Kh
        = Ew .comp KHc K'd K'd' (K' .mor d d' u) (Ew .comp KHc Kd K'd ad Kh)
          by inverse (Ew .hom KHc K'd') (Ew .comp KHc K'd K'd' (K' .mor d d' u) (Ew .comp KHc Kd K'd ad Kh))
               (Ew .comp KHc Kd K'd' (Ew .comp Kd K'd K'd' (K' .mor d d' u) ad) Kh) (Ew .assoc KHc Kd K'd K'd' Kh ad (K' .mor d d' u))
        = Ew .comp KHc K'd K'd' (K' .mor d d' u) (Ew .comp KHc K'Hc K'd (K' .mor Hc d (h .fst)) (g0 .component c))
          by cat_whisker_left Ew KHc K'd K'd' (K' .mor d d' u) (Ew .comp KHc Kd K'd ad Kh)
               (Ew .comp KHc K'Hc K'd (K' .mor Hc d (h .fst)) (g0 .component c))
               (inverse (Ew .hom KHc K'd) (Ew .comp KHc K'Hc K'd (K' .mor Hc d (h .fst)) (g0 .component c))
                 (Ew .comp KHc Kd K'd ad Kh) (Pd c h))
        = Ew .comp KHc K'Hc K'd' (Ew .comp K'Hc K'd K'd' (K' .mor d d' u) (K' .mor Hc d (h .fst))) (g0 .component c)
          by Ew .assoc KHc K'Hc K'd K'd' (g0 .component c) (K' .mor Hc d (h .fst)) (K' .mor d d' u)
        = Ew .comp KHc K'Hc K'd' (K' .mor Hc d' uh) (g0 .component c)
          by cat_whisker_right Ew KHc K'Hc K'd' (Ew .comp K'Hc K'd K'd' (K' .mor d d' u) (K' .mor Hc d (h .fst)))
               (K' .mor Hc d' uh) (g0 .component c)
               (inverse (Ew .hom K'Hc K'd') (K' .mor Hc d' uh) (Ew .comp K'Hc K'd K'd' (K' .mor d d' u) (K' .mor Hc d (h .fst)))
                 (K' .map_comp Hc d d' (h .fst) u))
        = Ew .comp KHc K'Hc K'd' (K' .mor Hc d' (D .comp Hc Hc' d' (h' .fst) Hf)) (g0 .component c)
          by cat_whisker_right Ew KHc K'Hc K'd' (K' .mor Hc d' uh) (K' .mor Hc d' (D .comp Hc Hc' d' (h' .fst) Hf))
               (g0 .component c) (refl (K' .mor Hc d') (inverse (D .hom Hc d') (D .comp Hc Hc' d' (h' .fst) Hf) uh P))
        = Ew .comp KHc K'Hc K'd' (Ew .comp K'Hc K'Hc' K'd' (K' .mor Hc' d' (h' .fst)) (K' .mor Hc Hc' Hf)) (g0 .component c)
          by cat_whisker_right Ew KHc K'Hc K'd' (K' .mor Hc d' (D .comp Hc Hc' d' (h' .fst) Hf))
               (Ew .comp K'Hc K'Hc' K'd' (K' .mor Hc' d' (h' .fst)) (K' .mor Hc Hc' Hf)) (g0 .component c)
               (K' .map_comp Hc Hc' d' Hf (h' .fst))
        = Ew .comp KHc K'Hc' K'd' (K' .mor Hc' d' (h' .fst)) (Ew .comp KHc K'Hc K'Hc' (K' .mor Hc Hc' Hf) (g0 .component c))
          by inverse (Ew .hom KHc K'd') (Ew .comp KHc K'Hc' K'd' (K' .mor Hc' d' (h' .fst))
                 (Ew .comp KHc K'Hc K'Hc' (K' .mor Hc Hc' Hf) (g0 .component c)))
               (Ew .comp KHc K'Hc K'd' (Ew .comp K'Hc K'Hc' K'd' (K' .mor Hc' d' (h' .fst)) (K' .mor Hc Hc' Hf)) (g0 .component c))
               (Ew .assoc KHc K'Hc K'Hc' K'd' (g0 .component c) (K' .mor Hc Hc' Hf) (K' .mor Hc' d' (h' .fst)))
        = Ew .comp KHc K'Hc' K'd' (K' .mor Hc' d' (h' .fst)) (Ew .comp KHc KHc' K'Hc' (g0 .component c') (K .mor Hc Hc' Hf))
          by cat_whisker_left Ew KHc K'Hc' K'd' (K' .mor Hc' d' (h' .fst))
               (Ew .comp KHc K'Hc K'Hc' (K' .mor Hc Hc' Hf) (g0 .component c))
               (Ew .comp KHc KHc' K'Hc' (g0 .component c') (K .mor Hc Hc' Hf)) (g0 .natural c c' f)
        = Ew .comp KHc KHc' K'd' (Ew .comp KHc' K'Hc' K'd' (K' .mor Hc' d' (h' .fst)) (g0 .component c')) (K .mor Hc Hc' Hf)
          by Ew .assoc KHc KHc' K'Hc' K'd' (K .mor Hc Hc' Hf) (g0 .component c') (K' .mor Hc' d' (h' .fst))
        = Ew .comp KHc KHc' K'd' (Ew .comp KHc' Kd' K'd' ad' (K .mor Hc' d' (h' .fst))) (K .mor Hc Hc' Hf)
          by cat_whisker_right Ew KHc KHc' K'd' (Ew .comp KHc' K'Hc' K'd' (K' .mor Hc' d' (h' .fst)) (g0 .component c'))
               (Ew .comp KHc' Kd' K'd' ad' (K .mor Hc' d' (h' .fst))) (K .mor Hc Hc' Hf) (Pd' c' h')
        = Ew .comp KHc Kd' K'd' ad' (Ew .comp KHc KHc' Kd' (K .mor Hc' d' (h' .fst)) (K .mor Hc Hc' Hf))
          by inverse (Ew .hom KHc K'd') (Ew .comp KHc Kd' K'd' ad' (Ew .comp KHc KHc' Kd' (K .mor Hc' d' (h' .fst)) (K .mor Hc Hc' Hf)))
               (Ew .comp KHc KHc' K'd' (Ew .comp KHc' Kd' K'd' ad' (K .mor Hc' d' (h' .fst))) (K .mor Hc Hc' Hf))
               (Ew .assoc KHc KHc' Kd' K'd' (K .mor Hc Hc' Hf) (K .mor Hc' d' (h' .fst)) ad')
        = Ew .comp KHc Kd' K'd' ad' (K .mor Hc d' (D .comp Hc Hc' d' (h' .fst) Hf))
          by cat_whisker_left Ew KHc Kd' K'd' ad' (Ew .comp KHc KHc' Kd' (K .mor Hc' d' (h' .fst)) (K .mor Hc Hc' Hf))
               (K .mor Hc d' (D .comp Hc Hc' d' (h' .fst) Hf))
               (inverse (Ew .hom KHc Kd') (K .mor Hc d' (D .comp Hc Hc' d' (h' .fst) Hf))
                 (Ew .comp KHc KHc' Kd' (K .mor Hc' d' (h' .fst)) (K .mor Hc Hc' Hf)) (K .map_comp Hc Hc' d' Hf (h' .fst)))
        = Ew .comp KHc Kd' K'd' ad' (K .mor Hc d' uh)
          by cat_whisker_left Ew KHc Kd' K'd' ad' (K .mor Hc d' (D .comp Hc Hc' d' (h' .fst) Hf)) (K .mor Hc d' uh)
               (refl (K .mor Hc d') P)
        = Ew .comp KHc Kd' K'd' ad' (Ew .comp KHc Kd Kd' (K .mor d d' u) Kh)
          by cat_whisker_left Ew KHc Kd' K'd' ad' (K .mor Hc d' uh) (Ew .comp KHc Kd Kd' (K .mor d d' u) Kh)
               (K .map_comp Hc d d' (h .fst) u)
        = Ew .comp KHc Kd K'd' (Ew .comp Kd Kd' K'd' ad' (K .mor d d' u)) Kh
          by Ew .assoc KHc Kd Kd' K'd' Kh (K .mor d d' u) ad' ∎)

def whisker_ext (C D : WildPrecat) (E : Precat) (H : WildFunctor C D)
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b)) (eso : IsEso C D H)
  (K K' : WildFunctor D (E .wild))
  (g0 : WildNatTrans C (E .wild) (functor_compose C D (E .wild) K H) (functor_compose C D (E .wild) K' H))
  : WildNatTrans D (E .wild) K K'
  ≔ (component ≔ whisker_ext_component C D E H hH eso K K' g0,
     natural ≔ d d' u ↦
       mere_rec (Σ (C .ob) (c ↦ CatIso D (H .obj c) d))
         (Id (E .wild .hom (K .obj d) (K' .obj d'))
           (E .wild .comp (K .obj d) (K' .obj d) (K' .obj d') (K' .mor d d' u) (whisker_ext_component C D E H hH eso K K' g0 d))
           (E .wild .comp (K .obj d) (K .obj d') (K' .obj d') (whisker_ext_component C D E H hH eso K K' g0 d') (K .mor d d' u)))
         (E .homset (K .obj d) (K' .obj d')
           (E .wild .comp (K .obj d) (K' .obj d) (K' .obj d') (K' .mor d d' u) (whisker_ext_component C D E H hH eso K K' g0 d))
           (E .wild .comp (K .obj d) (K .obj d') (K' .obj d') (whisker_ext_component C D E H hH eso K K' g0 d') (K .mor d d' u)))
         (t ↦ mere_rec (Σ (C .ob) (c ↦ CatIso D (H .obj c) d'))
           (Id (E .wild .hom (K .obj d) (K' .obj d'))
             (E .wild .comp (K .obj d) (K' .obj d) (K' .obj d') (K' .mor d d' u) (whisker_ext_component C D E H hH eso K K' g0 d))
             (E .wild .comp (K .obj d) (K .obj d') (K' .obj d') (whisker_ext_component C D E H hH eso K K' g0 d') (K .mor d d' u)))
           (E .homset (K .obj d) (K' .obj d')
             (E .wild .comp (K .obj d) (K' .obj d) (K' .obj d') (K' .mor d d' u) (whisker_ext_component C D E H hH eso K K' g0 d))
             (E .wild .comp (K .obj d) (K .obj d') (K' .obj d') (whisker_ext_component C D E H hH eso K K' g0 d') (K .mor d d' u)))
           (t' ↦ whisker_ext_natural_at C D E H hH eso K K' g0 d d' u (t .fst) (t .snd) (t' .fst) (t' .snd))
           (eso d'))
         (eso d))

{` The two round trips. `}
def whisker_ext_whisker (C D : WildPrecat) (E : Precat) (H : WildFunctor C D)
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b)) (eso : IsEso C D H)
  (K K' : WildFunctor D (E .wild))
  (g0 : WildNatTrans C (E .wild) (functor_compose C D (E .wild) K H) (functor_compose C D (E .wild) K' H))
  : Id (WildNatTrans C (E .wild) (functor_compose C D (E .wild) K H) (functor_compose C D (E .wild) K' H))
      (nat_trans_whisker_right C D (E .wild) H K K' (whisker_ext C D E H hH eso K K' g0)) g0
  ≔ let Ew ≔ E .wild in
    nat_trans_path_pointwise C Ew (E .homset) (functor_compose C D Ew K H) (functor_compose C D Ew K' H)
      (nat_trans_whisker_right C D Ew H K K' (whisker_ext C D E H hH eso K K' g0)) g0
      (c ↦
        let Hc ≔ H .obj c in
        let KHc ≔ K .obj Hc in
        let K'Hc ≔ K' .obj Hc in
        let a ≔ whisker_ext_component C D E H hH eso K K' g0 Hc in
        let P ≔ whisker_ext_contractible C D E H hH eso K K' g0 Hc .center .snd c (cat_identity_iso D Hc) in
        calc
          a
          = Ew .comp KHc KHc K'Hc a (Ew .idn KHc)
            by inverse (Ew .hom KHc K'Hc) (Ew .comp KHc KHc K'Hc a (Ew .idn KHc)) a (Ew .ru KHc K'Hc a)
          = Ew .comp KHc KHc K'Hc a (K .mor Hc Hc (D .idn Hc))
            by cat_whisker_left Ew KHc KHc K'Hc a (Ew .idn KHc) (K .mor Hc Hc (D .idn Hc))
                 (inverse (Ew .hom KHc KHc) (K .mor Hc Hc (D .idn Hc)) (Ew .idn KHc) (K .map_id Hc))
          = Ew .comp KHc K'Hc K'Hc (K' .mor Hc Hc (D .idn Hc)) (g0 .component c)
            by inverse (Ew .hom KHc K'Hc) (Ew .comp KHc K'Hc K'Hc (K' .mor Hc Hc (D .idn Hc)) (g0 .component c))
                 (Ew .comp KHc KHc K'Hc a (K .mor Hc Hc (D .idn Hc))) P
          = Ew .comp KHc K'Hc K'Hc (Ew .idn K'Hc) (g0 .component c)
            by cat_whisker_right Ew KHc K'Hc K'Hc (K' .mor Hc Hc (D .idn Hc)) (Ew .idn K'Hc) (g0 .component c) (K' .map_id Hc)
          = g0 .component c by Ew .lu KHc K'Hc (g0 .component c) ∎)

def whisker_whisker_ext (C D : WildPrecat) (E : Precat) (H : WildFunctor C D)
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b)) (eso : IsEso C D H)
  (K K' : WildFunctor D (E .wild)) (a : WildNatTrans D (E .wild) K K')
  : Id (WildNatTrans D (E .wild) K K') (whisker_ext C D E H hH eso K K' (nat_trans_whisker_right C D (E .wild) H K K' a)) a
  ≔ nat_trans_path_pointwise D (E .wild) (E .homset) K K'
      (whisker_ext C D E H hH eso K K' (nat_trans_whisker_right C D (E .wild) H K K' a)) a
      (d ↦ whisker_ext_prop C D E H eso K K' (nat_trans_whisker_right C D (E .wild) H K K' a) d
        (whisker_ext_contractible C D E H hH eso K K' (nat_trans_whisker_right C D (E .wild) H K K' a) d .center)
        (a .component d, c h ↦ a .natural (H .obj c) d (h .fst)) .fst)

{` lem:precomp-equiv-cat, full faithfulness: whiskering with a weak
   equivalence is an equivalence on natural transformations. `}
def precomposition_mor_is_equiv (C D : WildPrecat) (E : Precat) (H : WildFunctor C D) (w : IsWeakEquivalence C D H)
  (K K' : WildFunctor D (E .wild))
  : isEquiv (WildNatTrans D (E .wild) K K')
      (WildNatTrans C (E .wild) (functor_compose C D (E .wild) K H) (functor_compose C D (E .wild) K' H))
      (nat_trans_whisker_right C D (E .wild) H K K')
  ≔ let hH ≔ ff_mor_is_equiv C D H (w .fst) in
    quasi_inverse_equiv (WildNatTrans D (E .wild) K K')
      (WildNatTrans C (E .wild) (functor_compose C D (E .wild) K H) (functor_compose C D (E .wild) K' H))
      (nat_trans_whisker_right C D (E .wild) H K K') (whisker_ext C D E H hH (w .snd) K K')
      (whisker_whisker_ext C D E H hH (w .snd) K K') (whisker_ext_whisker C D E H hH (w .snd) K K') .equiv

def precomposition_fully_faithful (C D : WildPrecat) (E : Precat) (H : WildFunctor C D) (w : IsWeakEquivalence C D H)
  : IsFullyFaithful (FunctorWild D E) (FunctorWild C E) (precomposition_functor C D E H)
  ≔ ff_from_mor_equivs (FunctorWild D E) (FunctorWild C E) (precomposition_functor C D E H)
      (precomposition_mor_is_equiv C D E H w)
