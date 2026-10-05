export "650-precomposition-fully-faithful"

{` Chapter 6, lem:precomp-equiv-cat, part 2 (HoTT book Theorem 9.9.4):
   extending a functor F : C → E along a weak equivalence H : C → D, for
   E a category. For d : D the type ExtObj of triples (e, k, K) with
   k_{c,h} : F(c) ≅ e for every isomorphism h : H(c) ≅ d, compatible with
   arrows (k_{c',h'} ∘ F(f) = k_{c,h} whenever h' ∘ H(f) = h), is
   contractible: from one h0 : H(c0) ≅ d the center is (F c0, F(φ), ...)
   with H(φ_{c,h}) = h0⁻¹ ∘ h, and univalence of E contracts e. `}

{` Helpers. Lifting an arrow H(c) → d' through h' : H(c') ≅ d'. `}
def ff_lift_through_iso (C D : WildPrecat) (H : WildFunctor C D)
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b))
  (c c' : C .ob) (d' : D .ob) (h' : CatIso D (H .obj c') d') (x : D .hom (H .obj c) d')
  : Σ (C .hom c c') (f ↦ Id (D .hom (H .obj c) d') (D .comp (H .obj c) (H .obj c') d' (h' .fst) (H .mor c c' f)) x)
  ≔ let Hc ≔ H .obj c in
    let Hc' ≔ H .obj c' in
    let i' ≔ cat_iso_inverse D Hc' d' h' .fst in
    let m ≔ D .comp Hc d' Hc' i' x in
    let f ≔ ff_mor_inverse C D H hH c c' m in
    (f, calc
       D .comp Hc Hc' d' (h' .fst) (H .mor c c' f)
       = D .comp Hc Hc' d' (h' .fst) m
         by cat_whisker_left D Hc Hc' d' (h' .fst) (H .mor c c' f) m (ff_mor_inverse_counit C D H hH c c' m)
       = D .comp Hc d' d' (D .comp d' Hc' d' (h' .fst) i') x by D .assoc Hc d' Hc' d' x i' (h' .fst)
       = D .comp Hc d' d' (D .idn d') x
         by cat_whisker_right D Hc d' d' (D .comp d' Hc' d' (h' .fst) i') (D .idn d') x (h' .snd .fst .snd)
       = x by D .lu Hc d' x ∎)

{` Cancelling an isomorphism after H. `}
def ff_iso_cancel (C D : WildPrecat) (H : WildFunctor C D)
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b))
  (a b : C .ob) (d : D .ob) (h : CatIso D (H .obj b) d) (f f' : C .hom a b)
  (p : Id (D .hom (H .obj a) d) (D .comp (H .obj a) (H .obj b) d (h .fst) (H .mor a b f))
        (D .comp (H .obj a) (H .obj b) d (h .fst) (H .mor a b f')))
  : Id (C .hom a b) f f'
  ≔ equivalence_injective (C .hom a b) (D .hom (H .obj a) (H .obj b)) (ff_mor_equiv C D H hH a b) f f'
      (equivalence_injective (D .hom (H .obj a) (H .obj b)) (D .hom (H .obj a) d)
        (cat_postcompose_equiv D (H .obj b) d (h .fst) (h .snd) (H .obj a)) (H .mor a b f) (H .mor a b f') p)

{` (x ∘ y⁻¹) ∘ y = x. `}
def cat_iso_inverse_cancel_right (C : WildPrecat) (a b z : C .ob) (y : CatIso C a b) (x : C .hom a z)
  : Id (C .hom a z) (C .comp a b z (C .comp b a z x (cat_iso_inverse C a b y .fst)) (y .fst)) x
  ≔ let yi ≔ cat_iso_inverse C a b y .fst in
    calc
      C .comp a b z (C .comp b a z x yi) (y .fst)
      = C .comp a a z x (C .comp a b a yi (y .fst))
        by inverse (C .hom a z) (C .comp a a z x (C .comp a b a yi (y .fst))) (C .comp a b z (C .comp b a z x yi) (y .fst))
             (C .assoc a b a z (y .fst) yi x)
      = C .comp a a z x (C .idn a)
        by cat_whisker_left C a a z x (C .comp a b a yi (y .fst)) (C .idn a) (cat_iso_inverse C a b y .snd .fst .snd)
      = x by C .ru a z x ∎

{` The type of extension data at d. `}
def ExtArrowFamily (C D : WildPrecat) (E : WildPrecat) (H : WildFunctor C D) (F : WildFunctor C E) (d : D .ob)
  (e : E .ob) : Type
  ≔ (c : C .ob) → CatIso D (H .obj c) d → CatIso E (F .obj c) e

def ExtCompatible (C D : WildPrecat) (E : WildPrecat) (H : WildFunctor C D) (F : WildFunctor C E) (d : D .ob)
  (u : Σ (E .ob) (ExtArrowFamily C D E H F d)) : Type
  ≔ (c c' : C .ob) (h : CatIso D (H .obj c) d) (h' : CatIso D (H .obj c') d) (f : C .hom c c')
    → Id (D .hom (H .obj c) d) (D .comp (H .obj c) (H .obj c') d (h' .fst) (H .mor c c' f)) (h .fst)
    → Id (E .hom (F .obj c) (u .fst)) (E .comp (F .obj c) (F .obj c') (u .fst) (u .snd c' h' .fst) (F .mor c c' f))
        (u .snd c h .fst)

def ExtObj (C D : WildPrecat) (E : WildPrecat) (H : WildFunctor C D) (F : WildFunctor C E) (d : D .ob) : Type
  ≔ Σ (Σ (E .ob) (ExtArrowFamily C D E H F d)) (ExtCompatible C D E H F d)

def ext_compatible_prop (C D : WildPrecat) (E : Precat) (H : WildFunctor C D) (F : WildFunctor C (E .wild))
  (d : D .ob) (u : Σ (E .wild .ob) (ExtArrowFamily C D (E .wild) H F d))
  : isProp (ExtCompatible C D (E .wild) H F d u)
  ≔ let Ew ≔ E .wild in
    ch6c_pi_prop5 (C .ob) (_ ↦ C .ob) (c _ ↦ CatIso D (H .obj c) d) (_ c' _ ↦ CatIso D (H .obj c') d)
      (c c' _ _ ↦ C .hom c c')
      (c c' h h' f ↦ Id (D .hom (H .obj c) d) (D .comp (H .obj c) (H .obj c') d (h' .fst) (H .mor c c' f)) (h .fst)
        → Id (Ew .hom (F .obj c) (u .fst)) (Ew .comp (F .obj c) (F .obj c') (u .fst) (u .snd c' h' .fst) (F .mor c c' f))
            (u .snd c h .fst))
      (c c' h h' f ↦ pi_prop (Id (D .hom (H .obj c) d) (D .comp (H .obj c) (H .obj c') d (h' .fst) (H .mor c c' f)) (h .fst))
        (_ ↦ Id (Ew .hom (F .obj c) (u .fst)) (Ew .comp (F .obj c) (F .obj c') (u .fst) (u .snd c' h' .fst) (F .mor c c' f))
            (u .snd c h .fst))
        (_ ↦ E .homset (F .obj c) (u .fst) (Ew .comp (F .obj c) (F .obj c') (u .fst) (u .snd c' h' .fst) (F .mor c c' f))
            (u .snd c h .fst)))

{` The center from h0 : H(c0) ≅ d. `}
def ext_obj_phi (C D : WildPrecat) (H : WildFunctor C D)
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b))
  (d : D .ob) (c0 : C .ob) (h0 : CatIso D (H .obj c0) d) (c : C .ob) (h : CatIso D (H .obj c) d)
  : Σ (C .hom c c0) (f ↦ Id (D .hom (H .obj c) d) (D .comp (H .obj c) (H .obj c0) d (h0 .fst) (H .mor c c0 f)) (h .fst))
  ≔ ff_lift_through_iso C D H hH c c0 d h0 (h .fst)

def ext_obj_phi_iso (C D : WildPrecat) (H : WildFunctor C D)
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b))
  (d : D .ob) (c0 : C .ob) (h0 : CatIso D (H .obj c0) d) (c : C .ob) (h : CatIso D (H .obj c) d)
  : CatIsIso C c c0 (ext_obj_phi C D H hH d c0 h0 c h .fst)
  ≔ let Hc ≔ H .obj c in
    let Hc0 ≔ H .obj c0 in
    let phi ≔ ext_obj_phi C D H hH d c0 h0 c h in
    let i0 ≔ cat_iso_inverse D Hc0 d h0 in
    mor_equiv_functor_reflects_iso C D H hH c c0 (phi .fst)
      (cat_is_iso_transport D Hc Hc0 (D .comp Hc d Hc0 (i0 .fst) (h .fst)) (H .mor c c0 (phi .fst))
        (inverse (D .hom Hc Hc0) (H .mor c c0 (phi .fst)) (D .comp Hc d Hc0 (i0 .fst) (h .fst))
          (ff_mor_inverse_counit C D H hH c c0 (D .comp Hc d Hc0 (i0 .fst) (h .fst))))
        (cat_iso_compose D Hc d Hc0 i0 h .snd))

def ext_obj_center_family (C D : WildPrecat) (E : WildPrecat) (H : WildFunctor C D) (F : WildFunctor C E)
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b))
  (d : D .ob) (c0 : C .ob) (h0 : CatIso D (H .obj c0) d) : ExtArrowFamily C D E H F d (F .obj c0)
  ≔ c h ↦ functor_iso C E F c c0 (ext_obj_phi C D H hH d c0 h0 c h .fst, ext_obj_phi_iso C D H hH d c0 h0 c h)

def ext_obj_center_compatible (C D : WildPrecat) (E : WildPrecat) (H : WildFunctor C D) (F : WildFunctor C E)
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b))
  (d : D .ob) (c0 : C .ob) (h0 : CatIso D (H .obj c0) d)
  : ExtCompatible C D E H F d (F .obj c0, ext_obj_center_family C D E H F hH d c0 h0)
  ≔ c c' h h' f q ↦
      let Hc ≔ H .obj c in
      let Hc' ≔ H .obj c' in
      let Hc0 ≔ H .obj c0 in
      let phi ≔ ext_obj_phi C D H hH d c0 h0 c h in
      let phi' ≔ ext_obj_phi C D H hH d c0 h0 c' h' in
      let pf ≔ C .comp c c' c0 (phi' .fst) f in
      let eq : Id (C .hom c c0) pf (phi .fst)
        ≔ ff_iso_cancel C D H hH c c0 d h0 pf (phi .fst)
            (calc
              D .comp Hc Hc0 d (h0 .fst) (H .mor c c0 pf)
              = D .comp Hc Hc0 d (h0 .fst) (D .comp Hc Hc' Hc0 (H .mor c' c0 (phi' .fst)) (H .mor c c' f))
                by cat_whisker_left D Hc Hc0 d (h0 .fst) (H .mor c c0 pf)
                     (D .comp Hc Hc' Hc0 (H .mor c' c0 (phi' .fst)) (H .mor c c' f)) (H .map_comp c c' c0 f (phi' .fst))
              = D .comp Hc Hc' d (D .comp Hc' Hc0 d (h0 .fst) (H .mor c' c0 (phi' .fst))) (H .mor c c' f)
                by D .assoc Hc Hc' Hc0 d (H .mor c c' f) (H .mor c' c0 (phi' .fst)) (h0 .fst)
              = D .comp Hc Hc' d (h' .fst) (H .mor c c' f)
                by cat_whisker_right D Hc Hc' d (D .comp Hc' Hc0 d (h0 .fst) (H .mor c' c0 (phi' .fst))) (h' .fst)
                     (H .mor c c' f) (phi' .snd)
              = h .fst by q
              = D .comp Hc Hc0 d (h0 .fst) (H .mor c c0 (phi .fst))
                by inverse (D .hom Hc d) (D .comp Hc Hc0 d (h0 .fst) (H .mor c c0 (phi .fst))) (h .fst) (phi .snd) ∎) in
      concat (E .hom (F .obj c) (F .obj c0))
        (E .comp (F .obj c) (F .obj c') (F .obj c0) (F .mor c' c0 (phi' .fst)) (F .mor c c' f))
        (F .mor c c0 pf) (F .mor c c0 (phi .fst))
        (inverse (E .hom (F .obj c) (F .obj c0)) (F .mor c c0 pf)
          (E .comp (F .obj c) (F .obj c') (F .obj c0) (F .mor c' c0 (phi' .fst)) (F .mor c c' f))
          (F .map_comp c c' c0 f (phi' .fst)))
        (refl (F .mor c c0) eq)

{` Transport in the family of extension data along e1 = e2 postcomposes
   with idtoiso. `}
def ext_arrow_transport_base (C D : WildPrecat) (E : WildPrecat) (H : WildFunctor C D) (F : WildFunctor C E)
  (d : D .ob) (e1 : E .ob) (k : ExtArrowFamily C D E H F d e1) (c : C .ob) (h : CatIso D (H .obj c) d)
  : Id (E .hom (F .obj c) e1)
      (transport (E .ob) (ExtArrowFamily C D E H F d) e1 e1 (refl e1) k c h .fst)
      (E .comp (F .obj c) e1 e1 (cat_idtoiso E e1 e1 (refl e1) .fst) (k c h .fst))
  ≔ concat (E .hom (F .obj c) e1)
      (transport (E .ob) (ExtArrowFamily C D E H F d) e1 e1 (refl e1) k c h .fst) (k c h .fst)
      (E .comp (F .obj c) e1 e1 (cat_idtoiso E e1 e1 (refl e1) .fst) (k c h .fst))
      (transport_refl (E .ob) (ExtArrowFamily C D E H F d) e1 k (refl c) (refl h) .fst)
      (inverse (E .hom (F .obj c) e1) (E .comp (F .obj c) e1 e1 (cat_idtoiso E e1 e1 (refl e1) .fst) (k c h .fst))
        (k c h .fst)
        (concat (E .hom (F .obj c) e1) (E .comp (F .obj c) e1 e1 (cat_idtoiso E e1 e1 (refl e1) .fst) (k c h .fst))
          (E .comp (F .obj c) e1 e1 (E .idn e1) (k c h .fst)) (k c h .fst)
          (cat_whisker_right E (F .obj c) e1 e1 (cat_idtoiso E e1 e1 (refl e1) .fst) (E .idn e1) (k c h .fst)
            (inverse (CatIso E e1 e1) (cat_identity_iso E e1) (cat_idtoiso E e1 e1 (refl e1)) (cat_idtoiso_refl E e1) .fst))
          (E .lu (F .obj c) e1 (k c h .fst))))

def ext_arrow_transport (C D : WildPrecat) (E : WildPrecat) (H : WildFunctor C D) (F : WildFunctor C E)
  (d : D .ob) (e1 e2 : E .ob) (p : Id (E .ob) e1 e2) (k : ExtArrowFamily C D E H F d e1)
  (c : C .ob) (h : CatIso D (H .obj c) d)
  : Id (E .hom (F .obj c) e2)
      (transport (E .ob) (ExtArrowFamily C D E H F d) e1 e2 p k c h .fst)
      (E .comp (F .obj c) e1 e2 (cat_idtoiso E e1 e2 p .fst) (k c h .fst))
  ≔ J (E .ob) e1 (e2 p ↦ Id (E .hom (F .obj c) e2)
        (transport (E .ob) (ExtArrowFamily C D E H F d) e1 e2 p k c h .fst)
        (E .comp (F .obj c) e1 e2 (cat_idtoiso E e1 e2 p .fst) (k c h .fst)))
      (ext_arrow_transport_base C D E H F d e1 k c h) e2 p

{` Every extension datum equals the one built from h0. `}
def ext_obj_path_from (C D : WildPrecat) (E : Category) (H : WildFunctor C D) (F : WildFunctor C (E .wild))
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b))
  (d : D .ob) (c0 : C .ob) (h0 : CatIso D (H .obj c0) d) (x : ExtObj C D (E .wild) H F d)
  : Id (ExtObj C D (E .wild) H F d)
      ((F .obj c0, ext_obj_center_family C D (E .wild) H F hH d c0 h0),
       ext_obj_center_compatible C D (E .wild) H F hH d c0 h0) x
  ≔ let Ew ≔ E .wild in
    let A ≔ ExtArrowFamily C D Ew H F d in
    let k0 ≔ ext_obj_center_family C D Ew H F hH d c0 h0 in
    let e ≔ x .fst .fst in
    let k ≔ x .fst .snd in
    let kk ≔ x .snd in
    let p ≔ cat_isotoid Ew (E .univalent) (F .obj c0) e (k c0 h0) in
    let t ≔ transport (Ew .ob) A (F .obj c0) e p k0 in
    let arrows : (c : C .ob) (h : CatIso D (H .obj c) d) → Id (Ew .hom (F .obj c) e) (t c h .fst) (k c h .fst)
      ≔ c h ↦
          let phi ≔ ext_obj_phi C D H hH d c0 h0 c h in
          calc
            t c h .fst
            = Ew .comp (F .obj c) (F .obj c0) e (cat_idtoiso Ew (F .obj c0) e p .fst) (k0 c h .fst)
              by ext_arrow_transport C D Ew H F d (F .obj c0) e p k0 c h
            = Ew .comp (F .obj c) (F .obj c0) e (k c0 h0 .fst) (k0 c h .fst)
              by cat_whisker_right Ew (F .obj c) (F .obj c0) e (cat_idtoiso Ew (F .obj c0) e p .fst) (k c0 h0 .fst)
                   (k0 c h .fst) (cat_idtoiso_isotoid Ew (E .univalent) (F .obj c0) e (k c0 h0) .fst)
            = k c h .fst by kk c c0 h h0 (phi .fst) (phi .snd) ∎ in
    let base_path : Id (Σ (Ew .ob) A) (F .obj c0, k0) (e, k)
      ≔ (p, pathover_of_eq (Ew .ob) A (F .obj c0) e p k0 k
          (funext2 (C .ob) (c ↦ CatIso D (H .obj c) d) (c _ ↦ CatIso Ew (F .obj c) e) t k
            (c h ↦ cat_iso_path Ew (F .obj c) e (t c h) (k c h) (arrows c h)))) in
    equiv_inverse_map (Id (ExtObj C D Ew H F d) ((F .obj c0, k0), ext_obj_center_compatible C D Ew H F hH d c0 h0) x)
      (Id (Σ (Ew .ob) A) (F .obj c0, k0) (e, k))
      (subtype_path_equiv (Σ (Ew .ob) A) (ExtCompatible C D Ew H F d) (ext_compatible_prop C D (category_precat E) H F d)
        ((F .obj c0, k0), ext_obj_center_compatible C D Ew H F hH d c0 h0) x)
      base_path

def ext_obj_contractible (C D : WildPrecat) (E : Category) (H : WildFunctor C D) (F : WildFunctor C (E .wild))
  (hH : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (H .obj a) (H .obj b)) (H .mor a b)) (eso : IsEso C D H)
  (d : D .ob) : isContr (ExtObj C D (E .wild) H F d)
  ≔ mere_rec (Σ (C .ob) (c ↦ CatIso D (H .obj c) d)) (isContr (ExtObj C D (E .wild) H F d))
      (iscontr_isprop (ExtObj C D (E .wild) H F d))
      (t ↦ (((F .obj (t .fst), ext_obj_center_family C D (E .wild) H F hH d (t .fst) (t .snd)),
             ext_obj_center_compatible C D (E .wild) H F hH d (t .fst) (t .snd)),
            x ↦ inverse (ExtObj C D (E .wild) H F d)
              ((F .obj (t .fst), ext_obj_center_family C D (E .wild) H F hH d (t .fst) (t .snd)),
               ext_obj_center_compatible C D (E .wild) H F hH d (t .fst) (t .snd)) x
              (ext_obj_path_from C D E H F hH d (t .fst) (t .snd) x)))
      (eso d)
