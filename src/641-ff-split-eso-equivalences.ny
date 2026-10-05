export "640-cat-equivalence-fully-faithful"

{` Chapter 6, section 6.7, part 2: a fully faithful, split essentially
   surjective functor is an equivalence (the inverse map of
   lem:equiv-precat-is-ff-split-eso), and the forward map of that lemma.
   Everything here holds for wild precategories.

   Given F fully faithful and, for each d, a chosen object G(d) with an
   isomorphism h_d : F(G d) ≅ d, we set G(g) = F⁻¹(h_y⁻¹ ∘ (g ∘ h_x)) and
   η_c = F⁻¹(h_{Fc}⁻¹); then h and η are natural isomorphisms FG ≅ id and
   id ≅ GF, and AKS Lemma 6.2 (module 640) gives the equivalence. `}

{` The inverse of the action of a fully faithful functor on arrows. `}
def ff_mor_equiv (C D : WildPrecat) (F : WildFunctor C D)
  (hF : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b)) (a b : C .ob)
  : Equiv (C .hom a b) (D .hom (F .obj a) (F .obj b))
  ≔ (F .mor a b, hF a b)

def ff_mor_inverse (C D : WildPrecat) (F : WildFunctor C D)
  (hF : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b)) (a b : C .ob)
  (m : D .hom (F .obj a) (F .obj b)) : C .hom a b
  ≔ equiv_inverse_map (C .hom a b) (D .hom (F .obj a) (F .obj b)) (ff_mor_equiv C D F hF a b) m

def ff_mor_inverse_counit (C D : WildPrecat) (F : WildFunctor C D)
  (hF : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b)) (a b : C .ob)
  (m : D .hom (F .obj a) (F .obj b)) : Id (D .hom (F .obj a) (F .obj b)) (F .mor a b (ff_mor_inverse C D F hF a b m)) m
  ≔ equiv_counit (C .hom a b) (D .hom (F .obj a) (F .obj b)) (ff_mor_equiv C D F hF a b) m

def ff_mor_inverse_path (C D : WildPrecat) (F : WildFunctor C D)
  (hF : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b)) (a b : C .ob)
  (k : C .hom a b) (m : D .hom (F .obj a) (F .obj b)) (p : Id (D .hom (F .obj a) (F .obj b)) (F .mor a b k) m)
  : Id (C .hom a b) (ff_mor_inverse C D F hF a b m) k
  ≔ ch6c_equiv_inverse_path (C .hom a b) (D .hom (F .obj a) (F .obj b)) (ff_mor_equiv C D F hF a b) k m p

def ff_mor_inverse_idn (C D : WildPrecat) (F : WildFunctor C D)
  (hF : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b)) (a : C .ob)
  : Id (C .hom a a) (ff_mor_inverse C D F hF a a (D .idn (F .obj a))) (C .idn a)
  ≔ ff_mor_inverse_path C D F hF a a (C .idn a) (D .idn (F .obj a)) (F .map_id a)

def ff_mor_inverse_comp (C D : WildPrecat) (F : WildFunctor C D)
  (hF : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b)) (a b c : C .ob)
  (m1 : D .hom (F .obj a) (F .obj b)) (m2 : D .hom (F .obj b) (F .obj c))
  : Id (C .hom a c) (ff_mor_inverse C D F hF a c (D .comp (F .obj a) (F .obj b) (F .obj c) m2 m1))
      (C .comp a b c (ff_mor_inverse C D F hF b c m2) (ff_mor_inverse C D F hF a b m1))
  ≔ let Fa ≔ F .obj a in
    let Fb ≔ F .obj b in
    let Fc ≔ F .obj c in
    let k1 ≔ ff_mor_inverse C D F hF a b m1 in
    let k2 ≔ ff_mor_inverse C D F hF b c m2 in
    ff_mor_inverse_path C D F hF a c (C .comp a b c k2 k1) (D .comp Fa Fb Fc m2 m1)
      (calc
        F .mor a c (C .comp a b c k2 k1)
        = D .comp Fa Fb Fc (F .mor b c k2) (F .mor a b k1) by F .map_comp a b c k1 k2
        = D .comp Fa Fb Fc m2 (F .mor a b k1)
          by cat_whisker_right D Fa Fb Fc (F .mor b c k2) m2 (F .mor a b k1)
               (ff_mor_inverse_counit C D F hF b c m2)
        = D .comp Fa Fb Fc m2 m1
          by cat_whisker_left D Fa Fb Fc m2 (F .mor a b k1) m1 (ff_mor_inverse_counit C D F hF a b m1) ∎)

{` Conjugation by the chosen isomorphisms h_x : F(G x) ≅ x. `}
def split_eso_iso (C D : WildPrecat) (F : WildFunctor C D) (s : IsSplitEso C D F) (x : D .ob)
  : D .hom (F .obj (s x .fst)) x
  ≔ s x .snd .fst

def split_eso_iso_inverse (C D : WildPrecat) (F : WildFunctor C D) (s : IsSplitEso C D F) (x : D .ob)
  : D .hom x (F .obj (s x .fst))
  ≔ cat_iso_inverse D (F .obj (s x .fst)) x (s x .snd) .fst

def split_eso_iso_section (C D : WildPrecat) (F : WildFunctor C D) (s : IsSplitEso C D F) (x : D .ob)
  : Id (D .hom x x) (D .comp x (F .obj (s x .fst)) x (split_eso_iso C D F s x) (split_eso_iso_inverse C D F s x))
      (D .idn x)
  ≔ s x .snd .snd .fst .snd

def split_eso_iso_retraction (C D : WildPrecat) (F : WildFunctor C D) (s : IsSplitEso C D F) (x : D .ob)
  : Id (D .hom (F .obj (s x .fst)) (F .obj (s x .fst)))
      (D .comp (F .obj (s x .fst)) x (F .obj (s x .fst)) (split_eso_iso_inverse C D F s x) (split_eso_iso C D F s x))
      (D .idn (F .obj (s x .fst)))
  ≔ cat_iso_inverse D (F .obj (s x .fst)) x (s x .snd) .snd .fst .snd

def split_eso_conj (C D : WildPrecat) (F : WildFunctor C D) (s : IsSplitEso C D F) (x y : D .ob)
  (g : D .hom x y) : D .hom (F .obj (s x .fst)) (F .obj (s y .fst))
  ≔ D .comp (F .obj (s x .fst)) y (F .obj (s y .fst)) (split_eso_iso_inverse C D F s y)
      (D .comp (F .obj (s x .fst)) x y g (split_eso_iso C D F s x))

def split_eso_conj_idn (C D : WildPrecat) (F : WildFunctor C D) (s : IsSplitEso C D F) (x : D .ob)
  : Id (D .hom (F .obj (s x .fst)) (F .obj (s x .fst))) (split_eso_conj C D F s x x (D .idn x))
      (D .idn (F .obj (s x .fst)))
  ≔ let FGx ≔ F .obj (s x .fst) in
    let hx ≔ split_eso_iso C D F s x in
    let ix ≔ split_eso_iso_inverse C D F s x in
    concat (D .hom FGx FGx) (D .comp FGx x FGx ix (D .comp FGx x x (D .idn x) hx)) (D .comp FGx x FGx ix hx)
      (D .idn FGx)
      (cat_whisker_left D FGx x FGx ix (D .comp FGx x x (D .idn x) hx) hx (D .lu FGx x hx))
      (split_eso_iso_retraction C D F s x)

{` (h_y ∘ g ∘ h_x⁻¹-style bookkeeping): (h_z⁻¹ ∘ (g ∘ h_y)) ∘ h_y⁻¹ = h_z⁻¹ ∘ g. `}
def split_eso_conj_cancel (C D : WildPrecat) (F : WildFunctor C D) (s : IsSplitEso C D F) (y z : D .ob)
  (g : D .hom y z)
  : Id (D .hom y (F .obj (s z .fst)))
      (D .comp y (F .obj (s y .fst)) (F .obj (s z .fst)) (split_eso_conj C D F s y z g) (split_eso_iso_inverse C D F s y))
      (D .comp y z (F .obj (s z .fst)) (split_eso_iso_inverse C D F s z) g)
  ≔ let FGy ≔ F .obj (s y .fst) in
    let FGz ≔ F .obj (s z .fst) in
    let hy ≔ split_eso_iso C D F s y in
    let iy ≔ split_eso_iso_inverse C D F s y in
    let iz ≔ split_eso_iso_inverse C D F s z in
    let ghy ≔ D .comp FGy y z g hy in
    calc
      D .comp y FGy FGz (D .comp FGy z FGz iz ghy) iy
      = D .comp y z FGz iz (D .comp y FGy z ghy iy)
        by inverse (D .hom y FGz) (D .comp y z FGz iz (D .comp y FGy z ghy iy))
             (D .comp y FGy FGz (D .comp FGy z FGz iz ghy) iy) (D .assoc y FGy z FGz iy ghy iz)
      = D .comp y z FGz iz (D .comp y y z g (D .comp y FGy y hy iy))
        by cat_whisker_left D y z FGz iz (D .comp y FGy z ghy iy) (D .comp y y z g (D .comp y FGy y hy iy))
             (inverse (D .hom y z) (D .comp y y z g (D .comp y FGy y hy iy)) (D .comp y FGy z ghy iy)
               (D .assoc y FGy y z iy hy g))
      = D .comp y z FGz iz (D .comp y y z g (D .idn y))
        by cat_whisker_left D y z FGz iz (D .comp y y z g (D .comp y FGy y hy iy)) (D .comp y y z g (D .idn y))
             (cat_whisker_left D y y z g (D .comp y FGy y hy iy) (D .idn y) (split_eso_iso_section C D F s y))
      = D .comp y z FGz iz g
        by cat_whisker_left D y z FGz iz (D .comp y y z g (D .idn y)) g (D .ru y z g) ∎

def split_eso_conj_comp (C D : WildPrecat) (F : WildFunctor C D) (s : IsSplitEso C D F) (x y z : D .ob)
  (f : D .hom x y) (g : D .hom y z)
  : Id (D .hom (F .obj (s x .fst)) (F .obj (s z .fst)))
      (D .comp (F .obj (s x .fst)) (F .obj (s y .fst)) (F .obj (s z .fst))
        (split_eso_conj C D F s y z g) (split_eso_conj C D F s x y f))
      (split_eso_conj C D F s x z (D .comp x y z g f))
  ≔ let FGx ≔ F .obj (s x .fst) in
    let FGy ≔ F .obj (s y .fst) in
    let FGz ≔ F .obj (s z .fst) in
    let hx ≔ split_eso_iso C D F s x in
    let iy ≔ split_eso_iso_inverse C D F s y in
    let iz ≔ split_eso_iso_inverse C D F s z in
    let A ≔ split_eso_conj C D F s y z g in
    let fhx ≔ D .comp FGx x y f hx in
    calc
      D .comp FGx FGy FGz A (D .comp FGx y FGy iy fhx)
      = D .comp FGx y FGz (D .comp y FGy FGz A iy) fhx
        by D .assoc FGx y FGy FGz fhx iy A
      = D .comp FGx y FGz (D .comp y z FGz iz g) fhx
        by cat_whisker_right D FGx y FGz (D .comp y FGy FGz A iy) (D .comp y z FGz iz g) fhx
             (split_eso_conj_cancel C D F s y z g)
      = D .comp FGx z FGz iz (D .comp FGx y z g fhx)
        by inverse (D .hom FGx FGz) (D .comp FGx z FGz iz (D .comp FGx y z g fhx))
             (D .comp FGx y FGz (D .comp y z FGz iz g) fhx) (D .assoc FGx y z FGz fhx g iz)
      = D .comp FGx z FGz iz (D .comp FGx x z (D .comp x y z g f) hx)
        by cat_whisker_left D FGx z FGz iz (D .comp FGx y z g fhx) (D .comp FGx x z (D .comp x y z g f) hx)
             (D .assoc FGx x y z hx f g) ∎

{` The functor G. `}
def split_eso_inverse_functor (C D : WildPrecat) (F : WildFunctor C D)
  (hF : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b)) (s : IsSplitEso C D F)
  : WildFunctor D C
  ≔ (obj ≔ x ↦ s x .fst,
     mor ≔ x y g ↦ ff_mor_inverse C D F hF (s x .fst) (s y .fst) (split_eso_conj C D F s x y g),
     map_id ≔ x ↦
       concat (C .hom (s x .fst) (s x .fst))
         (ff_mor_inverse C D F hF (s x .fst) (s x .fst) (split_eso_conj C D F s x x (D .idn x)))
         (ff_mor_inverse C D F hF (s x .fst) (s x .fst) (D .idn (F .obj (s x .fst))))
         (C .idn (s x .fst))
         (refl (ff_mor_inverse C D F hF (s x .fst) (s x .fst)) (split_eso_conj_idn C D F s x))
         (ff_mor_inverse_idn C D F hF (s x .fst)),
     map_comp ≔ x y z f g ↦
       concat (C .hom (s x .fst) (s z .fst))
         (ff_mor_inverse C D F hF (s x .fst) (s z .fst) (split_eso_conj C D F s x z (D .comp x y z g f)))
         (ff_mor_inverse C D F hF (s x .fst) (s z .fst)
           (D .comp (F .obj (s x .fst)) (F .obj (s y .fst)) (F .obj (s z .fst))
             (split_eso_conj C D F s y z g) (split_eso_conj C D F s x y f)))
         (C .comp (s x .fst) (s y .fst) (s z .fst)
           (ff_mor_inverse C D F hF (s y .fst) (s z .fst) (split_eso_conj C D F s y z g))
           (ff_mor_inverse C D F hF (s x .fst) (s y .fst) (split_eso_conj C D F s x y f)))
         (refl (ff_mor_inverse C D F hF (s x .fst) (s z .fst))
           (inverse (D .hom (F .obj (s x .fst)) (F .obj (s z .fst)))
             (D .comp (F .obj (s x .fst)) (F .obj (s y .fst)) (F .obj (s z .fst))
               (split_eso_conj C D F s y z g) (split_eso_conj C D F s x y f))
             (split_eso_conj C D F s x z (D .comp x y z g f))
             (split_eso_conj_comp C D F s x y z f g)))
         (ff_mor_inverse_comp C D F hF (s x .fst) (s y .fst) (s z .fst)
           (split_eso_conj C D F s x y f) (split_eso_conj C D F s y z g)))

{` The counit: h is a natural isomorphism FG ≅ id. `}
def split_eso_counit_natural (C D : WildPrecat) (F : WildFunctor C D)
  (hF : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b)) (s : IsSplitEso C D F)
  (x y : D .ob) (g : D .hom x y)
  : Id (D .hom (F .obj (s x .fst)) y)
      (D .comp (F .obj (s x .fst)) x y g (split_eso_iso C D F s x))
      (D .comp (F .obj (s x .fst)) (F .obj (s y .fst)) y (split_eso_iso C D F s y)
        (F .mor (s x .fst) (s y .fst) (split_eso_inverse_functor C D F hF s .mor x y g)))
  ≔ let FGx ≔ F .obj (s x .fst) in
    let FGy ≔ F .obj (s y .fst) in
    let hx ≔ split_eso_iso C D F s x in
    let hy ≔ split_eso_iso C D F s y in
    let iy ≔ split_eso_iso_inverse C D F s y in
    let ghx ≔ D .comp FGx x y g hx in
    calc
      ghx
      = D .comp FGx y y (D .idn y) ghx
        by inverse (D .hom FGx y) (D .comp FGx y y (D .idn y) ghx) ghx (D .lu FGx y ghx)
      = D .comp FGx y y (D .comp y FGy y hy iy) ghx
        by cat_whisker_right D FGx y y (D .idn y) (D .comp y FGy y hy iy) ghx
             (inverse (D .hom y y) (D .comp y FGy y hy iy) (D .idn y) (split_eso_iso_section C D F s y))
      = D .comp FGx FGy y hy (D .comp FGx y FGy iy ghx)
        by inverse (D .hom FGx y) (D .comp FGx FGy y hy (D .comp FGx y FGy iy ghx))
             (D .comp FGx y y (D .comp y FGy y hy iy) ghx) (D .assoc FGx y FGy y ghx iy hy)
      = D .comp FGx FGy y hy (F .mor (s x .fst) (s y .fst) (split_eso_inverse_functor C D F hF s .mor x y g))
        by cat_whisker_left D FGx FGy y hy (D .comp FGx y FGy iy ghx)
             (F .mor (s x .fst) (s y .fst) (split_eso_inverse_functor C D F hF s .mor x y g))
             (inverse (D .hom FGx FGy)
               (F .mor (s x .fst) (s y .fst) (split_eso_inverse_functor C D F hF s .mor x y g))
               (D .comp FGx y FGy iy ghx)
               (ff_mor_inverse_counit C D F hF (s x .fst) (s y .fst) (split_eso_conj C D F s x y g))) ∎

def split_eso_counit (C D : WildPrecat) (F : WildFunctor C D)
  (hF : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b)) (s : IsSplitEso C D F)
  : NatIso D D (functor_compose D C D F (split_eso_inverse_functor C D F hF s)) (functor_identity D)
  ≔ ((component ≔ x ↦ split_eso_iso C D F s x,
      natural ≔ x y g ↦ split_eso_counit_natural C D F hF s x y g),
     x ↦ s x .snd .snd)

{` The unit η_c = F⁻¹(h_{Fc}⁻¹). `}
def split_eso_unit_component (C D : WildPrecat) (F : WildFunctor C D)
  (hF : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b)) (s : IsSplitEso C D F)
  (a : C .ob) : C .hom a (s (F .obj a) .fst)
  ≔ ff_mor_inverse C D F hF a (s (F .obj a) .fst) (split_eso_iso_inverse C D F s (F .obj a))

def split_eso_unit_natural (C D : WildPrecat) (F : WildFunctor C D)
  (hF : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b)) (s : IsSplitEso C D F)
  (a b : C .ob) (f : C .hom a b)
  : Id (C .hom a (s (F .obj b) .fst))
      (C .comp a (s (F .obj a) .fst) (s (F .obj b) .fst)
        (split_eso_inverse_functor C D F hF s .mor (F .obj a) (F .obj b) (F .mor a b f))
        (split_eso_unit_component C D F hF s a))
      (C .comp a b (s (F .obj b) .fst) (split_eso_unit_component C D F hF s b) f)
  ≔ let Fa ≔ F .obj a in
    let Fb ≔ F .obj b in
    let GFa ≔ s Fa .fst in
    let GFb ≔ s Fb .fst in
    let FGFa ≔ F .obj GFa in
    let FGFb ≔ F .obj GFb in
    let Ff ≔ F .mor a b f in
    let ea ≔ split_eso_unit_component C D F hF s a in
    let eb ≔ split_eso_unit_component C D F hF s b in
    let Gm ≔ split_eso_inverse_functor C D F hF s .mor Fa Fb Ff in
    let ia ≔ split_eso_iso_inverse C D F s Fa in
    let ib ≔ split_eso_iso_inverse C D F s Fb in
    let ha ≔ split_eso_iso C D F s Fa in
    let fha ≔ D .comp FGFa Fa Fb Ff ha in
    equivalence_injective (C .hom a GFb) (D .hom Fa FGFb) (ff_mor_equiv C D F hF a GFb)
      (C .comp a GFa GFb Gm ea) (C .comp a b GFb eb f)
      (calc
        F .mor a GFb (C .comp a GFa GFb Gm ea)
        = D .comp Fa FGFa FGFb (F .mor GFa GFb Gm) (F .mor a GFa ea) by F .map_comp a GFa GFb ea Gm
        = D .comp Fa FGFa FGFb (split_eso_conj C D F s Fa Fb Ff) (F .mor a GFa ea)
          by cat_whisker_right D Fa FGFa FGFb (F .mor GFa GFb Gm) (split_eso_conj C D F s Fa Fb Ff) (F .mor a GFa ea)
               (ff_mor_inverse_counit C D F hF GFa GFb (split_eso_conj C D F s Fa Fb Ff))
        = D .comp Fa FGFa FGFb (split_eso_conj C D F s Fa Fb Ff) ia
          by cat_whisker_left D Fa FGFa FGFb (split_eso_conj C D F s Fa Fb Ff) (F .mor a GFa ea) ia
               (ff_mor_inverse_counit C D F hF a GFa ia)
        = D .comp Fa Fb FGFb ib (D .comp Fa FGFa Fb fha ia)
          by inverse (D .hom Fa FGFb) (D .comp Fa Fb FGFb ib (D .comp Fa FGFa Fb fha ia))
               (D .comp Fa FGFa FGFb (split_eso_conj C D F s Fa Fb Ff) ia) (D .assoc Fa FGFa Fb FGFb ia fha ib)
        = D .comp Fa Fb FGFb ib (D .comp Fa Fa Fb Ff (D .comp Fa FGFa Fa ha ia))
          by cat_whisker_left D Fa Fb FGFb ib (D .comp Fa FGFa Fb fha ia) (D .comp Fa Fa Fb Ff (D .comp Fa FGFa Fa ha ia))
               (inverse (D .hom Fa Fb) (D .comp Fa Fa Fb Ff (D .comp Fa FGFa Fa ha ia)) (D .comp Fa FGFa Fb fha ia)
                 (D .assoc Fa FGFa Fa Fb ia ha Ff))
        = D .comp Fa Fb FGFb ib (D .comp Fa Fa Fb Ff (D .idn Fa))
          by cat_whisker_left D Fa Fb FGFb ib (D .comp Fa Fa Fb Ff (D .comp Fa FGFa Fa ha ia)) (D .comp Fa Fa Fb Ff (D .idn Fa))
               (cat_whisker_left D Fa Fa Fb Ff (D .comp Fa FGFa Fa ha ia) (D .idn Fa) (split_eso_iso_section C D F s Fa))
        = D .comp Fa Fb FGFb ib Ff
          by cat_whisker_left D Fa Fb FGFb ib (D .comp Fa Fa Fb Ff (D .idn Fa)) Ff (D .ru Fa Fb Ff)
        = D .comp Fa Fb FGFb (F .mor b GFb eb) Ff
          by cat_whisker_right D Fa Fb FGFb ib (F .mor b GFb eb) Ff
               (inverse (D .hom Fb FGFb) (F .mor b GFb eb) ib (ff_mor_inverse_counit C D F hF b GFb ib))
        = F .mor a GFb (C .comp a b GFb eb f)
          by inverse (D .hom Fa FGFb) (F .mor a GFb (C .comp a b GFb eb f)) (D .comp Fa Fb FGFb (F .mor b GFb eb) Ff)
               (F .map_comp a b GFb f eb) ∎)

def split_eso_unit_is_iso (C D : WildPrecat) (F : WildFunctor C D)
  (hF : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b)) (s : IsSplitEso C D F)
  (a : C .ob) : CatIsIso C a (s (F .obj a) .fst) (split_eso_unit_component C D F hF s a)
  ≔ let GFa ≔ s (F .obj a) .fst in
    let ia ≔ split_eso_iso_inverse C D F s (F .obj a) in
    mor_equiv_functor_reflects_iso C D F hF a GFa (split_eso_unit_component C D F hF s a)
      (cat_is_iso_transport D (F .obj a) (F .obj GFa) ia (F .mor a GFa (split_eso_unit_component C D F hF s a))
        (inverse (D .hom (F .obj a) (F .obj GFa)) (F .mor a GFa (split_eso_unit_component C D F hF s a)) ia
          (ff_mor_inverse_counit C D F hF a GFa ia))
        (cat_iso_inverse D (F .obj GFa) (F .obj a) (s (F .obj a) .snd) .snd))

def split_eso_unit (C D : WildPrecat) (F : WildFunctor C D)
  (hF : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b)) (s : IsSplitEso C D F)
  : NatIso C C (functor_identity C) (functor_compose C D C (split_eso_inverse_functor C D F hF s) F)
  ≔ ((component ≔ split_eso_unit_component C D F hF s,
      natural ≔ split_eso_unit_natural C D F hF s),
     split_eso_unit_is_iso C D F hF s)

{` The inverse map of lem:equiv-precat-is-ff-split-eso: a fully faithful,
   split essentially surjective functor is an equivalence. `}
def ff_split_eso_is_cat_equivalence_native (C D : WildPrecat) (F : WildFunctor C D)
  (hF : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b)) (s : IsSplitEso C D F)
  : IsCatEquivalence C D F
  ≔ cat_equivalence_from_nat_isos C D F (split_eso_inverse_functor C D F hF s)
      (split_eso_unit C D F hF s) (split_eso_counit C D F hF s)

def ff_split_eso_is_cat_equivalence (C D : WildPrecat) (F : WildFunctor C D) (h : IsFullyFaithful C D F)
  (s : IsSplitEso C D F) : IsCatEquivalence C D F
  ≔ ff_split_eso_is_cat_equivalence_native C D F (ff_mor_is_equiv C D F h) s

{` The forward map of lem:equiv-precat-is-ff-split-eso: lem:cat-equiv-ff
   and d ↦ (G(d), ε_d). `}
def cat_equivalence_split_eso (C D : WildPrecat) (F : WildFunctor C D) (E : IsCatEquivalence C D F)
  : IsSplitEso C D F
  ≔ d ↦ (E .fst .right .obj d, (adjunction_counit C D F (E .fst) d, E .snd .snd d))

def cat_equivalence_to_ff_split_eso (C D : WildPrecat) (F : WildFunctor C D) (E : IsCatEquivalence C D F)
  : Product (IsFullyFaithful C D F) (IsSplitEso C D F)
  ≔ (wild_cat_equivalence_ff C D F E, cat_equivalence_split_eso C D F E)

{` The counit of the constructed equivalence is the chosen isomorphism:
   its transpose G(h_d) ∘ η_{Gd} is the identity. `}
def split_eso_transpose_iso_path (C D : WildPrecat) (F : WildFunctor C D)
  (hF : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b)) (s : IsSplitEso C D F)
  (d : D .ob)
  : Id (C .hom (s d .fst) (s d .fst))
      (ff_split_eso_is_cat_equivalence_native C D F hF s .fst .transpose (s d .fst) d (split_eso_iso C D F s d))
      (C .idn (s d .fst))
  ≔ let Gd ≔ s d .fst in
    let FGd ≔ F .obj Gd in
    let GFGd ≔ s FGd .fst in
    let FGFGd ≔ F .obj GFGd in
    let hd ≔ split_eso_iso C D F s d in
    let idd ≔ split_eso_iso_inverse C D F s d in
    let hk ≔ split_eso_iso C D F s FGd in
    let ik ≔ split_eso_iso_inverse C D F s FGd in
    let cj ≔ split_eso_conj C D F s FGd d hd in
    let hdk ≔ D .comp FGFGd FGd d hd hk in
    concat (C .hom Gd Gd)
      (C .comp Gd GFGd Gd (ff_mor_inverse C D F hF GFGd Gd cj) (ff_mor_inverse C D F hF Gd GFGd ik))
      (ff_mor_inverse C D F hF Gd Gd (D .comp FGd FGFGd FGd cj ik))
      (C .idn Gd)
      (inverse (C .hom Gd Gd) (ff_mor_inverse C D F hF Gd Gd (D .comp FGd FGFGd FGd cj ik))
        (C .comp Gd GFGd Gd (ff_mor_inverse C D F hF GFGd Gd cj) (ff_mor_inverse C D F hF Gd GFGd ik))
        (ff_mor_inverse_comp C D F hF Gd GFGd Gd ik cj))
      (concat (C .hom Gd Gd) (ff_mor_inverse C D F hF Gd Gd (D .comp FGd FGFGd FGd cj ik))
        (ff_mor_inverse C D F hF Gd Gd (D .idn FGd)) (C .idn Gd)
        (refl (ff_mor_inverse C D F hF Gd Gd)
          (calc
            D .comp FGd FGFGd FGd (D .comp FGFGd d FGd idd hdk) ik
            = D .comp FGd d FGd idd (D .comp FGd FGFGd d hdk ik)
              by inverse (D .hom FGd FGd) (D .comp FGd d FGd idd (D .comp FGd FGFGd d hdk ik))
                   (D .comp FGd FGFGd FGd (D .comp FGFGd d FGd idd hdk) ik) (D .assoc FGd FGFGd d FGd ik hdk idd)
            = D .comp FGd d FGd idd (D .comp FGd FGd d hd (D .comp FGd FGFGd FGd hk ik))
              by cat_whisker_left D FGd d FGd idd (D .comp FGd FGFGd d hdk ik)
                   (D .comp FGd FGd d hd (D .comp FGd FGFGd FGd hk ik))
                   (inverse (D .hom FGd d) (D .comp FGd FGd d hd (D .comp FGd FGFGd FGd hk ik))
                     (D .comp FGd FGFGd d hdk ik) (D .assoc FGd FGFGd FGd d ik hk hd))
            = D .comp FGd d FGd idd (D .comp FGd FGd d hd (D .idn FGd))
              by cat_whisker_left D FGd d FGd idd (D .comp FGd FGd d hd (D .comp FGd FGFGd FGd hk ik))
                   (D .comp FGd FGd d hd (D .idn FGd))
                   (cat_whisker_left D FGd FGd d hd (D .comp FGd FGFGd FGd hk ik) (D .idn FGd)
                     (split_eso_iso_section C D F s FGd))
            = D .comp FGd d FGd idd hd
              by cat_whisker_left D FGd d FGd idd (D .comp FGd FGd d hd (D .idn FGd)) hd (D .ru FGd d hd)
            = D .idn FGd by split_eso_iso_retraction C D F s d ∎))
        (ff_mor_inverse_idn C D F hF Gd))

def split_eso_counit_path (C D : WildPrecat) (F : WildFunctor C D)
  (hF : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b)) (s : IsSplitEso C D F)
  (d : D .ob)
  : Id (D .hom (F .obj (s d .fst)) d)
      (adjunction_counit C D F (ff_split_eso_is_cat_equivalence_native C D F hF s .fst) d)
      (split_eso_iso C D F s d)
  ≔ ch6c_equiv_inverse_path (D .hom (F .obj (s d .fst)) d) (C .hom (s d .fst) (s d .fst))
      (nat_isos_transpose_equiv C D F (split_eso_inverse_functor C D F hF s)
        (split_eso_unit C D F hF s) (split_eso_counit C D F hF s) (s d .fst) d)
      (split_eso_iso C D F s d) (C .idn (s d .fst))
      (split_eso_transpose_iso_path C D F hF s d)

{` Round trip ff + split eso → equivalence → ff + split eso. `}
def ff_split_eso_round_trip (C D : WildPrecat) (F : WildFunctor C D)
  (x : Product (IsFullyFaithful C D F) (IsSplitEso C D F))
  : Id (Product (IsFullyFaithful C D F) (IsSplitEso C D F))
      (cat_equivalence_to_ff_split_eso C D F (ff_split_eso_is_cat_equivalence C D F (x .fst) (x .snd))) x
  ≔ let hF ≔ ff_mor_is_equiv C D F (x .fst) in
    let s ≔ x .snd in
    let E ≔ ff_split_eso_is_cat_equivalence C D F (x .fst) s in
    (is_fully_faithful_prop C D F (wild_cat_equivalence_ff C D F E) (x .fst),
     funext (D .ob) (d ↦ Σ (C .ob) (c ↦ CatIso D (F .obj c) d)) (cat_equivalence_split_eso C D F E) s
       (d ↦ (refl (s d .fst),
             cat_iso_path D (F .obj (s d .fst)) d (cat_equivalence_split_eso C D F E d .snd) (s d .snd)
               (split_eso_counit_path C D F hF s d))))

{` Litmus: for the identity functor with the split essential surjection
   d ↦ (d, id), the constructed inverse functor sends d to d. `}
def identity_split_eso (C : WildPrecat) : IsSplitEso C C (functor_identity C)
  ≔ d ↦ (d, cat_identity_iso C d)

def identity_ff_split_eso_inverse_obj (C : WildPrecat) (d : C .ob)
  : Id (C .ob) (ff_split_eso_is_cat_equivalence C C (functor_identity C) (identity_cat_equivalence_ff C)
      (identity_split_eso C) .fst .right .obj d) d
  ≔ refl d
