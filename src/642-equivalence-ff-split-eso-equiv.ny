export "641-ff-split-eso-equivalences"

{` Chapter 6, section 6.7, part 3: lem:equiv-precat-is-ff-split-eso. The
   map (F an equivalence) → (F fully faithful and split essentially
   surjective), sending D to (G(D), ε_D), is an equivalence for
   precategories. Its inverse is ff_split_eso_is_cat_equivalence (module
   641); the round trip on equivalences uses that an equivalence structure
   is determined by G on objects and the counit: G(g) = F⁻¹(ε⁻¹ ∘ g ∘ ε)
   and α(k) = G(k) ∘ η'. The proof only needs hom-sets in C. `}

{` Iterated dependent products of propositions. `}
def ch6c_pi_prop2 (A : Type) (B : A → Type) (P : (a : A) → B a → Type)
  (h : (a : A) (b : B a) → isProp (P a b)) : isProp ((a : A) (b : B a) → P a b)
  ≔ pi_prop A (a ↦ (b : B a) → P a b) (a ↦ pi_prop (B a) (P a) (h a))

def ch6c_pi_prop3 (A : Type) (B : A → Type) (X : (a : A) → B a → Type) (P : (a : A) (b : B a) → X a b → Type)
  (h : (a : A) (b : B a) (x : X a b) → isProp (P a b x)) : isProp ((a : A) (b : B a) (x : X a b) → P a b x)
  ≔ pi_prop A (a ↦ (b : B a) (x : X a b) → P a b x) (a ↦ ch6c_pi_prop2 (B a) (X a) (P a) (h a))

def ch6c_pi_prop4 (A : Type) (B : A → Type) (X : (a : A) → B a → Type) (Y : (a : A) (b : B a) → X a b → Type)
  (P : (a : A) (b : B a) (x : X a b) → Y a b x → Type)
  (h : (a : A) (b : B a) (x : X a b) (y : Y a b x) → isProp (P a b x y))
  : isProp ((a : A) (b : B a) (x : X a b) (y : Y a b x) → P a b x y)
  ≔ pi_prop A (a ↦ (b : B a) (x : X a b) (y : Y a b x) → P a b x y)
      (a ↦ ch6c_pi_prop3 (B a) (X a) (Y a) (P a) (h a))

def ch6c_pi_prop5 (A : Type) (B : A → Type) (X : (a : A) → B a → Type) (Y : (a : A) (b : B a) → X a b → Type)
  (Z : (a : A) (b : B a) (x : X a b) → Y a b x → Type)
  (P : (a : A) (b : B a) (x : X a b) (y : Y a b x) → Z a b x y → Type)
  (h : (a : A) (b : B a) (x : X a b) (y : Y a b x) (z : Z a b x y) → isProp (P a b x y z))
  : isProp ((a : A) (b : B a) (x : X a b) (y : Y a b x) (z : Z a b x y) → P a b x y z)
  ≔ pi_prop A (a ↦ (b : B a) (x : X a b) (y : Y a b x) (z : Z a b x y) → P a b x y z)
      (a ↦ ch6c_pi_prop4 (B a) (X a) (Y a) (Z a) (P a) (h a))

{` Calculus of an adjunction: the inverse transposition U = α⁻¹. `}
def adjunction_untranspose_retraction (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  (c : C .ob) (d : D .ob) (k : D .hom (F .obj c) d)
  : Id (D .hom (F .obj c) d) (adjunction_untranspose C D F R c d (R .transpose c d k)) k
  ≔ equivalence_injective (D .hom (F .obj c) d) (C .hom c (R .right .obj d)) (adjunction_transpose_equiv C D F R c d)
      (adjunction_untranspose C D F R c d (R .transpose c d k)) k
      (adjunction_untranspose_section C D F R c d (R .transpose c d k))

{` U(G(g) ∘ m) = g ∘ U(m). `}
def adjunction_untranspose_natural_right (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  (c : C .ob) (d d' : D .ob) (g : D .hom d d') (m : C .hom c (R .right .obj d))
  : Id (D .hom (F .obj c) d')
      (adjunction_untranspose C D F R c d' (C .comp c (R .right .obj d) (R .right .obj d') (R .right .mor d d' g) m))
      (D .comp (F .obj c) d d' g (adjunction_untranspose C D F R c d m))
  ≔ let G ≔ R .right in
    let Um ≔ adjunction_untranspose C D F R c d m in
    let Ggm ≔ C .comp c (G .obj d) (G .obj d') (G .mor d d' g) m in
    equivalence_injective (D .hom (F .obj c) d') (C .hom c (G .obj d')) (adjunction_transpose_equiv C D F R c d')
      (adjunction_untranspose C D F R c d' Ggm) (D .comp (F .obj c) d d' g Um)
      (calc
        R .transpose c d' (adjunction_untranspose C D F R c d' Ggm)
        = Ggm by adjunction_untranspose_section C D F R c d' Ggm
        = C .comp c (G .obj d) (G .obj d') (G .mor d d' g) (R .transpose c d Um)
          by cat_whisker_left C c (G .obj d) (G .obj d') (G .mor d d' g) m (R .transpose c d Um)
               (inverse (C .hom c (G .obj d)) (R .transpose c d Um) m (adjunction_untranspose_section C D F R c d m))
        = R .transpose c d' (D .comp (F .obj c) d d' g Um)
          by R .natural_right c d d' g (refl Um) ∎)

{` U(m) = ε_d ∘ F(m). `}
def adjunction_untranspose_formula (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  (c : C .ob) (d : D .ob) (m : C .hom c (R .right .obj d))
  : Id (D .hom (F .obj c) d) (adjunction_untranspose C D F R c d m)
      (D .comp (F .obj c) (F .obj (R .right .obj d)) d (adjunction_counit C D F R d) (F .mor c (R .right .obj d) m))
  ≔ let G ≔ R .right in
    let Gd ≔ G .obj d in
    let FGd ≔ F .obj Gd in
    let ed ≔ adjunction_counit C D F R d in
    equivalence_injective (D .hom (F .obj c) d) (C .hom c Gd) (adjunction_transpose_equiv C D F R c d)
      (adjunction_untranspose C D F R c d m) (D .comp (F .obj c) FGd d ed (F .mor c Gd m))
      (calc
        R .transpose c d (adjunction_untranspose C D F R c d m)
        = m by adjunction_untranspose_section C D F R c d m
        = C .comp c Gd Gd (C .idn Gd) m
          by inverse (C .hom c Gd) (C .comp c Gd Gd (C .idn Gd) m) m (C .lu c Gd m)
        = C .comp c Gd Gd (R .transpose Gd d ed) m
          by cat_whisker_right C c Gd Gd (C .idn Gd) (R .transpose Gd d ed) m
               (inverse (C .hom Gd Gd) (R .transpose Gd d ed) (C .idn Gd)
                 (adjunction_untranspose_section C D F R Gd d (C .idn Gd)))
        = R .transpose c d (D .comp (F .obj c) FGd d ed (F .mor c Gd m))
          by R .natural_left Gd c m d (refl ed) ∎)

{` Naturality of the counit: ε_y ∘ FG(g) = g ∘ ε_x. `}
def cat_adjunction_counit_naturality (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  (x y : D .ob) (g : D .hom x y)
  : Id (D .hom (F .obj (R .right .obj x)) y)
      (D .comp (F .obj (R .right .obj x)) (F .obj (R .right .obj y)) y (adjunction_counit C D F R y)
        (F .mor (R .right .obj x) (R .right .obj y) (R .right .mor x y g)))
      (D .comp (F .obj (R .right .obj x)) x y g (adjunction_counit C D F R x))
  ≔ let G ≔ R .right in
    let Gx ≔ G .obj x in
    let Gy ≔ G .obj y in
    let U ≔ adjunction_untranspose C D F R Gx y in
    calc
      D .comp (F .obj Gx) (F .obj Gy) y (adjunction_counit C D F R y) (F .mor Gx Gy (G .mor x y g))
      = U (G .mor x y g)
        by inverse (D .hom (F .obj Gx) y) (U (G .mor x y g))
             (D .comp (F .obj Gx) (F .obj Gy) y (adjunction_counit C D F R y) (F .mor Gx Gy (G .mor x y g)))
             (adjunction_untranspose_formula C D F R Gx y (G .mor x y g))
      = U (C .comp Gx Gx Gy (G .mor x y g) (C .idn Gx))
        by refl U (inverse (C .hom Gx Gy) (C .comp Gx Gx Gy (G .mor x y g) (C .idn Gx)) (G .mor x y g)
             (C .ru Gx Gy (G .mor x y g)))
      = D .comp (F .obj Gx) x y g (adjunction_counit C D F R x)
        by adjunction_untranspose_natural_right C D F R Gx x y g (C .idn Gx) ∎

{` The round trip on equivalences, pointwise. Here s is the split
   essential surjection (G(d), ε_d) of the equivalence E, and hF any proof
   that F is fully faithful. `}
def cat_equivalence_round_trip_mor (C D : WildPrecat) (F : WildFunctor C D)
  (hF : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b))
  (E : IsCatEquivalence C D F) (x y : D .ob) (g : D .hom x y)
  : Id (C .hom (E .fst .right .obj x) (E .fst .right .obj y))
      (split_eso_inverse_functor C D F hF (cat_equivalence_split_eso C D F E) .mor x y g)
      (E .fst .right .mor x y g)
  ≔ let R ≔ E .fst in
    let G ≔ R .right in
    let s ≔ cat_equivalence_split_eso C D F E in
    let FGx ≔ F .obj (G .obj x) in
    let FGy ≔ F .obj (G .obj y) in
    let ex ≔ adjunction_counit C D F R x in
    let ey ≔ adjunction_counit C D F R y in
    let iy ≔ split_eso_iso_inverse C D F s y in
    let FGg ≔ F .mor (G .obj x) (G .obj y) (G .mor x y g) in
    ff_mor_inverse_path C D F hF (G .obj x) (G .obj y) (G .mor x y g) (split_eso_conj C D F s x y g)
      (calc
        FGg
        = D .comp FGx FGy FGy (D .idn FGy) FGg
          by inverse (D .hom FGx FGy) (D .comp FGx FGy FGy (D .idn FGy) FGg) FGg (D .lu FGx FGy FGg)
        = D .comp FGx FGy FGy (D .comp FGy y FGy iy ey) FGg
          by cat_whisker_right D FGx FGy FGy (D .idn FGy) (D .comp FGy y FGy iy ey) FGg
               (inverse (D .hom FGy FGy) (D .comp FGy y FGy iy ey) (D .idn FGy) (split_eso_iso_retraction C D F s y))
        = D .comp FGx y FGy iy (D .comp FGx FGy y ey FGg)
          by inverse (D .hom FGx FGy) (D .comp FGx y FGy iy (D .comp FGx FGy y ey FGg))
               (D .comp FGx FGy FGy (D .comp FGy y FGy iy ey) FGg) (D .assoc FGx FGy y FGy FGg ey iy)
        = D .comp FGx y FGy iy (D .comp FGx x y g ex)
          by cat_whisker_left D FGx y FGy iy (D .comp FGx FGy y ey FGg) (D .comp FGx x y g ex)
               (cat_adjunction_counit_naturality C D F R x y g) ∎)

def cat_equivalence_round_trip_transpose (C D : WildPrecat) (F : WildFunctor C D)
  (hF : (a b : C .ob) → isEquiv (C .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b))
  (E : IsCatEquivalence C D F) (c : C .ob) (d : D .ob) (k : D .hom (F .obj c) d)
  : Id (C .hom c (E .fst .right .obj d))
      (ff_split_eso_is_cat_equivalence_native C D F hF (cat_equivalence_split_eso C D F E) .fst .transpose c d k)
      (E .fst .transpose c d k)
  ≔ let R ≔ E .fst in
    let G ≔ R .right in
    let s ≔ cat_equivalence_split_eso C D F E in
    let Fc ≔ F .obj c in
    let GFc ≔ G .obj Fc in
    let FGFc ≔ F .obj GFc in
    let Gd ≔ G .obj d in
    let ec' ≔ split_eso_unit_component C D F hF s c in
    let eFc ≔ adjunction_counit C D F R Fc in
    let iFc ≔ split_eso_iso_inverse C D F s Fc in
    let Gk ≔ G .mor Fc d k in
    let m ≔ C .comp c GFc Gd Gk ec' in
    let U ≔ adjunction_untranspose C D F R c d in
    calc
      C .comp c GFc Gd (split_eso_inverse_functor C D F hF s .mor Fc d k) ec'
      = m
        by cat_whisker_right C c GFc Gd (split_eso_inverse_functor C D F hF s .mor Fc d k) Gk ec'
             (cat_equivalence_round_trip_mor C D F hF E Fc d k)
      = R .transpose c d (U m)
        by inverse (C .hom c Gd) (R .transpose c d (U m)) m (adjunction_untranspose_section C D F R c d m)
      = R .transpose c d k
        by refl (R .transpose c d)
             (calc
               U m
               = D .comp Fc Fc d k (adjunction_untranspose C D F R c Fc ec')
                 by adjunction_untranspose_natural_right C D F R c Fc d k ec'
               = D .comp Fc Fc d k (D .comp Fc FGFc Fc eFc (F .mor c GFc ec'))
                 by cat_whisker_left D Fc Fc d k (adjunction_untranspose C D F R c Fc ec')
                      (D .comp Fc FGFc Fc eFc (F .mor c GFc ec'))
                      (adjunction_untranspose_formula C D F R c Fc ec')
               = D .comp Fc Fc d k (D .comp Fc FGFc Fc eFc iFc)
                 by cat_whisker_left D Fc Fc d k (D .comp Fc FGFc Fc eFc (F .mor c GFc ec'))
                      (D .comp Fc FGFc Fc eFc iFc)
                      (cat_whisker_left D Fc FGFc Fc eFc (F .mor c GFc ec') iFc
                        (ff_mor_inverse_counit C D F hF c GFc iFc))
               = D .comp Fc Fc d k (D .idn Fc)
                 by cat_whisker_left D Fc Fc d k (D .comp Fc FGFc Fc eFc iFc) (D .idn Fc)
                      (split_eso_iso_section C D F s Fc)
               = k by D .ru Fc d k ∎) ∎

{` Right adjoint data as a structure on its core (G on objects and
   arrows, and the transposition) with proposition-valued laws when C has
   hom-sets. `}
def AdjointCore (C D : WildPrecat) (F : WildFunctor C D) : Type
  ≔ Σ (D .ob → C .ob) (o ↦ Product ((x y : D .ob) → D .hom x y → C .hom (o x) (o y))
      ((c : C .ob) (d : D .ob) → D .hom (F .obj c) d → C .hom c (o d)))

def AdjointLawMapId (C D : WildPrecat) (F : WildFunctor C D) (t : AdjointCore C D F) : Type
  ≔ (x : D .ob) → Id (C .hom (t .fst x) (t .fst x)) (t .snd .fst x x (D .idn x)) (C .idn (t .fst x))

def AdjointLawMapComp (C D : WildPrecat) (F : WildFunctor C D) (t : AdjointCore C D F) : Type
  ≔ (x y z : D .ob) (f : D .hom x y) (g : D .hom y z)
    → Id (C .hom (t .fst x) (t .fst z)) (t .snd .fst x z (D .comp x y z g f))
        (C .comp (t .fst x) (t .fst y) (t .fst z) (t .snd .fst y z g) (t .snd .fst x y f))

def AdjointLawTransposeIso (C D : WildPrecat) (F : WildFunctor C D) (t : AdjointCore C D F) : Type
  ≔ (c : C .ob) (d : D .ob) → CatIsIso TypeWild (D .hom (F .obj c) d) (C .hom c (t .fst d)) (t .snd .snd c d)

def AdjointLawNaturalLeft (C D : WildPrecat) (F : WildFunctor C D) (t : AdjointCore C D F) : Type
  ≔ (c c' : C .ob) (f : C .hom c' c) (d : D .ob)
    → Id (D .hom (F .obj c) d → C .hom c' (t .fst d))
        (k ↦ C .comp c' c (t .fst d) (t .snd .snd c d k) f)
        (k ↦ t .snd .snd c' d (D .comp (F .obj c') (F .obj c) d k (F .mor c' c f)))

def AdjointLawNaturalRight (C D : WildPrecat) (F : WildFunctor C D) (t : AdjointCore C D F) : Type
  ≔ (c : C .ob) (d d' : D .ob) (g : D .hom d d')
    → Id (D .hom (F .obj c) d → C .hom c (t .fst d'))
        (k ↦ C .comp c (t .fst d) (t .fst d') (t .snd .fst d d' g) (t .snd .snd c d k))
        (k ↦ t .snd .snd c d' (D .comp (F .obj c) d d' g k))

def AdjointLaws (C D : WildPrecat) (F : WildFunctor C D) (t : AdjointCore C D F) : Type
  ≔ Product (AdjointLawMapId C D F t)
      (Product (AdjointLawMapComp C D F t)
        (Product (AdjointLawTransposeIso C D F t)
          (Product (AdjointLawNaturalLeft C D F t) (AdjointLawNaturalRight C D F t))))

def adjoint_laws_prop (C D : WildPrecat) (F : WildFunctor C D) (hs : HasHomSets C) (t : AdjointCore C D F)
  : isProp (AdjointLaws C D F t)
  ≔ let o ≔ t .fst in
    let mo ≔ t .snd .fst in
    let tr ≔ t .snd .snd in
    product_prop (AdjointLawMapId C D F t)
      (Product (AdjointLawMapComp C D F t)
        (Product (AdjointLawTransposeIso C D F t)
          (Product (AdjointLawNaturalLeft C D F t) (AdjointLawNaturalRight C D F t))))
      (pi_prop (D .ob) (x ↦ Id (C .hom (o x) (o x)) (mo x x (D .idn x)) (C .idn (o x)))
        (x ↦ hs (o x) (o x) (mo x x (D .idn x)) (C .idn (o x))))
      (product_prop (AdjointLawMapComp C D F t)
        (Product (AdjointLawTransposeIso C D F t)
          (Product (AdjointLawNaturalLeft C D F t) (AdjointLawNaturalRight C D F t)))
        (ch6c_pi_prop5 (D .ob) (_ ↦ D .ob) (_ _ ↦ D .ob) (x y _ ↦ D .hom x y) (_ y z _ ↦ D .hom y z)
          (x y z f g ↦ Id (C .hom (o x) (o z)) (mo x z (D .comp x y z g f))
            (C .comp (o x) (o y) (o z) (mo y z g) (mo x y f)))
          (x y z f g ↦ hs (o x) (o z) (mo x z (D .comp x y z g f))
            (C .comp (o x) (o y) (o z) (mo y z g) (mo x y f))))
        (product_prop (AdjointLawTransposeIso C D F t)
          (Product (AdjointLawNaturalLeft C D F t) (AdjointLawNaturalRight C D F t))
          (ch6c_pi_prop2 (C .ob) (_ ↦ D .ob)
            (c d ↦ CatIsIso TypeWild (D .hom (F .obj c) d) (C .hom c (o d)) (tr c d))
            (c d ↦ cat_is_iso_prop TypeWild (D .hom (F .obj c) d) (C .hom c (o d)) (tr c d)))
          (product_prop (AdjointLawNaturalLeft C D F t) (AdjointLawNaturalRight C D F t)
            (ch6c_pi_prop4 (C .ob) (_ ↦ C .ob) (c c' ↦ C .hom c' c) (_ _ _ ↦ D .ob)
              (c c' f d ↦ Id (D .hom (F .obj c) d → C .hom c' (o d))
                (k ↦ C .comp c' c (o d) (tr c d k) f)
                (k ↦ tr c' d (D .comp (F .obj c') (F .obj c) d k (F .mor c' c f))))
              (c c' f d ↦ pi_set (D .hom (F .obj c) d) (_ ↦ C .hom c' (o d)) (_ ↦ hs c' (o d))
                (k ↦ C .comp c' c (o d) (tr c d k) f)
                (k ↦ tr c' d (D .comp (F .obj c') (F .obj c) d k (F .mor c' c f)))))
            (ch6c_pi_prop4 (C .ob) (_ ↦ D .ob) (_ _ ↦ D .ob) (_ d d' ↦ D .hom d d')
              (c d d' g ↦ Id (D .hom (F .obj c) d → C .hom c (o d'))
                (k ↦ C .comp c (o d) (o d') (mo d d' g) (tr c d k))
                (k ↦ tr c d' (D .comp (F .obj c) d d' g k)))
              (c d d' g ↦ pi_set (D .hom (F .obj c) d) (_ ↦ C .hom c (o d')) (_ ↦ hs c (o d'))
                (k ↦ C .comp c (o d) (o d') (mo d d' g) (tr c d k))
                (k ↦ tr c d' (D .comp (F .obj c) d d' g k)))))))

def right_adjoint_data_sigma_equiv (C D : WildPrecat) (F : WildFunctor C D)
  : Equiv (RightAdjointData C D F) (Σ (AdjointCore C D F) (AdjointLaws C D F))
  ≔ quasi_inverse_equiv (RightAdjointData C D F) (Σ (AdjointCore C D F) (AdjointLaws C D F))
      (R ↦ ((R .right .obj, (R .right .mor, R .transpose)),
            (R .right .map_id, (R .right .map_comp, (R .transpose_iso, (R .natural_left, R .natural_right))))))
      (u ↦ (right ≔ (obj ≔ u .fst .fst, mor ≔ u .fst .snd .fst, map_id ≔ u .snd .fst, map_comp ≔ u .snd .snd .fst),
            transpose ≔ u .fst .snd .snd,
            transpose_iso ≔ u .snd .snd .snd .fst,
            natural_left ≔ u .snd .snd .snd .snd .fst,
            natural_right ≔ u .snd .snd .snd .snd .snd))
      (R ↦ refl R) (u ↦ refl u)

def right_adjoint_data_core (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  : AdjointCore C D F
  ≔ (R .right .obj, (R .right .mor, R .transpose))

{` When C has hom-sets, right adjoint data are identified as soon as their
   cores are. `}
def right_adjoint_data_path (C D : WildPrecat) (F : WildFunctor C D) (hs : HasHomSets C)
  (R R' : RightAdjointData C D F)
  (p : Id (AdjointCore C D F) (right_adjoint_data_core C D F R) (right_adjoint_data_core C D F R'))
  : Id (RightAdjointData C D F) R R'
  ≔ let e ≔ right_adjoint_data_sigma_equiv C D F in
    equivalence_injective (RightAdjointData C D F) (Σ (AdjointCore C D F) (AdjointLaws C D F)) e R R'
      (equiv_inverse_map (Id (Σ (AdjointCore C D F) (AdjointLaws C D F)) (e .map R) (e .map R'))
        (Id (AdjointCore C D F) (right_adjoint_data_core C D F R) (right_adjoint_data_core C D F R'))
        (subtype_path_equiv (AdjointCore C D F) (AdjointLaws C D F) (adjoint_laws_prop C D F hs) (e .map R) (e .map R'))
        p)

{` The unit and counit conditions of def:cat-equiv are propositions. `}
def CatEquivalenceIsoConditions (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F) : Type
  ≔ Product ((c : C .ob) → CatIsIso C c (R .right .obj (F .obj c)) (adjunction_unit C D F R c))
      ((d : D .ob) → CatIsIso D (F .obj (R .right .obj d)) d (adjunction_counit C D F R d))

def cat_equivalence_iso_conditions_prop (C D : WildPrecat) (F : WildFunctor C D) (R : RightAdjointData C D F)
  : isProp (CatEquivalenceIsoConditions C D F R)
  ≔ product_prop ((c : C .ob) → CatIsIso C c (R .right .obj (F .obj c)) (adjunction_unit C D F R c))
      ((d : D .ob) → CatIsIso D (F .obj (R .right .obj d)) d (adjunction_counit C D F R d))
      (pi_prop (C .ob) (c ↦ CatIsIso C c (R .right .obj (F .obj c)) (adjunction_unit C D F R c))
        (c ↦ cat_is_iso_prop C c (R .right .obj (F .obj c)) (adjunction_unit C D F R c)))
      (pi_prop (D .ob) (d ↦ CatIsIso D (F .obj (R .right .obj d)) d (adjunction_counit C D F R d))
        (d ↦ cat_is_iso_prop D (F .obj (R .right .obj d)) d (adjunction_counit C D F R d)))

def is_cat_equivalence_path (C D : WildPrecat) (F : WildFunctor C D) (E E' : IsCatEquivalence C D F)
  (p : Id (RightAdjointData C D F) (E .fst) (E' .fst)) : Id (IsCatEquivalence C D F) E E'
  ≔ equiv_inverse_map (Id (IsCatEquivalence C D F) E E') (Id (RightAdjointData C D F) (E .fst) (E' .fst))
      (subtype_path_equiv (RightAdjointData C D F) (CatEquivalenceIsoConditions C D F)
        (cat_equivalence_iso_conditions_prop C D F) E E')
      p

{` The round trip equivalence → ff + split eso → equivalence. `}
def cat_equivalence_round_trip (C D : WildPrecat) (F : WildFunctor C D) (hs : HasHomSets C)
  (E : IsCatEquivalence C D F)
  : Id (IsCatEquivalence C D F)
      (ff_split_eso_is_cat_equivalence C D F (cat_equivalence_to_ff_split_eso C D F E .fst)
        (cat_equivalence_to_ff_split_eso C D F E .snd)) E
  ≔ let hF ≔ ff_mor_is_equiv C D F (wild_cat_equivalence_ff C D F E) in
    let s ≔ cat_equivalence_split_eso C D F E in
    let E' ≔ ff_split_eso_is_cat_equivalence_native C D F hF s in
    let G ≔ E .fst .right in
    is_cat_equivalence_path C D F E' E
      (right_adjoint_data_path C D F hs (E' .fst) (E .fst)
        (refl (G .obj),
         (funext3 (D .ob) (_ ↦ D .ob) (x y ↦ D .hom x y) (x y _ ↦ C .hom (G .obj x) (G .obj y))
            (E' .fst .right .mor) (G .mor) (x y g ↦ cat_equivalence_round_trip_mor C D F hF E x y g),
          funext3 (C .ob) (_ ↦ D .ob) (c d ↦ D .hom (F .obj c) d) (c d _ ↦ C .hom c (G .obj d))
            (E' .fst .transpose) (E .fst .transpose)
            (c d k ↦ cat_equivalence_round_trip_transpose C D F hF E c d k))))

{` lem:equiv-precat-is-ff-split-eso (with hom-sets only needed in C). `}
def wild_cat_equivalence_ff_split_eso_equiv (C D : WildPrecat) (F : WildFunctor C D) (hs : HasHomSets C)
  : BookEquiv (IsCatEquivalence C D F) (Product (IsFullyFaithful C D F) (IsSplitEso C D F))
  ≔ book_quasi_inverse_equiv (IsCatEquivalence C D F) (Product (IsFullyFaithful C D F) (IsSplitEso C D F))
      (cat_equivalence_to_ff_split_eso C D F)
      (x ↦ ff_split_eso_is_cat_equivalence C D F (x .fst) (x .snd))
      (cat_equivalence_round_trip C D F hs)
      (ff_split_eso_round_trip C D F)

{` lem:equiv-precat-is-ff-split-eso for precategories C and D: the map
   E ↦ (lem:cat-equiv-ff, D ↦ (G(D), ε_D)) is an equivalence. `}
def cat_equivalence_ff_split_eso_equiv (C D : Precat) (F : WildFunctor (C .wild) (D .wild))
  : BookEquiv (IsCatEquivalence (C .wild) (D .wild) F)
      (Product (IsFullyFaithful (C .wild) (D .wild) F) (IsSplitEso (C .wild) (D .wild) F))
  ≔ wild_cat_equivalence_ff_split_eso_equiv (C .wild) (D .wild) F (C .homset)

def cat_equivalence_ff_split_eso_is_equiv (C D : Precat) (F : WildFunctor (C .wild) (D .wild))
  : BookIsEquiv (IsCatEquivalence (C .wild) (D .wild) F)
      (Product (IsFullyFaithful (C .wild) (D .wild) F) (IsSplitEso (C .wild) (D .wild) F))
      (cat_equivalence_to_ff_split_eso (C .wild) (D .wild) F)
  ≔ cat_equivalence_ff_split_eso_equiv C D F .equiv

{` Litmus: the map of the lemma sends the identity equivalence to the
   split essential surjection d ↦ (d, id_d). `}
def identity_cat_equivalence_split_eso (C : WildPrecat) (d : C .ob)
  : Id (Σ (C .ob) (c ↦ CatIso C c d))
      (cat_equivalence_to_ff_split_eso C C (functor_identity C) (identity_is_cat_equivalence C) .snd d)
      (d, cat_identity_iso C d)
  ≔ refl ((d, cat_identity_iso C d) : Σ (C .ob) (c ↦ CatIso C c d))
