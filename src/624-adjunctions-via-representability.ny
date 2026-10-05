export "623-representable-presheaves"

{` Chapter 6 (cats.tex), section 6.6: adjunctions via representability
   (lem:adj-via-repr) and uniqueness of right adjoints (cor:adj-unique).

   Since D may be wild, Hom_D(F -, d) need not be Set-valued; as in
   def:adjunction (RightAdjointData, module 603) we use U-valued functors
   C^op → U (TypeWild), and yo(G(d)) is the U-valued representable h_{G(d)}
   (its Set-valued version has the same underlying data, see
   representable_presheaf_underlying). `}

{` Hom_D(F -, d) : C^op → U, as in adjunction_nat_trans_left. `}
def left_adjoint_hom_functor (C D : WildPrecat) (F : WildFunctor C D) (d : D .ob)
  : WildFunctor (OppositeWild C) TypeWild
  ≔ functor_compose (OppositeWild C) (OppositeWild D) TypeWild (contravariant_representable D d)
      (opposite_functor C D F)

{` The hypotheses of lem:adj-via-repr: natural isomorphisms
   α_d : Hom_D(F -, d) ≅ yo(G(d)) for every object d. `}
def AdjRepresentingData (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D) (G0 : D .ob → C .wild .ob)
  : Type
  ≔ (d : D .ob) → NatIso (OppositeWild (C .wild)) TypeWild (left_adjoint_hom_functor (C .wild) D F d)
      (contravariant_representable (C .wild) (G0 d))

def AdjExtMor (C : Precat) (D : WildPrecat) (G0 : D .ob → C .wild .ob) : Type
  ≔ (d d' : D .ob) → D .hom d d' → C .wild .hom (G0 d) (G0 d')

def AdjExtMapId (C : Precat) (D : WildPrecat) (G0 : D .ob → C .wild .ob) (m : AdjExtMor C D G0) : Type
  ≔ (d : D .ob) → Id (C .wild .hom (G0 d) (G0 d)) (m d d (D .idn d)) (C .wild .idn (G0 d))

def AdjExtMapComp (C : Precat) (D : WildPrecat) (G0 : D .ob → C .wild .ob) (m : AdjExtMor C D G0) : Type
  ≔ (d d' d'' : D .ob) (g : D .hom d d') (g' : D .hom d' d'')
    → Id (C .wild .hom (G0 d) (G0 d'')) (m d d'' (D .comp d d' d'' g' g))
        (C .wild .comp (G0 d) (G0 d') (G0 d'') (m d' d'' g') (m d d' g))

{` Naturality of α_d in d (the field natural_right of RightAdjointData). `}
def AdjExtNatural (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D) (G0 : D .ob → C .wild .ob)
  (alpha : AdjRepresentingData C D F G0) (m : AdjExtMor C D G0) : Type
  ≔ (c : C .wild .ob) (d d' : D .ob) (g : D .hom d d')
    → Id (D .hom (F .obj c) d → C .wild .hom c (G0 d'))
        (k ↦ C .wild .comp c (G0 d) (G0 d') (m d d' g) (alpha d .fst .component c k))
        (k ↦ alpha d' .fst .component c (D .comp (F .obj c) d d' g k))

{` lem:adj-via-repr: the type of extensions of G to a functor D → C (with
   action on objects G0) such that α_d is natural in d. `}
def AdjunctionExtension (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D) (G0 : D .ob → C .wild .ob)
  (alpha : AdjRepresentingData C D F G0) : Type
  ≔ Σ (AdjExtMor C D G0) (m ↦
      Product (AdjExtMapId C D G0 m) (Product (AdjExtMapComp C D G0 m) (AdjExtNatural C D F G0 alpha m)))

{` An extension is exactly the remaining data of a (wild) adjunction. `}
def adjunction_extension_right_adjoint (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D)
  (G0 : D .ob → C .wild .ob) (alpha : AdjRepresentingData C D F G0) (E : AdjunctionExtension C D F G0 alpha)
  : RightAdjointData (C .wild) D F
  ≔ (right ≔ (obj ≔ G0, mor ≔ E .fst, map_id ≔ E .snd .fst, map_comp ≔ E .snd .snd .fst),
     transpose ≔ c d ↦ alpha d .fst .component c,
     transpose_iso ≔ c d ↦ alpha d .snd c,
     natural_left ≔ c c' f d ↦ alpha d .fst .natural c c' f,
     natural_right ≔ E .snd .snd .snd)

{` Inverse transposition, its section law, and injectivity of α. `}
def adj_repr_untranspose (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D) (G0 : D .ob → C .wild .ob)
  (alpha : AdjRepresentingData C D F G0) (d : D .ob) (c : C .wild .ob)
  : C .wild .hom c (G0 d) → D .hom (F .obj c) d
  ≔ alpha d .snd c .fst .fst

def adj_repr_section (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D) (G0 : D .ob → C .wild .ob)
  (alpha : AdjRepresentingData C D F G0) (d : D .ob) (c : C .wild .ob) (m : C .wild .hom c (G0 d))
  : Id (C .wild .hom c (G0 d)) (alpha d .fst .component c (adj_repr_untranspose C D F G0 alpha d c m)) m
  ≔ alpha d .snd c .fst .snd (refl m)

def adj_repr_injective (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D) (G0 : D .ob → C .wild .ob)
  (alpha : AdjRepresentingData C D F G0) (d : D .ob) (c : C .wild .ob) (x y : D .hom (F .obj c) d)
  (q : Id (C .wild .hom c (G0 d)) (alpha d .fst .component c x) (alpha d .fst .component c y))
  : Id (D .hom (F .obj c) d) x y
  ≔ let r ≔ alpha d .snd c .snd .fst in
    concat (D .hom (F .obj c) d) x (r (alpha d .fst .component c x)) y
      (inverse (D .hom (F .obj c) d) (r (alpha d .fst .component c x)) x (alpha d .snd c .snd .snd (refl x)))
      (concat (D .hom (F .obj c) d) (r (alpha d .fst .component c x)) (r (alpha d .fst .component c y)) y
        (refl r q) (alpha d .snd c .snd .snd (refl y)))

{` ε_d = α_d⁻¹(id_{G(d)}). `}
def adj_repr_counit (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D) (G0 : D .ob → C .wild .ob)
  (alpha : AdjRepresentingData C D F G0) (d : D .ob) : D .hom (F .obj (G0 d)) d
  ≔ adj_repr_untranspose C D F G0 alpha d (G0 d) (C .wild .idn (G0 d))

{` α_{d,c}(ε_d ∘ F f) = f. `}
def adj_repr_counit_transpose (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D)
  (G0 : D .ob → C .wild .ob) (alpha : AdjRepresentingData C D F G0) (d : D .ob) (c : C .wild .ob)
  (f : C .wild .hom c (G0 d))
  : Id (C .wild .hom c (G0 d))
      (alpha d .fst .component c
        (D .comp (F .obj c) (F .obj (G0 d)) d (adj_repr_counit C D F G0 alpha d) (F .mor c (G0 d) f)))
      f
  ≔ let e ≔ adj_repr_counit C D F G0 alpha d in
    calc
      alpha d .fst .component c (D .comp (F .obj c) (F .obj (G0 d)) d e (F .mor c (G0 d) f))
      = C .wild .comp c (G0 d) (G0 d) (alpha d .fst .component (G0 d) e) f
        by inverse (C .wild .hom c (G0 d)) (C .wild .comp c (G0 d) (G0 d) (alpha d .fst .component (G0 d) e) f)
             (alpha d .fst .component c (D .comp (F .obj c) (F .obj (G0 d)) d e (F .mor c (G0 d) f)))
             (happly (D .hom (F .obj (G0 d)) d) (_ ↦ C .wild .hom c (G0 d))
               (k ↦ C .wild .comp c (G0 d) (G0 d) (alpha d .fst .component (G0 d) k) f)
               (k ↦ alpha d .fst .component c (D .comp (F .obj c) (F .obj (G0 d)) d k (F .mor c (G0 d) f)))
               (alpha d .fst .natural (G0 d) c f) e)
      = C .wild .comp c (G0 d) (G0 d) (C .wild .idn (G0 d)) f
        by cat_whisker_right (C .wild) c (G0 d) (G0 d) (alpha d .fst .component (G0 d) e) (C .wild .idn (G0 d)) f
             (adj_repr_section C D F G0 alpha d (G0 d) (C .wild .idn (G0 d)))
      = f by C .wild .lu c (G0 d) f ∎

{` ε_d ∘ F(α_{d,c} k) = k. `}
def adj_repr_counit_untranspose (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D)
  (G0 : D .ob → C .wild .ob) (alpha : AdjRepresentingData C D F G0) (d : D .ob) (c : C .wild .ob)
  (k : D .hom (F .obj c) d)
  : Id (D .hom (F .obj c) d)
      (D .comp (F .obj c) (F .obj (G0 d)) d (adj_repr_counit C D F G0 alpha d)
        (F .mor c (G0 d) (alpha d .fst .component c k)))
      k
  ≔ adj_repr_injective C D F G0 alpha d c
      (D .comp (F .obj c) (F .obj (G0 d)) d (adj_repr_counit C D F G0 alpha d)
        (F .mor c (G0 d) (alpha d .fst .component c k))) k
      (adj_repr_counit_transpose C D F G0 alpha d c (alpha d .fst .component c k))

{` The forced action on arrows: G(g) = α_{d'}(g ∘ ε_d). `}
def adj_repr_mor (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D) (G0 : D .ob → C .wild .ob)
  (alpha : AdjRepresentingData C D F G0) : AdjExtMor C D G0
  ≔ d d' g ↦ alpha d' .fst .component (G0 d) (D .comp (F .obj (G0 d)) d d' g (adj_repr_counit C D F G0 alpha d))

def AdjExtNaturalAt (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D) (G0 : D .ob → C .wild .ob)
  (alpha : AdjRepresentingData C D F G0) (d d' : D .ob) (g : D .hom d d') (m : C .wild .hom (G0 d) (G0 d'))
  : Type
  ≔ (c : C .wild .ob)
    → Id (D .hom (F .obj c) d → C .wild .hom c (G0 d'))
        (k ↦ C .wild .comp c (G0 d) (G0 d') m (alpha d .fst .component c k))
        (k ↦ alpha d' .fst .component c (D .comp (F .obj c) d d' g k))

{` Uniqueness: an arrow making α natural at g is the forced one. `}
def adj_repr_mor_unique (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D) (G0 : D .ob → C .wild .ob)
  (alpha : AdjRepresentingData C D F G0) (d d' : D .ob) (g : D .hom d d') (m : C .wild .hom (G0 d) (G0 d'))
  (nr : AdjExtNaturalAt C D F G0 alpha d d' g m)
  : Id (C .wild .hom (G0 d) (G0 d')) m (adj_repr_mor C D F G0 alpha d d' g)
  ≔ let e ≔ adj_repr_counit C D F G0 alpha d in
    calc
      m
      = C .wild .comp (G0 d) (G0 d) (G0 d') m (C .wild .idn (G0 d))
        by inverse (C .wild .hom (G0 d) (G0 d')) (C .wild .comp (G0 d) (G0 d) (G0 d') m (C .wild .idn (G0 d))) m
             (C .wild .ru (G0 d) (G0 d') m)
      = C .wild .comp (G0 d) (G0 d) (G0 d') m (alpha d .fst .component (G0 d) e)
        by cat_whisker_left (C .wild) (G0 d) (G0 d) (G0 d') m (C .wild .idn (G0 d)) (alpha d .fst .component (G0 d) e)
             (inverse (C .wild .hom (G0 d) (G0 d)) (alpha d .fst .component (G0 d) e) (C .wild .idn (G0 d))
               (adj_repr_section C D F G0 alpha d (G0 d) (C .wild .idn (G0 d))))
      = adj_repr_mor C D F G0 alpha d d' g
        by happly (D .hom (F .obj (G0 d)) d) (_ ↦ C .wild .hom (G0 d) (G0 d'))
             (k ↦ C .wild .comp (G0 d) (G0 d) (G0 d') m (alpha d .fst .component (G0 d) k))
             (k ↦ alpha d' .fst .component (G0 d) (D .comp (F .obj (G0 d)) d d' g k))
             (nr (G0 d)) e ∎

{` Existence: the forced arrow makes α natural. `}
def adj_repr_mor_natural_at (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D) (G0 : D .ob → C .wild .ob)
  (alpha : AdjRepresentingData C D F G0) (d d' : D .ob) (g : D .hom d d') (c : C .wild .ob) (k : D .hom (F .obj c) d)
  : Id (C .wild .hom c (G0 d'))
      (C .wild .comp c (G0 d) (G0 d') (adj_repr_mor C D F G0 alpha d d' g) (alpha d .fst .component c k))
      (alpha d' .fst .component c (D .comp (F .obj c) d d' g k))
  ≔ let e ≔ adj_repr_counit C D F G0 alpha d in
    let ak ≔ alpha d .fst .component c k in
    let a' ≔ alpha d' .fst .component c in
    calc
      C .wild .comp c (G0 d) (G0 d') (alpha d' .fst .component (G0 d) (D .comp (F .obj (G0 d)) d d' g e)) ak
      = a' (D .comp (F .obj c) (F .obj (G0 d)) d' (D .comp (F .obj (G0 d)) d d' g e) (F .mor c (G0 d) ak))
        by happly (D .hom (F .obj (G0 d)) d') (_ ↦ C .wild .hom c (G0 d'))
             (k' ↦ C .wild .comp c (G0 d) (G0 d') (alpha d' .fst .component (G0 d) k') ak)
             (k' ↦ a' (D .comp (F .obj c) (F .obj (G0 d)) d' k' (F .mor c (G0 d) ak)))
             (alpha d' .fst .natural (G0 d) c ak) (D .comp (F .obj (G0 d)) d d' g e)
      = a' (D .comp (F .obj c) d d' g (D .comp (F .obj c) (F .obj (G0 d)) d e (F .mor c (G0 d) ak)))
        by refl a' (inverse (D .hom (F .obj c) d')
             (D .comp (F .obj c) d d' g (D .comp (F .obj c) (F .obj (G0 d)) d e (F .mor c (G0 d) ak)))
             (D .comp (F .obj c) (F .obj (G0 d)) d' (D .comp (F .obj (G0 d)) d d' g e) (F .mor c (G0 d) ak))
             (D .assoc (F .obj c) (F .obj (G0 d)) d d' (F .mor c (G0 d) ak) e g))
      = a' (D .comp (F .obj c) d d' g k)
        by refl a' (cat_whisker_left D (F .obj c) d d' g
             (D .comp (F .obj c) (F .obj (G0 d)) d e (F .mor c (G0 d) ak)) k
             (adj_repr_counit_untranspose C D F G0 alpha d c k)) ∎

def adj_repr_mor_natural (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D) (G0 : D .ob → C .wild .ob)
  (alpha : AdjRepresentingData C D F G0) : AdjExtNatural C D F G0 alpha (adj_repr_mor C D F G0 alpha)
  ≔ c d d' g ↦ funext (D .hom (F .obj c) d) (_ ↦ C .wild .hom c (G0 d'))
      (k ↦ C .wild .comp c (G0 d) (G0 d') (adj_repr_mor C D F G0 alpha d d' g) (alpha d .fst .component c k))
      (k ↦ alpha d' .fst .component c (D .comp (F .obj c) d d' g k))
      (adj_repr_mor_natural_at C D F G0 alpha d d' g c)

def adj_repr_map_id (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D) (G0 : D .ob → C .wild .ob)
  (alpha : AdjRepresentingData C D F G0) : AdjExtMapId C D G0 (adj_repr_mor C D F G0 alpha)
  ≔ d ↦ inverse (C .wild .hom (G0 d) (G0 d)) (C .wild .idn (G0 d)) (adj_repr_mor C D F G0 alpha d d (D .idn d))
      (adj_repr_mor_unique C D F G0 alpha d d (D .idn d) (C .wild .idn (G0 d))
        (c ↦ funext (D .hom (F .obj c) d) (_ ↦ C .wild .hom c (G0 d))
           (k ↦ C .wild .comp c (G0 d) (G0 d) (C .wild .idn (G0 d)) (alpha d .fst .component c k))
           (k ↦ alpha d .fst .component c (D .comp (F .obj c) d d (D .idn d) k))
           (k ↦ concat (C .wild .hom c (G0 d))
              (C .wild .comp c (G0 d) (G0 d) (C .wild .idn (G0 d)) (alpha d .fst .component c k))
              (alpha d .fst .component c k)
              (alpha d .fst .component c (D .comp (F .obj c) d d (D .idn d) k))
              (C .wild .lu c (G0 d) (alpha d .fst .component c k))
              (refl (alpha d .fst .component c)
                (inverse (D .hom (F .obj c) d) (D .comp (F .obj c) d d (D .idn d) k) k (D .lu (F .obj c) d k))))))

def adj_repr_map_comp_natural (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D) (G0 : D .ob → C .wild .ob)
  (alpha : AdjRepresentingData C D F G0) (d d' d'' : D .ob) (g : D .hom d d') (g' : D .hom d' d'')
  (c : C .wild .ob) (k : D .hom (F .obj c) d)
  : Id (C .wild .hom c (G0 d''))
      (C .wild .comp c (G0 d) (G0 d'')
        (C .wild .comp (G0 d) (G0 d') (G0 d'') (adj_repr_mor C D F G0 alpha d' d'' g')
          (adj_repr_mor C D F G0 alpha d d' g))
        (alpha d .fst .component c k))
      (alpha d'' .fst .component c (D .comp (F .obj c) d d'' (D .comp d d' d'' g' g) k))
  ≔ let m ≔ adj_repr_mor C D F G0 alpha d d' g in
    let m' ≔ adj_repr_mor C D F G0 alpha d' d'' g' in
    let ak ≔ alpha d .fst .component c k in
    calc
      C .wild .comp c (G0 d) (G0 d'') (C .wild .comp (G0 d) (G0 d') (G0 d'') m' m) ak
      = C .wild .comp c (G0 d') (G0 d'') m' (C .wild .comp c (G0 d) (G0 d') m ak)
        by inverse (C .wild .hom c (G0 d''))
             (C .wild .comp c (G0 d') (G0 d'') m' (C .wild .comp c (G0 d) (G0 d') m ak))
             (C .wild .comp c (G0 d) (G0 d'') (C .wild .comp (G0 d) (G0 d') (G0 d'') m' m) ak)
             (C .wild .assoc c (G0 d) (G0 d') (G0 d'') ak m m')
      = C .wild .comp c (G0 d') (G0 d'') m' (alpha d' .fst .component c (D .comp (F .obj c) d d' g k))
        by cat_whisker_left (C .wild) c (G0 d') (G0 d'') m' (C .wild .comp c (G0 d) (G0 d') m ak)
             (alpha d' .fst .component c (D .comp (F .obj c) d d' g k))
             (adj_repr_mor_natural_at C D F G0 alpha d d' g c k)
      = alpha d'' .fst .component c (D .comp (F .obj c) d' d'' g' (D .comp (F .obj c) d d' g k))
        by adj_repr_mor_natural_at C D F G0 alpha d' d'' g' c (D .comp (F .obj c) d d' g k)
      = alpha d'' .fst .component c (D .comp (F .obj c) d d'' (D .comp d d' d'' g' g) k)
        by refl (alpha d'' .fst .component c) (D .assoc (F .obj c) d d' d'' k g g') ∎

def adj_repr_map_comp (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D) (G0 : D .ob → C .wild .ob)
  (alpha : AdjRepresentingData C D F G0) : AdjExtMapComp C D G0 (adj_repr_mor C D F G0 alpha)
  ≔ d d' d'' g g' ↦
      inverse (C .wild .hom (G0 d) (G0 d''))
        (C .wild .comp (G0 d) (G0 d') (G0 d'') (adj_repr_mor C D F G0 alpha d' d'' g')
          (adj_repr_mor C D F G0 alpha d d' g))
        (adj_repr_mor C D F G0 alpha d d'' (D .comp d d' d'' g' g))
        (adj_repr_mor_unique C D F G0 alpha d d'' (D .comp d d' d'' g' g)
          (C .wild .comp (G0 d) (G0 d') (G0 d'') (adj_repr_mor C D F G0 alpha d' d'' g')
            (adj_repr_mor C D F G0 alpha d d' g))
          (c ↦ funext (D .hom (F .obj c) d) (_ ↦ C .wild .hom c (G0 d''))
             (k ↦ C .wild .comp c (G0 d) (G0 d'')
               (C .wild .comp (G0 d) (G0 d') (G0 d'') (adj_repr_mor C D F G0 alpha d' d'' g')
                 (adj_repr_mor C D F G0 alpha d d' g))
               (alpha d .fst .component c k))
             (k ↦ alpha d'' .fst .component c (D .comp (F .obj c) d d'' (D .comp d d' d'' g' g) k))
             (adj_repr_map_comp_natural C D F G0 alpha d d' d'' g g' c)))

{` The laws and naturality are propositions, since C has hom-sets. `}
def adj_ext_map_id_prop (C : Precat) (D : WildPrecat) (G0 : D .ob → C .wild .ob) (m : AdjExtMor C D G0)
  : isProp (AdjExtMapId C D G0 m)
  ≔ pi_prop (D .ob) (d ↦ Id (C .wild .hom (G0 d) (G0 d)) (m d d (D .idn d)) (C .wild .idn (G0 d)))
      (d ↦ C .homset (G0 d) (G0 d) (m d d (D .idn d)) (C .wild .idn (G0 d)))

def adj_ext_map_comp_prop (C : Precat) (D : WildPrecat) (G0 : D .ob → C .wild .ob) (m : AdjExtMor C D G0)
  : isProp (AdjExtMapComp C D G0 m)
  ≔ pi_prop (D .ob) (d ↦ (d' d'' : D .ob) (g : D .hom d d') (g' : D .hom d' d'')
        → Id (C .wild .hom (G0 d) (G0 d'')) (m d d'' (D .comp d d' d'' g' g))
            (C .wild .comp (G0 d) (G0 d') (G0 d'') (m d' d'' g') (m d d' g)))
      (d ↦ pi_prop (D .ob) (d' ↦ (d'' : D .ob) (g : D .hom d d') (g' : D .hom d' d'')
          → Id (C .wild .hom (G0 d) (G0 d'')) (m d d'' (D .comp d d' d'' g' g))
              (C .wild .comp (G0 d) (G0 d') (G0 d'') (m d' d'' g') (m d d' g)))
        (d' ↦ pi_prop (D .ob) (d'' ↦ (g : D .hom d d') (g' : D .hom d' d'')
            → Id (C .wild .hom (G0 d) (G0 d'')) (m d d'' (D .comp d d' d'' g' g))
                (C .wild .comp (G0 d) (G0 d') (G0 d'') (m d' d'' g') (m d d' g)))
          (d'' ↦ pi_prop (D .hom d d') (g ↦ (g' : D .hom d' d'')
              → Id (C .wild .hom (G0 d) (G0 d'')) (m d d'' (D .comp d d' d'' g' g))
                  (C .wild .comp (G0 d) (G0 d') (G0 d'') (m d' d'' g') (m d d' g)))
            (g ↦ pi_prop (D .hom d' d'') (g' ↦ Id (C .wild .hom (G0 d) (G0 d'')) (m d d'' (D .comp d d' d'' g' g))
                  (C .wild .comp (G0 d) (G0 d') (G0 d'') (m d' d'' g') (m d d' g)))
              (g' ↦ C .homset (G0 d) (G0 d'') (m d d'' (D .comp d d' d'' g' g))
                  (C .wild .comp (G0 d) (G0 d') (G0 d'') (m d' d'' g') (m d d' g)))))))

def adj_ext_natural_prop (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D) (G0 : D .ob → C .wild .ob)
  (alpha : AdjRepresentingData C D F G0) (m : AdjExtMor C D G0) : isProp (AdjExtNatural C D F G0 alpha m)
  ≔ pi_prop (C .wild .ob) (c ↦ (d d' : D .ob) (g : D .hom d d')
        → Id (D .hom (F .obj c) d → C .wild .hom c (G0 d'))
            (k ↦ C .wild .comp c (G0 d) (G0 d') (m d d' g) (alpha d .fst .component c k))
            (k ↦ alpha d' .fst .component c (D .comp (F .obj c) d d' g k)))
      (c ↦ pi_prop (D .ob) (d ↦ (d' : D .ob) (g : D .hom d d')
          → Id (D .hom (F .obj c) d → C .wild .hom c (G0 d'))
              (k ↦ C .wild .comp c (G0 d) (G0 d') (m d d' g) (alpha d .fst .component c k))
              (k ↦ alpha d' .fst .component c (D .comp (F .obj c) d d' g k)))
        (d ↦ pi_prop (D .ob) (d' ↦ (g : D .hom d d')
            → Id (D .hom (F .obj c) d → C .wild .hom c (G0 d'))
                (k ↦ C .wild .comp c (G0 d) (G0 d') (m d d' g) (alpha d .fst .component c k))
                (k ↦ alpha d' .fst .component c (D .comp (F .obj c) d d' g k)))
          (d' ↦ pi_prop (D .hom d d') (g ↦ Id (D .hom (F .obj c) d → C .wild .hom c (G0 d'))
                (k ↦ C .wild .comp c (G0 d) (G0 d') (m d d' g) (alpha d .fst .component c k))
                (k ↦ alpha d' .fst .component c (D .comp (F .obj c) d d' g k)))
            (g ↦ pi_set (D .hom (F .obj c) d) (_ ↦ C .wild .hom c (G0 d')) (_ ↦ C .homset c (G0 d'))
                (k ↦ C .wild .comp c (G0 d) (G0 d') (m d d' g) (alpha d .fst .component c k))
                (k ↦ alpha d' .fst .component c (D .comp (F .obj c) d d' g k))))))

def adj_ext_rest_prop (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D) (G0 : D .ob → C .wild .ob)
  (alpha : AdjRepresentingData C D F G0) (m : AdjExtMor C D G0)
  : isProp (Product (AdjExtMapId C D G0 m) (Product (AdjExtMapComp C D G0 m) (AdjExtNatural C D F G0 alpha m)))
  ≔ product_prop (AdjExtMapId C D G0 m) (Product (AdjExtMapComp C D G0 m) (AdjExtNatural C D F G0 alpha m))
      (adj_ext_map_id_prop C D G0 m)
      (product_prop (AdjExtMapComp C D G0 m) (AdjExtNatural C D F G0 alpha m)
        (adj_ext_map_comp_prop C D G0 m) (adj_ext_natural_prop C D F G0 alpha m))

def adj_repr_extension (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D) (G0 : D .ob → C .wild .ob)
  (alpha : AdjRepresentingData C D F G0) : AdjunctionExtension C D F G0 alpha
  ≔ (adj_repr_mor C D F G0 alpha,
     (adj_repr_map_id C D F G0 alpha, (adj_repr_map_comp C D F G0 alpha, adj_repr_mor_natural C D F G0 alpha)))

{` lem:adj-via-repr: the extension exists and is unique (the type of
   extensions is contractible). `}
def adjunction_via_representability (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D)
  (G0 : D .ob → C .wild .ob) (alpha : AdjRepresentingData C D F G0)
  : isContr (AdjunctionExtension C D F G0 alpha)
  ≔ (adj_repr_extension C D F G0 alpha,
     E ↦ equiv_inverse_map (Id (AdjunctionExtension C D F G0 alpha) E (adj_repr_extension C D F G0 alpha))
           (Id (AdjExtMor C D G0) (E .fst) (adj_repr_mor C D F G0 alpha))
           (subtype_path_equiv (AdjExtMor C D G0)
             (m ↦ Product (AdjExtMapId C D G0 m) (Product (AdjExtMapComp C D G0 m) (AdjExtNatural C D F G0 alpha m)))
             (adj_ext_rest_prop C D F G0 alpha) E (adj_repr_extension C D F G0 alpha))
           (funext3 (D .ob) (_ ↦ D .ob) (d d' ↦ D .hom d d') (d d' _ ↦ C .wild .hom (G0 d) (G0 d'))
              (E .fst) (adj_repr_mor C D F G0 alpha)
              (d d' g ↦ adj_repr_mor_unique C D F G0 alpha d d' g (E .fst d d' g)
                 (c ↦ E .snd .snd .snd c d d' g))))

{` Litmus: the resulting right adjoint has object part G0 and
   transposition α, on the nose. `}
def adjunction_via_representability_objects (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D)
  (G0 : D .ob → C .wild .ob) (alpha : AdjRepresentingData C D F G0) (d : D .ob)
  : Id (C .wild .ob)
      (adjunction_extension_right_adjoint C D F G0 alpha (adjunction_via_representability C D F G0 alpha .center)
        .right .obj d)
      (G0 d)
  ≔ refl (G0 d)

{` cor:adj-unique. A right adjoint is the same as G0 with representing
   isomorphisms plus an extension; the extensions are contractible, and
   for each d the pairs (G0 d, α_d) form a representation of the presheaf
   Hom_D(F -, d), which is unique when C is a category. `}
def right_adjoint_data_split_equiv (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D)
  : Equiv (RightAdjointData (C .wild) D F)
      (Σ (D .ob → C .wild .ob) (G0 ↦ Σ (AdjRepresentingData C D F G0) (AdjunctionExtension C D F G0)))
  ≔ quasi_inverse_equiv (RightAdjointData (C .wild) D F)
      (Σ (D .ob → C .wild .ob) (G0 ↦ Σ (AdjRepresentingData C D F G0) (AdjunctionExtension C D F G0)))
      (R ↦ (R .right .obj,
            (d ↦ ((component ≔ c ↦ R .transpose c d, natural ≔ c c' f ↦ R .natural_left c c' f d),
                  c ↦ R .transpose_iso c d),
             (R .right .mor, (R .right .map_id, (R .right .map_comp, R .natural_right))))))
      (t ↦ adjunction_extension_right_adjoint C D F (t .fst) (t .snd .fst) (t .snd .snd))
      (R ↦ refl R) (t ↦ refl t)

def right_adjoint_data_representations_equiv (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D)
  : Equiv (RightAdjointData (C .wild) D F)
      ((d : D .ob) → Σ (C .wild .ob) (x ↦ NatIso (OppositeWild (C .wild)) TypeWild
        (left_adjoint_hom_functor (C .wild) D F d) (contravariant_representable (C .wild) x)))
  ≔ compose_equiv (RightAdjointData (C .wild) D F)
      (Σ (D .ob → C .wild .ob) (G0 ↦ Σ (AdjRepresentingData C D F G0) (AdjunctionExtension C D F G0)))
      ((d : D .ob) → Σ (C .wild .ob) (x ↦ NatIso (OppositeWild (C .wild)) TypeWild
        (left_adjoint_hom_functor (C .wild) D F d) (contravariant_representable (C .wild) x)))
      (right_adjoint_data_split_equiv C D F)
      (compose_equiv
        (Σ (D .ob → C .wild .ob) (G0 ↦ Σ (AdjRepresentingData C D F G0) (AdjunctionExtension C D F G0)))
        (Σ (D .ob → C .wild .ob) (AdjRepresentingData C D F))
        ((d : D .ob) → Σ (C .wild .ob) (x ↦ NatIso (OppositeWild (C .wild)) TypeWild
          (left_adjoint_hom_functor (C .wild) D F d) (contravariant_representable (C .wild) x)))
        (family_equiv (D .ob → C .wild .ob)
          (G0 ↦ Σ (AdjRepresentingData C D F G0) (AdjunctionExtension C D F G0)) (AdjRepresentingData C D F)
          (G0 ↦ contractible_fiber_projection (AdjRepresentingData C D F G0) (AdjunctionExtension C D F G0)
            (adjunction_via_representability C D F G0)))
        (quasi_inverse_equiv (Σ (D .ob → C .wild .ob) (AdjRepresentingData C D F))
          ((d : D .ob) → Σ (C .wild .ob) (x ↦ NatIso (OppositeWild (C .wild)) TypeWild
            (left_adjoint_hom_functor (C .wild) D F d) (contravariant_representable (C .wild) x)))
          (t ↦ d ↦ (t .fst d, t .snd d))
          (s ↦ (d ↦ s d .fst, d ↦ s d .snd))
          (t ↦ refl t) (s ↦ refl s)))

{` Isomorphisms can be inverted, and this is an equivalence. `}
def cat_iso_inverse_equiv (C : WildPrecat) (a b : C .ob) : Equiv (CatIso C a b) (CatIso C b a)
  ≔ quasi_inverse_equiv (CatIso C a b) (CatIso C b a) (cat_iso_inverse C a b) (cat_iso_inverse C b a)
      (e ↦ cat_iso_path C a b (cat_iso_inverse C b a (cat_iso_inverse C a b e)) e (refl (e .fst)))
      (e ↦ cat_iso_path C b a (cat_iso_inverse C a b (cat_iso_inverse C b a e)) e (refl (e .fst)))

{` Hom_D(F -, d) as a presheaf, when its values are sets. `}
def left_adjoint_hom_presheaf (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D) (d : D .ob)
  (hs : (c : C .wild .ob) → isSet (D .hom (F .obj c) d)) : PresheafCategory C .wild .ob
  ≔ (obj ≔ c ↦ (D .hom (F .obj c) d, hs c),
     mor ≔ left_adjoint_hom_functor (C .wild) D F d .mor,
     map_id ≔ left_adjoint_hom_functor (C .wild) D F d .map_id,
     map_comp ≔ left_adjoint_hom_functor (C .wild) D F d .map_comp)

def left_adjoint_hom_nat_iso_equiv (C : Precat) (D : WildPrecat) (F : WildFunctor (C .wild) D) (d : D .ob)
  (hs : (c : C .wild .ob) → isSet (D .hom (F .obj c) d)) (x : C .wild .ob)
  : Equiv (NatIso (OppositeWild (C .wild)) TypeWild (left_adjoint_hom_functor (C .wild) D F d)
        (contravariant_representable (C .wild) x))
      (NatIso (OppositeWild (C .wild)) SetWild (left_adjoint_hom_presheaf C D F d hs) (representable_presheaf C x))
  ≔ quasi_inverse_equiv
      (NatIso (OppositeWild (C .wild)) TypeWild (left_adjoint_hom_functor (C .wild) D F d)
        (contravariant_representable (C .wild) x))
      (NatIso (OppositeWild (C .wild)) SetWild (left_adjoint_hom_presheaf C D F d hs) (representable_presheaf C x))
      (s ↦ ((component ≔ s .fst .component, natural ≔ s .fst .natural), s .snd))
      (s ↦ ((component ≔ s .fst .component, natural ≔ s .fst .natural), s .snd))
      (s ↦ refl s) (s ↦ refl s)

{` For a category C and a presheaf of sets, representing pairs (x, α)
   with α : Hom_D(F -, d) ≅ yo(x) form a proposition (cor:repr-prop). `}
def left_adjoint_representations_prop (C : Category) (D : WildPrecat) (F : WildFunctor (C .wild) D) (d : D .ob)
  (hs : (c : C .wild .ob) → isSet (D .hom (F .obj c) d))
  : isProp (Σ (C .wild .ob) (x ↦ NatIso (OppositeWild (C .wild)) TypeWild
      (left_adjoint_hom_functor (C .wild) D F d) (contravariant_representable (C .wild) x)))
  ≔ let C' ≔ category_precat C in
    let P ≔ PresheafCategory C' in
    let H ≔ left_adjoint_hom_presheaf C' D F d hs in
    let yo ≔ yoneda_functor C' in
    prop_from_equiv
      (Σ (C .wild .ob) (x ↦ NatIso (OppositeWild (C .wild)) TypeWild
        (left_adjoint_hom_functor (C .wild) D F d) (contravariant_representable (C .wild) x)))
      (IsRepresentable C' H)
      (compose_equiv
        (Σ (C .wild .ob) (x ↦ NatIso (OppositeWild (C .wild)) TypeWild
          (left_adjoint_hom_functor (C .wild) D F d) (contravariant_representable (C .wild) x)))
        (Σ (C .wild .ob) (x ↦ CatIso (P .wild) H (yo .obj x)))
        (IsRepresentable C' H)
        (family_equiv (C .wild .ob)
          (x ↦ NatIso (OppositeWild (C .wild)) TypeWild
            (left_adjoint_hom_functor (C .wild) D F d) (contravariant_representable (C .wild) x))
          (x ↦ CatIso (P .wild) H (yo .obj x))
          (x ↦ compose_equiv
            (NatIso (OppositeWild (C .wild)) TypeWild
              (left_adjoint_hom_functor (C .wild) D F d) (contravariant_representable (C .wild) x))
            (NatIso (OppositeWild (C .wild)) SetWild H (yo .obj x))
            (CatIso (P .wild) H (yo .obj x))
            (left_adjoint_hom_nat_iso_equiv C' D F d hs x)
            (canonical_inverse_equiv (CatIso (P .wild) H (yo .obj x)) (NatIso (OppositeWild (C .wild)) SetWild H (yo .obj x))
              (functor_cat_iso_equiv (OppositeWild (C .wild)) (category_precat SetCat) H (yo .obj x)))))
        (family_equiv (C .wild .ob) (x ↦ CatIso (P .wild) H (yo .obj x)) (x ↦ CatIso (P .wild) (yo .obj x) H)
          (x ↦ cat_iso_inverse_equiv (P .wild) H (yo .obj x))))
      (representability_prop C H)

{` If a right adjoint exists, the hom-types Hom_D(F c, d) are sets. `}
def right_adjoint_hom_sets (C : Category) (D : WildPrecat) (F : WildFunctor (C .wild) D)
  (R : RightAdjointData (C .wild) D F) (d : D .ob) (c : C .wild .ob) : isSet (D .hom (F .obj c) d)
  ≔ hlevel_two_to_set (D .hom (F .obj c) d)
      (hlevel_equiv (suc. (suc. zero.)) (C .wild .hom c (R .right .obj d)) (D .hom (F .obj c) d)
        (canonical_inverse_equiv (D .hom (F .obj c) d) (C .wild .hom c (R .right .obj d))
          (adjunction_transpose_equiv (C .wild) D F R c d))
        (set_to_hlevel_two (C .wild .hom c (R .right .obj d)) (C .homset c (R .right .obj d))))

{` cor:adj-unique: for a functor F defined on a category C (D may be
   wild), the data of a right adjoint F ⊣ G is a proposition. `}
def right_adjoint_data_prop (C : Category) (D : WildPrecat) (F : WildFunctor (C .wild) D)
  : isProp (RightAdjointData (C .wild) D F)
  ≔ R0 ↦ prop_from_equiv (RightAdjointData (C .wild) D F)
      ((d : D .ob) → Σ (C .wild .ob) (x ↦ NatIso (OppositeWild (C .wild)) TypeWild
        (left_adjoint_hom_functor (C .wild) D F d) (contravariant_representable (C .wild) x)))
      (right_adjoint_data_representations_equiv (category_precat C) D F)
      (pi_prop (D .ob) (d ↦ Σ (C .wild .ob) (x ↦ NatIso (OppositeWild (C .wild)) TypeWild
          (left_adjoint_hom_functor (C .wild) D F d) (contravariant_representable (C .wild) x)))
        (d ↦ left_adjoint_representations_prop C D F d (right_adjoint_hom_sets C D F R0 d)))
      R0
