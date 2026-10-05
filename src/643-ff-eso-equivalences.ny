export "642-equivalence-ff-split-eso-equiv"

{` Chapter 6, section 6.7, part 4: lem:ff-eso, the equivalence of split
   essential surjectivity and essential surjectivity for fully faithful
   functors out of a category, lem:cat-equiv-is-prop, and
   thm:ff-eso-equiv. The codomain may be a wild precategory throughout. `}

{` Transport of F(c) ≅ d along p : c = c' precomposes with the inverse of
   F(idtoiso p): (p_* h) ∘ F(idtoiso p) = h. `}
def ff_iso_fiber_transport_base (C D : WildPrecat) (F : WildFunctor C D) (d : D .ob) (c : C .ob)
  (h : CatIso D (F .obj c) d)
  : Id (D .hom (F .obj c) d)
      (D .comp (F .obj c) (F .obj c) d
        (transport (C .ob) (x ↦ CatIso D (F .obj x) d) c c (refl c) h .fst)
        (F .mor c c (cat_idtoiso C c c (refl c) .fst)))
      (h .fst)
  ≔ let Fc ≔ F .obj c in
    let t ≔ transport (C .ob) (x ↦ CatIso D (F .obj x) d) c c (refl c) h in
    calc
      D .comp Fc Fc d (t .fst) (F .mor c c (cat_idtoiso C c c (refl c) .fst))
      = D .comp Fc Fc d (h .fst) (F .mor c c (cat_idtoiso C c c (refl c) .fst))
        by cat_whisker_right D Fc Fc d (t .fst) (h .fst) (F .mor c c (cat_idtoiso C c c (refl c) .fst))
             (transport_refl (C .ob) (x ↦ CatIso D (F .obj x) d) c h .fst)
      = D .comp Fc Fc d (h .fst) (F .mor c c (C .idn c))
        by cat_whisker_left D Fc Fc d (h .fst) (F .mor c c (cat_idtoiso C c c (refl c) .fst)) (F .mor c c (C .idn c))
             (refl (F .mor c c)
               (inverse (CatIso C c c) (cat_identity_iso C c) (cat_idtoiso C c c (refl c)) (cat_idtoiso_refl C c) .fst))
      = D .comp Fc Fc d (h .fst) (D .idn Fc)
        by cat_whisker_left D Fc Fc d (h .fst) (F .mor c c (C .idn c)) (D .idn Fc) (F .map_id c)
      = h .fst by D .ru Fc d (h .fst) ∎

def ff_iso_fiber_transport (C D : WildPrecat) (F : WildFunctor C D) (d : D .ob) (c c' : C .ob)
  (p : Id (C .ob) c c') (h : CatIso D (F .obj c) d)
  : Id (D .hom (F .obj c) d)
      (D .comp (F .obj c) (F .obj c') d
        (transport (C .ob) (x ↦ CatIso D (F .obj x) d) c c' p h .fst)
        (F .mor c c' (cat_idtoiso C c c' p .fst)))
      (h .fst)
  ≔ J (C .ob) c (c' p ↦ Id (D .hom (F .obj c) d)
        (D .comp (F .obj c) (F .obj c') d
          (transport (C .ob) (x ↦ CatIso D (F .obj x) d) c c' p h .fst)
          (F .mor c c' (cat_idtoiso C c c' p .fst)))
        (h .fst))
      (ff_iso_fiber_transport_base C D F d c h) c' p

{` lem:ff-eso. If F is fully faithful and C is a category, then for any d
   the type Σ_c F(c) ≅ d is a proposition. `}
def ff_iso_fiber_path (C : Category) (D : WildPrecat) (F : WildFunctor (C .wild) D)
  (hF : (a b : C .wild .ob) → isEquiv (C .wild .hom a b) (D .hom (F .obj a) (F .obj b)) (F .mor a b))
  (d : D .ob) (u v : Σ (C .wild .ob) (c ↦ CatIso D (F .obj c) d))
  : Id (Σ (C .wild .ob) (c ↦ CatIso D (F .obj c) d)) u v
  ≔ let W ≔ C .wild in
    let c ≔ u .fst in
    let c' ≔ v .fst in
    let h ≔ u .snd in
    let h' ≔ v .snd in
    let Fc ≔ F .obj c in
    let Fc' ≔ F .obj c' in
    let hinv ≔ cat_iso_inverse D Fc' d h' in
    let m ≔ D .comp Fc d Fc' (hinv .fst) (h .fst) in
    let f ≔ ff_mor_inverse W D F hF c c' m in
    let Ff_is_m ≔ ff_mor_inverse_counit W D F hF c c' m in
    let Ff_iso : CatIsIso D Fc Fc' (F .mor c c' f)
      ≔ cat_is_iso_transport D Fc Fc' m (F .mor c c' f) (inverse (D .hom Fc Fc') (F .mor c c' f) m Ff_is_m)
          (cat_iso_compose D Fc d Fc' hinv h .snd) in
    let fi : CatIso W c c' ≔ (f, mor_equiv_functor_reflects_iso W D F hF c c' f Ff_iso) in
    let p ≔ cat_isotoid W (C .univalent) c c' fi in
    let B ≔ (x ↦ CatIso D (F .obj x) d) : W .ob → Type in
    let t ≔ transport (W .ob) B c c' p h in
    let Fid ≔ F .mor c c' (cat_idtoiso W c c' p .fst) in
    let arrows : Id (D .hom Fc' d) (t .fst) (h' .fst)
      ≔ equivalence_injective (D .hom Fc' d) (D .hom Fc d)
          (cat_precompose_equiv D Fc Fc' (F .mor c c' f) Ff_iso d) (t .fst) (h' .fst)
          (calc
            D .comp Fc Fc' d (t .fst) (F .mor c c' f)
            = D .comp Fc Fc' d (t .fst) Fid
              by cat_whisker_left D Fc Fc' d (t .fst) (F .mor c c' f) Fid
                   (refl (F .mor c c')
                     (inverse (CatIso W c c') (cat_idtoiso W c c' p) fi
                       (cat_idtoiso_isotoid W (C .univalent) c c' fi) .fst))
            = h .fst by ff_iso_fiber_transport W D F d c c' p h
            = D .comp Fc d d (D .idn d) (h .fst)
              by inverse (D .hom Fc d) (D .comp Fc d d (D .idn d) (h .fst)) (h .fst) (D .lu Fc d (h .fst))
            = D .comp Fc d d (D .comp d Fc' d (h' .fst) (hinv .fst)) (h .fst)
              by cat_whisker_right D Fc d d (D .idn d) (D .comp d Fc' d (h' .fst) (hinv .fst)) (h .fst)
                   (inverse (D .hom d d) (D .comp d Fc' d (h' .fst) (hinv .fst)) (D .idn d) (h' .snd .fst .snd))
            = D .comp Fc Fc' d (h' .fst) m
              by inverse (D .hom Fc d) (D .comp Fc Fc' d (h' .fst) m)
                   (D .comp Fc d d (D .comp d Fc' d (h' .fst) (hinv .fst)) (h .fst))
                   (D .assoc Fc d Fc' d (h .fst) (hinv .fst) (h' .fst))
            = D .comp Fc Fc' d (h' .fst) (F .mor c c' f)
              by cat_whisker_left D Fc Fc' d (h' .fst) m (F .mor c c' f)
                   (inverse (D .hom Fc Fc') (F .mor c c' f) m Ff_is_m) ∎) in
    (p, pathover_of_eq (W .ob) B c c' p h h' (cat_iso_path D Fc' d t h' arrows))

def ff_iso_fiber_prop (C : Category) (D : WildPrecat) (F : WildFunctor (C .wild) D)
  (h : IsFullyFaithful (C .wild) D F) (d : D .ob)
  : isProp (Σ (C .wild .ob) (c ↦ CatIso D (F .obj c) d))
  ≔ ff_iso_fiber_path C D F (ff_mor_is_equiv (C .wild) D F h) d

{` "if C is category, then split essential surjectivity is equivalent to
   essential surjectivity" (for fully faithful F). `}
def split_eso_prop (C : Category) (D : WildPrecat) (F : WildFunctor (C .wild) D) (h : IsFullyFaithful (C .wild) D F)
  : isProp (IsSplitEso (C .wild) D F)
  ≔ pi_prop (D .ob) (d ↦ Σ (C .wild .ob) (c ↦ CatIso D (F .obj c) d)) (ff_iso_fiber_prop C D F h)

def split_eso_from_eso (C : Category) (D : WildPrecat) (F : WildFunctor (C .wild) D) (h : IsFullyFaithful (C .wild) D F)
  (e : IsEso (C .wild) D F) : IsSplitEso (C .wild) D F
  ≔ d ↦ mere_rec (Σ (C .wild .ob) (c ↦ CatIso D (F .obj c) d)) (Σ (C .wild .ob) (c ↦ CatIso D (F .obj c) d))
      (ff_iso_fiber_prop C D F h d) (x ↦ x) (e d)

def eso_from_split_eso (C D : WildPrecat) (F : WildFunctor C D) (s : IsSplitEso C D F) : IsEso C D F
  ≔ d ↦ mere (Σ (C .ob) (c ↦ CatIso D (F .obj c) d)) (s d)

def split_eso_eso_equiv (C : Category) (D : WildPrecat) (F : WildFunctor (C .wild) D) (h : IsFullyFaithful (C .wild) D F)
  : BookEquiv (IsSplitEso (C .wild) D F) (IsEso (C .wild) D F)
  ≔ book_equivalence (IsSplitEso (C .wild) D F) (IsEso (C .wild) D F)
      (iff_equiv (IsSplitEso (C .wild) D F) (IsEso (C .wild) D F) (split_eso_prop C D F h) (is_eso_prop (C .wild) D F)
        (eso_from_split_eso (C .wild) D F) (split_eso_from_eso C D F h))

{` lem:cat-equiv-is-prop. If C is a category, being an equivalence is a
   proposition for F : C → D (D any wild precategory). Proof: by
   lem:equiv-precat-is-ff-split-eso it is equivalent to being fully
   faithful and split essentially surjective, which is a proposition by
   lem:ff-eso. (The book's route through cor:adj-unique is
   is_cat_equivalence_prop_via_adj_unique, if present.) `}
def ff_split_eso_prop (C : Category) (D : WildPrecat) (F : WildFunctor (C .wild) D)
  : isProp (Product (IsFullyFaithful (C .wild) D F) (IsSplitEso (C .wild) D F))
  ≔ u v ↦ (is_fully_faithful_prop (C .wild) D F (u .fst) (v .fst), split_eso_prop C D F (u .fst) (u .snd) (v .snd))

def is_cat_equivalence_prop (C : Category) (D : WildPrecat) (F : WildFunctor (C .wild) D)
  : isProp (IsCatEquivalence (C .wild) D F)
  ≔ E E' ↦
      let e ≔ native_equivalence (IsCatEquivalence (C .wild) D F) (Product (IsFullyFaithful (C .wild) D F) (IsSplitEso (C .wild) D F))
        (wild_cat_equivalence_ff_split_eso_equiv (C .wild) D F (C .homset)) in
      equivalence_injective (IsCatEquivalence (C .wild) D F) (Product (IsFullyFaithful (C .wild) D F) (IsSplitEso (C .wild) D F))
        e E E' (ff_split_eso_prop C D F (e .map E) (e .map E'))

{` thm:ff-eso-equiv, existence: a fully faithful and essentially
   surjective functor out of a category is an equivalence. `}
def wild_ff_eso_is_cat_equivalence (C : Category) (D : WildPrecat) (F : WildFunctor (C .wild) D)
  (h : IsFullyFaithful (C .wild) D F) (e : IsEso (C .wild) D F) : IsCatEquivalence (C .wild) D F
  ≔ ff_split_eso_is_cat_equivalence (C .wild) D F h (split_eso_from_eso C D F h e)

def ff_eso_is_cat_equivalence (C : Category) (D : Precat) (F : WildFunctor (C .wild) (D .wild))
  (h : IsFullyFaithful (C .wild) (D .wild) F) (e : IsEso (C .wild) (D .wild) F) : IsCatEquivalence (C .wild) (D .wild) F
  ≔ wild_ff_eso_is_cat_equivalence C (D .wild) F h e

{` Conversely every equivalence is fully faithful and essentially
   surjective (for any wild precategories). `}
def cat_equivalence_weak_equivalence (C D : WildPrecat) (F : WildFunctor C D) (E : IsCatEquivalence C D F)
  : IsWeakEquivalence C D F
  ≔ (wild_cat_equivalence_ff C D F E, eso_from_split_eso C D F (cat_equivalence_split_eso C D F E))

{` For C a category: being an equivalence is equivalent to being fully
   faithful and essentially surjective. `}
def cat_equivalence_weak_equivalence_equiv (C : Category) (D : WildPrecat) (F : WildFunctor (C .wild) D)
  : BookEquiv (IsCatEquivalence (C .wild) D F) (IsWeakEquivalence (C .wild) D F)
  ≔ book_equivalence (IsCatEquivalence (C .wild) D F) (IsWeakEquivalence (C .wild) D F)
      (iff_equiv (IsCatEquivalence (C .wild) D F) (IsWeakEquivalence (C .wild) D F)
        (is_cat_equivalence_prop C D F)
        (product_prop (IsFullyFaithful (C .wild) D F) (IsEso (C .wild) D F)
          (is_fully_faithful_prop (C .wild) D F) (is_eso_prop (C .wild) D F))
        (cat_equivalence_weak_equivalence (C .wild) D F)
        (x ↦ wild_ff_eso_is_cat_equivalence C D F (x .fst) (x .snd)))

{` thm:ff-eso-equiv: the projection (C ≃ D) → (C → D) is an injection
   (def:injection: proposition-valued fibers) ... `}
def cat_equivalence_projection (C D : WildPrecat) (e : CatEquivalence C D) : WildFunctor C D ≔ e .fst

def cat_equivalence_projection_fiber_equiv (C D : WildPrecat) (F : WildFunctor C D)
  : BookEquiv (BookFiber (CatEquivalence C D) (WildFunctor C D) (cat_equivalence_projection C D) F)
      (IsCatEquivalence C D F)
  ≔ book_projection_fiber_equiv (WildFunctor C D) (IsCatEquivalence C D) F

def cat_equivalence_projection_injective (C : Category) (D : WildPrecat)
  : IsEmbedding (CatEquivalence (C .wild) D) (WildFunctor (C .wild) D) (cat_equivalence_projection (C .wild) D)
  ≔ F ↦ hlevel_one_to_prop (BookFiber (CatEquivalence (C .wild) D) (WildFunctor (C .wild) D)
        (cat_equivalence_projection (C .wild) D) F)
      (hlevel_equiv (suc. zero.) (IsCatEquivalence (C .wild) D F)
        (BookFiber (CatEquivalence (C .wild) D) (WildFunctor (C .wild) D) (cat_equivalence_projection (C .wild) D) F)
        (canonical_inverse_equiv (BookFiber (CatEquivalence (C .wild) D) (WildFunctor (C .wild) D)
            (cat_equivalence_projection (C .wild) D) F) (IsCatEquivalence (C .wild) D F)
          (native_equivalence (BookFiber (CatEquivalence (C .wild) D) (WildFunctor (C .wild) D)
              (cat_equivalence_projection (C .wild) D) F) (IsCatEquivalence (C .wild) D F)
            (cat_equivalence_projection_fiber_equiv (C .wild) D F)))
        (prop_to_hlevel_one (IsCatEquivalence (C .wild) D F) (is_cat_equivalence_prop C D F)))

{` ... with image given by the fully faithful and essentially surjective
   functors: F is (merely) in the image iff it is a weak equivalence. `}
def cat_equivalence_projection_image (C : Category) (D : WildPrecat) (F : WildFunctor (C .wild) D)
  : BookEquiv (Mere (BookFiber (CatEquivalence (C .wild) D) (WildFunctor (C .wild) D)
        (cat_equivalence_projection (C .wild) D) F))
      (IsWeakEquivalence (C .wild) D F)
  ≔ let Fib ≔ BookFiber (CatEquivalence (C .wild) D) (WildFunctor (C .wild) D) (cat_equivalence_projection (C .wild) D) F in
    let e1 ≔ native_equivalence Fib (IsCatEquivalence (C .wild) D F) (cat_equivalence_projection_fiber_equiv (C .wild) D F) in
    let e2 ≔ native_equivalence (IsCatEquivalence (C .wild) D F) (IsWeakEquivalence (C .wild) D F)
      (cat_equivalence_weak_equivalence_equiv C D F) in
    book_equivalence (Mere Fib) (IsWeakEquivalence (C .wild) D F)
      (iff_equiv (Mere Fib) (IsWeakEquivalence (C .wild) D F) (mere_isprop Fib)
        (product_prop (IsFullyFaithful (C .wild) D F) (IsEso (C .wild) D F)
          (is_fully_faithful_prop (C .wild) D F) (is_eso_prop (C .wild) D F))
        (mere_rec Fib (IsWeakEquivalence (C .wild) D F)
          (product_prop (IsFullyFaithful (C .wild) D F) (IsEso (C .wild) D F)
            (is_fully_faithful_prop (C .wild) D F) (is_eso_prop (C .wild) D F))
          (t ↦ e2 .map (e1 .map t)))
        (w ↦ mere Fib (equiv_inverse_map Fib (IsCatEquivalence (C .wild) D F) e1
          (equiv_inverse_map (IsCatEquivalence (C .wild) D F) (IsWeakEquivalence (C .wild) D F) e2 w))))

{` Litmus: the identity functor of a category is fully faithful and
   essentially surjective, and the theorem returns an equivalence whose
   right adjoint is the identity on objects. `}
def identity_weak_equivalence (C : WildPrecat) : IsWeakEquivalence C C (functor_identity C)
  ≔ (identity_cat_equivalence_ff C, eso_from_split_eso C C (functor_identity C) (identity_split_eso C))

def identity_ff_eso_right_adjoint_obj (C : Category) (c : C .wild .ob)
  : Id (C .wild .ob)
      (ff_eso_is_cat_equivalence C (category_precat C) (functor_identity (C .wild))
        (identity_weak_equivalence (C .wild) .fst) (identity_weak_equivalence (C .wild) .snd) .fst .right .obj c) c
  ≔ refl c

{` Two equivalence structures on the identity functor of a category agree. `}
def identity_cat_equivalence_unique (C : Category)
  : Id (IsCatEquivalence (C .wild) (C .wild) (functor_identity (C .wild)))
      (identity_cat_equivalence_from_nat_isos (C .wild)) (identity_is_cat_equivalence (C .wild))
  ≔ is_cat_equivalence_prop C (C .wild) (functor_identity (C .wild))
      (identity_cat_equivalence_from_nat_isos (C .wild)) (identity_is_cat_equivalence (C .wild))
