export "603-adjunctions-and-equivalences"

{` Chapter 6 (cats.tex), section 6.4: isomorphisms in functor
   precategories (xca:funext-nat-trans), full subcategory inclusions and
   constant functors used as litmus examples. `}

{` The inclusion of a full subcategory, acting as the identity on arrows. `}
def full_subcat_inclusion (C : WildPrecat) (P : Subtypes (C .ob)) : WildFunctor (FullSubcat C P) C
  ≔ (obj ≔ x ↦ x .fst,
     mor ≔ x y f ↦ f,
     map_id ≔ x ↦ refl (C .idn (x .fst)),
     map_comp ≔ x y z f g ↦ refl (C .comp (x .fst) (y .fst) (z .fst) g f))

{` The constant functor at an object d; its laws are the unit law at d. `}
def constant_functor (C D : WildPrecat) (d : D .ob) : WildFunctor C D
  ≔ (obj ≔ _ ↦ d,
     mor ≔ _ _ _ ↦ D .idn d,
     map_id ≔ _ ↦ refl (D .idn d),
     map_comp ≔ _ _ _ _ _ ↦ inverse (D .hom d d) (D .comp d d d (D .idn d) (D .idn d)) (D .idn d)
       (D .lu d d (D .idn d)))

{` The chosen inverse of a component of a natural transformation with
   invertible components: the right inverse g_a of α_a. By cat_iso_inverse
   it is also a left inverse. `}
def nat_iso_inverse_component (C D : WildPrecat) (F G : WildFunctor C D) (alpha : WildNatTrans C D F G)
  (i : IsNatIso C D F G alpha) (a : C .ob) : D .hom (G .obj a) (F .obj a)
  ≔ i a .fst .fst

def nat_iso_inverse_left (C D : WildPrecat) (F G : WildFunctor C D) (alpha : WildNatTrans C D F G)
  (i : IsNatIso C D F G alpha) (a : C .ob)
  : Id (D .hom (F .obj a) (F .obj a))
      (D .comp (F .obj a) (G .obj a) (F .obj a) (nat_iso_inverse_component C D F G alpha i a)
        (alpha .component a))
      (D .idn (F .obj a))
  ≔ cat_iso_inverse D (F .obj a) (G .obj a) (alpha .component a, i a) .snd .fst .snd

def nat_iso_inverse_right (C D : WildPrecat) (F G : WildFunctor C D) (alpha : WildNatTrans C D F G)
  (i : IsNatIso C D F G alpha) (a : C .ob)
  : Id (D .hom (G .obj a) (G .obj a))
      (D .comp (G .obj a) (F .obj a) (G .obj a) (alpha .component a)
        (nat_iso_inverse_component C D F G alpha i a))
      (D .idn (G .obj a))
  ≔ i a .fst .snd

{` The inverses of the components are again natural (in any wild
   precategory D): F f ∘ α_a⁻¹ = α_b⁻¹ ∘ G f. `}
def nat_iso_inverse_natural (C D : WildPrecat) (F G : WildFunctor C D) (alpha : WildNatTrans C D F G)
  (i : IsNatIso C D F G alpha) (a b : C .ob) (f : C .hom a b)
  : Id (D .hom (G .obj a) (F .obj b))
      (D .comp (G .obj a) (F .obj a) (F .obj b) (F .mor a b f) (nat_iso_inverse_component C D F G alpha i a))
      (D .comp (G .obj a) (G .obj b) (F .obj b) (nat_iso_inverse_component C D F G alpha i b) (G .mor a b f))
  ≔ let Fa ≔ F .obj a in let Fb ≔ F .obj b in let Ga ≔ G .obj a in let Gb ≔ G .obj b in
    let Ff ≔ F .mor a b f in let Gf ≔ G .mor a b f in
    let al ≔ alpha .component a in let bl ≔ alpha .component b in
    let ga ≔ nat_iso_inverse_component C D F G alpha i a in
    let gb ≔ nat_iso_inverse_component C D F G alpha i b in
    calc
      D .comp Ga Fa Fb Ff ga
      = D .comp Ga Fb Fb (D .idn Fb) (D .comp Ga Fa Fb Ff ga)
        by inverse (D .hom Ga Fb) (D .comp Ga Fb Fb (D .idn Fb) (D .comp Ga Fa Fb Ff ga))
             (D .comp Ga Fa Fb Ff ga) (D .lu Ga Fb (D .comp Ga Fa Fb Ff ga))
      = D .comp Ga Fb Fb (D .comp Fb Gb Fb gb bl) (D .comp Ga Fa Fb Ff ga)
        by cat_whisker_right D Ga Fb Fb (D .idn Fb) (D .comp Fb Gb Fb gb bl) (D .comp Ga Fa Fb Ff ga)
             (inverse (D .hom Fb Fb) (D .comp Fb Gb Fb gb bl) (D .idn Fb)
               (nat_iso_inverse_left C D F G alpha i b))
      = D .comp Ga Gb Fb gb (D .comp Ga Fb Gb bl (D .comp Ga Fa Fb Ff ga))
        by inverse (D .hom Ga Fb) (D .comp Ga Gb Fb gb (D .comp Ga Fb Gb bl (D .comp Ga Fa Fb Ff ga)))
             (D .comp Ga Fb Fb (D .comp Fb Gb Fb gb bl) (D .comp Ga Fa Fb Ff ga))
             (D .assoc Ga Fb Gb Fb (D .comp Ga Fa Fb Ff ga) bl gb)
      = D .comp Ga Gb Fb gb (D .comp Ga Fa Gb (D .comp Fa Fb Gb bl Ff) ga)
        by cat_whisker_left D Ga Gb Fb gb (D .comp Ga Fb Gb bl (D .comp Ga Fa Fb Ff ga))
             (D .comp Ga Fa Gb (D .comp Fa Fb Gb bl Ff) ga) (D .assoc Ga Fa Fb Gb ga Ff bl)
      = D .comp Ga Gb Fb gb (D .comp Ga Fa Gb (D .comp Fa Ga Gb Gf al) ga)
        by cat_whisker_left D Ga Gb Fb gb (D .comp Ga Fa Gb (D .comp Fa Fb Gb bl Ff) ga)
             (D .comp Ga Fa Gb (D .comp Fa Ga Gb Gf al) ga)
             (cat_whisker_right D Ga Fa Gb (D .comp Fa Fb Gb bl Ff) (D .comp Fa Ga Gb Gf al) ga
               (inverse (D .hom Fa Gb) (D .comp Fa Ga Gb Gf al) (D .comp Fa Fb Gb bl Ff) (alpha .natural a b f)))
      = D .comp Ga Gb Fb gb (D .comp Ga Ga Gb Gf (D .comp Ga Fa Ga al ga))
        by cat_whisker_left D Ga Gb Fb gb (D .comp Ga Fa Gb (D .comp Fa Ga Gb Gf al) ga)
             (D .comp Ga Ga Gb Gf (D .comp Ga Fa Ga al ga))
             (inverse (D .hom Ga Gb) (D .comp Ga Ga Gb Gf (D .comp Ga Fa Ga al ga))
               (D .comp Ga Fa Gb (D .comp Fa Ga Gb Gf al) ga) (D .assoc Ga Fa Ga Gb ga al Gf))
      = D .comp Ga Gb Fb gb (D .comp Ga Ga Gb Gf (D .idn Ga))
        by cat_whisker_left D Ga Gb Fb gb (D .comp Ga Ga Gb Gf (D .comp Ga Fa Ga al ga))
             (D .comp Ga Ga Gb Gf (D .idn Ga))
             (cat_whisker_left D Ga Ga Gb Gf (D .comp Ga Fa Ga al ga) (D .idn Ga)
               (nat_iso_inverse_right C D F G alpha i a))
      = D .comp Ga Gb Fb gb Gf
        by cat_whisker_left D Ga Gb Fb gb (D .comp Ga Ga Gb Gf (D .idn Ga)) Gf (D .ru Ga Gb Gf) ∎

def nat_iso_inverse (C D : WildPrecat) (F G : WildFunctor C D) (alpha : WildNatTrans C D F G)
  (i : IsNatIso C D F G alpha) : WildNatTrans C D G F
  ≔ (component ≔ nat_iso_inverse_component C D F G alpha i,
     natural ≔ nat_iso_inverse_natural C D F G alpha i)

{` xca:funext-nat-trans, "only if": an isomorphism in the functor
   precategory has invertible components (evaluate the two inverse laws
   at each object). `}
def functor_cat_iso_components (C : WildPrecat) (D : Precat) (F G : WildFunctor C (D .wild))
  (alpha : WildNatTrans C (D .wild) F G) (i : CatIsIso (FunctorWild C D) F G alpha)
  : IsNatIso C (D .wild) F G alpha
  ≔ a ↦ ((i .fst .fst .component a,
          refl ((t ↦ t .component a)
              : WildNatTrans C (D .wild) G G → D .wild .hom (G .obj a) (G .obj a)) (i .fst .snd)),
         (i .snd .fst .component a,
          refl ((t ↦ t .component a)
              : WildNatTrans C (D .wild) F F → D .wild .hom (F .obj a) (F .obj a)) (i .snd .snd)))

{` xca:funext-nat-trans, "if": componentwise inverses form an inverse in
   the functor precategory. `}
def functor_cat_components_iso (C : WildPrecat) (D : Precat) (F G : WildFunctor C (D .wild))
  (alpha : WildNatTrans C (D .wild) F G) (i : IsNatIso C (D .wild) F G alpha)
  : CatIsIso (FunctorWild C D) F G alpha
  ≔ let beta ≔ nat_iso_inverse C (D .wild) F G alpha i in
    ((beta,
      nat_trans_path_pointwise C (D .wild) (D .homset) G G
        (nat_trans_compose C (D .wild) G F G alpha beta) (nat_trans_identity C (D .wild) G)
        (nat_iso_inverse_right C (D .wild) F G alpha i)),
     (beta,
      nat_trans_path_pointwise C (D .wild) (D .homset) F F
        (nat_trans_compose C (D .wild) F G F beta alpha) (nat_trans_identity C (D .wild) F)
        (nat_iso_inverse_left C (D .wild) F G alpha i)))

def is_nat_iso_prop (C D : WildPrecat) (F G : WildFunctor C D) (alpha : WildNatTrans C D F G)
  : isProp (IsNatIso C D F G alpha)
  ≔ pi_prop (C .ob) (a ↦ CatIsIso D (F .obj a) (G .obj a) (alpha .component a))
      (a ↦ cat_is_iso_prop D (F .obj a) (G .obj a) (alpha .component a))

{` xca:funext-nat-trans: α is invertible in C → D iff each component is. `}
def nat_trans_invertible_iff_components (C : WildPrecat) (D : Precat) (F G : WildFunctor C (D .wild))
  (alpha : WildNatTrans C (D .wild) F G)
  : Product (CatIsIso (FunctorWild C D) F G alpha → IsNatIso C (D .wild) F G alpha)
      (IsNatIso C (D .wild) F G alpha → CatIsIso (FunctorWild C D) F G alpha)
  ≔ (functor_cat_iso_components C D F G alpha, functor_cat_components_iso C D F G alpha)

{` Both sides are propositions, so the two implications form an
   equivalence; summing over α identifies the isomorphisms F ≅ G of the
   functor precategory with the natural isomorphisms. `}
def functor_cat_is_iso_equiv (C : WildPrecat) (D : Precat) (F G : WildFunctor C (D .wild))
  (alpha : WildNatTrans C (D .wild) F G)
  : Equiv (CatIsIso (FunctorWild C D) F G alpha) (IsNatIso C (D .wild) F G alpha)
  ≔ iff_equiv (CatIsIso (FunctorWild C D) F G alpha) (IsNatIso C (D .wild) F G alpha)
      (cat_is_iso_prop (FunctorWild C D) F G alpha) (is_nat_iso_prop C (D .wild) F G alpha)
      (functor_cat_iso_components C D F G alpha) (functor_cat_components_iso C D F G alpha)

def functor_cat_iso_equiv (C : WildPrecat) (D : Precat) (F G : WildFunctor C (D .wild))
  : Equiv (CatIso (FunctorWild C D) F G) (NatIso C (D .wild) F G)
  ≔ family_equiv (WildNatTrans C (D .wild) F G) (CatIsIso (FunctorWild C D) F G) (IsNatIso C (D .wild) F G)
      (functor_cat_is_iso_equiv C D F G)

{` Litmus: the negation of Bool as a natural isomorphism between constant
   Set-valued functors on the path category of Bool; the inverse computed
   from the components evaluates to negation. `}
def set_precat : Precat ≔ category_precat SetCat

def bool_negation_nat_trans
  : WildNatTrans (PathWild Bool) SetWild (constant_functor (PathWild Bool) SetWild set_cat_bool)
      (constant_functor (PathWild Bool) SetWild set_cat_bool)
  ≔ (component ≔ _ ↦ bool_not,
     natural ≔ _ _ _ ↦ refl bool_not)

def bool_negation_functor_iso
  : CatIsIso (FunctorWild (PathWild Bool) set_precat) (constant_functor (PathWild Bool) SetWild set_cat_bool)
      (constant_functor (PathWild Bool) SetWild set_cat_bool) bool_negation_nat_trans
  ≔ functor_cat_components_iso (PathWild Bool) set_precat (constant_functor (PathWild Bool) SetWild set_cat_bool)
      (constant_functor (PathWild Bool) SetWild set_cat_bool) bool_negation_nat_trans
      (_ ↦ set_cat_negation_iso .snd)

def bool_negation_functor_iso_inverse_value
  : Id Bool (bool_negation_functor_iso .fst .fst .component true. true.) false.
  ≔ refl (false. : Bool)
