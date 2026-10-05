export "620-natural-isomorphisms"

{` Chapter 6 (cats.tex), xca:functor-cat-univalent: the functor
   precategory C → D is univalent when D is (HoTT book Thm 9.2.5). We show
   that for each functor F the type Σ G, F ≅ G is contractible. By
   xca:funext-nat-trans it is Σ G, (natural isomorphism F → G), which we
   reorganize as a family over (a : C) → Σ y, F(a) ≅ y (contractible by
   univalence of D, with center the identity isomorphisms); over that
   center the remaining data (arrows of G, functor laws, naturality
   squares with identity components) is contractible because D has
   hom-sets and the squares force G(f) = F(f). `}

{` A Σ-type over a contractible base whose fiber over the center is
   contractible is contractible. `}
def sigma_contractible_from_center (A : Type) (B : A → Type) (hA : isContr A) (hB : isContr (B (hA .center)))
  : isContr (Σ A B)
  ≔ sigma_contractible A B hA (a ↦
      transport A (x ↦ isContr (B x)) (hA .center) a (inverse A a (hA .center) (hA .contract a)) hB)

def FunctorIsoBase (C D : WildPrecat) (F : WildFunctor C D) : Type
  ≔ (a : C .ob) → Σ (D .ob) (y ↦ CatIso D (F .obj a) y)

def FunctorIsoMor (C D : WildPrecat) (F : WildFunctor C D) (P : FunctorIsoBase C D F) : Type
  ≔ (a b : C .ob) → C .hom a b → D .hom (P a .fst) (P b .fst)

def FunctorIsoSquares (C D : WildPrecat) (F : WildFunctor C D) (P : FunctorIsoBase C D F)
  (m : FunctorIsoMor C D F P) : Type
  ≔ (a b : C .ob) (f : C .hom a b)
    → Id (D .hom (F .obj a) (P b .fst))
        (D .comp (F .obj a) (P a .fst) (P b .fst) (m a b f) (P a .snd .fst))
        (D .comp (F .obj a) (F .obj b) (P b .fst) (P b .snd .fst) (F .mor a b f))

def FunctorIsoFiber (C D : WildPrecat) (F : WildFunctor C D) (P : FunctorIsoBase C D F) : Type
  ≔ Σ (FunctorIsoMor C D F P) (m ↦
      Product (FunctorLaws C D ((a ↦ P a .fst), m)) (FunctorIsoSquares C D F P m))

{` Σ G, NatIso F G, reorganized. Both round trips are reflexivity. `}
def functor_nat_iso_total_equiv (C D : WildPrecat) (F : WildFunctor C D)
  : Equiv (Σ (WildFunctor C D) (G ↦ NatIso C D F G)) (Σ (FunctorIsoBase C D F) (FunctorIsoFiber C D F))
  ≔ quasi_inverse_equiv (Σ (WildFunctor C D) (G ↦ NatIso C D F G))
      (Σ (FunctorIsoBase C D F) (FunctorIsoFiber C D F))
      (s ↦ (a ↦ (s .fst .obj a, (s .snd .fst .component a, s .snd .snd a)),
            (s .fst .mor, ((s .fst .map_id, s .fst .map_comp), s .snd .fst .natural))))
      (t ↦ ((obj ≔ a ↦ t .fst a .fst,
             mor ≔ t .snd .fst,
             map_id ≔ t .snd .snd .fst .fst,
             map_comp ≔ t .snd .snd .fst .snd),
            ((component ≔ a ↦ t .fst a .snd .fst,
              natural ≔ t .snd .snd .snd),
             a ↦ t .fst a .snd .snd)))
      (s ↦ refl s) (t ↦ refl t)

def functor_iso_base_center (C D : WildPrecat) (F : WildFunctor C D) : FunctorIsoBase C D F
  ≔ a ↦ (F .obj a, cat_identity_iso D (F .obj a))

def functor_iso_base_contractible (C D : WildPrecat) (F : WildFunctor C D) (u : IsUnivalentCat D)
  : isContr (FunctorIsoBase C D F)
  ≔ let h ≔ pi_contractible (C .ob) (a ↦ Σ (D .ob) (y ↦ CatIso D (F .obj a) y))
        (a ↦ cat_univalent_iso_total_contractible D u (F .obj a)) in
    (functor_iso_base_center C D F,
     x ↦ contractible_prop (FunctorIsoBase C D F) h x (functor_iso_base_center C D F))

def functor_iso_squares_prop (C D : WildPrecat) (hs : HasHomSets D) (F : WildFunctor C D)
  (P : FunctorIsoBase C D F) (m : FunctorIsoMor C D F P) : isProp (FunctorIsoSquares C D F P m)
  ≔ pi_prop (C .ob) (a ↦ (b : C .ob) (f : C .hom a b)
        → Id (D .hom (F .obj a) (P b .fst))
            (D .comp (F .obj a) (P a .fst) (P b .fst) (m a b f) (P a .snd .fst))
            (D .comp (F .obj a) (F .obj b) (P b .fst) (P b .snd .fst) (F .mor a b f)))
      (a ↦ pi_prop (C .ob) (b ↦ (f : C .hom a b)
          → Id (D .hom (F .obj a) (P b .fst))
              (D .comp (F .obj a) (P a .fst) (P b .fst) (m a b f) (P a .snd .fst))
              (D .comp (F .obj a) (F .obj b) (P b .fst) (P b .snd .fst) (F .mor a b f)))
        (b ↦ pi_prop (C .hom a b) (f ↦ Id (D .hom (F .obj a) (P b .fst))
              (D .comp (F .obj a) (P a .fst) (P b .fst) (m a b f) (P a .snd .fst))
              (D .comp (F .obj a) (F .obj b) (P b .fst) (P b .snd .fst) (F .mor a b f)))
          (f ↦ hs (F .obj a) (P b .fst)
              (D .comp (F .obj a) (P a .fst) (P b .fst) (m a b f) (P a .snd .fst))
              (D .comp (F .obj a) (F .obj b) (P b .fst) (P b .snd .fst) (F .mor a b f)))))

def functor_iso_fiber_props (C D : WildPrecat) (hs : HasHomSets D) (F : WildFunctor C D)
  (P : FunctorIsoBase C D F) (m : FunctorIsoMor C D F P)
  : isProp (Product (FunctorLaws C D ((a ↦ P a .fst), m)) (FunctorIsoSquares C D F P m))
  ≔ product_prop (FunctorLaws C D ((a ↦ P a .fst), m)) (FunctorIsoSquares C D F P m)
      (functor_laws_prop C D hs ((a ↦ P a .fst), m)) (functor_iso_squares_prop C D hs F P m)

{` Over the identity isomorphisms, a naturality square
   G(f) ∘ id = id ∘ F(f) forces G(f) = F(f). `}
def functor_iso_fiber_center_arrow (C D : WildPrecat) (F : WildFunctor C D)
  (t : FunctorIsoFiber C D F (functor_iso_base_center C D F)) (a b : C .ob) (f : C .hom a b)
  : Id (D .hom (F .obj a) (F .obj b)) (t .fst a b f) (F .mor a b f)
  ≔ calc
      t .fst a b f
      = D .comp (F .obj a) (F .obj a) (F .obj b) (t .fst a b f) (D .idn (F .obj a))
        by inverse (D .hom (F .obj a) (F .obj b))
             (D .comp (F .obj a) (F .obj a) (F .obj b) (t .fst a b f) (D .idn (F .obj a))) (t .fst a b f)
             (D .ru (F .obj a) (F .obj b) (t .fst a b f))
      = D .comp (F .obj a) (F .obj b) (F .obj b) (D .idn (F .obj b)) (F .mor a b f)
        by t .snd .snd a b f
      = F .mor a b f
        by D .lu (F .obj a) (F .obj b) (F .mor a b f) ∎

def functor_iso_fiber_contractible (C D : WildPrecat) (hs : HasHomSets D) (F : WildFunctor C D)
  : isContr (FunctorIsoFiber C D F (functor_iso_base_center C D F))
  ≔ let P ≔ functor_iso_base_center C D F in
    let M ≔ FunctorIsoMor C D F P in
    let B ≔ (m : M) ↦ Product (FunctorLaws C D ((a ↦ P a .fst), m)) (FunctorIsoSquares C D F P m) in
    let center : FunctorIsoFiber C D F P
      ≔ (F .mor, ((F .map_id, F .map_comp), nat_trans_identity C D F .natural)) in
    (center,
     t ↦ equiv_inverse_map (Id (Σ M B) t center) (Id M (t .fst) (F .mor))
           (subtype_path_equiv M B (functor_iso_fiber_props C D hs F P) t center)
           (funext3 (C .ob) (_ ↦ C .ob) (a b ↦ C .hom a b) (a b _ ↦ D .hom (F .obj a) (F .obj b))
              (t .fst) (F .mor) (functor_iso_fiber_center_arrow C D F t)))

def functor_nat_iso_total_contractible (C D : WildPrecat) (hs : HasHomSets D) (u : IsUnivalentCat D)
  (F : WildFunctor C D) : isContr (Σ (WildFunctor C D) (G ↦ NatIso C D F G))
  ≔ hlevel_equiv zero. (Σ (FunctorIsoBase C D F) (FunctorIsoFiber C D F))
      (Σ (WildFunctor C D) (G ↦ NatIso C D F G))
      (canonical_inverse_equiv (Σ (WildFunctor C D) (G ↦ NatIso C D F G))
        (Σ (FunctorIsoBase C D F) (FunctorIsoFiber C D F)) (functor_nat_iso_total_equiv C D F))
      (sigma_contractible_from_center (FunctorIsoBase C D F) (FunctorIsoFiber C D F)
        (functor_iso_base_contractible C D F u) (functor_iso_fiber_contractible C D hs F))

{` xca:functor-cat-univalent. `}
def functor_wild_univalent (C : WildPrecat) (D : Category) : IsUnivalentCat (FunctorWild C (category_precat D))
  ≔ cat_univalent_from_contractible (FunctorWild C (category_precat D)) (F ↦
      hlevel_equiv zero. (Σ (WildFunctor C (D .wild)) (G ↦ NatIso C (D .wild) F G))
        (Σ (WildFunctor C (D .wild)) (G ↦ CatIso (FunctorWild C (category_precat D)) F G))
        (family_equiv (WildFunctor C (D .wild)) (G ↦ NatIso C (D .wild) F G)
          (G ↦ CatIso (FunctorWild C (category_precat D)) F G)
          (G ↦ canonical_inverse_equiv (CatIso (FunctorWild C (category_precat D)) F G) (NatIso C (D .wild) F G)
            (functor_cat_iso_equiv C (category_precat D) F G)))
        (functor_nat_iso_total_contractible C (D .wild) (D .homset) (D .univalent) F))

{` xca:functor-cat-univalent: "In this case we call it the functor
   category". Its underlying wild precategory is FunctorWild. `}
def FunctorCategory (C : WildPrecat) (D : Category) : Category
  ≔ (FunctorWild C (category_precat D), FunctorPrecat C (category_precat D) .homset,
     functor_wild_univalent C D)

{` The category of presheaves Set^{C^op} on a precategory C. `}
def PresheafCategory (C : Precat) : Category ≔ FunctorCategory (OppositeWild (C .wild)) SetCat

def functor_category_wild (C : WildPrecat) (D : Category)
  : Id WildPrecat (FunctorCategory C D .wild) (FunctorWild C (category_precat D))
  ≔ refl (FunctorWild C (category_precat D))

def presheaf_category_objects (C : Precat)
  : Id Type (PresheafCategory C .wild .ob) (WildFunctor (OppositeWild (C .wild)) SetWild)
  ≔ refl (WildFunctor (OppositeWild (C .wild)) SetWild)

{` Litmus: in the functor category from the path category of Bool to
   Set, the negation natural isomorphism of the constant functor at Bool
   (module 620) yields, by univalence, a self-identification of that
   functor whose idtoiso is again the negation isomorphism. (Evaluating
   this path is not feasible: it is built by transport along ua.) `}
def bool_constant_functor : FunctorCategory (PathWild Bool) SetCat .wild .ob
  ≔ constant_functor (PathWild Bool) SetWild set_cat_bool

def bool_negation_cat_iso
  : CatIso (FunctorCategory (PathWild Bool) SetCat .wild) bool_constant_functor bool_constant_functor
  ≔ (bool_negation_nat_trans, bool_negation_functor_iso)

def bool_negation_functor_path : Id (WildFunctor (PathWild Bool) SetWild) bool_constant_functor bool_constant_functor
  ≔ cat_isotoid (FunctorCategory (PathWild Bool) SetCat .wild) (FunctorCategory (PathWild Bool) SetCat .univalent)
      bool_constant_functor bool_constant_functor bool_negation_cat_iso

def bool_negation_functor_path_iso
  : Id (CatIso (FunctorCategory (PathWild Bool) SetCat .wild) bool_constant_functor bool_constant_functor)
      (cat_idtoiso (FunctorCategory (PathWild Bool) SetCat .wild) bool_constant_functor bool_constant_functor
        bool_negation_functor_path)
      bool_negation_cat_iso
  ≔ cat_idtoiso_isotoid (FunctorCategory (PathWild Bool) SetCat .wild) (FunctorCategory (PathWild Bool) SetCat .univalent)
      bool_constant_functor bool_constant_functor bool_negation_cat_iso
