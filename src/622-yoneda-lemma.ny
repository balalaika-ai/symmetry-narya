export "621-functor-categories"

{` Chapter 6 (cats.tex), section 6.6: the Yoneda embedding
   (def:yoneda), the Yoneda lemma with its naturality (thm:yoneda-lemma)
   and full faithfulness (cor:yo-ff).

   Size. The book asks C to be locally small and takes Set of U-small
   sets for the universe U of the hom-sets. Narya has a single universe
   Type, the hom-types of every precategory live in it and SetCat consists
   of all sets in Type, so the hypothesis is vacuous here. `}

{` ex:repr-functors / def:yoneda: the contravariant representable h_c as a
   Set-valued functor C^op → Set, for a precategory C. Its action on
   arrows and its laws are literally those of contravariant_representable
   (module 603); see representable_presheaf_underlying. `}
def representable_presheaf (C : Precat) (c : C .wild .ob) : WildFunctor (OppositeWild (C .wild)) SetWild
  ≔ (obj ≔ x ↦ (C .wild .hom x c, C .homset x c),
     mor ≔ x y g k ↦ C .wild .comp y x c k g,
     map_id ≔ contravariant_representable (C .wild) c .map_id,
     map_comp ≔ contravariant_representable (C .wild) c .map_comp)

{` Forgetting that the values are sets gives back h_c : C^op → U: the
   actions on objects and arrows agree on the nose (and the laws of
   representable_presheaf are by definition those of h_c). `}
def representable_presheaf_underlying (C : Precat) (c : C .wild .ob)
  : Id (FunctorData (OppositeWild (C .wild)) TypeWild)
      (functor_data (OppositeWild (C .wild)) TypeWild
        (functor_compose (OppositeWild (C .wild)) SetWild TypeWild (full_subcat_inclusion TypeWild SetPredicate)
          (representable_presheaf C c)))
      (functor_data (OppositeWild (C .wild)) TypeWild (contravariant_representable (C .wild) c))
  ≔ refl (functor_data (OppositeWild (C .wild)) TypeWild (contravariant_representable (C .wild) c))

{` def:yoneda: the action of yo on an arrow f : c → c' is the natural
   transformation h_c → h_c' given by postcomposition with f. `}
def yoneda_nat_trans (C : Precat) (c c' : C .wild .ob) (f : C .wild .hom c c')
  : WildNatTrans (OppositeWild (C .wild)) SetWild (representable_presheaf C c) (representable_presheaf C c')
  ≔ (component ≔ x k ↦ C .wild .comp x c c' f k,
     natural ≔ x y g ↦ funext (C .wild .hom x c) (_ ↦ C .wild .hom y c')
       (k ↦ C .wild .comp y x c' (C .wild .comp x c c' f k) g)
       (k ↦ C .wild .comp y c c' f (C .wild .comp y x c k g))
       (k ↦ inverse (C .wild .hom y c') (C .wild .comp y c c' f (C .wild .comp y x c k g))
          (C .wild .comp y x c' (C .wild .comp x c c' f k) g)
          (C .wild .assoc y x c c' g k f)))

{` def:yoneda: the Yoneda embedding yo : C → Set^{C^op}, yo(c) ≡ h_c. `}
def yoneda_functor (C : Precat) : WildFunctor (C .wild) (PresheafCategory C .wild)
  ≔ (obj ≔ c ↦ representable_presheaf C c,
     mor ≔ c c' f ↦ yoneda_nat_trans C c c' f,
     map_id ≔ c ↦ nat_trans_path_pointwise (OppositeWild (C .wild)) SetWild set_wild_homset
       (representable_presheaf C c) (representable_presheaf C c)
       (yoneda_nat_trans C c c (C .wild .idn c))
       (nat_trans_identity (OppositeWild (C .wild)) SetWild (representable_presheaf C c))
       (x ↦ funext (C .wild .hom x c) (_ ↦ C .wild .hom x c) (k ↦ C .wild .comp x c c (C .wild .idn c) k)
          (k ↦ k) (k ↦ C .wild .lu x c k)),
     map_comp ≔ c c' c'' f f' ↦ nat_trans_path_pointwise (OppositeWild (C .wild)) SetWild set_wild_homset
       (representable_presheaf C c) (representable_presheaf C c'')
       (yoneda_nat_trans C c c'' (C .wild .comp c c' c'' f' f))
       (nat_trans_compose (OppositeWild (C .wild)) SetWild (representable_presheaf C c)
         (representable_presheaf C c') (representable_presheaf C c'')
         (yoneda_nat_trans C c' c'' f') (yoneda_nat_trans C c c' f))
       (x ↦ funext (C .wild .hom x c) (_ ↦ C .wild .hom x c'')
          (k ↦ C .wild .comp x c c'' (C .wild .comp c c' c'' f' f) k)
          (k ↦ C .wild .comp x c' c'' f' (C .wild .comp x c c' f k))
          (k ↦ inverse (C .wild .hom x c'') (C .wild .comp x c' c'' f' (C .wild .comp x c c' f k))
             (C .wild .comp x c c'' (C .wild .comp c c' c'' f' f) k)
             (C .wild .assoc x c c' c'' k f f'))))

def yoneda_functor_object (C : Precat) (c : C .wild .ob)
  : Id (WildFunctor (OppositeWild (C .wild)) SetWild) (yoneda_functor C .obj c) (representable_presheaf C c)
  ≔ refl (representable_presheaf C c)

{` thm:yoneda-lemma. Evaluation at id_c. `}
def yoneda_evaluation (C : Precat) (F : PresheafCategory C .wild .ob) (c : C .wild .ob)
  (alpha : PresheafCategory C .wild .hom (yoneda_functor C .obj c) F) : F .obj c .fst
  ≔ alpha .component c (C .wild .idn c)

{` The inverse: x : F(c) gives the natural transformation with components
   k ↦ F(k)(x). `}
def yoneda_extension (C : Precat) (F : PresheafCategory C .wild .ob) (c : C .wild .ob) (x : F .obj c .fst)
  : PresheafCategory C .wild .hom (yoneda_functor C .obj c) F
  ≔ (component ≔ d k ↦ F .mor c d k x,
     natural ≔ d e g ↦ funext (C .wild .hom d c) (_ ↦ F .obj e .fst)
       (k ↦ F .mor d e g (F .mor c d k x))
       (k ↦ F .mor c e (C .wild .comp e d c k g) x)
       (k ↦ inverse (F .obj e .fst) (F .mor c e (C .wild .comp e d c k g) x) (F .mor d e g (F .mor c d k x))
          (happly (F .obj c .fst) (_ ↦ F .obj e .fst) (F .mor c e (C .wild .comp e d c k g))
             (y ↦ F .mor d e g (F .mor c d k y)) (F .map_comp c d e k g) x)))

{` Naturality of α at k : d → c, evaluated at id_c: α_d(k) = F(k)(α_c(id_c)). `}
def yoneda_component_formula (C : Precat) (F : PresheafCategory C .wild .ob) (c : C .wild .ob)
  (alpha : PresheafCategory C .wild .hom (yoneda_functor C .obj c) F) (d : C .wild .ob) (k : C .wild .hom d c)
  : Id (F .obj d .fst) (F .mor c d k (alpha .component c (C .wild .idn c))) (alpha .component d k)
  ≔ concat (F .obj d .fst) (F .mor c d k (alpha .component c (C .wild .idn c)))
      (alpha .component d (C .wild .comp d c c (C .wild .idn c) k)) (alpha .component d k)
      (happly (C .wild .hom c c) (_ ↦ F .obj d .fst)
        (j ↦ F .mor c d k (alpha .component c j)) (j ↦ alpha .component d (C .wild .comp d c c j k))
        (alpha .natural c d k) (C .wild .idn c))
      (refl (alpha .component d) (C .wild .lu d c k))

def yoneda_extension_evaluation (C : Precat) (F : PresheafCategory C .wild .ob) (c : C .wild .ob)
  (alpha : PresheafCategory C .wild .hom (yoneda_functor C .obj c) F)
  : Id (PresheafCategory C .wild .hom (yoneda_functor C .obj c) F)
      (yoneda_extension C F c (yoneda_evaluation C F c alpha)) alpha
  ≔ nat_trans_path_pointwise (OppositeWild (C .wild)) SetWild set_wild_homset (yoneda_functor C .obj c) F
      (yoneda_extension C F c (yoneda_evaluation C F c alpha)) alpha
      (d ↦ funext (C .wild .hom d c) (_ ↦ F .obj d .fst)
         (k ↦ F .mor c d k (alpha .component c (C .wild .idn c))) (alpha .component d)
         (k ↦ yoneda_component_formula C F c alpha d k))

def yoneda_evaluation_extension (C : Precat) (F : PresheafCategory C .wild .ob) (c : C .wild .ob)
  (x : F .obj c .fst)
  : Id (F .obj c .fst) (yoneda_evaluation C F c (yoneda_extension C F c x)) x
  ≔ happly (F .obj c .fst) (_ ↦ F .obj c .fst) (F .mor c c (C .wild .idn c)) (y ↦ y) (F .map_id c) x

{` thm:yoneda-lemma: evaluation at id_c is an equivalence
   Hom(yo(c), F) ≃ F(c); its underlying map is yoneda_evaluation. `}
def yoneda_lemma (C : Precat) (F : PresheafCategory C .wild .ob) (c : C .wild .ob)
  : BookEquiv (PresheafCategory C .wild .hom (yoneda_functor C .obj c) F) (F .obj c .fst)
  ≔ book_quasi_inverse_equiv (PresheafCategory C .wild .hom (yoneda_functor C .obj c) F) (F .obj c .fst)
      (yoneda_evaluation C F c) (yoneda_extension C F c)
      (yoneda_extension_evaluation C F c) (yoneda_evaluation_extension C F c)

def yoneda_lemma_map (C : Precat) (F : PresheafCategory C .wild .ob) (c : C .wild .ob)
  : Id (PresheafCategory C .wild .hom (yoneda_functor C .obj c) F → F .obj c .fst)
      (yoneda_lemma C F c .map) (yoneda_evaluation C F c)
  ≔ refl (yoneda_evaluation C F c)

{` The hom-set of Set^{C^op} as an object of Set. `}
def presheaf_hom_set (C : Precat) (F G : PresheafCategory C .wild .ob) : SetWild .ob
  ≔ (PresheafCategory C .wild .hom F G, PresheafCategory C .homset F G)

{` thm:yoneda-lemma, "isomorphism": evaluation is an isomorphism in Set. `}
def yoneda_lemma_set_iso (C : Precat) (F : PresheafCategory C .wild .ob) (c : C .wild .ob)
  : CatIsIso SetWild (presheaf_hom_set C (yoneda_functor C .obj c) F) (F .obj c) (yoneda_evaluation C F c)
  ≔ type_equiv_to_is_iso (PresheafCategory C .wild .hom (yoneda_functor C .obj c) F) (F .obj c .fst)
      (yoneda_evaluation C F c)
      (native_equivalence (PresheafCategory C .wild .hom (yoneda_functor C .obj c) F) (F .obj c .fst)
        (yoneda_lemma C F c) .equiv)

{` thm:yoneda-lemma, naturality in F. Evaluation at c as a functor
   Set^{C^op} → U, and the Yoneda isomorphism as a natural isomorphism
   Hom(yo(c), -) → ev_c (naturality squares hold by reflexivity). `}
def presheaf_evaluation_functor (C : Precat) (c : C .wild .ob) : WildFunctor (PresheafCategory C .wild) TypeWild
  ≔ (obj ≔ F ↦ F .obj c .fst,
     mor ≔ F G beta ↦ beta .component c,
     map_id ≔ F ↦ refl ((x ↦ x) : F .obj c .fst → F .obj c .fst),
     map_comp ≔ F G H beta gamma ↦
       refl ((x ↦ gamma .component c (beta .component c x)) : F .obj c .fst → H .obj c .fst))

def yoneda_natural_in_presheaf (C : Precat) (c : C .wild .ob)
  : NatIso (PresheafCategory C .wild) TypeWild
      (covariant_representable (PresheafCategory C .wild) (yoneda_functor C .obj c))
      (presheaf_evaluation_functor C c)
  ≔ ((component ≔ F ↦ yoneda_evaluation C F c,
      natural ≔ F G beta ↦
        refl ((alpha ↦ beta .component c (alpha .component c (C .wild .idn c)))
          : PresheafCategory C .wild .hom (yoneda_functor C .obj c) F → G .obj c .fst)),
     F ↦ type_equiv_to_is_iso (PresheafCategory C .wild .hom (yoneda_functor C .obj c) F) (F .obj c .fst)
       (yoneda_evaluation C F c)
       (native_equivalence (PresheafCategory C .wild .hom (yoneda_functor C .obj c) F) (F .obj c .fst)
         (yoneda_lemma C F c) .equiv))

{` thm:yoneda-lemma, naturality in c. For fixed F, c ↦ Hom(yo(c), F) is
   the composite of yo^op with the contravariant representable of
   Set^{C^op} at F, and F is viewed as a U-valued functor. `}
def yoneda_hom_presheaf (C : Precat) (F : PresheafCategory C .wild .ob)
  : WildFunctor (OppositeWild (C .wild)) TypeWild
  ≔ functor_compose (OppositeWild (C .wild)) (OppositeWild (PresheafCategory C .wild)) TypeWild
      (contravariant_representable (PresheafCategory C .wild) F)
      (opposite_functor (C .wild) (PresheafCategory C .wild) (yoneda_functor C))

def presheaf_underlying (C : Precat) (F : PresheafCategory C .wild .ob) : WildFunctor (OppositeWild (C .wild)) TypeWild
  ≔ functor_compose (OppositeWild (C .wild)) SetWild TypeWild (full_subcat_inclusion TypeWild SetPredicate) F

def yoneda_natural_in_object_square (C : Precat) (F : PresheafCategory C .wild .ob) (c c' : C .wild .ob)
  (f : C .wild .hom c' c) (alpha : PresheafCategory C .wild .hom (yoneda_functor C .obj c) F)
  : Id (F .obj c' .fst) (F .mor c c' f (alpha .component c (C .wild .idn c)))
      (alpha .component c' (C .wild .comp c' c' c f (C .wild .idn c')))
  ≔ concat (F .obj c' .fst) (F .mor c c' f (alpha .component c (C .wild .idn c))) (alpha .component c' f)
      (alpha .component c' (C .wild .comp c' c' c f (C .wild .idn c')))
      (yoneda_component_formula C F c alpha c' f)
      (refl (alpha .component c') (inverse (C .wild .hom c' c) (C .wild .comp c' c' c f (C .wild .idn c')) f
        (C .wild .ru c' c f)))

def yoneda_natural_in_object (C : Precat) (F : PresheafCategory C .wild .ob)
  : NatIso (OppositeWild (C .wild)) TypeWild (yoneda_hom_presheaf C F) (presheaf_underlying C F)
  ≔ ((component ≔ c ↦ yoneda_evaluation C F c,
      natural ≔ c c' f ↦ funext (PresheafCategory C .wild .hom (yoneda_functor C .obj c) F) (_ ↦ F .obj c' .fst)
        (alpha ↦ F .mor c c' f (alpha .component c (C .wild .idn c)))
        (alpha ↦ alpha .component c' (C .wild .comp c' c' c f (C .wild .idn c')))
        (yoneda_natural_in_object_square C F c c' f)),
     c ↦ type_equiv_to_is_iso (PresheafCategory C .wild .hom (yoneda_functor C .obj c) F) (F .obj c .fst)
       (yoneda_evaluation C F c)
       (native_equivalence (PresheafCategory C .wild .hom (yoneda_functor C .obj c) F) (F .obj c .fst)
         (yoneda_lemma C F c) .equiv))

{` cor:yo-ff: yo is fully faithful; the inverse of yo on arrows is
   evaluation at the identity. `}
def yoneda_mor_equiv (C : Precat) (c c' : C .wild .ob)
  : BookIsEquiv (C .wild .hom c c')
      (PresheafCategory C .wild .hom (yoneda_functor C .obj c) (yoneda_functor C .obj c'))
      (yoneda_functor C .mor c c')
  ≔ book_quasi_inverse_equiv (C .wild .hom c c')
      (PresheafCategory C .wild .hom (yoneda_functor C .obj c) (yoneda_functor C .obj c'))
      (yoneda_functor C .mor c c') (yoneda_evaluation C (yoneda_functor C .obj c') c)
      (f ↦ C .wild .ru c c' f)
      (alpha ↦ nat_trans_path_pointwise (OppositeWild (C .wild)) SetWild set_wild_homset
         (yoneda_functor C .obj c) (yoneda_functor C .obj c')
         (yoneda_nat_trans C c c' (yoneda_evaluation C (yoneda_functor C .obj c') c alpha)) alpha
         (d ↦ funext (C .wild .hom d c) (_ ↦ C .wild .hom d c')
            (k ↦ C .wild .comp d c c' (alpha .component c (C .wild .idn c)) k) (alpha .component d)
            (k ↦ yoneda_component_formula C (yoneda_functor C .obj c') c alpha d k))) .equiv

def yoneda_fully_faithful (C : Precat)
  : IsFullyFaithful (C .wild) (PresheafCategory C .wild) (yoneda_functor C)
  ≔ fully_faithful_from_equivs (C .wild) (PresheafCategory C .wild) (yoneda_functor C) (yoneda_mor_equiv C)

{` Litmus: the precategory of sets, the presheaf h_Bool, and the Yoneda
   lemma at F = h_Bool, c = Bool: evaluation of yo(not) gives not, and the
   inverse sends not to the natural transformation k ↦ not ∘ k. `}
def yoneda_litmus_evaluation
  : Id (Bool → Bool)
      (yoneda_evaluation set_precat (yoneda_functor set_precat .obj set_cat_bool) set_cat_bool
        (yoneda_functor set_precat .mor set_cat_bool set_cat_bool bool_not))
      bool_not
  ≔ refl bool_not

def yoneda_litmus_extension
  : Id Bool
      (yoneda_extension set_precat (yoneda_functor set_precat .obj set_cat_bool) set_cat_bool bool_not
        .component set_cat_bool (x ↦ true.) false.)
      false.
  ≔ refl (false. : Bool)

def yoneda_litmus_inverse_value
  : Id Bool
      (equiv_inverse_map (PresheafCategory set_precat .wild .hom (yoneda_functor set_precat .obj set_cat_bool)
          (yoneda_functor set_precat .obj set_cat_bool)) (Bool → Bool)
        (native_equivalence (PresheafCategory set_precat .wild .hom (yoneda_functor set_precat .obj set_cat_bool)
            (yoneda_functor set_precat .obj set_cat_bool)) (Bool → Bool)
          (yoneda_lemma set_precat (yoneda_functor set_precat .obj set_cat_bool) set_cat_bool))
        bool_not .component set_cat_bool bool_not true.)
      true.
  ≔ refl (true. : Bool)
