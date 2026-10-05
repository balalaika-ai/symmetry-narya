export "620-natural-isomorphisms"

{` Chapter 6 (cats.tex), the \wip example after def:full-faithful (line
   728): the core inclusion is faithful, projections can be full but not
   faithful, and full subcategory inclusions are fully faithful. The core
   and the product wild precategory are defined here (the book has no
   formal definition of either). `}

{` The core of a wild precategory: same objects, isomorphisms as arrows. `}
def CoreWild (C : WildPrecat) : WildPrecat
  ≔ (ob ≔ C .ob,
     hom ≔ a b ↦ CatIso C a b,
     idn ≔ a ↦ cat_identity_iso C a,
     comp ≔ a b c e2 e1 ↦ cat_iso_compose C a b c e2 e1,
     lu ≔ a b e ↦ cat_iso_path C a b (cat_iso_compose C a b b (cat_identity_iso C b) e) e (C .lu a b (e .fst)),
     ru ≔ a b e ↦ cat_iso_path C a b (cat_iso_compose C a a b e (cat_identity_iso C a)) e (C .ru a b (e .fst)),
     assoc ≔ a b c d e1 e2 e3 ↦
       cat_iso_path C a d (cat_iso_compose C a c d e3 (cat_iso_compose C a b c e2 e1))
         (cat_iso_compose C a b d (cat_iso_compose C b c d e3 e2) e1)
         (C .assoc a b c d (e1 .fst) (e2 .fst) (e3 .fst)))

{` The core is a (wild) pregroupoid. `}
def core_invertible (C : WildPrecat) : IsPregroupoid (CoreWild C)
  ≔ a b e ↦
      ((cat_iso_inverse C a b e,
        cat_iso_path C b b (cat_iso_compose C b a b e (cat_iso_inverse C a b e)) (cat_identity_iso C b)
          (e .snd .fst .snd)),
       (cat_iso_inverse C a b e,
        cat_iso_path C a a (cat_iso_compose C a b a (cat_iso_inverse C a b e) e) (cat_identity_iso C a)
          (cat_iso_inverse C a b e .snd .fst .snd)))

def core_inclusion (C : WildPrecat) : WildFunctor (CoreWild C) C
  ≔ (obj ≔ a ↦ a,
     mor ≔ a b e ↦ e .fst,
     map_id ≔ a ↦ refl (C .idn a),
     map_comp ≔ a b c e1 e2 ↦ refl (C .comp a b c (e2 .fst) (e1 .fst)))

{` "core inclusion is faithful": isIso is a proposition, so forgetting
   it is an injection. `}
def core_inclusion_faithful (C : WildPrecat) : IsFaithful (CoreWild C) C (core_inclusion C)
  ≔ a b ↦ path_equivalences_embedding (CatIso C a b) (C .hom a b) (e ↦ e .fst)
      (u v ↦ book_equivalence (Id (CatIso C a b) u v) (Id (C .hom a b) (u .fst) (v .fst))
        (cat_iso_path_equiv C a b u v) .equiv)

{` The core inclusion need not be full: in Set the constant map at true on
   Bool is not an isomorphism. `}
def constant_true_not_iso (i : CatIsIso SetWild set_cat_bool set_cat_bool (_ ↦ true.)) : Empty
  ≔ let h ≔ i .snd .fst in
    bool_encode true. false.
      (concat Bool true. (h true.) false.
        (inverse Bool (h true.) true. (i .snd .snd (refl (true. : Bool))))
        (i .snd .snd (refl (false. : Bool))))

def set_core_inclusion_not_full (h : IsFull (CoreWild SetWild) SetWild (core_inclusion SetWild)) : Empty
  ≔ mere_rec (BookFiber (CatIso SetWild set_cat_bool set_cat_bool) (Bool → Bool) (e ↦ e .fst) (_ ↦ true.)) Empty
      empty_prop
      (t ↦ constant_true_not_iso
        (transport (Bool → Bool) (CatIsIso SetWild set_cat_bool set_cat_bool) (t .fst .fst) (_ ↦ true.)
          (inverse (Bool → Bool) (_ ↦ true.) (t .fst .fst) (t .snd)) (t .fst .snd)))
      (h set_cat_bool set_cat_bool (_ ↦ true.))

{` The product of two wild precategories, componentwise. `}
def ProductWild (C D : WildPrecat) : WildPrecat
  ≔ (ob ≔ Product (C .ob) (D .ob),
     hom ≔ x y ↦ Product (C .hom (x .fst) (y .fst)) (D .hom (x .snd) (y .snd)),
     idn ≔ x ↦ (C .idn (x .fst), D .idn (x .snd)),
     comp ≔ x y z g f ↦ (C .comp (x .fst) (y .fst) (z .fst) (g .fst) (f .fst),
                         D .comp (x .snd) (y .snd) (z .snd) (g .snd) (f .snd)),
     lu ≔ x y f ↦ (C .lu (x .fst) (y .fst) (f .fst), D .lu (x .snd) (y .snd) (f .snd)),
     ru ≔ x y f ↦ (C .ru (x .fst) (y .fst) (f .fst), D .ru (x .snd) (y .snd) (f .snd)),
     assoc ≔ x y z w f g h ↦
       (C .assoc (x .fst) (y .fst) (z .fst) (w .fst) (f .fst) (g .fst) (h .fst),
        D .assoc (x .snd) (y .snd) (z .snd) (w .snd) (f .snd) (g .snd) (h .snd)))

def product_projection_left (C D : WildPrecat) : WildFunctor (ProductWild C D) C
  ≔ (obj ≔ x ↦ x .fst,
     mor ≔ x y f ↦ f .fst,
     map_id ≔ x ↦ refl (C .idn (x .fst)),
     map_comp ≔ x y z f g ↦ refl (C .comp (x .fst) (y .fst) (z .fst) (g .fst) (f .fst)))

{` "projections can be full": the projection C × D → C is full as soon
   as every hom-type of D is (merely) inhabited. `}
def product_projection_full (C D : WildPrecat) (hD : (d d' : D .ob) → Mere (D .hom d d'))
  : IsFull (ProductWild C D) C (product_projection_left C D)
  ≔ x y b ↦ mere_rec (D .hom (x .snd) (y .snd))
      (Mere (BookFiber (Product (C .hom (x .fst) (y .fst)) (D .hom (x .snd) (y .snd))) (C .hom (x .fst) (y .fst))
        (f ↦ f .fst) b))
      (mere_isprop (BookFiber (Product (C .hom (x .fst) (y .fst)) (D .hom (x .snd) (y .snd))) (C .hom (x .fst) (y .fst))
        (f ↦ f .fst) b))
      (k ↦ mere (BookFiber (Product (C .hom (x .fst) (y .fst)) (D .hom (x .snd) (y .snd))) (C .hom (x .fst) (y .fst))
        (f ↦ f .fst) b) ((b, k), refl b))
      (hD (x .snd) (y .snd))

{` "not faithful": if D has two different parallel arrows (and C has an
   object), the projection is not faithful. `}
def product_projection_not_faithful (C D : WildPrecat) (c : C .ob) (d d' : D .ob) (k1 k2 : D .hom d d')
  (ne : Id (D .hom d d') k1 k2 → Empty) (h : IsFaithful (ProductWild C D) C (product_projection_left C D)) : Empty
  ≔ ne (refl ((t ↦ t .fst .snd)
          : BookFiber (Product (C .hom c c) (D .hom d d')) (C .hom c c) (f ↦ f .fst) (C .idn c) → D .hom d d')
        (h (c, d) (c, d') (C .idn c) ((C .idn c, k1), refl (C .idn c)) ((C .idn c, k2), refl (C .idn c))))

{` A concrete instance: the one-object precategory of the monoid
   (Bool, and, true). Its hom-type Bool is inhabited and has two elements,
   so the projection Set × B(Bool, and) → Set is full but not faithful. `}
def bool_conjunction (a b : Bool) : Bool ≔ match a [ true. ↦ b | false. ↦ false. ]

def bool_and_true_right (a : Bool) : Id Bool (bool_conjunction a true.) a
  ≔ match a [ true. ↦ refl (true. : Bool) | false. ↦ refl (false. : Bool) ]

def bool_and_assoc (a b c : Bool) : Id Bool (bool_conjunction a (bool_conjunction b c)) (bool_conjunction (bool_conjunction a b) c)
  ≔ match a [ true. ↦ refl (bool_conjunction b c) | false. ↦ refl (false. : Bool) ]

def BoolAndWild : WildPrecat
  ≔ (ob ≔ Unit,
     hom ≔ _ _ ↦ Bool,
     idn ≔ _ ↦ true.,
     comp ≔ _ _ _ g f ↦ bool_conjunction g f,
     lu ≔ _ _ f ↦ refl f,
     ru ≔ _ _ f ↦ bool_and_true_right f,
     assoc ≔ _ _ _ _ f g h ↦ bool_and_assoc h g f)

def bool_and_composite_litmus : Id Bool (BoolAndWild .comp star. star. star. true. false.) false.
  ≔ refl (false. : Bool)

def set_bool_and_projection_full
  : IsFull (ProductWild SetWild BoolAndWild) SetWild (product_projection_left SetWild BoolAndWild)
  ≔ product_projection_full SetWild BoolAndWild (_ _ ↦ mere Bool true.)

def set_bool_and_projection_not_faithful
  (h : IsFaithful (ProductWild SetWild BoolAndWild) SetWild (product_projection_left SetWild BoolAndWild)) : Empty
  ≔ product_projection_not_faithful SetWild BoolAndWild set_cat_bool star. star. true. false.
      (bool_encode true. false.) h

{` "full subcategory inclusions are fully faithful": the inclusion acts as
   the identity on hom-types. `}
def full_subcat_inclusion_fully_faithful (C : WildPrecat) (P : Subtypes (C .ob))
  : IsFullyFaithful (FullSubcat C P) C (full_subcat_inclusion C P)
  ≔ fully_faithful_from_equivs (FullSubcat C P) C (full_subcat_inclusion C P)
      (x y ↦ book_equivalence (C .hom (x .fst) (y .fst)) (C .hom (x .fst) (y .fst))
        (identity_equiv (C .hom (x .fst) (y .fst))) .equiv)

def set_inclusion_fully_faithful : IsFullyFaithful SetWild TypeWild (full_subcat_inclusion TypeWild SetPredicate)
  ≔ full_subcat_inclusion_fully_faithful TypeWild SetPredicate
