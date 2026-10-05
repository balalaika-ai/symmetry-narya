export "603-adjunctions-and-equivalences"

{` Chapter 6 (cats.tex), section 6.9: def:prod-in-a-cat,
   xca:product-cone-prop, the remark def:product-cones-as-terminal,
   def:coprod-in-a-cat and the surrounding prose (products and coproducts
   of types, binary products, coproduct cocones as initial cocones).

   A cone on a, b is (P, p₁ : P → a, p₂ : P → b). An arrow from a cone
   (X, x₁, x₂) to (P, p₁, p₂) is f : X → P with identifications
   x_i = p_i ∘ f (the book's orientation "x_i = p_i f"). "There is a unique
   arrow" is read as contractibility of this type (isContr). `}

def CatCone (C : WildPrecat) (a b : C .ob) : Type ≔ Σ (C .ob) (p ↦ Product (C .hom p a) (C .hom p b))

def ConeFactorization (C : WildPrecat) (a b : C .ob) (X P : CatCone C a b) : Type
  ≔ Σ (C .hom (X .fst) (P .fst)) (f ↦
      Product (Id (C .hom (X .fst) a) (X .snd .fst) (C .comp (X .fst) (P .fst) a (P .snd .fst) f))
        (Id (C .hom (X .fst) b) (X .snd .snd) (C .comp (X .fst) (P .fst) b (P .snd .snd) f)))

{` def:prod-in-a-cat. `}
def IsProductCone (C : WildPrecat) (a b : C .ob) (P : CatCone C a b) : Type
  ≔ (X : CatCone C a b) → isContr (ConeFactorization C a b X P)

def ProductCone (C : WildPrecat) (a b : C .ob) : Type ≔ Σ (CatCone C a b) (IsProductCone C a b)

def is_product_cone_prop (C : WildPrecat) (a b : C .ob) (P : CatCone C a b) : isProp (IsProductCone C a b P)
  ≔ pi_prop (CatCone C a b) (X ↦ isContr (ConeFactorization C a b X P))
      (X ↦ iscontr_isprop (ConeFactorization C a b X P))

{` Identity and composite arrows of cones. `}
def cone_fac_idn (C : WildPrecat) (a b : C .ob) (X : CatCone C a b) : ConeFactorization C a b X X
  ≔ (C .idn (X .fst),
     (inverse (C .hom (X .fst) a) (C .comp (X .fst) (X .fst) a (X .snd .fst) (C .idn (X .fst))) (X .snd .fst)
        (C .ru (X .fst) a (X .snd .fst)),
      inverse (C .hom (X .fst) b) (C .comp (X .fst) (X .fst) b (X .snd .snd) (C .idn (X .fst))) (X .snd .snd)
        (C .ru (X .fst) b (X .snd .snd))))

def cone_fac_leg (C : WildPrecat) (a : C .ob) (x y z : C .ob) (xa : C .hom x a) (ya : C .hom y a) (za : C .hom z a)
  (k : C .hom y z) (h : C .hom x y) (kk : Id (C .hom y a) ya (C .comp y z a za k)) (hh : Id (C .hom x a) xa (C .comp x y a ya h))
  : Id (C .hom x a) xa (C .comp x z a za (C .comp x y z k h))
  ≔ calc
      xa
      = C .comp x y a ya h by hh
      = C .comp x y a (C .comp y z a za k) h by cat_whisker_right C x y a ya (C .comp y z a za k) h kk
      = C .comp x z a za (C .comp x y z k h)
        by inverse (C .hom x a) (C .comp x z a za (C .comp x y z k h)) (C .comp x y a (C .comp y z a za k) h)
             (C .assoc x y z a h k za) ∎

def cone_fac_comp (C : WildPrecat) (a b : C .ob) (X Y Z : CatCone C a b) (k : ConeFactorization C a b Y Z)
  (h : ConeFactorization C a b X Y) : ConeFactorization C a b X Z
  ≔ (C .comp (X .fst) (Y .fst) (Z .fst) (k .fst) (h .fst),
     (cone_fac_leg C a (X .fst) (Y .fst) (Z .fst) (X .snd .fst) (Y .snd .fst) (Z .snd .fst) (k .fst) (h .fst)
        (k .snd .fst) (h .snd .fst),
      cone_fac_leg C b (X .fst) (Y .fst) (Z .fst) (X .snd .snd) (Y .snd .snd) (Z .snd .snd) (k .fst) (h .fst)
        (k .snd .snd) (h .snd .snd)))

{` Isomorphisms of cones over a univalent C: the type of cones Y with an
   isomorphism e : X ≅ Y of vertices such that y_i ∘ e = x_i is
   contractible. `}
def ConeIso (C : WildPrecat) (a b : C .ob) (X Y : CatCone C a b) : Type
  ≔ Σ (CatIso C (X .fst) (Y .fst)) (e ↦
      Product (Id (C .hom (X .fst) a) (C .comp (X .fst) (Y .fst) a (Y .snd .fst) (e .fst)) (X .snd .fst))
        (Id (C .hom (X .fst) b) (C .comp (X .fst) (Y .fst) b (Y .snd .snd) (e .fst)) (X .snd .snd)))

def cone_iso_refl (C : WildPrecat) (a b : C .ob) (X : CatCone C a b) : ConeIso C a b X X
  ≔ (cat_identity_iso C (X .fst), (C .ru (X .fst) a (X .snd .fst), C .ru (X .fst) b (X .snd .snd)))

def cone_product_contractible (A B : Type) (hA : isContr A) (hB : isContr B) : isContr (Product A B)
  ≔ sigma_contractible A (_ ↦ B) hA (_ ↦ hB)

def cone_iso_total_contractible (C : WildPrecat) (u : IsUnivalentCat C) (a b : C .ob) (X : CatCone C a b)
  : isContr (Σ (CatCone C a b) (ConeIso C a b X))
  ≔ let x ≔ X .fst in
    let QE ≔ Σ (C .ob) (q ↦ CatIso C x q) in
    let Fa : QE → Type ≔ qe ↦ Fiber (C .hom (qe .fst) a) (C .hom x a) (k ↦ C .comp x (qe .fst) a k (qe .snd .fst)) (X .snd .fst) in
    let Fb : QE → Type ≔ qe ↦ Fiber (C .hom (qe .fst) b) (C .hom x b) (k ↦ C .comp x (qe .fst) b k (qe .snd .fst)) (X .snd .snd) in
    contractible_retract (Σ QE (qe ↦ Product (Fa qe) (Fb qe))) (Σ (CatCone C a b) (ConeIso C a b X))
      (sigma_contractible QE (qe ↦ Product (Fa qe) (Fb qe)) (cat_univalent_iso_total_contractible C u x)
        (qe ↦ cone_product_contractible (Fa qe) (Fb qe)
          (cat_precompose_equiv C x (qe .fst) (qe .snd .fst) (qe .snd .snd) a .equiv (X .snd .fst))
          (cat_precompose_equiv C x (qe .fst) (qe .snd .fst) (qe .snd .snd) b .equiv (X .snd .snd))))
      (t ↦ ((t .fst .fst, (t .snd .fst .fst, t .snd .snd .fst)), (t .fst .snd, (t .snd .fst .snd, t .snd .snd .snd))))
      (s ↦ ((s .fst .fst, s .snd .fst), ((s .fst .snd .fst, s .snd .snd .fst), (s .fst .snd .snd, s .snd .snd .snd))))
      (s ↦ refl s)

{` Two product cones on a, b are isomorphic as cones (in any wild
   precategory): the comparison arrows compose to arrows of cones that
   must agree with the identities by uniqueness. `}
def product_cone_iso (C : WildPrecat) (a b : C .ob) (P Q : ProductCone C a b) : ConeIso C a b (P .fst) (Q .fst)
  ≔ let p ≔ P .fst in let q ≔ Q .fst in
    let cf ≔ Q .snd p .center in
    let cg ≔ P .snd q .center in
    let gf : Id (C .hom (p .fst) (p .fst)) (C .comp (p .fst) (q .fst) (p .fst) (cg .fst) (cf .fst)) (C .idn (p .fst))
      ≔ contractible_prop (ConeFactorization C a b p p) (P .snd p)
          (cone_fac_comp C a b p q p cg cf) (cone_fac_idn C a b p) .fst in
    let fg : Id (C .hom (q .fst) (q .fst)) (C .comp (q .fst) (p .fst) (q .fst) (cf .fst) (cg .fst)) (C .idn (q .fst))
      ≔ contractible_prop (ConeFactorization C a b q q) (Q .snd q)
          (cone_fac_comp C a b q p q cf cg) (cone_fac_idn C a b q) .fst in
    ((cf .fst, ((cg .fst, fg), (cg .fst, gf))),
     (inverse (C .hom (p .fst) a) (p .snd .fst) (C .comp (p .fst) (q .fst) a (q .snd .fst) (cf .fst)) (cf .snd .fst),
      inverse (C .hom (p .fst) b) (p .snd .snd) (C .comp (p .fst) (q .fst) b (q .snd .snd) (cf .fst)) (cf .snd .snd)))

{` xca:product-cone-prop: in a univalent wild precategory the type of
   product cones on a, b is a proposition. `}
def product_cone_prop (C : WildPrecat) (u : IsUnivalentCat C) (a b : C .ob) : isProp (ProductCone C a b)
  ≔ P Q ↦
    let r : Id (CatCone C a b) (P .fst) (Q .fst)
      ≔ contractible_prop (Σ (CatCone C a b) (ConeIso C a b (P .fst))) (cone_iso_total_contractible C u a b (P .fst))
          (P .fst, cone_iso_refl C a b (P .fst)) (Q .fst, product_cone_iso C a b P Q) .fst in
    (r, pathover_of_eq (CatCone C a b) (IsProductCone C a b) (P .fst) (Q .fst) r (P .snd) (Q .snd)
          (is_product_cone_prop C a b (Q .fst)
            (transport (CatCone C a b) (IsProductCone C a b) (P .fst) (Q .fst) r (P .snd)) (Q .snd)))

{` "We say that a (wild) category has binary products if every pair of
   objects has a product cone"; by xca:product-cone-prop the product cone is
   then unique, and having binary products is a proposition. `}
def HasBinaryProducts (C : WildPrecat) : Type ≔ (a b : C .ob) → ProductCone C a b

def product_cone_unique (C : WildPrecat) (u : IsUnivalentCat C) (a b : C .ob) (P : ProductCone C a b)
  : isContr (ProductCone C a b)
  ≔ (P, Q ↦ product_cone_prop C u a b Q P)

def has_binary_products_prop (C : WildPrecat) (u : IsUnivalentCat C) : isProp (HasBinaryProducts C)
  ≔ pi_prop (C .ob) (a ↦ (b : C .ob) → ProductCone C a b)
      (a ↦ pi_prop (C .ob) (b ↦ ProductCone C a b) (b ↦ product_cone_prop C u a b))

{` "(A × B, fst, snd) is a product cone in the wild category of types." `}
def type_product_cone (A B : Type) : CatCone TypeWild A B ≔ (Product A B, (t ↦ t .fst, t ↦ t .snd))

def type_product_cone_is_product (A B : Type) : IsProductCone TypeWild A B (type_product_cone A B)
  ≔ X ↦ contractible_retract
      (Σ (Product (X .fst → A) (X .fst → B)) (w ↦ Id (Product (X .fst → A) (X .fst → B)) (X .snd) w))
      (ConeFactorization TypeWild A B X (type_product_cone A B))
      (iscontr_idfrom (Product (X .fst → A) (X .fst → B)) (X .snd))
      (t ↦ (x ↦ (t .fst .fst x, t .fst .snd x), (t .snd .fst, t .snd .snd)))
      (s ↦ ((x ↦ s .fst x .fst, x ↦ s .fst x .snd), (s .snd .fst, s .snd .snd)))
      (s ↦ refl s)

def type_has_binary_products : HasBinaryProducts TypeWild
  ≔ A B ↦ (type_product_cone A B, type_product_cone_is_product A B)

{` Every product cone of types is (A × B, fst, snd). `}
def type_product_cone_path (A B : Type) (P : ProductCone TypeWild A B)
  : Id (ProductCone TypeWild A B) P (type_has_binary_products A B)
  ≔ product_cone_prop TypeWild type_wild_univalent A B P (type_has_binary_products A B)

{` Litmus: the cone (Bool, id, not) on Bool, Bool factors through
   Bool × Bool by x ↦ (x, not x). `}
def product_litmus_cone : CatCone TypeWild Bool Bool ≔ (Bool, (x ↦ x, bool_not))

def product_litmus_factor
  : Id (Product Bool Bool) (type_product_cone_is_product Bool Bool product_litmus_cone .center .fst true.)
      (true., false.)
  ≔ refl ((true., false.) : Product Bool Bool)

{` def:product-cones-as-terminal: for a precategory C, the precategory of
   cones on a, b with arrows the filled triangles; a product cone is
   exactly a terminal cone (def:terminal-obj unfolded: every hom type into
   it is contractible), definitionally. For a wild C the unit and
   associativity laws of the cone category would need coherences, as for
   slices (def:slice-cat); the terminality statement only uses objects and
   arrows. `}
def cone_fac_prop (C : WildPrecat) (hs : HasHomSets C) (a b : C .ob) (X P : CatCone C a b) (f : C .hom (X .fst) (P .fst))
  : isProp (Product (Id (C .hom (X .fst) a) (X .snd .fst) (C .comp (X .fst) (P .fst) a (P .snd .fst) f))
             (Id (C .hom (X .fst) b) (X .snd .snd) (C .comp (X .fst) (P .fst) b (P .snd .snd) f)))
  ≔ product_prop (Id (C .hom (X .fst) a) (X .snd .fst) (C .comp (X .fst) (P .fst) a (P .snd .fst) f))
      (Id (C .hom (X .fst) b) (X .snd .snd) (C .comp (X .fst) (P .fst) b (P .snd .snd) f))
      (hs (X .fst) a (X .snd .fst) (C .comp (X .fst) (P .fst) a (P .snd .fst) f))
      (hs (X .fst) b (X .snd .snd) (C .comp (X .fst) (P .fst) b (P .snd .snd) f))

def cone_fac_path (C : WildPrecat) (hs : HasHomSets C) (a b : C .ob) (X P : CatCone C a b)
  (u v : ConeFactorization C a b X P) (p : Id (C .hom (X .fst) (P .fst)) (u .fst) (v .fst))
  : Id (ConeFactorization C a b X P) u v
  ≔ let T : C .hom (X .fst) (P .fst) → Type
      ≔ f ↦ Product (Id (C .hom (X .fst) a) (X .snd .fst) (C .comp (X .fst) (P .fst) a (P .snd .fst) f))
              (Id (C .hom (X .fst) b) (X .snd .snd) (C .comp (X .fst) (P .fst) b (P .snd .snd) f)) in
    (p, pathover_of_eq (C .hom (X .fst) (P .fst)) T (u .fst) (v .fst) p (u .snd) (v .snd)
          (cone_fac_prop C hs a b X P (v .fst) (transport (C .hom (X .fst) (P .fst)) T (u .fst) (v .fst) p (u .snd))
            (v .snd)))

def cone_precat_wild (C : WildPrecat) (hs : HasHomSets C) (a b : C .ob) : WildPrecat
  ≔ (ob ≔ CatCone C a b,
     hom ≔ ConeFactorization C a b,
     idn ≔ cone_fac_idn C a b,
     comp ≔ cone_fac_comp C a b,
     lu ≔ X Y f ↦ cone_fac_path C hs a b X Y (cone_fac_comp C a b X Y Y (cone_fac_idn C a b Y) f) f
       (C .lu (X .fst) (Y .fst) (f .fst)),
     ru ≔ X Y f ↦ cone_fac_path C hs a b X Y (cone_fac_comp C a b X X Y f (cone_fac_idn C a b X)) f
       (C .ru (X .fst) (Y .fst) (f .fst)),
     assoc ≔ X Y Z W f g h ↦ cone_fac_path C hs a b X W
       (cone_fac_comp C a b X Z W h (cone_fac_comp C a b X Y Z g f))
       (cone_fac_comp C a b X Y W (cone_fac_comp C a b Y Z W h g) f)
       (C .assoc (X .fst) (Y .fst) (Z .fst) (W .fst) (f .fst) (g .fst) (h .fst)))

def cone_homset (C : WildPrecat) (hs : HasHomSets C) (a b : C .ob) : HasHomSets (cone_precat_wild C hs a b)
  ≔ X P ↦ sigma_set (C .hom (X .fst) (P .fst))
      (f ↦ Product (Id (C .hom (X .fst) a) (X .snd .fst) (C .comp (X .fst) (P .fst) a (P .snd .fst) f))
             (Id (C .hom (X .fst) b) (X .snd .snd) (C .comp (X .fst) (P .fst) b (P .snd .snd) f)))
      (hs (X .fst) (P .fst))
      (f ↦ prop_is_set (Product (Id (C .hom (X .fst) a) (X .snd .fst) (C .comp (X .fst) (P .fst) a (P .snd .fst) f))
             (Id (C .hom (X .fst) b) (X .snd .snd) (C .comp (X .fst) (P .fst) b (P .snd .snd) f)))
             (cone_fac_prop C hs a b X P f))

def ConePrecat (C : Precat) (a b : C .wild .ob) : Precat
  ≔ (cone_precat_wild (C .wild) (C .homset) a b, cone_homset (C .wild) (C .homset) a b)

def product_cone_is_terminal_cone (C : WildPrecat) (hs : HasHomSets C) (a b : C .ob) (P : CatCone C a b)
  : Id Type (IsProductCone C a b P)
      ((X : cone_precat_wild C hs a b .ob) → isContr (cone_precat_wild C hs a b .hom X P))
  ≔ refl (IsProductCone C a b P)

{` def:coprod-in-a-cat: cocones (C, i₁ : a → C, i₂ : b → C) with a unique
   f : C → X such that x_j = f ∘ i_j. `}
def CatCocone (C : WildPrecat) (a b : C .ob) : Type ≔ Σ (C .ob) (x ↦ Product (C .hom a x) (C .hom b x))

def CoconeFactorization (C : WildPrecat) (a b : C .ob) (K X : CatCocone C a b) : Type
  ≔ Σ (C .hom (K .fst) (X .fst)) (f ↦
      Product (Id (C .hom a (X .fst)) (X .snd .fst) (C .comp a (K .fst) (X .fst) f (K .snd .fst)))
        (Id (C .hom b (X .fst)) (X .snd .snd) (C .comp b (K .fst) (X .fst) f (K .snd .snd))))

def IsCoproductCocone (C : WildPrecat) (a b : C .ob) (K : CatCocone C a b) : Type
  ≔ (X : CatCocone C a b) → isContr (CoconeFactorization C a b K X)

def CoproductCocone (C : WildPrecat) (a b : C .ob) : Type ≔ Σ (CatCocone C a b) (IsCoproductCocone C a b)

{` Duality: coproduct cocones in C are exactly product cones in C^op. `}
def coproduct_cocone_is_op_product_cone (C : WildPrecat) (a b : C .ob) (K : CatCocone C a b)
  : Id Type (IsCoproductCocone C a b K) (IsProductCone (OppositeWild C) a b K)
  ≔ refl (IsCoproductCocone C a b K)

{` "In other words, a coproduct cocone is an initial cocone under the pair
   of objects A, B": the precategory of cocones is the opposite of the cone
   precategory of C^op, and IsCoproductCocone is initiality there. `}
def cocone_precat_wild (C : WildPrecat) (hs : HasHomSets C) (a b : C .ob) : WildPrecat
  ≔ OppositeWild (cone_precat_wild (OppositeWild C) (x y ↦ hs y x) a b)

def coproduct_cocone_is_initial_cocone (C : WildPrecat) (hs : HasHomSets C) (a b : C .ob) (K : CatCocone C a b)
  : Id Type (IsCoproductCocone C a b K)
      ((X : cocone_precat_wild C hs a b .ob) → isContr (cocone_precat_wild C hs a b .hom K X))
  ≔ refl (IsCoproductCocone C a b K)

{` "In the wild category of types, we have the coproduct cocones
   (A ⊔ B, inl, inr)": precomposition with inl, inr is an equivalence
   (Sum A B → X) ≃ (A → X) × (B → X), and the factorizations of a cocone
   are its fiber. `}
def type_coproduct_cocone (A B : Type) : CatCocone TypeWild A B ≔ (Sum A B, (a ↦ inl. a, b ↦ inr. b))

def type_coproduct_copair (A B X : Type) (w : Product (A → X) (B → X)) : Sum A B → X
  ≔ [ inl. a ↦ w .fst a | inr. b ↦ w .snd b ]

def type_coproduct_copair_eta (A B X : Type) (f : Sum A B → X) (z : Sum A B)
  : Id X (type_coproduct_copair A B X (a ↦ f (inl. a), b ↦ f (inr. b)) z) (f z)
  ≔ match z [ inl. a ↦ refl (f (inl. a)) | inr. b ↦ refl (f (inr. b)) ]

def type_coproduct_universal_equiv (A B X : Type) : Equiv (Sum A B → X) (Product (A → X) (B → X))
  ≔ quasi_inverse_equiv (Sum A B → X) (Product (A → X) (B → X))
      (f ↦ (a ↦ f (inl. a), b ↦ f (inr. b)))
      (type_coproduct_copair A B X)
      (f ↦ funext (Sum A B) (_ ↦ X) (type_coproduct_copair A B X (a ↦ f (inl. a), b ↦ f (inr. b))) f
        (type_coproduct_copair_eta A B X f))
      (w ↦ refl w)

def type_coproduct_cocone_is_coproduct (A B : Type) : IsCoproductCocone TypeWild A B (type_coproduct_cocone A B)
  ≔ X ↦
    let e ≔ type_coproduct_universal_equiv A B (X .fst) in
    contractible_retract (BookFiber (Sum A B → X .fst) (Product (A → X .fst) (B → X .fst)) (e .map) (X .snd))
      (CoconeFactorization TypeWild A B (type_coproduct_cocone A B) X)
      (native_contraction (BookFiber (Sum A B → X .fst) (Product (A → X .fst) (B → X .fst)) (e .map) (X .snd))
        (book_equivalence (Sum A B → X .fst) (Product (A → X .fst) (B → X .fst)) e .equiv (X .snd)))
      (t ↦ (t .fst, (t .snd .fst, t .snd .snd)))
      (s ↦ (s .fst, (s .snd .fst, s .snd .snd)))
      (s ↦ refl s)

{` Litmus: the cocone (Bool, id, const true) under Bool, Unit factors
   through Bool ⊔ Unit by the map sending inr ⋆ to true and inl x to x. `}
def coproduct_litmus_cocone : CatCocone TypeWild Bool Unit ≔ (Bool, (x ↦ x, _ ↦ true.))

def coproduct_litmus_factor
  : Product
      (Id Bool (type_coproduct_cocone_is_coproduct Bool Unit coproduct_litmus_cocone .center .fst (inr. star.)) true.)
      (Id Bool (type_coproduct_cocone_is_coproduct Bool Unit coproduct_litmus_cocone .center .fst (inl. false.)) false.)
  ≔ (refl (true. : Bool), refl (false. : Bool))
