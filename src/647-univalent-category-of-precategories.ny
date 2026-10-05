export "644-wild-precategory-of-wild-precategories"
export "646-category-identity"

{` Chapter 6, xca:wildcat-of-precats. The wild full subprecategory PreCat
   of WildPrecatWild on the precategories is univalent, and so is the
   further full subcategory Cat on the categories.

   An isomorphism F : C ≅ D in PreCat (functors G, H with F ∘ G = id and
   H ∘ F = id) is the same as an isomorphism of precategories (F fully
   faithful and an equivalence on objects): both are propositions, the
   forward direction uses the object and arrow components of the
   identifications, the backward direction path induction via
   precategory_path_equiv (module 645). Univalence then follows from
   (C = D) ≃ (C ≅ D) as precategories. `}

def PrecatPredicate : Subtypes WildPrecat ≔ C ↦ (HasHomSets C, has_hom_sets_prop C)

def PreCatWild : WildPrecat ≔ FullSubcat WildPrecatWild PrecatPredicate

def precat_wild_object (x : PreCatWild .ob) : Precat ≔ (x .fst, x .snd)

def precat_wild_object_equiv : Equiv (PreCatWild .ob) Precat
  ≔ quasi_inverse_equiv (PreCatWild .ob) Precat precat_wild_object (C ↦ (C .wild, C .homset))
      (x ↦ refl x) (C ↦ refl C)

{` A functor identified with the identity functor acts by equivalences on
   arrows. `}
def functor_path_identity_mor_equiv (D : WildPrecat) (K : WildFunctor D D)
  (P : Id (WildFunctor D D) K (functor_identity D)) (a b : D .ob)
  : isEquiv (D .hom a b) (D .hom (K .obj a) (K .obj b)) (K .mor a b)
  ≔ J (WildFunctor D D) (functor_identity D)
      (K' _ ↦ (a' b' : D .ob) → isEquiv (D .hom a' b') (D .hom (K' .obj a') (K' .obj b')) (K' .mor a' b'))
      (a' b' ↦ identity_equiv (D .hom a' b') .equiv) K
      (inverse (WildFunctor D D) K (functor_identity D) P) a b

def ch6c_transport2 (A : Type) (Q : A → A → Type) (a a' b b' : A) (p : Id A a a') (q : Id A b b') (t : Q a b)
  : Q a' b'
  ≔ transport A (z ↦ Q a' z) b b' q (transport A (z ↦ Q z b) a a' p t)

{` Forward: an isomorphism in PreCat is fully faithful and an equivalence
   on objects. `}
def precat_wild_iso_to_precat_iso (x y : PreCatWild .ob) (F : WildFunctor (x .fst) (y .fst))
  (i : CatIsIso PreCatWild x y F)
  : Product (IsFullyFaithful (x .fst) (y .fst) F) (BookIsEquiv (x .fst .ob) (y .fst .ob) (F .obj))
  ≔ let C ≔ x .fst in
    let D ≔ y .fst in
    let G ≔ i .fst .fst in
    let H ≔ i .snd .fst in
    let p ≔ i .fst .snd in
    let q ≔ i .snd .snd in
    let FG ≔ functor_compose D C D F G in
    let HF ≔ functor_compose C D C H F in
    let fs : (z : D .ob) → Id (D .ob) (F .obj (G .obj z)) z ≔ z ↦ p .obj (refl z) in
    let rf : (c : C .ob) → Id (C .ob) (H .obj (F .obj c)) c ≔ c ↦ q .obj (refl c) in
    let obj_equiv : Equiv (C .ob) (D .ob) ≔ biinvertible_equiv (C .ob) (D .ob) (F .obj) (G .obj) fs (H .obj) rf in
    let r : (c : C .ob) → Id (C .ob) (G .obj (F .obj c)) c
      ≔ c ↦ concat (C .ob) (G .obj (F .obj c)) (H .obj (F .obj (G .obj (F .obj c)))) c
          (inverse (C .ob) (H .obj (F .obj (G .obj (F .obj c)))) (G .obj (F .obj c)) (rf (G .obj (F .obj c))))
          (concat (C .ob) (H .obj (F .obj (G .obj (F .obj c)))) (H .obj (F .obj c)) c
            (refl (H .obj) (fs (F .obj c))) (rf c)) in
    let fg_eq ≔ functor_path_identity_mor_equiv D FG p in
    let hf_eq ≔ functor_path_identity_mor_equiv C HF q in
    let mid : (z w : D .ob) → isEquiv (C .hom (G .obj z) (G .obj w)) (D .hom (F .obj (G .obj z)) (F .obj (G .obj w)))
        (F .mor (G .obj z) (G .obj w))
      ≔ z w ↦ ch6c_two_out_of_six (D .hom z w) (C .hom (G .obj z) (G .obj w))
          (D .hom (F .obj (G .obj z)) (F .obj (G .obj w)))
          (C .hom (H .obj (F .obj (G .obj z))) (H .obj (F .obj (G .obj w))))
          (G .mor z w) (F .mor (G .obj z) (G .obj w)) (H .mor (F .obj (G .obj z)) (F .obj (G .obj w)))
          (fg_eq z w) (hf_eq (G .obj z) (G .obj w)) in
    (ff_from_mor_equivs C D F (a b ↦
       ch6c_transport2 (C .ob) (a' b' ↦ isEquiv (C .hom a' b') (D .hom (F .obj a') (F .obj b')) (F .mor a' b'))
         (G .obj (F .obj a)) a (G .obj (F .obj b)) b (r a) (r b) (mid (F .obj a) (F .obj b))),
     book_equivalence (C .ob) (D .ob) obj_equiv .equiv)

{` Backward: by path induction, the functor of the isomorphism of
   precategories attached to an identification is an isomorphism in
   PreCat. `}
def precat_path_functor_is_iso (x : PreCatWild .ob) (D : Precat) (p : Id Precat (precat_wild_object x) D)
  : CatIsIso PreCatWild x (D .wild, D .homset) (precategory_path_to_isomorphism (precat_wild_object x) D p .fst)
  ≔ J Precat (precat_wild_object x)
      (D p ↦ CatIsIso PreCatWild x (D .wild, D .homset) (precategory_path_to_isomorphism (precat_wild_object x) D p .fst))
      (cat_is_iso_transport PreCatWild x x (functor_identity (x .fst))
        (precategory_path_to_isomorphism (precat_wild_object x) (precat_wild_object x) (refl (precat_wild_object x)) .fst)
        (precategory_path_to_isomorphism_refl (precat_wild_object x) .fst)
        (cat_identity_is_iso PreCatWild x))
      D p

{` Every isomorphism of precategories is the image of an identification;
   stated for an abstract proof that the path-induction map is an
   equivalence, so that its inverse is never evaluated. `}
def precat_iso_property_from_paths (px : Precat) (Q : (D : Precat) → PrecatIsomorphism px D → Type)
  (base : (D : Precat) (p : Id Precat px D) → Q D (precategory_path_to_isomorphism px D p))
  (e : (D : Precat) → isEquiv (Id Precat px D) (PrecatIsomorphism px D) (precategory_path_to_isomorphism px D))
  (D : Precat) (i : PrecatIsomorphism px D) : Q D i
  ≔ let eq : Equiv (Id Precat px D) (PrecatIsomorphism px D) ≔ (precategory_path_to_isomorphism px D, e D) in
    transport (PrecatIsomorphism px D) (Q D)
      (precategory_path_to_isomorphism px D (equiv_inverse_map (Id Precat px D) (PrecatIsomorphism px D) eq i)) i
      (equiv_counit (Id Precat px D) (PrecatIsomorphism px D) eq i)
      (base D (equiv_inverse_map (Id Precat px D) (PrecatIsomorphism px D) eq i))

def precat_iso_to_precat_wild_iso (x y : PreCatWild .ob) (F : WildFunctor (x .fst) (y .fst))
  (w : Product (IsFullyFaithful (x .fst) (y .fst) F) (BookIsEquiv (x .fst .ob) (y .fst .ob) (F .obj)))
  : CatIsIso PreCatWild x y F
  ≔ precat_iso_property_from_paths (precat_wild_object x)
      (D i ↦ CatIsIso PreCatWild x (D .wild, D .homset) (i .fst))
      (D p ↦ precat_path_functor_is_iso x D p)
      (D ↦ precategory_path_to_isomorphism_is_equiv (precat_wild_object x) D)
      (precat_wild_object y) (F, w)

def precat_iso_precat_wild_iso_equiv (x y : PreCatWild .ob)
  : Equiv (PrecatIsomorphism (precat_wild_object x) (precat_wild_object y)) (CatIso PreCatWild x y)
  ≔ let C ≔ x .fst in
    let D ≔ y .fst in
    family_equiv (WildFunctor C D)
      (F ↦ Product (IsFullyFaithful C D F) (BookIsEquiv (C .ob) (D .ob) (F .obj)))
      (CatIsIso PreCatWild x y)
      (F ↦ iff_equiv (Product (IsFullyFaithful C D F) (BookIsEquiv (C .ob) (D .ob) (F .obj))) (CatIsIso PreCatWild x y F)
        (product_prop (IsFullyFaithful C D F) (BookIsEquiv (C .ob) (D .ob) (F .obj))
          (is_fully_faithful_prop C D F) (book_isequiv_isprop (C .ob) (D .ob) (F .obj)))
        (cat_is_iso_prop PreCatWild x y F)
        (precat_iso_to_precat_wild_iso x y F)
        (precat_wild_iso_to_precat_iso x y F))

{` xca:wildcat-of-precats: PreCat is univalent. `}
def precat_wild_path_iso_equiv (x y : PreCatWild .ob) : Equiv (Id (PreCatWild .ob) x y) (CatIso PreCatWild x y)
  ≔ let px ≔ precat_wild_object x in
    let py ≔ precat_wild_object y in
    compose_equiv (Id (PreCatWild .ob) x y) (Id Precat px py) (CatIso PreCatWild x y)
      (equivalence_on_paths (PreCatWild .ob) Precat precat_wild_object_equiv x y)
      (compose_equiv (Id Precat px py) (PrecatIsomorphism px py) (CatIso PreCatWild x y)
        (native_equivalence (Id Precat px py) (PrecatIsomorphism px py) (precategory_path_equiv px py))
        (precat_iso_precat_wild_iso_equiv x y))

def precat_wild_univalent : IsUnivalentCat PreCatWild
  ≔ cat_univalent_from_equivalences PreCatWild precat_wild_path_iso_equiv

{` "Conclude that the further wild full subcategory Cat on the categories
   is univalent as well." `}
def CategoryPredicate : Subtypes (PreCatWild .ob) ≔ x ↦ (IsUnivalentCat (x .fst), is_univalent_cat_prop (x .fst))

def CatWild : WildPrecat ≔ FullSubcat PreCatWild CategoryPredicate

def cat_wild_univalent : IsUnivalentCat CatWild
  ≔ full_subcat_univalent PreCatWild CategoryPredicate precat_wild_univalent

def CatWildCategory : WildCategory ≔ (CatWild, cat_wild_univalent)

{` Litmus: the category of sets is an object of Cat, and its identity
   functor is an isomorphism there whose underlying isomorphism of
   precategories has the identity on objects. `}
def set_cat_in_cat_wild : CatWild .ob ≔ ((SetCat .wild, SetCat .homset), SetCat .univalent)

def set_cat_identity_iso_in_cat_wild : CatIso CatWild set_cat_in_cat_wild set_cat_in_cat_wild
  ≔ cat_identity_iso CatWild set_cat_in_cat_wild

def set_cat_in_cat_wild_objects : Id Type (set_cat_in_cat_wild .fst .fst .ob) SetTypes
  ≔ refl SetTypes
