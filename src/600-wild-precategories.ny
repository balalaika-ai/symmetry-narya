export "29-propositional-truncation"

{` Chapter 6 (cats.tex), section 6.2. Core notions: wild precategories,
   precategories, isomorphisms, univalence and categories.

   Conventions. Composition is written comp a b c g f for g ∘ f with
   f : hom a b and g : hom b c, as in the footnote to def:wild-cat. The unit
   and associativity laws have the book's orientations
   λ : id_B ∘ f = f, ρ : f ∘ id_A = f, α : h ∘ (g ∘ f) = (h ∘ g) ∘ f. `}

{` def:wild-cat (struc:cat-ob, struc:cat-mor, struc:cat-id, struc:cat-comp,
   struc:cat-unit-laws, struct:cat-assoc). `}
def WildPrecat : Type ≔ sig (
  ob : Type,
  hom : ob → ob → Type,
  idn : (a : ob) → hom a a,
  comp : (a b c : ob) → hom b c → hom a b → hom a c,
  lu : (a b : ob) (f : hom a b) → Id (hom a b) (comp a b b (idn b) f) f,
  ru : (a b : ob) (f : hom a b) → Id (hom a b) (comp a a b f (idn a)) f,
  assoc : (a b c d : ob) (f : hom a b) (g : hom b c) (h : hom c d)
    → Id (hom a d) (comp a c d h (comp a b c g f)) (comp a b d (comp b c d h g) f) )

{` def:precategory: all hom types are sets. A precategory is a wild
   precategory together with this property. `}
def HasHomSets (C : WildPrecat) : Type ≔ (a b : C .ob) → isSet (C .hom a b)

def has_hom_sets_prop (C : WildPrecat) : isProp (HasHomSets C)
  ≔ pi_prop (C .ob) (a ↦ (b : C .ob) → isSet (C .hom a b))
      (a ↦ pi_prop (C .ob) (b ↦ isSet (C .hom a b)) (b ↦ isset_isprop (C .hom a b)))

def Precat : Type ≔ sig (wild : WildPrecat, homset : HasHomSets wild)

{` def:iso-in-cat. The displayed type isIso(f): a right inverse g with
   f ∘ g = id_B and a left inverse h with h ∘ f = id_A (the displayed
   orientation; the prose before it writes the identifications reversed). `}
def CatIsIso (C : WildPrecat) (a b : C .ob) (f : C .hom a b) : Type
  ≔ Product (Σ (C .hom b a) (g ↦ Id (C .hom b b) (C .comp b a b f g) (C .idn b)))
      (Σ (C .hom b a) (h ↦ Id (C .hom a a) (C .comp a b a h f) (C .idn a)))

def CatIso (C : WildPrecat) (a b : C .ob) : Type ≔ Σ (C .hom a b) (f ↦ CatIsIso C a b f)

{` Every identity arrow is an isomorphism. `}
def cat_identity_is_iso (C : WildPrecat) (a : C .ob) : CatIsIso C a a (C .idn a)
  ≔ ((C .idn a, C .lu a a (C .idn a)), (C .idn a, C .lu a a (C .idn a)))

def cat_identity_iso (C : WildPrecat) (a : C .ob) : CatIso C a a
  ≔ (C .idn a, cat_identity_is_iso C a)

{` A map with a section and a retraction (a biinvertible map) is an
   equivalence. `}
def biinvertible_equiv (A B : Type) (f : A → B) (s : B → A) (fs : (b : B) → Id B (f (s b)) b)
  (r : B → A) (rf : (a : A) → Id A (r (f a)) a) : Equiv A B
  ≔ quasi_inverse_equiv A B f s
      (a ↦ concat A (s (f a)) (r (f a)) a
        (concat A (s (f a)) (r (f (s (f a)))) (r (f a))
          (inverse A (r (f (s (f a)))) (s (f a)) (rf (s (f a))))
          (refl r (fs (f a))))
        (rf a)) fs

{` Path algebra in a wild precategory: whiskering an identification. `}
def cat_whisker_left (C : WildPrecat) (a b c : C .ob) (g : C .hom b c) (f f' : C .hom a b)
  (p : Id (C .hom a b) f f') : Id (C .hom a c) (C .comp a b c g f) (C .comp a b c g f')
  ≔ refl ((k ↦ C .comp a b c g k) : C .hom a b → C .hom a c) p

def cat_whisker_right (C : WildPrecat) (a b c : C .ob) (g g' : C .hom b c) (f : C .hom a b)
  (p : Id (C .hom b c) g g') : Id (C .hom a c) (C .comp a b c g f) (C .comp a b c g' f)
  ≔ refl ((k ↦ C .comp a b c k f) : C .hom b c → C .hom a c) p

{` The footnote to def:iso-in-cat: for an isomorphism f : a → b, the maps
   f ∘ - and - ∘ f are equivalences, using only λ, ρ and α. `}
def cat_postcompose_section (C : WildPrecat) (a b : C .ob) (f : C .hom a b) (i : CatIsIso C a b f)
  (x : C .ob) (m : C .hom x b)
  : Id (C .hom x b) (C .comp x a b f (C .comp x b a (i .fst .fst) m)) m
  ≔ let g ≔ i .fst .fst in
    concat (C .hom x b) (C .comp x a b f (C .comp x b a g m)) (C .comp x b b (C .idn b) m) m
      (concat (C .hom x b) (C .comp x a b f (C .comp x b a g m)) (C .comp x b b (C .comp b a b f g) m)
        (C .comp x b b (C .idn b) m)
        (C .assoc x b a b m g f)
        (cat_whisker_right C x b b (C .comp b a b f g) (C .idn b) m (i .fst .snd)))
      (C .lu x b m)

def cat_postcompose_retraction (C : WildPrecat) (a b : C .ob) (f : C .hom a b) (i : CatIsIso C a b f)
  (x : C .ob) (k : C .hom x a)
  : Id (C .hom x a) (C .comp x b a (i .snd .fst) (C .comp x a b f k)) k
  ≔ let h ≔ i .snd .fst in
    concat (C .hom x a) (C .comp x b a h (C .comp x a b f k)) (C .comp x a a (C .idn a) k) k
      (concat (C .hom x a) (C .comp x b a h (C .comp x a b f k)) (C .comp x a a (C .comp a b a h f) k)
        (C .comp x a a (C .idn a) k)
        (C .assoc x a b a k f h)
        (cat_whisker_right C x a a (C .comp a b a h f) (C .idn a) k (i .snd .snd)))
      (C .lu x a k)

def cat_postcompose_equiv (C : WildPrecat) (a b : C .ob) (f : C .hom a b) (i : CatIsIso C a b f)
  (x : C .ob) : Equiv (C .hom x a) (C .hom x b)
  ≔ biinvertible_equiv (C .hom x a) (C .hom x b) (k ↦ C .comp x a b f k)
      (m ↦ C .comp x b a (i .fst .fst) m) (cat_postcompose_section C a b f i x)
      (m ↦ C .comp x b a (i .snd .fst) m) (cat_postcompose_retraction C a b f i x)

def cat_precompose_section (C : WildPrecat) (a b : C .ob) (f : C .hom a b) (i : CatIsIso C a b f)
  (x : C .ob) (m : C .hom a x)
  : Id (C .hom a x) (C .comp a b x (C .comp b a x m (i .snd .fst)) f) m
  ≔ let h ≔ i .snd .fst in
    concat (C .hom a x) (C .comp a b x (C .comp b a x m h) f) (C .comp a a x m (C .idn a)) m
      (concat (C .hom a x) (C .comp a b x (C .comp b a x m h) f) (C .comp a a x m (C .comp a b a h f))
        (C .comp a a x m (C .idn a))
        (inverse (C .hom a x) (C .comp a a x m (C .comp a b a h f)) (C .comp a b x (C .comp b a x m h) f)
          (C .assoc a b a x f h m))
        (cat_whisker_left C a a x m (C .comp a b a h f) (C .idn a) (i .snd .snd)))
      (C .ru a x m)

def cat_precompose_retraction (C : WildPrecat) (a b : C .ob) (f : C .hom a b) (i : CatIsIso C a b f)
  (x : C .ob) (k : C .hom b x)
  : Id (C .hom b x) (C .comp b a x (C .comp a b x k f) (i .fst .fst)) k
  ≔ let g ≔ i .fst .fst in
    concat (C .hom b x) (C .comp b a x (C .comp a b x k f) g) (C .comp b b x k (C .idn b)) k
      (concat (C .hom b x) (C .comp b a x (C .comp a b x k f) g) (C .comp b b x k (C .comp b a b f g))
        (C .comp b b x k (C .idn b))
        (inverse (C .hom b x) (C .comp b b x k (C .comp b a b f g)) (C .comp b a x (C .comp a b x k f) g)
          (C .assoc b a b x g f k))
        (cat_whisker_left C b b x k (C .comp b a b f g) (C .idn b) (i .fst .snd)))
      (C .ru b x k)

def cat_precompose_equiv (C : WildPrecat) (a b : C .ob) (f : C .hom a b) (i : CatIsIso C a b f)
  (x : C .ob) : Equiv (C .hom b x) (C .hom a x)
  ≔ biinvertible_equiv (C .hom b x) (C .hom a x) (k ↦ C .comp a b x k f)
      (m ↦ C .comp b a x m (i .snd .fst)) (cat_precompose_section C a b f i x)
      (m ↦ C .comp b a x m (i .fst .fst)) (cat_precompose_retraction C a b f i x)

{` The footnote to def:iso-in-cat: isIso(f) is a proposition, in any wild
   precategory. If f is an isomorphism, both factors are fibers of the
   equivalences f ∘ - and - ∘ f, hence contractible. `}
def cat_is_iso_contractible (C : WildPrecat) (a b : C .ob) (f : C .hom a b) (i : CatIsIso C a b f)
  : isContr (CatIsIso C a b f)
  ≔ sigma_contractible (Σ (C .hom b a) (g ↦ Id (C .hom b b) (C .comp b a b f g) (C .idn b)))
      (_ ↦ Σ (C .hom b a) (h ↦ Id (C .hom a a) (C .comp a b a h f) (C .idn a)))
      (cat_postcompose_equiv C a b f i b .equiv (C .idn b))
      (_ ↦ cat_precompose_equiv C a b f i a .equiv (C .idn a))

def cat_is_iso_prop (C : WildPrecat) (a b : C .ob) (f : C .hom a b) : isProp (CatIsIso C a b f)
  ≔ u v ↦ contractible_prop (CatIsIso C a b f) (cat_is_iso_contractible C a b f u) u v

{` Two isomorphisms are identified as soon as their underlying arrows are. `}
def cat_iso_path (C : WildPrecat) (a b : C .ob) (e d : CatIso C a b)
  (p : Id (C .hom a b) (e .fst) (d .fst)) : Id (CatIso C a b) e d
  ≔ (p, pathover_of_eq (C .hom a b) (CatIsIso C a b) (e .fst) (d .fst) p (e .snd) (d .snd)
      (cat_is_iso_prop C a b (d .fst)
        (transport (C .hom a b) (CatIsIso C a b) (e .fst) (d .fst) p (e .snd)) (d .snd)))

def cat_iso_path_equiv (C : WildPrecat) (a b : C .ob) (e d : CatIso C a b)
  : Equiv (Id (CatIso C a b) e d) (Id (C .hom a b) (e .fst) (d .fst))
  ≔ subtype_path_equiv (C .hom a b) (CatIsIso C a b) (cat_is_iso_prop C a b) e d

{` In a precategory the type of isomorphisms is a set. `}
def cat_iso_set (C : WildPrecat) (hs : HasHomSets C) (a b : C .ob) : isSet (CatIso C a b)
  ≔ sigma_set (C .hom a b) (CatIsIso C a b) (hs a b)
      (f ↦ prop_is_set (CatIsIso C a b f) (cat_is_iso_prop C a b f))

{` def:univalent-cat. idtoiso is defined by path induction (Narya's J),
   sending refl a to id_a; the computation rule holds as the
   identification cat_idtoiso_refl, since J has only a typal beta rule. `}
def cat_idtoiso (C : WildPrecat) (a b : C .ob) (p : Id (C .ob) a b) : CatIso C a b
  ≔ J (C .ob) a (b _ ↦ CatIso C a b) (cat_identity_iso C a) b p

def cat_idtoiso_refl (C : WildPrecat) (a : C .ob)
  : Id (CatIso C a a) (cat_identity_iso C a) (cat_idtoiso C a a (refl a))
  ≔ Jβ (C .ob) a (b _ ↦ CatIso C a b) (cat_identity_iso C a)

def IsUnivalentCat (C : WildPrecat) : Type
  ≔ (a b : C .ob) → BookIsEquiv (Id (C .ob) a b) (CatIso C a b) (cat_idtoiso C a b)

def is_univalent_cat_prop (C : WildPrecat) : isProp (IsUnivalentCat C)
  ≔ pi_prop (C .ob) (a ↦ (b : C .ob) → BookIsEquiv (Id (C .ob) a b) (CatIso C a b) (cat_idtoiso C a b))
      (a ↦ pi_prop (C .ob) (b ↦ BookIsEquiv (Id (C .ob) a b) (CatIso C a b) (cat_idtoiso C a b))
        (b ↦ book_isequiv_isprop (Id (C .ob) a b) (CatIso C a b) (cat_idtoiso C a b)))

{` def:category: a wild category is a univalent wild precategory, a
   category is a univalent precategory (stored as the wild precategory
   with both properties). `}
def WildCategory : Type ≔ sig (wild : WildPrecat, univalent : IsUnivalentCat wild)

def Category : Type ≔ sig (wild : WildPrecat, homset : HasHomSets wild, univalent : IsUnivalentCat wild)

def category_precat (C : Category) : Precat ≔ (C .wild, C .homset)

def category_wild_category (C : Category) : WildCategory ≔ (C .wild, C .univalent)

def cat_idtoiso_equiv (C : WildPrecat) (u : IsUnivalentCat C) (a b : C .ob)
  : Equiv (Id (C .ob) a b) (CatIso C a b)
  ≔ native_equivalence (Id (C .ob) a b) (CatIso C a b) (cat_idtoiso C a b, u a b)

def cat_isotoid (C : WildPrecat) (u : IsUnivalentCat C) (a b : C .ob) (e : CatIso C a b) : Id (C .ob) a b
  ≔ equiv_inverse_map (Id (C .ob) a b) (CatIso C a b) (cat_idtoiso_equiv C u a b) e

def cat_idtoiso_isotoid (C : WildPrecat) (u : IsUnivalentCat C) (a b : C .ob) (e : CatIso C a b)
  : Id (CatIso C a b) (cat_idtoiso C a b (cat_isotoid C u a b e)) e
  ≔ equiv_counit (Id (C .ob) a b) (CatIso C a b) (cat_idtoiso_equiv C u a b) e

def cat_isotoid_idtoiso (C : WildPrecat) (u : IsUnivalentCat C) (a b : C .ob) (p : Id (C .ob) a b)
  : Id (Id (C .ob) a b) (cat_isotoid C u a b (cat_idtoiso C a b p)) p
  ≔ equiv_retraction (Id (C .ob) a b) (CatIso C a b) (cat_idtoiso_equiv C u a b) p

{` Criteria for univalence (fundamental theorem of identity types). `}
def cat_contractible_map_is_equiv (X Y : Type) (f : X → Y) (hX : isContr X) (hY : isContr Y)
  : isEquiv X Y f
  ≔ y ↦ sigma_contractible X (x ↦ Id Y (f x) y) hX
      (x ↦ prop_paths_contractible Y (contractible_prop Y hY) (f x) y)

def cat_univalent_from_contractible (C : WildPrecat)
  (h : (a : C .ob) → isContr (Σ (C .ob) (b ↦ CatIso C a b))) : IsUnivalentCat C
  ≔ a b ↦ book_equivalence (Id (C .ob) a b) (CatIso C a b)
      (cat_idtoiso C a b,
       fiberwise_from_total (C .ob) (b ↦ Id (C .ob) a b) (b ↦ CatIso C a b) (cat_idtoiso C a)
         (cat_contractible_map_is_equiv (Σ (C .ob) (b ↦ Id (C .ob) a b)) (Σ (C .ob) (b ↦ CatIso C a b))
           (totalize (C .ob) (b ↦ Id (C .ob) a b) (b ↦ CatIso C a b) (cat_idtoiso C a))
           (iscontr_idfrom (C .ob) a) (h a)) b) .equiv

{` Any family of equivalences (a = b) ≃ (a ≅ b), not necessarily idtoiso,
   already makes C univalent. `}
def cat_univalent_from_equivalences (C : WildPrecat)
  (e : (a b : C .ob) → Equiv (Id (C .ob) a b) (CatIso C a b)) : IsUnivalentCat C
  ≔ cat_univalent_from_contractible C (a ↦
      hlevel_equiv zero. (Σ (C .ob) (b ↦ Id (C .ob) a b)) (Σ (C .ob) (b ↦ CatIso C a b))
        (family_equiv (C .ob) (b ↦ Id (C .ob) a b) (b ↦ CatIso C a b) (e a))
        (iscontr_idfrom (C .ob) a))

def cat_univalent_iso_total_contractible (C : WildPrecat) (u : IsUnivalentCat C) (a : C .ob)
  : isContr (Σ (C .ob) (b ↦ CatIso C a b))
  ≔ hlevel_equiv zero. (Σ (C .ob) (b ↦ Id (C .ob) a b)) (Σ (C .ob) (b ↦ CatIso C a b))
      (family_equiv (C .ob) (b ↦ Id (C .ob) a b) (b ↦ CatIso C a b) (cat_idtoiso_equiv C u a))
      (iscontr_idfrom (C .ob) a)

{` lem:obj-gpd: the type of objects of a category is a groupoid, since
   each a = b is equivalent to the set a ≅ b. `}
def category_objects_groupoid (C : Category) : isGroupoid (C .wild .ob)
  ≔ a b ↦ hlevel_two_to_set (Id (C .wild .ob) a b)
      (hlevel_equiv (suc. (suc. zero.)) (CatIso (C .wild) a b) (Id (C .wild .ob) a b)
        (canonical_inverse_equiv (Id (C .wild .ob) a b) (CatIso (C .wild) a b)
          (cat_idtoiso_equiv (C .wild) (C .univalent) a b))
        (set_to_hlevel_two (CatIso (C .wild) a b) (cat_iso_set (C .wild) (C .homset) a b)))

{` def:wild-pre-groupoid: (wild) pregroupoids have all arrows invertible;
   (wild) groupoids are univalent (wild) pregroupoids. `}
def IsPregroupoid (C : WildPrecat) : Type ≔ (a b : C .ob) (f : C .hom a b) → CatIsIso C a b f

def is_pregroupoid_prop (C : WildPrecat) : isProp (IsPregroupoid C)
  ≔ pi_prop (C .ob) (a ↦ (b : C .ob) (f : C .hom a b) → CatIsIso C a b f)
      (a ↦ pi_prop (C .ob) (b ↦ (f : C .hom a b) → CatIsIso C a b f)
        (b ↦ pi_prop (C .hom a b) (f ↦ CatIsIso C a b f) (f ↦ cat_is_iso_prop C a b f)))

def WildPregroupoid : Type ≔ sig (wild : WildPrecat, invertible : IsPregroupoid wild)

def Pregroupoid : Type ≔ sig (wild : WildPrecat, homset : HasHomSets wild, invertible : IsPregroupoid wild)

def WildGroupoid : Type
  ≔ sig (wild : WildPrecat, univalent : IsUnivalentCat wild, invertible : IsPregroupoid wild)

def GroupoidCat : Type
  ≔ sig (wild : WildPrecat, homset : HasHomSets wild, univalent : IsUnivalentCat wild,
      invertible : IsPregroupoid wild)

def groupoid_cat_category (G : GroupoidCat) : Category ≔ (G .wild, G .homset, G .univalent)

{` Inverses and composites of isomorphisms. `}
def cat_iso_inverse (C : WildPrecat) (a b : C .ob) (e : CatIso C a b) : CatIso C b a
  ≔ let f ≔ e .fst in
    let g ≔ e .snd .fst .fst in
    let h ≔ e .snd .snd .fst in
    let hg : Id (C .hom b a) h g
      ≔ concat (C .hom b a) h (C .comp b b a h (C .comp b a b f g)) g
          (concat (C .hom b a) h (C .comp b b a h (C .idn b)) (C .comp b b a h (C .comp b a b f g))
            (inverse (C .hom b a) (C .comp b b a h (C .idn b)) h (C .ru b a h))
            (cat_whisker_left C b b a h (C .idn b) (C .comp b a b f g)
              (inverse (C .hom b b) (C .comp b a b f g) (C .idn b) (e .snd .fst .snd))))
          (concat (C .hom b a) (C .comp b b a h (C .comp b a b f g)) (C .comp b a a (C .comp a b a h f) g) g
            (C .assoc b a b a g f h)
            (concat (C .hom b a) (C .comp b a a (C .comp a b a h f) g) (C .comp b a a (C .idn a) g) g
              (cat_whisker_right C b a a (C .comp a b a h f) (C .idn a) g (e .snd .snd .snd))
              (C .lu b a g))) in
    (g, ((f, concat (C .hom a a) (C .comp a b a g f) (C .comp a b a h f) (C .idn a)
                (cat_whisker_right C a b a g h f (inverse (C .hom b a) h g hg)) (e .snd .snd .snd)),
         (f, e .snd .fst .snd)))

def cat_iso_compose (C : WildPrecat) (a b c : C .ob) (e2 : CatIso C b c) (e1 : CatIso C a b) : CatIso C a c
  ≔ let f ≔ e1 .fst in
    let g ≔ e2 .fst in
    let f' ≔ e1 .snd .fst .fst in
    let g' ≔ e2 .snd .fst .fst in
    let f'' ≔ e1 .snd .snd .fst in
    let g'' ≔ e2 .snd .snd .fst in
    (C .comp a b c g f,
     ((C .comp c b a f' g',
       concat (C .hom c c) (C .comp c a c (C .comp a b c g f) (C .comp c b a f' g'))
         (C .comp c b c g (C .comp c a b f (C .comp c b a f' g'))) (C .idn c)
         (inverse (C .hom c c) (C .comp c b c g (C .comp c a b f (C .comp c b a f' g')))
           (C .comp c a c (C .comp a b c g f) (C .comp c b a f' g'))
           (C .assoc c a b c (C .comp c b a f' g') f g))
         (concat (C .hom c c) (C .comp c b c g (C .comp c a b f (C .comp c b a f' g')))
           (C .comp c b c g g') (C .idn c)
           (cat_whisker_left C c b c g (C .comp c a b f (C .comp c b a f' g')) g'
             (concat (C .hom c b) (C .comp c a b f (C .comp c b a f' g'))
               (C .comp c b b (C .comp b a b f f') g') g'
               (C .assoc c b a b g' f' f)
               (concat (C .hom c b) (C .comp c b b (C .comp b a b f f') g') (C .comp c b b (C .idn b) g') g'
                 (cat_whisker_right C c b b (C .comp b a b f f') (C .idn b) g' (e1 .snd .fst .snd))
                 (C .lu c b g'))))
           (e2 .snd .fst .snd))),
      (C .comp c b a f'' g'',
       concat (C .hom a a) (C .comp a c a (C .comp c b a f'' g'') (C .comp a b c g f))
         (C .comp a b a (C .comp b c a (C .comp c b a f'' g'') g) f) (C .idn a)
         (C .assoc a b c a f g (C .comp c b a f'' g''))
         (concat (C .hom a a) (C .comp a b a (C .comp b c a (C .comp c b a f'' g'') g) f)
           (C .comp a b a f'' f) (C .idn a)
           (cat_whisker_right C a b a (C .comp b c a (C .comp c b a f'' g'') g) f'' f
             (concat (C .hom b a) (C .comp b c a (C .comp c b a f'' g'') g)
               (C .comp b b a f'' (C .comp b c b g'' g)) f''
               (inverse (C .hom b a) (C .comp b b a f'' (C .comp b c b g'' g))
                 (C .comp b c a (C .comp c b a f'' g'') g) (C .assoc b c b a g g'' f''))
               (concat (C .hom b a) (C .comp b b a f'' (C .comp b c b g'' g)) (C .comp b b a f'' (C .idn b)) f''
                 (cat_whisker_left C b b a f'' (C .comp b c b g'' g) (C .idn b) (e2 .snd .snd .snd))
                 (C .ru b a f''))))
           (e1 .snd .snd .snd)))))
