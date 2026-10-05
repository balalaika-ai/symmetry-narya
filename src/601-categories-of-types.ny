export "600-wild-precategories"

{` Chapter 6, section 6.2: the wild category of types, full
   subcategories, the category of sets and path groupoids. `}

{` The wild category of types (rem:wild, first bullet after def:category):
   objects Type, arrows A → B; λ, ρ and α are reflexivities. `}
def TypeWild : WildPrecat
  ≔ (ob ≔ Type,
     hom ≔ A B ↦ A → B,
     idn ≔ A ↦ x ↦ x,
     comp ≔ A B C g f ↦ x ↦ g (f x),
     lu ≔ A B f ↦ refl f,
     ru ≔ A B f ↦ refl f,
     assoc ≔ A B C D f g h ↦ refl (x ↦ h (g (f x))))

{` Isomorphisms in the wild category of types are exactly equivalences:
   isIso(f) is biinvertibility with identifications of functions. `}
def type_is_iso_to_equiv (A B : Type) (f : A → B) (i : CatIsIso TypeWild A B f) : isEquiv A B f
  ≔ biinvertible_equiv A B f (i .fst .fst) (b ↦ i .fst .snd (refl b))
      (i .snd .fst) (a ↦ i .snd .snd (refl a)) .equiv

def type_equiv_to_is_iso (A B : Type) (f : A → B) (h : isEquiv A B f) : CatIsIso TypeWild A B f
  ≔ let e : Equiv A B ≔ (f, h) in
    ((equiv_inverse_map A B e,
      funext B (_ ↦ B) (x ↦ f (equiv_inverse_map A B e x)) (x ↦ x) (equiv_counit A B e)),
     (equiv_inverse_map A B e,
      funext A (_ ↦ A) (x ↦ equiv_inverse_map A B e (f x)) (x ↦ x) (equiv_retraction A B e)))

def type_iso_equiv (A B : Type) : Equiv (CatIso TypeWild A B) (Equiv A B)
  ≔ compose_equiv (CatIso TypeWild A B) (Σ (A → B) (isEquiv A B)) (Equiv A B)
      (family_equiv (A → B) (f ↦ CatIsIso TypeWild A B f) (isEquiv A B)
        (f ↦ iff_equiv (CatIsIso TypeWild A B f) (isEquiv A B f)
          (cat_is_iso_prop TypeWild A B f) (isequiv_isprop A B f)
          (type_is_iso_to_equiv A B f) (type_equiv_to_is_iso A B f)))
      (canonical_inverse_equiv (Equiv A B) (Σ (A → B) (isEquiv A B)) (equiv_sigma_equiv A B))

{` "It is univalent by the Univalence Axiom." `}
def type_wild_univalent : IsUnivalentCat TypeWild
  ≔ cat_univalent_from_equivalences TypeWild (A B ↦
      compose_equiv (Id Type A B) (Equiv A B) (CatIso TypeWild A B) (univalence_equiv A B)
        (canonical_inverse_equiv (CatIso TypeWild A B) (Equiv A B) (type_iso_equiv A B)))

def TypeWildCategory : WildCategory ≔ (TypeWild, type_wild_univalent)

{` def:full-subcat: the full (wide) subprecategory on a predicate
   P : Ob(C) → Prop, with objects Ob(C)_P (SubtypeCarrier) and all other
   structure inherited from C. `}
def FullSubcat (C : WildPrecat) (P : Subtypes (C .ob)) : WildPrecat
  ≔ (ob ≔ SubtypeCarrier (C .ob) P,
     hom ≔ x y ↦ C .hom (x .fst) (y .fst),
     idn ≔ x ↦ C .idn (x .fst),
     comp ≔ x y z ↦ C .comp (x .fst) (y .fst) (z .fst),
     lu ≔ x y ↦ C .lu (x .fst) (y .fst),
     ru ≔ x y ↦ C .ru (x .fst) (y .fst),
     assoc ≔ x y z w ↦ C .assoc (x .fst) (y .fst) (z .fst) (w .fst))

{` def:full-subcat: "It is non-wild/univalent, if C is". `}
def full_subcat_homset (C : WildPrecat) (P : Subtypes (C .ob)) (hs : HasHomSets C)
  : HasHomSets (FullSubcat C P)
  ≔ x y ↦ hs (x .fst) (y .fst)

def full_subcat_univalent (C : WildPrecat) (P : Subtypes (C .ob)) (u : IsUnivalentCat C)
  : IsUnivalentCat (FullSubcat C P)
  ≔ cat_univalent_from_equivalences (FullSubcat C P) (x y ↦
      compose_equiv (Id (SubtypeCarrier (C .ob) P) x y) (Id (C .ob) (x .fst) (y .fst))
        (CatIso C (x .fst) (y .fst))
        (subtype_path_equiv (C .ob) (t ↦ P t .fst) (t ↦ P t .snd) x y)
        (cat_idtoiso_equiv C u (x .fst) (y .fst)))

def full_subcat_precat (C : Precat) (P : Subtypes (C .wild .ob)) : Precat
  ≔ (FullSubcat (C .wild) P, full_subcat_homset (C .wild) P (C .homset))

def full_subcat_category (C : Category) (P : Subtypes (C .wild .ob)) : Category
  ≔ (FullSubcat (C .wild) P, full_subcat_homset (C .wild) P (C .homset),
     full_subcat_univalent (C .wild) P (C .univalent))

{` The category of sets: the full subcategory of the wild category of
   types on the sets. Its objects are exactly SetTypes (checked below). `}
def SetPredicate : Subtypes Type ≔ A ↦ (isSet A, isset_isprop A)

def SetWild : WildPrecat ≔ FullSubcat TypeWild SetPredicate

def set_wild_objects : Id Type (SetWild .ob) SetTypes ≔ refl SetTypes

def set_wild_homset : HasHomSets SetWild
  ≔ A B ↦ pi_set (A .fst) (_ ↦ B .fst) (_ ↦ B .snd)

def SetCat : Category
  ≔ (SetWild, set_wild_homset, full_subcat_univalent TypeWild SetPredicate type_wild_univalent)

{` Litmus: in the category of sets, the composite of the negation of Bool
   with itself is computed pointwise, and negation is an isomorphism. `}
def set_cat_bool : SetCat .wild .ob ≔ (Bool, bool_set)

def set_cat_negation_twice
  : Id Bool (SetCat .wild .comp set_cat_bool set_cat_bool set_cat_bool bool_not bool_not true.) true.
  ≔ refl (true. : Bool)

def set_cat_negation_iso : CatIso (SetCat .wild) set_cat_bool set_cat_bool
  ≔ (bool_not,
     ((bool_not, funext Bool (_ ↦ Bool) (x ↦ bool_not (bool_not x)) (x ↦ x) bool_not_involutive),
      (bool_not, funext Bool (_ ↦ Bool) (x ↦ bool_not (bool_not x)) (x ↦ x) bool_not_involutive)))

{` ex:path-groupoid: the wild path groupoid of a type X; arrows x = y,
   composition q ∘ p = p · q, identities refl. `}
def PathWild (X : Type) : WildPrecat
  ≔ (ob ≔ X,
     hom ≔ x y ↦ Id X x y,
     idn ≔ x ↦ refl x,
     comp ≔ x y z q p ↦ concat X x y z p q,
     lu ≔ x y p ↦ concat_p1 X x y p,
     ru ≔ x y p ↦ concat_1p X x y p,
     assoc ≔ x y z w p q r ↦ concat_assoc X x y z w p q r)

{` "The arrows are invertible, since paths are always invertible." `}
def path_wild_invertible (X : Type) : IsPregroupoid (PathWild X)
  ≔ x y p ↦ ((inverse X x y p, concat_inverse_left X x y p),
              (inverse X x y p, concat_inverse_right X x y p))

def path_wild_iso_equiv (X : Type) (x y : X) : Equiv (Id X x y) (CatIso (PathWild X) x y)
  ≔ quasi_inverse_equiv (Id X x y) (CatIso (PathWild X) x y)
      (p ↦ (p, path_wild_invertible X x y p)) (e ↦ e .fst)
      (p ↦ refl p)
      (e ↦ cat_iso_path (PathWild X) x y (e .fst, path_wild_invertible X x y (e .fst)) e (refl (e .fst)))

def path_wild_univalent (X : Type) : IsUnivalentCat (PathWild X)
  ≔ cat_univalent_from_equivalences (PathWild X) (path_wild_iso_equiv X)

{` ex:path-groupoid: every type gives a wild groupoid. `}
def PathGroupoid (X : Type) : WildGroupoid
  ≔ (PathWild X, path_wild_univalent X, path_wild_invertible X)

{` ex:path-groupoid: "If X is a 1-type, then this structure is a groupoid." `}
def path_groupoid_of_groupoid (X : Type) (h : isGroupoid X) : GroupoidCat
  ≔ (PathWild X, h, path_wild_univalent X, path_wild_invertible X)
