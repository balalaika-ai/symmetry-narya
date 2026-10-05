export "604-wild-pointed-types"
export "43-set-truncation"

{` Chapter 6 (cats.tex): the (pre)category Set^A of families of sets used
   for ex:Sigma-Pi-adj. The wild category of families of types FamilyWild
   (the bullet after def:category, with univalence family_wild_univalent)
   is defined in module 604 and reused here; the book writes its arrows as
   (X →_B Y) ≔ Π_{b:B} X(b) → Y(b), mixing the names of the base and of the
   families. `}

{` Families of sets over A with fiberwise maps (the book's Set^A in
   ex:Sigma-Pi-adj); a precategory since fiberwise maps between families of
   sets form a set. By xca:path-core-adj these are the functors from the
   path groupoid of A to Set. `}
def FamilySetWild (A : Type) : WildPrecat
  ≔ (ob ≔ A → SetTypes,
     hom ≔ P Q ↦ (a : A) → P a .fst → Q a .fst,
     idn ≔ P ↦ a y ↦ y,
     comp ≔ P Q R g f ↦ a y ↦ g a (f a y),
     lu ≔ P Q f ↦ refl f,
     ru ≔ P Q f ↦ refl f,
     assoc ≔ P Q R S f g h ↦ refl ((a y ↦ h a (g a (f a y))) : (a : A) → P a .fst → S a .fst))

def family_set_homset (A : Type) : HasHomSets (FamilySetWild A)
  ≔ P Q ↦ pi_set A (a ↦ P a .fst → Q a .fst) (a ↦ pi_set (P a .fst) (_ ↦ Q a .fst) (_ ↦ Q a .snd))

def FamilySetPrecat (A : Type) : Precat ≔ (FamilySetWild A, family_set_homset A)

{` Litmus: a family over Bool and a fiberwise map computed by refl; the
   fiberwise negation is an isomorphism, and the corresponding identification
   of families exists by univalence. `}
def family_litmus_family : Bool → Type ≔ [ false. ↦ Unit | true. ↦ Bool ]

def family_litmus_map : FamilyWild Bool .hom family_litmus_family family_litmus_family
  ≔ [ false. ↦ u ↦ u | true. ↦ bool_not ]

def family_litmus_composite
  : Id Bool (FamilyWild Bool .comp family_litmus_family family_litmus_family family_litmus_family
      family_litmus_map family_litmus_map true. true.) true.
  ≔ refl (true. : Bool)

def family_litmus_is_iso : CatIsIso (FamilyWild Bool) family_litmus_family family_litmus_family family_litmus_map
  ≔ family_fiberwise_equiv_iso Bool family_litmus_family family_litmus_family family_litmus_map
      [ false. ↦ identity_equiv Unit .equiv | true. ↦ bool_not_equiv .equiv ]

def family_litmus_path : Id (Bool → Type) family_litmus_family family_litmus_family
  ≔ cat_isotoid (FamilyWild Bool) (family_wild_univalent Bool) family_litmus_family family_litmus_family
      (family_litmus_map, family_litmus_is_iso)
