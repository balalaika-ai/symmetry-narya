export "1208-abelian-hom-pointwise"
export "686-category-of-groups"

{` Chapter 12, sec:ab-mon-closed-cat ("The category of abelian groups",
   abelian.tex 935; the section has no text in the pinned book). The
   category of abelian groups is the full subcategory of the category of
   groups (module 686) on the abelian groups; it is univalent with hom-sets.
   The group Hom(G, H) of sec:ab-hom is an abelian group whose symmetries are
   the morphisms G → H (an internal hom). `}

def AbelianGroupPredicate : Subtypes Group ≔ G ↦ (IsAbelian G, is_abelian_prop G)

def AbWild : WildPrecat ≔ FullSubcat GroupWild AbelianGroupPredicate

def AbCat : Category ≔ full_subcat_category GroupCat AbelianGroupPredicate

def ab_cat_objects : Id Type (AbCat .wild .ob) AbelianGroup ≔ refl AbelianGroup

def ab_cat_homs (A B : AbelianGroup) : Id Type (AbCat .wild .hom A B) (GroupHom (A .fst) (B .fst))
  ≔ refl (GroupHom (A .fst) (B .fst))

def ab_cat_objects_groupoid : isGroupoid (AbCat .wild .ob) ≔ category_objects_groupoid AbCat

{` The inclusion AbCat → GroupCat, fully faithful. `}
def ab_group_inclusion : WildFunctor AbWild GroupWild
  ≔ (obj ≔ A ↦ A .fst,
     mor ≔ A B f ↦ f,
     map_id ≔ A ↦ refl (group_hom_id (A .fst)),
     map_comp ≔ A B C f g ↦ refl (group_hom_compose (A .fst) (B .fst) (C .fst) f g))

def ab_group_inclusion_fully_faithful : IsFullyFaithful AbWild GroupWild ab_group_inclusion
  ≔ fully_faithful_from_equivs AbWild GroupWild ab_group_inclusion
      (A B ↦ identity_book_equiv (GroupHom (A .fst) (B .fst)) .equiv)

{` Isomorphisms in AbCat are group isomorphisms, and identifications of
   abelian groups are isomorphisms (univalence of AbCat). `}
def ab_cat_univalent : IsUnivalentCat AbWild ≔ AbCat .univalent

def ab_cat_path_iso_equiv (A B : AbelianGroup) : Equiv (Id AbelianGroup A B) (CatIso AbWild A B)
  ≔ cat_idtoiso_equiv AbWild ab_cat_univalent A B

{` The internal hom: Hom(G, H) as an object of AbCat, with
   USym(Hom(G, H)) ≃ AbCat(G, H). `}
def ab_internal_hom (A B : AbelianGroup) : AbCat .wild .ob ≔ abelian_hom_abelian_group (A .fst) B

def ab_internal_hom_usym_equiv (A B : AbelianGroup)
  : Equiv (USym (ab_internal_hom A B .fst)) (AbCat .wild .hom A B)
  ≔ abelian_hom_usym_equiv (A .fst) B

{` Litmus: Z is an object of AbCat, Σ₃ is not (every object has commuting
   symmetries). `}
def circle_ab_object (C : CircleSignature) : AbCat .wild .ob ≔ circle_abelian_group C

def ab_object_not_sigma3 (A : AbCat .wild .ob) (p : Id Group (A .fst) (symmetric_group three)) : Empty
  ≔ sigma3_no_abelian_structure A p
