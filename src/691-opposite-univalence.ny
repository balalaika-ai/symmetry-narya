export "603-adjunctions-and-equivalences"

{` Duality for univalence: the opposite of a univalent wild precategory is
   univalent. Isomorphisms a ≅ b in C^op are the isomorphisms b ≅ a of C
   with the two inverse conditions swapped. `}

def opposite_iso_to_iso (C : WildPrecat) (a b : C .ob) (e : CatIso (OppositeWild C) a b) : CatIso C b a
  ≔ (e .fst, (e .snd .snd, e .snd .fst))

def iso_to_opposite_iso (C : WildPrecat) (a b : C .ob) (e : CatIso C b a) : CatIso (OppositeWild C) a b
  ≔ (e .fst, (e .snd .snd, e .snd .fst))

def opposite_iso_equiv (C : WildPrecat) (a b : C .ob) : Equiv (CatIso (OppositeWild C) a b) (CatIso C b a)
  ≔ quasi_inverse_equiv (CatIso (OppositeWild C) a b) (CatIso C b a)
      (opposite_iso_to_iso C a b) (iso_to_opposite_iso C a b) (e ↦ refl e) (e ↦ refl e)

def cat_iso_inverse_involutive (C : WildPrecat) (a b : C .ob) (e : CatIso C a b)
  : Id (CatIso C a b) (cat_iso_inverse C b a (cat_iso_inverse C a b e)) e
  ≔ cat_iso_path C a b (cat_iso_inverse C b a (cat_iso_inverse C a b e)) e
      (refl (e .fst))

def cat_iso_reverse_equiv (C : WildPrecat) (a b : C .ob) : Equiv (CatIso C a b) (CatIso C b a)
  ≔ quasi_inverse_equiv (CatIso C a b) (CatIso C b a) (cat_iso_inverse C a b) (cat_iso_inverse C b a)
      (cat_iso_inverse_involutive C a b) (cat_iso_inverse_involutive C b a)

def opposite_univalent (C : WildPrecat) (u : IsUnivalentCat C) : IsUnivalentCat (OppositeWild C)
  ≔ cat_univalent_from_equivalences (OppositeWild C) (a b ↦
      compose_equiv (Id (C .ob) a b) (CatIso C b a) (CatIso (OppositeWild C) a b)
        (compose_equiv (Id (C .ob) a b) (CatIso C a b) (CatIso C b a)
          (cat_idtoiso_equiv C u a b) (cat_iso_reverse_equiv C a b))
        (canonical_inverse_equiv (CatIso (OppositeWild C) a b) (CatIso C b a) (opposite_iso_equiv C a b)))

def opposite_category (C : Category) : Category
  ≔ (OppositeWild (C .wild), a b ↦ C .homset b a, opposite_univalent (C .wild) (C .univalent))
