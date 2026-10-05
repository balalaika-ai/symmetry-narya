export "607-terminal-initial-objects"

{` Chapter 6 (cats.tex), lem:op-idem: taking opposites is an equivalence
   from the type of wild precategories to itself, with an identification
   (C^op)^op = C.

   Deviation: the book calls the identification "trivially defined". In
   (C^op)^op every component agrees judgmentally with C except
   associativity, which is α⁻¹⁻¹ (def:op-cat uses α⁻¹); the identification
   is therefore refl on objects, arrows, identities, composition and the
   unit laws, and inverse_inverse (function extensionality) on α. `}

def opposite_opposite_assoc_path (C : WildPrecat)
  : Id (CatAssocLaw C) (OppositeWild (OppositeWild C) .assoc) (C .assoc)
  ≔ let O ≔ C .ob in
    let H ≔ C .hom in
    let A ≔ OppositeWild (OppositeWild C) .assoc in
    let B ≔ C .assoc in
    funext O (a ↦ (b c d : O) (f : H a b) (g : H b c) (h : H c d) → CatAssocAt C a b c d f g h) A B (a ↦
      funext O (b ↦ (c d : O) (f : H a b) (g : H b c) (h : H c d) → CatAssocAt C a b c d f g h) (A a) (B a) (b ↦
        funext O (c ↦ (d : O) (f : H a b) (g : H b c) (h : H c d) → CatAssocAt C a b c d f g h) (A a b) (B a b) (c ↦
          funext O (d ↦ (f : H a b) (g : H b c) (h : H c d) → CatAssocAt C a b c d f g h) (A a b c) (B a b c) (d ↦
            funext (H a b) (f ↦ (g : H b c) (h : H c d) → CatAssocAt C a b c d f g h) (A a b c d) (B a b c d) (f ↦
              funext (H b c) (g ↦ (h : H c d) → CatAssocAt C a b c d f g h) (A a b c d f) (B a b c d f) (g ↦
                funext (H c d) (h ↦ CatAssocAt C a b c d f g h) (A a b c d f g) (B a b c d f g) (h ↦
                  inverse_inverse (H a d) (C .comp a c d h (C .comp a b c g f)) (C .comp a b d (C .comp b c d h g) f)
                    (B a b c d f g h))))))))

{` lem:op-idem: the identification (C^op)^op = C. `}
def opposite_opposite_path (C : WildPrecat) : Id WildPrecat (OppositeWild (OppositeWild C)) C
  ≔ (refl (C .ob), refl (C .hom), refl (C .idn), refl (C .comp), refl (C .lu), refl (C .ru),
     opposite_opposite_assoc_path C)

{` lem:op-idem: (-)^op is an equivalence (in the book's sense) from the
   type of wild precategories to itself; it is its own inverse. `}
def opposite_book_equiv : BookEquiv WildPrecat WildPrecat
  ≔ book_quasi_inverse_equiv WildPrecat WildPrecat OppositeWild OppositeWild
      opposite_opposite_path opposite_opposite_path

def opposite_is_book_equiv : BookIsEquiv WildPrecat WildPrecat OppositeWild
  ≔ opposite_book_equiv .equiv

{` The same for precategories: the double opposite of a precategory is
   identified with it (the hom-set field lies over the identification
   above and is a proposition). `}
def opposite_precat_involution (C : Precat) : Id Precat (opposite_precat (opposite_precat C)) C
  ≔ (opposite_opposite_path (C .wild),
     pathover_of_eq WildPrecat HasHomSets (OppositeWild (OppositeWild (C .wild))) (C .wild)
       (opposite_opposite_path (C .wild)) (opposite_precat (opposite_precat C) .homset) (C .homset)
       (has_hom_sets_prop (C .wild)
         (transport WildPrecat HasHomSets (OppositeWild (OppositeWild (C .wild))) (C .wild)
           (opposite_opposite_path (C .wild)) (opposite_precat (opposite_precat C) .homset))
         (C .homset)))

{` Litmus checks: the double opposite has the original arrows and
   composition judgmentally; the path is refl on objects. `}
def opposite_opposite_hom_check
  : Id Type (OppositeWild (OppositeWild TypeWild) .hom Bool Unit) (Bool → Unit)
  ≔ refl (Bool → Unit)

def opposite_opposite_comp_check (f : Bool → Unit) (g : Unit → Nat)
  : Id (Bool → Nat) (OppositeWild (OppositeWild TypeWild) .comp Bool Unit Nat g f) (x ↦ g (f x))
  ≔ refl ((x ↦ g (f x)) : Bool → Nat)

def opposite_opposite_objects_check (C : WildPrecat)
  : Id (Id Type (C .ob) (C .ob)) (opposite_opposite_path C .ob) (refl (C .ob))
  ≔ refl (refl (C .ob))

def opposite_equiv_map_check : Id (WildPrecat → WildPrecat) (opposite_book_equiv .map) OppositeWild
  ≔ refl OppositeWild
