export "604-wild-pointed-types"
export "151-equivalence-exercises"
export "170-preimage-transfer"

{` Chapter 6 (cats.tex), running-text claims of section 6.2 not covered by
   a block: "for the wild precategory of types and functions, [univalence]
   is exactly the Univalence Axiom", and "the category of sets sits inside
   the wild category of types". `}

{` The Univalence Axiom (def:univalence) for the universe of Narya: the map
   p ↦ ptoe(p) (transport_equiv, whose underlying map is transport) is an
   equivalence. Equivalences X ≃ Y are the native Equiv here. `}
def UnivalenceStatement : Type ≔ (X Y : Type) → BookIsEquiv (Id Type X Y) (Equiv X Y) (transport_equiv X Y)

def univalence_statement_holds : UnivalenceStatement
  ≔ X Y ↦ book_equivalence (Id Type X Y) (Equiv X Y) (transport_univalence_equiv X Y) .equiv

{` idtoiso for the wild category of types followed by the comparison of
   isomorphisms with equivalences (type_iso_equiv) is ptoe. `}
def type_idtoiso_underlying_refl (A : Type)
  : Id (A → A) (cat_idtoiso TypeWild A A (refl A) .fst) (id_to_equiv A A (refl A) .map)
  ≔ concat (A → A) (cat_idtoiso TypeWild A A (refl A) .fst) (x ↦ x) (id_to_equiv A A (refl A) .map)
      (inverse (A → A) (x ↦ x) (cat_idtoiso TypeWild A A (refl A) .fst) (cat_idtoiso_refl TypeWild A .fst))
      (Jβ Type A (B _ ↦ Equiv A B) (identity_equiv A) .map)

def type_idtoiso_underlying (A B : Type) (p : Id Type A B)
  : Id (A → B) (cat_idtoiso TypeWild A B p .fst) (transport_equiv A B p .map)
  ≔ concat (A → B) (cat_idtoiso TypeWild A B p .fst) (id_to_equiv A B p .map) (transport_equiv A B p .map)
      (J Type A (B p ↦ Id (A → B) (cat_idtoiso TypeWild A B p .fst) (id_to_equiv A B p .map))
        (type_idtoiso_underlying_refl A) B p)
      (id_transport_equiv_path A B p .map)

def type_idtoiso_triangle (A B : Type)
  : Id (Id Type A B → Equiv A B)
      (compose (Id Type A B) (CatIso TypeWild A B) (Equiv A B) (type_iso_equiv A B .map) (cat_idtoiso TypeWild A B))
      (transport_equiv A B)
  ≔ funext (Id Type A B) (_ ↦ Equiv A B)
      (compose (Id Type A B) (CatIso TypeWild A B) (Equiv A B) (type_iso_equiv A B .map) (cat_idtoiso TypeWild A B))
      (transport_equiv A B)
      (p ↦ equiv_path A B (type_iso_equiv A B .map (cat_idtoiso TypeWild A B p)) (transport_equiv A B p)
        (type_idtoiso_underlying A B p))

{` "For the wild precategory of types and functions, this condition is
   exactly the Univalence Axiom": both directions. `}
def type_wild_univalent_to_univalence (u : IsUnivalentCat TypeWild) : UnivalenceStatement
  ≔ X Y ↦ book_equivalence (Id Type X Y) (Equiv X Y)
      (transport_equiv X Y,
       two_out_of_three_composite (Id Type X Y) (CatIso TypeWild X Y) (Equiv X Y)
         (cat_idtoiso TypeWild X Y) (transport_equiv X Y) (type_iso_equiv X Y .map)
         (type_idtoiso_triangle X Y)
         (native_equivalence (Id Type X Y) (CatIso TypeWild X Y) (cat_idtoiso TypeWild X Y, u X Y) .equiv)
         (type_iso_equiv X Y .equiv)) .equiv

def univalence_to_type_wild_univalent (ua : UnivalenceStatement) : IsUnivalentCat TypeWild
  ≔ X Y ↦ book_equivalence (Id Type X Y) (CatIso TypeWild X Y)
      (cat_idtoiso TypeWild X Y,
       two_out_of_three_left (Id Type X Y) (CatIso TypeWild X Y) (Equiv X Y)
         (cat_idtoiso TypeWild X Y) (transport_equiv X Y) (type_iso_equiv X Y .map)
         (type_idtoiso_triangle X Y)
         (native_equivalence (Id Type X Y) (Equiv X Y) (transport_equiv X Y, ua X Y) .equiv)
         (type_iso_equiv X Y .equiv)) .equiv

def type_wild_univalent_iff_univalence
  : Product (IsUnivalentCat TypeWild → UnivalenceStatement) (UnivalenceStatement → IsUnivalentCat TypeWild)
  ≔ (type_wild_univalent_to_univalence, univalence_to_type_wild_univalent)

{` "Note that the category of sets sits inside the wild category of
   types": SetWild is the full subcategory of TypeWild on the sets (module
   601); the inclusion functor is fully faithful (full_subcat_inclusion and
   set_inclusion_fully_faithful, modules 620 and 627) and it is an
   injection on objects. `}
def set_inclusion_objects_embedding : IsEmbedding SetTypes Type (A ↦ A .fst)
  ≔ subtype_projection_embedding Type isSet isset_isprop

{` Litmus: transporting along the identification obtained from the
   negation isomorphism of Bool computes as negation (pointwise, via the
   iso-to-path map of TypeWild and univalence). `}
def type_wild_bool_negation_iso : CatIso TypeWild Bool Bool
  ≔ (bool_not, type_equiv_to_is_iso Bool Bool bool_not (bool_not_equiv .equiv))

def type_wild_bool_negation_path_map
  : Id (Bool → Bool) (cat_idtoiso TypeWild Bool Bool
        (cat_isotoid TypeWild type_wild_univalent Bool Bool type_wild_bool_negation_iso) .fst) bool_not
  ≔ refl ((e ↦ e .fst) : CatIso TypeWild Bool Bool → Bool → Bool)
      (cat_idtoiso_isotoid TypeWild type_wild_univalent Bool Bool type_wild_bool_negation_iso)
