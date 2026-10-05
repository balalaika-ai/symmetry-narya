export "605-preorders-and-posets"

{` Chapter 6 (cats.tex), section 6.3: terminal and initial objects
   (def:terminal-obj, xca:terminal-prop, def:initial-obj,
   xca:unit-ptd-types) and the examples in the text. Contractibility is
   the book's (BookIsContr: a center and paths from it). `}

{` def:terminal-obj: every arrow type A → 1 is contractible. `}
def IsTerminalObj (C : WildPrecat) (t : C .ob) : Type ≔ (a : C .ob) → BookIsContr (C .hom a t)

def is_terminal_obj_prop (C : WildPrecat) (t : C .ob) : isProp (IsTerminalObj C t)
  ≔ pi_prop (C .ob) (a ↦ BookIsContr (C .hom a t)) (a ↦ book_iscontr_isprop (C .hom a t))

def TerminalObj (C : WildPrecat) : Type ≔ Σ (C .ob) (IsTerminalObj C)

{` def:initial-obj: every arrow type 0 → A is contractible. `}
def IsInitialObj (C : WildPrecat) (i : C .ob) : Type ≔ (a : C .ob) → BookIsContr (C .hom i a)

def is_initial_obj_prop (C : WildPrecat) (i : C .ob) : isProp (IsInitialObj C i)
  ≔ pi_prop (C .ob) (a ↦ BookIsContr (C .hom i a)) (a ↦ book_iscontr_isprop (C .hom i a))

def InitialObj (C : WildPrecat) : Type ≔ Σ (C .ob) (IsInitialObj C)

{` Duality (the paragraph before def:op-cat): initial objects of C are
   judgmentally the terminal objects of C^op. `}
def initial_is_terminal_op (C : WildPrecat) (i : C .ob)
  : Id Type (IsInitialObj C i) (IsTerminalObj (OppositeWild C) i)
  ≔ refl (IsInitialObj C i)

def book_contractible_paths (A : Type) (c : BookIsContr A) (x y : A) : Id A x y
  ≔ contractible_prop A (native_contraction A c) x y

{` Any two terminal objects are isomorphic: the unique arrows compose to
   endomorphisms of terminal objects, which equal the identities. `}
def terminal_objects_iso (C : WildPrecat) (s t : TerminalObj C) : CatIso C (s .fst) (t .fst)
  ≔ let f ≔ t .snd (s .fst) .center in
    let g ≔ s .snd (t .fst) .center in
    (f, ((g, book_contractible_paths (C .hom (t .fst) (t .fst)) (t .snd (t .fst))
              (C .comp (t .fst) (s .fst) (t .fst) f g) (C .idn (t .fst))),
         (g, book_contractible_paths (C .hom (s .fst) (s .fst)) (s .snd (s .fst))
              (C .comp (s .fst) (t .fst) (s .fst) g f) (C .idn (s .fst)))))

{` xca:terminal-prop: in a univalent wild precategory the type of terminal
   objects is a proposition. `}
def terminal_objects_prop (C : WildPrecat) (u : IsUnivalentCat C) : isProp (TerminalObj C)
  ≔ s t ↦ subtype_equal (C .ob) (IsTerminalObj C) (is_terminal_obj_prop C) s t
      (cat_isotoid C u (s .fst) (t .fst) (terminal_objects_iso C s t))

{` Dually, initial objects (terminal objects of the opposite). `}
def initial_objects_iso (C : WildPrecat) (s t : InitialObj C) : CatIso C (s .fst) (t .fst)
  ≔ let f ≔ s .snd (t .fst) .center in
    let g ≔ t .snd (s .fst) .center in
    (f, ((g, book_contractible_paths (C .hom (t .fst) (t .fst)) (t .snd (t .fst))
              (C .comp (t .fst) (s .fst) (t .fst) f g) (C .idn (t .fst))),
         (g, book_contractible_paths (C .hom (s .fst) (s .fst)) (s .snd (s .fst))
              (C .comp (s .fst) (t .fst) (s .fst) g f) (C .idn (s .fst)))))

def initial_objects_prop (C : WildPrecat) (u : IsUnivalentCat C) : isProp (InitialObj C)
  ≔ s t ↦ subtype_equal (C .ob) (IsInitialObj C) (is_initial_obj_prop C) s t
      (cat_isotoid C u (s .fst) (t .fst) (initial_objects_iso C s t))

{` "The unit type 1 is a terminal object in the wild category of types,
   and in the category of sets." `}
def unit_terminal_type : IsTerminalObj TypeWild Unit
  ≔ A ↦ (center ≔ _ ↦ star.,
         contract ≔ f ↦ funext A (_ ↦ Unit) (_ ↦ star.) f (x ↦ unit_prop star. (f x)))

def unit_set_object : SetCat .wild .ob ≔ (Unit, prop_is_set Unit unit_prop)

def unit_terminal_set : IsTerminalObj (SetCat .wild) unit_set_object
  ≔ A ↦ unit_terminal_type (A .fst)

{` "The empty type 0 is initial in the wild category of types." `}
def empty_initial_type : IsInitialObj TypeWild Empty
  ≔ A ↦ (center ≔ e ↦ absurd A e,
         contract ≔ f ↦ funext Empty (_ ↦ A) (e ↦ absurd A e) f (e ↦ match e []))

{` In a univalent wild category, the types of terminal and initial objects
   are then contractible. `}
def type_wild_terminal_contractible : BookIsContr (TerminalObj TypeWild)
  ≔ (center ≔ (Unit, unit_terminal_type),
     contract ≔ t ↦ terminal_objects_prop TypeWild type_wild_univalent (Unit, unit_terminal_type) t)

def type_wild_initial_contractible : BookIsContr (InitialObj TypeWild)
  ≔ (center ≔ (Empty, empty_initial_type),
     contract ≔ t ↦ initial_objects_prop TypeWild type_wild_univalent (Empty, empty_initial_type) t)

{` xca:unit-ptd-types: the unit type pointed at its unique element
   (pointed_unit of module 98) is terminal and initial in the wild
   category of pointed types. `}
def unit_carrier_contractible : BookIsContr Unit
  ≔ (center ≔ star., contract ≔ u ↦ unit_prop star. u)

def pointed_unit_terminal : IsTerminalObj PointedWild pointed_unit
  ≔ X ↦ (center ≔ (_ ↦ star., refl (star. : Unit)),
         contract ≔ f ↦ equiv_inverse_map
           (Id (BookPointedMap X pointed_unit) (_ ↦ star., refl (star. : Unit)) f)
           (PointedHomotopy X pointed_unit (_ ↦ star., refl (star. : Unit)) f)
           (pointed_map_path_equiv X pointed_unit (_ ↦ star., refl (star. : Unit)) f)
           (x ↦ unit_prop star. (f .fst x),
            prop_is_set Unit unit_prop star. (f .fst (X .point))
              (concat Unit star. star. (f .fst (X .point)) (refl (star. : Unit)) (unit_prop star. (f .fst (X .point))))
              (f .snd)))

def pointed_unit_initial : IsInitialObj PointedWild pointed_unit
  ≔ X ↦ contractible_domain_pointed_maps pointed_unit X unit_carrier_contractible

def pointed_unit_zero_object : Product (IsTerminalObj PointedWild pointed_unit) (IsInitialObj PointedWild pointed_unit)
  ≔ (pointed_unit_terminal, pointed_unit_initial)

{` Litmus checks: the unique map to 1 is constant; 1 is not initial and 0
   is not terminal among types; the unique pointed map from the pointed
   unit picks the base point. `}
def unit_terminal_map_value : Id Unit (unit_terminal_type Bool .center true.) star.
  ≔ refl (star. : Unit)

def unit_not_initial_type (h : IsInitialObj TypeWild Unit) : Empty ≔ h Empty .center star.

def empty_not_terminal_type (h : IsTerminalObj TypeWild Empty) : Empty ≔ h Unit .center star.

def pointed_unit_initial_value
  : Id Bool (pointed_unit_initial pointed_bool_true .center .fst star.) true.
  ≔ refl (true. : Bool)
