export "604-wild-pointed-types"

{` Chapter 6 (cats.tex), ex:poset and xca:order-poset: preorders,
   their description by a reflexive transitive proposition-valued
   relation, posets (univalent preorders), the equivalence of univalence
   with antisymmetry, and the examples of the book. `}

{` ex:poset: a preorder is a precategory in which every arrow type is a
   proposition. `}
def HomsAreProps (C : WildPrecat) : Type ≔ (a b : C .ob) → isProp (C .hom a b)

def homs_are_props_prop (C : WildPrecat) : isProp (HomsAreProps C)
  ≔ pi_prop (C .ob) (a ↦ (b : C .ob) → isProp (C .hom a b))
      (a ↦ pi_prop (C .ob) (b ↦ isProp (C .hom a b)) (b ↦ isprop_isprop (C .hom a b)))

def Preorder : Type ≔ sig (wild : WildPrecat, homprop : HomsAreProps wild)

def preorder_homset (P : Preorder) : HasHomSets (P .wild)
  ≔ a b ↦ prop_is_set (P .wild .hom a b) (P .homprop a b)

def preorder_precat (P : Preorder) : Precat ≔ (P .wild, preorder_homset P)

{` "In this case, the types of λ, ρ and α are contractible." `}
def CatAssocAt (C : WildPrecat) (a b c d : C .ob) (f : C .hom a b) (g : C .hom b c) (h : C .hom c d) : Type
  ≔ Id (C .hom a d) (C .comp a c d h (C .comp a b c g f)) (C .comp a b d (C .comp b c d h g) f)

def CatAssocLaw (C : WildPrecat) : Type
  ≔ (a b c d : C .ob) (f : C .hom a b) (g : C .hom b c) (h : C .hom c d) → CatAssocAt C a b c d f g h

def precat_assoc_law_prop (C : WildPrecat) (hs : HasHomSets C) : isProp (CatAssocLaw C)
  ≔ pi_prop (C .ob)
      (a ↦ (b c d : C .ob) (f : C .hom a b) (g : C .hom b c) (h : C .hom c d) → CatAssocAt C a b c d f g h)
      (a ↦ pi_prop (C .ob)
        (b ↦ (c d : C .ob) (f : C .hom a b) (g : C .hom b c) (h : C .hom c d) → CatAssocAt C a b c d f g h)
        (b ↦ pi_prop (C .ob)
          (c ↦ (d : C .ob) (f : C .hom a b) (g : C .hom b c) (h : C .hom c d) → CatAssocAt C a b c d f g h)
          (c ↦ pi_prop (C .ob)
            (d ↦ (f : C .hom a b) (g : C .hom b c) (h : C .hom c d) → CatAssocAt C a b c d f g h)
            (d ↦ pi_prop (C .hom a b) (f ↦ (g : C .hom b c) (h : C .hom c d) → CatAssocAt C a b c d f g h)
              (f ↦ pi_prop (C .hom b c) (g ↦ (h : C .hom c d) → CatAssocAt C a b c d f g h)
                (g ↦ pi_prop (C .hom c d) (h ↦ CatAssocAt C a b c d f g h)
                  (h ↦ hs a d (C .comp a c d h (C .comp a b c g f)) (C .comp a b d (C .comp b c d h g) f))))))))

def preorder_left_unit_contractible (P : Preorder)
  : isContr ((a b : P .wild .ob) (f : P .wild .hom a b)
      → Id (P .wild .hom a b) (P .wild .comp a b b (P .wild .idn b) f) f)
  ≔ (P .wild .lu, l ↦ precat_left_unit_prop (P .wild) (preorder_homset P) l (P .wild .lu))

def preorder_right_unit_contractible (P : Preorder)
  : isContr ((a b : P .wild .ob) (f : P .wild .hom a b)
      → Id (P .wild .hom a b) (P .wild .comp a a b f (P .wild .idn a)) f)
  ≔ (P .wild .ru, r ↦ precat_right_unit_prop (P .wild) (preorder_homset P) r (P .wild .ru))

def preorder_assoc_contractible (P : Preorder) : isContr (CatAssocLaw (P .wild))
  ≔ (P .wild .assoc, s ↦ precat_assoc_law_prop (P .wild) (preorder_homset P) s (P .wild .assoc))

{` "The data of a preorder reduces to just a type P and a binary relation
   ≤ : P → P → Prop that is reflexive (via the identities) and transitive
   (via composition)." The two descriptions are equivalent types. `}
def PreorderRelation : Type ≔ sig (
  carrier : Type,
  rel : carrier → carrier → PropTypes,
  reflexive : (x : carrier) → rel x x .fst,
  transitive : (x y z : carrier) → rel x y .fst → rel y z .fst → rel x z .fst )

def preorder_of_relation (R : PreorderRelation) : Preorder
  ≔ ((ob ≔ R .carrier,
      hom ≔ x y ↦ R .rel x y .fst,
      idn ≔ x ↦ R .reflexive x,
      comp ≔ x y z q p ↦ R .transitive x y z p q,
      lu ≔ x y p ↦ R .rel x y .snd (R .transitive x y y p (R .reflexive y)) p,
      ru ≔ x y p ↦ R .rel x y .snd (R .transitive x x y (R .reflexive x) p) p,
      assoc ≔ x y z w p q r ↦ R .rel x w .snd (R .transitive x z w (R .transitive x y z p q) r)
        (R .transitive x y w p (R .transitive y z w q r))),
     x y ↦ R .rel x y .snd)

def relation_of_preorder (P : Preorder) : PreorderRelation
  ≔ (carrier ≔ P .wild .ob,
     rel ≔ x y ↦ (P .wild .hom x y, P .homprop x y),
     reflexive ≔ x ↦ P .wild .idn x,
     transitive ≔ x y z p q ↦ P .wild .comp x y z q p)

def preorder_relation_roundtrip (P : Preorder)
  : Id Preorder (preorder_of_relation (relation_of_preorder P)) P
  ≔ let C ≔ P .wild in
    let hs ≔ preorder_homset P in
    let Q ≔ preorder_of_relation (relation_of_preorder P) .wild in
    ((refl (C .ob), refl (C .hom), refl (C .idn), refl (C .comp),
      precat_left_unit_prop C hs (Q .lu) (C .lu),
      precat_right_unit_prop C hs (Q .ru) (C .ru),
      precat_assoc_law_prop C hs (Q .assoc) (C .assoc)),
     refl (P .homprop))

def relation_preorder_roundtrip (R : PreorderRelation)
  : Id PreorderRelation (relation_of_preorder (preorder_of_relation R)) R
  ≔ refl R

def preorder_relation_equiv : Equiv Preorder PreorderRelation
  ≔ quasi_inverse_equiv Preorder PreorderRelation relation_of_preorder preorder_of_relation
      preorder_relation_roundtrip relation_preorder_roundtrip

{` In a preorder an isomorphism is just a pair of arrows back and forth. `}
def preorder_iso_of_arrows (P : Preorder) (a b : P .wild .ob) (f : P .wild .hom a b) (g : P .wild .hom b a)
  : CatIso (P .wild) a b
  ≔ (f, ((g, P .homprop b b (P .wild .comp b a b f g) (P .wild .idn b)),
         (g, P .homprop a a (P .wild .comp a b a g f) (P .wild .idn a))))

def preorder_iso_prop (P : Preorder) (a b : P .wild .ob) : isProp (CatIso (P .wild) a b)
  ≔ sigma_prop (P .wild .hom a b) (CatIsIso (P .wild) a b) (P .homprop a b)
      (f ↦ cat_is_iso_prop (P .wild) a b f)

{` ex:poset: "x ≤ y and y ≤ x implies x = y". The book calls this
   condition "symmetric"; the displayed condition is antisymmetry. `}
def IsAntisymmetric (C : WildPrecat) : Type
  ≔ (a b : C .ob) → C .hom a b → C .hom b a → Id (C .ob) a b

def preorder_univalent_antisymmetric (P : Preorder) (u : IsUnivalentCat (P .wild)) : IsAntisymmetric (P .wild)
  ≔ a b f g ↦ cat_isotoid (P .wild) u a b (preorder_iso_of_arrows P a b f g)

def preorder_path_arrow (P : Preorder) (a b : P .wild .ob) (p : Id (P .wild .ob) a b) : P .wild .hom a b
  ≔ transport (P .wild .ob) (x ↦ P .wild .hom a x) a b p (P .wild .idn a)

{` An antisymmetric preorder has a set of objects: antisymmetry gives a
   weakly constant endomap of every identity type (Hedberg's argument,
   module 161). `}
def preorder_antisymmetric_objects_set (P : Preorder) (anti : IsAntisymmetric (P .wild)) : isSet (P .wild .ob)
  ≔ let O ≔ P .wild .ob in
    collapsible_paths_set O
      (x y p ↦ anti x y (preorder_path_arrow P x y p) (preorder_path_arrow P y x (inverse O x y p)))
      (x y p q ↦ refl (anti x y)
        (P .homprop x y (preorder_path_arrow P x y p) (preorder_path_arrow P x y q))
        (P .homprop y x (preorder_path_arrow P y x (inverse O x y p)) (preorder_path_arrow P y x (inverse O x y q))))

def preorder_antisymmetric_univalent (P : Preorder) (anti : IsAntisymmetric (P .wild))
  : IsUnivalentCat (P .wild)
  ≔ cat_univalent_from_equivalences (P .wild) (a b ↦
      iff_equiv (Id (P .wild .ob) a b) (CatIso (P .wild) a b)
        (preorder_antisymmetric_objects_set P anti a b) (preorder_iso_prop P a b)
        (cat_idtoiso (P .wild) a b) (e ↦ anti a b (e .fst) (e .snd .fst .fst)))

{` ex:poset: a preorder is univalent if and only if its relation is
   antisymmetric. `}
def preorder_univalent_iff_antisymmetric (P : Preorder)
  : Product (IsUnivalentCat (P .wild) → IsAntisymmetric (P .wild))
      (IsAntisymmetric (P .wild) → IsUnivalentCat (P .wild))
  ≔ (preorder_univalent_antisymmetric P, preorder_antisymmetric_univalent P)

{` ex:poset: a partial order (poset) is a univalent preorder. `}
def Poset : Type ≔ sig (wild : WildPrecat, homprop : HomsAreProps wild, univalent : IsUnivalentCat wild)

def poset_preorder (P : Poset) : Preorder ≔ (P .wild, P .homprop)

def poset_category (P : Poset) : Category ≔ (P .wild, preorder_homset (poset_preorder P), P .univalent)

def poset_from_antisymmetric (P : Preorder) (anti : IsAntisymmetric (P .wild)) : Poset
  ≔ (P .wild, P .homprop, preorder_antisymmetric_univalent P anti)

{` ex:poset: "In this case, the type of objects is a set." `}
def poset_objects_set (P : Poset) : isSet (P .wild .ob)
  ≔ preorder_antisymmetric_objects_set (poset_preorder P)
      (preorder_univalent_antisymmetric (poset_preorder P) (P .univalent))

{` ex:poset, typical examples. (ℕ, ≤) with the book's order
   (def:orderonN, BookLe). `}
def NatLeqPreorder : Preorder
  ≔ preorder_of_relation (Nat, m n ↦ (BookLe m n, book_le_prop m n), n ↦ (zero., add_zero_left n),
      m n k p q ↦ book_le_trans m n k p q)

def nat_leq_poset : Poset
  ≔ poset_from_antisymmetric NatLeqPreorder (m n p q ↦ book_le_antisym_equiv m n .map (p, q))

{` (ℤ, ≤), module 54. `}
def IntLeqPreorder : Preorder
  ≔ preorder_of_relation (Int, x y ↦ (IntLe x y, int_le_prop x y), int_le_refl, int_le_trans)

def int_leq_poset : Poset ≔ poset_from_antisymmetric IntLeqPreorder int_le_antisym

{` (Prop, →): antisymmetry is propositional extensionality. `}
def PropImplicationPreorder : Preorder
  ≔ preorder_of_relation (PropTypes, P Q ↦ (P .fst → Q .fst, pi_prop (P .fst) (_ ↦ Q .fst) (_ ↦ Q .snd)),
      P ↦ x ↦ x, P Q R f g ↦ x ↦ g (f x))

def prop_implication_poset : Poset
  ≔ poset_from_antisymmetric PropImplicationPreorder (P Q f g ↦ proposition_extensionality P Q f g)

{` (Sub(S), ⊆). The book assumes S is a set; this hypothesis is not needed,
   the construction works for every type S. `}
def SubtypeInclusionPreorder (S : Type) : Preorder
  ≔ preorder_of_relation (Subtypes S, P Q ↦ (Inclusion S P Q, inclusion_prop S P Q),
      inclusion_refl S, inclusion_trans S)

def subtype_inclusion_poset (S : Type) : Poset
  ≔ poset_from_antisymmetric (SubtypeInclusionPreorder S) (inclusion_antisym S)

{` ex:poset: "A preorder that fails to be a poset is the two-element type 2
   with the always true relation", hence a precategory that is not
   univalent. `}
def BoolChaoticPreorder : Preorder
  ≔ preorder_of_relation (Bool, _ _ ↦ (Unit, unit_prop), _ ↦ star., _ _ _ _ _ ↦ star.)

def bool_chaotic_precat : Precat ≔ preorder_precat BoolChaoticPreorder

def bool_chaotic_not_univalent (u : IsUnivalentCat (BoolChaoticPreorder .wild)) : Empty
  ≔ bool_encode true. false. (preorder_univalent_antisymmetric BoolChaoticPreorder u true. false. star. star.)

{` xca:order-poset: the type of orders with the divisibility relation of
   def:Order (an arrow d → k is d | k) is a poset. `}
def OrderDivisibilityPreorder : Preorder
  ≔ preorder_of_relation (Order, d k ↦ (OrderDivides d k, order_divides_prop d k),
      order_divides_refl, order_divides_trans)

def order_divisibility_poset : Poset
  ≔ poset_from_antisymmetric OrderDivisibilityPreorder order_divides_antisym

{` Litmus checks: 2 ≤ 5 in ℕ is witnessed by the difference 3, and its
   composite with 5 ≤ 7 has difference 5; -3 ≤ 2 in ℤ. `}
def nat_leq_two_five : NatLeqPreorder .wild .hom 2 5 ≔ (3, refl (5 : Nat))

def nat_leq_composite_difference
  : Id Nat (NatLeqPreorder .wild .comp 2 5 7 (2, refl (7 : Nat)) nat_leq_two_five .fst) 5
  ≔ refl (5 : Nat)

def int_leq_example : IntLeqPreorder .wild .hom (neg. 2) (pos. 2) ≔ star.

def bool_chaotic_iso : CatIso (BoolChaoticPreorder .wild) true. false.
  ≔ preorder_iso_of_arrows BoolChaoticPreorder true. false. star. star.
