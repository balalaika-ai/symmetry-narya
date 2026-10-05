export "643-ff-eso-equivalences"
export "625-adjunction-units"

{` Chapter 6, section 6.7: fidelity check of def:cat-equiv and litmus
   examples for the univalence hypotheses of lem:ff-eso,
   lem:cat-equiv-is-prop and thm:ff-eso-equiv. `}

{` def:cat-equiv asks that the unit η and counit ε, as natural
   transformations, be isomorphisms. For precategories this is equivalent
   to the componentwise condition used in IsCatEquivalence
   (xca:funext-nat-trans, functor_cat_is_iso_equiv). `}
def cat_equivalence_functor_cat_isos_equiv (C D : Precat) (F : WildFunctor (C .wild) (D .wild))
  : Equiv (IsCatEquivalence (C .wild) (D .wild) F)
      (Σ (RightAdjointData (C .wild) (D .wild) F) (R ↦
        Product
          (CatIsIso (FunctorWild (C .wild) C) (functor_identity (C .wild))
            (functor_compose (C .wild) (D .wild) (C .wild) (R .right) F)
            (adjunction_unit_nat_trans (C .wild) (D .wild) F R))
          (CatIsIso (FunctorWild (D .wild) D) (functor_compose (D .wild) (C .wild) (D .wild) F (R .right))
            (functor_identity (D .wild))
            (adjunction_counit_nat_trans (C .wild) (D .wild) F R))))
  ≔ let W ≔ C .wild in
    let V ≔ D .wild in
    family_equiv (RightAdjointData W V F) (CatEquivalenceIsoConditions W V F)
      (R ↦ Product
          (CatIsIso (FunctorWild W C) (functor_identity W) (functor_compose W V W (R .right) F)
            (adjunction_unit_nat_trans W V F R))
          (CatIsIso (FunctorWild V D) (functor_compose V W V F (R .right)) (functor_identity V)
            (adjunction_counit_nat_trans W V F R)))
      (R ↦ product_equiv
        ((c : W .ob) → CatIsIso W c (R .right .obj (F .obj c)) (adjunction_unit W V F R c))
        ((d : V .ob) → CatIsIso V (F .obj (R .right .obj d)) d (adjunction_counit W V F R d))
        (CatIsIso (FunctorWild W C) (functor_identity W) (functor_compose W V W (R .right) F)
          (adjunction_unit_nat_trans W V F R))
        (CatIsIso (FunctorWild V D) (functor_compose V W V F (R .right)) (functor_identity V)
          (adjunction_counit_nat_trans W V F R))
        (canonical_inverse_equiv
          (CatIsIso (FunctorWild W C) (functor_identity W) (functor_compose W V W (R .right) F)
            (adjunction_unit_nat_trans W V F R))
          ((c : W .ob) → CatIsIso W c (R .right .obj (F .obj c)) (adjunction_unit W V F R c))
          (functor_cat_is_iso_equiv W C (functor_identity W) (functor_compose W V W (R .right) F)
            (adjunction_unit_nat_trans W V F R)))
        (canonical_inverse_equiv
          (CatIsIso (FunctorWild V D) (functor_compose V W V F (R .right)) (functor_identity V)
            (adjunction_counit_nat_trans W V F R))
          ((d : V .ob) → CatIsIso V (F .obj (R .right .obj d)) d (adjunction_counit W V F R d))
          (functor_cat_is_iso_equiv V D (functor_compose V W V F (R .right)) (functor_identity V)
            (adjunction_counit_nat_trans W V F R))))

{` Indiscrete (chaotic) precategories: every hom type is Unit. `}
def IndiscreteWild (A : Type) : WildPrecat
  ≔ (ob ≔ A,
     hom ≔ _ _ ↦ Unit,
     idn ≔ _ ↦ star.,
     comp ≔ _ _ _ _ _ ↦ star.,
     lu ≔ _ _ f ↦ unit_prop star. f,
     ru ≔ _ _ f ↦ unit_prop star. f,
     assoc ≔ _ _ _ _ _ _ _ ↦ refl (star. : Unit))

def indiscrete_homset (A : Type) : HasHomSets (IndiscreteWild A) ≔ _ _ ↦ unit_set

def IndiscretePrecat (A : Type) : Precat ≔ (IndiscreteWild A, indiscrete_homset A)

def indiscrete_iso (A : Type) (a b : A) : CatIso (IndiscreteWild A) a b
  ≔ (star., ((star., refl (star. : Unit)), (star., refl (star. : Unit))))

def indiscrete_iso_prop (A : Type) (a b : A) : isProp (CatIso (IndiscreteWild A) a b)
  ≔ sigma_prop Unit (CatIsIso (IndiscreteWild A) a b) unit_prop (cat_is_iso_prop (IndiscreteWild A) a b)

{` The terminal category: the indiscrete precategory on Unit is univalent. `}
def terminal_univalent : IsUnivalentCat (IndiscreteWild Unit)
  ≔ cat_univalent_from_contractible (IndiscreteWild Unit) (a ↦
      let T ≔ Σ Unit (b ↦ CatIso (IndiscreteWild Unit) a b) in
      let c : T ≔ (a, indiscrete_iso Unit a a) in
      (c, x ↦ sigma_prop Unit (b ↦ CatIso (IndiscreteWild Unit) a b) unit_prop (indiscrete_iso_prop Unit a) x c))

def TerminalCategory : Category ≔ (IndiscreteWild Unit, indiscrete_homset Unit, terminal_univalent)

{` The indiscrete precategory on Bool is not univalent (true ≅ false). `}
def indiscrete_bool_not_univalent (u : IsUnivalentCat (IndiscreteWild Bool)) : Empty
  ≔ bool_encode true. false. (cat_isotoid (IndiscreteWild Bool) u true. false. (indiscrete_iso Bool true. false.))

{` The unique functor to the terminal category is fully faithful and split
   essentially surjective in two ways (choosing true or false). `}
def indiscrete_bool_to_terminal : WildFunctor (IndiscreteWild Bool) (IndiscreteWild Unit)
  ≔ (obj ≔ _ ↦ star.,
     mor ≔ _ _ _ ↦ star.,
     map_id ≔ _ ↦ refl (star. : Unit),
     map_comp ≔ _ _ _ _ _ ↦ refl (star. : Unit))

def indiscrete_bool_to_terminal_ff
  : IsFullyFaithful (IndiscreteWild Bool) (IndiscreteWild Unit) indiscrete_bool_to_terminal
  ≔ ff_from_mor_equivs (IndiscreteWild Bool) (IndiscreteWild Unit) indiscrete_bool_to_terminal
      (_ _ ↦ quasi_inverse_equiv Unit Unit (_ ↦ star.) (_ ↦ star.) (x ↦ unit_prop star. x) (y ↦ unit_prop star. y) .equiv)

def indiscrete_bool_split_eso (b : Bool)
  : IsSplitEso (IndiscreteWild Bool) (IndiscreteWild Unit) indiscrete_bool_to_terminal
  ≔ d ↦ (b, indiscrete_iso Unit star. d)

def indiscrete_bool_equivalence (b : Bool)
  : IsCatEquivalence (IndiscreteWild Bool) (IndiscreteWild Unit) indiscrete_bool_to_terminal
  ≔ ff_split_eso_is_cat_equivalence (IndiscreteWild Bool) (IndiscreteWild Unit) indiscrete_bool_to_terminal
      indiscrete_bool_to_terminal_ff (indiscrete_bool_split_eso b)

{` Litmus for the claim before def:we-cat ("This will not be equivalent to
   the corresponding category"): taken literally it can fail, since this
   non-univalent precategory is equivalent to a category. `}
def non_univalent_precat_equivalent_to_category
  : Product (IsUnivalentCat (IndiscreteWild Bool) → Empty)
      (CatEquivalence (IndiscreteWild Bool) (TerminalCategory .wild))
  ≔ (indiscrete_bool_not_univalent, (indiscrete_bool_to_terminal, indiscrete_bool_equivalence true.))

{` lem:cat-equiv-is-prop needs C to be a category: the two equivalence
   structures differ (their right adjoints pick true and false). `}
def indiscrete_bool_equivalences_differ
  (p : Id (IsCatEquivalence (IndiscreteWild Bool) (IndiscreteWild Unit) indiscrete_bool_to_terminal)
        (indiscrete_bool_equivalence true.) (indiscrete_bool_equivalence false.)) : Empty
  ≔ bool_encode true. false.
      (refl ((E ↦ E .fst .right .obj star.)
          : IsCatEquivalence (IndiscreteWild Bool) (IndiscreteWild Unit) indiscrete_bool_to_terminal → Bool) p)

def is_cat_equivalence_not_prop_without_univalence
  (h : isProp (IsCatEquivalence (IndiscreteWild Bool) (IndiscreteWild Unit) indiscrete_bool_to_terminal)) : Empty
  ≔ indiscrete_bool_equivalences_differ (h (indiscrete_bool_equivalence true.) (indiscrete_bool_equivalence false.))

{` lem:ff-eso needs C to be a category: Σ_c F(c) ≅ * has the two distinct
   elements (true, _) and (false, _). `}
def ff_iso_fiber_not_prop_without_univalence
  (h : isProp (Σ Bool (c ↦ CatIso (IndiscreteWild Unit) (indiscrete_bool_to_terminal .obj c) star.))) : Empty
  ≔ bool_encode true. false.
      (h (true., indiscrete_iso Unit star. star.) (false., indiscrete_iso Unit star. star.) .fst)

{` The identity of the terminal category is an equivalence, and the
   equivalence structure is unique (lem:cat-equiv-is-prop applies). `}
def terminal_identity_equivalence_unique
  (E E' : IsCatEquivalence (TerminalCategory .wild) (TerminalCategory .wild) (functor_identity (TerminalCategory .wild)))
  : Id (IsCatEquivalence (TerminalCategory .wild) (TerminalCategory .wild) (functor_identity (TerminalCategory .wild))) E E'
  ≔ is_cat_equivalence_prop TerminalCategory (TerminalCategory .wild) (functor_identity (TerminalCategory .wild)) E E'
